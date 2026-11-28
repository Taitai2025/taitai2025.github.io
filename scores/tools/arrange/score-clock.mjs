const EPS = 1e-8;
const sameQ = (a, b) => Math.abs(a-b) <= EPS;
const unique = values => [...new Set(values)];
const keyed = (values, key) => [...new Map(values.map(value=>[key(value),value])).values()];

function collapseTempoMarks(marks, issues) {
  const sorted = marks.sort((a,b)=>a.atQ-b.atQ);
  const events = [];
  for (let first=0; first<sorted.length;) {
    const base=sorted[first];
    let end=first+1;
    while (end<sorted.length && sameQ(sorted[end].atQ,base.atQ)) end++;
    const samePosition=sorted.slice(first,end);
    if (samePosition.some(mark=>!sameQ(mark.bpm,base.bpm))) {
      issues.push({atQ:base.atQ,measureIndex:base.measureIndex,kind:'tempo',reason:'同一拍位的速度标记互相冲突',sustained:true});
    } else {
      events.push({atQ:base.atQ,bpm:base.bpm,measureIndex:base.measureIndex,sources:unique(samePosition.map(mark=>mark.source))});
    }
    first=end;
  }
  return events;
}

function swingUncertainties(part,durationQ) {
  const marks=part.measureDetails.flatMap(bar=>bar.swingMarks.map(mark=>({
    ...mark,measureIndex:bar.index,atQ:bar.startQ+Math.max(0,Math.min(bar.durationQ,mark.onset)),
  }))).sort((a,b)=>a.atQ-b.atQ || Number(a.swung)-Number(b.swung));
  const intervals=[];
  let active=null;
  for (const mark of marks) {
    if (mark.swung && !active) active=mark;
    else if (!mark.swung && active) {
      intervals.push([active,mark.atQ]);
      active=null;
    }
  }
  if (active) intervals.push([active,durationQ]);
  return intervals.filter(([start,endQ])=>endQ>start.atQ+EPS).map(([{atQ,measureIndex},endQ])=>({
    atQ,endQ,measureIndex,kind:'played-timing',reason:'摇摆节奏改变实际拍内位置',sustained:false,
  }));
}

export function assembleScoreClock(parts) {
  const measures=[], marks=[], issues=[];
  const measureCount=Math.max(...parts.map(part=>part.measureDetails.length));
  let startQ=0;
  for (let index=0; index<measureCount; index++) {
    const written=parts.map(part=>part.measureDetails[index]).filter(Boolean);
    const number=written[0].number;
    const lengths=written.map(bar=>bar.actualDurationQ).filter(duration=>duration>EPS);
    const meters=written.map(bar=>bar.meterQ).filter(duration=>duration!==null);
    const meterQ=meters[0]??null;
    const actualDurationQ=Math.max(0,...lengths);
    const durationQ=actualDurationQ || (written.some(bar=>bar.implicit) ? 0 : meterQ??0);
    const endQ=startQ+durationQ;
    const uncertainLengths=lengths.some(duration=>!sameQ(duration,actualDurationQ));
    const uncertainMeters=meters.some(meter=>!sameQ(meter,meterQ));
    const rhythmReasons=new Set();
    if (written.length!==parts.length || written.some(bar=>bar.number!==number)) rhythmReasons.add('各声部的小节无法完全对齐');
    if (uncertainLengths) rhythmReasons.add('各声部的小节实际时值不一致');
    if (uncertainMeters) rhythmReasons.add('各声部的拍号时值不一致');
    if (durationQ<=EPS) rhythmReasons.add('无法确认小节的实际长度');

    const flowIssues=unique(written.flatMap(bar=>bar.flowIssues));
    const backward=keyed(written.map(bar=>bar.repeatBackward).filter(Boolean),repeat=>repeat.times);
    if (backward.length>1) flowIssues.push('各声部的反复次数不一致');
    const endings=keyed(written.flatMap(bar=>bar.endings),ending=>JSON.stringify(ending));
    for (const type of ['start','stop','discontinue']) {
      if (endings.filter(ending=>ending.type===type).length>1) flowIssues.push('各声部的一、二房范围不一致');
    }
    const rehearsalMarks=keyed(written.flatMap(bar=>bar.rehearsalMarks),mark=>JSON.stringify(mark))
      .sort((a,b)=>a.onset-b.onset)
      .map(mark=>({label:mark.label,atQ:startQ+mark.onset}));

    for (const bar of written) {
      for (const reason of bar.rhythmIssues) rhythmReasons.add(reason);
      for (const mark of bar.tempoMarks) {
        if (mark.onset < -EPS || mark.onset > durationQ+EPS) {
          issues.push({atQ:startQ,measureIndex:index,kind:'tempo',reason:'速度标记超出小节拍位',sustained:true});
          continue;
        }
        marks.push({atQ:startQ+Math.max(0,Math.min(durationQ,mark.onset)),bpm:mark.bpm,measureIndex:index,source:mark.source});
      }
      for (const {onset,...issue} of bar.timingIssues) {
        const atQ=startQ+Math.max(0,Math.min(durationQ,onset));
        issues.push({atQ,measureIndex:index,...issue});
      }
    }
    for (const reason of rhythmReasons) issues.push({atQ:startQ,measureIndex:index,kind:'rhythm',reason,sustained:false});

    const pickup=index===0 && actualDurationQ>EPS && meterQ!==null && actualDurationQ<meterQ-EPS;
    const uncertain=rhythmReasons.size>0;
    for (const bar of written) {
      Object.assign(bar,{startQ,endQ,durationQ,pickup,uncertain});
      for (const event of bar.events) {
        event.startQ=startQ+event.onset;
        event.durationQ=event.duration;
        event.endQ=event.duration===null ? null : event.startQ+event.duration;
        if (event.sounding!==null) event.pitchKey=`p:${event.sounding}`;
      }
    }
    measures.push({
      index,number,startQ,endQ,durationQ,actualDurationQ,meterQ,pickup,uncertain,
      implicit:written.some(bar=>bar.implicit),
      newPage:written.some(bar=>bar.newPage),
      rehearsals:unique(rehearsalMarks.map(mark=>mark.label)),rehearsalMarks,
      repeatForward:written.some(bar=>bar.repeatForward),repeatBackward:backward[0]??null,endings,flowIssues,
    });
    startQ=endQ;
  }
  const tempoEvents=collapseTempoMarks(marks,issues);
  for (const part of parts) issues.push(...swingUncertainties(part,startQ));
  let nextTempo=0;
  const timingUncertainties=keyed(issues,issue=>JSON.stringify(issue)).sort((a,b)=>a.atQ-b.atQ).filter(issue=>{
    if (!issue.coveredByTempoMark) return true;
    while (nextTempo<tempoEvents.length && tempoEvents[nextTempo].atQ<issue.atQ-EPS) nextTempo++;
    return !sameQ(tempoEvents[nextTempo]?.atQ,issue.atQ);
  });
  return {measures,durationQ:startQ,tempoEvents,timingUncertainties};
}

const validBpm = bpm => Number.isFinite(bpm) && bpm>0;

/**
 * Convert a written quarter-note span after tempo is confirmed. An explicit
 * constant quarter BPM or written-coordinate overrides can supply tempo
 * where the score has missing, variable or conflicting markings.
 */
export function quarterSpanSeconds(model,startQ,endQ,{tempoConfirmed=false,quarterBpm=null,tempoOverrides=[]}={}) {
  if (tempoConfirmed!==true || !Number.isFinite(startQ) || !Number.isFinite(endQ) ||
      startQ < -EPS || endQ < startQ-EPS ||
      Number.isFinite(model.durationQ) && endQ>model.durationQ+EPS ||
      quarterBpm!==null && !validBpm(quarterBpm) || !Array.isArray(tempoOverrides)) return null;
  if (sameQ(startQ,endQ)) return 0;
  const presentIssues=model.timingUncertainties??[];
  if (presentIssues.some(issue=>{
    if (issue.kind==='rhythm') {
      const measure=model.measures?.[issue.measureIndex];
      if (measure && measure.endQ>measure.startQ+EPS) return measure.endQ>startQ+EPS && measure.startQ<endQ-EPS;
    }
    if (Number.isFinite(issue.endQ)) return issue.endQ>startQ+EPS && issue.atQ<=endQ+EPS;
    return !issue.sustained && issue.atQ>=startQ-EPS && issue.atQ<=endQ+EPS;
  })) return null;
  const overrides=[...tempoOverrides].sort((a,b)=>a?.startQ-b?.startQ);
  if (overrides.some((override,index)=>{
    if (!override) return true;
    const {startQ:start,endQ:end,bpm}=override;
    return !Number.isFinite(start) || !Number.isFinite(end) || start < -EPS || end <= start+EPS ||
      Number.isFinite(model.durationQ) && end>model.durationQ+EPS || !validBpm(bpm) ||
      index>0 && start<overrides[index-1].endQ-EPS;
  })) return null;

  const invalidators=presentIssues.filter(issue=>issue.sustained);
  const changes=[...(model.tempoEvents??[]),...invalidators.map(issue=>({atQ:issue.atQ,bpm:null,kind:issue.kind}))]
    .sort((a,b)=>a.atQ-b.atQ || Number(a.bpm===null)-Number(b.bpm===null));
  let nextChange=0, nextOverride=0, bpm=null, activeUncertainty=null, seconds=0;
  let position=startQ;
  while (position<endQ-EPS) {
    while (nextChange<changes.length && changes[nextChange].atQ<=position+EPS) {
      const change=changes[nextChange++];
      bpm=validBpm(change.bpm) ? change.bpm : null;
      activeUncertainty=bpm===null ? change.kind : null;
    }
    while (nextOverride<overrides.length && overrides[nextOverride].endQ<=position+EPS) nextOverride++;
    const override=overrides[nextOverride];
    const active=override && override.startQ<=position+EPS;
    const applicable=active ? override.bpm : quarterBpm??bpm;
    if (!validBpm(applicable) || activeUncertainty==='played-timing') return null;
    const overrideBoundary=active ? override.endQ : override?.startQ??Infinity;
    const nextBoundary=Math.min(endQ,changes[nextChange]?.atQ??Infinity,overrideBoundary);
    if (nextBoundary<=position) return null;
    seconds+=(nextBoundary-position)*60/applicable;
    position=nextBoundary;
  }
  return seconds;
}
