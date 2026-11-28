import {quarterSpanSeconds} from './score-clock.mjs';

const EPS = 1e-8;
const MAX_VISITS = 12000;
const MAX_REPEAT_DEPTH = 32;
const near = (left,right) => Math.abs(left-right) <= EPS;

function endingRanges(measures) {
  const ranges=[];
  let opening=null;
  for (const [index,measure] of measures.entries()) {
    const markers=measure.endings??[];
    const starts=markers.filter(marker=>marker.type==='start');
    const closes=markers.filter(marker=>marker.type==='stop'||marker.type==='discontinue');
    if (starts.length+closes.length!==markers.length || starts.length>1 || closes.length>1) return null;
    if (starts.length) {
      const number=String(starts[0].number??'').trim();
      if (opening || !['1','2'].includes(number)) return null;
      opening={start:index,number};
    }
    if (closes.length) {
      if (!opening || opening.number!==String(closes[0].number??'').trim()) return null;
      ranges.push({...opening,end:index});
      opening=null;
    }
  }
  return opening ? null : ranges;
}

function repeatRanges(measures) {
  const endings=endingRanges(measures);
  if (!endings) return null;
  const starts=[];
  const repeats=[];
  let usedImplicitStart=false;
  for (const [index,measure] of measures.entries()) {
    if (measure.flowIssues?.length) return null;
    if (measure.repeatForward) starts.push(index);
    if (!measure.repeatBackward) continue;
    const implicit=!starts.length;
    if (implicit && usedImplicitStart) return null;
    usedImplicitStart ||= implicit;
    const start=starts.pop()??0;
    const times=measure.repeatBackward.times??2;
    if (!Number.isSafeInteger(times) || times<1 || times>MAX_VISITS) return null;
    repeats.push({start,end:index,times,children:[]});
  }
  if (starts.length) return null;

  for (let index=0;index<endings.length;index+=2) {
    const first=endings[index], second=endings[index+1];
    const repeat=repeats.find(item=>item.end===first.end);
    if (first.number!=='1' || second?.number!=='2' || second.start!==first.end+1
      || !repeat || repeat.times!==2 || first.start<repeat.start) return null;
    repeat.first=first;
    repeat.second=second;
    repeat.end=second.end;
  }
  const roots=[];
  const parents=[];
  repeats.sort((left,right)=>left.start-right.start||right.end-left.end);
  for (const repeat of repeats) {
    while (parents.length && parents.at(-1).end<repeat.start) parents.pop();
    const parent=parents.at(-1);
    if (parents.length>=MAX_REPEAT_DEPTH || (parent && (
      repeat.start===parent.start || repeat.end>=parent.end ||
      (parent.first && repeat.end>=parent.first.start)
    ))) return null;
    (parent?.children??roots).push(repeat);
    parents.push(repeat);
  }
  return roots;
}

function performanceOrder(measures) {
  const repeats=repeatRanges(measures);
  if (!repeats) return null;
  const order=[];
  const writeRange=(start,end,children)=>{
    let index=start;
    for (const child of children) {
      if (!writeRange(index,child.start-1,[])) return false;
      for (let pass=1;pass<=child.times;pass++) {
        const endOfPass=child.first ? (pass===1 ? child.first.end : child.first.start-1) : child.end;
        if (!writeRange(child.start,endOfPass,child.children)) return false;
        if (child.second && pass===2 && !writeRange(child.second.start,child.second.end,[])) return false;
      }
      index=child.end+1;
    }
    if (order.length+Math.max(0,end-index+1)>MAX_VISITS) return false;
    for (;index<=end;index++) order.push(index);
    return true;
  };
  return writeRange(0,measures.length-1,repeats) ? order : null;
}

function buildTimeline(measures,order) {
  let position=0;
  const runs=[];
  const visits=order.map((index,visitIndex)=>{
    const measure=measures[index];
    if (!visitIndex || index!==order[visitIndex-1]+1) {
      runs.push({start:position,end:null,startQ:measure.startQ,endQ:null});
    }
    const start=position;
    position+=measure.endQ-measure.startQ;
    const run=runs.at(-1);
    run.end=position;
    run.endQ=measure.endQ;
    return {index,measure,start,end:position};
  });
  return {visits,runs,end:position,rhythmIssues:visits.filter(visit=>visit.measure.uncertain)};
}

function assignByMeasure(plan,count) {
  const byMeasure=[];
  const players=new Map();
  let cursor=0;
  for (const section of plan?.sections??[]) {
    if (section.start!==cursor || !Number.isInteger(section.end)
      || section.end<=cursor || section.end>count || !Array.isArray(section.mappings)) break;
    const rows=section.mappings.filter(row=>row.status==='assigned' && row.player?.id!=null);
    for (const {player} of rows) players.set(player.id,player);
    for (;cursor<section.end;cursor++) byMeasure.push(rows);
  }
  return {byMeasure,players,complete:cursor===count};
}

function pageCandidates(model,assignment,supplied,includeEmbedded) {
  const candidates=new Map();
  const manualPlayers=new Set();
  const include=(beforeMeasure,playerId,source,confirmed,scope)=>{
    if (playerId==null || !Number.isInteger(beforeMeasure) || beforeMeasure<1 || beforeMeasure>=model.measures.length) return;
    const key=JSON.stringify([playerId,beforeMeasure]);
    const prior=candidates.get(key);
    if (!prior || confirmed) candidates.set(key,{beforeMeasure,playerId,source,confirmed,scope});
    if (source==='manual') manualPlayers.add(playerId);
  };
  if (Array.isArray(supplied)) {
    for (const candidate of supplied) {
      for (const playerId of candidate.playerId==null ? assignment.players.keys() : [candidate.playerId]) {
        include(candidate.beforeMeasure,playerId,'manual',candidate.confirmed!==false,candidate.scope);
      }
    }
  }
  if (!Array.isArray(supplied) || includeEmbedded) {
    const parts=new Map(model.parts?.map(part=>[part.id,part]));
    for (const [index,measure] of model.measures.entries()) {
      const relevant=new Set([...(assignment.byMeasure[index-1]??[]),...(assignment.byMeasure[index]??[])]);
      for (const row of relevant) {
        const part=parts.get(row.source?.id);
        if (!manualPlayers.has(row.player.id) && (part?.measureDetails?.[index]?.newPage ?? measure.newPage)) {
          include(index,row.player.id,'embedded',false);
        }
      }
    }
  }
  return [...candidates.values()].sort((left,right)=>left.beforeMeasure-right.beforeMeasure);
}

function mergeIntervals(intervals) {
  const merged=[];
  intervals.sort((left,right)=>left.start-right.start || left.end-right.end);
  for (const interval of intervals) {
    const prior=merged.at(-1);
    if (prior && interval.start<=prior.end+EPS) prior.end=Math.max(prior.end,interval.end);
    else merged.push({...interval});
  }
  return merged;
}

function addTie(ties,partId,event,time,connecting) {
  const identity=JSON.stringify([partId,event.voice,event.pitchKey]);
  if (!ties.has(identity)) ties.set(identity,[]);
  ties.get(identity).push({time,connecting,known:event.pitchKey!=null});
}

function findTies(track) {
  const connected=[];
  for (const events of track.ties.values()) {
    events.sort((left,right)=>left.time-right.time);
    for (let first=0;first<events.length;) {
      let end=first+1;
      while (end<events.length && near(events[first].time,events[end].time)) end++;
      const group=events.slice(first,end);
      const heads=group.filter(event=>event.connecting).length;
      const tails=group.length-heads;
      const time=events[first].time;
      if (heads && heads===tails && group.every(event=>event.known)) connected.push(time);
      else track.uncertainties.push({
        start:time,end:tails>heads ? track.end : time,reason:'unresolved-tie',
      });
      first=end;
    }
  }
  return connected.sort((left,right)=>left-right);
}

function playedTracks(model,timeline,assignment) {
  const parts=new Map(model.parts?.map(part=>[part.id,part]));
  const tracks=new Map(Array.from(assignment.players.keys(),id=>[
    id,{intervals:[],uncertainties:[],timingWarnings:[],ties:new Map(),instruments:[],end:timeline.end},
  ]));
  for (const visit of timeline.visits) {
    const {index,measure,start,end}=visit;
    for (const row of assignment.byMeasure[index]??[]) {
      const track=tracks.get(row.player.id);
      const partId=row.source?.id;
      const details=parts.get(partId)?.measureDetails?.[index];
      const instrument=row.target?.profile??row.target?.name;
      const previous=track.instruments.at(-1);
      if (instrument && previous?.name!==instrument) track.instruments.push({name:instrument,at:start});
      if (!details || !Array.isArray(details.events) || (!details.events.length && !details.hasExplicitTiming)) {
        track.uncertainties.push({start,end,reason:'missing-notes'});
        continue;
      }
      if (details.uncertain) track.uncertainties.push({start,end,reason:'rhythm-unverified'});
      for (const event of details.events) {
        if (event.cue) continue;
        const {startQ,endQ}=event;
        if (!Number.isFinite(startQ) || !Number.isFinite(endQ) || endQ<startQ-EPS
          || startQ<measure.startQ-EPS || endQ>measure.endQ+EPS || (!event.grace && near(startQ,endQ))) {
          track.uncertainties.push({start,end,reason:'missing-notes'});
          continue;
        }
        if (event.rest || event.type==='rest') continue;
        const attack=start+Math.max(0,startQ-measure.startQ);
        const release=end-Math.max(0,measure.endQ-endQ);
        if (event.grace || event.performanceModified) {
          track.timingWarnings.push({start:attack,end:release,reason:'attack-or-release-unverified'});
        }
        if (event.letRing) track.uncertainties.push({start:release,end:timeline.end,reason:'unresolved-sustain'});
        if (event.tieStop) addTie(track.ties,partId,event,attack,true);
        if (event.tieStart) addTie(track.ties,partId,event,release,false);
        track.intervals.push({start:attack,end:release});
      }
    }
  }
  for (const track of tracks.values()) {
    track.connectedTies=findTies(track);
    track.intervals=mergeIntervals(track.intervals);
  }
  return tracks;
}

function firstAfter(intervals,beat) {
  let left=0,right=intervals.length;
  while (left<right) {
    const mid=Math.floor((left+right)/2);
    if (intervals[mid].start<=beat+EPS) left=mid+1;
    else right=mid;
  }
  return left;
}

function silentSpan(track,beat,end) {
  const next=firstAfter(track.intervals,beat);
  const before=track.intervals[next-1];
  if (before && before.end>=beat-EPS) {
    if (before.end>beat+EPS && before.start<beat-EPS) return {start:beat,end:beat};
    if (before.start>=beat-EPS) return {start:track.intervals[next-2]?.end??0,end:beat};
  }
  return {start:before?.end??0,end:track.intervals[next]?.start??end};
}

function intervalTouches(interval,start,end) {
  if (near(interval.start,interval.end)) return interval.start>=start-EPS && interval.start<=end+EPS;
  return interval.start<end-EPS && interval.end>start+EPS;
}

function runningTempoWarnings(model,timeline) {
  const marks=(model.tempoEvents??[]).filter(event=>Number.isFinite(event.bpm)&&event.bpm>0);
  const changes=[...marks,...(model.timingUncertainties??[]).filter(issue=>issue.sustained)]
    .sort((left,right)=>left.atQ-right.atQ||Number(right.bpm!=null)-Number(left.bpm!=null));
  const warnings=[];
  let playedTempo=null;
  for (const [index,run] of timeline.runs.entries()) {
    const written=marks.findLast(mark=>mark.atQ<=run.startQ+EPS);
    const firstMark=marks.find(mark=>mark.atQ>=run.startQ-EPS && mark.atQ<run.endQ-EPS);
    if (index && (!firstMark || !near(firstMark.atQ,run.startQ))
      && (playedTempo===null || !written || !near(playedTempo,written.bpm))) {
      warnings.push({start:run.start,end:firstMark ? run.start+firstMark.atQ-run.startQ : run.end});
    }
    const finalChange=changes.findLast(mark=>mark.atQ<run.endQ-EPS && mark.atQ>=run.startQ-EPS);
    if (finalChange) playedTempo=finalChange.bpm??null;
  }
  return warnings;
}

function playedSwingIntervals(model,timeline) {
  if (timeline.runs.length===1) return [];
  const intervals=[];
  for (const part of model.parts??[]) {
    let activeSince=null;
    for (const visit of timeline.visits) {
      const marks=part.measureDetails?.[visit.index]?.swingMarks;
      if (!marks?.length) continue;
      const sorted=[...marks].sort((left,right)=>left.onset-right.onset||Number(left.swung)-Number(right.swung));
      for (const mark of sorted) {
        const at=Math.min(visit.end,visit.start+Math.max(0,mark.onset));
        if (mark.swung) activeSince??=at;
        else if (activeSince!==null) {
          intervals.push({start:activeSince,end:at});
          activeSince=null;
        }
      }
    }
    if (activeSince!==null) intervals.push({start:activeSince,end:timeline.end});
  }
  return mergeIntervals(intervals.filter(interval=>interval.end>interval.start+EPS));
}

function coveredByOverrides(startQ,endQ,overrides) {
  let covered=startQ;
  for (const span of overrides) {
    if (span?.startQ<=covered+EPS && span.endQ>covered) covered=span.endQ;
    if (covered>=endQ-EPS) return true;
  }
  return false;
}

function secondsAcrossRuns(model,runs,start,end,options,warnings) {
  let seconds=0;
  for (const run of runs) {
    const from=Math.max(start,run.start);
    const to=Math.min(end,run.end);
    if (from>=to-EPS) continue;
    const startQ=run.startQ+from-run.start;
    const endQ=run.startQ+to-run.start;
    if (!options.quarterBpm && warnings.some(warning=>intervalTouches(warning,from,to)
      && !coveredByOverrides(run.startQ+Math.max(from,warning.start)-run.start,
        run.startQ+Math.min(to,warning.end)-run.start,options.tempoOverrides))) {
      return {seconds:null,reason:'repeat-tempo-unverified'};
    }
    const tempoConfirmed=options.tempoConfirmed || coveredByOverrides(startQ,endQ,options.tempoOverrides);
    const duration=quarterSpanSeconds(model,startQ,endQ,{...options,tempoConfirmed});
    if (duration===null || !Number.isFinite(duration)) {
      const timingUnverified=(model.timingUncertainties??[]).some(issue=>issue.kind==='played-timing'
        && issue.atQ>=startQ-EPS && issue.atQ<=endQ+EPS);
      return {seconds:null,reason:timingUnverified ? 'attack-or-release-unverified' : 'tempo-unverified'};
    }
    seconds+=duration;
  }
  return {seconds};
}

function clockIsValid(measures) {
  return measures.every((measure,index)=>{
    const previous=measures[index-1];
    return Number.isFinite(measure.startQ) && Number.isFinite(measure.endQ) && measure.endQ>measure.startQ+EPS
      && near(measure.startQ,previous?.endQ??0);
  });
}

function crossingsFor(timeline,candidate,track,otherCuts,model,tempo,warnings,swingIntervals) {
  const evaluated=[];
  for (let visitIndex=1;visitIndex<timeline.visits.length;visitIndex++) {
    const from=timeline.visits[visitIndex-1], to=timeline.visits[visitIndex];
    const low=Math.min(from.index,to.index), high=Math.max(from.index,to.index);
    const boundary=candidate.beforeMeasure;
    if (boundary<=low || boundary>high) continue;
    const beat=to.start;
    const {start,end}=silentSpan(track,beat,timeline.end);
    const reasons=[];
    const problems=track.uncertainties.filter(issue=>intervalTouches(issue,start,end));
    const crossesRhythm=timeline.rhythmIssues.some(visit=>intervalTouches(visit,start,end));
    if (crossesRhythm) reasons.push('rhythm-unverified');
    for (const problem of problems) reasons.push(problem.reason);
    const beats=end-start;
    let seconds=null;
    let availableBeats=null;
    if (beats<=EPS) {
      availableBeats=0;
      seconds=0;
      reasons.push(track.connectedTies.some(at=>near(at,beat)) ? 'sustained-across-page' : 'no-silence');
    } else if (!reasons.length) {
      availableBeats=beats;
      const warning=track.timingWarnings.find(issue=>intervalTouches(issue,start,end)
        || near(issue.start,end) || near(issue.end,start));
      const swung=swingIntervals.some(interval=>intervalTouches(interval,start,end)||near(interval.start,end));
      if (warning || swung) reasons.push('attack-or-release-unverified');
      else {
        const result=secondsAcrossRuns(model,timeline.runs,start,end,tempo,warnings);
        seconds=result.seconds;
        if (result.reason) reasons.push(result.reason);
      }
    }
    if (otherCuts.some(cut=>cut!==boundary && cut>low && cut<=high)) reasons.push('several-page-boundaries');
    if (track.instruments.slice(1).some(change=>change.at>=start-EPS && change.at<=end+EPS)) {
      reasons.push('instrument-change-in-window');
    }
    evaluated.push({
      fromMeasure:from.index,toMeasure:to.index,boundaryBeat:beat,availableBeats,
      releaseBeat:availableBeats===null ? null : start,attackBeat:availableBeats===null ? null : end,
      availableSeconds:seconds,reasons:[...new Set(reasons)],
    });
  }
  return evaluated;
}

function withStatus(candidate,status,reasons,visits=[],availableBeats=null,availableSeconds=null) {
  return {...candidate,status,reasons,visits,availableBeats,availableSeconds};
}

function reviewCandidate(candidate,track,visits,thresholds) {
  if (!track) return withStatus(candidate,'review',['player-unassigned']);
  if (!visits.length) return withStatus(candidate,'review',['boundary-not-visited']);
  if (!track.intervals.length && !track.uncertainties.length) {
    return withStatus(candidate,'none',['no-playing-notes'],visits,0,0);
  }
  const reasons=new Set(visits.flatMap(visit=>visit.reasons));
  if (!candidate.confirmed) reasons.add('printed-layout-unconfirmed');
  const beats=visits.some(visit=>visit.availableBeats===0)
    ? 0
    : visits.some(visit=>visit.availableBeats===null)
      ? null
      : Math.min(...visits.map(visit=>visit.availableBeats));
  const seconds=beats===0 ? 0 : visits.some(visit=>visit.availableSeconds===null)
    ? null
    : Math.min(...visits.map(visit=>visit.availableSeconds));
  let status='review';
  if (beats===0) status='none';
  else if ((beats!==null && beats+EPS<thresholds.minimumBeats)
    || (seconds!==null && seconds+EPS<thresholds.minimumSeconds)) status='short';
  else if (beats!==null && seconds!==null && !reasons.size) status='possible';
  return withStatus(candidate,status,[...reasons],visits,beats,seconds);
}

/**
 * Evaluate actual crossings of a proposed page cut in a section assignment.
 * All measure positions are zero-based written indices. Played beats restart
 * only at the beginning of the score. The source layout remains advisory.
 */
export function analyzePageTurns(model,plan,options={}) {
  const measures=model.measures??[];
  const assignment=assignByMeasure(plan,measures.length);
  const candidates=pageCandidates({...model,measures},assignment,options.candidates,options.includeEmbedded===true);
  const override=options.tempoOverride;
  const confirmed=override?.confirmed===true;
  const globalBpm=confirmed ? override.bpm : null;
  const overrides=confirmed && Array.isArray(override.intervals)
    ? [...override.intervals].sort((left,right)=>left?.startQ-right?.startQ)
    : [];
  const quarterBpm=Number.isFinite(globalBpm)&&globalBpm>0 ? globalBpm : null;
  const tempo={
    tempoConfirmed:quarterBpm!==null||options.tempoConfirmed===true,
    quarterBpm,
    tempoOverrides:overrides,
  };
  const thresholds={
    minimumBeats:Number.isFinite(options.minimumBeats) ? Math.max(0,options.minimumBeats) : 0,
    minimumSeconds:Number.isFinite(options.minimumSeconds) ? Math.max(0,options.minimumSeconds) : 3,
  };
  const failed=reason=>({
    ...thresholds,performanceOrder:null,
    candidates:candidates.map(candidate=>withStatus(candidate,'review',[reason])),
  });
  if (!assignment.complete) return failed('assignment-plan-incomplete');
  if (!clockIsValid(measures)) return failed('rhythm-unverified');
  const order=performanceOrder(measures);
  if (!order) return failed('repeat-order-unverified');
  if (!candidates.length) return {...thresholds,performanceOrder:order,candidates:[]};
  const timeline=buildTimeline(measures,order);
  const tracks=playedTracks(model,timeline,assignment);
  const warnings=runningTempoWarnings(model,timeline);
  const swingIntervals=playedSwingIntervals(model,timeline);
  const cutsByPlayer=new Map();
  for (const candidate of candidates) {
    if (!cutsByPlayer.has(candidate.playerId)) cutsByPlayer.set(candidate.playerId,[]);
    cutsByPlayer.get(candidate.playerId).push(candidate.beforeMeasure);
  }
  return {
    ...thresholds,performanceOrder:order,
    candidates:candidates.map(candidate=>{
      const track=tracks.get(candidate.playerId);
      const visits=track ? crossingsFor(timeline,candidate,track,cutsByPlayer.get(candidate.playerId),model,tempo,warnings,swingIntervals) : [];
      return reviewCandidate(candidate,track,visits,thresholds);
    }),
  };
}
