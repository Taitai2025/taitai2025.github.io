import { roles } from '../instruments.mjs';
import { parseMusicXML } from '../musicxml.mjs';
import { readScoreFile } from '../score-file.mjs';
import { planSections,sectionGapReasons } from '../section-planner.mjs';
import { compareOptionalLayers,comparisonReasons } from '../section-compare.mjs';
import { analyzePageTurns } from '../turn-windows.mjs';
import { configKind,demoXML,displaySeatNames,freshPlayer,generalRoster,makeRoster,maxPlayers,numberValue,pagePositions,printedPageCuts,readSettings,sectionsFrom } from './setup.mjs';
import { describe,displayNumber,downloadCsv,el,make,priorityLabels,renderParts,renderPlayers,status,table } from './view.mjs';

const state={score:null,scoreKey:'',rosterScoreKey:'',players:[],draft:null,result:null,loadId:0,configId:0,compareId:0,comparison:null};
const fieldIds=['segment-starts','switch-beats','turn-seconds','page-starts','turn-tempo','page-hints'];

function invalidate() {
  const hadResult=Boolean(state.result);
  state.compareId++;
  state.comparison=null;
  el('comparison-result').hidden=true;
  el('compare-plans').disabled=false;
  state.result=null;
  el('plan-result').hidden=true;
  const ready=Boolean(state.score&&state.players.length);
  el('run-plan').disabled=!ready;
  status('plan-status',ready?(hadResult?'设置已更改，请重新计算。':'可计算分段方案。'):'载入总谱并添加演奏员后即可计算。');
}
function paintPlayers() {
  renderPlayers(state.players,invalidate,paintPlayers,Boolean(state.score));
  el('add-player').disabled=state.players.length>=maxPlayers;
  invalidate();
}
function startsFromRehearsals() {
  return state.score?.measures.flatMap((bar,i)=>bar.rehearsals?.length?[i+1]:[])??[];
}
function clearScore() {
  state.score=null;state.scoreKey='';
  el('loaded-score').hidden=true;
  el('segment-starts').value='1';el('page-starts').value='';el('turn-tempo').value='';el('page-hints').checked=false;
  paintPlayers();
}
function currentSettings() {
  const fields=Object.fromEntries(fieldIds.map(id=>[id,el(id).type==='checkbox'?el(id).checked:el(id).value]));
  const parts=state.score?.parts.map(({id,role,priority})=>({id,role,priority}))??[];
  return {kind:configKind,version:1,scoreKey:state.scoreKey,parts,fields,players:state.players.map(player=>({...player}))};
}
function applySettings(draft) {
  const matched=Boolean(state.score&&state.scoreKey&&draft.scoreKey===state.scoreKey);
  for (const id of (matched?fieldIds:['switch-beats','turn-seconds'])) {
    if (el(id).type==='checkbox') el(id).checked=draft.fields[id]===true;
    else if (typeof draft.fields[id]==='string') el(id).value=draft.fields[id].slice(0,350);
  }
  if (!matched) return false;
  state.players=draft.players.map(player=>({...player}));
  state.rosterScoreKey=state.scoreKey;
  if (state.draft===draft) state.draft=null;
  const saved=new Map(draft.parts.filter(p=>p&&typeof p.id==='string').map(p=>[p.id,p]));
  for (const part of state.score.parts) {
    const chosen=saved.get(part.id);
    if (!chosen) continue;
    if (Object.hasOwn(roles,chosen.role)) part.role=chosen.role;
    if (Object.hasOwn(priorityLabels,chosen.priority)) part.priority=chosen.priority;
  }
  return true;
}
async function scoreDigest(text) {
  if (!globalThis.crypto?.subtle) return '';
  const bytes=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(text));
  return [...new Uint8Array(bytes)].map(value=>value.toString(16).padStart(2,'0')).join('');
}
async function loadScore(source,isDemo=false) {
  const loadId=++state.loadId;
  const previous=state.score?currentSettings():null;
  clearScore();status('score-status','正在读取总谱。');
  try {
    const text=await source(), key=await scoreDigest(text);
    if (loadId!==state.loadId) return;
    const score=parseMusicXML(text);
    if (!score.measures?.length) throw new Error('没有可用于分段的小节。请核对总谱。');
    state.score=score;state.scoreKey=key;
    if (!key||key!==state.rosterScoreKey) state.players=generalRoster(state.players);
    state.rosterScoreKey=key;
    for (const part of score.parts) part.priority='required';
    const restored=state.draft?applySettings(state.draft):false;
    if (!restored&&!isDemo&&previous?.scoreKey===key) applySettings(previous);
    if (isDemo&&!restored) {
      el('segment-starts').value='1, 3, 5, 7';
      el('page-starts').value='5';el('turn-tempo').value='96';
      score.parts[1].priority='optional';
      state.players=[freshPlayer('qudi','笛子席'),freshPlayer('cello','低音席'),freshPlayer('altoSheng','笙席')];
      state.players[2].secondary='sheng';
      state.players[2].absences='3-4';
    }
    el('use-rehearsals').disabled=!startsFromRehearsals().some(start=>start>1);
    const copy=score.title+' · '+score.measures.length+' 小节 · '+score.parts.length+' 个声部';
    status('score-status',copy+(restored?' · 已恢复同一份谱的设置。':''));
    el('loaded-score').hidden=false;
    renderParts(score.parts,invalidate);
    paintPlayers();
  } catch(error) {
    if (loadId!==state.loadId) return;
    clearScore();status('score-status',error.message,true);
  }
}
function createPlan() {
  const score=state.score,count=score.measures.length;
  const players=makeRoster(state.players,count);
  const sections=sectionsFrom(el('segment-starts').value,count);
  const switchBeats=numberValue(el('switch-beats').value,'兼奏间隔',0,64);
  const minimumSeconds=numberValue(el('turn-seconds').value,'翻页时长',0.5,60);
  const bpm=numberValue(el('turn-tempo').value,'确认速度',20,400,true);
  const defaults=pagePositions(el('page-starts').value,count);
  const plan=planSections(score,players,{sections,switchBeats});
  const context={players,sections,switchBeats,minimumSeconds,bpm,defaults,includeEmbedded:el('page-hints').checked};
  return {plan,baselinePlan:plan,context,...timingFor(plan,context),seatNames:displaySeatNames(players)};
}
function timingFor(plan,{players,minimumSeconds,bpm,defaults,includeEmbedded}) {
  const assigned=new Set(plan.sections.flatMap(section=>section.mappings.flatMap(row=>row.player?[row.player.id]:[])));
  const candidates=printedPageCuts(players,defaults,assigned);
  const checkTurns=Boolean(candidates.length||includeEmbedded);
  const timing=checkTurns
    ? analyzePageTurns(state.score,plan,{
        candidates,includeEmbedded,
        minimumBeats:0,minimumSeconds,...(bpm!==null?{tempoOverride:{bpm,confirmed:true}}:{}),
      })
    : {candidates:[]};
  return {timing,checkTurns};
}
function measureLabel(i) {
  return state.score.measures[i]?.number??String(i+1);
}
function makeMapping(row) {
  const assigned=row.status==='assigned';
  const source=row.source;
  const reasons=assigned?describe(row.evaluation?.review):
    (row.reasons??[]).map(reason=>sectionGapReasons[reason]??reason);
  const notes=[
    ...reasons,
    ...(row.carriesIn?['接续上段延音']:[]),...(row.carriesOut?['延音跨段']:[]),
  ];
  return {
    part:source.name,partId:source.id,priority:priorityLabels[source.priority]??priorityLabels.required,
    player:state.result.seatNames.get(row.player?.id)??'',playerId:row.player?.id??'',instrument:row.target?.name??'',
    outcome:assigned?(row.evaluation?.safe===false?'待复核':'候选可承接'):'未分配',
    needsReview:!assigned||row.evaluation?.safe===false,notes,
  };
}
function flattenSections() {
  return state.result.plan.sections.map(section=>({
    start:section.start+1,end:section.end,originalStart:measureLabel(section.start),originalEnd:measureLabel(section.end-1),
    mappings:section.mappings.map(makeMapping),
    switches:section.switches.map(sw=>({
      player:state.result.seatNames.get(sw.player?.id)??sw.player?.name??sw.player,playerId:sw.player?.id??'',
      from:sw.from?.name??sw.from,to:sw.to?.name??sw.to,
      beats:sw.availableBeats,minimumBeats:sw.minimumBeats,
    })),
    ties:section.gaps.ties.map(tie=>({part:tie.source?.name??'',reason:sectionGapReasons[tie.reason]??tie.reason})),
    priorityConflict:section.priorityConflict??null,
  }));
}
function flattenTurns() {
  const statusLabels={possible:'时长达到要求',short:'休止太短',none:'没有可用休止',review:'待复核'};
  return state.result.timing.candidates.map(candidate=>({
    player:state.result.seatNames.get(candidate.playerId)??candidate.playerId,playerId:candidate.playerId,bar:candidate.beforeMeasure+1,
    originalBar:measureLabel(candidate.beforeMeasure),
    source:candidate.source==='embedded'?'源谱提示':candidate.scope==='seat'?'席位实际分页':'默认分页',
    beats:candidate.availableBeats,seconds:candidate.availableSeconds,status:candidate.status,
    outcome:statusLabels[candidate.status]??'待复核',reasons:describe(candidate.reasons),
    visits:(candidate.visits??[]).map(visit=>({
      from:visit.fromMeasure+1,to:visit.toMeasure+1,boundaryBeat:visit.boundaryBeat,
      releaseBeat:visit.releaseBeat,attackBeat:visit.attackBeat,
      beats:visit.availableBeats,seconds:visit.availableSeconds,reasons:describe(visit.reasons),
    })),
  }));
}
function renderResult() {
  if (!state.result) return;
  const only=el('issue-only').checked,sections=flattenSections(),turns=flattenTurns();
  const score=state.score;
  el('plan-identity').textContent=score.title+' · '+score.measures.length+' 小节 · '+score.parts.length+' 个声部'
    +(state.scoreKey?' · 谱件指纹 '+state.scoreKey.slice(0,12):'')
    +(state.result.comparison?' · 已采用可选层取舍候选':' · 逐段基线');
  const nodes=[];
  for (const [i,section] of sections.entries()) {
    const mappings=only?section.mappings.filter(row=>row.needsReview):section.mappings;
    if (only&&!mappings.length&&!section.ties.length&&!section.priorityConflict) continue;
    const title='顺序 '+section.start+'–'+section.end+' · 原谱 '+section.originalStart+'–'+section.originalEnd;
    const entry=make('details','','segment-plan');
    entry.open=i===0||sections.length<=4||mappings.some(row=>row.outcome==='未分配'&&row.priority==='必保留');
    entry.append(make('summary',title));
    if (mappings.length) entry.append(table(['原声部','优先级','席位','乐器','结论','复核备注'],mappings.map(row=>[
      row.part,row.priority,row.player||'—',row.instrument||'—',row.outcome,row.notes.join('；')||'—',
    ]),title+'的声部分工'));
    else entry.append(make('p','此段没有活动声部。','meta'));
    for (const tie of section.ties) entry.append(make('p',tie.part+' '+tie.reason,'segment-error'));
    if (section.priorityConflict) entry.append(make('p',
      '本段有必保声部与上段的可选延音争用席位。若调整前段安排，可能多保留 '+section.priorityConflict.requiredRecoverable+' 个声部。','segment-error'));
    for (const sw of section.switches) entry.append(make('p',sw.player+'由'+sw.from+'换至'+sw.to+'，有 '+displayNumber(sw.beats)+' 拍休止。','meta'));
    nodes.push(entry);
  }
  el('section-results').replaceChildren(...(nodes.length?nodes:[make('p','当前视图没有需要复核的声部。','meta')]));
  const turnsBox=el('turn-results');turnsBox.replaceChildren();
  if (turns.length) {
    const shown=only?turns.filter(row=>row.status!=='possible'):turns;
    turnsBox.append(make('h3','逐席位换页'));
    if (shown.length) turnsBox.append(table(['演奏员','新一页小节','来源','四分音符拍','秒','结论','复核备注'],shown.map(row=>[
      row.player,row.bar+'（原谱 '+row.originalBar+'）',row.source,displayNumber(row.beats),displayNumber(row.seconds),
      row.outcome,[...row.reasons,row.visits.length>1?'已核对 '+row.visits.length+' 次经过':''].filter(Boolean).join('；'),
    ]),'逐席位翻页休止'));
    else turnsBox.append(make('p','当前视图没有需要复核的换页位置。','meta'));
  } else if (state.result.checkTurns) turnsBox.append(make('p','尚无可供核对的席位分页提示。','meta'));
  el('plan-limitations').replaceChildren(...state.result.plan.limitations.map(text=>make('li',text)));
  el('plan-result').hidden=false;
}
function renderComparison() {
  const value=state.comparison;
  if(!value||!state.result) return;
  const {baseline,candidate,report}=value;
  const applied=Boolean(state.result.comparison);
  const summary=table(['方案','必保声部段覆盖','可选声部段覆盖','延音待核'],[
    ['逐段基线',baseline.totals.requiredMatched+'/'+baseline.totals.required,baseline.totals.optionalMatched+'/'+baseline.totals.optional,baseline.totals.tieGaps],
    ['比较候选',candidate.totals.requiredMatched+'/'+candidate.totals.required,candidate.totals.optionalMatched+'/'+candidate.totals.optional,candidate.totals.tieGaps],
  ],'可选层取舍与逐段基线比较');
  el('comparison-summary').replaceChildren(summary);
  const names=report.omittedNames.length?'候选整条不分配：'+report.omittedNames.join('、')+'。':'';
  status('comparison-status',`已比较 ${report.tested} 个方案；${comparisonReasons[report.termination]}。${report.improved?'找到优于逐段基线的候选。':'本次范围内未找到更好的候选。'}${applied?'已采用候选，翻页检查已重算。':'当前分工保持逐段基线。'}`);
  el('comparison-notes').textContent=names+report.explanation;
  el('apply-comparison').hidden=!report.improved||applied;
  el('restore-baseline').hidden=!applied;
  el('compare-plans').disabled=applied;
  el('comparison-result').hidden=false;
}
function save(content,suffix,type) {
  const href=URL.createObjectURL(new Blob([content],{type}));
  const anchor=make('a');
  const title=(state.score?.title??'分段').replace(/[\\/:*?"<>|]/gu,'_').slice(0,52);
  anchor.download='国乐谱汇_'+title+'_'+suffix;anchor.href=href;
  document.body.append(anchor);anchor.click();anchor.remove();
  setTimeout(()=>URL.revokeObjectURL(href),4000);
}
el('load-demo').addEventListener('click',()=>{el('load-score').value='';loadScore(()=>demoXML,true);});
el('load-score').addEventListener('change',event=>{
  const file=event.currentTarget.files[0];
  if (!file) return;
  loadScore(()=>readScoreFile(file));
});
el('add-player').addEventListener('click',()=>{
  if (state.players.length<maxPlayers) state.players.push(freshPlayer());
  paintPlayers();el('player-settings').lastElementChild?.querySelector('input')?.focus();
});
el('load-config').addEventListener('change',async event=>{
  const field=event.currentTarget,file=field.files[0],configId=++state.configId;
  if (!file) return;
  try {
    if (file.size>250000) throw new Error('设置文件过大。');
    const draft=readSettings(await file.text());
    if (configId!==state.configId) return;
    state.draft=draft;state.players=generalRoster(draft.players);
    const restored=applySettings(draft);
    if (state.score) renderParts(state.score.parts,invalidate);
    paintPlayers();
    status('roster-status',restored?'已恢复这份总谱的席位、缺席、分页、分段和优先级。':'已恢复通用名单。载入同一份原谱后再恢复缺席、分页、分段和优先级。');
  } catch(error) {
    if (configId===state.configId) status('roster-status',error.message,true);
  } finally {
    if (configId===state.configId) field.value='';
  }
});
el('save-config').addEventListener('click',()=>save(JSON.stringify(currentSettings(),null,2),'设置.json','application/json'));
el('use-rehearsals').addEventListener('click',()=>{
  el('segment-starts').value=[...new Set([1,...startsFromRehearsals()])].join(', ');invalidate();
});
for (const id of fieldIds) el(id).addEventListener('input',invalidate);
el('issue-only').addEventListener('change',renderResult);
el('run-plan').addEventListener('click',()=>{
  if (!state.score||!state.players.length) return;
  try {
    state.compareId++;state.comparison=null;el('comparison-result').hidden=true;el('compare-plans').disabled=false;
    state.result=createPlan();const plan=state.result.plan,totals=plan.totals;
    status('plan-status',plan.sections.length+' 段 · 必保覆盖 '+totals.requiredMatched+'/'+totals.required+
      ' · 可选覆盖 '+totals.optionalMatched+'/'+totals.optional+' · 兼奏换手 '+totals.switches+' 处');
    renderResult();
  } catch(error) {invalidate();status('plan-status',error.message,true);}
});
el('compare-plans').addEventListener('click',async()=>{
  if(!state.result||!state.score) return;
  const requested=++state.compareId,score=state.score,context=state.result.context;
  el('compare-plans').disabled=true;
  el('comparison-result').hidden=false;
  el('comparison-summary').replaceChildren();
  el('comparison-notes').textContent='仅对标为可选的整条声部尝试取舍，最多比较 32 个方案或约 1.5 秒。单次求解完成后检查预算。';
  el('apply-comparison').hidden=true;el('restore-baseline').hidden=true;
  status('comparison-status','正在比较可选层取舍，当前分工保持不变。');
  try {
    const result=await compareOptionalLayers(score,context.players,{
      sections:context.sections,switchBeats:context.switchBeats,
      maxPlans:32,maxMillis:1500,
      cancelled:()=>requested!==state.compareId||state.score!==score||!state.result,
      yieldControl:()=>new Promise(resolve=>setTimeout(resolve,0)),
    });
    if(requested!==state.compareId||result.report.termination==='cancelled') return;
    state.comparison=result;renderComparison();
  } catch(error) {
    if(requested===state.compareId) status('comparison-status',error.message,true);
  } finally {
    if(requested===state.compareId) el('compare-plans').disabled=false;
  }
});
el('apply-comparison').addEventListener('click',()=>{
  if(!state.result||!state.comparison?.report.improved) return;
  const plan=state.comparison.candidate;
  state.result={...state.result,plan,comparison:state.comparison.report,...timingFor(plan,state.result.context)};
  status('plan-status','已采用比较候选。必保声部段覆盖 '+plan.totals.requiredMatched+'/'+plan.totals.required+'；请复核整条可选层的取舍。');
  renderResult();renderComparison();
});
el('restore-baseline').addEventListener('click',()=>{
  if(!state.result) return;
  const plan=state.result.baselinePlan;
  state.result={...state.result,plan,comparison:null,...timingFor(plan,state.result.context)};
  status('plan-status','已恢复逐段基线，翻页检查已重算。');
  renderResult();renderComparison();
});
el('export-json').addEventListener('click',()=>{
  const content={kind:'guoyue-section-plan',version:1,title:state.score.title,scoreCheck:state.scoreKey,
    summary:state.result.plan.totals,sections:flattenSections(),turns:flattenTurns(),limitations:state.result.plan.limitations,
    comparison:state.comparison?.report??null,comparisonApplied:Boolean(state.result.comparison)};
  save(JSON.stringify(content,null,2),'排练方案.json','application/json');
});
el('export-csv').addEventListener('click',()=>{
  const rows=[['记录','段起／页首','段末','原谱起','原谱末','原声部','优先级','席位','乐器','结论','复核项','四分音符拍','秒','席位编号']];
  const append=(cells,id='')=>rows.push([...Array.from({length:13},(_,i)=>cells[i]??''),id]);
  if(state.result.comparison) {
    const comparison=state.result.comparison;
    append(['候选比较','','','','','','','','','已采用有界比较候选',
      '已比较 '+comparison.tested+' 个方案；'+comparisonReasons[comparison.termination]+'；整条不分配 '+comparison.omittedNames.join('、')+'；未证明全曲最优']);
  }
  for (const section of flattenSections()) {
    for (const row of section.mappings) append(['分段',section.start,section.end,section.originalStart,section.originalEnd,row.part,
      row.priority,row.player,row.instrument,row.outcome,row.notes.join('；')],row.playerId);
    for (const sw of section.switches) append(['换乐器',section.start,section.end,section.originalStart,section.originalEnd,
      '','',sw.player,sw.from+' → '+sw.to,'候选休止','至少 '+sw.minimumBeats+' 拍',sw.beats],sw.playerId);
    for (const tie of section.ties) append(['延音',section.start,section.end,section.originalStart,section.originalEnd,tie.part,'','','','待复核',tie.reason]);
    if (section.priorityConflict) append(['优先级',section.start,section.end,section.originalStart,section.originalEnd,
      '','','','','待复核','上段可选延音占用席位，本段可复核 '+section.priorityConflict.requiredRecoverable+' 个必保声部']);
  }
  for (const turn of flattenTurns()) append(['翻页',turn.bar,'',turn.originalBar,'','','',turn.player,'',turn.outcome,
    [turn.source,...turn.reasons].join('；'),turn.beats,turn.seconds],turn.playerId);
  save(downloadCsv(rows),'排练分工.csv','text/csv;charset=utf-8');
});
el('print-plan').addEventListener('click',()=>{
  const closed=[...el('section-results').querySelectorAll('details:not([open])')];
  closed.forEach(node=>{node.open=true;});
  window.addEventListener('afterprint',()=>closed.forEach(node=>{node.open=false;}),{once:true});
  window.print();
});
paintPlayers();
