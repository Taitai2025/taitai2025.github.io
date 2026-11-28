import assert from 'node:assert/strict';
import { compareOptionalLayers } from '../scores/tools/arrange/section-compare.mjs';

const shift={chromatic:0,diatonic:0,known:true};
const measures=[{startQ:0,endQ:4,rehearsals:[]},{startQ:4,endQ:8,rehearsals:[]}];
const sections=[{start:0,end:1},{start:1,end:2}];
function event(midi,index,marks={}) {
  return {type:'pitched',sounding:midi,startQ:4*index,endQ:4*(index+1),staff:'1',voice:'1',fifths:0,transpose:shift,...marks};
}
function part(id,priority,notes) {
  return {id,name:id,priority,role:'lead',shift,staves:1,voices:1,unsafeFeatures:[],warnings:[],
    measureDetails:notes.map((note,index)=>({events:note===null?[]:[event(note,index,id==='可选持续层'?{tieStart:index===0,tieStop:index===1}:{})]}))};
}
function player(id,low,high) {
  return {id,name:id,unavailable:[],instruments:[{profile:id,name:id,role:'lead',low,high,poly:1,staves:1,chromatic:0,diatonic:0}]};
}
const model={measures,parts:[part('必保旋律','required',[60,84]),part('可选持续层','optional',[84,84])],durationQ:8};
const players=[player('拉弦席',50,80),player('吹管席',70,90)];
const initial=JSON.stringify({model,players});
const result=await compareOptionalLayers(model,players,{sections,maxMillis:5000});
assert.equal(result.baseline.totals.requiredMatched,1);
assert.equal(result.baseline.totals.optionalMatched,2);
assert.equal(result.baseline.totals.priorityConflicts,1);
assert.equal(result.candidate.totals.requiredMatched,2,'Removing the whole optional held layer releases the later required seat.');
assert.equal(result.candidate.totals.required,2);
assert.equal(result.candidate.totals.optional,2,'Omitted roles stay in the coverage denominator.');
assert.equal(result.candidate.totals.optionalMatched,0);
assert.equal(result.candidate.totals.unfilledOptional,2);
assert.equal(result.candidate.totals.tieGaps,0,'Whole-layer omission does not create an artificially cut tie.');
assert.deepEqual(result.report.omittedIds,['可选持续层']);
assert.equal(result.report.improved,true);
assert.equal(result.report.optimality,'not-certified');
assert.equal(result.report.allLayerSubsetsTested,true);
assert.equal(result.report.termination,'exhausted-candidates');
assert.equal(result.report.tested,2);
assert.equal(result.report.totalCandidates,'2');
for(const section of result.candidate.sections) {
  const assigned=section.mappings.filter(row=>row.status==='assigned');
  assert.equal(new Set(assigned.map(row=>row.player.id)).size,assigned.length,'No seat has simultaneous assignments.');
  assert(assigned.every(row=>row.source.bounds[0]>=row.target.low&&row.source.bounds[1]<=row.target.high));
  const omission=section.mappings.find(row=>row.source.id==='可选持续层');
  assert.equal(omission.status,'unfilled');
  assert.deepEqual(omission.reasons,['optional-layer-omitted']);
}
assert.equal(JSON.stringify({model,players}),initial,'Comparison does not mutate source or roster.');

const locked={...model,parts:model.parts.map(row=>({...row,priority:'required'}))};
const kept=await compareOptionalLayers(locked,players,{sections,maxMillis:5000});
assert.equal(kept.report.tested,1);
assert.equal(kept.report.improved,false);
assert.deepEqual(kept.report.omittedIds,[],'A required layer must never be removed.');

const limit=await compareOptionalLayers(model,players,{sections,maxPlans:1,maxMillis:5000});
assert.equal(limit.report.termination,'plan-budget');
assert.equal(limit.report.improved,false);
assert.equal(limit.report.allLayerSubsetsTested,false);
assert.strictEqual(limit.candidate,limit.baseline);
const expired=await compareOptionalLayers(model,players,{sections,maxMillis:0});
assert.equal(expired.report.termination,'time-budget');
assert.equal(expired.report.tested,1);
let stop=false;
const cancelled=await compareOptionalLayers(model,players,{sections,maxMillis:5000,yieldControl:async()=>{stop=true;},cancelled:()=>stop});
assert.equal(cancelled.report.termination,'cancelled');
assert.equal(cancelled.report.tested,1);

const impossible={...model,parts:[part('必保低音','required',[30,30])]};
const gap=await compareOptionalLayers(impossible,players,{sections,maxMillis:5000});
assert.equal(gap.candidate.totals.requiredMatched,0,'No new pitch or fictitious player is invented for an infeasible role.');
assert.equal(gap.report.improved,false);
await assert.rejects(()=>compareOptionalLayers(model,players,{sections,maxPlans:0}),/数量/u);
await assert.rejects(()=>compareOptionalLayers(model,players,{sections,maxMillis:10001}),/时长/u);
console.log('PASS: optional held-layer obstruction, full-chain omission, coverage denominators, required-layer protection, seat exclusivity, source immutability, plan/time/cancel budgets, and infeasible roles.');
