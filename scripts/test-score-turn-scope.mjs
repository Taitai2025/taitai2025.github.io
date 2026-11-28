import assert from 'node:assert/strict';
import {analyzePageTurns} from '../scores/tools/arrange/turn-windows.mjs';

const measures = Array.from({length:4}, (_, i) => ({
  startQ:4*i,
  endQ:4*(i+1),
  repeatForward:i===0,
  repeatBackward:i===3 ? {times:2} : null
}));
const seatIds = ['seat-1','seat-2','seat-3'];
const parts = seatIds.map((id, index) => ({
  id,
  measureDetails:measures.map((measure, i) => ({
    newPage:i===1 && index===0,
    events:[{startQ:measure.startQ,endQ:measure.startQ+1}]
  }))
}));
const plan = {sections:[{start:0,end:4,mappings:parts.map(source => ({
  source,
  player:{id:source.id},
  status:'assigned',
  target:{profile:'qudi'}
}))}]};
const model = {measures,parts,durationQ:16};
const options = {tempoOverride:{bpm:60,confirmed:true},minimumSeconds:2};
const analyze = candidates => analyzePageTurns(model,plan,{...options,candidates}).candidates;
const pairs = rows => rows.map(row=>[row.playerId,row.beforeMeasure]);

const scoped=analyze([{playerId:'seat-1',beforeMeasure:1},{playerId:'seat-2',beforeMeasure:2}]);
assert.deepEqual(pairs(scoped),[['seat-1',1],['seat-2',2]]);
for (const row of scoped) {
  assert.equal(row.status,'possible');
  assert.equal(row.source,'manual');
  assert.equal(row.confirmed,true);
  assert.equal(row.visits.length,3);
  assert.equal(row.availableSeconds,3);
  assert.deepEqual(row.reasons,[]);
}
const global=analyze([{beforeMeasure:1},{beforeMeasure:2}]);
assert.equal(global.length,6);
assert(global.every(row=>row.status==='review' && row.reasons.includes('several-page-boundaries')));
const hint=analyze(undefined);
assert.deepEqual(pairs(hint),[['seat-1',1]]);
assert.equal(hint[0].confirmed,false);
assert(hint[0].reasons.includes('printed-layout-unconfirmed'));
const deleted=analyze([{playerId:'not-in-current-roster',beforeMeasure:1}]);
assert.equal(deleted[0].status,'review');
assert.deepEqual(deleted[0].reasons,['player-unassigned']);

console.log('PASS: per-seat breaks, independent repeat crossings, shared breaks, XML hints, and stale player diagnostics');

const mixed=analyzePageTurns(model,plan,{...options,includeEmbedded:true,candidates:[{
  beforeMeasure:2,playerId:'seat-2',scope:'seat',
}]}).candidates;
assert.deepEqual(pairs(mixed),[['seat-1',1],['seat-2',2]]);
assert.deepEqual(mixed.map(row=>[row.source,row.confirmed]),[['embedded',false],['manual',true]]);
assert.equal(mixed[1].scope,'seat');

const overridden=analyzePageTurns(model,plan,{...options,includeEmbedded:true,candidates:[{
  beforeMeasure:2,playerId:'seat-1',scope:'seat',
}]}).candidates;
assert.deepEqual(pairs(overridden),[['seat-1',2]]);
assert.equal(overridden[0].scope,'seat');

const {
  configKind,displaySeatNames,freshPlayer,generalRoster,makeRoster,pagePositions,printedPageCuts,readSettings,
}=await import('../scores/tools/arrange/sections/setup.mjs');
const rows=[
  {...freshPlayer('qudi','同名'),absences:'3-4',pageStarts:'4'},
  freshPlayer('altoSheng','同名'),
  freshPlayer('pipa'),
];
const roster=makeRoster(rows,8);
assert.deepEqual(roster[0].unavailable,[{start:2,end:4}]);
assert.deepEqual(roster[0].pageStarts,[3]);
assert.deepEqual([...displaySeatNames(roster).values()],['同名（席位 1）','同名（席位 2）','席位 3']);
assert.deepEqual(printedPageCuts(roster,[6],new Set(['seat-1','seat-2'])),[
  {beforeMeasure:3,playerId:'seat-1',scope:'seat'},
  {beforeMeasure:6,playerId:'seat-2',scope:'default'},
]);
assert.equal(readSettings(JSON.stringify({kind:configKind,version:1,players:[{name:'旧设置',primary:'qudi'}]})).players[0].pageStarts,'');
assert.equal(generalRoster(rows)[0].pageStarts,'');
assert.equal(generalRoster(rows)[0].absences,'');
assert.equal(rows[0].pageStarts,'4');
assert.throws(()=>pagePositions('1',8),/第一页/u);
assert.throws(()=>pagePositions('9',8),/1 至 8/u);
assert.deepEqual(pagePositions('７, 5，5',8),[4,6]);
console.log('PASS: mixed embedded and manual precedence, old settings, score-bound ranges, exact seat identification');
