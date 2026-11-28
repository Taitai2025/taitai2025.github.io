import assert from 'node:assert/strict';
import {
  createProject, readProject, restoreProject, scoreFingerprint, projectSizeLimit,
} from '../scores/tools/arrange/project.mjs';

const xmlA = '<score-partwise><work><work-title>同名曲目</work-title></work></score-partwise>';
const xmlB = xmlA.replace('</work>', '<work-number>2</work-number></work>');
const keyA = await scoreFingerprint(xmlA), keyB = await scoreFingerprint(xmlB);
assert.match(keyA, /^[a-f0-9]{64}$/);
assert.notEqual(keyA, keyB, 'Same title does not mean the same source score.');
assert.equal(keyA, await scoreFingerprint(xmlA), 'Decoded XML from MXL/XML has one identity.');

const parts = [
  {id:'P1',name:'主旋律',role:'lead',priority:'required',notes:12},
  {id:'P2',name:'低音',role:'bass',priority:'optional',notes:8},
];
const seats = [
  {id:2,profile:'qudi',role:'lead',low:'G4',high:'D6'},
  {id:7,profile:'cello',role:'bass',low:'C2',high:'E5'},
];
const project = createProject({scoreKey:keyA,title:'同名曲目',parts,seats,lastSeatId:10});
assert.deepEqual(Object.keys(project).sort(), ['kind','lastSeatId','parts','seats','source','version']);
assert(!JSON.stringify(project).includes('notes'), 'Project contains no note content or trusted result.');
const imported = readProject(JSON.stringify({...project,assignments:[{safe:true}],script:'untrusted'}));
assert.deepEqual(imported, project, 'Unknown fields and purported solver results are discarded.');
const current = parts.map(part => ({...part,priority:'required',role:'any',notes:part.notes+100}));
const restored = restoreProject(imported,keyA,current);
assert.deepEqual(restored.seats.map(seat=>seat.id), [2,7]);
assert.equal(restored.lastSeatId,10, 'A removed seat ID is not recycled after restore.');
assert.deepEqual(restored.parts.map(part=>[part.role,part.priority,part.notes]), [['lead','required',112],['bass','optional',108]]);
assert.deepEqual(current.map(part=>part.priority), ['required','required'], 'Restoration is atomic and does not mutate parsed source.');
restored.seats[0].low='C4';
assert.equal(imported.seats[0].low,'G4','Restored settings are independent copies.');

assert.throws(()=>restoreProject(project,keyB,current),/指纹不一致/u);
assert.throws(()=>restoreProject(project,'',current),/指纹不一致/u);
assert.throws(()=>restoreProject(project,keyA,current.slice(1)),/声部清单/u);
assert.throws(()=>restoreProject(project,keyA,[current[0],{...current[1],id:'OTHER'}]),/原声部编号/u);
assert.throws(()=>restoreProject(project,keyA,[current[0],current[0]]),/原声部编号/u);
assert.throws(()=>readProject('not JSON'),/有效的 JSON/u);
assert.throws(()=>readProject(' '.repeat(projectSizeLimit+1)),/过大/u);
assert.throws(()=>readProject(JSON.stringify({kind:'guoyue-arrange-report',version:1})),/结果报告/u);
assert.throws(()=>readProject(JSON.stringify({...project,version:999})),/项目设置/u);
assert.throws(()=>readProject(JSON.stringify({...project,source:{sha256:'short',title:'x'}})),/指纹/u);
assert.throws(()=>readProject(JSON.stringify({...project,seats:[seats[0],seats[0]]})),/席位编号/u);
assert.throws(()=>readProject(JSON.stringify({...project,lastSeatId:1})),/编号计数/u);
assert.throws(()=>readProject(JSON.stringify({...project,seats:[{...seats[0],profile:'__proto__'}]})),/乐器/u);
assert.throws(()=>readProject(JSON.stringify({...project,seats:[{...seats[0],low:'G7',high:'C4'}]})),/音域/u);
assert.throws(()=>readProject(JSON.stringify({...project,parts:[parts[0],parts[0]]})),/原声部编号/u);
assert.throws(()=>readProject(JSON.stringify({...project,parts:[{...parts[0],priority:'verified'}]})),/优先级/u);
assert.throws(()=>readProject(JSON.stringify({...project,seats:Array.from({length:65},(_,i)=>({...seats[0],id:i+1})),lastSeatId:65})),/64/u);

console.log('PASS: source identity, atomic matching restore, stable seat IDs, result stripping, malformed inputs, bounded files, and independent copies.');
