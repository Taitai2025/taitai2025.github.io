import { profiles } from '../instruments.mjs';
import { readRange } from '../musicxml.mjs';

export const configKind = 'guoyue-section-config';
export const maxPlayers = 64;
export const freshPlayer = (primary='qudi',name='') => ({
  name,primary,secondary:'',primaryLow:'',primaryHigh:'',secondaryLow:'',secondaryHigh:'',absences:'',pageStarts:'',
});

export const generalRoster = rows => rows.map(row=>({...row,absences:'',pageStarts:''}));

function items(text) {
  return String(text??'').normalize('NFKC').trim().split(/[\s,、，]+/u).filter(Boolean);
}
function bar(text,count) {
  if (!/^\d{1,6}$/u.test(text)) throw new Error('小节顺序请填写正整数。');
  const value=Number(text);
  if (value<1||value>count) throw new Error('小节顺序须在 1 至 '+count+' 之间。');
  return value;
}
export function positions(text,count) {
  return [...new Set(items(text).map(value=>bar(value,count)-1))].sort((a,b)=>a-b);
}
export function sectionsFrom(text,count) {
  const starts=[...new Set([0,...positions(text,count)])];
  if (starts.length>96) throw new Error('单份总谱最多划分 96 段。可以分乐章试配。');
  return starts.map((start,i)=>({start,end:starts[i+1]??count}));
}
export function absencesFrom(text,count) {
  const ranges=items(text).map(item=>{
    const bounds=item.replace(/[–—至]/gu,'-').split('-');
    if (bounds.length>2) throw new Error('缺席区间请写成 5-8 或 14。');
    const start=bar(bounds[0],count), end=bar(bounds[1]??bounds[0],count);
    if (end<start) throw new Error('缺席区间的结束小节须在起始小节之后。');
    return {start:start-1,end};
  }).sort((a,b)=>a.start-b.start);
  const merged=[];
  for (const range of ranges) {
    const previous=merged.at(-1);
    if (previous&&range.start<=previous.end) previous.end=Math.max(previous.end,range.end);
    else merged.push(range);
  }
  return merged;
}
export function makeRoster(rows,count) {
  return rows.map((row,i)=>{
    const name=row.name.trim()||'席位 '+(i+1);
    const instruments=[];
    try {
      if (!Object.hasOwn(profiles,row.primary) || row.primary===row.secondary) throw new Error('请选择主奏乐器，兼奏请选择另一件乐器。');
      for (const key of ['primary','secondary']) {
        const id=row[key];
        if (!id) continue;
        if (!Object.hasOwn(profiles,id)) throw new Error('有未识别的乐器。');
        const profile=profiles[id];
        const range=key+'Low';
        const highRange=key+'High';
        const low=row[range].trim()?readRange(row[range]):profile.low;
        const high=row[highRange].trim()?readRange(row[highRange]):profile.high;
        if (low===null||high===null||low>high) throw new Error(profile.name+'的实音范围无效。请填 C4 等音名或 MIDI 音高。');
        instruments.push({...profile,profile:id,low,high});
      }
      return {
        id:'seat-'+(i+1),name,instruments,unavailable:absencesFrom(row.absences,count),
        pageStarts:pagePositions(row.pageStarts,count),
      };
    } catch(error) {
      throw new Error(name+'：'+error.message);
    }
  });
}
export function pagePositions(text,count) {
  const bars=positions(text,count);
  if (bars.includes(0)) throw new Error('第一页开始处无需翻页。请填写第二页及之后的起始小节。');
  if (bars.length>96) throw new Error('每个席位最多核对 96 个分页位置。');
  return bars;
}
export function printedPageCuts(players,defaultStarts,assignedPlayerIds) {
  return players.flatMap(player=>{
    const individual=player.pageStarts.length>0;
    const bars=individual?player.pageStarts:assignedPlayerIds.has(player.id)?defaultStarts:[];
    return bars.map(beforeMeasure=>({
      beforeMeasure,playerId:player.id,scope:individual?'seat':'default',
    }));
  });
}
export function displaySeatNames(players) {
  const counts=new Map();
  for (const {name} of players) counts.set(name,(counts.get(name)??0)+1);
  return new Map(players.map(({id,name},i)=>[id,counts.get(name)>1?name+'（席位 '+(i+1)+'）':name]));
}
export function numberValue(raw,label,min,max,optional=false) {
  if (!raw && optional) return null;
  const value=Number(raw);
  if (!raw||!Number.isFinite(value)||value<min||value>max) throw new Error(label+'须在 '+min+' 至 '+max+' 之间。');
  return value;
}
export function readSettings(text) {
  let data;
  try { data=JSON.parse(text); } catch { throw new Error('设置文件不是有效的 JSON。'); }
  if (!data||data.kind!==configKind||data.version!==1||!Array.isArray(data.players)||data.players.length>maxPlayers) {
    throw new Error('请选择本工具导出的设置 JSON。');
  }
  const players=data.players.map(row=>{
    if (!row||!Object.hasOwn(profiles,row.primary)||(row.secondary&&!Object.hasOwn(profiles,row.secondary))) {
      throw new Error('设置中有无法识别的乐器。');
    }
    const textLimits={absences:180,pageStarts:350};
    return Object.fromEntries(Object.keys(freshPlayer()).map(key=>[key, typeof row[key]==='string'?row[key].slice(0,textLimits[key]??60):'']));
  });
  const fields=data.fields&&typeof data.fields==='object'?data.fields:{};
  return {players,fields,scoreKey:typeof data.scoreKey==='string'?data.scoreKey.slice(0,80):'',
    parts:Array.isArray(data.parts)?data.parts.slice(0,64):[]};
}

const demoParts=[
  ['P1','旋律',['G5','A5','F5','G5','E5','G5','A5','F5']],
  ['P2','中声部',['D4','E4','','','B3','C4','','']],
  ['P3','低音',['C3','D3','F3','G3','C3','E3','D3','F3']],
];
function demoMeasure(pitch,i,lead) {
  const initial='<attributes><divisions>1</divisions><key><fifths>0</fifths></key><time><beats>4</beats><beat-type>4</beat-type></time></attributes>';
  const print=i===4?'<print new-page="yes"/>':'';
  const mark=lead&&(i===0||i===4)?'<direction><direction-type><rehearsal>'+(!i?'A':'B')+'</rehearsal></direction-type></direction>':'';
  const tempo=lead&&!i?'<direction><direction-type><words>Moderato</words></direction-type><sound tempo="96"/></direction>':'';
  const rest=d=>'<note><rest/><duration>'+d+'</duration></note>';
  const beats=i===3||i===4?2:4;
  const playing=pitch?'<note><pitch><step>'+pitch[0]+'</step><octave>'+pitch[1]+'</octave></pitch><duration>'+beats+'</duration></note>':rest(beats);
  return '<measure number="'+(i+1)+'">'+print+(i===0?initial:'')+mark+tempo+(i===4?rest(2):'')+playing+(i===3?rest(2):'')+'</measure>';
}
export const demoXML='<?xml version="1.0"?><score-partwise version="4.0"><work><work-title>八小节分段示例</work-title></work><part-list>'+
  demoParts.map(([id,name])=>'<score-part id="'+id+'"><part-name>'+name+'</part-name></score-part>').join('')+'</part-list>'+
  demoParts.map(([id,,notes])=>'<part id="'+id+'">'+notes.map((pitch,i)=>demoMeasure(pitch,i,id==='P1')).join('')+'</part>').join('')+'</score-partwise>';
