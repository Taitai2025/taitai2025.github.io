import { profiles,roles } from '../instruments.mjs';
import { midiName } from '../musicxml.mjs';

export const el=id=>document.getElementById(id);
export const priorityLabels={required:'必保留',optional:'可选'};
const instrumentLabels=Object.fromEntries(Object.entries(profiles).map(([id,p])=>[id,p.name+' · '+p.family]));

export function make(tag,text='',css='') {
  const node=document.createElement(tag);
  node.textContent=text;
  if (css) node.className=css;
  return node;
}
export function status(id,text,error=false) {
  const node=el(id);
  node.textContent=text;
  node.classList.toggle('segment-error',error);
}
function label(text,input) {
  const node=make('label',text,'field');
  node.append(input);
  return node;
}
function select(options,value,change) {
  const node=make('select');
  for (const [key,title] of Object.entries(options)) {
    const option=make('option',title);option.value=key;node.append(option);
  }
  node.value=value;
  node.addEventListener('change',()=>change(node.value));
  return node;
}
function textInput(value,placeholder,change,max=60) {
  const node=make('input');
  node.type='text';node.value=value;node.placeholder=placeholder;node.maxLength=max;
  node.addEventListener('input',()=>change(node.value));
  return node;
}
export function table(titles,rows,caption) {
  const wrap=make('div','','table-wrap'), display=make('table','','segment-table'), head=make('thead'), body=make('tbody');
  wrap.tabIndex=0;
  wrap.setAttribute('role','region');wrap.setAttribute('aria-label',caption);
  const heading=make('tr');
  for (const title of titles) {
    const cell=make('th',title);cell.scope='col';heading.append(cell);
  }
  head.append(heading);
  for (const row of rows) {
    const tr=make('tr');
    row.forEach((value,i)=>{
      const cell=value instanceof Node?value:make(i===0?'th':'td',String(value??''));
      if (i===0) cell.scope='row';tr.append(cell);
    });
    body.append(tr);
  }
  const description=make('caption',caption);
  description.hidden=true;
  display.append(description,head,body);wrap.append(display);
  return wrap;
}
export function renderParts(parts,invalidated) {
  const rows=parts.map(part=>{
    const role=select(roles,part.role,value=>{part.role=value;invalidated();});
    const priority=select(priorityLabels,part.priority,value=>{part.priority=value;invalidated();});
    role.setAttribute('aria-label',part.name+'的功能');priority.setAttribute('aria-label',part.name+'的优先级');
    const r=make('td'),p=make('td');r.append(role);p.append(priority);
    const range=part.bounds?part.bounds.map(midiName).join('–'):'待核';
    return [part.name,range,r,p];
  });
  el('part-settings').replaceChildren(table(['原声部','实音范围','功能','优先级'],rows,'声部设置'));
}
export function renderPlayers(players,invalidated,repaint,scoreReady) {
  const rows=players.map((player,i)=>{
    const fields=make('div','','segment-fields');
    const set=(key,value)=>{player[key]=value;invalidated();};
    fields.append(label('席位备注',textInput(player.name,'席位 '+(i+1),v=>set('name',v))));
    for (const [key,title] of [['primary','主奏'],['secondary','兼奏']]) {
      const names=key==='primary'?instrumentLabels:{'':'无',...instrumentLabels};
      const choice=select(names,player[key],v=>{player[key]=v;player[key+'Low']='';player[key+'High']='';repaint();});
      fields.append(label(title+'乐器',choice));
      const profile=profiles[player[key]];
      if (!profile||profile.unpitched) continue;
      for (const [edge,text] of [['Low','下限'],['High','上限']]) {
        const field=key+edge;
        fields.append(label(title+text,textInput(player[field],midiName(profile[edge.toLowerCase()]),v=>set(field,v),12)));
      }
    }
    const absence=textInput(player.absences,'如 5-8, 14',v=>set('absences',v),180);
    absence.disabled=!scoreReady;
    fields.append(label('缺席小节顺序',absence));
    const row=make('fieldset','','player-fields'), buttons=make('div','','actions');
    const pageBreaks=make('details','','seat-page-breaks');
    const cuts=textInput(player.pageStarts,'如 9, 24',v=>set('pageStarts',v),350);
    cuts.disabled=!scoreReady;
    pageBreaks.open=Boolean(player.pageStarts);
    pageBreaks.append(make('summary','本席位的实际分页'),label('新页起始小节顺序',cuts),
      make('p','填写后覆盖本席位的默认分页。','meta'));
    const remove=make('button','移除','button');remove.type='button';remove.setAttribute('aria-label','移除演奏员 '+(i+1));
    remove.addEventListener('click',()=>{players.splice(i,1);repaint();});
    buttons.append(remove);row.append(make('legend','演奏员 '+(i+1)),fields,pageBreaks,buttons);
    return row;
  });
  el('player-settings').replaceChildren(...(rows.length?rows:[make('p','可先添加一位演奏员，或载入上面的示例。','meta')]));
}
const reasonLabel={
  incompatible:'实音音域或发声能力不匹配',unavailable:'没有可用席位',absence:'演奏员本段缺席',
  'tie-continuation':'需保留原延音的演奏员', 'tie-forward':'后续延音没有同一席位',
  'switch-window':'兼奏休止太短', 'player-conflict':'席位已在本段安排其他声部',
  'timing-unverified':'小节时值待核',
  'printed-layout-unconfirmed':'需与实际打印分页核对','tempo-unconfirmed':'演奏速度待核',
  'repeat-unconfirmed':'反复走向待核','jump-ambiguous':'跳转走向待核',
  'tempo-unverified':'演奏速度待核','repeat-tempo-unverified':'反复处速度待核',
  'repeat-order-unverified':'反复或跳转的演奏顺序待核','rhythm-unverified':'源谱时值待核',
  'missing-notes':'声部的谱面信息不足','unresolved-tie':'延音接续待核','unresolved-sustain':'持续音结束时间待核',
  'attack-or-release-unverified':'起音或收音时间待核','sustained-across-page':'有持续音跨越分页',
  'no-silence':'分页处没有连续休止','no-playing-notes':'该席位在此无演奏片段',
  'several-page-boundaries':'同一休止跨过多个分页位置','instrument-change-in-window':'同时需要在休止内换乐器',
  'boundary-not-visited':'实际演奏顺序未经过此分页','player-unassigned':'分页处席位待核',
  'assignment-plan-incomplete':'分工未覆盖整份总谱',
};
export function describe(reasons) {
  return (reasons??[]).map(reason=>typeof reason==='string'?(reasonLabel[reason]??reason):
    (reasonLabel[reason?.code]??reason?.message??reason?.code??'')).filter(Boolean);
}
export function displayNumber(value) {
  return Number.isFinite(value)?Number(value.toFixed(2)).toLocaleString('zh-CN'):'待核';
}
export function downloadCsv(rows) {
  const quote=value=>{
    const text=String(value??'');
    const safe=/^\s*[=+\-@]|^[\t\r\n]/u.test(text)?"'"+text:text;
    return '"'+safe.replace(/"/gu,'""')+'"';
  };
  return '\ufeff'+rows.map(row=>row.map(quote).join(',')).join('\r\n')+'\r\n';
}
