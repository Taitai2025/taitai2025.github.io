import { solveAssignment } from './assignment.mjs';
import { parseMusicXML, readRange, midiName, evaluateMapping, exportMusicXML } from './musicxml.mjs';
import { readScoreFile } from './score-file.mjs';
import { profiles, presets, roles, sampleXML } from './instruments.mjs';
import { createProject, readProject, restoreProject, scoreFingerprint, projectSizeLimit } from './project.mjs';

const el=(id)=>document.getElementById(id);
const create=(tag,text='',classes='')=>{
  const node=document.createElement(tag);
  if (text) node.textContent=text;
  if (classes) node.className=classes;
  return node;
};
const state = {analysis:null,scoreKey:'',parts:[],seats:[],mappings:null,sourceLoaded:0,seatId:0,projectLoaded:0,pendingProject:null};

function status(id,message,type='') {
  const node=el(id);
  node.textContent=message;
  node.classList.toggle('work-error',type==='error');
  node.classList.toggle('work-success',type==='ok');
}
function selector(options,selected,label) {
  const select=create('select');
  select.setAttribute('aria-label',label);
  for(const [value,text] of Object.entries(options)) {
    const option=create('option',text); option.value=value; select.append(option);
  }
  select.value=selected;
  return select;
}
function field(name,input) {
  const container=create('label','','field');
  container.append(create('span',name),input);
  return container;
}
function flagStale() {
  state.mappings=null;
  el('result-wrap').hidden=true;
  el('solve').disabled=!state.analysis||!state.seats.length;
  status('result-status',state.analysis?'设置已经更新。计算后查看匹配结果。':'载入原谱并设置席位后，开始匹配。');
}
function marks(part) {
  const values=[];
  if (part.bounds) values.push(`${midiName(part.bounds[0])}–${midiName(part.bounds[1])} 实音`);
  if (part.unpitched) values.push(`${part.unpitched} 个无固定音高记谱`);
  if (part.type==='unknown') values.push('音域待确认');
  values.push(`${part.measures} 小节`);
  if (part.polyphony) values.push(`最多 ${part.polyphony} 个同时发声`);
  if (part.shift?.chromatic) values.push(`写音转实音 ${part.shift.chromatic>0?'+':''}${part.shift.chromatic} 半音`);
  return values.join(' · ');
}
function showSource() {
  const table=el('source-rows');
  const body=document.createDocumentFragment();
  for (const part of state.parts) {
    const tr=create('tr');
    const heading=create('th',part.name);
    heading.scope='row';
    heading.append(create('small',part.id));
    const detail=create('td',marks(part));
    if (part.warnings.length||part.unsafeFeatures.length) {
      const more=create('details');
      more.append(create('summary','源谱标记'));
      const flags=create('ul');
      for (const item of [...part.warnings,...part.unsafeFeatures]) flags.append(create('li',item));
      more.append(flags);
      detail.append(more);
    }
    const role=selector(roles,part.role,`${part.name}的作用`);
    const priority=selector({required:'必保留',optional:'可选'},part.priority,`${part.name}的优先级`);
    role.addEventListener('change',()=>{part.role=role.value;flagStale();});
    priority.addEventListener('change',()=>{part.priority=priority.value;flagStale();});
    const r=create('td'),p=create('td');
    r.append(role);p.append(priority);
    tr.append(heading,detail,r,p);
    body.append(tr);
  }
  table.replaceChildren(body);
  el('source-table-wrap').hidden=!state.analysis;
}
function clearSource() {
  state.analysis=null;
  state.scoreKey='';
  state.parts=[];
  el('save-project').disabled=true;
  el('score-identity').textContent='';
  showSource();
  flagStale();
}
function useProject(project) {
  const restored=restoreProject(project,state.scoreKey,state.parts);
  state.parts=restored.parts;
  state.seats=restored.seats;
  state.seatId=restored.lastSeatId;
  state.pendingProject=null;
  el('cancel-project').hidden=true;
  showSource();showSeats();flagStale();
  status('project-status','已恢复同一份原谱的席位、音域、角色和优先级。请重新计算匹配。','ok');
}
async function loadSource(read) {
  const requested=++state.sourceLoaded;
  const previousKey=state.scoreKey;
  const previousParts=new Map(state.parts.map(part=>[part.id,{role:part.role,priority:part.priority}]));
  clearSource();
  status('source-status','正在读取原谱。');
  try {
    const xml=await read();
    if(requested!==state.sourceLoaded) return;
    const analysis=parseMusicXML(xml);
    let scoreKey='',fingerprintError='';
    try { scoreKey=await scoreFingerprint(xml); } catch(error) { fingerprintError=error.message; }
    if(requested!==state.sourceLoaded) return;
    state.analysis=analysis;
    state.scoreKey=scoreKey;
    const sameSource=Boolean(scoreKey&&scoreKey===previousKey);
    state.parts=analysis.parts.map(part=>({...part,priority:'required',...(sameSource?previousParts.get(part.id):{})}));
    el('save-project').disabled=!scoreKey;
    el('score-identity').textContent=scoreKey?'谱件指纹 SHA-256：'+scoreKey:'';
    status('source-status',`已读取《${analysis.title}》 · ${analysis.parts.length} 个声部 · ${analysis.totalNotes.toLocaleString('zh-CN')} 个记谱事件`,'ok');
    if(fingerprintError) status('project-status',fingerprintError+' 编制匹配仍可使用，项目恢复暂不可用。','error');
    else if(state.pendingProject) {
      if(state.pendingProject.source.sha256===scoreKey) {
        try { useProject(state.pendingProject); } catch(error) { status('project-status',error.message,'error'); }
      } else {
        status('project-status',`待恢复项目《${state.pendingProject.source.title}》与这份谱不同，未套用项目设置。`,'error');
      }
    } else {
      status('project-status',sameSource?'已重新载入同一份原谱并保留声部设置。':'可下载项目设置，下次连同原谱一起打开。更换原谱后重新设定声部优先级。');
    }
  } catch(error) {
    if(requested!==state.sourceLoaded) return;
    clearSource();
    status('source-status',error.message,'error');
    return;
  }
  showSource();
  flagStale();
}
function newSeat(id) {
  const profile=profiles[id];
  return {id:++state.seatId,profile:id,role:profile.role,low:midiName(profile.low),high:midiName(profile.high)};
}
function applyPreset(preset) {
  state.seats=presets[preset].ids.map(newSeat);
  showSeats();
  flagStale();
}
function showSeats() {
  const display=document.createDocumentFragment();
  const opts=Object.fromEntries(Object.entries(profiles).map(([key,p])=>[key,`${p.name} · ${p.family}`]));
  state.seats.forEach((seat,index)=>{
    const row=create('div','','seat');
    row.append(create('p',`席位 ${seat.id}`,'seat-heading'));
    const instrument=selector(opts,seat.profile,`席位 ${seat.id} 乐器`);
    const low=create('input'),high=create('input');
    low.value=seat.low;high.value=seat.high;
    const role=selector(roles,seat.role,`席位 ${seat.id} 作用`);
    const remove=create('button','移除','button');
    remove.type='button';
    remove.setAttribute('aria-label',`移除席位 ${seat.id}`);
    instrument.addEventListener('change',()=>{
      seat.profile=instrument.value;
      const profile=profiles[seat.profile];
      seat.low=midiName(profile.low);seat.high=midiName(profile.high);seat.role=profile.role;
      low.value=seat.low;high.value=seat.high;role.value=seat.role;
      flagStale();
    });
    low.addEventListener('input',()=>{seat.low=low.value;flagStale();});
    high.addEventListener('input',()=>{seat.high=high.value;flagStale();});
    role.addEventListener('change',()=>{seat.role=role.value;flagStale();});
    remove.addEventListener('click',()=>{
      state.seats=state.seats.filter(item=>seat.id!==item.id);
      showSeats();flagStale();
    });
    row.append(field('乐器',instrument),field('实音下限',low),field('实音上限',high),field('预计作用',role),remove);
    display.append(row);
  });
  if (!state.seats.length) display.append(create('p','尚无席位，可添加乐器或载入编制预设。','meta'));
  el('seats').replaceChildren(display);
  el('add-seat').disabled=state.seats.length>=64;
}
function buildTargets() {
  const totals={},used={};
  state.seats.forEach(seat=>{totals[seat.profile]=(totals[seat.profile]||0)+1;});
  return state.seats.map((seat,index)=>{
    const profile=profiles[seat.profile], low=readRange(seat.low),high=readRange(seat.high);
    if (low===null||high===null||low>high) throw new Error(`席位 ${seat.id} 的实音音域无效。`);
    used[seat.profile]=(used[seat.profile]||0)+1;
    return {...profile,id:'seat-'+seat.id,seat:seat.id,low,high,role:seat.role,
      label:totals[seat.profile]>1?`${profile.name} ${used[seat.profile]}`:profile.name};
  });
}
function run() {
  try {
    const targets=buildTargets();
    const evaluations=state.parts.map(part=>targets.map(target=>evaluateMapping(part,target,part.role)));
    const solution=solveAssignment(evaluations.map(list=>list.map(e=>e.cost)),state.parts.map(p=>p.priority));
    const mappings=state.parts.map((source,i)=>{
      const j=solution.assigned[i];
      return {source,target:j===null?null:targets[j],evaluation:j===null?null:evaluations[i][j],candidates:evaluations[i]};
    });
    state.mappings=mappings;
    showResults(targets,solution,mappings);
  } catch(error) {
    el('result-wrap').hidden=true;
    status('result-status',error.message,'error');
  }
}
function showResults(targets,solution,mappings) {
  const required=mappings.filter(m=>m.source.priority==='required').length;
  const optional=mappings.length-required;
  const proposed=mappings.filter(m=>m.evaluation?.safe).length;
  const review=mappings.filter(m=>m.target&&!m.evaluation.safe).length;
  status('result-status',`必保留 ${solution.requiredMatched}/${required} · 可选 ${solution.optionalMatched}/${optional} · 可写入草稿 ${proposed} · 待复核映射 ${review}`);
  const body=document.createDocumentFragment();
  for (const row of mappings) {
    const {source,target,evaluation,candidates}=row;
    const tr=create('tr'),title=create('th',source.name),seat=create('td'),reviewCell=create('td','','explanation');
    title.scope='row';
    title.append(create('small',`${source.priority==='required'?'必保留':'可选'} · ${roles[source.role]}`));
    if (target) {
      seat.append(create('strong',target.label),create('small',`席位 ${target.seat} · ${midiName(target.low)}–${midiName(target.high)}`));
      if (evaluation.safe) {
        reviewCell.append(create('span',evaluation.changing?'可安全转换写音':'可按原记谱承接','pill'));
        if (evaluation.changing) {
          const diff=source.shift.chromatic-target.chromatic;
          reviewCell.append(create('small',`写音 ${diff>0?'+':''}${diff} 半音，实音保持。`));
        }
      } else {
        reviewCell.append(create('span','待手工复核','pill review'));
        const list=create('ul');
        evaluation.review.forEach(reason=>list.append(create('li',reason)));
        reviewCell.append(list);
      }
    } else {
      seat.append(create('span','未分配','pill neutral'));
      const feasible=candidates.filter(x=>x.cost!==null).length;
      if (feasible) reviewCell.append(create('p',`有 ${feasible} 个兼容席位，已分给其他声部。可补充席位或调低次要声部的优先级。`));
      else {
        const counts=new Map();
        candidates.flatMap(e=>e.reasons).forEach(x=>counts.set(x,(counts.get(x)||0)+1));
        const reasons=[...counts].sort((a,b)=>b[1]-a[1]).slice(0,3);
        const list=create('ul');
        reasons.forEach(([reason,n])=>list.append(create('li',`${reason}（${n} 个席位）`)));
        reviewCell.append(create('p','未发现可承接的席位。'),list);
      }
    }
    tr.append(title,seat,reviewCell);
    body.append(tr);
  }
  el('result-rows').replaceChildren(body);
  el('result-wrap').hidden=false;
  el('export-xml').disabled=proposed===0;
  status('export-status',`MusicXML 草稿保留所有源声部。只写入 ${proposed} 个通过安全检查的映射，其余按原谱保留。`);
}
function fileName(suffix) {
  return `国乐谱汇_${state.analysis.title.replace(/[\\/:*?"<>|]/g,'_').slice(0,48)}_${suffix}`;
}
function download(content,name,type) {
  const url=URL.createObjectURL(new Blob([content],{type}));
  const a=create('a');a.download=name;a.href=url;document.body.append(a);a.click();a.remove();
  setTimeout(()=>URL.revokeObjectURL(url),3000);
}
function rowsForExport() {
  return state.mappings.map(({source,target,evaluation,candidates})=>({
    id:source.id,source:source.name,role:roles[source.role],priority:source.priority==='required'?'必保留':'可选',
    sourceRange:source.bounds?.map(midiName).join('–')||'待确认',
    target:target?.label||'',seat:target?.seat||'',cost:evaluation?.cost??'',
    outcome:!target?'未分配':evaluation.safe?evaluation.changing?'可安全转换写音':'可按原记谱承接':'待手工复核',
    notes:evaluation ? evaluation.review.join('；') : [...new Set(candidates.flatMap(x=>x.reasons))].join('；') || '兼容席位已分配给其他声部',
  }));
}
const escaped=(value)=>{
  const normalized=String(value);
  const safe=/^[=+\-@\t\r\n]/.test(normalized)?"'"+normalized:normalized;
  return '"'+safe.replaceAll('"','""')+'"';
};
el('export-csv').addEventListener('click',()=>{
  if (!state.mappings) return;
  const fields={id:'声部编号',source:'原声部',role:'声部作用',priority:'优先级',sourceRange:'实音音域',target:'目标乐器',seat:'席位',cost:'匹配代价',outcome:'结论',notes:'待复核事项'};
  const prefix=Object.values(fields).map(escaped).join(',');
  const lines=rowsForExport().map(row=>Object.keys(fields).map(key=>escaped(row[key])).join(','));
  download('\ufeff'+[prefix,...lines].join('\r\n'),fileName('编配核对.csv'),'text/csv;charset=utf-8');
});
el('export-json').addEventListener('click',()=>{
  if (!state.mappings) return;
  download(JSON.stringify({kind:'guoyue-arrange-report',version:1,score:state.analysis.title,sourceSha256:state.scoreKey,targets:buildTargets(),assignments:rowsForExport()},null,2),
    fileName('编配方案.json'),'application/json;charset=utf-8');
});
el('export-xml').addEventListener('click',()=>{
  if (!state.mappings) return;
  try {
    const result=exportMusicXML(state.analysis,state.mappings);
    download(result.xml,fileName('编配草稿.musicxml'),'application/vnd.recordare.musicxml+xml');
    status('export-status',`已导出并回读核对 ${result.changed} 个映射，其中 ${result.rewritten} 个转换了写音。全谱实音、拍位与时值校验通过。`,'ok');
  } catch(error) {
    status('export-status',error.message,'error');
  }
});
el('source-file').addEventListener('change',event=>{
  const file=event.target.files[0];
  if (!file) return;
  loadSource(()=>readScoreFile(file));
});
el('demo').addEventListener('click',()=>{
  el('source-file').value='';
  loadSource(()=>sampleXML);
});
el('save-project').addEventListener('click',()=>{
  if(!state.analysis||!state.scoreKey) return;
  try {
    const project=createProject({scoreKey:state.scoreKey,title:state.analysis.title,parts:state.parts,seats:state.seats,lastSeatId:state.seatId});
    download(JSON.stringify(project,null,2),fileName('项目设置.json'),'application/json;charset=utf-8');
    status('project-status','项目设置已下载。文件不包含音符，下次请同时准备原来的 MusicXML 或 MXL。','ok');
  } catch(error) {status('project-status',error.message,'error');}
});
el('load-project').addEventListener('change',async event=>{
  const field=event.currentTarget,file=field.files[0];
  if(!file) return;
  const requested=++state.projectLoaded;
  try {
    if(file.size>projectSizeLimit) throw new Error('项目文件过大，请选择 250 KB 以内的设置文件。');
    const project=readProject(await file.text());
    if(requested!==state.projectLoaded) return;
    if(state.analysis&&state.scoreKey===project.source.sha256) useProject(project);
    else {
      state.pendingProject=project;
      el('cancel-project').hidden=false;
      status('project-status',`已暂存项目《${project.source.title}》。请选择对应的原始 MusicXML/MXL，指纹一致后恢复设置。当前设置保持不变。`);
    }
  } catch(error) {
    if(requested===state.projectLoaded) status('project-status',error.message,'error');
  } finally {
    if(requested===state.projectLoaded) field.value='';
  }
});
el('cancel-project').addEventListener('click',()=>{
  state.projectLoaded++;
  state.pendingProject=null;
  el('cancel-project').hidden=true;
  status('project-status','已取消等待恢复的项目。当前设置保持不变。');
});
for(const preset of Object.keys(presets)) el(`preset-${preset}`).addEventListener('click',()=>applyPreset(preset));
el('add-seat').addEventListener('click',()=>{
  if(state.seats.length>=64) return;
  state.seats.push(newSeat('qudi'));
  showSeats();flagStale();
  el('seats').querySelector('.seat:last-child select')?.focus();
});
el('solve').addEventListener('click',run);
applyPreset('mixed');
