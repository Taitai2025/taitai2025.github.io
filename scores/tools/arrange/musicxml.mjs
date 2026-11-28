import { assembleScoreClock } from './score-clock.mjs';

const steps = ['C', 'D', 'E', 'F', 'G', 'A', 'B'];
const stepPitch = [0, 2, 4, 5, 7, 9, 11];
const accidentalNames = new Map([
  [-2, 'flat-flat'], [-1, 'flat'], [0, 'natural'], [1, 'sharp'], [2, 'double-sharp'],
]);
const mod = (n, m) => ((n % m) + m) % m;
const children = (node, name) => [...(node?.children || [])].filter(child => !name || child.localName === name);
const child = (node, name) => children(node, name)[0];
const value = (node, name) => child(node, name)?.textContent.trim() || '';
const number = (node, name, fallback = NaN) => value(node, name) === '' ? fallback : Number(value(node, name));
const zero = () => ({ chromatic: 0, diatonic: 0, known: true });
const signature = ({ chromatic, diatonic }) => `${chromatic}/${diatonic}`;
const EPS = 1e-8;
const MAX_NOTES = 120000;
const specialized = new Set(['accidental-mark','harmonic','bends','bend','tablature','scordatura','instrument-change','string']);
const sustained = new Set(['tie','tied']);
const quarterUnits = new Map([
  ['maxima',32],['long',16],['breve',8],['whole',4],['half',2],['quarter',1],
  ['eighth',1/2],['16th',1/4],['32nd',1/8],['64th',1/16],['128th',1/32],
  ['256th',1/64],['512th',1/128],['1024th',1/256],
]);
const flowWords = /\bd\s*\.\s*[cs](?:\s*\.|\b)|\b(?:da\s+capo|dal\s+segno|to\s+coda|al\s+fine|al\s+coda)\b|^\s*(?:fine|coda|segno)\s*[.!]?\s*$|从头反复|到尾声|跳至|跳到|返回记号|返回开头/iu;
const tempoWords = /\b(?:rit(?:ardando|enuto)?|rall(?:entando)?|accel(?:erando)?|allarg(?:ando)?|rubato|stringendo|smorz(?:ando)?|meno\s+mosso|pi[uù]\s+mosso|a\s+tempo|tempo\s+(?:primo|i))(?=[\s.,;]|$)|渐快|渐慢|自由速度|回原速|恢复原速/iu;
const tempoLabel = /^(?:grave|largo|larghetto|lento|adagio|adagietto|andante|andantino|moderato|allegretto|allegro|vivace|vivacissimo|presto|prestissimo)(?=[\s.,;]|$)|庄板|广板|慢板|柔板|行板|中板|小快板|快板|急板/iu;

function recordNoteFeatures(note, features) {
  const todo=children(note);
  while(todo.length) {
    const node=todo.pop();
    if(specialized.has(node.localName)) features.add('特殊音高或乐器专用记号');
    if(sustained.has(node.localName)) features.add('跨音保持线');
    if(node.localName==='notations'||node.localName==='ornaments'||node.localName==='technical') todo.push(...children(node));
  }
}

function timingIssue(bar, onset, kind, reason, sustained=false) {
  bar.timingIssues.push({onset,kind,reason,sustained});
}

function offsetQ(element,divisions) {
  if (!element) return 0;
  const raw=element.textContent.trim();
  const offset=Number(raw)/divisions;
  return divisions && raw!=='' && Number.isFinite(offset) ? offset : null;
}

function metronomeTempo(node) {
  if (child(node,'metronome-note')||child(node,'beat-unit-tied')||children(node,'beat-unit').length!==1) return null;
  const unit=quarterUnits.get(value(node,'beat-unit'));
  const raw=value(node,'per-minute');
  const bpm=unit*(2-2**-children(node,'beat-unit-dot').length)*Number(raw);
  return /^\d+(?:\.\d+)?$/.test(raw) && Number.isFinite(bpm) && bpm>0 ? bpm : null;
}

function readSound(node,cursor,divisions,directionOffset,bar) {
  if (['dacapo','dalsegno','tocoda','segno','coda','fine','forward-repeat'].some(attribute=>{
    const mark=node.getAttribute(attribute);
    return mark!==null && mark!=='no';
  })) bar.flowIssues.push('含返始、返记号、尾声、终止点或未写出的反复指令');
  if (node.hasAttribute('time-only')) bar.flowIssues.push('含只适用于指定反复遍次的播放指令');
  const ownOffset=child(node,'offset');
  const offset=offsetQ(ownOffset??directionOffset,divisions);
  const onset=cursor+(offset??0);
  const swing=child(node,'swing');
  if (swing) bar.swingMarks.push({onset:offset===null ? 0 : onset,swung:offset===null || !child(swing,'straight')});
  if (!node.hasAttribute('tempo')) return null;
  const bpm=Number(node.getAttribute('tempo'));
  if (offset===null || !Number.isFinite(bpm) || bpm<=0 || node.hasAttribute('time-only')) {
    timingIssue(bar,onset,'tempo','缺少可用的固定速度',true);
    return null;
  }
  const mark={onset,bpm,source:'sound'};
  bar.tempoMarks.push(mark);
  return mark;
}

function readDirection(node,cursor,divisions,bar) {
  const offset=child(node,'offset');
  const delta=offsetQ(offset,divisions);
  const onset=cursor+(delta??0);
  const sounds=children(node,'sound');
  const playbackMarks=sounds.map(sound=>readSound(sound,cursor,divisions,offset?.getAttribute('sound')==='yes'?offset:null,bar)).filter(Boolean);
  const hasPlaybackTempo=sounds.some(sound=>sound.hasAttribute('tempo'));
  for (const type of children(node,'direction-type')) {
    for (const mark of children(type)) {
      switch (mark.localName) {
        case 'rehearsal': {
          const label=mark.textContent.trim();
          if (label) bar.rehearsalMarks.push({label,onset});
          break;
        }
        case 'segno':
        case 'coda':
          bar.flowIssues.push('含返记号或尾声标记');
          break;
        case 'words': {
          const words=mark.textContent.trim().normalize('NFKC');
          if (!words.includes('已展开') && flowWords.test(words)) bar.flowIssues.push('含文字跳转指令');
          if (tempoWords.test(words)) timingIssue(bar,onset,'tempo-variation','文字速度变化需要排练确认',true);
          else if (tempoLabel.test(words)) bar.timingIssues.push({
            onset,kind:'tempo',reason:'速度术语缺少可确认的数值',sustained:true,coveredByTempoMark:true,
          });
          break;
        }
        case 'metronome': {
          const bpm=metronomeTempo(mark);
          if (delta===null || bpm===null) {
            timingIssue(bar,onset,'tempo-variation','节拍器标记的速度或拍位需要确认',true);
          } else if (!hasPlaybackTempo) {
            bar.tempoMarks.push({onset,bpm,source:'metronome'});
          } else if (playbackMarks.some(playback=>Math.abs(playback.bpm-bpm)>EPS)) {
            timingIssue(bar,Math.min(onset,...playbackMarks.map(playback=>playback.onset)),'tempo','谱面与播放速度互相冲突',true);
          }
          break;
        }
      }
    }
  }
}

function readBarline(node,cursor,bar) {
  const location=node.getAttribute('location')||'right';
  const repeat=child(node,'repeat');
  if (repeat) {
    const direction=repeat.getAttribute('direction');
    if (repeat.getAttribute('after-jump')==='yes') bar.flowIssues.push('含仅在跳转后生效的反复指令');
    if (direction==='forward' && location==='left') bar.repeatForward=true;
    else if (direction==='backward' && location==='right') {
      const raw=repeat.getAttribute('times');
      const times=raw===null ? 2 : Number(raw);
      if (!Number.isSafeInteger(times) || times<1) bar.flowIssues.push('反复次数无法识别');
      else if (bar.repeatBackward && bar.repeatBackward.times!==times) bar.flowIssues.push('同小节的反复次数不一致');
      else bar.repeatBackward={times};
    } else {
      bar.flowIssues.push('反复线不在预期的小节边界');
    }
  }
  const ending=child(node,'ending');
  if (ending) {
    const type=ending.getAttribute('type');
    const number=ending.getAttribute('number')??'';
    if (type==='start' && location==='left' || ['stop','discontinue'].includes(type) && location==='right') {
      bar.endings.push({type,number,location});
    } else {
      bar.flowIssues.push('一、二房标记不在预期的小节边界');
    }
  }
  if (child(node,'segno')||child(node,'coda')||node.hasAttribute('segno')||node.hasAttribute('coda')) {
    bar.flowIssues.push('含返记号或尾声标记');
  }
  if (child(node,'fermata')) timingIssue(bar,location==='left'?0:cursor,'played-timing','延长号改变实际时长');
}

function noteTiming(note,mark,onset,duration,bar) {
  const ties=children(note,'tie');
  const tied=children(note,'notations').flatMap(notation=>children(notation,'tied'));
  const tieTypes=new Set([...ties,...tied].map(item=>item.getAttribute('type')));
  const tieConditional=ties.some(item=>item.hasAttribute('time-only'));
  if (tieConditional || note.hasAttribute('time-only')) bar.flowIssues.push('含只适用于指定反复遍次的音符或延音线');
  const grace=child(note,'grace');
  const performanceModified=['attack','release'].some(attribute=>note.hasAttribute(attribute)) ||
    Boolean(grace && ['steal-time-previous','steal-time-following','make-time'].some(attribute=>grace.hasAttribute(attribute)));
  if (performanceModified) timingIssue(bar,onset,'played-timing','演奏起音或收音位置需复核');
  const fermata=children(note,'notations').some(notation=>child(notation,'fermata'));
  if (fermata) timingIssue(bar,onset+(duration??0),'played-timing','延长号改变实际时长');
  let pitchKey=null;
  if (mark.localName==='unpitched') {
    const displayStep=value(mark,'display-step'), displayOctave=value(mark,'display-octave');
    const instrument=children(note,'instrument').map(item=>item.getAttribute('id')).filter(Boolean).sort().join(',');
    if (instrument || displayStep && displayOctave) pitchKey=`u:${instrument}:${displayStep}:${displayOctave}`;
  }
  return {tieStart:tieTypes.has('start')||tieTypes.has('continue'),tieStop:tieTypes.has('stop')||tieTypes.has('continue'),
    tieConditional,letRing:tieTypes.has('let-ring'),pitchKey,performanceModified,fermata,rest:mark.localName==='rest'};
}

export function midiName(midi) {
  if (!Number.isFinite(midi)) return '待确认';
  const names = ['C','C♯','D','E♭','E','F','F♯','G','A♭','A','B♭','B'];
  return `${names[mod(midi,12)] ?? '?'}${Math.floor(midi/12)-1}`;
}

export function readRange(value) {
  const text = String(value).trim();
  if (/^\d{1,3}$/.test(text)) {
    const midi = Number(text);
    return midi <= 127 ? midi : null;
  }
  const m = text.match(/^([A-Ga-g])([#♯b♭]?)(-1|[0-9])$/);
  if (!m) return null;
  const accidental = /[#♯]/.test(m[2]) ? 1 : /[b♭]/.test(m[2]) ? -1 : 0;
  const pitch = 12 * (Number(m[3]) + 1) + stepPitch[steps.indexOf(m[1].toUpperCase())] + accidental;
  return pitch >= 0 && pitch <= 127 ? pitch : null;
}

function readPitch(pitch) {
  const letter = steps.indexOf(value(pitch,'step'));
  const alter = number(pitch,'alter',0);
  const octave = number(pitch,'octave');
  if (letter < 0 || !Number.isInteger(alter) || !Number.isInteger(octave) || octave < 0 || octave > 9) return null;
  return { letter, alter, octave, midi:12*(octave+1)+stepPitch[letter]+alter };
}

function readTranspose(node) {
  const chromatic = number(node,'chromatic');
  const octave = number(node,'octave-change',0);
  const diatonic = number(node,'diatonic',chromatic===0 ? 0 : NaN);
  return {
    chromatic:chromatic+12*octave, diatonic:Number.isInteger(diatonic)?diatonic+7*octave:null,
    known:Number.isInteger(chromatic)&&Number.isInteger(octave)&&!child(node,'double'),
  };
}

function timingMeter(node) {
  const beats = children(node,'beats');
  const types = children(node,'beat-type');
  if (!beats.length || beats.length!==types.length) return null;
  let ticks = 0;
  for (let i=0;i<beats.length;i++) {
    const counts = beats[i].textContent.trim().split('+').map(Number);
    const base = Number(types[i].textContent);
    if (!counts.every(n=>Number.isInteger(n)&&n>0) || !Number.isInteger(base)||base<=0) return null;
    ticks += 4*counts.reduce((a,b)=>a+b,0)/base;
  }
  return ticks;
}

function peakPolyphony(intervals) {
  const ends = intervals.flatMap(([start,end])=>[[start,1],[end,-1]]);
  ends.sort((a,b)=>Math.abs(a[0]-b[0])<EPS ? a[1]-b[1] : a[0]-b[0]);
  let active=0,peak=0;
  for (const [,delta] of ends) {
    active+=delta;
    peak=Math.max(active,peak);
  }
  return peak;
}

function roleFor(name, bounds, type) {
  if (type==='unpitched') return 'perc';
  if (/低音|低胡|革胡|大提琴|bass|cello|tuba/i.test(name) || (bounds!==null&&bounds[1]<60)) return 'bass';
  if (/中阮|大阮|中胡|中音笙|中音唢呐|viola|horn|伴奏|accomp|harmony/i.test(name)) return 'inner';
  if (/高音|梆笛|曲笛|笛子|主旋律|flute|violin|clarinet|oboe|trumpet/i.test(name)) return 'lead';
  return 'any';
}

function inspectPart(part, header, isConcertScore, countNotes) {
  let divisions=null, meter=null, baseShift=zero(), currentFifths=0;
  const perStaff=new Map();
  const noteEvents=[], measureDetails=[], offsets=new Map(), instrumentIds=new Set();
  const repeatStyles=new Set(), slashStaves=new Set();
  const melodicPitches=[], cuePitches=[], voices=new Set();
  const warnings=[], unsafeFeatures=new Set(), keyChanges=new Set([0]);
  let numberedShift=false, polyphony=0, unpitched=0, pitched=0, ambiguousPitch=0, rests=0;
  const sig=part.getAttribute('id');
  const name=value(header,'part-name') || sig;
  if (header.querySelector('player')) unsafeFeatures.add('多个演奏身份');
  if (children(header,'score-instrument').length>1) unsafeFeatures.add('多个音色或兼奏标识');
  const partMeasures=children(part,'measure');
  let maxBar=0, staffCount=1;
  for (const [index,measure] of partMeasures.entries()) {
    let cursor=0, high=0, lastStart=0, lastValid=false, multiRest=0;
    const intervals=[], transposeChanges=[], pitchedEvents=[];
    const label=measure.getAttribute('number') || String(index+1);
    const bar={
      index,number:label,implicit:measure.getAttribute('implicit')==='yes',
      events:[],rehearsalMarks:[],tempoMarks:[],swingMarks:[],timingIssues:[],rhythmIssues:[],flowIssues:[],
      repeatForward:false,repeatBackward:null,endings:[],newPage:false,pageNumber:null,hasExplicitTiming:false,
    };
    if (measure.getAttribute('non-controlling')==='yes') bar.rhythmIssues.push('含无法与其他声部对齐的小节线');
    const rhythmWarning=message=>{
      warnings.push(`第 ${label} 小节${message}。`);
      bar.rhythmIssues.push(message);
    };
    for (const node of children(measure)) {
      switch(node.localName) {
        case 'attributes': {
          if (child(node,'divisions')) {
            const durationUnits=number(node,'divisions');
            divisions=Number.isFinite(durationUnits)&&durationUnits>0?durationUnits:null;
          }
          for (const shift of children(node,'transpose')) {
            const staff=shift.hasAttribute('number')?Number(shift.getAttribute('number')):null;
            if (staff!==null) numberedShift=true;
            transposeChanges.push({onset:cursor, staff, shift:readTranspose(shift)});
          }
          if (child(node,'for-part')) unsafeFeatures.add('实音总谱的独立分谱移调');
          if (child(node,'staff-details')) unsafeFeatures.add('自定义谱表');
          const declaredStaves=number(node,'staves',1);
          if (Number.isSafeInteger(declaredStaves)) staffCount=Math.max(staffCount,declaredStaves);
          for (const key of children(node,'key')) {
            if (child(key,'cancel')) unsafeFeatures.add('调号取消记号');
            const fifths=number(key,'fifths');
            if (!Number.isInteger(fifths)||Math.abs(fifths)>7||key.getAttribute('number')||child(key,'key-octave')) {
              unsafeFeatures.add('非标准或分谱表调号');
            } else {
              currentFifths=fifths;
              keyChanges.add(fifths);
            }
          }
          const timeSignatures=children(node,'time');
          if (timeSignatures.length) {
            meter=timingMeter(timeSignatures[0]);
            if (timeSignatures.some(time=>timingMeter(time)!==meter)) bar.rhythmIssues.push('各谱表的拍号时值不一致');
          }
          for (const style of children(node,'measure-style')) {
            const staff=style.getAttribute('number')||'all';
            for (const mark of children(style)) {
              if (mark.localName==='measure-repeat' || mark.localName==='beat-repeat') {
                const key=`${mark.localName}:${staff}`;
                if (mark.getAttribute('type')==='stop') repeatStyles.delete(key);
                else repeatStyles.add(key);
              }
              if (mark.localName==='slash') {
                if (mark.getAttribute('type')==='stop' && cursor<=EPS) slashStaves.delete(staff);
                if (slashStaves.size) bar.rhythmIssues.push('斜线记谱的实际音符需要确认');
                if (mark.getAttribute('type')==='stop') slashStaves.delete(staff);
                else slashStaves.add(staff);
              }
            }
            multiRest=Math.max(multiRest,number(style,'multiple-rest',0));
          }
          break;
        }
        case 'direction':
          if (node.querySelector('octave-shift')) unsafeFeatures.add('八度线');
          readDirection(node,cursor,divisions,bar);
          break;
        case 'harmony':
          unsafeFeatures.add('和弦符号');
          break;
        case 'barline':
          readBarline(node,cursor,bar);
          break;
        case 'print':
          if (node.getAttribute('new-page')==='yes') {
            bar.newPage=true;
            bar.pageNumber=node.getAttribute('page-number');
          }
          break;
        case 'sound':
          if (node.querySelector('instrument-change')) unsafeFeatures.add('中途换奏乐器');
          readSound(node,cursor,divisions,null,bar);
          break;
        case 'backup':
        case 'forward': {
          const raw=number(node,'duration');
          const duration=raw/divisions;
          if (!divisions || !Number.isFinite(duration) || raw<0) rhythmWarning('拍位存在未识别时值');
          else {
            const backup=node.localName==='backup';
            cursor+=(backup?-1:1)*duration;
            if (!backup && duration>EPS) bar.hasExplicitTiming=true;
          }
          if (cursor < -EPS) rhythmWarning('的声部游标退到了小节起点之前');
          high=Math.max(high,cursor);
          lastValid=false;
          break;
        }
        case 'note': {
          countNotes();
          const noteMarks=children(node).filter(el=>['pitch','rest','unpitched'].includes(el.localName));
          if (noteMarks.length!==1) {
            throw new Error(`${name} 第 ${label} 小节的音符必须且只能包含音高、休止或无固定音高记谱中的一种。`);
          }
          const [mark]=noteMarks;
          const grace=Boolean(child(node,'grace')), cue=Boolean(child(node,'cue')), chord=Boolean(child(node,'chord'));
          const raw=number(node,'duration');
          const length=raw/divisions;
          const duration=grace?0:divisions && Number.isFinite(length) && length>0?length:null;
          const onset=chord&&lastValid ? lastStart : cursor;
          if (chord&&!lastValid) rhythmWarning('有缺少起始音的和弦成员');
          if (duration===null) rhythmWarning('存在无法确定拍位的音符');
          if (duration>EPS) bar.hasExplicitTiming=true;
          if (!chord) {
            lastStart=onset;
            lastValid=true;
            cursor+=duration??0;
          }
          high=Math.max(high,cursor,onset+(duration??0));
          const staff=value(node,'staff')||'1';
          const voice=value(node,'voice')||'1';
          const staffNumber=Number(staff);
          if (Number.isSafeInteger(staffNumber)) staffCount=Math.max(staffCount,staffNumber);
          voices.add(voice);
          for (const n of children(node,'instrument')) instrumentIds.add(n.getAttribute('id'));
          const pitchData=mark.localName==='pitch'?readPitch(mark):null;
          let type='unknown';
          if (mark.localName==='rest') {
            rests++;
            type='rest';
          } else if (mark.localName==='unpitched') {
            unpitched++;
            type='unpitched';
          } else if (!pitchData) {
            ambiguousPitch++;
            unsafeFeatures.add('微分音、不完整音高或八度叠奏');
          } else {
            type='pitched';
          }
          recordNoteFeatures(node,unsafeFeatures);
          if (cue) unsafeFeatures.add('提示音');
          const event={measure:index,onset,duration,sounding:null,type,chord,cue,grace,voice,staff,fifths:currentFifths,written:pitchData,
            ...noteTiming(node,mark,onset,duration,bar)};
          noteEvents.push(event);
          bar.events.push(event);
          if (type==='pitched') pitchedEvents.push(event);
          break;
        }
      }
    }
    // Later voices can rewind the cursor. Mid-measure changes apply in score order.
    transposeChanges.sort((a,b)=>a.onset-b.onset);
    let nextChange=0;
    const applyTransposeThrough=(onset)=>{
      while (nextChange<transposeChanges.length && transposeChanges[nextChange].onset<=onset+EPS) {
        const {staff,shift}=transposeChanges[nextChange++];
        if (staff===null) {
          baseShift=shift;
          perStaff.clear();
        } else {
          perStaff.set(staff,shift);
        }
      }
    };
    for (const event of pitchedEvents.sort((a,b)=>a.onset-b.onset)) {
      const {onset,duration,staff,written,cue,grace}=event;
      applyTransposeThrough(onset);
      const shift=perStaff.get(Number(staff))||baseShift;
      if (!shift.known) {
        event.type='unknown';
        ambiguousPitch++;
        unsafeFeatures.add('微分音、不完整音高或八度叠奏');
        continue;
      }
      event.transpose=shift;
      event.sounding=written.midi+shift.chromatic;
      if (!cue) { pitched++; melodicPitches.push(event.sounding); }
      else cuePitches.push(event.sounding);
      offsets.set(signature(shift),shift);
      if (!grace&&!cue&&duration>0) intervals.push([onset,onset+duration]);
    }
    applyTransposeThrough(Infinity);
    const poly=peakPolyphony(intervals);
    polyphony=Math.max(polyphony,poly);
    maxBar=Math.max(maxBar,high);
    if (meter!==null && high-meter>EPS) warnings.push(`第 ${label} 小节音乐时长超过拍号（${high.toFixed(2)} / ${meter.toFixed(2)} 四分拍）。`);
    if (slashStaves.size && !bar.rhythmIssues.includes('斜线记谱的实际音符需要确认')) {
      bar.rhythmIssues.push('斜线记谱的实际音符需要确认');
    }
    if ((repeatStyles.size || multiRest>1) && !bar.hasExplicitTiming) bar.rhythmIssues.push('缩写记谱的小节缺少完整时值');
    bar.meterQ=meter;
    bar.actualDurationQ=high;
    measureDetails.push(bar);
  }
  if (part.querySelector('instrument-change')) unsafeFeatures.add('中途换奏乐器');
  const p=melodicPitches.length?melodicPitches:cuePitches;
  const bounds=p.length?p.reduce(([lo,hi],v)=>[Math.min(lo,v),Math.max(hi,v)],[Infinity,-Infinity]):null;
  const shift=offsets.size===1?[...offsets.values()][0]:null;
  if (offsets.size>1) unsafeFeatures.add('多个移调区段');
  if (numberedShift) unsafeFeatures.add('分谱表移调');
  if (instrumentIds.size>1) unsafeFeatures.add('多个演奏乐器');
  if (isConcertScore) unsafeFeatures.add('MusicXML 实音总谱');
  if (voices.size>1) unsafeFeatures.add('同谱不同声部');
  if (staffCount>1) unsafeFeatures.add('多谱表');
  const type=unpitched>0&&pitched>0?'mixed':unpitched>0?'unpitched':pitched>0?'pitched':'unknown';
  return {
    id:sig,name,bounds,shift,offsets:[...offsets.values()], measures:partMeasures.length,noteEvents,measureDetails,
    notes:pitched,unpitched,rests,ambiguousPitch,cueNotes:cuePitches.length,polyphony,maxBar,role:roleFor(name,bounds,type),
    staves:staffCount,voices:voices.size,keyChanges:[...keyChanges],warnings:[...new Set(warnings)].slice(0,25),
    unsafeFeatures:[...unsafeFeatures],type,
  };
}

export function parseMusicXML(xml) {
  if (typeof xml!=='string'||!xml.trim()) throw new Error('乐谱内容为空。');
  if (xml.length>12000000) throw new Error('主谱件超过 1,200 万字符，请按乐章导出。');
  if (/<!ENTITY/i.test(xml)) throw new Error('这个文件包含自定义 XML 实体，无法安全读取。');
  const stripped=xml.replace(/<!DOCTYPE\s+score-partwise(?:\s+PUBLIC\s+"[^"\r\n]*"\s+"[^"\r\n]*"|\s+SYSTEM\s+"[^"\r\n]*")?\s*>/ig,'');
  if (/<!DOCTYPE/i.test(stripped)||/<\?(?!xml\s|xml\?>)/i.test(stripped)) throw new Error('这个文件含有未支持的 XML 声明或处理指令。');
  const doc=new DOMParser().parseFromString(stripped,'application/xml');
  if (doc.querySelector('parsererror')) throw new Error('XML 无法解析，请从制谱软件重新导出。');
  const root=doc.documentElement;
  if (root.localName!=='score-partwise'||root.namespaceURI) throw new Error('请选择按声部分组的 MusicXML（score-partwise）。');
  const headers=children(child(root,'part-list'),'score-part');
  const headerMap=new Map(headers.map(h=>[h.getAttribute('id'),h]));
  const parts=children(root,'part');
  if (!parts.length||parts.length>64) throw new Error('此工具支持 1 到 64 个乐谱声部。');
  const ids=parts.map(p=>p.getAttribute('id'));
  if (new Set(ids).size!==ids.length||headers.length!==headerMap.size||ids.some(id=>!id||!headerMap.has(id))) {
    throw new Error('乐谱声部编号缺失、重复或无法与乐器列表对应。');
  }
  let totalNotes=0;
  const count=()=>{ if (++totalNotes>MAX_NOTES) throw new Error('分析上限为 120,000 个记谱事件。请按乐章拆分后再试。'); };
  const concert=child(child(root,'defaults'),'concert-score')||root.querySelector('concert-score');
  const analysis=parts.map(part=>inspectPart(part,headerMap.get(part.getAttribute('id')),Boolean(concert),count));
  return {
    doc,title:value(root,'movement-title')||value(child(root,'work'),'work-title')||'未命名总谱',
    parts:analysis,totalNotes,...assembleScoreClock(analysis),
  };
}

function spelledPitch(midi, diatonicIndex) {
  const letter=mod(diatonicIndex,7);
  const octave=Math.floor(diatonicIndex/7);
  const alter=midi-(12*(octave+1)+stepPitch[letter]);
  if (octave<0||octave>9||!accidentalNames.has(alter)) return null;
  return { letter,octave,alter };
}

function writtenShift(source,target) {
  return { chromatic:source.chromatic-target.chromatic, diatonic:source.diatonic-target.diatonic };
}

function transposeFifths(fifths,delta) {
  const wantedLetter=mod(4*fifths+delta.diatonic,7);
  const wantedPitch=mod(7*fifths+delta.chromatic,12);
  for (let k=-7;k<=7;k++) if (mod(4*k,7)===wantedLetter&&mod(7*k,12)===wantedPitch) return k;
  return null;
}

function modalAccidental(fifths, letter) {
  const sharps=[3,0,4,1,5,2,6], flats=[6,2,5,1,4,0,3];
  if (fifths>=0) return sharps.slice(0,fifths).includes(letter)?1:0;
  return flats.slice(0,-fifths).includes(letter)?-1:0;
}

export function evaluateMapping(part,target,role) {
  const reasons=[], review=[];
  const reasonsToReview=part.unsafeFeatures.filter(f=>!['同谱不同声部','多谱表'].includes(f));
  const targetUnpitched=target.unpitched??(target.role==='perc');
  if (part.type==='unpitched'&&!targetUnpitched) reasons.push('原谱含无固定音高记谱，需要对应席位。');
  if (part.type==='pitched'&&targetUnpitched) reasons.push('目标席位无法承接有固定音高的声部。');
  if (part.type==='mixed') reasons.push('存在有音高与无音高混合，须人工分配。');
  if (part.type==='unknown'||part.ambiguousPitch>0) reasons.push('无法从原谱可靠识别全声部的实音。');
  if (part.bounds&&(part.bounds[0]<target.low||part.bounds[1]>target.high)) reasons.push(`实音 ${midiName(part.bounds[0])}–${midiName(part.bounds[1])} 超过目标音域。`);
  if (part.polyphony>target.poly) reasons.push(`原谱每处最多 ${part.polyphony} 个同时发声，目标席位上限 ${target.poly}。`);
  if (part.staves>target.staves) reasons.push('原谱的独立谱表数超过目标谱表数。');
  const offsetMatch=Boolean(part.shift&&part.shift.chromatic===target.chromatic
    &&(part.shift.diatonic===target.diatonic||target.chromatic===0&&part.shift.diatonic===null));
  const changing=part.type==='pitched'&&!offsetMatch;
  if (!part.shift && part.type==='pitched') review.push('原谱有不同的移调区段。');
  if (part.type==='unpitched') review.push('无固定音高声部的击打位置和音色须手工校核。');
  if (part.warnings.length) review.push('源谱存在需复核的时值或小节警报。');
  if (changing && (part.shift?.diatonic===null || part.staves!==1 || part.voices!==1 || part.polyphony>1 || reasonsToReview.length)) {
    review.push('该声部超出安全移调范围，需人工转写。');
  }
  if (reasonsToReview.includes('实音总谱的独立分谱移调')) {
    review.push('原谱含独立分谱移调，改变乐器前须人工核对。');
  }
  if (changing&&part.shift&&part.shift.diatonic!==null && !review.length) {
    const delta=writtenShift(part.shift,target);
    if(part.keyChanges.some(fifths=>transposeFifths(fifths,delta)===null)) review.push('转换后存在超出七升七降的调号，需人工重拼。');
    if(part.noteEvents.some(({written:p})=>p&&!spelledPitch(p.midi+delta.chromatic,p.octave*7+p.letter+delta.diatonic))) {
      review.push('转换后存在超出双升双降的音名，需人工重拼。');
    }
  }
  if (role!==target.role && role!=='any' && target.role!=='any' && [role,target.role].includes('bass')) {
    review.push('声部作用不同，先核对低音骨架和乐器音色，再采用这一建议。');
  }
  if (!changing && reasonsToReview.some(f=>['多个音色或兼奏标识','多个演奏身份','多个演奏乐器','中途换奏乐器','自定义谱表','特殊音高或乐器专用记号'].includes(f))) {
    review.push('本声部含兼奏、专用记号或自定义谱表，改变乐器名称前需人工核对。');
  }
  const mismatch = role==='any'||target.role==='any'||role===target.role ? 0 : [role,target.role].includes('bass') ? 60 : 14;
  const midpoint=part.bounds?(part.bounds[0]+part.bounds[1])/2:(target.low+target.high)/2;
  const middle = (target.low+target.high)/2;
  const edge = part.bounds ? Math.max(0,6-Math.min(part.bounds[0]-target.low,target.high-part.bounds[1])) : 0;
  const localeMatch=target.name===part.name;
  const cost = mismatch+Math.abs(midpoint-middle)*0.55+edge*2+(changing?12:0)+(review.length?100:0)+(localeMatch?0:3);
  return { cost: reasons.length?null:Math.round(cost*10)/10,safe:!reasons.length&&!review.length,changing,reasons,review };
}

function setNode(doc,parent,name,content,following=[]) {
  let item=child(parent,name);
  if (!item) {
    item=doc.createElement(name);
    const next=children(parent).find(el=>following.includes(el.localName));
    parent.insertBefore(item,next||null);
  }
  item.textContent=String(content);
  return item;
}
function attributes(doc,measure) {
  const firstTimeline=children(measure).find(el=>['note','forward','backup','direction','harmony','sound'].includes(el.localName));
  let node=children(measure).find(el=>el.localName==='attributes'&&(!firstTimeline||Boolean(el.compareDocumentPosition(firstTimeline)&4)));
  if (!node) {
    node=doc.createElement('attributes');
    const next=children(measure).find(el=>!['print','barline'].includes(el.localName));
    measure.insertBefore(node,next||null);
  }
  return node;
}
const followingKey=['time','staves','part-symbol','instruments','clef','staff-details','transpose','for-part','directive','measure-style'];
function putKey(doc,attr,fifths) {
  const key=child(attr,'key')||setNode(doc,attr,'key','',followingKey);
  setNode(doc,key,'fifths',fifths,['mode','key-octave']);
}
function putTranspose(doc,attr,target) {
  const t=doc.createElement('transpose');
  const octaveChange=Math.trunc(target.chromatic/12);
  setNode(doc,t,'diatonic',target.diatonic-7*octaveChange);
  setNode(doc,t,'chromatic',target.chromatic-12*octaveChange);
  if (octaveChange) setNode(doc,t,'octave-change',octaveChange);
  const next=children(attr).find(el=>['for-part','directive','measure-style'].includes(el.localName));
  attr.insertBefore(t,next||null);
}

function rewritePart(doc,part,info,target) {
  const delta=writtenShift(info.shift,target);
  const measures=children(part,'measure');
  let fifths=transposeFifths(0,delta);
  if(fifths===null) throw new Error(`${info.name} 的默认调号无法安全转换。`);
  const initial=attributes(doc,measures[0]);
  if (!child(initial,'key')) putKey(doc,initial,0);
  for (const measure of measures) {
    const accidentalMemory=new Map();
    for (const node of children(measure)) {
      if (node.localName==='attributes') {
        for (const old of children(node,'transpose')) old.remove();
        const key=child(node,'key');
        if (key) {
          fifths=transposeFifths(number(key,'fifths'),delta);
          if (fifths===null) throw new Error(`${info.name} 的调号超出可安全转换范围。`);
          setNode(doc,key,'fifths',fifths,['mode','key-octave']);
          accidentalMemory.clear();
        }
      }
      if (node.localName!=='note'||!child(node,'pitch')) continue;
      const p=child(node,'pitch');
      const parsed=readPitch(p);
      if(!parsed) throw new Error(`${info.name} 有无法安全转换的音高。`);
      const mapped=spelledPitch(parsed.midi+delta.chromatic,parsed.octave*7+parsed.letter+delta.diatonic);
      if(!mapped) throw new Error(`${info.name} 出现超出双升或双降的音名，需人工重拼。`);
      setNode(doc,p,'step',steps[mapped.letter]);
      if (mapped.alter) setNode(doc,p,'alter',mapped.alter,['octave']);
      else child(p,'alter')?.remove();
      setNode(doc,p,'octave',mapped.octave);
      const code=mapped.octave*7+mapped.letter;
      const prior=accidentalMemory.has(code)?accidentalMemory.get(code):modalAccidental(fifths,mapped.letter);
      const original=child(node,'accidental');
      if (prior!==mapped.alter||original) {
        setNode(doc,node,'accidental',accidentalNames.get(mapped.alter),['time-modification','stem','notehead','notehead-text','staff','beam','notations','lyric','play','listen']);
      }
      accidentalMemory.set(code,mapped.alter);
    }
  }
  if (target.chromatic!==0||target.diatonic!==0) putTranspose(doc,initial,target);
}
function renamePart(doc,header,target) {
  setNode(doc,header,'part-name',target.label);
  child(header,'part-name-display')?.remove();
  child(header,'part-abbreviation-display')?.remove();
  if (child(header,'part-abbreviation')) setNode(doc,header,'part-abbreviation',target.short||target.label);
  const instrument=child(header,'score-instrument');
  if (instrument) {
    setNode(doc,instrument,'instrument-name',target.name);
    if (child(instrument,'instrument-abbreviation')) setNode(doc,instrument,'instrument-abbreviation',target.short||target.name);
    if (target.sound && child(instrument,'instrument-sound')) setNode(doc,instrument,'instrument-sound',target.sound);
    else child(instrument,'instrument-sound')?.remove();
  }
  const midi=child(header,'midi-instrument');
  if (target.program && midi) {
    setNode(doc,midi,'midi-program',target.program,['midi-unpitched','volume','pan','elevation']);
  }
}
function musicalSignature(part) {
  return part.noteEvents.map(({fifths,written,transpose,...timing})=>timing);
}
export function exportMusicXML(analysis, mappings) {
  const doc=analysis.doc.cloneNode(true),root=doc.documentElement;
  const headers=new Map(children(child(root,'part-list'),'score-part').map(h=>[h.getAttribute('id'),h]));
  const parts=new Map(children(root,'part').map(h=>[h.getAttribute('id'),h]));
  let changed=0, rewritten=0;
  for (const {source, target, evaluation} of mappings) {
    if (!target||!evaluation?.safe) continue;
    const header=headers.get(source.id),part=parts.get(source.id);
    if (!header||!part) throw new Error('无法定位需要修改的声部。');
    if (evaluation.changing) { rewritePart(doc,part,source,target); rewritten++; }
    renamePart(doc,header,target);
    changed++;
  }
  if (!changed) throw new Error('当前没有通过安全校验且可以写入的映射。');
  const xml='<?xml version="1.0" encoding="UTF-8"?>\n'+new XMLSerializer().serializeToString(root)+'\n';
  const verify=parseMusicXML(xml);
  for (const [i,source] of analysis.parts.entries()) {
    const actual=verify.parts[i];
    if (actual.id!==source.id || JSON.stringify(musicalSignature(actual))!==JSON.stringify(musicalSignature(source))) {
      throw new Error(`${source.name} 导出回读时的实音或拍位发生变化，已取消导出。`);
    }
  }
  return { xml,changed,rewritten };
}
