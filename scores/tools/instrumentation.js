'use strict';

const REVIEW_OPTIONS = {
  中音笙: [
    {name:'钢琴',note:'可先试配中声部和弦。需重新处理延音、音色和力度。'},
    {name:'中音排笙',note:'检查实音、指法、最低音与持续吹奏。'},
  ],
  低音笙: [
    {name:'大提琴',note:'可试补低声部线条。先核八度和音域，保留和声需另作处理。'},
    {name:'低音提琴',note:'可试补持续低音。弦低音与笙的发音、复音能力不同。'},
  ],
  低音提琴: [
    {name:'大提琴',note:'需核对最低音、实际音高、乐队音量和平行声部。'},
    {name:'低音革胡',note:'核对定弦、移调与可演奏最低音。'},
  ],
  低音革胡: [
    {name:'低音提琴',note:'先核定弦、音域与读谱习惯。'},
    {name:'大提琴',note:'只在低音线不超音域且不冲突时试排。'},
  ],
  革胡: [{name:'大提琴',note:'先核定弦、指法和实际音高。'}],
  低音管: [{name:'大管',note:'确认原谱所称乐器、用谱体系和实音后再安排。'}],
  中胡: [
    {name:'中提琴',note:'可试奏中声部线条。需另制谱并检查音色与原旋律是否冲突。'},
    {name:'二胡',note:'先核低音域。若移高八度，应检查和声及旋律重心。'},
  ],
  大阮: [{name:'中阮',note:'先核低音域与重叠声部，必要时改配低音。'}],
  竖琴: [{name:'钢琴',note:'可试奏和弦或分解音型，需处理踏板、余音和音量。'}],
  古筝: [{name:'扬琴',note:'仅建议检查可移植的单音或分解型。特殊定弦、滑音与刮奏需另作方案。'}],
  高音唢呐: [{name:'唢呐',note:'核对实际调性、音域及独奏音色。'}],
  中音唢呐: [{name:'唢呐',note:'先核调性、声音投射和音域。高音型号不能默认承担中频和声。'}],
  拉弦: [{name:'二胡',note:'先查出原谱实际声部后安排。'}],
};

const SAMPLE = ['梆笛','曲笛','高音笙','高音唢呐','扬琴','琵琶','中阮','大阮','古筝','二胡','中胡','大提琴','低音提琴','排鼓','大堂鼓','小军鼓','碰铃','吊镲'];
const STORAGE_KEY = 'guoyue:instrument-selection:v1';

function evaluateRoster(work, selected) {
  const lines = work.lines.filter(line => line.kind === 'observed');
  const names = [...new Set(lines.flatMap(line => line.instruments))];
  const available = names.filter(name => selected.has(name));
  const missing = names.filter(name => !selected.has(name));
  const flagged = lines.filter(line => line.unresolved.length);
  const concurrent = lines.filter(line => line.instruments.length > 1);
  const repeated = names.filter(name => {
    const mentions = lines.filter(line => line.instruments.includes(name)).map(line => line.label);
    return mentions.length > 1 && mentions.some(label => /[ⅠⅡⅢⅣ]|(?:胡|琴|笛|笙)[IVX]+|独奏/.test(label));
  });
  const options = missing.flatMap(name => {
    const idea = (REVIEW_OPTIONS[name] || []).find(choice => selected.has(choice.name));
    return idea ? [{missing:name,candidate:idea.name,note:idea.note,alreadyAssigned:names.includes(idea.name)}] : [];
  });
  const optional = work.lines.filter(line => line.kind === 'optional');
  const reserve = work.lines.filter(line => line.kind === 'reserve');
  const score = names.length ? available.length / (names.length + flagged.length) : 0;
  const complete = names.length > 0 && !missing.length && !flagged.length;
  return {work, names, available, missing, flagged, concurrent, repeated, options, optional, reserve, score, complete};
}

function filterRosters(works, selected, query, mode) {
  const terms = query.trim().toLocaleLowerCase().split(/\s+/).filter(Boolean);
  const states = works.map(work => evaluateRoster(work,selected));
  return states.filter(state => {
    const text = [state.work.title, ...state.work.lines.flatMap(line => [line.label,...line.instruments])].join(' ').toLocaleLowerCase();
    return terms.every(term => text.includes(term)) &&
      (mode === 'all' || (mode === 'clear' ? state.complete : !state.complete));
  }).sort((a,b) => b.score-a.score || a.missing.length-b.missing.length || a.work.title.localeCompare(b.work.title,'zh-Hans'));
}

function node(tag, text, className) {
  const element = document.createElement(tag);
  if (text) element.textContent = text;
  if (className) element.className = className;
  return element;
}

function getSelection() {
  try {
    const value = JSON.parse(localStorage.getItem(STORAGE_KEY) || '[]');
    return new Set(Array.isArray(value) ? value.filter(item => typeof item === 'string') : []);
  } catch {
    return new Set();
  }
}

function saveSelection(selection) {
  try { localStorage.setItem(STORAGE_KEY, JSON.stringify([...selection])); }
  catch { /* Browsers may disable local storage. */ }
}

function appendEntry(container, title, text) {
  if (!text) return;
  const line = node('p');
  line.append(node('strong',title + '。'), text);
  container.append(line);
}

function resultItem(result) {
  const {work, names, available, missing, flagged, concurrent, repeated, options, optional, reserve, complete} = result;
  const item = node('details','','fit-result');
  const heading = node('summary');
  const metric = complete ? '已覆盖索引中的已识别乐器' : `已覆盖 ${available.length} / ${names.length} 种已识别乐器`;
  heading.append(node('span',work.title),node('span',`${metric}${flagged.length ? ' · '+flagged.length+' 条待辨认的谱件标签' : ''}`,'fit-score'));
  item.append(heading);
  appendEntry(item,'缺席乐器',missing.join('、'));
  appendEntry(item,'待辨认谱件',flagged.map(line=>line.label).join('、'));
  appendEntry(item,'兼奏或多件打击乐',concurrent.map(line=>line.label).join('、'));
  appendEntry(item,'可能有分部或独奏',repeated.join('、'));
  appendEntry(item,'可选谱件',optional.map(line=>line.label).join('、'));
  appendEntry(item,'包内已列的备用谱件',reserve.map(line=>line.label).join('、'));
  if (options.length) {
    const title = node('p','可试排的候选替代');
    const list = node('ul','','note-list');
    for (const option of options) {
      const ask = option.alreadyAssigned ? ' 该乐器在此版本已有声部，需检查是否能兼顾。' : '';
      list.append(node('li',`${option.missing} → ${option.candidate}。 ${option.note}${ask}`));
    }
    item.append(title,list);
  }
  if (work.note) item.append(node('small',work.note));
  const link = node('a','打开受保护的谱件目录');
  link.href = '/scores/archive/#' + encodeURIComponent(work.slug);
  item.append(link);
  return item;
}

async function initialize() {
  const store = getSelection();
  const groups = document.getElementById('instrument-groups');
  const found = document.getElementById('fit-results');
  const query = document.getElementById('instrument-search');
  const piece = document.getElementById('work-search');
  const mode = document.getElementById('match-filter');
  const instrumentCount = document.getElementById('selection-count');
  const scoresCount = document.getElementById('result-count');
  const response = await fetch('./rosters.json');
  if (!response.ok) throw new Error('Invalid published instrument index');
  const data = await response.json();
  const relevant = new Set(data.works.flatMap(work => work.lines.flatMap(line => line.instruments)));
  const unknown = [...relevant];
  const displayed = new Set();
  const choices = [];
  for (const [family,names] of [...Object.entries(data.families),['其他索引乐器',unknown]]) {
    const distinct = names.filter(name => relevant.has(name) && !displayed.has(name));
    if (!distinct.length) continue;
    distinct.forEach(name => displayed.add(name));
    const details = node('details','','instrument-family');
    details.open = family === '民族管乐';
    const summary = node('summary',family);
    const grid = node('div','','instrument-list');
    details.append(summary,grid);
    groups.append(details);
    const members = [];
    for (const name of distinct) {
      const label = node('label','','instrument-option');
      const input = node('input');
      input.type = 'checkbox';
      input.value = name;
      input.checked = store.has(name);
      label.append(input,name);
      grid.append(label);
      members.push({name,label,input});
      input.addEventListener('change',() => {
        if (input.checked) store.add(name); else store.delete(name);
        refresh(true);
      });
    }
    choices.push({details,summary,family,members});
  }
  groups.setAttribute('aria-busy','false');

  const syncOptions = () => {
    const look = query.value.trim().toLocaleLowerCase();
    for (const choice of choices) {
      let shown = 0;
      let checked = 0;
      for (const member of choice.members) {
        member.input.checked = store.has(member.name);
        if (member.input.checked) checked++;
        member.label.hidden = Boolean(look) && !member.name.toLocaleLowerCase().includes(look);
        if (!member.label.hidden) shown++;
      }
      choice.summary.textContent = checked ? `${choice.family}（已选 ${checked}）` : choice.family;
      choice.details.hidden = !shown;
      if (look && shown) choice.details.open = true;
    }
  };

  function refresh(sync = false) {
    for (const name of store) if (!relevant.has(name)) store.delete(name);
    if (sync) syncOptions();
    instrumentCount.textContent = store.size ? `已选 ${store.size} 种乐器。` : '尚未勾选乐器。也可直接展开查看谱件编制。';
    const rows = filterRosters(data.works,store,piece.value,mode.value);
    const message = rows.length ? `显示 ${rows.length} 个曲目或编制版本。` : '没有符合条件的谱件。可调整查询词或覆盖范围。';
    scoresCount.textContent = message;
    found.replaceChildren(...rows.map(resultItem));
    saveSelection(store);
  }
  document.getElementById('load-sample').addEventListener('click',() => {
    store.clear();
    SAMPLE.filter(name => relevant.has(name)).forEach(name => store.add(name));
    refresh(true);
  });
  document.getElementById('clear-instruments').addEventListener('click',() => {
    store.clear();
    refresh(true);
  });
  query.addEventListener('input',syncOptions);
  piece.addEventListener('input',() => refresh());
  mode.addEventListener('change',() => refresh());
  refresh(true);
}

if (typeof module !== 'undefined') module.exports = {evaluateRoster,filterRosters};
if (typeof document !== 'undefined') initialize().catch(() => {
  document.getElementById('instrument-groups').setAttribute('aria-busy','false');
  document.getElementById('selection-count').textContent = '谱件编制索引暂不可用，请稍后刷新页面。';
});
