/* Programme planning is local to the browser. No personal data is submitted. */
(() => {
  'use strict';
  const KEY = 'guoyue.programme.v1';
  const MAX_ITEMS = 60;
  let records = [], byId = new Map(), byPath = new Map(), selected = new Set();
  let toastTimer, plan, storageError = false;
  const $ = id => document.getElementById(id);
  const el = (tag, attrs = {}, text = '') => {
    const node = document.createElement(tag);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
    if (text !== '') node.textContent = text;
    return node;
  };
  const blank = () => ({schemaVersion: 1, title: '', date: '', notes: '', items: []});
  const cleanText = (value, max) => typeof value === 'string' ? value.slice(0, max) : '';
  const minuteValue = value => {
    if (value === '' || value === null || value === undefined) return '';
    const n = Number(value);
    return Number.isFinite(n) && n >= 0 && n <= 300 ? String(Math.round(n * 10) / 10) : '';
  };
  const validDate = value => {
    if (typeof value !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(value)) return '';
    const d = new Date(value + 'T00:00:00Z');
    return Number.isFinite(d.valueOf()) && d.toISOString().slice(0, 10) === value ? value : '';
  };
  function normalize(value, strict = false) {
    if (!value || value.schemaVersion !== 1 || !Array.isArray(value.items)) throw new Error('这不是支持的国乐谱汇选曲单（格式版本 1）。');
    if (value.items.length > MAX_ITEMS) throw new Error('一份选曲单最多保留 60 个曲目版本。');
    const ids = new Set(), skipped = [];
    const items = [];
    for (const row of value.items) {
      if (!row || typeof row.id !== 'string' || !byId.has(row.id)) { skipped.push(cleanText(row?.id, 100) || '未知条目'); continue; }
      if (ids.has(row.id)) continue;
      ids.add(row.id);
      items.push({id: row.id, minutes: minuteValue(row.minutes), note: cleanText(row.note, 2000)});
    }
    if (strict && value.items.length && !items.length) throw new Error('清单中的曲目在当前目录中都不存在。原有清单保持不变。');
    return {value: {schemaVersion: 1, title: cleanText(value.title, 80), date: validDate(value.date), notes: cleanText(value.notes, 2000), items}, skipped};
  }
  function read() {
    try {
      const raw = localStorage.getItem(KEY);
      if (!raw) return blank();
      const parsed = normalize(JSON.parse(raw));
      if (parsed.skipped.length) queueMicrotask(() => notify(`有 ${parsed.skipped.length} 个旧目录条目暂不可用；可保留原备份供核对。`));
      return parsed.value;
    } catch (_) {
      storageError = true;
      queueMicrotask(() => notify('无法读取本地清单。当前操作可继续，请导出 JSON 保存。'));
      return blank();
    }
  }
  function persist() {
    try { localStorage.setItem(KEY, JSON.stringify(plan)); storageError = false; }
    catch (_) { storageError = true; notify('浏览器未允许保存。请在离开前下载 JSON 备份。'); }
    syncButtons();
    updateSummary();
  }
  function notify(text) {
    let node = $('guoyue-notification');
    if (!node) { node = el('div', {id: 'guoyue-notification', class: 'toast', role: 'status', 'aria-live': 'polite'}); document.body.append(node); }
    node.textContent = text; node.hidden = false;
    clearTimeout(toastTimer); toastTimer = setTimeout(() => { node.hidden = true; }, 4400);
  }
  function syncButtons() {
    const ids = new Set(plan.items.map(i => i.id));
    document.querySelectorAll('[data-collect]').forEach(button => {
      const active = ids.has(button.dataset.collect);
      button.setAttribute('aria-pressed', String(active));
      const title = byId.get(button.dataset.collect)?.title || '此曲目';
      button.setAttribute('aria-label', `${active ? '从选曲单移除' : '加入选曲单'}：${title}`);
      button.querySelector('span').textContent = active ? '已加入选曲单' : '加入选曲单';
    });
    document.querySelectorAll('.header-action[href="/scores/planner/"]').forEach(a => {
      let badge = a.querySelector('.plan-count');
      if (!badge) { badge = el('span', {class: 'plan-count', 'aria-hidden': 'true'}); a.append(badge); }
      badge.textContent = plan.items.length; badge.hidden = !plan.items.length;
      a.setAttribute('aria-label', `我的选曲单，${plan.items.length} 个版本`);
    });
  }
  function toggle(id) {
    const index = plan.items.findIndex(i => i.id === id);
    if (index >= 0) { plan.items.splice(index, 1); selected.delete(id); notify('已从选曲单移除。'); }
    else {
      if (plan.items.length >= MAX_ITEMS) return notify('选曲单已达到 60 个版本，请先整理现有曲目。');
      plan.items.push({id, minutes: '', note: ''}); notify('已加入选曲单，可在“我的选曲单”比较与整理。');
    }
    persist(); if ($('programme-app')) renderPlan();
  }
  function collectButton(record) {
    const button = el('button', {type: 'button', class: 'collect-button', 'data-collect': record.id, 'aria-pressed': 'false'});
    button.innerHTML = '<svg viewBox="0 0 20 20" aria-hidden="true"><path d="M5 3h10v14l-5-3-5 3z"/></svg><span>加入选曲单</span>';
    button.addEventListener('click', () => toggle(record.id));
    return button;
  }
  function decorate() {
    document.querySelectorAll('.card,.edition-card').forEach(card => {
      const a = card.querySelector('h3 a');
      const record = a && byPath.get(new URL(a.href).pathname);
      if (!record || card.querySelector('[data-collect]')) return;
      (card.querySelector('.edition-actions') || card).append(collectButton(record));
    });
    const current = byPath.get(location.pathname);
    if (current) {
      const actions = document.querySelector('.hero-actions');
      if (actions && !actions.querySelector('[data-collect]')) actions.append(collectButton(current));
      const feedback = [...document.querySelectorAll('a[href="/scores/tools/cooperation/"]')].filter(a => a.closest('main'));
      feedback.forEach(a => { a.href = '/scores/tools/cooperation/?' + new URLSearchParams({work: current.title, version: current.version}); });
    }
    syncButtons();
  }
  function download(name, value, mime) {
    const objectURL = URL.createObjectURL(new Blob([value], {type: mime}));
    const a = el('a', {href: objectURL, download: name}); document.body.append(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(objectURL), 1500);
  }
  const fileDate = () => new Intl.DateTimeFormat('sv-SE', {timeZone: 'Asia/Shanghai'}).format(new Date());
  function updateSummary() {
    const summary = $('plan-summary'); if (!summary) return;
    const filled = plan.items.filter(i => i.minutes !== '');
    const total = filled.reduce((sum, i) => sum + Number(i.minutes), 0);
    summary.replaceChildren(el('span', {}, `已选 ${plan.items.length} 个曲目版本`),
      el('span', {}, filled.length ? `已填时长合计 ${Math.round(total * 10) / 10} 分钟（${filled.length}/${plan.items.length} 项）` : '时长待填写'),
      el('span', {}, storageError ? '尚未写入浏览器，请导出备份' : '自动保存在本浏览器'));
    $('compare-plan').textContent = `比较所选版本（${selected.size}/4）`;
    $('compare-plan').disabled = selected.size < 2;
    for (const id of ['export-plan', 'export-plan-csv', 'print-plan']) $(id).disabled = !plan.items.length;
  }
  function renderPlan() {
    const container = $('plan-list'); container.replaceChildren();
    if (!plan.items.length) {
      const empty = el('div', {class: 'empty-state'});
      empty.append(el('span', {class: 'path-symbol', 'aria-hidden': 'true'}, '选'), el('h3', {}, '先挑几首想排的作品'),
        el('p', {}, '在曲目卡片或详情页点击“加入选曲单”。这里会保留所选版本，并可比较编制、谱式和获取方式。'));
      const actions = el('div', {class: 'actions'}); actions.append(el('a', {href: '/scores/library/', class: 'button primary'}, '浏览已发布简谱'), el('a', {href: '/scores/open/', class: 'button'}, '寻找开放谱本')); empty.append(actions); container.append(empty);
    }
    plan.items.forEach((item, index) => {
      const record = byId.get(item.id); if (!record) return;
      const article = el('article', {class: 'plan-item', 'data-plan-id': item.id});
      article.append(el('span', {class: 'plan-order', 'aria-label': `第 ${index + 1} 首`}, String(index + 1).padStart(2, '0')));
      const body = el('div'); const h3 = el('h3'); h3.append(el('a', {href: record.url}, record.title)); body.append(h3);
      body.append(el('p', {class: 'meta'}, `${record.ensemble} · ${record.kind}`), el('p', {class: 'meta'}, record.version));
      const select = el('label', {class: 'plan-select'}); const checkbox = el('input', {type: 'checkbox'}); checkbox.checked = selected.has(item.id);
      checkbox.addEventListener('change', () => {
        if (checkbox.checked) {
          if (selected.size >= 4) { checkbox.checked = false; return notify('每次最多比较四个版本。'); }
          selected.add(item.id);
        } else selected.delete(item.id);
        updateSummary();
      }); select.append(checkbox, document.createTextNode('加入本次比较')); body.append(select);
      const actions = el('div', {class: 'plan-row-actions'});
      for (const [label, step] of [['前移', -1], ['后移', 1]]) {
        const b = el('button', {type: 'button', 'aria-label': `${label} ${record.title}`}, label); b.disabled = index + step < 0 || index + step >= plan.items.length;
        b.addEventListener('click', () => { [plan.items[index], plan.items[index + step]] = [plan.items[index + step], plan.items[index]]; persist(); renderPlan(); container.querySelectorAll('.plan-item')[index + step]?.querySelector('h3 a')?.focus(); }); actions.append(b);
      }
      const remove = el('button', {type: 'button', 'aria-label': `移除 ${record.title}`}, '移除');
      remove.addEventListener('click', () => { toggle(item.id); const next = container.querySelectorAll('.plan-item')[Math.min(index, plan.items.length - 1)]; next?.querySelector('h3 a')?.focus(); }); actions.append(remove); body.append(actions); article.append(body);
      const notes = el('div', {class: 'plan-annotation'}), minutesLabel = el('label', {}, '预计时长 / 分钟');
      const minutes = el('input', {type: 'number', min: 0, max: 300, step: .1, placeholder: '待填', 'aria-label': `${record.title} 预计时长（分钟）`}); minutes.value = item.minutes;
      minutes.addEventListener('input', () => { item.minutes = minuteValue(minutes.value); persist(); });
      minutes.addEventListener('change', () => { const val = minuteValue(minutes.value); if (minutes.value !== '' && val === '') notify('时长请填写 0 至 300 分钟。'); item.minutes = val; minutes.value = val; persist(); }); minutesLabel.append(minutes); notes.append(minutesLabel);
      const noteLabel = el('label', {}, '排练备注'), note = el('textarea', {rows: 2, maxlength: 2000, placeholder: '节选乐章、缺席声部、待确认事项…', 'aria-label': `${record.title} 排练备注`}); note.value = item.note;
      note.addEventListener('input', () => { item.note = note.value; persist(); }); noteLabel.append(note); notes.append(noteLabel); article.append(notes); container.append(article);
    });
    updateSummary();
  }
  function compare() {
    const chosen = plan.items.filter(i => selected.has(i.id)).map(i => byId.get(i.id));
    if (chosen.length < 2 || chosen.length > 4) return;
    const table = el('table'); const caption = el('caption', {class: 'sr-only'}, '所选曲目版本信息对照'); table.append(caption);
    const tr = el('tr'); tr.append(el('th', {scope: 'col'}, '对照项目'));
    for (const record of chosen) { const th = el('th', {scope: 'col'}); th.append(el('a', {href: record.url}, record.title)); tr.append(th); }
    const head = el('thead'); head.append(tr); table.append(head); const body = el('tbody');
    const fields = [['编制 / 谱种', r => r.ensemble], ['署名', r => r.composer], ['版本', r => r.version], ['文件', r => r.partCount === null ? '按原站谱本与卷册取用' : `${r.partCount} 份独立分谱文件`], ['记谱版本', r => r.variants.length ? r.variants.join('、') : r.format], ['乐章', r => r.movements.length ? r.movements.join('、') : '参见具体谱本'], ['已登记乐器', r => r.instruments.length ? r.instruments.join('、') : '见原谱编制'], ['获取方式', r => r.access], ['核验记录', r => r.quality], ['排练情况', r => r.rehearsal]];
    for (const [label, readValue] of fields) { const row = el('tr'); row.append(el('th', {scope: 'row'}, label)); chosen.forEach(record => row.append(el('td', {}, readValue(record)))); body.append(row); }
    table.append(body); $('comparison-content').replaceChildren(table); $('compare-dialog').showModal(); $('close-comparison').focus();
  }
  function csvCell(value) {
    let text = String(value ?? '');
    if (/^[\s]*[=+@-]/.test(text)) text = "'" + text;
    return '"' + text.replaceAll('"', '""') + '"';
  }
  function csv() {
    const rows = [['曲序', '曲目', '编制或谱种', '版本', '时长分钟', '排练备注', '详情链接']];
    plan.items.forEach((i, n) => { const r = byId.get(i.id); rows.push([n + 1, r.title, r.ensemble, r.version, i.minutes, i.note, 'https://taitai2025.github.io' + r.url]); });
    download(`国乐谱汇_选曲单_${fileDate()}.csv`, '\ufeff' + rows.map(row => row.map(csvCell).join(',')).join('\r\n') + '\r\n', 'text/csv;charset=utf-8');
  }
  function showImportPreview(imported, skipped) {
    const dialog = el('dialog', {class: 'comparison-dialog import-preview', 'aria-labelledby': 'import-heading'});
    dialog.append(el('h2', {id: 'import-heading'}, '核对导入的选曲单'), el('p', {}, `${imported.title || '未命名选曲单'} · ${imported.items.length} 个可用版本`));
    if (skipped.length) dialog.append(el('p', {class: 'callout'}, `${skipped.length} 个条目已不在当前目录中，将跳过。请保留原始文件以备核对。`));
    dialog.append(el('p', {}, '合并会保留当前顺序与备注，补入新的曲目。替换会使用导入的整份清单。'));
    const actions = el('div', {class: 'actions'});
    const finish = () => { dialog.close(); dialog.remove(); };
    const merge = el('button', {class: 'button primary', type: 'button'}, '合并到当前清单');
    merge.addEventListener('click', () => {
      const ids = new Set(plan.items.map(i => i.id)), added = imported.items.filter(i => !ids.has(i.id));
      if (plan.items.length + added.length > MAX_ITEMS) return notify('合并后超过 60 项，请先整理清单。');
      plan.items.push(...added); if (!plan.title) plan.title = imported.title; if (!plan.date) plan.date = imported.date; if (!plan.notes) plan.notes = imported.notes;
      persist(); populateFields(); renderPlan(); finish(); notify(`已合并 ${added.length} 个新版本。`);
    });
    const replace = el('button', {class: 'button', type: 'button'}, '替换当前清单');
    replace.addEventListener('click', () => { plan = imported; selected.clear(); persist(); populateFields(); renderPlan(); finish(); notify('选曲单已恢复。'); });
    const cancel = el('button', {class: 'button', type: 'button'}, '取消'); cancel.addEventListener('click', finish);
    dialog.addEventListener('cancel', () => dialog.remove(), {once: true});
    actions.append(merge, replace, cancel); dialog.append(actions); document.body.append(dialog); dialog.showModal(); merge.focus();
  }
  function populateFields() { $('plan-title').value = plan.title; $('plan-date').value = plan.date; $('plan-notes').value = plan.notes; }
  function preparePrint() {
    // Native textareas can clip long notes on paper. Print plain text instead.
    document.querySelectorAll('.plan-fields input,.plan-fields textarea,.plan-annotation input,.plan-annotation textarea').forEach(field => {
      let mirror = field.nextElementSibling;
      if (!mirror?.classList.contains('print-value')) { mirror = el('span', {class: 'print-only print-value', 'aria-hidden': 'true'}); field.after(mirror); }
      mirror.textContent = field.value || '未填写';
    });
  }
  function setupPlanner() {
    populateFields();
    for (const [id, key] of [['plan-title', 'title'], ['plan-date', 'date'], ['plan-notes', 'notes']]) $(id).addEventListener('input', () => { plan[key] = key === 'date' ? validDate($(id).value) : $(id).value; persist(); });
    $('compare-plan').addEventListener('click', compare);
    $('close-comparison').addEventListener('click', () => $('compare-dialog').close());
    $('export-plan').addEventListener('click', () => download(`国乐谱汇_选曲单_${fileDate()}.json`, JSON.stringify(plan, null, 2) + '\n', 'application/json'));
    $('export-plan-csv').addEventListener('click', csv);
    $('print-plan').addEventListener('click', () => { preparePrint(); window.print(); });
    window.addEventListener('beforeprint', preparePrint);
    $('import-plan').addEventListener('click', () => $('plan-file').click());
    $('plan-file').addEventListener('change', async () => {
      const file = $('plan-file').files?.[0]; $('plan-file').value = ''; if (!file) return;
      try { if (file.size > 256 * 1024) throw new Error('文件超过 256 KB，不像普通选曲单。'); const parsed = normalize(JSON.parse(await file.text()), true); showImportPreview(parsed.value, parsed.skipped); }
      catch (error) { notify(error instanceof SyntaxError ? '文件不是有效的 JSON。当前清单保持不变。' : error.message); }
    });
    renderPlan();
  }
  async function start() {
    try {
      const response = await fetch('/scores/collection-index.json');
      if (!response.ok) throw new Error('catalogue unavailable');
      const payload = await response.json();
      if (payload.schemaVersion !== 1 || !Array.isArray(payload.records)) throw new Error('catalogue schema unavailable');
      records = payload.records.filter(r => typeof r.id === 'string' && typeof r.url === 'string' && r.url.startsWith('/scores/'));
      byId = new Map(records.map(r => [r.id, r])); byPath = new Map(records.map(r => [r.url, r]));
      plan = read(); decorate(); if ($('programme-app')) setupPlanner();
      window.addEventListener('storage', event => {
        if (event.key !== KEY && event.key !== null) return;
        plan = read(); selected = new Set([...selected].filter(id => plan.items.some(i => i.id === id))); syncButtons();
        if ($('programme-app')) { populateFields(); renderPlan(); notify('已同步此浏览器另一页的选曲修改。'); }
      });
    } catch (_) {
      if ($('programme-app')) {
        $('plan-list').append(el('p', {class: 'callout'}, '曲目目录暂时未能加载。现有本地清单没有被修改，请刷新后重试。'));
        for (const id of ['compare-plan', 'export-plan', 'export-plan-csv', 'import-plan', 'print-plan']) $(id).disabled = true;
      }
    }
  }
  start();
})();
