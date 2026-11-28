// Behavioural checks for the local programme planner; no browser or network.
// Run after building. Use NODE_PATH for an existing jsdom installation if needed.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';

const require = createRequire(import.meta.url);
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const code = fs.readFileSync(path.join(root, 'scores/experience.js'), 'utf8');
const catalogue = JSON.parse(fs.readFileSync(path.join(root, 'scores/collection-index.json'), 'utf8'));
const KEY = 'guoyue.programme.v1';
const records = catalogue.records.slice(0, 6);
const ids = records.map(record => record.id);
const tick = () => new Promise(resolve => setImmediate(resolve));
const sample = (count = 2) => ({schemaVersion: 1, title: '春季音乐会候选', date: '2027-03-06', notes: '先排困难段落。', items: ids.slice(0, count).map((id, index) => ({id, minutes: String(3 + index), note: `第 ${index + 1} 首备注`}))});

async function surface({page = 'planner', initial = null, offline = false} = {}) {
  const html = fs.readFileSync(path.join(root, `scores/${page}/index.html`), 'utf8');
  const console = new VirtualConsole();
  const errors = [];
  console.on('jsdomError', error => errors.push(error.message));
  const dom = new JSDOM(html, {url: `https://taitai2025.github.io/scores/${page}/`, runScripts: 'outside-only', virtualConsole: console});
  const w = dom.window;
  const downloads = [];
  let printed = 0;
  w.Blob = globalThis.Blob;
  w.URL.createObjectURL = blob => { downloads.push({blob}); return `blob:check-${downloads.length}`; };
  w.URL.revokeObjectURL = () => {};
  w.HTMLAnchorElement.prototype.click = function () { if (this.download) downloads.at(-1).name = this.download; };
  w.HTMLDialogElement.prototype.showModal = function () { this.setAttribute('open', ''); };
  w.HTMLDialogElement.prototype.close = function () { this.removeAttribute('open'); };
  w.print = () => { printed += 1; };
  w.fetch = async () => { if (offline) throw new Error('offline'); return {ok: true, json: async () => catalogue}; };
  if (initial !== null) w.localStorage.setItem(KEY, typeof initial === 'string' ? initial : JSON.stringify(initial));
  w.eval(code);
  await tick();
  const q = selector => w.document.querySelector(selector);
  const all = selector => [...w.document.querySelectorAll(selector)];
  const saved = () => JSON.parse(w.localStorage.getItem(KEY));
  const type = (selector, value, event = 'input') => { const node = q(selector); node.value = value; node.dispatchEvent(new w.Event(event, {bubbles: true})); };
  const importFile = async value => {
    const input = q('#plan-file');
    const content = typeof value === 'string' ? value : JSON.stringify(value);
    Object.defineProperty(input, 'files', {configurable: true, value: [{size: Buffer.byteLength(content), text: async () => content}]});
    input.dispatchEvent(new w.Event('change', {bubbles: true}));
    await tick();
  };
  return {dom, w, q, all, saved, type, importFile, downloads, errors, get printed() { return printed; }, close() { dom.window.close(); }};
}

const results = [];
async function check(name, test) {
  try { await test(); results.push({name, passed: true}); }
  catch (error) { results.push({name, passed: false, error: error.message}); }
}

await check('empty planner explains the next action and disables empty exports', async () => {
  const s = await surface();
  try {
    assert.match(s.q('#plan-list').textContent, /先挑几首/);
    assert.equal(s.q('#compare-plan').disabled, true);
    assert.equal(s.q('#export-plan').disabled, true);
    assert.equal(s.w.localStorage.getItem(KEY), null);
  } finally { s.close(); }
});

await check('catalogue add/remove persists IDs and updates the header', async () => {
  const s = await surface({page: 'library'});
  try {
    const button = s.q('[data-collect]');
    assert.ok(button);
    button.click();
    assert.equal(s.saved().items[0].id, button.dataset.collect);
    assert.equal(button.getAttribute('aria-pressed'), 'true');
    assert.equal(s.q('.plan-count').textContent, '1');
    button.click();
    assert.equal(s.saved().items.length, 0);
  } finally { s.close(); }
});

await check('comparison accepts two to four versions and refuses a fifth', async () => {
  const s = await surface({initial: sample(5)});
  try {
    const boxes = s.all('.plan-select input');
    boxes[0].click();
    assert.equal(s.q('#compare-plan').disabled, true);
    boxes[1].click();
    assert.equal(s.q('#compare-plan').disabled, false);
    s.q('#compare-plan').click();
    assert.equal(s.all('#comparison-content thead th').length, 3);
    s.q('#close-comparison').click();
    boxes[2].click(); boxes[3].click(); boxes[4].click();
    assert.equal(boxes[4].checked, false);
    s.q('#compare-plan').click();
    assert.equal(s.all('#comparison-content thead th').length, 5);
  } finally { s.close(); }
});

await check('JSON backup restores text, order, dates and duration without HTML execution', async () => {
  const initial = sample(2);
  initial.notes = '<img src=x onerror="window.pwned=1">\n演奏顺序待确认';
  const s = await surface({initial});
  try {
    s.q('#export-plan').click();
    const exported = JSON.parse(await s.downloads.at(-1).blob.text());
    assert.deepEqual(exported, initial);
    await s.importFile({...exported, title: '<svg onload="window.pwned=1">新版', items: [...exported.items].reverse()});
    assert.ok(s.q('.import-preview[open]'));
    assert.equal(s.q('img[src=x]'), null);
    assert.equal(s.w.pwned, undefined);
    s.all('.import-preview button').find(button => button.textContent === '替换当前清单').click();
    assert.equal(s.saved().items[0].id, initial.items[1].id);
    assert.equal(s.q('#plan-notes').value, initial.notes);
    assert.equal(s.q('.import-preview'), null);
  } finally { s.close(); }
});

await check('import merge keeps current annotations; unsupported JSON does not overwrite', async () => {
  const s = await surface({initial: sample(2)});
  try {
    const incoming = sample(3); incoming.items[0].note = 'incoming replacement';
    await s.importFile(incoming);
    s.all('.import-preview button').find(button => button.textContent === '合并到当前清单').click();
    assert.equal(s.saved().items.length, 3);
    assert.equal(s.saved().items[0].note, '第 1 首备注');
    const unchanged = s.w.localStorage.getItem(KEY);
    await s.importFile({schemaVersion: 99, items: []});
    assert.equal(s.w.localStorage.getItem(KEY), unchanged);
    assert.equal(s.q('.import-preview'), null);
    await s.importFile({schemaVersion: 1, items: [{id: 'not-in-catalogue'}]});
    assert.equal(s.w.localStorage.getItem(KEY), unchanged);
  } finally { s.close(); }
});

await check('CSV quotes text and escapes spreadsheet formula prefixes', async () => {
  const initial = sample(2);
  initial.items[0].note = '=HYPERLINK("https://example.invalid","test")';
  initial.items[1].note = '\t+1\n二胡、笙';
  const s = await surface({initial});
  try {
    s.q('#export-plan-csv').click();
    const content = await s.downloads.at(-1).blob.text();
    assert.ok(content.includes('"\'=HYPERLINK(""https://example.invalid"",""test"")"'));
    assert.ok(content.includes('"\'\t+1\n二胡、笙"'));
    assert.ok(content.includes('https://taitai2025.github.io/scores/work/'));
    s.q('#print-plan').click();
    assert.equal(s.printed, 1);
  } finally { s.close(); }
});

await check('another tab updates the programme; clearing storage also clears its view', async () => {
  const s = await surface({initial: sample(2)});
  try {
    const next = sample(3); next.title = '另一页修改后的清单';
    s.w.localStorage.setItem(KEY, JSON.stringify(next));
    s.w.dispatchEvent(new s.w.StorageEvent('storage', {key: KEY, storageArea: s.w.localStorage}));
    assert.equal(s.all('.plan-item').length, 3);
    assert.equal(s.q('#plan-title').value, next.title);
    s.w.localStorage.clear();
    s.w.dispatchEvent(new s.w.StorageEvent('storage', {key: null, storageArea: s.w.localStorage}));
    assert.equal(s.all('.plan-item').length, 0, 'A cleared plan must not remain available to write back on the next edit.');
  } finally { s.close(); }
});

await check('failed local saving is reflected in the persistent summary and export remains usable', async () => {
  const s = await surface({initial: sample(2)});
  try {
    s.w.Storage.prototype.setItem = () => { throw new s.w.DOMException('full', 'QuotaExceededError'); };
    s.type('#plan-title', '不能保存的新标题');
    assert.match(s.q('#plan-summary').textContent, /尚未写入|未保存|保存失败/);
    assert.equal(s.q('#export-plan').disabled, false);
    s.q('#export-plan').click();
    assert.equal(JSON.parse(await s.downloads.at(-1).blob.text()).title, '不能保存的新标题');
  } finally { s.close(); }
});

await check('duration input is saved and exported before a blur or change event', async () => {
  const s = await surface({initial: sample(2)});
  try {
    s.type('.plan-annotation input[type="number"]', '5.5');
    assert.equal(s.saved().items[0].minutes, '5.5');
    assert.match(s.q('#plan-summary').textContent, /9\.5 分钟/);
    s.q('#export-plan').click();
    const exported = JSON.parse(await s.downloads.at(-1).blob.text());
    assert.equal(exported.items[0].minutes, '5.5');
  } finally { s.close(); }
});

await check('print mirrors contain full multiline notes and refresh without duplication', async () => {
  const s = await surface({initial: sample(2)});
  try {
    const programmeNote = '整体备注：二胡先分部排练。\n'.repeat(80);
    const partNote = '<img src=x onerror="window.pwned=1">\n' + '笙与曲笛对齐换气；保留小节号。\n'.repeat(70);
    s.type('#plan-notes', programmeNote);
    s.type('.plan-annotation textarea', partNote);
    s.w.dispatchEvent(new s.w.Event('beforeprint'));
    assert.equal(s.q('#plan-notes').nextElementSibling.textContent, programmeNote);
    assert.equal(s.q('.plan-annotation textarea').nextElementSibling.textContent, partNote);
    assert.equal(s.q('img[src=x]'), null);
    const count = s.all('.print-value').length;
    s.type('.plan-annotation textarea', partNote + '\n改在下一次排练核对。');
    s.q('#print-plan').click();
    assert.equal(s.all('.print-value').length, count);
    assert.equal(s.q('.plan-annotation textarea').nextElementSibling.textContent, partNote + '\n改在下一次排练核对。');
    assert.equal(s.printed, 1);
  } finally { s.close(); }
});

await check('catalogue network failure gives a visible explanation and leaves local data untouched', async () => {
  const initial = sample(2);
  const s = await surface({initial, offline: true});
  try {
    assert.match(s.q('#plan-list').textContent, /暂时未能加载/);
    assert.deepEqual(s.saved(), initial);
    assert.equal(s.q('#compare-plan').disabled, true);
  } finally { s.close(); }
});

for (const result of results) console.log(`${result.passed ? 'PASS' : 'FAIL'} ${result.name}${result.error ? `\n  ${result.error}` : ''}`);
const failed = results.filter(result => !result.passed);
console.log(`${results.length - failed.length}/${results.length} experience checks passed.`);
if (failed.length) process.exitCode = 1;
