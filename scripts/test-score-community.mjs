// Exercise the generated contact/intake/support pages without a network or browser.
// Run after build-score-site.py. QR fingerprints bind these uses to the supplied originals.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';

const require = createRequire(import.meta.url);
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const origin = 'https://taitai2025.github.io';
const contact = '/scores/contact/';
const intake = '/scores/orchestras/submit/';
const support = '/scores/support/';
const updates = '/scores/updates/';
const code = fs.readFileSync(path.join(root, 'scores/community/community.js'), 'utf8');
const cooperationCode = fs.readFileSync(path.join(root, 'scores/tools/drafts.js'), 'utf8');
const config = JSON.parse(fs.readFileSync(path.join(root, 'scores/community/config.json'), 'utf8'));
const digest = file => createHash('sha256').update(fs.readFileSync(path.join(root, file))).digest('hex');
const tick = () => new Promise(resolve => setImmediate(resolve));
const surfaces = new Set();

function surface(route = contact, {run = true, query = '', clipboard = 'success', legacy = false, formSelector = '[data-community-draft]'} = {}) {
  const source = fs.readFileSync(path.join(root, route, 'index.html'), 'utf8');
  const errors = [];
  const console = new VirtualConsole();
  console.on('jsdomError', error => errors.push(error.message));
  const dom = new JSDOM(source, {url: `${origin}${route}${query}`, runScripts: 'outside-only', virtualConsole: console});
  const w = dom.window;
  const q = selector => w.document.querySelector(selector);
  const all = selector => [...w.document.querySelectorAll(selector)];
  const outbound = [];
  const copied = [];
  const downloads = [];
  const storageWrites = [];
  w.fetch = async (...args) => { outbound.push(['fetch', ...args]); throw new Error('Network disabled in test'); };
  w.XMLHttpRequest.prototype.open = function (...args) { outbound.push(['xhr', ...args]); throw new Error('Network disabled in test'); };
  Object.defineProperty(w.navigator, 'sendBeacon', {configurable: true, value: (...args) => { outbound.push(['beacon', ...args]); return false; }});
  w.Storage.prototype.setItem = function (...args) { storageWrites.push(args); };
  Object.defineProperty(w.navigator, 'clipboard', {configurable: true, value: clipboard === 'missing' ? undefined : {
    writeText: async text => { if (clipboard === 'reject') throw new Error('Clipboard denied'); copied.push(text); },
  }});
  w.Blob = globalThis.Blob;
  w.URL.createObjectURL = blob => { downloads.push({blob}); return `blob:community-test-${downloads.length}`; };
  w.URL.revokeObjectURL = () => {};
  w.HTMLAnchorElement.prototype.click = function () {
    if (this.download) Object.assign(downloads.at(-1), {name: this.download, href: this.href});
  };
  w.HTMLFormElement.prototype.submit = function () { outbound.push(['form', this.action]); };
  const form = q(formSelector);
  const field = name => form.elements.namedItem(name);
  function set(name, value, event = 'input') {
    const input = field(name);
    assert.ok(input, `Missing field ${name}`);
    if (input.type === 'checkbox') input.checked = value;
    else input.value = value;
    input.dispatchEvent(new w.Event(event, {bubbles: true}));
  }
  function submit() {
    const event = new w.Event('submit', {bubbles: true, cancelable: true});
    form.dispatchEvent(event);
    assert.equal(event.defaultPrevented, true, 'The local draft form must prevent native navigation');
  }
  if (run) w.eval(legacy ? cooperationCode : code);
  const result = {w, q, all, form, field, set, submit, outbound, copied, downloads, storageWrites, errors,
    close() { dom.window.close(); surfaces.delete(result); }};
  surfaces.add(result);
  return result;
}

function fillScore(s, overrides = {}) {
  for (const [name, value] of Object.entries({'作品名称': '山雪', '用途与需求': '学校排练，申请查阅。', ...overrides})) s.set(name, value);
}
function fillIntake(s) {
  for (const [name, value] of Object.entries({
    '乐团名称': '测试大学民族乐团', '所属高校': '测试大学', '所在地区': '中国 / 合肥',
    '乐团介绍': '每周排练，开展民乐教学与年度音乐会。', '公开入口与出处': 'https://example.edu/orchestra',
    '照片与图注': '合照01：2026 年音乐会谢幕；请在邮件中另附原图。',
    '来源与展示范围': '文字与照片由本团提供，可以用于本站乐团介绍，署名测试大学民族乐团。',
    '回复方式': 'orchestra@example.edu',
  })) s.set(name, value);
  s.set('来源确认', true, 'change');
}

const results = [];
async function check(name, test) {
  try { await test(); results.push({name, passed: true}); }
  catch (error) { results.push({name, passed: false, error: error.stack || error.message}); }
  finally { for (const s of [...surfaces]) s.close(); }
}

await check('without JavaScript visitors can contact the owner, read support details and download the intake template', () => {
  const s = surface(contact, {run: false});
  const body = s.w.document.body.textContent;
  for (const value of [config.email, config.backupEmail, config.wechat, config.qq]) assert.ok(body.includes(value));
  assert.ok(s.q(`a[href="mailto:${config.email}"]`));
  assert.ok(s.q('a[href="/scores/orchestras/submit/"]'));
  assert.equal(s.q('[data-draft-submit]').hidden, true);
  assert.equal(s.form.querySelector('fieldset').disabled, true, 'Uninitialized forms cannot leak contact details via implicit GET');
  const i = surface(intake, {run: false});
  assert.equal(i.form.querySelector('fieldset').disabled, true);
  const template = i.q('a[download][href="/scores/orchestras/intake-template.txt"]');
  assert.ok(template);
  assert.ok(fs.existsSync(path.join(root, new URL(template.href).pathname)));
  const mail = i.all('a[href^="mailto:"]').find(a => new URL(a.href).searchParams.has('body'));
  assert.ok(mail, 'Complete materials can be emailed without the form');
  assert.equal(new URL(mail.href).pathname, config.email);
  assert.match(new URL(mail.href).searchParams.get('body'), /乐团名称/);
  assert.equal(i.all('input[type=file]').length, 0, 'A static intake does not pretend to accept file uploads');
  const p = surface(support, {run: false});
  assert.equal(p.all('.community-payment-card').length, 2);
  assert.match(p.w.document.body.textContent, /自愿/);
  assert.match(p.w.document.body.textContent, /不是谱件购买|不.*(?:谱件|密码|授权)/);
});

await check('new routes have unique titles, correct canonical URLs, real links and current cache fingerprints', () => {
  const titles = [];
  for (const route of [contact, intake, support, updates]) {
    const s = surface(route, {run: false});
    assert.equal(s.all('h1').length, 1);
    titles.push(s.w.document.title);
    assert.equal(s.q('link[rel=canonical]').href, origin + route);
    assert.ok(s.q('meta[name=description]').content.length >= 30);
    const ids = s.all('[id]').map(el => el.id);
    assert.equal(ids.length, new Set(ids).size);
    for (const [selector, attribute, file] of [
      ['script[src]', 'src', '/scores/community/community.js'],
      ['link[rel=stylesheet]', 'href', '/scores/community/community.css'],
    ]) {
      const nodes = s.all(selector).filter(node => new URL(node.getAttribute(attribute), s.w.location.href).pathname === file);
      assert.equal(nodes.length, 1, `${route}: one ${file} reference`);
      assert.equal(new URL(nodes[0].getAttribute(attribute), s.w.location.href).searchParams.get('v'), digest(file).slice(0, 12));
    }
    for (const a of s.all('.community-page a[href]')) {
      const url = new URL(a.href);
      if (url.protocol === 'mailto:') {
        assert.ok([config.email, config.backupEmail].includes(url.pathname));
        continue;
      }
      assert.equal(url.protocol, 'https:');
      if (url.origin !== origin) continue;
      const local = path.join(root, url.pathname, url.pathname.endsWith('/') ? 'index.html' : '');
      assert.ok(fs.existsSync(local), `${route}: missing ${url.pathname}`);
      if (url.hash && !url.hash.startsWith('#page=')) {
        const target = new JSDOM(fs.readFileSync(local, 'utf8'));
        try { assert.ok(target.window.document.getElementById(decodeURIComponent(url.hash.slice(1))), `Missing ${url.href}`); }
        finally { target.window.close(); }
      }
    }
  }
  assert.equal(new Set(titles).size, titles.length);
});

await check('friend and payment QR codes retain the exact supplied originals and cannot be swapped silently', () => {
  const expected = {
    'wechat-friend.jpg': '534195798e685af42ecce25d7d496dd8a59714ebbeedce14fdfc745b98b709e0',
    'wechat-support.jpg': 'dda327c5aefed9234ed66dfeea400eecbb8c4969c6f3828958b461c9fe6dcb1d',
    'alipay-support.jpg': '77aa79c57b6e5e5e0772e6ed895885f2fa11104d4d260b66aa235a71e58e849b',
  };
  for (const [name, hash] of Object.entries(expected)) {
    assert.equal(config.assets[name].src, `/scores/community/${name}`);
    assert.equal(config.assets[name].sha256, hash);
    assert.equal(digest(config.assets[name].src), hash);
  }
  const s = surface(contact, {run: false});
  assert.equal(s.all('.community-page img').length, 1);
  assert.equal(s.q('#wechat img').getAttribute('src'), config.assets['wechat-friend.jpg'].src);
  assert.match(s.q('#wechat img').alt, /好友/);
  const p = surface(support, {run: false});
  for (const [selector, name, label] of [
    ['.community-payment-card.wechat', 'wechat-support.jpg', '微信支付'],
    ['.community-payment-card.alipay', 'alipay-support.jpg', '支付宝'],
  ]) {
    const card = p.q(selector);
    assert.equal(card.querySelector('img').getAttribute('src'), config.assets[name].src);
    assert.ok(card.querySelector('h2').textContent.includes(label));
    assert.equal(new URL(card.querySelector('a[download]').href).pathname, config.assets[name].src);
    assert.ok(Number(card.querySelector('img').width) > 0 && Number(card.querySelector('img').height) > 0);
  }
});

await check('blank, whitespace-only and unconfirmed required materials do not generate drafts', () => {
  for (const route of [contact, intake]) {
    const s = surface(route);
    assert.equal(s.form.querySelector('fieldset').disabled, false);
    assert.equal(s.q('[data-draft-submit]').hidden, false);
    s.submit();
    assert.equal(s.q('[data-draft-result]').hidden, true);
    assert.equal(s.q('[data-draft-text]').value, '');
    route === intake ? fillIntake(s) : fillScore(s);
    const requiredName = route === intake ? '乐团名称' : '作品名称';
    s.set(requiredName, '   \t ');
    s.submit();
    assert.equal(s.q('[data-draft-result]').hidden, true);
    assert.equal(s.q('[data-draft-mail]').hasAttribute('href'), false);
    s.set(requiredName, '完整名称');
    if (route === intake) {
      s.set('来源确认', false, 'change');
      s.submit();
      assert.equal(s.q('[data-draft-result]').hidden, true);
      s.set('来源确认', true, 'change');
    }
    s.submit();
    assert.equal(s.q('[data-draft-result]').hidden, false, 'Correcting invalid fields must allow a new draft');
    assert.deepEqual(s.outbound, []);
  }
});

await check('a complete orchestra intake produces an inspectable draft without claiming delivery or storing private fields', () => {
  const s = surface(intake);
  fillIntake(s);
  s.submit();
  const draft = s.q('[data-draft-text]').value;
  for (const text of ['测试大学民族乐团', 'https://example.edu/orchestra', '合照01', 'orchestra@example.edu', '可公开展示范围']) assert.ok(draft.includes(text));
  assert.match(draft, /附件请.*手动添加/);
  assert.match(s.q('[data-draft-status]').textContent, /尚未发送/);
  assert.doesNotMatch(s.q('[data-draft-status]').textContent, /发送成功|提交成功|已收到/);
  assert.deepEqual(s.outbound, []);
  assert.deepEqual(s.storageWrites, []);
  assert.deepEqual(s.errors, []);
});

await check('a short score request opens a correctly addressed email draft containing the visible text', () => {
  const s = surface();
  fillScore(s);
  s.submit();
  const mail = new URL(s.q('[data-draft-mail]').href);
  assert.equal(mail.protocol, 'mailto:');
  assert.equal(mail.pathname, config.email);
  assert.ok(mail.searchParams.get('subject').includes('山雪'));
  assert.equal(mail.searchParams.get('body'), s.q('[data-draft-text]').value);
  assert.match(s.q('[data-draft-mail-note]').textContent, /由你发送/);
  assert.deepEqual(s.outbound, []);
});

await check('editing an input or changing a selection invalidates stale drafts and mail links', () => {
  const s = surface();
  fillScore(s);
  s.submit();
  s.set('作品名称', '古槐寻根');
  assert.equal(s.q('[data-draft-result]').hidden, true);
  assert.equal(s.q('[data-draft-text]').value, '');
  assert.equal(s.q('[data-draft-mail]').hasAttribute('href'), false);
  assert.match(s.q('[data-draft-status]').textContent, /重新/);
  s.submit();
  assert.match(s.q('[data-draft-text]').value, /古槐寻根/);
  assert.doesNotMatch(s.q('[data-draft-text]').value, /山雪/);
  s.set('交流类型', '版本核对', 'change');
  assert.equal(s.q('[data-draft-result]').hidden, true);
  s.submit();
  assert.match(s.q('[data-draft-text]').value, /版本核对/);
});

await check('long email drafts retain every character for copy and TXT while the mail link falls back to subject only', async () => {
  const s = surface();
  const longText = '申请校内排练查阅。'.repeat(100) + '完整草稿结束标志';
  fillScore(s, {'用途与需求': longText});
  s.submit();
  const draft = s.q('[data-draft-text]').value;
  assert.ok(draft.includes(longText));
  const mail = new URL(s.q('[data-draft-mail]').href);
  assert.equal(mail.pathname, config.email);
  assert.equal(mail.searchParams.has('body'), false);
  assert.ok(mail.searchParams.has('subject'));
  assert.match(s.q('[data-draft-mail-note]').textContent, /草稿较长/);
  s.q('[data-copy-draft]').click();
  await tick();
  assert.equal(s.copied.at(-1), draft);
  s.q('[data-download-draft]').click();
  assert.equal(s.downloads.length, 1);
  assert.ok(s.downloads[0].name.endsWith('.txt'));
  assert.equal((await s.downloads[0].blob.text()).replace(/^\ufeff/, ''), draft + '\n');
  assert.deepEqual(s.outbound, []);
  assert.deepEqual(s.storageWrites, []);
});

await check('catalogue query text is bounded and stays text, including malicious markup and control characters', () => {
  const payload = '<img src=x onerror="window.communityAttack=1">\n新版';
  const query = '?' + new URLSearchParams({work: payload, version: '版'.repeat(300), password: 'SHOULD-NOT-ENTER-DRAFT'});
  const s = surface(contact, {query});
  assert.equal(s.q('img[src=x]'), null);
  assert.equal(s.w.communityAttack, undefined);
  assert.equal(s.field('作品名称').value, payload.replace(/\n/g, ' '));
  assert.ok(s.field('谱件版本').value.length <= s.field('谱件版本').maxLength);
  s.set('用途与需求', '排练资料核对');
  s.submit();
  assert.ok(s.q('[data-draft-text]').value.includes('<img src=x'));
  assert.doesNotMatch(s.q('[data-draft-text]').value, /SHOULD-NOT-ENTER-DRAFT/);
  assert.equal(s.q('img[src=x]'), null);
  assert.equal(s.w.communityAttack, undefined);
  assert.deepEqual(s.outbound, []);
  assert.deepEqual(s.storageWrites, []);
});

await check('clipboard denial and missing clipboard leave contact details and full drafts available for manual copying', async () => {
  for (const clipboard of ['reject', 'missing']) {
    const s = surface(contact, {clipboard});
    const button = s.all('[data-copy]').find(node => node.dataset.copy === config.email);
    button.click();
    await tick();
    assert.match(s.q('[data-community-status]').textContent, /无法复制.*手动复制/);
    assert.ok(s.q(`a[href="mailto:${config.email}"]`));
    fillScore(s);
    s.submit();
    const before = s.q('[data-draft-text]').value;
    s.q('[data-copy-draft]').click();
    await tick();
    assert.match(s.q('[data-draft-status]').textContent, /无法复制.*手动复制/);
    assert.equal(s.q('[data-draft-text]').value, before);
    assert.equal(s.q('[data-draft-result]').hidden, false);
    assert.equal(s.q('[data-draft-text]').readOnly, true);
    assert.deepEqual(s.copied, []);
    assert.deepEqual(s.errors, []);
  }
});

await check('protected score details lead to a prefilled request while open-source navigation remains open', () => {
  const workData = JSON.parse(fs.readFileSync(path.join(root, 'scores/data/works.json'), 'utf8'));
  const works = Array.isArray(workData) ? workData : workData.works;
  for (const work of works) {
    const s = surface(`/scores/work/${work.slug}/`, {run: false});
    assert.equal(s.all('.score-access-notice').length, 1, work.slug);
    const request = s.q('.score-access-notice a[href*="contact/"]');
    const url = new URL(request.href);
    assert.equal(url.searchParams.get('work'), work.title, work.slug);
    assert.equal(url.searchParams.get('version'), work.version, work.slug);
    assert.equal(url.hash, '#request');
  }
  const open = surface('/scores/open/', {run: false});
  assert.equal(open.all('.score-access-notice').length, 0);
});

await check('existing score-feedback and cooperation forms also block inactive or invalid submission and invalidate changed drafts', () => {
  for (const name of ['校谱反馈', '共建与制谱交流']) {
    const options = {legacy: true, formSelector: `[data-draft="${name}"]`};
    const staticPage = surface('/scores/tools/cooperation/', {...options, run: false});
    assert.equal(staticPage.form.querySelector('fieldset').disabled, true);
    assert.equal(staticPage.form.querySelector('button[type=submit]').hidden, true);
    const s = surface('/scores/tools/cooperation/', options);
    const q = selector => s.form.querySelector(selector);
    assert.equal(q('fieldset').disabled, false);
    assert.equal(q('button[type=submit]').hidden, false);
    s.submit();
    assert.equal(q('[data-ready]').hidden, true);
    for (const input of s.form.querySelectorAll('[required]')) s.set(input.name, '具体资料');
    const required = s.form.querySelector('[required]');
    s.set(required.name, '   \t ');
    s.submit();
    assert.equal(q('[data-ready]').hidden, true);
    assert.equal(q('[data-mail]').hasAttribute('href'), false);
    s.set(required.name, '云南印象 V27');
    s.submit();
    assert.equal(q('[data-ready]').hidden, false);
    assert.match(q('.generated-draft').textContent, /云南印象 V27/);
    assert.match(q('output').textContent, /尚未发送/);
    const select = q('select');
    s.set(select.name, select.options[1].value, 'change');
    assert.equal(q('[data-ready]').hidden, true);
    assert.equal(q('.generated-draft').textContent, '');
    assert.equal(q('[data-mail]').hasAttribute('href'), false);
    s.submit();
    assert.ok(q('.generated-draft').textContent.includes(select.options[1].value));
    assert.deepEqual(s.outbound, []);
    assert.deepEqual(s.storageWrites, []);
    assert.deepEqual(s.errors, []);
  }
});

await check('existing feedback forms keep long draft text intact when falling back to a subject-only email link', async () => {
  for (const name of ['校谱反馈', '共建与制谱交流']) {
    const s = surface('/scores/tools/cooperation/', {legacy: true, formSelector: `[data-draft="${name}"]`});
    const q = selector => s.form.querySelector(selector);
    for (const input of s.form.querySelectorAll('[required]')) s.set(input.name, '具体资料');
    const field = q('textarea[required]');
    const longText = '小节声部问题与依据。'.repeat(50) + '最后一项仍应保留';
    assert.ok(longText.length <= field.maxLength);
    s.set(field.name, longText);
    s.submit();
    const draft = q('.generated-draft').textContent;
    assert.ok(draft.includes(longText));
    const mail = new URL(q('[data-mail]').href);
    assert.equal(mail.pathname, config.email);
    assert.equal(mail.searchParams.has('body'), false);
    assert.ok(mail.searchParams.get('subject').includes(name));
    assert.equal(q('[data-mail]').hidden, false);
    assert.match(q('output').textContent, /尚未发送.*内容较长/);
    q('[data-save]').click();
    assert.equal(s.downloads.length, 1);
    assert.equal((await s.downloads[0].blob.text()).replace(/^\ufeff/, ''), draft + '\n');
    assert.deepEqual(s.outbound, []);
  }
});

for (const result of results) {
  console.log(`${result.passed ? 'PASS' : 'FAIL'} ${result.name}`);
  if (!result.passed) console.error(result.error);
}
console.log(`${results.filter(result => result.passed).length}/${results.length} community checks passed.`);
if (results.some(result => !result.passed)) process.exitCode = 1;
