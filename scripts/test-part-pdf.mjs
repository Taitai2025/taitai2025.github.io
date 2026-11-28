import { createHash, webcrypto } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { test } from 'node:test';
import assert from 'node:assert/strict';

const require = createRequire(import.meta.url);
const { JSDOM, VirtualConsole } = require('jsdom');
const page = readFileSync(new URL('../scores/work/huahaoyueyuan/index.html', import.meta.url), 'utf8');
const script = readFileSync(new URL('../scores/part-pdf.js', import.meta.url), 'utf8');
const slug = 'huahaoyueyuan';
const raw = 'https://raw.githubusercontent.com/Taitai2025/taitai2025.github.io/score-pdf-files/';
const path = 'parts/huahaoyueyuan/minyue-jianpu-20261127-abcdef0123456789/0001.pdf';
const example = Uint8Array.from(Buffer.from('%PDF-1.7\nsynthetic fixture'));
const sha256 = createHash('sha256').update(example).digest('hex');
const settle = () => new Promise(resolve => setTimeout(resolve, 20));

function setup({manifestStatus = 200, pdfViewerEnabled = true, rejectPDF = false, corruptPDF = false} = {}) {
  const dom = new JSDOM(page, {
    url: 'https://taitai2025.github.io/scores/work/huahaoyueyuan/',
    runScripts: 'outside-only',
    virtualConsole: new VirtualConsole(),
  });
  const { window } = dom;
  const parts = [...window.document.querySelectorAll('[data-filename]')];
  const [valid, wrongPages, wrongTag, wrongWork] = parts;
  const asset = row => ({path, sha256, bytes: example.length, pages: Number(row.dataset.partPages)});
  const manifest = {
    [slug]: {
      [valid.dataset.filename]: asset(valid),
      [wrongPages.dataset.filename]: {...asset(wrongPages), pages: -1},
      [wrongTag.dataset.filename]: {...asset(wrongTag), path: path.replace('20261127', '20261126')},
      [wrongWork.dataset.filename]: {...asset(wrongWork), path: path.replace(slug, 'qin-bingmayong')},
    },
  };
  const stats = {calls: [], revoked: [], blob: null};
  Object.defineProperty(window.navigator, 'pdfViewerEnabled', {value: pdfViewerEnabled});
  Object.defineProperty(window.crypto, 'subtle', {value: webcrypto.subtle});
  window.HTMLDialogElement.prototype.showModal = function () { this.open = true; };
  window.URL.createObjectURL = blob => {
    stats.blob = blob;
    return 'blob:https://taitai2025.github.io/test-pdf';
  };
  window.URL.revokeObjectURL = url => stats.revoked.push(url);
  window.fetch = async (url, options) => {
    stats.calls.push({url, options});
    if (url.endsWith('direct-parts.json')) {
      return {ok: manifestStatus === 200, json: async () => manifest};
    }
    assert.equal(url, raw + path);
    if (rejectPDF) throw new Error('simulated network failure');
    const data = example.slice();
    if (corruptPDF) data[data.length - 1] ^= 1;
    return {ok: true, arrayBuffer: async () => data.buffer};
  };
  window.eval(script);
  return {dom, window, valid, stats};
}

test('adds a link only for an indexed file in the current release', async () => {
  const {dom, window, valid} = setup();
  await settle();
  assert.equal(window.document.querySelectorAll('[data-part-pdf-link]').length, 1);
  assert.equal(valid.querySelector('a').href, raw + path);
  dom.window.close();
});

test('uses a PDF Blob for the native viewer, preserving bytes and filename', async () => {
  const {dom, window, valid, stats} = setup();
  await settle();
  valid.querySelector('a').click();
  await settle();
  const dialog = window.document.querySelector('dialog');
  const iframe = dialog.querySelector('iframe');
  assert.equal(dialog.open, true);
  assert.equal(iframe.hidden, false);
  assert.match(iframe.src, /^blob:/);
  assert.equal(stats.blob.type, 'application/pdf');
  assert.equal(stats.blob.size, example.length);
  assert.equal(dialog.querySelector('[data-part-pdf-download]').download, valid.dataset.filename);
  assert.equal(dialog.querySelector('[data-part-pdf-new-tab]').href, iframe.src);
  assert.equal(dialog.querySelector('input'), null);
  dialog.dispatchEvent(new window.Event('close'));
  assert.deepEqual(stats.revoked, ['blob:https://taitai2025.github.io/test-pdf']);
  dom.window.close();
});

test('preserves the original download when fetch fails or bytes differ', async () => {
  for (const options of [{rejectPDF: true}, {corruptPDF: true}]) {
    const {dom, window, valid, stats} = setup(options);
    await settle();
    valid.querySelector('a').click();
    await settle();
    const dialog = window.document.querySelector('dialog');
    assert.equal(dialog.querySelector('iframe').hidden, true);
    assert.equal(dialog.querySelector('[data-part-pdf-download]').href, raw + path);
    assert.equal(stats.blob, null);
    dom.window.close();
  }
});

test('retains the direct link if a mobile browser lacks a native PDF viewer', async () => {
  const {dom, window, valid, stats} = setup({pdfViewerEnabled: false});
  await settle();
  const event = new window.MouseEvent('click', {bubbles: true, cancelable: true});
  valid.querySelector('a').dispatchEvent(event);
  assert.equal(event.defaultPrevented, false);
  assert.equal(window.document.querySelector('dialog'), null);
  assert.equal(stats.calls.length, 1);
  dom.window.close();
});

test('leaves archive downloads visible when there is no release manifest', async () => {
  const {dom, window} = setup({manifestStatus: 404});
  await settle();
  assert.equal(window.document.querySelectorAll('[data-part-pdf-link]').length, 0);
  assert.match(window.document.querySelector('#files a[href$=".zip"]').href, /\.zip$/);
  dom.window.close();
});
