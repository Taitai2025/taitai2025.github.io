// Verify the real, generated showcase: no browser, network or remote writes.
// Run after build-score-site.py (or build-orchestra-showcase.py).
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';

const require = createRequire(import.meta.url);
const {JSDOM, VirtualConsole} = require('jsdom');
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const script = fs.readFileSync(path.join(root, 'scores/orchestras/showcase.js'), 'utf8');
const css = fs.readFileSync(path.join(root, 'scores/orchestras/showcase.css'), 'utf8');
const data = JSON.parse(fs.readFileSync(path.join(root, 'scores/orchestras/data.json'), 'utf8'));
const nmou = data.orchestras.find(entry => entry.slug === 'ustc-nmou');
const photoCount = nmou.gallery.length;
const videoCount = nmou.videos.length;
const galleryStatus = (current, total = photoCount) => new RegExp(`^${current} / ${total}(?:\\s|$)`);
const directory = '/scores/orchestras/';
const detail = `${directory}ustc-nmou/`;
const routes = [directory, ...data.orchestras.map(entry => `${directory}${entry.slug}/`)];
const entryFor = route => data.orchestras.find(entry => route === `${directory}${entry.slug}/`);
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

function surface(route = directory, {query = '', run = true, reduced = false} = {}) {
  const source = fs.readFileSync(path.join(root, route, 'index.html'), 'utf8');
  const errors = [];
  const console = new VirtualConsole();
  console.on('jsdomError', error => errors.push(error.message));
  const dom = new JSDOM(source, {url: `https://taitai2025.github.io${route}${query}`, runScripts: 'outside-only', virtualConsole: console});
  const w = dom.window;
  const doc = w.document;
  const q = selector => doc.querySelector(selector);
  const all = selector => [...doc.querySelectorAll(selector)];
  const scrolls = [];
  let reduce = reduced;
  let fetches = 0;
  w.matchMedia = () => ({matches: reduce});
  w.fetch = async () => { fetches += 1; throw new Error('Offline by test design'); };
  const track = q('[data-gallery-track]');
  if (track) {
    const slides = all('[data-gallery-slide]');
    track.getBoundingClientRect = () => ({left: 100, right: 1100, width: 1000, top: 0, bottom: 500, height: 500});
    slides.forEach((slide, index) => {
      slide.getBoundingClientRect = () => ({left: 100 + index * 810 - track.scrollLeft, right: 890 + index * 810 - track.scrollLeft, width: 790, top: 0, bottom: 500, height: 500});
    });
    track.scrollTo = options => {
      scrolls.push(options);
      track.scrollLeft = Math.min(slides.length * 790 + (slides.length - 1) * 20 - 1000, options.left);
      track.dispatchEvent(new w.Event('scroll'));
    };
    all('[data-gallery-slide] img').forEach(img => {
      Object.defineProperty(img, 'complete', {configurable: true, value: true});
      Object.defineProperty(img, 'naturalWidth', {configurable: true, value: Number(img.getAttribute('width'))});
    });
  }
  if (run) w.eval(script);
  const type = (selector, value, event = 'input') => {
    const node = q(selector);
    node.value = value;
    node.dispatchEvent(new w.Event(event, {bubbles: true}));
  };
  const key = (node, key, options = {}) => {
    const event = new w.KeyboardEvent('keydown', {key, bubbles: true, cancelable: true, ...options});
    node.dispatchEvent(event);
    return event;
  };
  return {w, doc, q, all, type, key, scrolls, errors, setReduced(value) { reduce = value; }, get fetches() { return fetches; }, close() { dom.window.close(); }};
}

const results = [];
async function check(name, task) {
  try { await task(); results.push({name, passed: true}); }
  catch (error) { results.push({name, passed: false, error: error.stack || error.message}); }
}

await check('static pages remain useful without JavaScript or a data fetch', () => {
  for (const route of routes) {
    const s = surface(route, {run: false});
    try {
      const entry = entryFor(route);
      assert.equal(s.all('h1').length, 1);
      assert.equal(s.all('[data-showcase-entry][hidden]').length, 0);
      if (s.q('[data-showcase-form]')) assert.equal(s.q('[data-showcase-form]').hidden, true);
      if (entry) {
        assert.equal(s.all('[data-gallery-slide]').length, entry.gallery.length);
        assert.equal(s.all('.orchestra-video').length, entry.videos.length);
        assert.ok(s.q('#sources').textContent.trim().length > 20, 'Each orchestra identifies its own source');
        if (route === detail) {
          assert.match(s.q('#story').textContent, /2002 年 12 月/);
          assert.match(s.q('#story').textContent, /中华音韵/);
          assert.match(s.q('#sources').textContent, /不代表当前人数或累计届数/);
          assert.match(s.q('#sources').textContent, /原文发布日期尚未确认/);
          assert.doesNotMatch(s.q('.orchestra-detail-hero').textContent, /70\s*余|23\s*届/);
        }
      } else {
        assert.equal(s.all('.orchestra-directory-card').length, data.orchestras.length);
        assert.ok(s.q('.orchestra-collection-note').textContent.includes(`当前收录 ${data.orchestras.length} 支乐团`));
      }
    } finally { s.close(); }
  }
});

await check('SEO describes real entries and uses real local photographs', () => {
  for (const route of routes) {
    const s = surface(route, {run: false});
    try {
      const entry = entryFor(route);
      assert.equal(s.q('link[rel=canonical]').href, `https://taitai2025.github.io${route}`);
      assert.ok(s.q('meta[name=description]').content.length >= 30);
      const socialImage = new URL(s.q('meta[property="og:image"]').content);
      assert.equal(socialImage.origin, 'https://taitai2025.github.io');
      assert.ok(fs.existsSync(path.join(root, socialImage.pathname)));
      assert.ok(s.q('meta[property="og:image:alt"]').content.length > 10);
      const schema = JSON.parse(s.q('script[type="application/ld+json"]').textContent);
      assert.ok(schema['@graph'].some(node => node['@type'] === 'BreadcrumbList'));
      if (entry) {
        const group = schema['@graph'].find(node => node['@type'] === 'MusicGroup');
        assert.equal(group.name, entry.name);
        if (entry.founded) assert.equal(group.foundingDate, entry.founded);
        else assert.equal(group.foundingDate, undefined, 'Unknown founding dates are not invented for search engines');
        const official = Object.entries(entry.sources).filter(([key, value]) => key.startsWith('official') && value?.url).map(([, value]) => value.url);
        assert.deepEqual(group.sameAs || [], official);
        assert.ok(!JSON.stringify(schema).includes('datePublished'));
        assert.ok(!JSON.stringify(schema).includes('numberOfEmployees'));
      } else {
        const collection = schema['@graph'].find(node => node['@type'] === 'CollectionPage');
        assert.equal(collection.mainEntity.numberOfItems, data.orchestras.length);
        assert.deepEqual(collection.mainEntity.itemListElement.map(item => item.url), data.orchestras.map(entry => `https://taitai2025.github.io${directory}${entry.slug}/`));
      }
      for (const img of s.all('img')) {
        assert.ok(img.alt.length > 10);
        assert.ok(Number(img.width) > 0 && Number(img.height) > 0);
        assert.ok(fs.existsSync(path.join(root, img.getAttribute('src'))));
      }
      for (const [selector, attribute, asset] of [
        ['link[rel=stylesheet]', 'href', '/scores/orchestras/showcase.css'],
        ['script[src]', 'src', '/scores/orchestras/showcase.js'],
      ]) {
        const matches = s.all(selector).filter(node => new URL(node.getAttribute(attribute), s.w.location.href).pathname === asset);
        assert.equal(matches.length, 1, `One current ${asset} reference`);
        const url = new URL(matches[0].getAttribute(attribute), s.w.location.href);
        const fingerprint = createHash('sha256').update(fs.readFileSync(path.join(root, asset))).digest('hex').slice(0, 12);
        assert.equal(url.searchParams.get('v'), fingerprint, `Cache fingerprint for ${asset}`);
      }
    } finally { s.close(); }
  }
});

await check('every source, internal jump and downloaded intake template resolves', () => {
  for (const route of routes) {
    const s = surface(route, {run: false});
    try {
      const ids = s.all('[id]').map(node => node.id);
      assert.equal(new Set(ids).size, ids.length);
      for (const a of s.all('.orchestra-showcase a[href]')) {
        const href = a.getAttribute('href');
        if (href.startsWith('#')) assert.ok(s.doc.getElementById(href.slice(1)), `Missing jump ${href}`);
        else if (href.startsWith('/')) {
          const url = new URL(href, s.w.location.href);
          const target = path.join(root, url.pathname, url.pathname.endsWith('/') ? 'index.html' : '');
          assert.ok(fs.existsSync(target), `Missing local file ${target}`);
          if (url.hash) assert.ok(fs.readFileSync(target, 'utf8').includes(`id="${url.hash.slice(1)}"`), `Missing source anchor ${url.href}`);
        } else if (href.startsWith('mailto:')) {
          assert.equal(new URL(href).pathname, 'yangshutai26@mails.ucas.ac.cn');
          assert.ok(new URL(href).searchParams.get('subject'), 'Submission email has a useful subject');
        } else {
          assert.ok(href.startsWith('https://'));
          if (a.target === '_blank') assert.ok(a.rel.includes('noopener') && a.rel.includes('noreferrer'));
        }
      }
      const intake = s.q('a[download]');
      assert.ok(intake.href.endsWith('/scores/orchestras/intake-template.txt'));
      assert.ok(s.q('#contribute a[href="/scores/orchestras/submit/"]'), 'The orchestra call to action opens its dedicated intake');
      assert.equal(s.q('#contribute a[href="/scores/tools/cooperation/#cooperation"]'), null);
      assert.match(s.q('#contribute').textContent, /点击或下载不会自动提交资料/);
    } finally { s.close(); }
  }
});

await check('Chinese aliases, case and fullwidth multi-word searches match the real orchestra', () => {
  const s = surface();
  try {
    for (const value of ['中科大', '中国科大', '小乐', '合肥', 'ＮＭＯＵ USTC', 'nationalities music']) {
      s.type('[data-showcase-search]', value);
      assert.equal(s.all('[data-showcase-entry]:not([hidden])').length, 1, value);
    }
    assert.equal(s.fetches, 0);
    assert.deepEqual(s.errors, []);
  } finally { s.close(); }
});

await check('empty results explain the next step; reset restores results and focuses the search', () => {
  const s = surface(directory, {query: '?from=homepage#orchestra-list'});
  try {
    s.type('[data-showcase-search]', '尚未收录的另一所学校');
    assert.equal(s.all('[data-showcase-entry]:not([hidden])').length, 0);
    assert.equal(s.q('[data-showcase-empty]').hidden, false);
    assert.ok(s.q('[data-showcase-status]').textContent.includes(`0 / ${data.orchestras.length}`));
    assert.equal(new URL(s.w.location.href).searchParams.get('from'), 'homepage');
    assert.equal(s.w.location.hash, '#orchestra-list');
    s.q('[data-showcase-reset]').click();
    assert.equal(s.all('[data-showcase-entry]:not([hidden])').length, data.orchestras.length);
    assert.equal(s.q('[data-showcase-empty]').hidden, true);
    assert.equal(s.doc.activeElement, s.q('[data-showcase-search]'));
    assert.equal(new URL(s.w.location.href).searchParams.get('q'), null);
  } finally { s.close(); }
});

await check('shareable search URLs and back navigation restore filters without HTML injection', () => {
  const s = surface(directory, {query: '?q=NMOU&country=CN'});
  try {
    assert.equal(s.q('[data-showcase-search]').value, 'NMOU');
    assert.equal(s.q('[data-showcase-select]').value, 'CN');
    const originalImages = s.all('img').length;
    s.type('[data-showcase-search]', '<img src=x onerror=alert(1)>');
    assert.equal(s.all('img').length, originalImages);
    assert.equal(s.all('[data-showcase-entry]:not([hidden])').length, 0);
    s.w.history.pushState({}, '', '?q=合肥&country=CN');
    s.w.dispatchEvent(new s.w.PopStateEvent('popstate'));
    assert.equal(s.q('[data-showcase-search]').value, '合肥');
    assert.equal(s.all('[data-showcase-entry]:not([hidden])').length, 1);
    s.w.history.pushState({}, '', '?country=unregistered');
    s.w.dispatchEvent(new s.w.PopStateEvent('popstate'));
    assert.equal(s.q('[data-showcase-select]').value, '');
    const submit = new s.w.Event('submit', {bubbles: true, cancelable: true});
    s.q('[data-showcase-form]').dispatchEvent(submit);
    assert.ok(submit.defaultPrevented);
  } finally { s.close(); }
});

await check('performance title and year filters compose and retain the full static archive', () => {
  const s = surface(detail, {query: '?year=2025'});
  try {
    assert.equal(s.all('.orchestra-video:not([hidden])').length, nmou.videos.filter(video => video.year === 2025).length);
    s.type('[data-showcase-select]', '2021', 'change');
    s.type('[data-showcase-search]', 'acg');
    assert.equal(s.all('.orchestra-video:not([hidden])').length, 1);
    assert.match(s.q('.orchestra-video:not([hidden])').textContent, /2021.*ACG/s);
    s.type('[data-showcase-select]', '2025', 'change');
    assert.equal(s.all('.orchestra-video:not([hidden])').length, 0);
    assert.equal(s.q('[data-showcase-empty]').hidden, false);
    s.q('[data-showcase-form]').reset();
    assert.equal(s.all('.orchestra-video:not([hidden])').length, videoCount);
    assert.equal(s.q('[data-showcase-empty]').hidden, true);
    assert.equal(s.fetches, 0);
  } finally { s.close(); }
});

await check('every listed orchestra opens its own static detail, gallery and performance filters', async () => {
  const listing = surface(directory);
  try {
    for (const entry of data.orchestras) {
      listing.type('[data-showcase-search]', entry.name);
      const visible = listing.all('[data-showcase-entry]:not([hidden])');
      assert.equal(visible.length, 1, entry.slug);
      assert.equal(visible[0].querySelector('h3 a').getAttribute('href'), `${directory}${entry.slug}/`);
      const s = surface(`${directory}${entry.slug}/`);
      try {
        const photos = entry.gallery.length;
        assert.equal(s.all('[data-gallery-slide]').length, photos);
        assert.equal(s.all('[data-gallery-to]').length, photos);
        assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(1, photos));
        s.q(`[data-gallery-to="${photos - 1}"]`).click();
        await sleep(160);
        assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(photos, photos));
        assert.equal(s.q('[data-gallery-next]').disabled, true);
        const years = [...new Set(entry.videos.map(video => video.year))];
        for (const year of years) {
          s.type('[data-showcase-select]', String(year), 'change');
          assert.equal(s.all('.orchestra-video:not([hidden])').length, entry.videos.filter(video => video.year === year).length, `${entry.slug} ${year}`);
        }
        s.q('[data-showcase-form]').reset();
        assert.equal(s.all('.orchestra-video:not([hidden])').length, entry.videos.length);
        assert.deepEqual(s.errors, []);
        assert.equal(s.fetches, 0);
      } finally { s.close(); }
    }
    listing.q('[data-showcase-reset]').click();
    assert.equal(listing.all('[data-showcase-entry]:not([hidden])').length, data.orchestras.length);
  } finally { listing.close(); }
});

await check('NPU submission keeps its provenance, uncertain founding date and event-label years separate from NMOU facts', () => {
  const entry = data.orchestras.find(orchestra => orchestra.slug === 'npu-folk-orchestra');
  assert.ok(entry, 'The user-supplied NPU orchestra is included');
  const s = surface(`${directory}${entry.slug}/`, {run: false});
  try {
    assert.ok(s.q('h1').textContent.replace(/\s+/g, '').includes(entry.name));
    assert.equal(s.all('.orchestra-voices li').length, 4);
    assert.doesNotMatch(s.q('#story').textContent, /2002 年 12 月|中华音韵|中国科学技术大学/);
    const note = s.q('.orchestra-source-note').textContent;
    assert.match(note, /2005/);
    assert.match(note, /口述/);
    assert.match(note, /不将其作为已核实成立日期/);
    assert.match(note, /2026 年 11 月/);
    assert.match(note, /(?:允许|授权).*展示/);
    const graph = JSON.parse(s.q('script[type="application/ld+json"]').textContent)['@graph'];
    const group = graph.find(item => item['@type'] === 'MusicGroup');
    assert.equal(group.foundingDate, undefined);
    assert.equal(group.sameAs, undefined);
    assert.equal(s.q('a[href="https://space.bilibili.com/64643274"]'), null, 'NPU must not inherit NMOU official-account links');
    assert.equal(s.all('.orchestra-honor').length, 0, 'Participation must not become an unverified award');
    const performances = s.q('#performances');
    assert.match(performances.textContent, /不等同于实际演出日/);
    assert.match(performances.textContent, /2025\.12\.25/);
    assert.match(performances.textContent, /未将上传账号认定为乐团官方账号/);
    for (const card of s.all('.orchestra-video')) {
      const url = new URL(card.querySelector('h3 a').href);
      assert.equal(url.search, '');
    }
    for (const link of s.all('a[href]')) assert.doesNotMatch(link.getAttribute('href'), /\.docx?(?:$|\?)/i, 'The original editable submission is not a public download');
  } finally { s.close(); }
});

await check('gallery controls stop at either boundary and reveal the selected photo number', async () => {
  const s = surface(detail);
  try {
    assert.equal(s.q('[data-gallery-controls]').hidden, false);
    assert.equal(s.q('[data-gallery-prev]').disabled, true);
    assert.equal(s.q('[data-gallery-next]').disabled, false);
    assert.equal(s.scrolls.length, 0, 'The gallery must not auto-play');
    s.q('[data-gallery-next]').click();
    assert.equal(s.scrolls.at(-1).left, 810);
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(2));
    assert.equal(s.q('[data-gallery-to="1"]').getAttribute('aria-current'), 'true');
    s.q(`[data-gallery-to="${photoCount - 1}"]`).click();
    await sleep(160);
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(photoCount));
    assert.equal(s.q('[data-gallery-next]').disabled, true);
    s.q('[data-gallery-to="0"]').click();
    assert.equal(s.q('[data-gallery-prev]').disabled, true);
    assert.equal(s.all('[data-gallery-to][aria-current=true]').length, 1);
    assert.deepEqual(s.errors, []);
  } finally { s.close(); }
});

await check('keyboard navigation works on the gallery without stealing keys from image links', () => {
  const s = surface(detail);
  try {
    const track = s.q('[data-gallery-track]');
    track.focus();
    assert.equal(track.tabIndex, 0);
    assert.ok(s.key(track, 'ArrowRight').defaultPrevented);
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(2));
    assert.ok(s.key(track, 'End').defaultPrevented);
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(photoCount));
    s.key(track, 'Home');
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(1));
    const before = s.scrolls.length;
    assert.equal(s.key(s.q('.orchestra-gallery-image'), 'ArrowRight').defaultPrevented, false);
    assert.equal(s.key(track, 'ArrowRight', {ctrlKey: true}).defaultPrevented, false);
    assert.equal(s.scrolls.length, before);
  } finally { s.close(); }
});

await check('touch or scrollbar movement updates controls after scrolling stops', async () => {
  const s = surface(detail);
  try {
    const track = s.q('[data-gallery-track]');
    track.scrollLeft = 2430;
    track.dispatchEvent(new s.w.Event('scroll'));
    await sleep(160);
    assert.match(s.q('[data-gallery-status]').textContent, galleryStatus(4));
    assert.equal(s.q('[data-gallery-to="3"]').getAttribute('aria-current'), 'true');
    assert.equal(s.q('[data-gallery-prev]').disabled, false);
  } finally { s.close(); }
});

await check('reduced motion is honoured when the preference changes during the visit', () => {
  const s = surface(detail);
  try {
    s.q('[data-gallery-next]').click();
    assert.equal(s.scrolls.at(-1).behavior, 'smooth');
    s.setReduced(true);
    s.q('[data-gallery-next]').click();
    assert.equal(s.scrolls.at(-1).behavior, 'auto');
    assert.match(css, /@media\(prefers-reduced-motion:reduce\)/);
  } finally { s.close(); }
});

await check('failed images retain their captions and explain the failure without hiding the archive', () => {
  const s = surface(detail);
  try {
    const slide = s.q('[data-gallery-slide]');
    const img = slide.querySelector('img');
    img.dispatchEvent(new s.w.Event('error'));
    assert.equal(slide.querySelector('[data-image-error]').hidden, false);
    assert.ok(img.classList.contains('is-unavailable'));
    assert.match(slide.querySelector('h3').textContent, /青风抚乐/);
    assert.equal(s.all('.orchestra-video:not([hidden])').length, videoCount);
    img.dispatchEvent(new s.w.Event('load'));
    assert.equal(slide.querySelector('[data-image-error]').hidden, true);
    assert.equal(s.fetches, 0);
    assert.deepEqual(s.errors, []);
  } finally { s.close(); }
});

await check('print stylesheet expands the complete photo gallery and filtered performance archive', () => {
  const print = css.slice(css.indexOf('@media print'));
  assert.match(print, /\.orchestra-gallery-track\{[^}]*display:grid[^}]*overflow:visible/);
  assert.match(print, /\[data-showcase-entry\]\[hidden\]\{display:block!important/);
  assert.match(print, /\.orchestra-gallery-slide\{[^}]*break-inside:avoid/);
  assert.match(print, /content:attr\(href\)/);
});

for (const result of results) {
  console.log(`${result.passed ? 'PASS' : 'FAIL'} ${result.name}`);
  if (!result.passed) console.error(result.error);
}
console.log(`${results.filter(result => result.passed).length}/${results.length} showcase checks passed.`);
if (results.some(result => !result.passed)) process.exitCode = 1;
