#!/usr/bin/env python3
"""Check catalogue meaning and real filter queries without generating site files."""
import importlib.util
import json
from html.parser import HTMLParser
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('score_catalogue_build', ROOT / 'scripts/build-score-site.py')
build = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = build
spec.loader.exec_module(build)
works = json.loads((ROOT / 'scores/data/works.json').read_text())
sources = json.loads((ROOT / 'scores/data/sources.json').read_text())
parts = build.window_json(ROOT / 'scores/parts-index.js')
rosters = json.loads((ROOT / 'scores/tools/rosters.json').read_text())
build.prepare_works(works, rosters, parts)


class Article(HTMLParser):
    def __init__(self, html):
        super().__init__()
        self.attrs = None
        self.feed(html)

    def handle_starttag(self, tag, attrs):
        if tag == 'article':
            self.attrs = dict(attrs)


records = {
    'works': [{'id': w['slug'], 'attrs': Article(build.work_card(w)).attrs} for w in works],
    'open': [{'id': w['slug'], 'attrs': Article(build.open_card(w)).attrs} for w in sources['openScores']],
    'sources': [{'id': str(i), 'attrs': Article(build.source_card(w)).attrs} for i, w in enumerate(sources['sources'])],
}
cases = [
    {'group': 'works', 'q': '秦兵马俑 固定调', 'expected': ['qin-bingmayong']},
    {'group': 'works', 'q': '秦·兵马俑简谱', 'expected': ['qin-bingmayong']},
    {'group': 'works', 'q': '秦兵马俑总谱', 'expected': []},
    {'group': 'works', 'q': '大东北我的家乡总谱', 'expected': ['dongbei-ensemble', 'dongbei-orchestra', 'dongbei-mixed']},
    {'group': 'works', 'q': 'LaLaLand', 'expected': ['la-la-land']},
    {'group': 'works', 'q': '秦兵马俑 笛子', 'expected': ['qin-bingmayong']},
    {'group': 'works', 'q': '秦兵马俑 打击乐', 'expected': ['qin-bingmayong']},
    {'group': 'works', 'q': '', 'facets': {'format': '简谱指挥总谱'}, 'expected': ['dongbei-ensemble', 'dongbei-orchestra', 'dongbei-mixed']},
    {'group': 'open', 'q': '二胡', 'expected': ['liangxiao-liu-tianhua-early', 'yueye-liu-tianhua-early', 'xianjuyin-liu-tianhua-early', 'bingzhongyin-liu-tianhua-early']},
    {'group': 'open', 'q': '', 'facets': {'notation': '简谱'}, 'expected': ['yang-guan-san-die-1920']},
    {'group': 'open', 'q': '', 'facets': {'notation': '五线谱', 'instrument': '二胡'}, 'expected': ['liangxiao-liu-tianhua-early', 'yueye-liu-tianhua-early', 'xianjuyin-liu-tianhua-early']},
    {'group': 'open', 'q': '土耳其进行曲总谱', 'expected': []},
    {'group': 'sources', 'q': '', 'facets': {'scope': '付费租借'}, 'expected': ['67']},
    {'group': 'sources', 'q': '', 'facets': {'scope': '登记申请', 'provider': '竹韵小集'}, 'expected': ['65', '66']},
]

# Exercise the actual browser filter script with a small DOM adapter. No rendered
# page is written and no browser, external dependency or network is required.
runner = r'''
const fs = require('node:fs');
const vm = require('node:vm');
const input = JSON.parse(fs.readFileSync(0, 'utf8'));
const script = fs.readFileSync(input.script, 'utf8');
const results = input.cases.map(test => {
  const nodes = input.records[test.group].map(record => ({
    ...record, hidden: false,
    dataset: Object.fromEntries(Object.entries(record.attrs).filter(([key]) => key.startsWith('data-'))
      .map(([key, value]) => [key.slice(5).replace(/-([a-z])/g, (_, letter) => letter.toUpperCase()), value])),
    getAttribute(name) { return this.attrs[name] ?? null; },
    querySelectorAll() { return []; }, querySelector() { return null; },
  }));
  const selected = test.facets || {};
  const selectors = Object.keys(selected).map(name => ({name, value: '',
    options: [...new Set(nodes.flatMap(node => (node.attrs[`data-${name}`] || '').split('|')))]
      .map(value => ({value})),
  }));
  const search = {value: ''}, status = {}, empty = {}, listeners = {};
  const form = {querySelector() { return search; }, querySelectorAll() { return selectors; },
    addEventListener(name, fn) { listeners[name] = fn; }, removeAttribute() {}};
  const params = new URLSearchParams({q: test.q, ...selected});
  const location = {search: `?${params}`, pathname: '/scores/search/', hash: ''};
  let saved = '';
  const context = {URLSearchParams, location, setTimeout: fn => fn(),
    history: {state: null, replaceState(_state, _title, url) { saved = url; }},
    document: {querySelector(name) { return name === '[data-filters]' ? form : name === '[data-filter-status]' ? status : empty; },
      querySelectorAll() { return nodes; }}};
  vm.runInNewContext(script, context);
  const actual = nodes.filter(node => !node.hidden).map(node => node.id);
  listeners.input();
  const savedParams = new URLSearchParams(saved.split('?')[1] || '');
  const remembered = (!test.q || savedParams.get('q') === test.q)
    && Object.entries(selected).every(([key, value]) => savedParams.get(key) === value);
  return {label: test.q || JSON.stringify(selected), actual, expected: test.expected, remembered};
});
process.stdout.write(JSON.stringify(results));
'''
payload = {'script': str(ROOT / 'scores/filters.js'), 'records': records, 'cases': cases}
process = subprocess.run(['node', '-e', runner], input=json.dumps(payload, ensure_ascii=False), capture_output=True, text=True, check=True)
results = json.loads(process.stdout)
for result in results:
    assert sorted(result['actual']) == sorted(result['expected']), result
    assert result['remembered'], result

open_scores = sources['openScores']
assert all(w.get('instruments') for w in open_scores)
zip_scores = [w for w in open_scores if w['download'].lower().endswith('.zip')]
assert len(zip_scores) == 4
assert all('ZIP' in build.open_download_label(w) for w in zip_scores)
assert all('Space' not in w['details'] for w in open_scores)
assert all('总谱' not in Article(build.work_card(w)).attrs['data-formats'].split('|') for w in works if not w['fullScores'])
assert all(w['access'] != '原机构查阅' for w in sources['sources'])
assert '曾叶发' in build.source_card(sources['sources'][13])

captured = {}
original_output = build.output
build.output = lambda route, title, desc, body, **kwargs: captured.update({route: {'desc': desc, 'body': body}})
try:
    build.work_pages(works, parts)
finally:
    build.output = original_output
assert '署名待补录' in captured['/scores/work/wusheng-zuqu/']['body']
assert '指挥总谱' not in captured['/scores/work/qin-bingmayong/']['desc']
assert '另附简谱指挥总谱' in captured['/scores/work/dongbei-ensemble/']['desc']
print(f'PASS: {len(cases)} real filter queries and URL-state cases; {len(works)} work versions; {len(open_scores)} open editions; {len(sources["sources"])} resource entries. No site files generated.')
