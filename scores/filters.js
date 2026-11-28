const filters = document.querySelector('[data-filters]');
if (filters) {
  const search = filters.querySelector('input[type="search"]');
  const selectors = [...filters.querySelectorAll('select[name]')];
  const items = [...document.querySelectorAll('[data-entry]')];
  const status = document.querySelector('[data-filter-status]');
  const empty = document.querySelector('[data-filter-empty]');
  const normalize = (value) => value.normalize('NFKC').toLocaleLowerCase().replace(/[《》·•・]/g, '');
  const romanNumbers = new Map([
    ['i', '1'], ['ii', '2'], ['iii', '3'], ['iv', '4'], ['v', '5'], ['vi', '6'],
    ['vii', '7'], ['viii', '8'], ['ix', '9'], ['x', '10'], ['xi', '11'], ['xii', '12'],
  ]);
  const canonicalVoice = (value) => normalize(value).replace(
    /(\p{Script=Han})\s*(i{1,3}|iv|vi{0,3}|ix|xi{0,2}|[1-9]\d*)(?![a-z\d])/gu,
    (_, name, number) => `${name}‖${romanNumbers.get(number) ?? number}‖`,
  );
  const melodyTerms = new Map([
    ['主旋律备用', 'reserve'], ['带主旋律提示', 'with'], ['带主旋律', 'with'],
    ['不带主旋律提示', 'without'], ['不带主旋律', 'without'],
    ['无主旋律提示', 'without'], ['无主旋律', 'without'],
  ]);
  const formatAliases = new Map([
    ['带主旋律提示', '带主旋律'], ['不带主旋律提示', '不带主旋律'],
    ['无主旋律提示', '不带主旋律'], ['无主旋律', '不带主旋律'],
  ]);
  const params = new URLSearchParams(location.search);
  const query = params.get('q');
  if (query) search.value = query.slice(0, 180);
  for (const selector of selectors) {
    const value = params.get(selector.name);
    if (value && [...selector.options].some((option) => option.value === value)) selector.value = value;
  }
  const entries = items.map((node) => ({
    node,
    searchable: normalize(node.dataset.search),
    title: normalize(node.dataset.workTitle || '').split(/[（(｜|]/u)[0],
    formats: new Set(normalize(node.dataset.formats || '').split('|').filter(Boolean)),
    voice: canonicalVoice(node.dataset.search),
    files: [...node.querySelectorAll('[data-filename]')].map((file) => ({
      node: file, name: normalize(file.dataset.filename), melody: file.dataset.melody,
    })),
    fileCount: node.querySelector('[data-voice-count]'),
  }));
  const formats = [...new Set([
    ...formatAliases.keys(), ...entries.flatMap((entry) => [...entry.formats]),
  ])].sort((left, right) => right.length - left.length);
  const splitFormat = (word) => {
    const format = formats.find((term) => word.endsWith(term));
    if (!format) return [word];
    const prefix = word.slice(0, word.length - format.length);
    const canonical = formatAliases.get(format) ?? format;
    return prefix ? [prefix, canonical] : [canonical];
  };
  const searchableWord = (word, entry) => {
    if (entry.node.dataset.workTitle && formats.includes(word)) return entry.formats.has(word);
    if (entry.searchable.includes(word)) return true;
    if (/[a-z]/i.test(word) && entry.searchable.replace(/\s+/g, '').includes(word)) return true;
    if (!entry.title || !word.startsWith(entry.title)) return false;
    const remaining = word.slice(entry.title.length);
    return Boolean(remaining && entry.searchable.includes(remaining));
  };
  const fileWord = (word, entry, file) => {
    if (melodyTerms.has(word)) return file.melody === melodyTerms.get(word);
    if (word.includes('‖')) return entry.voice.includes(word);
    return entry.searchable.includes(word) || file.name.includes(word);
  };
  const rememberFilters = () => {
    const next = new URLSearchParams(location.search);
    const value = search.value.trim();
    if (value) next.set('q', value); else next.delete('q');
    for (const selector of selectors) {
      if (selector.value) next.set(selector.name, selector.value); else next.delete(selector.name);
    }
    const suffix = next.toString();
    history.replaceState(history.state, '', location.pathname + (suffix ? `?${suffix}` : '') + location.hash);
  };
  const refresh = (remember = false) => {
    const query = search.value.trim();
    const fileMode = Boolean(entries[0]?.fileCount);
    const words = (fileMode ? canonicalVoice(query) : normalize(query)).split(/\s+/).filter(Boolean);
    const terms = fileMode ? words : words.flatMap(splitFormat);
    const single = [];
    let count = 0;
    let visibleFiles = 0;
    for (const entry of entries) {
      const { node, files, fileCount } = entry;
      const filterMismatch = selectors.some((selector) => selector.value
        && !(node.getAttribute(`data-${selector.name}`) || '').split('|').includes(selector.value));
      if (fileCount) {
        let fileMatches = 0;
        for (const file of files) {
          file.node.hidden = !terms.every(word => fileWord(word, entry, file));
          if (!file.node.hidden) fileMatches += 1;
        }
        fileCount.textContent = fileMatches;
        node.hidden = Boolean(filterMismatch || fileMatches === 0);
        if (!node.hidden) {
          visibleFiles += fileMatches;
          single.push(node);
        }
      } else {
        node.hidden = Boolean(filterMismatch || !terms.every((word) => searchableWord(word, entry)));
      }
      if (!node.hidden) count += 1;
    }
    if (single.length === 1 && words.length) single[0].open = true;
    status.textContent = fileMode
      ? `共 ${count} 个声部，${visibleFiles} 份匹配文件`
      : `显示 ${count} / ${items.length} 项`;
    if (empty) empty.hidden = count > 0;
    if (remember) rememberFilters();
  };
  filters.addEventListener('submit', (event) => { event.preventDefault(); refresh(true); });
  filters.addEventListener('input', () => refresh(true));
  filters.addEventListener('change', () => refresh(true));
  filters.addEventListener('reset', () => setTimeout(() => refresh(true), 0));
  filters.removeAttribute('hidden');
  refresh();
}
