const filters = document.querySelector('[data-filters]');
if (filters) {
  const search = filters.querySelector('input[type="search"]');
  const scope = filters.querySelector('[name="scope"]');
  const ensemble = filters.querySelector('[name="ensemble"]');
  const items = [...document.querySelectorAll('[data-entry]')];
  const status = document.querySelector('[data-filter-status]');
  const empty = document.querySelector('[data-filter-empty]');
  const normalize = (value) => value.normalize('NFKC').toLocaleLowerCase();
  const query = new URLSearchParams(location.search).get('q');
  if (query) search.value = query.slice(0, 180);
  const entries = items.map((node) => ({
    node,
    searchable: normalize(node.dataset.search),
    title: normalize(node.dataset.workTitle || ''),
    files: [...node.querySelectorAll('[data-filename]')].map((file) => ({
      node: file, name: normalize(file.dataset.filename),
    })),
    fileCount: node.querySelector('[data-voice-count]'),
  }));
  const searchableWord = (word, entry) => {
    if (entry.searchable.includes(word)) return true;
    if (!entry.title) return false;
    const base = word.replace(/简谱分谱$|简谱$|分谱$/, '');
    if (base && entry.searchable.includes(base)) return true;
    if (!base.startsWith(entry.title)) return false;
    const remaining = base.slice(entry.title.length);
    return remaining !== '' && entry.searchable.includes(remaining);
  };
  const fileWord = (word, entry, file) => {
    if (word === '带主旋律') return /(?<![不无])带主旋律/.test(file.name);
    if (word === '不带主旋律' || word === '无主旋律') return /不带主旋律|无主旋律/.test(file.name);
    return entry.searchable.includes(word) || file.name.includes(word);
  };
  const refresh = () => {
    const words = normalize(search.value.trim()).split(/\s+/).filter(Boolean);
    const single = [];
    let count = 0;
    let visibleFiles = 0;
    for (const entry of entries) {
      const { node, files, fileCount } = entry;
      const filterMismatch = (scope?.value && node.dataset.scope !== scope.value)
        || (ensemble?.value && node.dataset.ensemble !== ensemble.value);
      if (fileCount) {
        let fileMatches = 0;
        for (const file of files) {
          file.node.hidden = !words.every(word => fileWord(word, entry, file));
          if (!file.node.hidden) fileMatches += 1;
        }
        fileCount.textContent = fileMatches;
        node.hidden = Boolean(filterMismatch || fileMatches === 0);
        if (!node.hidden) {
          visibleFiles += fileMatches;
          single.push(node);
        }
      } else {
        node.hidden = Boolean(filterMismatch || !words.every((word) => searchableWord(word, entry)));
      }
      if (!node.hidden) count += 1;
    }
    if (single.length === 1 && words.length) single[0].open = true;
    status.textContent = entries[0]?.fileCount
      ? `共 ${count} 个声部，${visibleFiles} 份匹配文件`
      : `显示 ${count} / ${items.length} 项`;
    if (empty) empty.hidden = count > 0;
  };
  filters.addEventListener('submit', (event) => event.preventDefault());
  filters.addEventListener('input', refresh);
  filters.addEventListener('change', refresh);
  filters.removeAttribute('hidden');
  refresh();
}
