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
  const refresh = () => {
    const words = normalize(search.value.trim()).split(/\s+/).filter(Boolean);
    let count = 0;
    for (const item of items) {
      item.hidden = Boolean((scope?.value && item.dataset.scope !== scope.value)
        || (ensemble?.value && item.dataset.ensemble !== ensemble.value)
        || !words.every(word => normalize(item.dataset.search).includes(word)));
      if (!item.hidden) count += 1;
    }
    status.textContent = `显示 ${count} / ${items.length} 项`;
    if (empty) empty.hidden = count > 0;
  };
  filters.addEventListener('submit', (event) => event.preventDefault());
  filters.addEventListener('input', refresh);
  filters.addEventListener('change', refresh);
  filters.removeAttribute('hidden');
  refresh();
}
