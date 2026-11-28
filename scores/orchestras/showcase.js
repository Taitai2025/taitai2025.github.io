/* Progressive enhancement only: every story, photograph and link is in HTML. */
(() => {
  'use strict';
  const normalize = value => String(value || '').normalize('NFKC').toLocaleLowerCase().trim();

  function enhanceFilter(root) {
    const form = root.querySelector('[data-showcase-form]');
    const input = form?.querySelector('[data-showcase-search]');
    const select = form?.querySelector('[data-showcase-select]');
    const status = root.querySelector('[data-showcase-status]');
    const empty = root.querySelector('[data-showcase-empty]');
    const entries = [...root.querySelectorAll('[data-showcase-entry]')];
    if (!form || !input || !select || !status || !empty) return;
    const queryKey = root.dataset.queryKey;
    const facetKey = root.dataset.facetKey;
    const unit = root.dataset.unit;
    const allowed = new Set([...select.options].map(option => option.value));
    const indexed = entries.map(node => ({node, search: normalize(node.dataset.search), facet: node.dataset[facetKey]}));

    function update({writeURL = true} = {}) {
      const terms = normalize(input.value).split(/\s+/u).filter(Boolean);
      let count = 0;
      indexed.forEach(({node, search, facet}) => {
        const match = (!select.value || facet === select.value) && terms.every(term => search.includes(term));
        node.hidden = !match;
        if (match) count += 1;
      });
      status.textContent = `显示 ${count} / ${entries.length} ${unit}`;
      empty.hidden = count !== 0;
      if (writeURL) {
        try {
          const url = new URL(window.location.href);
          const query = input.value.trim().slice(0, input.maxLength);
          if (query) url.searchParams.set(queryKey, query);
          else url.searchParams.delete(queryKey);
          if (select.value) url.searchParams.set(facetKey, select.value);
          else url.searchParams.delete(facetKey);
          window.history.replaceState(window.history.state, '', url);
        } catch {
          // Filtering still works in local files or restricted history contexts.
        }
      }
    }

    function readURL() {
      const params = new URLSearchParams(window.location.search);
      input.value = (params.get(queryKey) || '').slice(0, input.maxLength);
      const selected = params.get(facetKey) || '';
      select.value = allowed.has(selected) ? selected : '';
      update({writeURL: false});
    }

    function reset() {
      input.value = '';
      select.value = '';
      update();
      input.focus();
    }

    input.addEventListener('input', () => update());
    select.addEventListener('change', () => update());
    form.addEventListener('submit', event => { event.preventDefault(); update(); });
    form.addEventListener('reset', event => { event.preventDefault(); reset(); });
    root.querySelectorAll('[data-showcase-reset]').forEach(button => button.addEventListener('click', reset));
    window.addEventListener('popstate', readURL);
    readURL();
    form.hidden = false;
  }

  function enhanceGallery(root) {
    const track = root.querySelector('[data-gallery-track]');
    const slides = [...root.querySelectorAll('[data-gallery-slide]')];
    const controls = root.querySelector('[data-gallery-controls]');
    const previous = root.querySelector('[data-gallery-prev]');
    const next = root.querySelector('[data-gallery-next]');
    const dots = [...root.querySelectorAll('[data-gallery-to]')];
    const status = root.querySelector('[data-gallery-status]');
    if (!track || slides.length < 2 || !controls || !previous || !next || !status) return;
    let current = 0;
    let scrollTimer;
    const reducedMotion = () => window.matchMedia?.('(prefers-reduced-motion: reduce)').matches ?? true;

    function render(index) {
      current = Math.max(0, Math.min(slides.length - 1, index));
      previous.disabled = current === 0;
      next.disabled = current === slides.length - 1;
      dots.forEach((dot, position) => {
        if (position === current) dot.setAttribute('aria-current', 'true');
        else dot.removeAttribute('aria-current');
      });
      const caption = slides[current].querySelector('h3')?.textContent || '';
      const message = `${current + 1} / ${slides.length} · ${caption}`;
      if (status.textContent !== message) status.textContent = message;
    }

    function nearest() {
      const left = track.getBoundingClientRect().left;
      const distances = slides.map(slide => Math.abs(slide.getBoundingClientRect().left - left));
      return distances.indexOf(Math.min(...distances));
    }

    function go(index) {
      const bounded = Math.max(0, Math.min(slides.length - 1, index));
      const left = Math.max(0, track.scrollLeft + slides[bounded].getBoundingClientRect().left - track.getBoundingClientRect().left);
      render(bounded);
      if (typeof track.scrollTo === 'function') track.scrollTo({left, behavior: reducedMotion() ? 'auto' : 'smooth'});
      else track.scrollLeft = left;
    }

    previous.addEventListener('click', () => go(current - 1));
    next.addEventListener('click', () => go(current + 1));
    dots.forEach(button => button.addEventListener('click', () => go(Number(button.dataset.galleryTo))));
    track.addEventListener('keydown', event => {
      if (event.target !== track || event.altKey || event.ctrlKey || event.metaKey) return;
      const destination = {ArrowLeft: current - 1, ArrowRight: current + 1, Home: 0, End: slides.length - 1}[event.key];
      if (destination === undefined) return;
      event.preventDefault();
      go(destination);
    });
    track.addEventListener('scroll', () => {
      window.clearTimeout(scrollTimer);
      scrollTimer = window.setTimeout(() => render(nearest()), 130);
    }, {passive: true});
    window.addEventListener('resize', () => render(nearest()));
    slides.forEach(slide => {
      const img = slide.querySelector('img');
      const fallback = slide.querySelector('[data-image-error]');
      if (!img || !fallback) return;
      const showError = () => { img.classList.add('is-unavailable'); fallback.hidden = false; };
      const clearError = () => { img.classList.remove('is-unavailable'); fallback.hidden = true; };
      img.addEventListener('error', showError);
      img.addEventListener('load', clearError);
      if (img.complete && img.naturalWidth === 0) showError();
    });
    render(0);
    controls.hidden = false;
  }

  document.querySelectorAll('[data-showcase-filter]').forEach(enhanceFilter);
  document.querySelectorAll('[data-orchestra-gallery]').forEach(enhanceGallery);
})();
