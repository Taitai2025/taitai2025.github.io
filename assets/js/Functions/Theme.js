(function () {
  'use strict';

  const STORAGE_KEY = 'site_theme'; // "dark" | "light"

  const TOGGLE_SELECTOR =
    '#toggle-btn, #toggle-btn-social, #toggle-btn-toolkit, #toggle-btn-schedule, #toggle-btn-meditations, #top-toggle-btn';

  function applyTheme(theme) {
    if (theme === 'dark') {
      document.body.classList.add('dark-mode');
    } else {
      document.body.classList.remove('dark-mode');
    }
  }

  function updateToggleBtnIcon() {
    const isDark = document.body.classList.contains('dark-mode');
    document.querySelectorAll(TOGGLE_SELECTOR).forEach((button) => {
      const icon = button.querySelector('i');
      if (!icon) return;
      icon.classList.toggle('fa-sun', !isDark);
      icon.classList.toggle('fa-moon', isDark);
    });
  }

  function saveTheme() {
    try {
      localStorage.setItem(
        STORAGE_KEY,
        document.body.classList.contains('dark-mode') ? 'dark' : 'light'
      );
    } catch (e) { /* ignore (private mode etc.) */ }
  }

  function toggleTheme() {
    document.body.classList.toggle('dark-mode');
    updateToggleBtnIcon();
    saveTheme();

    // keep compatibility with Schedule theme
    if (window.Schedule && typeof window.Schedule.updateCalendarTheme === 'function') {
      window.Schedule.updateCalendarTheme();
    }
  }

  function initialTheme() {
    // 1) explicit choice saved from a previous visit
    try {
      const saved = localStorage.getItem(STORAGE_KEY);
      if (saved === 'dark' || saved === 'light') return saved;
    } catch (e) { /* ignore */ }

    // 2) operating-system preference
    if (window.matchMedia) {
      if (window.matchMedia('(prefers-color-scheme: dark)').matches) return 'dark';
      if (window.matchMedia('(prefers-color-scheme: light)').matches) return 'light';
    }

    // 3) fallback: time of day (18:00 - 6:00 -> dark)
    const currentHour = new Date().getHours();
    return (currentHour >= 18 || currentHour < 6) ? 'dark' : 'light';
  }

  function initializeTheme() {
    applyTheme(initialTheme());
    updateToggleBtnIcon();
  }

  // Event delegation: keeps working even after Translate.js swaps
  // page innerHTML (which replaces the in-page legacy toggle buttons).
  function bindThemeToggles() {
    if (document.documentElement.dataset.themeDelegation === '1') return;
    document.documentElement.dataset.themeDelegation = '1';

    document.addEventListener('click', (e) => {
      const btn = e.target && e.target.closest ? e.target.closest(TOGGLE_SELECTOR) : null;
      if (!btn) return;
      toggleTheme();
    });
  }

  function init() {
    initializeTheme();
    bindThemeToggles();

    // After a language swap the in-page buttons are new DOM nodes;
    // re-sync their sun/moon icons with the current theme.
    window.addEventListener('site:langchange', updateToggleBtnIcon);
  }

  window.Theme = {
    init,
    toggleTheme,
    updateToggleBtnIcon,
    applyTheme,
  };
})();
