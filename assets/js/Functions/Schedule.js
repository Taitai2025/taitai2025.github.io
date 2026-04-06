(function () {
  function getLang() {
    if (window.SiteLang && typeof window.SiteLang.getLang === 'function') return window.SiteLang.getLang();
    return ((document.body && document.body.dataset && document.body.dataset.lang) || 'en').toLowerCase().startsWith('zh') ? 'zh' : 'en';
  }

  function dict() {
    const lang = getLang();
    const store = window.SCHEDULE_PAGE_I18N || {};
    return store[lang] || store.en || {};
  }

  function t(key) {
    const d = dict();
    return d[key] || key;
  }

  function applyScheduleI18N() {
    const root = document.getElementById('schedule');
    if (!root) return;
    root.querySelectorAll('[data-sched-i18n]').forEach((el) => {
      const key = el.getAttribute('data-sched-i18n');
      el.textContent = t(key);
    });
    root.querySelectorAll('[data-sched-placeholder]').forEach((el) => {
      const key = el.getAttribute('data-sched-placeholder');
      el.setAttribute('placeholder', t(key));
    });
  }

  function setScheduleView(view) {
    const mapView = (view === 'timetable') ? 'my-timetable' : view;
    document.querySelectorAll('.schedule-switch-btn').forEach((btn) => {
      btn.classList.toggle('active', btn.dataset.view === mapView);
    });
    document.querySelectorAll('#schedule .schedule-section').forEach((sec) => sec.classList.remove('active'));
    const target = document.getElementById(mapView + '-section');
    if (target) target.classList.add('active');
  }

  function initNoteBox() {
    const box = document.getElementById('schedule-notes');
    const status = document.getElementById('note-status');
    if (!box || !status) return;
    const KEY = 'taitai_schedule_local_note';
    box.value = localStorage.getItem(KEY) || '';
    let timer = null;
    box.addEventListener('input', () => {
      if (timer) clearTimeout(timer);
      timer = setTimeout(() => {
        localStorage.setItem(KEY, box.value);
        status.textContent = t('notes_saved');
      }, 220);
    });
  }

  function bindSwitchers() {
    document.querySelectorAll('.schedule-switch-btn').forEach((btn) => {
      btn.addEventListener('click', () => setScheduleView(btn.dataset.view));
    });
  }

  function initSchedulePage() {
    applyScheduleI18N();
    bindSwitchers();
    initNoteBox();
    setScheduleView('my-timetable');
  }

  function updateCalendarTheme() { /* reserved for future calendar integration */ }

  window.addEventListener('site:langchange', function () {
    applyScheduleI18N();
    const status = document.getElementById('note-status');
    if (status && status.textContent) status.textContent = t('notes_saved');
  });

  window.Schedule = window.Schedule || {};
  window.Schedule.setScheduleView = setScheduleView;
  window.Schedule.initSchedulePage = initSchedulePage;
  window.Schedule.initWeeksSelection = undefined;
  window.Schedule.initSemesterSelection = undefined;
  window.Schedule.updateCalendarTheme = updateCalendarTheme;
})();
