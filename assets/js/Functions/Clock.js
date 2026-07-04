(function () {
  'use strict';

  let _timerId = null;

  // The clock always shows the site owner's local time (Beijing, UTC+8),
  // matching the "GMT+8" placeholder text in the markup.
  function updateClock() {
    const hm = new Date().toLocaleTimeString('en-GB', {
      timeZone: 'Asia/Shanghai',
      hour12: false,
      hour: '2-digit',
      minute: '2-digit',
    });
    const timeString = `GMT+8 ${hm}`;

    const ids = ['top-clock', 'clock', 'clock-social', 'clock-toolkit', 'clock-schedule', 'clock-meditations'];
    ids.forEach((id) => {
      const el = document.getElementById(id);
      if (el) el.textContent = timeString;
    });
  }

  function start() {
    updateClock();

    // prevent double interval
    if (_timerId !== null) clearInterval(_timerId);
    _timerId = setInterval(updateClock, 1000);
  }

  window.Clock = {
    start,
    updateClock,
  };
})();
