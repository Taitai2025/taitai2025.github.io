
window.SCHEDULE_PAGE_I18N = window.SCHEDULE_PAGE_I18N || {};
window.SCHEDULE_PAGE_I18N.en = {
  heading: "Current Rhythm",
  subtitle: "Not a public timetable down to the hour, but a lighter snapshot of where my recent time and attention are going.",
  btn_my: "Current Rhythm",
  btn_ustc: "USTC Timetable",
  btn_calendar: "Calendar",
  focus_title: "Current focus",
  focus_body: "This semester I am mainly in Beijing for my undergraduate thesis, with sustained attention to numerical ODE methods, accelerated optimization algorithms, and paper reading.",
  base_title: "Usual base",
  base_body: "I am mostly based in Beijing, often around UCAS Yuquan Road and Zhongguancun, and I occasionally return to Hefei for academic matters and orchestra work.",
  reach_title: "Best way to reach me",
  reach_body: "Email is the best choice for academic or formal communication; friends can reach me through WeChat. Sundays are often reserved for rehearsal or orchestra-related work.",
  weekly_title: "A rough weekly rhythm",
  timeblock: "Time block",
  monfri: "Mon–Fri",
  saturday: "Saturday",
  sunday: "Sunday",
  morning: "Morning",
  afternoon: "Afternoon",
  evening: "Evening",
  monfri_morning: "Paper reading, derivations, and thesis-related core tasks",
  sat_morning: "Supplementary reading, errands, and lighter recovery-oriented tasks",
  sun_morning: "Rest, tidying up, and light exercise",
  monfri_afternoon: "Writing, note organization, and communication with supervisors or classmates",
  sat_afternoon: "Music-related tasks, travel back, or temporary arrangements",
  sun_afternoon: "UCAS orchestra rehearsal or orchestra-related work",
  monfri_evening: "Running, badminton, and a brief review of the day",
  sat_evening: "Meeting friends, watching films, or relaxing",
  sun_evening: "Closing the week and planning the next one",
  notes_title: "A small local note to myself",
  notes_body: "This note is saved only in the current browser, useful for small goals or temporary reminders.",
  notes_placeholder: "Write a short reminder here...",
  notes_saved: "Saved locally",
  ustc_title: "USTC timetable placeholder",
  ustc_body: "This section is reserved for your future semester or course timetable. The structure is already separated out in JS/CSS so you can add your own class blocks later.",
  calendar_title: "Calendar placeholder",
  calendar_body: "This section is reserved for future calendar integration or manually maintained events.",
};


(function () {
  const mount = document.getElementById("mount-schedule") || document.body;
  mount.insertAdjacentHTML("beforeend", `
  <div id="schedule">
    <button id="toggle-btn-schedule">
      <span><i class="fas fa-sun"></i></span>
    </button>
    <div id="clock-schedule">GMT+8 00:00</div>

    <div class="container">
      <div class="schedule-heading" data-sched-i18n="heading">Current Rhythm</div>
      <p class="page-subtitle" data-sched-i18n="subtitle">Not a public timetable down to the hour, but a lighter snapshot of where my recent time and attention are going.</p>

      <div class="schedule-switcher">
        <button class="schedule-switch-btn active" data-view="my-timetable" data-sched-i18n="btn_my">Current Rhythm</button>
        <button class="schedule-switch-btn" data-view="ustc-timetable" data-sched-i18n="btn_ustc">USTC Timetable</button>
        <button class="schedule-switch-btn" data-view="calendar" data-sched-i18n="btn_calendar">Calendar</button>
      </div>

      <div class="schedule-section active" id="my-timetable-section">
        <div class="schedule-grid">
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="focus_title">Current focus</div>
            <p data-sched-i18n="focus_body">This semester I am mainly in Beijing for my undergraduate thesis, with sustained attention to numerical ODE methods, accelerated optimization algorithms, and paper reading.</p>
          </div>
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="base_title">Usual base</div>
            <p data-sched-i18n="base_body">I am mostly based in Beijing, often around UCAS Yuquan Road and Zhongguancun, and I occasionally return to Hefei for academic matters and orchestra work.</p>
          </div>
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="reach_title">Best way to reach me</div>
            <p data-sched-i18n="reach_body">Email is the best choice for academic or formal communication; friends can reach me through WeChat. Sundays are often reserved for rehearsal or orchestra-related work.</p>
          </div>
        </div>

        <div class="section">
          <h2 data-sched-i18n="weekly_title">A rough weekly rhythm</h2>
          <div class="routine-table-wrap">
            <table>
              <thead>
                <tr>
                  <th data-sched-i18n="timeblock">Time block</th>
                  <th data-sched-i18n="monfri">Mon–Fri</th>
                  <th data-sched-i18n="saturday">Saturday</th>
                  <th data-sched-i18n="sunday">Sunday</th>
                </tr>
              </thead>
              <tbody>
                <tr>
                  <td data-sched-i18n="morning">Morning</td>
                  <td data-sched-i18n="monfri_morning">Paper reading, derivations, and thesis-related core tasks</td>
                  <td data-sched-i18n="sat_morning">Supplementary reading, errands, and lighter recovery-oriented tasks</td>
                  <td data-sched-i18n="sun_morning">Rest, tidying up, and light exercise</td>
                </tr>
                <tr>
                  <td data-sched-i18n="afternoon">Afternoon</td>
                  <td data-sched-i18n="monfri_afternoon">Writing, note organization, and communication with supervisors or classmates</td>
                  <td data-sched-i18n="sat_afternoon">Music-related tasks, travel back, or temporary arrangements</td>
                  <td data-sched-i18n="sun_afternoon">UCAS orchestra rehearsal or orchestra-related work</td>
                </tr>
                <tr>
                  <td data-sched-i18n="evening">Evening</td>
                  <td data-sched-i18n="monfri_evening">Running, badminton, and a brief review of the day</td>
                  <td data-sched-i18n="sat_evening">Meeting friends, watching films, or relaxing</td>
                  <td data-sched-i18n="sun_evening">Closing the week and planning the next one</td>
                </tr>
              </tbody>
            </table>
          </div>
        </div>

        <div class="section">
          <h2 data-sched-i18n="notes_title">A small local note to myself</h2>
          <p class="small" data-sched-i18n="notes_body">This note is saved only in the current browser, useful for small goals or temporary reminders.</p>
          <textarea class="note-box" id="schedule-notes" data-sched-placeholder="notes_placeholder"></textarea>
          <div class="note-status" id="note-status"></div>
        </div>
      </div>

      <div class="schedule-section" id="ustc-timetable-section">
        <div class="placeholder-panel">
          <h2 data-sched-i18n="ustc_title">USTC timetable placeholder</h2>
          <p data-sched-i18n="ustc_body">This section is reserved for your future semester or course timetable. The structure is already separated out in JS/CSS so you can add your own class blocks later.</p>
        </div>
      </div>

      <div class="schedule-section" id="calendar-section">
        <div class="placeholder-panel">
          <h2 data-sched-i18n="calendar_title">Calendar placeholder</h2>
          <p data-sched-i18n="calendar_body">This section is reserved for future calendar integration or manually maintained events.</p>
        </div>
      </div>
    </div>
  </div>
`);
})();
