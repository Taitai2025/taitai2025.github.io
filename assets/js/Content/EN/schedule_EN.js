window.SCHEDULE_PAGE_I18N = window.SCHEDULE_PAGE_I18N || {};
window.SCHEDULE_PAGE_I18N.en = {
  heading: "Current Schedule & Everyday Rhythm",
  subtitle: "Autumn 2026: I am attending first-year graduate coursework at the UCAS Yanqi Lake campus. Here are my recent classes, rehearsals and travel plans.",
  btn_my: "Current Rhythm",
  btn_ustc: "USTC Timetable",
  btn_calendar: "Calendar",
  focus_title: "Current focus",
  focus_body: "I am currently attending first-year graduate coursework at the UCAS Yanqi Lake campus, with classes on Monday through Saturday mornings. On Sundays, I rehearse with the Shunhua Chinese Chamber Ensemble in the morning and the UCAS Chinese Orchestra in the afternoon.",
  base_title: "Usual base",
  base_body: "Weekdays: UCAS Yanqi Lake campus. Sundays: UCAS Zhongguancun campus. Other holidays: home near the UCAS Yuquan Road campus.",
  reach_title: "Best way to reach me",
  reach_body: "WeChat or QQ is preferred for everyday contact. For academic discussions, please use my UCAS email.",
  weekly_title: "A rough weekly rhythm",
  timeblock: "Time block",
  monfri: "Mon–Fri",
  saturday: "Saturday",
  sunday: "Sunday",
  morning: "Morning",
  afternoon: "Afternoon",
  evening: "Evening",
  monfri_morning: "Classes at Yanqi Lake: first-year graduate coursework",
  sat_morning: "Classes at Yanqi Lake: first-year graduate coursework",
  sun_morning: "Shunhua Chinese Chamber Ensemble rehearsal",
  monfri_afternoon: "Flexible",
  sat_afternoon: "Flexible",
  sun_afternoon: "UCAS Chinese Orchestra rehearsal",
  monfri_evening: "Flexible",
  sat_evening: "Flexible",
  sun_evening: "Flexible",
  notes_title: "A small local note to myself",
  notes_body: "This note is saved only in the current browser, useful for small goals or temporary reminders.",
  notes_placeholder: "Write a short reminder here...",
  notes_saved: "Saved locally",
  ustc_title: "USTC timetable placeholder",
  ustc_body: "This section is reserved for your future semester or course timetable. The structure is already separated out in JS/CSS so you can add your own class blocks later.",
  calendar_title: "Calendar placeholder",
  calendar_body: "This section is reserved for future calendar integration or manually maintained events.",
  reach_link: "Find my WeChat and QQ",
  weekly_note: "I may play badminton during free time on Sundays. Other unspecified time slots vary from week to week.",
  upcoming_title: "Coming up",
  upcoming_date: "December 6, 2026",
  upcoming_body: "Returning to USTC to take part in the NMOU USTC Student Chinese Orchestra 2026 Solo Concert.",
  archive_title: "Summer 2026 record",
  archive_note: "The rhythm and plans from that summer are retained below as a historical record.",
  archive_focus_body: "During the summer after my senior year, my main work is to turn the results of my graduation thesis and the Undergraduate Innovation and Entrepreneurship Training Program into manuscripts intended for submission, while preparing for the entrance examinations before starting at the Chinese Academy of Sciences. I will be in Shanghai on July 9 for a small closed-door sharing session with Prof. Ngô Bảo Châu and Prof. Zhiwei Yun, and in Kunming from July 17 to 19 for the Third Western Forum on Operations Research and Development, a workshop on the frontiers of operations optimization and digital-intelligent science.",
  archive_base_body: "I am mostly based in Beijing and at home. On ordinary weekdays, I usually spend the morning at the UCAS Yuquan Road campus and the afternoon at home.",
  archive_reach_body: "Email is the best choice for academic or formal communication; friends can reach me through WeChat. Sundays are usually reserved for UCAS Chinese Orchestra rehearsal.",
  archive_monfri_morning: "UCAS Yuquan Road campus: manuscript writing, algorithm notes, and exam preparation",
  archive_sat_morning: "Supplementary reading, errands, and lighter recovery-oriented tasks",
  archive_sun_morning: "Rest, tidying up, light exercise, or concert-related arrangements",
  archive_monfri_afternoon: "Working from home: manuscript revision, note organization, and submission preparation",
  archive_sat_afternoon: "Films, Chinese instrumental concerts, badminton, running and working out, or temporary arrangements",
  archive_sun_afternoon: "UCAS Chinese Orchestra rehearsal",
  archive_monfri_evening: "Films, Chinese instrumental concerts, badminton, running and working out, or a brief review of the day",
  archive_sat_evening: "Meeting friends, watching films, or relaxing",
  archive_sun_evening: "Closing the week and planning the next one",
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
      <div class="schedule-heading" data-sched-i18n="heading">Current Schedule &amp; Everyday Rhythm</div>
      <p class="page-subtitle" data-sched-i18n="subtitle">Autumn 2026: I am attending first-year graduate coursework at the UCAS Yanqi Lake campus. Here are my recent classes, rehearsals and travel plans.</p>

      <div class="schedule-switcher">
        <button class="schedule-switch-btn active" data-view="my-timetable" data-sched-i18n="btn_my">Current Rhythm</button>
        <button class="schedule-switch-btn" data-view="ustc-timetable" data-sched-i18n="btn_ustc">USTC Timetable</button>
        <button class="schedule-switch-btn" data-view="calendar" data-sched-i18n="btn_calendar">Calendar</button>
      </div>

      <div class="schedule-section active" id="my-timetable-section">
        <div class="schedule-grid">
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="focus_title">Current focus</div>
            <p data-sched-i18n="focus_body">I am currently attending first-year graduate coursework at the UCAS Yanqi Lake campus, with classes on Monday through Saturday mornings. On Sundays, I rehearse with the Shunhua Chinese Chamber Ensemble in the morning and the UCAS Chinese Orchestra in the afternoon.</p>
          </div>
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="base_title">Usual base</div>
            <p data-sched-i18n="base_body">Weekdays: UCAS Yanqi Lake campus. Sundays: UCAS Zhongguancun campus. Other holidays: home near the UCAS Yuquan Road campus.</p>
          </div>
          <div class="schedule-card">
            <div class="schedule-title" data-sched-i18n="reach_title">Best way to reach me</div>
            <p data-sched-i18n="reach_body">WeChat or QQ is preferred for everyday contact. For academic discussions, please use my UCAS email.</p>
            <p><a href="mailto:yangshutai26@mails.ucas.ac.cn">yangshutai26@mails.ucas.ac.cn</a></p>
            <a href="#resume" data-sched-i18n="reach_link">Find my WeChat and QQ</a>
          </div>
        </div>

        <div class="section schedule-upcoming">
          <h2 data-sched-i18n="upcoming_title">Coming up</h2>
          <p><strong><time datetime="2026-12-06" data-sched-i18n="upcoming_date">December 6, 2026</time></strong></p>
          <p data-sched-i18n="upcoming_body">Returning to USTC to take part in the NMOU USTC Student Chinese Orchestra 2026 Solo Concert.</p>
        </div>

        <div class="section">
          <h2 data-sched-i18n="weekly_title">A rough weekly rhythm</h2>
          <div class="routine-table-wrap">
            <table class="routine-table">
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
                  <td data-sched-i18n="monfri_morning">Classes at Yanqi Lake: first-year graduate coursework</td>
                  <td data-sched-i18n="sat_morning">Classes at Yanqi Lake: first-year graduate coursework</td>
                  <td data-sched-i18n="sun_morning">Shunhua Chinese Chamber Ensemble rehearsal</td>
                </tr>
                <tr>
                  <td data-sched-i18n="afternoon">Afternoon</td>
                  <td data-sched-i18n="monfri_afternoon">Flexible</td>
                  <td data-sched-i18n="sat_afternoon">Flexible</td>
                  <td data-sched-i18n="sun_afternoon">UCAS Chinese Orchestra rehearsal</td>
                </tr>
                <tr>
                  <td data-sched-i18n="evening">Evening</td>
                  <td data-sched-i18n="monfri_evening">Flexible</td>
                  <td data-sched-i18n="sat_evening">Flexible</td>
                  <td data-sched-i18n="sun_evening">Flexible</td>
                </tr>
              </tbody>
            </table>
          </div>
          <p class="small" data-sched-i18n="weekly_note">I may play badminton during free time on Sundays. Other unspecified time slots vary from week to week.</p>
        </div>

        <details class="section schedule-archive">
          <summary data-sched-i18n="archive_title">Summer 2026 record</summary>
          <p class="small" data-sched-i18n="archive_note">The rhythm and plans from that summer are retained below as a historical record.</p>
          <h3 data-sched-i18n="focus_title">Current focus</h3>
          <p data-sched-i18n="archive_focus_body">During the summer after my senior year, my main work is to turn the results of my graduation thesis and the Undergraduate Innovation and Entrepreneurship Training Program into manuscripts intended for submission, while preparing for the entrance examinations before starting at the Chinese Academy of Sciences. I will be in Shanghai on July 9 for a small closed-door sharing session with Prof. Ngô Bảo Châu and Prof. Zhiwei Yun, and in Kunming from July 17 to 19 for the Third Western Forum on Operations Research and Development, a workshop on the frontiers of operations optimization and digital-intelligent science.</p>
          <h3 data-sched-i18n="base_title">Usual base</h3>
          <p data-sched-i18n="archive_base_body">I am mostly based in Beijing and at home. On ordinary weekdays, I usually spend the morning at the UCAS Yuquan Road campus and the afternoon at home.</p>
          <h3 data-sched-i18n="reach_title">Best way to reach me</h3>
          <p data-sched-i18n="archive_reach_body">Email is the best choice for academic or formal communication; friends can reach me through WeChat. Sundays are usually reserved for UCAS Chinese Orchestra rehearsal.</p>
        <div class="section">
          <h2 data-sched-i18n="weekly_title">A rough weekly rhythm</h2>
          <div class="routine-table-wrap">
            <table class="routine-table">
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
                  <td data-sched-i18n="archive_monfri_morning">UCAS Yuquan Road campus: manuscript writing, algorithm notes, and exam preparation</td>
                  <td data-sched-i18n="archive_sat_morning">Supplementary reading, errands, and lighter recovery-oriented tasks</td>
                  <td data-sched-i18n="archive_sun_morning">Rest, tidying up, light exercise, or concert-related arrangements</td>
                </tr>
                <tr>
                  <td data-sched-i18n="afternoon">Afternoon</td>
                  <td data-sched-i18n="archive_monfri_afternoon">Working from home: manuscript revision, note organization, and submission preparation</td>
                  <td data-sched-i18n="archive_sat_afternoon">Films, Chinese instrumental concerts, badminton, running and working out, or temporary arrangements</td>
                  <td data-sched-i18n="archive_sun_afternoon">UCAS Chinese Orchestra rehearsal</td>
                </tr>
                <tr>
                  <td data-sched-i18n="evening">Evening</td>
                  <td data-sched-i18n="archive_monfri_evening">Films, Chinese instrumental concerts, badminton, running and working out, or a brief review of the day</td>
                  <td data-sched-i18n="archive_sat_evening">Meeting friends, watching films, or relaxing</td>
                  <td data-sched-i18n="archive_sun_evening">Closing the week and planning the next one</td>
                </tr>
              </tbody>
            </table>
          </div>
        </div>

        </details>

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
