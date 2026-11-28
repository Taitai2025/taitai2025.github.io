/* Explicit, local-only draft preparation. Nothing is sent in the background. */
(() => {
  'use strict';
  const globalStatus = document.querySelector('[data-community-status]');
  async function copyText(text, status, label) {
    try {
      if (!navigator.clipboard?.writeText) throw new Error('Clipboard unavailable');
      await navigator.clipboard.writeText(text);
      status.textContent = `${label}已复制，可粘贴到邮件或聊天中。`;
    } catch {
      status.textContent = `浏览器暂时无法复制，请选中${label}文字手动复制。`;
    }
  }
  for (const button of document.querySelectorAll('[data-copy]')) {
    button.hidden = false;
    button.addEventListener('click', () => copyText(button.dataset.copy, globalStatus, button.dataset.copyLabel || '内容'));
  }
  for (const form of document.querySelectorAll('[data-community-draft]')) {
    const submit = form.querySelector('[data-draft-submit]');
    const result = form.querySelector('[data-draft-result]');
    const preview = form.querySelector('[data-draft-text]');
    const status = form.querySelector('[data-draft-status]');
    const letter = form.querySelector('[data-draft-mail]');
    const mailNote = form.querySelector('[data-draft-mail-note]');
    let draft = '';
    const title = form.dataset.communityDraft;
    const recipient = form.dataset.recipient;
    if (!/^[\w.+-]+@[\w.-]+\.[a-z]{2,}$/i.test(recipient)) continue;
    form.querySelector('fieldset').disabled = false;
    submit.hidden = false;
    // The query carries only public catalogue metadata, never a password.
    if (title === '谱件查阅与交流') {
      const params = new URLSearchParams(location.search);
      for (const [param, field] of [['work', '作品名称'], ['version', '谱件版本']]) {
        const input = form.elements.namedItem(field);
        if (input && !input.value) input.value = (params.get(param) || '').replace(/[\u0000-\u001f]/g, ' ').slice(0, input.maxLength);
      }
    }
    function clearDraft() {
      if (!draft) return;
      draft = '';
      preview.value = '';
      result.hidden = true;
      letter.removeAttribute('href');
      status.textContent = '内容已修改，请重新整理草稿后发送。';
    }
    form.addEventListener('input', event => {
      if (event.target.setCustomValidity) event.target.setCustomValidity('');
      if (!result.contains(event.target)) clearDraft();
    });
    form.addEventListener('change', event => { if (!result.contains(event.target)) clearDraft(); });
    form.addEventListener('submit', event => {
      event.preventDefault();
      for (const field of form.querySelectorAll('[required]')) {
        if (field.type === 'checkbox') continue;
        field.setCustomValidity(field.value.trim() ? '' : '请填写实际内容，不能仅输入空格。');
      }
      if (!form.reportValidity()) return;
      const entries = [...new FormData(form)].map(([name, value]) => [name, String(value).trim()]).filter(([, value]) => value);
      draft = [`国乐谱汇 · ${title}`, ...entries.map(([name, value]) => `${name}：\n${value}`), '图片与其他附件请在邮件或聊天中手动添加。'].join('\n\n');
      preview.value = draft;
      result.hidden = false;
      const subject = `国乐谱汇 · ${title} · ${form.elements.namedItem('乐团名称')?.value || form.elements.namedItem('作品名称')?.value || ''}`.slice(0, 180);
      const full = `mailto:${recipient}?subject=${encodeURIComponent(subject)}&body=${encodeURIComponent(draft)}`;
      if (full.length <= 1800) {
        letter.href = full;
        mailNote.textContent = '邮件应用会带入这份草稿。请检查收件人、正文与附件，再由你发送。';
      } else {
        letter.href = `mailto:${recipient}?subject=${encodeURIComponent(subject)}`;
        mailNote.textContent = '草稿较长，邮件链接只预填收件人与主题。请先复制草稿，粘贴到邮件正文；也可以把下载的 TXT 作为附件发送。';
      }
      status.textContent = '草稿已整理，尚未发送。请核对后选择邮件、微信或 QQ 发送。';
    });
    form.querySelector('[data-copy-draft]').addEventListener('click', () => { if (draft) copyText(draft, status, '草稿'); });
    form.querySelector('[data-download-draft]').addEventListener('click', () => {
      if (!draft) return;
      const url = URL.createObjectURL(new Blob(['\ufeff' + draft + '\n'], {type: 'text/plain;charset=utf-8'}));
      const a = document.createElement('a');
      a.href = url;
      a.download = `国乐谱汇_${title}.txt`;
      a.click();
      setTimeout(() => URL.revokeObjectURL(url), 1000);
      status.textContent = '草稿下载已准备；请在邮件或聊天中自行添加并发送。';
    });
  }
})();
