'use strict';

const contextParams = new URLSearchParams(location.search);
const contextWork = (contextParams.get('work') || '').slice(0, 80);
const contextVersion = (contextParams.get('version') || '').slice(0, 100);
const scoreField = document.querySelector('[data-draft="校谱反馈"] [name="谱件版本"]');
if (scoreField && !scoreField.value && contextWork) {
  scoreField.value = [contextWork, contextVersion].filter(Boolean).join(' · ').slice(0, scoreField.maxLength);
}
for (const form of document.querySelectorAll('[data-draft]')) {
  const contact = form.dataset.recipient;
  if (!contact || !/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(contact)) continue;
  const preview = form.querySelector('.generated-draft');
  const status = form.querySelector('output');
  const actions = form.querySelector('[data-ready]');
  const letter = form.querySelector('[data-mail]');
  const save = form.querySelector('[data-save]');
  const fields = form.querySelector('fieldset');
  const submit = form.querySelector('button[type="submit"]');
  const title = form.dataset.draft;
  let body = '';
  function draftParts(data) {
    return [...data].filter(([,value]) => String(value).trim()).map(([key,value]) => [key,String(value).trim()]);
  }
  function draftBody(entries) {
    return [`国乐谱汇 · ${title}`,...entries.map(([key,value]) => `${key}\n${value}`)].join('\n\n');
  }
  form.addEventListener('submit',event => {
    event.preventDefault();
    for (const field of form.querySelectorAll('input[required],textarea[required],select[required]')) {
      field.setCustomValidity(field.value.trim() ? '' : '请填写此项，不能只输入空格。');
    }
    if (!form.reportValidity()) {
      status.textContent='请补全必填内容，再生成草稿。';
      return;
    }
    body = draftBody(draftParts(new FormData(form)));
    preview.textContent = body;
    preview.hidden = false;
    actions.hidden = false;
    const url = `mailto:${contact}?subject=${encodeURIComponent('国乐谱汇 · ' + title)}&body=${encodeURIComponent(body)}`;
    if (url.length < 1850) {
      letter.href=url;
      letter.hidden=false;
      status.textContent='草稿已生成，尚未发送。可以下载，也可在自己的邮件应用中核对后发送。';
    } else {
      letter.href=`mailto:${contact}?subject=${encodeURIComponent('国乐谱汇 · ' + title)}`;
      letter.hidden=false;
      status.textContent='草稿已生成，尚未发送。内容较长，邮件链接只带入收件人和主题；请复制下方全文，或下载 TXT 后粘贴到邮件中。';
    }
  });
  function invalidate(event) {
    if (typeof event.target.setCustomValidity === 'function') event.target.setCustomValidity('');
    if (!body) return;
    body='';
    preview.textContent='';
    preview.hidden=true;
    actions.hidden=true;
    letter.removeAttribute('href');
    status.textContent='内容已修改。请重新生成草稿。';
  }
  form.addEventListener('input', invalidate);
  form.addEventListener('change', invalidate);
  save.addEventListener('click', () => {
    if (!body) return;
    const url = URL.createObjectURL(new Blob([body+'\n'], {type:'text/plain;charset=utf-8'}));
    const link=document.createElement('a');
    link.href=url;
    link.download=`国乐谱汇_${title}.txt`;
    link.click();
    window.setTimeout(() => URL.revokeObjectURL(url),1000);
  });
  if (fields) fields.disabled=false;
  if (submit) submit.hidden=false;
}
