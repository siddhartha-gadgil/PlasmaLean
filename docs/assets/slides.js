(() => {
  const slides = [...document.querySelectorAll('[data-slide]')];
  if (!slides.length) return;
  const controls = document.getElementById('slide-controls');
  const previous = document.getElementById('slide-prev');
  const next = document.getElementById('slide-next');
  const counter = document.getElementById('slide-counter');
  const select = document.getElementById('slide-select');
  const view = document.getElementById('slide-view');
  let index = 0;
  let readAll = false;

  function hashIndex() {
    let id;
    try { id = decodeURIComponent(window.location.hash.slice(1)); }
    catch { return -1; }
    return slides.findIndex(slide => slide.id === id || slide.contains(document.getElementById(id)));
  }

  function show(target, { updateHistory = true, focus = false } = {}) {
    index = Math.max(0, Math.min(slides.length - 1, target));
    slides.forEach((slide, i) => { slide.hidden = !readAll && i !== index; });
    document.body.classList.toggle('presenting', !readAll);
    previous.disabled = index === 0;
    next.disabled = index === slides.length - 1;
    counter.textContent = `${index + 1} / ${slides.length}`;
    select.value = String(index);
    view.setAttribute('aria-pressed', String(readAll));
    view.textContent = readAll ? 'Present slides' : 'Read all';
    if (updateHistory && window.location.hash !== `#${slides[index].id}`) {
      window.history.pushState(null, '', `#${slides[index].id}`);
    }
    if (focus) {
      slides[index].focus({ preventScroll: true });
      slides[index].scrollIntoView({ block: 'start', behavior: 'instant' });
    }
  }

  previous.addEventListener('click', () => show(index - 1, { focus: true }));
  next.addEventListener('click', () => show(index + 1, { focus: true }));
  select.addEventListener('change', () => show(Number(select.value), { focus: true }));
  view.addEventListener('click', () => {
    readAll = !readAll;
    show(index, { updateHistory: false });
    slides[index].scrollIntoView({ block: 'start', behavior: 'instant' });
  });
  document.getElementById('slide-print').addEventListener('click', () => window.print());
  document.addEventListener('keydown', event => {
    if (readAll || event.altKey || event.ctrlKey || event.metaKey || event.defaultPrevented ||
        event.target.closest('a, button, input, select, textarea, [contenteditable], [role="textbox"]')) return;
    let target;
    if (event.key === 'ArrowRight' || event.key === 'PageDown' || (event.key === ' ' && !event.shiftKey)) target = index + 1;
    if (event.key === 'ArrowLeft' || event.key === 'PageUp' || (event.key === ' ' && event.shiftKey)) target = index - 1;
    if (event.key === 'Home') target = 0;
    if (event.key === 'End') target = slides.length - 1;
    if (target === undefined) return;
    event.preventDefault();
    show(target, { focus: true });
  });
  const restoreHash = () => show(Math.max(0, hashIndex()), { updateHistory: false });
  window.addEventListener('hashchange', restoreHash);
  window.addEventListener('popstate', restoreHash);
  // Without JavaScript all slides remain visible. No timers or external assets.
  controls.hidden = false;
  restoreHash();
})();
