import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import { renderSlideshow } from './render_slideshow.mjs';

// Dependency-free contract/controller tests; not browser layout or accessibility QA.
const root = path.resolve(import.meta.dirname, '..');
const read = file => fs.readFileSync(path.join(root, file), 'utf8');
const deck = JSON.parse(read('progress/slideshow.json'));
const progress = JSON.parse(read('progress/status.json'));
const html = read('docs/slides.html');
const script = read('docs/assets/slides.js');
assert.equal(html, renderSlideshow(deck, progress), 'Generated slideshow is stale');
assert.equal([...html.matchAll(/data-slide>/g)].length, deck.slides.length);
assert.equal([...html.matchAll(/<h3>Progress so far<\/h3>/g)].length, deck.slides.length);
assert.equal([...html.matchAll(/class="slide-evidence"/g)].length, deck.slides.length);
assert.ok(!/<section[^>]+\bhidden\b/.test(html), 'Slides must be readable without JavaScript');
assert.ok(!/\b(?:src|href)="https?:/.test(html), 'The slideshow must not need external assets');
assert.match(read('docs/assets/slides.css'), /\.slide\[hidden\][^{]*\{[^}]*display:\s*block !important/, 'Printing must reveal all slides');
assert.throws(() => renderSlideshow({ ...deck, updated: '1900-01-01' }, progress), /Refresh slideshow.updated/);
assert.throws(() => renderSlideshow({ ...deck, report: 'old.md' }, progress), /Refresh slideshow.report/);
assert.throws(() => renderSlideshow({ ...deck, slides: [deck.slides[0], deck.slides[0]] }, progress), /Duplicate slide/);
const missingEvidence = structuredClone(deck);
missingEvidence.slides[0].evidence = [];
assert.throws(() => renderSlideshow(missingEvidence, progress), /needs evidence/);
const unsafeLink = structuredClone(deck);
unsafeLink.slides[0].evidence[0].href = 'javascript:alert(1)';
assert.throws(() => renderSlideshow(unsafeLink, progress), /local evidence/);
const escaped = structuredClone(deck);
escaped.slides[0].title = '<script>test & "quotes"</script>';
assert.ok(renderSlideshow(escaped, progress).includes('&lt;script&gt;test &amp; &quot;quotes&quot;&lt;/script&gt;'));

function mount(hash = '') {
  const elements = new Map();
  let focused = null;
  let prints = 0;
  class Element {
    constructor(id) { this.id = id; this.hidden = false; this.disabled = false; this.events = {}; this.attributes = {}; }
    addEventListener(type, callback) { (this.events[type] ||= []).push(callback); }
    dispatch(type, event = {}) { if (type !== 'click' || !this.disabled) for (const callback of this.events[type] || []) callback(event); }
    setAttribute(name, value) { this.attributes[name] = value; }
    contains(element) { return element === this || element?.parent === this; }
    focus() { focused = this.id; }
    scrollIntoView() {}
    closest() { return null; }
  }
  for (const match of html.matchAll(/\bid="([^"]+)"/g)) elements.set(match[1], new Element(match[1]));
  const slides = deck.slides.map(slide => elements.get(slide.id));
  for (const slide of slides) elements.get(`${slide.id}-title`).parent = slide;
  const body = new Element('body');
  const classes = new Set();
  body.classList = { toggle(name, on) { if (on) classes.add(name); else classes.delete(name); } };
  const document = new Element('document');
  Object.assign(document, { body, querySelectorAll: () => slides, getElementById: id => elements.get(id) || null });
  const window = new Element('window');
  const history = [];
  Object.assign(window, {
    location: { hash },
    history: { pushState(state, title, fragment) { history.push(fragment); window.location.hash = fragment; } },
    print() { prints++; }
  });
  vm.runInNewContext(script, { document, window }, { filename: 'slides.js' });
  return {
    slides, elements, window, history, classes,
    focused: () => focused,
    prints: () => prints,
    visible: () => slides.filter(slide => !slide.hidden).map(slide => slide.id),
    click: id => elements.get(id).dispatch('click'),
    key(key, options = {}) {
      const event = { key, target: body, prevented: false, preventDefault() { this.prevented = true; }, ...options };
      document.dispatch('keydown', event);
      return event.prevented;
    }
  };
}

const ids = deck.slides.map(slide => slide.id);
const app = mount();
assert.deepEqual(app.visible(), [ids[0]]);
assert.equal(app.elements.get('slide-controls').hidden, false);
assert.equal(app.elements.get('slide-prev').disabled, true);
assert.equal(app.elements.get('slide-counter').textContent, `1 / ${ids.length}`);
assert.equal(app.history.length, 0, 'Loading must not add a history entry');
app.click('slide-next');
assert.deepEqual(app.visible(), [ids[1]]);
assert.equal(app.focused(), ids[1]);
assert.equal(app.window.location.hash, `#${ids[1]}`);
assert.equal(app.key('ArrowRight'), true);
assert.deepEqual(app.visible(), [ids[2]]);
app.key('ArrowLeft');
app.key(' ', { shiftKey: true });
assert.deepEqual(app.visible(), [ids[0]]);
app.key('PageDown');
app.key('PageUp');
assert.deepEqual(app.visible(), [ids[0]]);
app.key(' ');
assert.deepEqual(app.visible(), [ids[1]]);
app.key('End');
assert.deepEqual(app.visible(), [ids.at(-1)]);
assert.equal(app.elements.get('slide-next').disabled, true);
const historySize = app.history.length;
app.key('ArrowRight');
assert.equal(app.history.length, historySize, 'Do not wrap or duplicate boundary history');
app.key('Home');
assert.deepEqual(app.visible(), [ids[0]]);
assert.equal(app.key('ArrowRight', { ctrlKey: true }), false);
assert.equal(app.key('ArrowRight', { metaKey: true }), false);
assert.equal(app.key('ArrowRight', { altKey: true }), false);
assert.equal(app.key('ArrowRight', { defaultPrevented: true }), false);
assert.equal(app.key('ArrowRight', { target: { closest: () => ({}) } }), false, 'Leave form, button, link and editable key handling alone');
assert.equal(app.key('Escape'), false);
assert.deepEqual(app.visible(), [ids[0]]);
app.elements.get('slide-select').value = '4';
app.elements.get('slide-select').dispatch('change');
assert.deepEqual(app.visible(), [ids[4]]);
app.click('slide-prev');
assert.deepEqual(app.visible(), [ids[3]]);
app.click('slide-view');
assert.deepEqual(app.visible(), ids);
assert.equal(app.classes.has('presenting'), false);
assert.equal(app.elements.get('slide-view').attributes['aria-pressed'], 'true');
assert.equal(app.key(' '), false, 'Read-all mode must preserve normal scrolling');
app.click('slide-view');
assert.deepEqual(app.visible(), [ids[3]]);
app.click('slide-print');
assert.equal(app.prints(), 1);
app.window.location.hash = `#${ids[1]}`;
app.window.dispatch('popstate');
assert.deepEqual(app.visible(), [ids[1]]);
app.window.location.hash = `#${ids[2]}`;
app.window.dispatch('hashchange');
assert.deepEqual(app.visible(), [ids[2]]);
assert.deepEqual(mount(`#${ids[5]}`).visible(), [ids[5]], 'Direct slide bookmarks must work');
assert.deepEqual(mount(`#${ids[5]}-title`).visible(), [ids[5]], 'Heading anchors must reveal their slide');
assert.deepEqual(mount('#missing-slide').visible(), [ids[0]]);
assert.deepEqual(mount('#%E0%A4%A').visible(), [ids[0]], 'Malformed fragments must not break controls');
console.log(`Slideshow checks passed: ${ids.length} slides, evidence/data contracts, safe rendering, navigation, keyboard, history, read-all and print hook.`);
