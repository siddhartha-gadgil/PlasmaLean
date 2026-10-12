import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import vm from 'node:vm';
import { execFileSync } from 'node:child_process';

// Read-only structural regression checks. These do not claim browser/visual QA.
const root = path.resolve(import.meta.dirname, '..');
const docs = path.join(root, 'docs');
const files = fs.readdirSync(docs).filter(file => file.endsWith('.html'));
const contents = new Map(files.map(file => [file, fs.readFileSync(path.join(docs, file), 'utf8')]));
const ids = new Map();
let checkedLinks = 0;
let checkedScripts = 0;
for (const [file, html] of contents) {
  const markup = html.replace(/<script\b[^>]*>[\s\S]*?<\/script>/gi, '');
  const pageIds = [...markup.matchAll(/\bid=["']([^"']+)["']/g)].map(match => match[1]);
  assert.equal(new Set(pageIds).size, pageIds.length, `Duplicate IDs in ${file}`);
  ids.set(file, new Set(pageIds));
  for (const match of html.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/gi)) {
    if (/\bsrc=|\btype=["']application\//i.test(match[1]) || !match[2].trim()) continue;
    new vm.Script(match[2], { filename: file });
    checkedScripts++;
  }
}
function checkLink(from, raw) {
  const href = raw.replaceAll('&amp;', '&');
  if (!href || href === '#' || /^(?:[a-z]+:|\/\/)/i.test(href)) return;
  const url = new URL(href, `https://local.invalid/${from}`);
  const file = decodeURIComponent(url.pathname.slice(1));
  assert.ok(!file.includes('..'), `Escaping local link: ${from} → ${href}`);
  assert.ok(fs.existsSync(path.join(docs, file)), `Missing local target: ${from} → ${href}`);
  if (url.hash && ids.has(file)) {
    const fragment = decodeURIComponent(url.hash.slice(1));
    const tabRoute = file === 'index.html' && ids.get(file).has(`sec-${fragment}`) && ids.get(file).has(`tab-${fragment}`);
    assert.ok(ids.get(file).has(fragment) || tabRoute, `Missing fragment: ${from} → ${href}`);
  }
  checkedLinks++;
}
for (const [file, html] of contents) {
  const markup = html.replace(/<script\b[^>]*>[\s\S]*?<\/script>/gi, '');
  for (const match of markup.matchAll(/\b(?:href|src)=["']([^"']+)["']/g)) checkLink(file, match[1]);
}
const search = JSON.parse(fs.readFileSync(path.join(docs, 'assets/search-index.json'), 'utf8'));
for (const entry of search) checkLink('index.html', entry.url);
const statuses = JSON.parse(fs.readFileSync(path.join(root, 'progress/status.json'), 'utf8'));
for (const [key, status] of Object.entries(statuses.tasks)) {
  const colon = key.indexOf(':');
  const page = key.slice(0, colon);
  const id = key.slice(colon + 1);
  assert.ok(search.some(entry => entry.url === `${page}.html` && entry.title.startsWith(`${id} · `) && entry.section.includes(status)), `Unrendered progress: ${key}`);
}
const taskEntries = search.filter(entry => / · (?:Planning only|Partially implemented|Lean verified)/.test(entry.section));
// 107 original entries plus five explicit vacuum-demonstrator work packages.
assert.equal(taskEntries.length, 112, 'Tracked tasks have changed; audit coverage before updating this fixture');
const landing = contents.get('index.html');
const template = fs.readFileSync(path.join(root, 'scripts/templates/overview.html'), 'utf8');
const canvasIds = html => [...html.matchAll(/<canvas\b[^>]*\bid="([^"]+)"/g)].map(match => match[1]);
assert.deepEqual(canvasIds(landing), canvasIds(template), 'Original graphics must be retained');
assert.ok(canvasIds(landing).length >= 5, 'Landing page graphics are missing');
for (const tab of ['background', 'vision', 'kernel', 'sanity', 'theory', 'references', 'agent', 'realization']) {
  assert.ok(ids.get('index.html').has(`sec-${tab}`) && ids.get('index.html').has(`tab-${tab}`), `Original tab is missing: ${tab}`);
}
assert.ok(landing.includes('href="progress.html"'), 'Progress must be reachable from the original landing page');
assert.ok(landing.match(/<nav class="handbook-bar"[^>]*>[\s\S]*?href="slides.html"[\s\S]*?<\/nav>/), 'Slideshow must be directly reachable from the landing navigation');
const slideshow = JSON.parse(fs.readFileSync(path.join(root, 'progress/slideshow.json'), 'utf8'));
assert.ok(search.some(entry => entry.url === 'slides.html'), 'Slideshow must be searchable');
for (const slide of slideshow.slides) {
  assert.ok(search.some(entry => entry.url === `slides.html#${slide.id}`), `Unsearchable slide: ${slide.id}`);
}
assert.ok(landing.includes('href="vacuum-demonstrator.html"'), 'Device basis must be reachable from the original landing page');
assert.ok(contents.get('vacuum-demonstrator.html').includes('97/250'), 'Tube clearance certificate is missing');
assert.ok(contents.get('vacuum-demonstrator.html').includes('not seconds'), 'Field-line parameter must not be labelled as particle time');
assert.ok(!landing.includes('Only plans have been made and no Lean code'), 'Landing status is obsolete');
assert.ok(contents.get('progress.html').includes('998/45'), 'Exact thermal margin is missing');
assert.ok(contents.get('overview.html').includes("location.search + location.hash"), 'Legacy overview bookmarks must survive');
execFileSync(process.execPath, ['scripts/generate_handbook.mjs', '--check'], { cwd: root, stdio: 'inherit' });
execFileSync(process.execPath, ['scripts/check_slideshow.mjs'], { cwd: root, stdio: 'inherit' });
console.log(`Site checks passed: ${files.length} pages, ${checkedLinks} local links/search targets, ${checkedScripts} inline scripts, ${taskEntries.length} task entries, original graphics preserved.`);
