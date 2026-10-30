import fs from 'node:fs';
import path from 'node:path';
import { renderSlideshow } from './render_slideshow.mjs';

const root = path.resolve(import.meta.dirname, '..');
const docsDir = path.join(root, 'docs');
const checkOnly = process.argv.includes('--check');
function writeOutput(file, content) {
  if (checkOnly) {
    if (!fs.existsSync(file) || fs.readFileSync(file, 'utf8') !== content) {
      throw new Error(`Generated file is stale: ${path.relative(root, file)}`);
    }
  } else {
    fs.writeFileSync(file, content);
  }
}
const pages = [
  { source: 'notes/domain-libraries.md', slug: 'domain-library', short: 'Library method', group: 'Foundation', summary: 'How PlasmaLean separates domain assumptions, sanity checks, and verified theory.' },
  { source: 'notes/formalization/00-model-contracts.md', slug: 'model-contracts', short: 'Model contracts', group: 'Foundation', summary: 'What a design proof can claim, how contracts compose, and where assumptions live.' },
  { source: 'notes/formalization/01-geometry-and-fields.md', slug: 'geometry-and-fields', short: 'Geometry & fields', group: 'Physics', summary: 'Pressure surfaces, flux coordinates, field-line dynamics, quasisymmetry, and near-axis theory.' },
  { source: 'notes/formalization/02-plasma-models-and-equilibrium.md', slug: 'plasma-models-and-equilibrium', short: 'Models & equilibrium', group: 'Physics', summary: 'Ideal MHD, static and weak equilibria, boundary conditions, and model reductions.' },
  { source: 'notes/formalization/03-mhd-stability.md', slug: 'mhd-stability', short: 'MHD stability', group: 'Physics', summary: 'Energy principles, continuum operators, neutral modes, and honest stability certificates.' },
  { source: 'notes/formalization/04-particles-and-transport.md', slug: 'particles-and-transport', short: 'Particles & transport', group: 'Physics', summary: 'Full and reduced orbits, confinement horizons, kinetic transport, and reactor profiles.' },
  { source: 'notes/formalization/05-verified-numerics.md', slug: 'verified-numerics', short: 'Verified numerics', group: 'Verification', summary: 'Exact inputs, continuous bounds, equilibrium validation, and certificate identity.' },
  { source: 'notes/formalization/06-coils-and-design.md', slug: 'coils-and-design', short: 'Coils & design', group: 'Design', summary: 'Biot–Savart fields, inverse coil design, manufacturing geometry, and robust workflows.' },
  { source: 'notes/design/vacuum-demonstrator.md', slug: 'vacuum-demonstrator', short: 'Vacuum demonstrator', group: 'Design', summary: 'Checked tolerance-aware calibration fixture, the CNT reference direction, and the remaining boundary to a practical stellarator.' },
  { source: 'notes/formalization/07-materials-and-engineering.md', slug: 'materials-and-engineering', short: 'Materials & engineering', group: 'Design', summary: 'Heat, stress, magnets, quench, neutronics, lifetime, power, and maintenance.' },
  { source: 'notes/formalization/08-roadmap.md', slug: 'roadmap', short: 'Roadmap', group: 'Program', summary: 'Evidence gates, the first coding sequence, research questions, and progress records.' },
  { source: 'notes/implementation-plan.md', slug: 'implementation-plan', short: 'Implementation plan', group: 'Program', summary: 'Cyclic plan: theory tracks, certificate techniques, and a ladder of successively realistic models for confinement and burn temperature.' },
  { source: 'notes/formalization/09-literature.md', slug: 'literature', short: 'Literature', group: 'Program', summary: 'Primary sources, extraction discipline, software roles, and theorem reading order.' }
];

const aliases = new Map(pages.map(page => [path.basename(page.source), `${page.slug}.html`]));
const pageBySlug = new Map(pages.map(page => [page.slug, page]));
const progressText = 'Planning only — no Lean code written';
const progress = JSON.parse(fs.readFileSync(path.join(root, 'progress/status.json'), 'utf8'));
const slideshow = JSON.parse(fs.readFileSync(path.join(root, 'progress/slideshow.json'), 'utf8'));
const usedProgressKeys = new Set();
function taskProgress(page, id) {
  const key = `${page.slug}:${id}`;
  usedProgressKeys.add(key);
  return progress.tasks[key] || progressText;
}
const overviewSections = [
  ['background', 'Stellarator concepts', ['geometry-and-fields', 'particles-and-transport']],
  ['vision', 'Vision & architecture', ['domain-library', 'model-contracts']],
  ['kernel', 'The kernel', ['plasma-models-and-equilibrium']],
  ['sanity', 'Boundary & sanity checks', []],
  ['theory', 'Theory engine & graphics', ['mhd-stability', 'verified-numerics']],
  ['references', 'Literature overview', ['literature']],
  ['agent', 'AI discovery blueprint', ['roadmap', 'implementation-plan']],
  ['realization', 'Illustrative design studio', ['coils-and-design', 'vacuum-demonstrator', 'materials-and-engineering']]
];

function escapeHtml(value) {
  return value.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;').replaceAll('"', '&quot;');
}

function slugify(value) {
  return value.toLowerCase().replace(/[^a-z0-9\s-]/g, '').trim().replace(/\s+/g, '-').replace(/-+/g, '-');
}

function rewriteHref(href) {
  const [file, hash = ''] = href.split('#');
  const target = aliases.get(path.basename(file));
  return target ? `${target}${hash ? `#${hash}` : ''}` : href;
}

function inline(value) {
  const codes = [];
  let text = value.replace(/`([^`]+)`/g, (_, code) => `@@CODE${codes.push(`<code>${escapeHtml(code)}</code>`) - 1}@@`);
  text = escapeHtml(text);
  text = text.replace(/\[([^\]]+)\]\(([^)]+)\)/g, (_, label, href) => `<a href="${escapeHtml(rewriteHref(href))}">${label}</a>`);
  text = text.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>');
  text = text.replace(/(?<!\*)\*([^*]+)\*(?!\*)/g, '<em>$1</em>');
  text = text.replace(/@@CODE(\d+)@@/g, (_, index) => codes[Number(index)]);
  return text;
}

function splitTableRow(line) {
  return line.trim().replace(/^\|/, '').replace(/\|$/, '').split('|').map(cell => cell.trim());
}

function isDivider(line) {
  return /^\s*\|?\s*:?-{3,}/.test(line) && line.includes('|');
}

function renderMarkdown(markdown, page) {
  const lines = markdown.split(/\r?\n/);
  const headings = [];
  const tasks = [];
  let html = '';
  let paragraph = [];
  let listType = null;
  let i = 0;

  const flushParagraph = () => {
    if (paragraph.length) html += `<p>${inline(paragraph.join(' '))}</p>\n`;
    paragraph = [];
  };
  const closeList = () => {
    if (listType) html += `</${listType}>\n`;
    listType = null;
  };
  const uniqueSlug = title => {
    const base = slugify(title) || 'section';
    let candidate = base;
    let n = 2;
    while (headings.some(heading => heading.id === candidate)) candidate = `${base}-${n++}`;
    return candidate;
  };

  while (i < lines.length) {
    const line = lines[i];
    if (line.startsWith('```')) {
      flushParagraph(); closeList();
      const language = line.slice(3).trim();
      const body = [];
      i++;
      while (i < lines.length && !lines[i].startsWith('```')) body.push(lines[i++]);
      html += `<pre${language ? ` data-language="${escapeHtml(language)}"` : ''}><code>${escapeHtml(body.join('\n'))}</code></pre>\n`;
      i++; continue;
    }
    if (line.trim() === '$$') {
      flushParagraph(); closeList();
      const body = [];
      i++;
      while (i < lines.length && lines[i].trim() !== '$$') body.push(lines[i++]);
      html += `<div class="math-block">$$${escapeHtml(body.join('\n'))}$$</div>\n`;
      i++; continue;
    }
    const heading = line.match(/^(#{1,4})\s+(.+)$/);
    if (heading) {
      flushParagraph(); closeList();
      const level = heading[1].length;
      const title = heading[2].replace(/\[([^\]]+)\]\([^)]+\)/g, '$1');
      if (level === 1) { i++; continue; }
      const id = uniqueSlug(title);
      headings.push({ level, title, id });
      html += `<h${level} id="${id}">${inline(heading[2])}</h${level}>\n`;
      if (level === 3 && /^R\d+\./.test(title)) {
        const id = title.split('.')[0];
        const status = taskProgress(page, id);
        tasks.push({ id, title, section: title, status });
        html += `<div class="task-progress"><strong>Progress so far:</strong> ${inline(status)}</div>\n`;
      }
      i++; continue;
    }
    if (line.includes('|') && i + 1 < lines.length && isDivider(lines[i + 1])) {
      flushParagraph(); closeList();
      const headers = splitTableRow(line);
      i += 2;
      const rows = [];
      while (i < lines.length && lines[i].includes('|') && lines[i].trim()) rows.push(splitTableRow(lines[i++]));
      const taskTable = headers.some(header => /^(ID|Order|Gate|First target)$/i.test(header));
      if (taskTable) headers.push('Progress so far');
      html += '<div class="table-wrap"><table><thead><tr>' + headers.map(header => `<th>${inline(header)}</th>`).join('') + '</tr></thead><tbody>';
      for (const row of rows) {
        if (taskTable) {
          const taskId = row[0].replace(/\*|`/g, '').trim();
          const taskTitle = (row[1] || row[0]).replace(/\*|`/g, '').trim();
          const status = taskProgress(page, taskId);
          tasks.push({ id: taskId, title: taskTitle, section: headings.at(-1)?.title || 'Tasks', status });
          row.push(status);
        }
        html += '<tr>' + row.map((cell, index) => `<td${taskTable && index === row.length - 1 ? ' class="progress-cell"' : ''}>${inline(cell)}</td>`).join('') + '</tr>';
      }
      html += '</tbody></table></div>\n';
      continue;
    }
    const ordered = line.match(/^\s*\d+\.\s+(.+)$/);
    const unordered = line.match(/^\s*[-*]\s+(.+)$/);
    if (ordered || unordered) {
      flushParagraph();
      const nextType = ordered ? 'ol' : 'ul';
      if (listType !== nextType) { closeList(); listType = nextType; html += `<${listType}>\n`; }
      const itemText = (ordered || unordered)[1];
      const isImplementationTask = Boolean(ordered && headings.at(-1)?.title === 'First implementation targets');
      let status;
      if (isImplementationTask) {
        const id = `I${tasks.length + 1}`;
        status = taskProgress(page, id);
        tasks.push({ id, title: itemText, section: headings.at(-1).title, status });
      }
      html += `<li>${inline(itemText)}${isImplementationTask ? `<div class="task-progress"><strong>Progress so far:</strong> ${inline(status)}</div>` : ''}</li>\n`;
      i++; continue;
    }
    if (line.startsWith('> ')) {
      flushParagraph(); closeList();
      html += `<blockquote>${inline(line.slice(2))}</blockquote>\n`;
      i++; continue;
    }
    if (!line.trim()) {
      flushParagraph(); closeList(); i++; continue;
    }
    paragraph.push(line.trim());
    i++;
  }
  flushParagraph(); closeList();
  return { html, headings, tasks };
}

function nav(currentSlug) {
  let lastGroup = '';
  let number = 0;
  const content = pages.map(page => {
    const heading = page.group !== lastGroup ? `<div class="nav-kicker">${lastGroup = page.group}</div>` : '';
    const item = `<a href="${page.slug}.html"${page.slug === currentSlug ? ' aria-current="page"' : ''}><span class="nav-number">${String(number++).padStart(2, '0')}</span>${page.short}</a>`;
    return `${heading}${item}`;
  }).join('');
  return `<nav class="side-nav" aria-label="Handbook chapters"><div class="nav-kicker">Explore</div><a href="index.html">Home · illustrated overview</a><a href="handbook.html">Handbook &amp; tasks</a><a href="slides.html">Progress slideshow</a><a href="progress.html">Verified progress &amp; assumptions</a><a href="#" data-search>Search handbook</a>${content}</nav>`;
}

function header() {
  return `<header class="site-header"><div class="header-inner">
    <a class="brand" href="index.html"><span class="brand-mark">λ</span><span>PlasmaLean<small>Verified stellarator design</small></span></a>
    <div class="header-links"><a href="index.html">Home</a><a href="handbook.html">Handbook</a><a href="progress.html">Progress</a><a href="roadmap.html">Roadmap</a><a href="literature.html">Sources</a><a href="#" class="search-link" data-search>Search <span aria-hidden="true">⌘K</span></a><a href="https://github.com/siddhartha-gadgil/PlasmaLean">GitHub ↗</a></div>
    <button class="menu-toggle" data-menu aria-label="Open handbook navigation" aria-expanded="false">☰</button>
  </div></header>`;
}

function searchDialog() {
  return `<dialog id="search-dialog" class="search-dialog"><div class="search-box"><input id="search-input" type="search" placeholder="Search the handbook…" aria-label="Search handbook"><div id="search-results" class="search-results"><p>Search topics and task IDs across the handbook.</p></div></div></dialog>`;
}

function documentPage(page, title, rendered) {
  const overview = overviewSections.find(([, , chapters]) => chapters.includes(page.slug));
  const overviewLink = overview ? `<p class="overview-return"><a href="index.html#${overview[0]}">← Illustrated introduction: ${escapeHtml(overview[1])}</a></p>` : '';
  const toc = rendered.headings.filter(item => item.level === 2 || item.level === 3).map(item => `<a href="#${item.id}">${item.title}</a>`).join('');
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="${escapeHtml(page.summary)}"><title>${escapeHtml(page.short)} · PlasmaLean</title><link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css"><link rel="stylesheet" href="assets/site.css"><script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script><script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"></script><script defer src="assets/site.js"></script></head><body>
  ${header()}<div class="app-shell">${nav(page.slug)}<main class="doc">
    <section class="doc-hero"><div class="eyebrow">${page.group} · PlasmaLean handbook</div><h1>${escapeHtml(title)}</h1><p>${escapeHtml(page.summary)}</p><div class="hero-meta"><span>Lean 4.34.1</span><span>Mathlib 4.34.1</span><span>${rendered.tasks.length} tracked tasks</span></div></section>
    <div class="progress-banner"><span class="progress-dot"></span><div><strong>Implementation status · ${escapeHtml(progress.updated)}</strong>${escapeHtml(progress.summary)} <a href="progress.html">Compiled declarations, build results and assumptions →</a> Chapter notes retain their original planning context; the task progress fields report subsequent work.</div></div>
    ${overviewLink}<article class="prose">${rendered.html}</article>
  </main><aside class="toc" aria-label="On this page"><div class="nav-kicker">On this page</div><ul>${toc}</ul></aside></div>${searchDialog()}<footer class="site-footer">PlasmaLean · Plans are not proofs. Every implemented claim must identify its assumptions, declaration, and build result.</footer></body></html>`;
}

const results = [];
for (const page of pages) {
  const markdown = fs.readFileSync(path.join(root, page.source), 'utf8');
  const title = markdown.match(/^#\s+(.+)$/m)?.[1] || page.short;
  const rendered = renderMarkdown(markdown, page);
  results.push({ ...page, title, ...rendered });
  writeOutput(path.join(docsDir, `${page.slug}.html`), documentPage(page, title, rendered));
}

for (const key of Object.keys(progress.tasks)) {
  if (!usedProgressKeys.has(key)) throw new Error(`Progress key does not match a task: ${key}`);
}
const reportPage = { source: `progress/${progress.report}`, slug: 'progress', short: 'Verified progress', group: 'Evidence', summary: progress.summary };
const reportMarkdown = fs.readFileSync(path.join(root, reportPage.source), 'utf8');
const reportRendered = renderMarkdown(reportMarkdown, reportPage);
writeOutput(path.join(docsDir, 'progress.html'), documentPage(reportPage, `Progress · ${progress.updated}`, reportRendered));
writeOutput(path.join(docsDir, 'slides.html'), renderSlideshow(slideshow, progress));

const workstreams = results.map((page, index) => `<a class="workstream-card" href="${page.slug}.html"><span class="index">${String(index).padStart(2, '0')} · ${page.group}</span><h3>${escapeHtml(page.short)}</h3><p>${escapeHtml(page.summary)}</p><span class="task-count">${page.tasks.length} tracked tasks</span></a>`).join('');
const sequence = [
  ['model-contracts.html#first-implementation-targets', 'Equilibrium kernel', 'Definitions, tangency, and witnesses'],
  ['mhd-stability.html#start-with-an-abstract-energy-theorem', 'Abstract energy', 'Conservation, coercivity, and zero modes'],
  ['verified-numerics.html#exact-inputs-and-interval-arithmetic', 'Rational intervals', 'Exact decoding and checker soundness'],
  ['geometry-and-fields.html#theorem-backlog', 'Parametric geometry', 'Continuous curve and clearance bounds'],
  ['materials-and-engineering.html#first-exact-thermal-theorem', 'Slab heat', 'Exact thermal margin over an input box'],
  ['coils-and-design.html#filament-fields', 'Biot–Savart fields', 'Source-distance and derivative bounds']
].map(([href, title, detail], index) => `<a href="${href}"><div><strong>${title}</strong><br><span>${detail}</span></div><em>${escapeHtml(progress.tasks[`roadmap:${index + 1}`])}</em></a>`).join('');

const totalTasks = results.reduce((sum, page) => sum + page.tasks.length, 0);
const progressedTasks = results.flatMap(page => page.tasks).filter(task => task.status !== progressText).length;
const handbookHtml = `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><meta name="description" content="The PlasmaLean formalization handbook for verified stellarator design."><title>PlasmaLean · Formalization handbook</title><link rel="stylesheet" href="assets/site.css"><script defer src="assets/site.js"></script></head><body>${header()}${nav('').replace('class="side-nav"', 'class="side-nav home-nav"')}<main class="landing-shell">
  <section class="landing-hero"><div class="doc-hero"><div class="eyebrow">Formalization handbook · October 2026</div><h1>From magnetic geometry to a design proof.</h1><p>A rigorous, staged plan for turning stellarator models, numerical candidates, and engineering data into explicit Lean-checked contracts.</p><div class="hero-meta"><span>${pages.length} guides</span><span>${totalTasks} tracked task entries</span><span>${progressedTasks} entries with scoped progress</span></div></div>
  <aside class="status-panel"><div class="eyebrow">Project status</div><div class="status-stat">${escapeHtml(progress.panel?.stat || 'Contract C1–C5')}</div><h2>${escapeHtml(progress.panel?.headline || 'Status against the stellarator contract')}</h2><p>${escapeHtml(progress.summary)} Counts include repeated roadmap entries, not independent completed goals.</p><a href="progress.html">Read the checked results &amp; remaining gaps →</a></aside></section>
  <section class="overview-feature" aria-labelledby="overview-heading"><div><div class="eyebrow">The motivation &amp; the big picture</div><h2 id="overview-heading">Why stellarators? Why formal proofs?</h2><p>Explore the original illustrated introduction: magnetic confinement, the torus and its field lines, the role of AI discovery, and the architecture of a verified design library.</p><a class="overview-button" href="index.html#background">Explore the illustrated overview →</a></div><div class="overview-topics"><a href="index.html#vision">Project vision &amp; library architecture →</a><a href="index.html#kernel">Boozer coordinates &amp; magnetic geometry →</a><a href="index.html#theory">KAM &amp; stability graphics →</a><a href="index.html#realization">Interactive design demonstration →</a></div></section>
  <section><div class="section-head"><div class="eyebrow">How to read the program</div><h2>One design, several proof obligations.</h2><p>No single “stable” flag is enough. The stellarator contract asks one candidate, with common witnesses, for C1 current-free rotational transform, C2 omnigeneity for thermal ions and electrons, C3 finite-β MHD stability, C4 existence and C5 thermal performance; component and uncertainty contracts then compose around the same candidate. Non-axisymmetry is a consequence of C1, not a goal.</p></div><div class="principles"><div class="principle"><b>Explicit assumptions</b><p>Physical laws, empirical fits, validity ranges, boundaries, norms, and horizons remain visible in every claim.</p></div><div class="principle"><b>Small trusted core</b><p>External solvers propose candidates. Exact decoders and proved checkers establish only the claims their soundness theorems support.</p></div><div class="principle"><b>Evidence gates</b><p>Progress is reported by reviewable artifacts, from an honest kernel through a robust integrated candidate.</p></div></div></section>
  <section><div class="section-head"><div class="eyebrow">The handbook</div><h2>Detailed workstreams</h2><p>Each chapter preserves the complete planning note and gives every tracked task an explicit progress field.</p></div><div class="workstream-grid">${workstreams}</div></section>
  <section><div class="section-head"><div class="eyebrow">Start here</div><h2>The first coding sequence</h2><p>The initial sequence builds reusable, auditable results before attempting a full three-dimensional candidate.</p></div><div class="sequence">${sequence}</div></section>
</main>${searchDialog()}<footer class="site-footer">PlasmaLean · A human-readable guide to the formalization plan. Planning status is kept separate from verified code.</footer></body></html>`;
writeOutput(path.join(docsDir, 'handbook.html'), handbookHtml);

const searchIndex = [];
searchIndex.push({ title: 'Progress slideshow', section: `Evidence updated ${slideshow.updated} · ${progress.summary}`, url: 'slides.html', text: 'progress slideshow presentation latest run evidence vacuum fixture' });
for (const slide of slideshow.slides) {
  searchIndex.push({ title: slide.title, section: 'Progress slideshow', url: `slides.html#${slide.id}`, text: `${slide.title} ${slide.lead} ${slide.progress}`.toLowerCase() });
}
for (const [id, title] of overviewSections) {
  searchIndex.push({ title, section: 'Illustrated overview · interactive graphics and motivation', url: `index.html#${id}`, text: `${title} illustrated overview graphics motivation`.toLowerCase() });
}
for (const page of [...results, { ...reportPage, ...reportRendered }]) {
  searchIndex.push({ title: page.short, section: page.summary, url: `${page.slug}.html`, text: `${page.short} ${page.summary}`.toLowerCase() });
  for (const heading of page.headings) searchIndex.push({ title: heading.title, section: page.short, url: `${page.slug}.html#${heading.id}`, text: `${heading.title} ${page.short}`.toLowerCase() });
  for (const task of page.tasks) searchIndex.push({ title: task.id ? `${task.id} · ${task.title}` : task.title, section: `${page.short} · ${task.status}`, url: `${page.slug}.html`, text: `${task.id} ${task.title} ${task.section} ${task.status}`.toLowerCase() });
}
writeOutput(path.join(docsDir, 'assets/search-index.json'), JSON.stringify(searchIndex, null, 2));

const chapterDirectory = `<details class="landing-chapters"><summary>Formalization handbook · all ${pages.length} guides</summary><p>Detailed plans and progress for every workstream. <a href="progress.html">Compiled results &amp; assumption ledger →</a> <a href="vacuum-demonstrator.html">Vacuum demonstrator: checked margins &amp; next device →</a></p><nav aria-label="All handbook chapters">${pages.map(page => `<a href="${page.slug}.html">${escapeHtml(page.short)}</a>`).join('')}</nav><a href="handbook.html">Handbook overview &amp; task progress →</a></details>`;
const landingHtml = fs.readFileSync(path.join(root, 'scripts/templates/overview.html'), 'utf8')
  .replace('<!-- HANDBOOK_CHAPTER_DIRECTORY -->', chapterDirectory)
  .replaceAll('Only plans have been made and no Lean code has been written for these tasks. Diagrams, code sketches, and the sandbox illustrate the intended program.', 'Foundational proofs, field derivatives and tolerance-aware vacuum-fixture certificates compile, together with exact symmetric equilibria, local stability criteria, alpha-confinement and burn-temperature theorems in idealized models. <a href="progress.html">See the checked declarations and assumptions</a>. Diagrams, code sketches, and the sandbox remain illustrative; no coil-produced stellarator or practical design is certified.');
writeOutput(path.join(docsDir, 'index.html'), landingHtml);
// Preserve earlier overview bookmarks, including the selected tab.
writeOutput(path.join(docsDir, 'overview.html'), `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>PlasmaLean · Overview moved</title><link rel="canonical" href="index.html"><script>location.replace('index.html' + location.search + location.hash);</script></head>
<body><p>The illustrated overview is now the <a href="index.html">PlasmaLean home page</a>.</p></body></html>
`);
console.log(`${checkOnly ? 'Checked' : 'Generated'} ${results.length + 4} content pages (including ${slideshow.slides.length} progress slides) plus an overview redirect with ${totalTasks} task entries (${progressedTasks} with progress).`);
