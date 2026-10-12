import assert from 'node:assert/strict';

const escapeHtml = value => String(value).replaceAll('&', '&amp;').replaceAll('<', '&lt;')
  .replaceAll('>', '&gt;').replaceAll('"', '&quot;');

function fixtureDiagram() {
  return `<figure class="fixture-diagram">
    <svg viewBox="0 0 440 330" role="img" aria-labelledby="fixture-title fixture-description">
      <title id="fixture-title">Two-loop calibration fixture</title>
      <desc id="fixture-description">Schematic, not to scale. Two circular coils of radius 10 cm in planes z equals plus and minus 20 cm. A 5 cm observation ball surrounds a smaller 1 mm probe ball at the origin.</desc>
      <line class="diagram-axis" x1="170" y1="24" x2="170" y2="302" />
      <text x="181" y="29">z</text>
      <ellipse class="diagram-coil" cx="170" cy="75" rx="116" ry="30" />
      <ellipse class="diagram-coil" cx="170" cy="255" rx="116" ry="30" />
      <line class="diagram-measure" x1="170" y1="75" x2="286" y2="75" />
      <text x="202" y="65">10 cm</text>
      <text x="297" y="80">z = +20 cm</text>
      <text x="297" y="260">z = −20 cm</text>
      <circle class="diagram-region" cx="170" cy="165" r="42" />
      <circle class="diagram-probe" cx="170" cy="165" r="6" />
      <line class="diagram-measure" x1="213" y1="148" x2="273" y2="137" />
      <text x="282" y="141">5 cm ball</text>
      <line class="diagram-measure" x1="177" y1="168" x2="273" y2="188" />
      <text x="282" y="193">1 mm probe</text>
      <text x="45" y="322">Schematic · radii and probe enlarged for clarity</text>
    </svg>
    <figcaption>Same current orientation in both coils. No simulated field lines are shown.</figcaption>
  </figure>`;
}

// Content stays in progress/slideshow.json. No raw HTML is accepted from the data.
export function renderSlideshow(deck, progress) {
  assert.equal(deck.updated, progress.updated, 'Refresh slideshow.updated after each run');
  assert.equal(deck.report, progress.report, 'Refresh slideshow.report and content after each run');
  assert.ok(Array.isArray(deck.slides) && deck.slides.length > 0, 'Slideshow must have slides');
  const seen = new Set();
  const text = (value, name) => assert.ok(typeof value === 'string' && value.trim(), `Missing slideshow ${name}`);
  text(deck.status, 'status');
  const safeLink = href => {
    assert.match(href, /^[a-z][a-z0-9-]*\.html(?:#[a-z0-9-]+)?$/, 'Use a local evidence page/fragment');
    return escapeHtml(href);
  };
  const slides = deck.slides.map((slide, index) => {
    assert.match(slide.id, /^[a-z][a-z0-9-]*$/);
    assert.ok(!seen.has(slide.id), `Duplicate slide ${slide.id}`);
    seen.add(slide.id);
    for (const key of ['eyebrow', 'title', 'lead', 'progress', 'boundary']) text(slide[key], key);
    assert.ok(slide.evidence?.length, `Slide ${slide.id} needs evidence`);
    assert.ok(!slide.diagram || slide.diagram === 'fixture', 'Unknown slide diagram');
    const cards = (slide.cards || []).map(card => {
      for (const key of ['title', 'text', 'status']) text(card[key], `card.${key}`);
      assert.ok(['checked', 'partial', 'synthetic', 'next'].includes(card.kind), 'Unknown card status');
      return `<article class="slide-card"><span class="card-status ${card.kind}">${escapeHtml(card.status)}</span><h3>${escapeHtml(card.title)}</h3><p>${escapeHtml(card.text)}</p></article>`;
    }).join('\n');
    const metrics = slide.metrics?.map(metric => {
      text(metric.value, 'metric.value'); text(metric.label, 'metric.label');
      return `<div><dt>${escapeHtml(metric.label)}</dt><dd>${escapeHtml(metric.value)}</dd></div>`;
    }).join('');
    const evidence = slide.evidence.map(link => {
      text(link.label, 'evidence.label');
      return `<a href="${safeLink(link.href)}">${escapeHtml(link.label)} <span aria-hidden="true">↗</span></a>`;
    }).join('');
    const heading = index === 0 ? 'h1' : 'h2';
    return `<section id="${slide.id}" class="slide${index === 0 ? ' opening-slide' : ''}" aria-labelledby="${slide.id}-title" tabindex="-1" data-slide>
      <div class="slide-topline"><p class="eyebrow">${escapeHtml(slide.eyebrow)}</p><span class="slide-number">${String(index + 1).padStart(2, '0')} / ${String(deck.slides.length).padStart(2, '0')}</span></div>
      <${heading} id="${slide.id}-title">${escapeHtml(slide.title)}</${heading}>
      <p class="slide-lead">${escapeHtml(slide.lead)}</p>
      ${metrics ? `<dl class="slide-metrics">${metrics}</dl>` : ''}
      ${cards ? `<div class="slide-content${slide.diagram ? ' with-diagram' : ''}">${slide.diagram ? fixtureDiagram() : ''}<div class="slide-cards cards-${slide.cards.length}">${cards}</div></div>` : ''}
      <div class="slide-progress"><h3>Progress so far</h3><p>${escapeHtml(slide.progress)}</p></div>
      <p class="slide-boundary"><strong>Claim boundary.</strong> ${escapeHtml(slide.boundary)}</p>
      <footer class="slide-evidence"><span>Evidence · ${escapeHtml(deck.updated)}</span>${evidence}</footer>
    </section>`;
  }).join('\n');
  const options = deck.slides.map((slide, index) => `<option value="${index}">${index + 1}. ${escapeHtml(slide.title)}</option>`).join('');
  return `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
  <meta name="description" content="${escapeHtml(progress.summary)}">
  <title>Progress slideshow · PlasmaLean</title>
  <link rel="stylesheet" href="assets/slides.css"><script defer src="assets/slides.js"></script>
</head><body>
  <a class="skip-link" href="#presentation">Skip to slides</a>
  <header class="deck-header"><a class="deck-brand" href="index.html"><span aria-hidden="true">λ</span> PlasmaLean</a><nav aria-label="Website"><a href="index.html">Home &amp; graphics</a><a href="handbook.html">Handbook</a><a href="progress.html">Full report</a></nav><p>Evidence updated <time datetime="${escapeHtml(deck.updated)}">${escapeHtml(deck.updated)}</time></p></header>
  <main id="presentation" class="deck" tabindex="-1" aria-label="Progress slideshow">${slides}</main>
  <nav id="slide-controls" class="slide-controls" aria-label="Slideshow controls" hidden>
    <div class="step-controls"><button id="slide-prev" type="button" aria-label="Previous slide" aria-controls="presentation">← Previous</button><output id="slide-counter" aria-live="polite" aria-atomic="true"></output><button id="slide-next" type="button" aria-label="Next slide" aria-controls="presentation">Next →</button></div>
    <div class="view-controls"><label for="slide-select">Jump to</label><select id="slide-select" aria-controls="presentation">${options}</select><button id="slide-view" type="button" aria-pressed="false" aria-controls="presentation">Read all</button><button id="slide-print" type="button">Print / PDF</button></div>
    <p class="keyboard-hint">← → / Space to move · Home / End to jump · No autoplay</p>
  </nav>
  <noscript><p class="no-script">All slides are shown below each other. Enable JavaScript for presentation controls, or use your browser's Print command to print the full deck.</p></noscript>
  <footer class="deck-footer">${escapeHtml(deck.status)} <a href="roadmap.html#milestones-and-evidence-gates">What the milestones mean</a></footer>
</body></html>
`;
}
