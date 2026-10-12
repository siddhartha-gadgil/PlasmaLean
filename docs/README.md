# PlasmaLean website

The website uses the original illustrated landing page at `index.html`, including
its tabs and interactive graphics. It links to all 11 detailed planning chapters
and to the handbook overview at `handbook.html`. Each chapter links back to the
corresponding landing-page tab. Earlier `overview.html` bookmarks redirect to
`index.html`, preserving the selected tab.

Regenerate the site from the repository root:

```sh
node scripts/generate_handbook.mjs
```

Chapter content comes from `notes/domain-libraries.md` and
`notes/formalization/*.md`. The illustrated overview is maintained in
`scripts/templates/overview.html`; edit that template, since regeneration adds
the chapter directory and writes it to `docs/index.html`. Shared styles and
interactions live in `docs/assets/`.

Preview with `python3 -m http.server 8765 --directory docs`, then open
`http://localhost:8765/`. The overview uses the original Tailwind, Chart.js, and
KaTeX CDN dependencies. Its graphics and sandbox values are illustrative.
All formalization tasks start with planning-only progress.
