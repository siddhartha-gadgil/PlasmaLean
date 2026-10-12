# PlasmaLean website

The website uses the original illustrated landing page at `index.html`, including
its tabs and interactive graphics. It links to all 12 detailed guides,
the handbook overview at `handbook.html`, and the progress slideshow at
`slides.html`. Each chapter links back to the
corresponding landing-page tab. Earlier `overview.html` bookmarks redirect to
`index.html`, preserving the selected tab.

Regenerate the site from the repository root:

```sh
node scripts/generate_handbook.mjs
```

Chapter content comes from `notes/domain-libraries.md` and
`notes/formalization/*.md`, plus `notes/design/vacuum-demonstrator.md`.
The illustrated overview is maintained in
`scripts/templates/overview.html`; edit that template, since regeneration adds
the chapter directory and writes it to `docs/index.html`. Shared styles and
interactions live in `docs/assets/`.

Preview with `python3 -m http.server 8765 --directory docs`, then open
`http://localhost:8765/`. The overview uses the original Tailwind, Chart.js, and
KaTeX CDN dependencies. Its graphics and sandbox values are illustrative.
Current task status comes from `progress/status.json`, with declaration names,
assumptions and build evidence in the dated report it names. Unimplemented tasks
retain planning-only status. The report is rendered as `progress.html`, reachable
from the original landing page and all handbook chapters.

## Progress slideshow

Edit `progress/slideshow.json` after each run, then regenerate the site. Its date
and report must match `progress/status.json`; generation rejects mismatches.
Each slide carries progress so far, a claim boundary and links to evidence.
Refresh the narrative and counts from that run's checked results, including
stagnation or blockers rather than suggesting unearned progress. Keep slide IDs
stable so search results and shared bookmarks remain useful.

The renderer is `scripts/render_slideshow.mjs`; presentation styles and controls
are `docs/assets/slides.css` and `docs/assets/slides.js`. No external libraries,
fonts or network calls are required for the slideshow. Use Previous/Next, the
slide picker, arrow keys, Space, or Home/End. Read all displays every slide;
Print / PDF uses print styles to include the complete deck. With JavaScript
disabled, all slides remain readable. The original landing-page graphics and
their CDN dependencies are unchanged.

After regeneration, run `node scripts/check_site.mjs` to check local links,
fragments, search destinations, task coverage and preserved landing-page graphics.
It also runs `scripts/check_slideshow.mjs` for the slideshow's content contract,
navigation logic, keyboard shortcuts, deep links, read-all mode and print hook.
`node scripts/generate_handbook.mjs --check` checks reproducibility without writing
files. These checks do not replace browser-rendered visual or interaction testing.
