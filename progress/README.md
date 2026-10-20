# Progress

[12 October 2026: verified foundations and remaining integration gaps](2026-10-12-progress.md).

[12 October 2026, run 2: tolerance-aware vacuum fields and probe-escape sanity](2026-10-12-progress-2.md).

[14 October 2026: exact equilibria, interchange criteria and symmetric confinement](2026-10-14-progress.md).

[20 October 2026: implementation plan, note corrections and proof-engineering skill](2026-10-20-progress.md).

[20 October 2026, Phase 1: burn temperature, transport comparison, vacuum maximum principle](2026-10-20-progress-2.md).

[20 October 2026, Phase 2: core-temperature barrier, all-mode screw-pinch stability, min-B obstruction](2026-10-20-progress-3.md).

`status.json` is the per-task status source used to generate the website. Keep
declarations, scope, build results and assumptions in the dated report; update
the manifest only after the corresponding Lean result compiles. Unlisted tasks
remain planning-only. Run `node scripts/generate_handbook.mjs` after updates.

`slideshow.json` is the human-readable progress narrative for `docs/slides.html`.
Refresh its results, boundaries, evidence links and next steps after every run;
its `updated` and `report` must match `status.json`. The generator checks this
alignment, but scientific scope and counts still need human review against the
dated evidence. Run `node scripts/check_site.mjs` before handing off the update.

[20 October 2026, Phase 3: 3.5 MeV alphas confined for all time, stellarator-geometry core barrier, validated BVP](2026-10-20-progress-4.md).

[20 October 2026, Phase 4: near-quasisymmetric alphas for 0.11 s, a validated plasma equilibrium, Mercier findings](2026-10-20-progress-5.md).
