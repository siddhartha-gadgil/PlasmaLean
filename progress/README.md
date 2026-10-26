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

[20 October 2026, Phase 5: one field with a pressure-budget band (first called "one consistent plasma"), certified Mercier stability, near-QA alphas for 0.19 s](2026-10-20-progress-6.md).

[20 October 2026, Phase 6: the pressure-budget band on the actual geometry, high-Q and ignited, ballooning, a first exact stellarator field](2026-10-20-progress-7.md).

[20 October 2026, Phase 7 part 1: certified field-line confinement in an exact stellarator field; the coarea step formalized](2026-10-20-progress-8.md).

[20 October 2026, Phase 7 part 2: ballooning on every surface, coils for the stellarator field, trapped-alpha non-resonance](2026-10-20-progress-9.md).

[20 October 2026, Phase 8: a finite-β non-axisymmetric equilibrium, and the invariant-torus route to all-time stellarator confinement](2026-10-20-progress-10.md).

[21 October 2026, Phase 9 part 1: a validated approximate invariant torus, and the first KAM lemmas](2026-10-21-progress.md).

[21 October 2026, Phase 9 part 2: the first coil-produced stellarator field with certified confinement; KAM convergence, algebra and composition](2026-10-21-progress-2.md).

[21 October 2026, Phase 9 part 3: KAM inputs complete for the stellarator torus; a sheared finite-β non-axisymmetric equilibrium](2026-10-21-progress-3.md).

[21 October 2026, Phase 9 part 4: the finite-β non-axisymmetric families are Mercier-unstable](2026-10-21-progress-4.md).

[21 October 2026, Phase 10: all-time field-line confinement in an exact stellarator field, by a verified KAM theorem](2026-10-21-progress-5.md).

[21 October 2026, Phase 10 addendum: field-line existence — all-time confinement without hypotheses](2026-10-21-progress-6.md).

[21 October 2026: coil-produced field confined for 52 transits; generic KAM; guiding-centre groundwork](2026-10-21-progress-7.md).

[21 October 2026: exact guiding-centre invariant torus for alphas; coil-KAM blocked](2026-10-21-progress-8.md).

[21 October 2026: all-time confinement of passing 3.5 MeV alpha guiding centres in an exact stellarator field](2026-10-21-progress-9.md).

[21 October 2026, Phase 11 part 1: robust alpha confinement over a range of B₀R₀; both signs; μ > 0 identity; trapped progress](2026-10-21-progress-10.md).

[21 October 2026, Phase 14B: a Mercier-stable finite-β non-axisymmetric band; trapped-alpha kick bound](2026-10-21-progress-11.md).

[21 October 2026, Phase 11 part 2: μ > 0 alpha guiding centres over a pitch-angle cell; stable band with derived labels](2026-10-21-progress-12.md).

[25 October 2026, Phase 11 part 3, Phase 14B, Phase 15: an energy window and λ ∈ [0, 1/8] for alpha guiding centres; family-2 ballooning reduced (not certified); a workstation pipeline](2026-10-25-progress-13.md).

[26 October 2026, Phase 11 part 4, Phase 16: passing alphas confined forever for every λ ∈ [0, 1/4]; low-memory kernel checks; proof-term certificates instead of decide +kernel; the workstation pipeline in use](2026-10-26-progress-14.md).
