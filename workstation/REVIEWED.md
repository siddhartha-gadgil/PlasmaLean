# Reviewed workstation runs

One line per `workstation/*` branch handled on the laptop (skill `plasmalean-workstation-update`).

- `workstation/smoke-20261025T091004Z` — smoke: smoke ok (hornbill, Linux x86_64, 24 CPUs; Python packages, Lean build, axioms, push all ok) — workstation 0.0 CPU-min/0.84 GB, laptop n/a — 2026-10-25
- `workstation/lambda-cell-20261025T093842Z` — lambda-cell [1/8, 3/16] (Mu3): failed: numerics, lam_maj.py node_bounds "node invalid" — majorant of the inverse-square-root node LAM1·mQQ·g² = 1.62 ≥ 1 on the complex strip at λ = 3/16 (a structural limit of the majorant, not resolution; the half-width cell [1/8, 5/32] is expected to fail the same way) — workstation 37 min/4.2 GB, laptop n/a — 2026-10-25
- `workstation/lambda-cell-20261025T103705Z` — lambda-cell [1/8, 3/16] (Mu3): failed: Lean, `Mu3Adm` line 144 `BHM 5 + EHM 5 ≤ 1623/10000` (decide +kernel did not reduce to true); all 64+8 check modules, chains and Maj built (old format, peak 7.76 GB); generated files were not committed, so rerun with --skip-numerics after 2af2f39 to get them — workstation 30.5 CPU-min/7.76 GB, laptop n/a — 2026-10-25
- `workstation/lambda-cell-20261025T121254Z` — lambda-cell [1/8, 3/16] (Mu3), --skip-numerics rerun: failed: same `Mu3Adm` check; diagnosis from the pushed files: Lean `BHM 5 + EHM 5 = 1629/10⁴` (emitted ball data, index 5 = Z) but the majorant script used az0 = 1623/10⁴, so the emitted bound is false (generator inconsistency between maj_g.py constants and the emitted ball lists) — workstation 1.2 CPU-min/1.8 GB, laptop n/a — 2026-10-25
