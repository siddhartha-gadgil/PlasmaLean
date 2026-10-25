# Reviewed workstation runs

One line per `workstation/*` branch handled on the laptop (skill `plasmalean-workstation-update`).

- `workstation/smoke-20261025T091004Z` — smoke: smoke ok (hornbill, Linux x86_64, 24 CPUs; Python packages, Lean build, axioms, push all ok) — workstation 0.0 CPU-min/0.84 GB, laptop n/a — 2026-10-25
- `workstation/lambda-cell-20261025T093842Z` — lambda-cell [1/8, 3/16] (Mu3): failed: numerics, lam_maj.py node_bounds "node invalid" — majorant of the inverse-square-root node LAM1·mQQ·g² = 1.62 ≥ 1 on the complex strip at λ = 3/16 (a structural limit of the majorant, not resolution; the half-width cell [1/8, 5/32] is expected to fail the same way) — workstation 37 min/4.2 GB, laptop n/a — 2026-10-25
