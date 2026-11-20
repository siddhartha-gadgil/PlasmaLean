# Source analysis: "Complex vacuum fields and new stability estimates" (18 November 2026)

| Field | Value |
| --- | --- |
| Task | source analysis for `plasmalean-update-notes-from` |
| Mode | source study (no proof attempts, no explorations) |
| Assessment note | `N-42` (`notes/theory/fusion-complex-geometry-assessment.md`) |
| Status | analysis complete; checks below |
| Date | 20 November 2026 |

## Sources

1. `sources/fusion_complex_geometry_and_stability.pdf`: "Fusion / research note. Complex vacuum
   fields and new stability estimates", dated 18 November 2026, 28 pages, no authors named. It was
   supplied through Vamsi Pingali and committed by the user on 19 November 2026 (`9be616f`).
   SHA-256 `4f080749dc96358bfaba878144fd21b5e327efc67f2856d02149163693df7f7e`.
2. The accompanying bundle `sources/fusion_complex_geometry_reproducibility/` (`433fe74`), used
   **only** to read the LaTeX source of the same note. `pdftotext` drops every displayed formula
   because the PDF renders them as images. The bundle's `continuation_*.tex` files are the full
   text, and the formulas were read from them. The bundle's scripts were **not run**. The checks
   below come from independent scripts in `scripts/fcg_source/`. The bundle's copies of
   `candidate.json` and `DommaschkQA2RData.lean` are byte-identical to the project files
   (`cmp`). The Lean data file's blob hash at `6312f1c` is `dbca1da…`, as the bundle states.

The note pins project commit `6312f1c` (17 November 2026) for the Dommaschk seed tori.

## Artifacts

- `02_literature_review.md`: extraction table, source study per result, techniques and stress
  tests.
- `02_examples.md`: exact and numerical checks, with the commands and outputs.
- Scripts: `scripts/fcg_source/check_laurent.py`, `check_algebra.py`,
  `check_cylinder_hotcore.py`.

## Outcome

See `N-42`. In short, every explicit formula, constant and identity checked agrees with the
source, and no claim was found incorrect. The results come from three different configurations:
a Dommaschk vacuum family, a periodic cylinder, and a prescribed exact weak-QS field. As the
source itself stresses, they are not one stellarator.
