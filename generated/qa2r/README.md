# Script-generated QA2R certificates

Lean sources written by the campaign scripts in `scripts/dommaschk_kam/` for the Dommaschk QA2R
field (notes N-49 onwards), copied unchanged from the workstation caches by
`scripts/qa2r/collect_generated.py`. They are the modules cited in the notes together with every
generated module they import. Audit findings AW-H1 and AW-H2 (25 November 2026) are the reason
they are here.

| File | Content |
| --- | --- |
| `archives/<Package>.tar.zst` | the sources of one package, as stored in git (`scripts/qa2r/pack.py unpack` restores them; the replay does this itself) |
| `<Package>/<Module>.lean` | one Lean module, named `<Package>.<Module>` (unpacked; ignored by git) |
| `MANIFEST.sha256` | SHA-256 of every source |
| `receipts.json` | per source: campaign receipt key, theorems named by the receipt, recorded time and peak memory |
| `roots.txt` | the cited modules, imported by `scripts/check_axioms_qa2r.lean` |
| `packages.txt` | the package names (roots of the Lake library `QA2RGenerated`) |
| `replay-report.json` | result of the last full replay |

The library `QA2RGenerated` (`lakefile.toml`) is on demand: it is not part of the default build.

    python3 scripts/qa2r/replay.py            # hashes, tiered `lake build`, axiom audit
    python3 scripts/qa2r/replay.py --target PeriodicCollarFamilyCache.DommaschkPeriodicOriginalCollar

The replay reads nothing under `/tmp` and no campaign cache. A full replay needs a machine with
at least 64 GB of memory (the largest module peaks at about 34 GB) and several hundred CPU-hours.

The scripts that produced these sources, and their numerical inputs, are untrusted: the evidence
is the Lean build and the axiom audit. Generated modules that no note cites stay in the
workstation caches and support no claim.

## Opposite-inner campaign closeout, 26 November 2026

At the original QA2R radial label 0.470 and phases within 2⁻²⁷ radians of π/2, the signed field-line certificate joins 320 ODE rows in each direction and all 15,360 action panels on the angular interval [−5, 5] about that section. For every independently observed regular first well through one of those births at the specified upper height, the dimensionless one-way action is at least 287167485626455/211106232532992, strictly above the target by more than 0.0003. The inequality quantifies over qualifying observations. Existence of such an observation and thermal particle confinement are separate questions.

| Archived root | Checked declaration | Campaign receipt key |
| --- | --- | --- |
| `OppositeInnerThroughCache.DommaschkOppositeInnerThrough320` | `from_nested_tori` | `810f6f41a3dc3ef923cc9402c044c06711a157871ba359e287e775bd55f52716` |
| `OppositeObservedWellCache.DommaschkOppositeObservedWells320` | `grounded_exclusion` | `8eeee84f13cde027cf0c4e98d91881954f68412b69837ad131e95509bdebd3e0` |

The 640 signed ODE rows and 640 signed action rows completed without a recorded row failure. The workstation journal records progress at 10:30 and 10:42 IST on 25 November. At 00:43 IST on 26 November the final assembly failed because Lean grouped successive list appends from the left. The repaired assembler groups the remaining blocks on the right as it joins each segment. It reused every checked row. The dependent first-well observer then completed.

These two roots add 12,383 sources to the previously archived 43,435. To append accepted roots on a producer workstation with the prior archive unpacked, use `collect_generated.py --extend --extra-root MODULE` for the selected module names, followed by `pack.py pack`. The repository replay command above checks the full archive. [Original campaign specification](../../notes/theory/opposite-inner-physical-trace.md) · [Full replay report](replay-report.json)
