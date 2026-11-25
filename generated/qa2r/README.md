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
