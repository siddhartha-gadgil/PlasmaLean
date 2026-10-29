# scripts/

Setup, audits, site generation, untrusted numerical oracles and the workstation pipeline. Nothing
in this folder is trusted: oracles only propose certificate data, which the Lean kernel re-checks.

## Setup and audits

| Script | Purpose |
| --- | --- |
| [`setup.sh`](setup.sh) | Idempotent setup (Linux/macOS): installs elan if missing (toolchain from `lean-toolchain`), `lake exe cache get`, `lake build`; `--check-axioms` runs the axiom audit, `--python` creates the venv `.venv-ws` from `requirements.txt`, `--no-build` stops after the cache, `--help` |
| [`check_axioms.lean`](check_axioms.lean) | Axiom audit of the default build: `lake env lean scripts/check_axioms.lean` checks every declaration of `PlasmaLean` (only `propext`, `Classical.choice`, `Quot.sound`) and prints the axioms of the main entry points; add new entry points here |
| [`check_axioms_heavy.lean`](check_axioms_heavy.lean) | Axioms of the on-demand top modules (`RationalStellaratorGCEwFamily`, `…GCMuWide`, `…GCMuQuarter`, Mu3–Mu5); build those modules first |
| [`audit_kernel_fact.py`](audit_kernel_fact.py) | Classifies the kernel-fact leaves of `kernel_fact` proofs on the built oleans (a, a-data, b = recursive PlasmaLean definition unfolded; `--time` times the b leaves), to find leaves that should become explicit certificates |
| [`requirements.txt`](requirements.txt) | Python packages for the oracle scripts and the workstation pipeline |

## Website

| Script | Purpose |
| --- | --- |
| [`generate_handbook.mjs`](generate_handbook.mjs) | Regenerates `docs/` (handbook pages from the notes, progress page, slideshow from `progress/slideshow.json`) |
| [`check_site.mjs`](check_site.mjs), [`check_slideshow.mjs`](check_slideshow.mjs) | Site checks: local links, fragments, inline scripts, task entries, slideshow structure |
| [`render_slideshow.mjs`](render_slideshow.mjs), [`templates/`](templates/) | Slideshow renderer and page template used by the generator |

## Untrusted oracles (numerics that propose certificate data and emit Lean)

| Script or folder | Feeds |
| --- | --- |
| [`kam_oracle/`](kam_oracle/) | KAM torus A of the rational stellarator field (`Design/KamTorusA*`) |
| [`gc_kam/`](gc_kam/) | Guiding-centre KAM families: Torus/NegTorus, Fam, Mu cells (`lamcell/`, with `validate.py`), energy window (`ew_*`), low-memory and proof-term emitters (`lowmem/`, `proofterm/`) |
| [`coil_kam_oracle/`](coil_kam_oracle/) | Coil-field KAM refit and residual certificate (`Design/CoilKam*`) |
| [`rational_stellarator_oracle/`](rational_stellarator_oracle/), [`rational_stellarator_coils/`](rational_stellarator_coils/) | First-integral boxes of the rational field; polygonal and cubic coil sets and their certificates (`Design/PolygonCoil*`, `RationalStellaratorCoilsGrad`) |
| [`solovev_band_oracle/`](solovev_band_oracle/), `solovev_ballooning_oracle.py`, `solovev_mercier_oracle.py`, `solovev_mercier_quadrature_oracle.py` | Solov'ev transport bands, ballooning cells and boxes, Mercier index and quadrature cells |
| `landreman_mercier_oracle.py`, `landreman_family2_map.py`, `landreman_family2_ballooning_oracle.py`, [`family2_ballooning_cert/`](family2_ballooning_cert/) | Landreman family 2: Mercier index, maps, ballooning study and certificate search (no theorem yet) |
| `helical_mercier_oracle.py` | Mercier index of the helical equilibrium |
| [`trapped_reanchor/`](trapped_reanchor/) | Trapped-alpha oscillation cells (`Design/NearAxisQATrappedOsc*`), with a bit-exact mirror of the checker |
| `validated_bvp_oracle.py`, `validated_slab_oracle.py` | Validated BVP and slab Grad–Shafranov data (`Design/ValidatedBVP`, `ValidatedSlab*`) |
| [`workstation/`](workstation/README.md) | Workstation pipeline: heavy numerics and builds on a big machine, re-checked on the laptop |

Some modules (for example `SolovevMercierQuadrature`, the Landreman `…Cert*` modules) have no
generator here; see the module docstrings and the implementation plan.

## Conventions

At the first Lean use, run `scripts/setup.sh --check-axioms` (or `--no-build` on a machine that
should not build everything); it installs `elan` when Lean is missing and selects the pinned
toolchain. Do not substitute an unrelated system Lean. The full default build is heavy: keep each
Lean process within about 6 GB, build stale heavy modules one at a time (`lake build --no-build
<Top>` lists them), and send first builds of large certificates to the workstation.

Create the Python environment only when a script needs it, and activate it in each shell:

```bash
scripts/setup.sh --python --no-build
source .venv-ws/bin/activate
```

Oracles go in their own subfolder per family, take configurable input and output paths (not
`/tmp`), validate every emitted bound in exact arithmetic before writing Lean, and are run with
`python3 -I` on any downloaded data.
