# First-mirror signs on the four complete radial tube sequences

At the upper archive height $h_U=5300546391395933/5000000000000000$, a physical signed QA2R line following any of the four canonical radial tube sequences has two transverse first mirrors. Lean has now verified the signs and orientations on the **complete** interval needed for this implication. The original signed ODE trajectory through those tubes is the remaining input. Its upper-height first contacts have outward elapsed azimuths between $317/64$ and $331/64$. [Physical first-mirror theorem](../../PlasmaLean/Design/DommaschkRibbonFirstMirrors.lean) · [Earlier collar and short-prefix certificates](radial-ribbon-mirror-orientation.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-181 |
| Kind | Full physical tube and cap certificates for a prescribed-action implication |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-167, N-169, N-171, N-172 and the canonical wide signed position packets |
| Dependency requirement | For each chosen tile, `Enclosed y (-331/64) (331/64)` and `Tracks forwardRows backwardRows 332 y` for the same physical line. |
| Produces | The exact `Signs y ∧ Simple y` contract used for radial action continuation, both strict exterior signs and the exclusion of either first-well endpoint as a local maximum. |
| Status | The field and derivative implications have passed on every specified tube and cap. An original birth at an arbitrary intermediate radius still needs a joined ODE solution reaching both caps in the same tile. |
| Lean evidence | `DommaschkRadialRibbonNoGrazingFamily.on_tubes`, `upper_caps`, `excludes_grazing` and `signs_and_simple`. |
| Audit evidence | The four tile implications and the family use only `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Complete field coverage

For every original tile, all points in the first 317 position slabs on each clock satisfy $|B|<h_U$, including the common section and clock seams. Sixteen compensated harmonic models cover the 2,536 signed slabs. Their largest upper bound on the scaled gap $R^{16}(|B|^2-h_U^2)$ is less than $-0.00000729427$. The four tile bindings individually check each archived physical radius, central polynomial and affine clock before applying the common sign. [Incoming field verifier](../../scripts/dommaschk_kam/verify_radial_ribbon_incoming.py)

On rows 317 through 330, the N-172 proofs cover a further 112 signed tubes and give $d|B|^2/ds>1/16384$ on the outward clock $s$. The positive exterior sign at $s=331/64$ is separately checked on the final endpoint of row 330 for both directions on every tile. Continuity yields an interior crossing, the earlier strict sign makes it the first crossing, and the positive derivative excludes any other contact in the collar. In signed physical time the derivative is negative on the left and positive on the right. These signs rule out both local maxima in the grazing alternative. [Grazing exclusion](../../PlasmaLean/Design/DommaschkRibbonGrazingAlternative.lean) · [Exterior-cap certificates](../../scripts/dommaschk_kam/verify_radial_ribbon_caps.py)

The result applies to each solution satisfying the original tube membership and the spatially regular signed ODE on the stated window. The sources use 340-row packets, inspect the first 332 rows through the `Tracks` input, and use the extra row to allow an ordinary derivative at the cap. The physical ODE producer uses the same forward and backward row selectors. The upper-height result can be composed directly with a solution from any position in the appropriate section seed. Realization of the prescribed action also requires the common through-birth family and its two strict endpoint action inequalities. [Canonical tile and family attachment](../../scripts/dommaschk_kam/campaign_radial_ribbon_orientation.py) · [Four-tile action contract](../../scripts/dommaschk_kam/verify_radial_ribbon_nongrazing.py)

## Reproduction

Use the original widened four-ribbon archive and its packet and cap receipts from N-169. The input archive has SHA-256 `c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486`. The commands below run serially and resume from previously accepted Lean modules.

```sh
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
r=/tmp/plasma-n169-four-ribbons.json
lake build PlasmaLean.Design.DommaschkRibbonGrazingAlternative PlasmaLean.Design.DommaschkRadialSectionAction
"$py" "$dir/verify_radial_ribbon_slopes.py" --ribbon "$r" --output /tmp/plasma-n172-all-slopes.json
"$py" "$dir/verify_radial_ribbon_incoming.py" --ribbon "$r" --output /tmp/plasma-n172-incoming.json
"$py" "$dir/campaign_radial_ribbon_orientation.py" --tiles 0 1 2 3 \
  --ribbon "$r" --packets /tmp/plasma-n169-packets.json --caps /tmp/plasma-n169-caps.json \
  --below /tmp/plasma-n172-incoming.json --slopes /tmp/plasma-n172-all-slopes.json \
  --output /tmp/plasma-n181-tiles.json
"$py" "$dir/verify_radial_ribbon_nongrazing.py" --ribbon "$r" \
  --tiles /tmp/plasma-n181-tiles.json --output /tmp/plasma-n181-through-cap.json
```

| Canonical radial tile | Original through-cap implication key |
| ---: | --- |
| 0 | `b836be2aecf381eb801b1140f18b7e0b344687876b78fb0be00d3d42a7ca800a` |
| 1 | `21490c6d267115e05762f8775d610cde29c5d21a5f427c8a951397f5fdac93e9` |
| 2 | `f05db07b35e6cdf40f0e5b66de6241d966c3e328bac2265eb9c72762e269bb30` |
| 3 | `c8a7f1a8f70c18528d69eb1ee8097d6f530548388d3ff133cdbb8b2bed5e9054` |

The family key is `94d766bf455298a2ad003c9809cc650a50503608d2663a9ce355876ec81f4f16`. It exports `signs_and_simple k enclosed tracked` at the original exact height as well as the two separate exterior signs from `upper_caps k tracked`. The final replay took 3.67 seconds and peaked at 4.95 GiB. An input containing only partially verified tile histories was rejected before the family was compiled.
