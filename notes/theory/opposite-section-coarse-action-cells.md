# Physical coarse action panels at the opposite QA2R section

Lean proves that one pair of nested embedded QA2R tori supports all four opposite-section action launches. For every birth angle $|\phi-\pi/2|\le 2^{-20}$, each radius has a signed physical trajectory through its admitted birth on $[-5/64,5/64]$. On $[-1/64,1/64]$, 96 independently certified enclosures across the four launches imply all 384 chronological action cells. Each enclosure uses the archived position coefficients, radius and angular model for its own sign. [Coarse-cell lemma](../../PlasmaLean/Certificates/CoarseActionCells.lean) · [Common-tori checker](../../scripts/dommaschk_kam/verify_coarse_common_births.py)

## Metadata

| Field | Value |
| --- | --- |
| ID | N-140 |
| Title | Physical coarse action panels at the opposite QA2R section |
| Kind | Certificate |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-60, N-83, N-94, N-120, N-134, N-138, N-139 |
| Dependency requirement | Individual signed position tubes, checked harmonic models, exact physical sparse field identities, and the N-139 coarse packet for the same radius, direction count and height. |
| Produces | Physical signed coarse cells, the signed ODE and action cover from the same admitted birth, and a direct check of the expanded block in the complete coarse archive. |
| Difficulty | Coarse intervals cross multiple native storage cells. Both the opposite-section field evaluation and the negative-time indexing must retain the exact directed rounding. |
| Status | The physical claims apply on the stated launch windows. Each endpoint still requires propagation and action coverage out to its mirror brackets for the whole-well target. |
| Lean evidence | `DommaschkCoarseActionPhase.physical_phase`, `NativeActionInterval.coarse_time_mem`, `NativeActionInterval.directed_cells`, and `DommaschkCoarseOppositeCommon456464509517.common`. |
| Audit evidence | The physical applications use `propext`, `Classical.choice` and `Quot.sound`. |
| Last updated | 25 November 2026 |

## Physical meaning

Let $t$ denote the signed angular displacement from $\pi/2$. The field magnitude is evaluated at $(R,\pi/2+t,z)$. The angular change sends $(\cos 2t,\sin 2t)$ to $(-\cos 2t,-\sin 2t)$. For a monomial with angular exponents $c,d$, the corresponding coefficient receives the factor $(-1)^{c+d}$. Lean proves this substitution for every sparse polynomial. Applying it to spatial coefficients before Horner evaluation preserves the order of directed integer rounding in the source. The four field expansions checked in this basis are the toroidal denominator, both poloidal numerators and the compensated toroidal expression. [Physical angular substitution](../../PlasmaLean/Design/DommaschkCoarseActionPhase.lean) · [Signed field model producer](../../scripts/dommaschk_kam/verify_coarse_action_models.py)

The model proof encloses $D$, $R^8$, $R^{16}$, $R^{16}|B|^2$ and $R^{16}(h^2-|B|^2)$ on the true signed position tube. It selects the upper or lower application height for that endpoint. The panel proof checks each of those models by exact Horner arithmetic, verifies all positive divisors and the directed square root, then matches the density, squared-speed and speed digits to the corresponding 72-bit subword. For $m$ source panels and $c$ consecutive copies, the generic time lemma proves the closed subinterval inclusion whenever $mc=48$. The negative clock reverses the order of both the slabs and their constituent panels. [Physical column identities](../../PlasmaLean/Design/DommaschkNativeActionColumns.lean) · [Directed cell proofs](../../PlasmaLean/Certificates/CoarseActionCells.lean)

The signed-arclength density being bounded is $R|B|/B_\phi$. The other input is the clipped squared parallel speed $\max(2(h-|B|),0)$. Both are in model units. Each local proof exposes the expanded full word as `.archive`, its equality with the stored chronological block as `.original`, and its integer mass as `.encoded_mass`. A closed ODE passage from the transferred physical birth supplies every position-tube hypothesis on both signed sides. [Original physical cells from a birth](../../scripts/dommaschk_kam/verify_coarse_action_birth.py)

## Launch cases

The heights are $h_L=5297961656084411/5000000000000000$ and $h_U=5300546391395933/5000000000000000$. A lower packet rounds both physical inputs down. An upper packet rounds them up. The two blocks adjoining each of the four launches are different indexed objects in the trajectory and action archives, including when the integer masses coincide.

| Launch radius | Height | Directed comparison | Negative and positive chronological indices |
| --- | --- | --- | --- |
| $456/1000$ | $h_U$ | Upper | 327, 328 |
| $464/1000$ | $h_U$ | Lower | 328, 329 |
| $509/1000$ | $h_L$ | Upper | 326, 327 |
| $517/1000$ | $h_L$ | Lower | 327, 328 |

At $456/1000$, each signed block has integer mass 8420756413444. The two individual Horner and rounding proofs took 13.3 and 13.6 seconds on the workstation after their physical model inputs were available. The corresponding applications to the expanded blocks took 4.1 and 4.2 seconds. A one-bit alteration to the first density digit was rejected by the signed input check.

The joint theorem has receipt `64e03bda839e634d0f849d1bc474c3be40dd521cf5efc1364242bd0919d21c70`. Its four signed birth receipts, in the order shown above, start with `bfbbb7365e38`, `e28693b59032`, `0f186fad4d52` and `7bb780fbe1df`. The theorem quantifies the common tori before the birth angle and the four endpoint statements. Each endpoint has its own physical trajectory between these same tori.

## Reproduction

Start with the N-139 packet receipts in the indicated directory and five-slab signed prefixes for the four opposite-section endpoints. The family verifier runs one checker at a time. Model and field certificates are cached by content, with a separate root for each independently signed row.

```bash
lake build PlasmaLean.Certificates.CoarseActionCells PlasmaLean.Design.DommaschkCoarseActionPhase
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_launch_family.py \
  --packets /tmp/plasma-n139-packets --output /tmp/plasma-n140-opposite-family.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_coarse_common_births.py \
  --family /tmp/plasma-n140-opposite-family.json --output /tmp/plasma-n140-common-births.json
```

Individual rows are replayed with `verify_coarse_physical_action.py --packet PACKET --row I --output REPORT`. The packet is authenticated before the row checker reads its chronological block. [Serial family checker](../../scripts/dommaschk_kam/verify_coarse_launch_family.py) · [Common physical birth checker](../../scripts/dommaschk_kam/verify_coarse_common_births.py)
