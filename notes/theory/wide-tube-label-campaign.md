# Wide-tube label campaign for QA2R: screen and design

**27 November 2026.** The campaign that N-214 and N-215 call for was costed before any proof run. Repeating the existing thin tubes on a grid is out of reach (of the order of 10⁵ to 10⁶ CPU-hours). A screen shows that this is unnecessary: the field-line flow of the QA2R well is almost linear over tubes about 500 times wider than the certified ones, so one coarse trace per direction can carry the label for a whole thermal-electron bounce. This note fixes the target and the stages. No certificate has been produced yet; C2 remains open.

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-216` |
| Title | Wide-tube label campaign for QA2R: screen and design |
| Kind | Computation (untrusted screen) and campaign design; status log for the campaign |
| Addresses | G-10, G-8, Q-35; RG.5 item 2 |
| Depends on | N-213, N-214, N-215; `Certificates.PositionFrameODE.FieldBounds`, `PositionFrameChain.Chain.trajectory`, `Kinetic.LabelDrift.lipschitz_displacement_le` |
| Dependency requirement | The Lipschitz-label drift theorem (compiled); the moving-frame slab format and its soundness theorem; the campaign receipts for cost data. |
| Produces | Feasibility numbers, the target population, the certificate design and the stage list. |
| Difficulty | Hard. Stages 2 and 3 need new Lean theory (a flow label on a tube) and a new slab certificate with a lower logarithmic-norm bound on wide balls. |
| Status | Stage 1 (screen) done. Stages 2–5 not started. |
| Lean evidence | none for this note |
| Audit evidence | Not audited. Numerics: `scripts/dommaschk_kam/screen_wide_tube.py`, `scripts/dommaschk_kam/results/wide_tube_20261127.json`. |
| Last updated | 27 November 2026 (created) |

## Target (default choice, to be confirmed)

Thermal **electrons** in the top height band on the original launch line (label 0.474, phase 0), at the illustrative scale 10 keV, B₀ = 5 T, R₀ = 10 m (ε = 6.7·10⁻⁶), for about one bounce period (about 4·10⁻⁵ s). Deuterons at this scale have a banana excursion as large as the nested region (N-214) and are not a target of this campaign. The user has not fixed a device scale; these values enter only the final specification, not the certificate.

## Why the thin-tube grid is out of reach (from the campaign receipts)

A certified slab step with its Jacobian costs minutes of CPU: the 2,334 trace modules average 202 s and the 388 Jacobian modules 468 s, and the first campaign cost about 320 CPU-hours in all. A tube has physical radius below 1/300000. Covering the electron window of one half bounce (3.4·10⁻⁴ radially by 3.7·10⁻⁴ transversally, N-214) with such tubes needs of the order of 10⁴ traces of 664 slabs, that is, of the order of 10⁵ to 10⁶ CPU-hours on this 24-core machine.

## Screen: tubes can be about 500 times wider (numerical observation, untrusted)

In the frame of the variational matrix M along the reference line, the Jacobian of the reduced equation is A(φ, v) = M⁻¹(J(y + Mv) − J(y))M. The screen samples A on balls |v| ≤ ρ along 332 slabs of 1/64 radian in each direction and reports the extreme eigenvalues of its symmetric part.

| Frame radius ρ | Largest physical tube radius | Largest \|μ\| | Growth over the half well | Label Lipschitz constant |
| --- | --- | --- | --- | --- |
| 10⁻⁵ | 1.9·10⁻⁵ | 0.0003 | 1.0008 | 1.86 |
| 10⁻⁴ | 1.9·10⁻⁴ | 0.0034 | 1.008 | 1.87 |
| 3·10⁻⁴ | 5.6·10⁻⁴ | 0.010 | 1.023 | 1.90 |
| 10⁻³ | 1.9·10⁻³ | 0.034 | 1.080 | 1.98 |
| 3·10⁻³ | 5.6·10⁻³ | 0.104 | 1.265 | 2.26 |

At ρ = 10⁻³ the tube is five percent of the minor radius and contains the whole electron window of several half bounces, and the label constant is still below 2. The same computation in fixed (R, z) coordinates, without a frame, gives a constant near 35, so the moving frame is worth keeping; it does not need the precision of the thin tubes.

**Conditional inference.** With K ≈ 2 and a drift speed of at most 0.62 ε, the direct bound of N-215 keeps a guiding centre inside a tube of radius 1.9·10⁻³ for about 240 R₀/v at ε = 6.7·10⁻⁶, about one bounce period. A band-form statement on that horizon would be the first instance with physical inputs. Its excursion, measured as change of distance to the axis, includes the variation of the field line's own distance to the axis along the well, so it will be of the order of the minor radius times the shaping, not of the tube radius. Going beyond a bounce needs the averaged estimate; covering the precession needs further traces (about 100 for a full poloidal turn at this radius).

## Stages

1. **Screen** (done, this note).
2. **Lean theory, field-independent.** From a two-sided logarithmic-norm bound in a moving frame on a tube: uniqueness of lines in the tube, the section-point label, its Lipschitz constant and its invariance, in the form required by `lipschitz_displacement_le` (a label on an open subset of space, constant on field lines of B). Includes the bridge between field lines in space and solutions of the planar equation with the toroidal angle as time.
3. **Slab certificate with both signs.** Extend the position-frame Step record and `FieldBounds` by a lower bound, with limits suited to radius 10⁻³, and generate and compile the 664 slab proofs for label 0.474. Pilot first: 8 slabs per direction, to measure cost and the enclosure quality on wide balls.
4. **QA2R label theorem** on the tube, and the drift bound with explicit constants.
5. **Band statement**: a `BandSpec` with the target above, orbit existence on the horizon, and the excursion constant.

Budget: stage 3 is expected to cost of the order of the first campaign's trace work (hundreds of CPU-hours) only if wide balls do not degrade the enclosures; the pilot decides. Stop rule: if the pilot cannot certify |μ| ≤ 0.1 at ρ = 10⁻³, fall back to ρ = 3·10⁻⁴ before spending more.

## Reproduction

```bash
cd scripts/dommaschk_kam
../../.venv-ws/bin/python screen_wide_tube.py --output results/wide_tube_20261127.json
```
