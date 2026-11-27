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
| Status | Stages 1 and 2a done. Stage 3: Lean theory complete; **pilot passed** on 8 forward slabs (0–3, 268–271) at radius 3·10⁻⁴: two-sided Jacobian bound on the whole ball and full `FieldBounds`, compiled by Lean. Full forward trace (332 slabs) running. Backward direction, the connected chain from a real entrance set, stages 2b, 4, 5 not done. |
| Lean evidence | Stage 2a: `PlasmaLean/Theory/Fields/BackwardDistance.lean` (default build): `LowerOneSidedOn`, `lowerOneSidedOn_of_jacobian`, `norm_sub_le_exp_mul_of_lower`, `norm_sub_le_exp_sum_mul_of_lower` (chain over slabs), sharpness example `norm_exp_smul_sub_zero_eq`. Standard axioms only. Stage 3, field-independent parts (on demand, in `scripts/check_axioms_heavy.lean`): `PositionFrameWideChain.Steps.trajectory` (a chain over `PositionFrameWide.valid`, no small-radius limits) and `DommaschkJacobianLower.spatial_log_norm_lower_of_bounds`, `spatial_log_norm_abs_of_bounds` (lower and two-sided bounds from the same trace and disk data). Mean-value step (default build): `FrameJacobianVariation.abs_quad_sub_le`, `abs_quad_le_of_center`, `directional_bound_of_basis`. Field-specific second derivatives (on demand): `DommaschkJacobianSecond.secondEntry`, `entry_derivative`, `velocityHessian`, `jacobian_derivative`, `abs_quad_le_of_center`, `abs_quad_le_of_central_bounds` (forward clock only). |
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

## Stage 3 scoping, 27 November 2026 (rigorous-style Python intervals; no Lean compiled)

Scripts and data: `scripts/qa2r_wide/enclosure_pilot.py`, `scripts/qa2r_wide/sweep_forward_20261127.json` (all 332 forward slabs of the label-0.474 trace, exact rational intervals around float-proposed references and frames). Done by a sub-agent; the coordinator checked the cited Lean declarations and reran one slab.

- **Correction to the stage 1 table.** The screen used the exact variational frame. The certificate format interpolates the frame affinely on each slab, which adds a term of about 0.02–0.04 to μ at any radius. The quantity a certificate must bound is therefore larger: float samples give at most 0.046 at ρ = 3·10⁻⁴ and 0.065 at 10⁻³ (not 0.010 and 0.034), and the growth over the half well is about 1.19 and 1.43 (not 1.02 and 1.08).
- **The existing enclosure does not scale.** It puts the whole ball in the remainder of a Taylor model in time, monomial by monomial. At ρ = 10⁻³ it certifies |μ| up to 2.6 (mean 1.0); at 3·10⁻⁴ up to 0.74.
- **A mean-value form works.** Bound the Jacobian on the central line as now, and add ρ times an interval bound on its spatial derivative over the tube. Result: |μ| ≤ 0.051 at ρ = 3·10⁻⁴ on every slab (integral 0.175 over the half well); at 10⁻³ it reaches 0.123, or 0.102 with a 2×2 split of the box.
- **The lower bound is free.** The existing proof (`symmetric_bounds` in the generated Bounds modules) already has a two-sided trace bound and discards the lower half; `DommaschkJacobian.quadratic_le_of_trace` applied to the negated entries gives the lower bound with the same data.
- **Radius limits.** `PositionFrameSlabs.growth` hard-codes a trial radius below 10⁻⁵ and the `Limits`; `Certificates/PositionFrameWide.lean` already drops them, but there is no generic chain over `PositionFrameWide.valid`.
- **Inputs.** A label-0.474 trace needs only repository inputs (the candidate, the torus seeds, the committed field data and harmonic blocks); no `/tmp` packet.
- **Cost estimate (extrapolated from receipts, unverified):** about 70 CPU-seconds per slab if grouped by 12 as in N-152, about 7 CPU-hours for 332 slabs; the backward direction by the phase-zero reflection.

**Decision by the stop rule:** ρ = 3·10⁻⁴ (physical tube radius about 5.6·10⁻⁴ to 7·10⁻⁴). With a label constant near 1.86 × 1.19 ≈ 2.2, the direct bound keeps the illustrative electron inside for about 60 R₀/v, roughly a quarter of a bounce period (about 10⁻⁵ s), not a full one. The radius 10⁻³ needs a finer split or a second-order form and is deferred.

**New Lean theory needed before the pilot** (field-independent first): a chain over `PositionFrameWide.valid`; the lower-bound corollary of `quadratic_le_of_trace`; a perturbation lemma (a two-sided central bound plus a bound on the directional derivative of the Jacobian on a convex tube gives two-sided bounds on the tube); derivative lemmas for the quotient-rule entries with second derivatives. The last two are the main risk: their formulas were only checked numerically.

## Pilot result, 27 November 2026 (compiled Lean; generated modules in the workstation cache)

Generator `scripts/qa2r_wide/wide_tube_pilot.py` (reference line and frames proposed by `wide_trace.py`, untrusted; every emitted bound validated in exact arithmetic, then checked by Lean). Hand-written support, on demand, standard axioms: `Design/DommaschkWideTubeHessian.lean` (`dU_dZ`, `directional_bounds`) and `Design/DommaschkWideTubeStep.lean` (`abs_quadratic`, `neg_le_quadratic`, `field_bounds`). Done by a sub-agent; the coordinator rebuilt the hand-written modules, re-ran the axiom check on a generated slab and both chains, and read the statements.

For each of the 8 pilot slabs Lean proves, on the closed slab and the whole trial ball of frame radius 3·10⁻⁴: `abs_quadratic` (|⟪w, Ã w⟫| ≤ μ‖w‖²), `neg_le_quadratic`, `field_bounds` (the full `FieldBounds`) and `physical_step`; and for each group of four a chain with `trajectory`.

| Slabs | Certified μ (two-sided) | Central part | Prototype prediction |
| --- | --- | --- | --- |
| 0–3 | 0.0249 – 0.0258 | 0.0197 – 0.0202 | 0.0250 – 0.0259 |
| 268–271 | 0.0368 – 0.0375 | 0.0196 – 0.0206 | 0.0388 – 0.0396 |

Measured cost: 276 generated modules, 3.05 CPU-hours, about 23 CPU-minutes per slab, at most 2.5 GB per process. The earlier estimate of 70 CPU-seconds per slab assumed grouped Horner enclosures, which are not implemented for the second derivatives; 98 % of the cost is the sparse monomial enclosures. The full forward trace therefore costs about 127 CPU-hours as is.

Assumptions of the pilot (not proved): the reference line and frames are float proposals taken as given integers; the group 268–271 starts from an assumed entrance radius, so the two groups are not connected; no birth-set theorem is attached to the entrance of slab 0. The lower bound is proved per slab but not yet fed into `BackwardDistance`.

## Reproduction

```bash
cd scripts/dommaschk_kam
../../.venv-ws/bin/python screen_wide_tube.py --output results/wide_tube_20261127.json
cd ../.. && lake build PlasmaLean.Design.DommaschkWideTubeStep
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_trace.py
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_tube_pilot.py \
  --groups 0-3 268-271 --later-radius 284/1000000 --compile --jobs 8
```
