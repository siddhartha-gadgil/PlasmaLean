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
| Status | Stages 1 and 2a done. Stage 3 forward: **all 332 slabs compiled** at radius 3·10⁻⁴ and joined into one chain from slab 0 (direct `lean` compile, then rebuilt under `lake` from the repository archive at commit `880c2fe` and audited on 28 November 2026: 11,290 modules, 605,245 declarations, standard axioms only; `generated/qa2r_wide/replay-report.json`). Stage 2b: generic parts compiled on 28 November 2026 (flow label, cylindrical lift, slab-wise tube); the slab certificates are not yet connected to them. Stages 4, 5 not done. |
| Lean evidence | Stage 2a: `PlasmaLean/Theory/Fields/BackwardDistance.lean` (default build): `LowerOneSidedOn`, `lowerOneSidedOn_of_jacobian`, `norm_sub_le_exp_mul_of_lower`, `norm_sub_le_exp_sum_mul_of_lower` (chain over slabs), sharpness example `norm_exp_smul_sub_zero_eq`. Standard axioms only. Stage 3, field-independent parts (on demand, in `scripts/check_axioms_heavy.lean`): `PositionFrameWideChain.Steps.trajectory` (a chain over `PositionFrameWide.valid`, no small-radius limits) and `DommaschkJacobianLower.spatial_log_norm_lower_of_bounds`, `spatial_log_norm_abs_of_bounds` (lower and two-sided bounds from the same trace and disk data). Mean-value step (default build): `FrameJacobianVariation.abs_quad_sub_le`, `abs_quad_le_of_center`, `directional_bound_of_basis`. Field-specific second derivatives (on demand): `DommaschkJacobianSecond.secondEntry`, `entry_derivative`, `velocityHessian`, `jacobian_derivative`, `abs_quad_le_of_center`, `abs_quad_le_of_central_bounds` (forward clock only). |
| Audit evidence | Not audited. Numerics: `scripts/dommaschk_kam/screen_wide_tube.py`, `scripts/dommaschk_kam/results/wide_tube_20261127.json`. |
| Last updated | 28 November 2026 |

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

## Forward trace result, 27 November 2026 (compiled Lean)

All 332 forward slabs of the label-0.474 trace, 1/64 radian each (toroidal angle 0 to 5.1875), with frame trial radius 3·10⁻⁴ and entrance radius 2.3·10⁻⁴ at slab 0:

- **Per slab** (`DommaschkWideTubeF000` … `F331`): `abs_quadratic` and `neg_le_quadratic` (two-sided bound on the frame-reduced Jacobian on the whole trial ball), `field_bounds`, `checked`. The certified μ lies between 0.0204 and 0.0524 (largest at slab 238); the values are in `generated/qa2r_wide/certified_mu.txt`. Their integral over the trace is 0.1761, so the backward growth factor is at most e^0.1761 ≈ 1.193.
- **Joined** (`DommaschkWideTubeRows000Joined`): `steps`, `field_bounds`, and `trajectory`: every point of the entrance set launches one field line through all 332 slabs, lying in every recorded tube and ending in the exit set. Assembled from chunks of 8 slabs with `PositionFrameWideChain.Steps.append` and `fieldBoundsOn_append` (the generator's single-proof chain timed out at this length).
- **Evidence:** 11,290 generated modules compiled with `lean -DwarningAsError=true`; 664 slab theorems and the three joined theorems report standard axioms only. Cost 167 CPU-hours, at most 2.5 GB per process.
- **In the repository:** sources as `generated/qa2r_wide/WideTube.tar.zst` with `MANIFEST.sha256`; on-demand Lake library `QA2RWide`; `scripts/qa2r_wide/replay.py` (hashes, `lake build`, `scripts/check_axioms_qa2r_wide.lean`).

Same assumptions as the pilot: the reference line and frames are numerical proposals taken as data, and no theorem yet relates the entrance set to births on the tori. These are statements about field lines of the vacuum field; no particle statement follows yet.

## Stage 2b design and generic theorems, 28 November 2026

**Design.** The label is built on space-time `ℝ × Plane` (toroidal angle on the universal cover, then radius and height), not on Cartesian space. This removes the angle branch cut and the need to prove that the tube does not overlap itself after a full turn. A guiding-centre path is lifted to these coordinates by integrating its angular velocity.

**Compiled Lean (default build, standard axioms; the first two written by sub-agents, statements and axioms checked by the coordinator):**

- `Theory/Fields/FlowLabel.lean`. For x′ = F(t, x): a structure `Tube F c a b W V C M` (from the inner tube V solutions reach the section time c inside the outer tube W; solutions in W are unique, at most C times further apart at the section, and have speed at most M). Then `label` (the section point) satisfies `norm_label_sub_le` (‖Δlabel‖ ≤ C(‖Δx‖ + M|Δt|)), `label_invariant` (constant along the field (1, F)), and `displacement_le`: a path with velocity λ·(1, F) + w that stays over V moves the label by at most C(1 + M) sup‖w‖ · t. Sanity: `tube_zero`, `label_zero`.
- `Theory/Fields/CylindricalLift.lean`. `exists_lift`: a differentiable path off the z-axis has a lifted angle θ and radius R with X = cylPoint R θ z and velocity `cylVelocity` in the lifted coordinates; `norm_cylVelocity_le` (factor max(1, 1/R)).
- `Theory/Fields/PiecewiseTube.lean`. `isOpen_region_inter`: a tube given slab by slab with different gauges is open when the later slab's set lies in the earlier one's at each node.

**Still to do for the label on the QA2R tube.** (i) Backward existence on a slab and two-sided frame distance bounds from the slab certificates (in progress). (ii) Assemble `Tube` for a chain of slabs: backward radii, node jumps, the constant C = e^{Σμ/64} · max‖M⁻¹‖. (iii) Negative angles by the phase-zero reflection. (iv) The joined list of the 332 lower bounds.

**Scoping numbers for stage 4 (untrusted, `scripts/qa2r_wide/scope_label.py`).** On the trial tube: R between 0.877 and 0.9955, |z| ≤ 0.0776, |B| between 1.0438 and 1.0604, ‖∇|B|‖ ≤ 1.35, ‖∇|B|‖/|B|² ≤ 1.22, planar field-line speed ≤ 0.136, ‖M⁻¹‖ ≤ 1.86 (1.54 on the first 220 slabs). With the crude drift bound of N-215 (twice the trapped-particle value) the label moves by about 2.6 ε per R₀/v, so a section ball of radius about 2.3·10⁻⁴ holds the illustrative electron for about 13 R₀/v, about 2·10⁻⁶ s, not the 10⁻⁵ s estimated above. In that time the orbit covers at most about 2 radians of toroidal angle if the parallel speed is bounded through a certified lower bound |B| ≥ 1.04 on the tube and the pitch window, so the first 140 to 220 slabs suffice. Stage 4 therefore also needs certified bounds on |B|, ∇|B| and the planar speed on the tube; none exists yet for this field.

## Reproduction

```bash
cd scripts/dommaschk_kam
../../.venv-ws/bin/python screen_wide_tube.py --output results/wide_tube_20261127.json
cd ../.. && lake build PlasmaLean.Design.DommaschkWideTubeStep
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_trace.py
OPENBLAS_NUM_THREADS=1 .venv-ws/bin/python scripts/qa2r_wide/wide_tube_pilot.py \
  --groups 0-3 268-271 --later-radius 284/1000000 --compile --jobs 8
python3 scripts/qa2r_wide/replay.py        # the full forward trace from the repository archive
```
