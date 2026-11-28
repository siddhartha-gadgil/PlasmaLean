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
| Status | Stages 1 and 2a done. Stage 3 forward: **all 332 slabs compiled** at radius 3·10⁻⁴ and joined into one chain from slab 0 (direct `lean` compile, then rebuilt under `lake` from the repository archive at commit `880c2fe` and audited on 28 November 2026: 11,290 modules, 605,245 declarations, standard axioms only; `generated/qa2r_wide/replay-report.json`). Stage 2b: compiled on 28 November 2026 up to the two-sided tube structure for QA2R on toroidal angles (−3.5, 3.5) (`DommaschkWideTubeRows000Tube.tube`, `isOpen_region`), Stage 4: done on 28 November 2026 (`DommaschkWideTubeRows000Orbit.stays_in_tube`: a QA2R guiding centre born in the tube stays there and its label moves at most κt, for about 1.5·10⁻⁶ s at the illustrative electron scale). Stage 5: a formal `BandContract` instance was proved on 28 November 2026 with recorded caveats (support defined through the reference, envelope-size excursion, horizon about 10⁻⁶ s). |
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

**Slab certificates connected, 28 November 2026 (compiled Lean, standard axioms; written by sub-agents and generated scripts, statements and axioms checked by the coordinator).**

- `Theory/Fields/MovingFrameBackward.lean`, `Certificates/PositionFrameBackward.lean`: backward existence on a slab by time reversal of the forward step (`backward_step`) and the two-sided frame distance bound (`frame_dist_le`).
- `Certificates/PositionFrameTube.lean`, `PositionFrameHalfTube.lean`: for a chain of slabs with lower bounds and backward radii, `reach`, `dist_chain`, `eq_of_eq`, `inner_relOpen`, and the one-sided structure `halfTube` with constant ‖M(0)‖ · e^{Σ max(0, μ)/64} · max(op/detLower).
- `Theory/Fields/FlowLabelSymmetric.lean`: `HalfTube.double` (a one-sided tube and a reflection conjugating the field to its time reversal give a two-sided `Tube`), `isOpen_region_double`. `Design/DommaschkTubeSymmetry.lean`: the reflection identity `flow_symm` for the QA2R planar equation.
- `Design/DommaschkTubeCheck.lean`: executable checks `radiiCheck` (backward radii) and `trialPacked` (trial tube inside the cylindrical envelope `Region`), with soundness.
- Generated library: `DommaschkWideTubeRows000Lower.lower` (the 332 lower bounds as one list statement) and `DommaschkWideTubeRows000Tube` for the **first 224 slabs** (toroidal angle 0 to 3.5): `halfTube`, `tube`, `isOpen_region`. The label constant is `labelConstant = e^{223/2000} · 1741/1000`, about 1.95. The inner tube has frame radius 3.0·10⁻⁴ at the section and 2.68·10⁻⁴ at the end. The envelope check fails on the full 332 slabs (the tube comes within 2·10⁻³ of the envelope's edge), so 224 slabs are used.

**Hypothesis still open in these theorems:** a bound M for the planar field-line speed on `Region`. Negative angles come from the reflection; no backward compile is needed.

## Stage 4 parts, 28 November 2026 (compiled Lean, standard axioms; sub-agents, checked by the coordinator)

- **Field bounds on the envelope** (`Design/DommaschkRegionFieldBounds.lean`, on demand; 24 generated row modules with 2,175 box checks, about 7 CPU-hours): for every point of `Region` and every toroidal angle, planar field-line speed ≤ 9/25 (`planar_speed_le`), 47/50 ≤ |B| ≤ 141/100 (`strength_ge`, `strength_le`), 47/50 ≤ B_φ ≤ 13/10. `DommaschkRegionRegularity.vacuum_at` (C², nonzero, curl-free, divergence-free) and `contDiffAt_spaceTime_region`. The speed bound discharges the hypothesis of `tube`; this is not yet wired into the generated module.
- **Gradient of |B|: not available on the envelope.** The numerical supremum of ‖∇|B|‖ on `Region` is about 5.3 (1.35 on the tube), so the bound must be certified on the tube, slab by slab. In progress.
- **Continuation** (`Theory/Fields/FlowLabelStay.lean`, default build): `stays`, `stays_core`: a path whose label stays in a section set and whose time stays in a window does not leave the region.
- **Forward core** (`Certificates/PositionFrameCore.lean`): `eq_of_eq_forward`, `core_subset_inner`, `mem_core_of_label`, `isClosed_coreD_window`, `coreD_subset`. The margin between the recorded forward tube and the inner tube is at least 1.1·10⁻⁵ on the 224 slabs (float check; the Lean `marginCheck` is not yet run on the records). A statement first requested, closedness of the mirrored core with an intersection at the section, is false in general; the union version is used, with a section condition that still needs a lemma for a start point slightly off the midplane (height 5079·2⁻⁸⁰).
- **Guiding-centre lift** (`Theory/Kinetic/CylindricalDrift.lean`, default build; `Design/DommaschkCylindricalDrift.lean`): `exists_lift_decomp`: a Littlejohn orbit that stays off the axis where B ≠ 0 has a lifted path X with (z τ).1 = cylPoint X, and while X is over `Region` its velocity is rate · (1, field-line equation) + perturbation with ‖perturbation‖ ≤ max(1, 1/R) · 2H/(|q||B|²) · ‖∇|B|‖; `hamiltonian_eq_birth` (energy conservation on an interval). Sanity instance with the toroidal field in `Sanity/CylindricalDrift.lean`.

## Stage 4 result, 28 November 2026 (compiled Lean, standard axioms)

**`DommaschkWideTubeRows000Orbit.stays_in_tube`** (generated library; proved generically as `Design/DommaschkTubeDrift.stays_in_tube`). Let z be a Littlejohn orbit of the QA2R field on [0, T] with m > 0, q ≠ 0, μ ≥ 0, born at `cylPoint R₀ θ₀ z₀` with (θ₀, (R₀, z₀)) over the inner tube and its field-line label within r of the reference point. Suppose

- κ ≥ `labelConstant` · (1 + 9/25) · (8/7) · 2H/(|q| · 1.039²) · 11/8, that is κ ≥ 3.86 · 2H/|q| (H the birth energy);
- r + κT + 2·5079·2⁻⁸⁰ ≤ entrance radius (2.3·10⁻⁴);
- m·vpar² ≥ 2(H − μ·1.039), vpar ≥ 0, and |θ₀| + (vpar/1.039 · (13/10)/(7/8) + κ/(1.36·`labelConstant`))·T ≤ b′ < 3.5.

Then there is a lifted path X with X(0) the birth point and, for all t in [0, T]: the guiding centre is `cylPoint` of X(t); X(t) is over the inner tube and in the recorded forward tube or its mirror image; |θ(t)| ≤ b′; and the label has moved at most κt. The a-priori regularity (off the axis, B ≠ 0) is derived by a bootstrap, not assumed. Nothing is assumed about the field beyond the certificates.

Certified inputs added for this (sub-agents; checked by the coordinator): on the two-sided trial tube ‖∇|B|‖ ≤ 11/8, |B| ≥ 1039/1000, planar speed ≤ 7/50 (`DommaschkWideTubeRows000Field.bounds`; exact identity `DommaschkGradientBridge.gradAbsB_sq`; 253 box checks in 28 generated modules, about 3 CPU-hours, 12 GB per check); the kernel checks `margin_checked`, `section_checked` on the 224 records. The theorem uses the envelope speed bound 9/25, not the tube-local 7/50.

**Size of the statement (arithmetic on the certified constants, not a Lean theorem).** In the units of N-214, 2H/|q| = ε·v, so κ ≈ 3.86 ε per R₀/v. For the illustrative electron (ε = 6.7·10⁻⁶) a birth with r small has T up to about 8.9 R₀/v, about 1.5·10⁻⁶ s at R₀ = 10 m. The angle condition needs the pitch: with the mirror height 1.0601 of the top band, vpar ≈ 0.14 v and the angle covered is about 1.9 radians, inside the window; without pitch information (vpar = v) it fails. The horizon is about a fifteenth of a half bounce. The constant is about six times the true drift rate of N-215 (0.617 ε): factors 1.95 (label), 1.36 (time direction), 8/7 (1/R), and 2 (energy bound for the drift of a trapped particle).

**Orbit existence, 28 November 2026.** `DommaschkWideTubeRows000Orbit.exists_orbit_stays_in_tube` (generic form `Design/DommaschkTubeOrbit.exists_orbit_stays_in_tube`): under the same side conditions, without assuming an orbit, a Littlejohn orbit exists on [0, T] and has the properties above. Proof: the existing forward continuation theorem `ODEGlobal.exists_forward_of_apriori` in the open set of regular states, with the compact set (tube window) × [−vpar, vpar]; the a-priori bound is `stays_in_tube` on each partial orbit plus energy conservation. No hypothesis was added. `stays_in_tube` itself still covers every orbit, so no uniqueness is needed. Replay and audit passed at `6190258` (11,322 modules, standard axioms).

**Not proved:** any statement about a population; anything beyond 1.5·10⁻⁶ s; the regular-mirror property of these births. The reference line and frames remain numerical proposals, but the theorem does not depend on their accuracy beyond what the certificates check.

## Tightened constants, 28 November 2026 (compiled Lean, standard axioms; supersedes the constants stated in the stage 4 section above)

The orbit theorem and the band instance were restated with three sharper inputs, all already certified (sub-agent; build, forbidden constructs and audit checked by the coordinator; replay passed at `49f0629`):

- the tube-local planar speed 7/50 in place of the envelope bound 9/25;
- the drift bounded by (2H − μ·1.039)/(|q|·1.039²)·‖∇|B|‖ in place of 2H/(|q|·1.039²)·‖∇|B|‖ (`DommaschkCylindricalDrift.norm_drift_le_strength`; the drift carries m v∥² + μ|B| = 2H − μ|B|);
- the tube-local B_φ ≤ 21/20 in the angular rate, giving the factor (21/20)/(7/8) = 6/5 in place of (13/10)/(7/8).

New side conditions of `stays_in_tube` and `exists_orbit_stays_in_tube`: κ ≥ `labelConstant`·(1 + 7/50)·(8/7)·((2H − μ·1.039)/(|q|·1.039²))·(11/8), and the angle condition with vpar/1.039·(6/5) and the same drift term. The label budget, the parallel-speed condition and the conclusions are unchanged.

**Size (arithmetic on the certified constants, not a Lean theorem).** κ ≈ 3.29·H/|q| for a top-band particle (μ = H/1.0601), against 7.71·H/|q| before: a factor 2.3. At ε = 6.7·10⁻⁶ the label budget allows about 20.8 R₀/v and the angle window about 21.5 R₀/v, so the horizon is about 20.8 R₀/v, about 3.5·10⁻⁶ s at R₀ = 10 m, about a sixth of a half bounce (before: 8.9 R₀/v).

**Band instance.** The pitch window is now μ/E > 47/50 (the top band has 1/h ≈ 0.9433), and `kappa`, `Inputs` use the new formulas with the factor (2 − (47/50)·1.039)·e₂. `inputs_example` now has horizon 30 (before 10) at m = q = 1, e₂ = 10⁻⁶. The caveats of stage 5 are unchanged, and the instance still fails the acceptance rule of N-213.

## Stage 5: a formal band-form instance, 28 November 2026 (compiled Lean, standard axioms)

Done at the user's request, with the caveats below. Generic part `Design/DommaschkTubeBand.lean` (on demand); instance `DommaschkWideTubeRows000Band` in the generated library (it also imports `CommonLittlejohnCache` of `QA2RGenerated` for the regular mirror births). Written by a sub-agent; statements, axioms and the build checked by the coordinator. Replay and audit passed at `3153d3b` (11,323 modules).

**`band_contract`.** For inputs satisfying `Inputs m q e₂ T vp` and any birth law ν that is absolutely continuous, finite and nonzero on the support, `BandContract (spec m q ν e₁ e₂ T) B` holds for the QA2R field, where the specification is:

| Input | Value |
| --- | --- |
| Species | m > 0, q ≠ 0, symbolic |
| Energy window | the open interval (e₁, e₂) |
| Pitch window | μ/E > 47/50 (9/10 before the tightening) |
| Axis | the circle R = 15/16, z = 0 |
| Horizon | T > 0 |
| Excursion | 1/8 |
| Required fraction | 1 |
| Support | the interior of the trapped reference population among the "good" births: position within toroidal angle 1/4 of the section and over the inner tube, label within 10⁻⁴ of the reference point, 0 < E < e₂, μ > 0.94 E |

`Inputs` consists of three inequalities between the inputs: κ·T ≤ 10⁻⁴ with κ = `labelConstant`·1.36·(8/7)·(2e₂/(|q|·1.039²))·(11/8); m·vp² ≥ 2e₂(1 − 0.9·1.039); and (vp/1.039·(13/10)/(7/8) + κ/(1.36·`labelConstant`))·T ≤ 3.

Further theorems: `exists_seed` (the lifts of the original launch point, at every energy of the window, every height of the top mirror band and both signs, lie in the support; that point is within 5·10⁻⁵ of the tube's start point, `launch_near`), `band_contract_restrict` (a concrete birth law: volume restricted to a unit ball around a support point), `inputs_example` and `band_contract_example` (the inputs are satisfiable: m = q = 1, e₂ = 10⁻⁶, T = 10 in model units).

**Caveats.**

1. **The support is defined through the reference population.** It is the interior of the set of trapped births that are good, so every support point is in the reference and the fraction 1 holds by construction. The specification does not fix a support in elementary terms before the proof; this is the weakness named in audit finding AW-H3, addressed only in part. What is explicit: the support is open, nonempty, and contains the stated seed births.
2. **The excursion 1/8 is the size of the envelope cross-section** around the circle R = 15/16, not a tube-scale bound. It says the guiding centre stays over the envelope. The sharper content is the label statement of stage 4, which is not expressible in the band form.
3. **The horizon is short.** κT ≤ 10⁻⁴ gives T ≤ about 13 in the example's units; at the illustrative electron scale this is about a tenth of a half bounce, of the order of 10⁻⁶ s. A family of such statements does not give a band claim on a transport time scale.
4. **Model units.** Lengths are in R₀ and the field in the model normalization; no SI device scale is fixed, although `BandSpec` documents SI.
5. **Model.** Static Littlejohn guiding-centre equations in the vacuum field; no collisions, no electric field, no derivation from the Lorentz force.
6. **A second library.** A cold replay of the band module needs the sources of `generated/qa2r/` as well.

**Status of clause C2.** A formal `BandContract` instance for the actual field now exists. Because of caveats 1 to 3 it should not be read as establishing confinement of a trapped population; the research target of C2 (a predeclared population, a horizon of many bounces, a tube-scale excursion) remains open.

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
