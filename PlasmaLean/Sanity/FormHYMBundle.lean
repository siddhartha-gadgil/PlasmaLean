/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMBundle
public import PlasmaLean.Sanity.FormPeriods
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sanity checks for the bundle data of the anti-self-dual lift (`Theory/Fields/FormHYMBundle`)

Fixture: the field of a straight wire, `B = (-y, x, 0)/(x² + y²)`, on the complement of its axis
(`wireRegion`, not simply connected), and the unit circle `loop`, around which the circulation
is `2π` (`Sanity.FormPeriods.wire_circulation`).

1. **Periods.** `wire_torusPeriod`: the period of the lift over (unit circle) `× S¹_ℓ`, with
   the orientation `(∂_s, ∂_τ)`, is `-2πℓ`; `wire_chernNumber`: the Chern number is `-ℓ`;
   `wire_chernNumber_mem_int_iff`: it is an integer exactly when `ℓ` is. Accepted value `ℓ = 1`
   (`-1`); rejected value `ℓ = 1/2` (`wire_chernNumber_half_not_int`). Trivial case: a uniform
   field has period `0` (`uniform_torusPeriod`).
2. **Transition function.** `transition_two_pi_periodic_iff`: `exp(i(lam - 2πτ))` is
   `ℓ`-periodic exactly when `ℓ` is an integer.
3. **The bundle of the wire lift.** `wireBundle`: cocycle data with two cylinder charts over
   the complements of the half-planes `{y = 0, x ≤ 0}` and `{y = 0, x ≥ 0}`, the global vector
   potential `A = -½ log(x² + y²) e_z` (`fieldCurl_wireA`) and the two branches of the angle
   (`formGrad_angle`), which differ by `0` on `{y > 0}` and by `2π` on `{y < 0}`
   (`angle_sub_mem`).
   * accepted: `wireBundle_isPeriodic`: the data are `n`-periodic for every integer `n`, and
     the transition function is not trivial (`wireBundle_trans_ne_one`);
   * both directions: `wire_exists_periodic_iff`: two-chart `ℓ`-periodic data with curvature
     the wire lift exist exactly when `ℓ ∈ ℤ`;
   * rejected: `wire_half_not_isPeriodic`: for `ℓ = 1/2` there are no periodic data at all
     (any index type);
   * rejected: `wire_not_one_chart`: for `ℓ ≠ 0` there are no one-chart periodic data, so the
     bundle is not trivial as a bundle with this curvature and a periodic connection form; on a
     star-convex region one chart suffices (`VacuumForm.exists_liftBundleData`).
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormHYMBundle

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Sanity.FormTopology PlasmaLean.Sanity.FormPeriods PlasmaLean.Contract
open TopologicalSpace Topology
open scoped RealInnerProductSpace

/-! ## Periods and Chern numbers of the wire lift -/

/-- The unit circle `t ↦ (cos 2πt, sin 2πt, 0)`, `t ∈ [0, 1]`, as a curve in space. -/
noncomputable def loop (t : ℝ) : Space := (wireLoop t : Space)

/-- The loop is `C¹`. -/
theorem contDiff_loop : ContDiff ℝ 1 loop := by
  change ContDiff ℝ 1 fun t : ℝ => unitCircle (2 * Real.pi * t)
  unfold unitCircle
  fun_prop

/-- The loop lies in the wire region. -/
theorem loop_mem (t : ℝ) : loop t ∈ wireRegion := unitCircle_mem _

/-- The loop closes up. -/
theorem loop_closed : loop 0 = loop 1 := congrArg Subtype.val wireLoop_one.symm

/-- **Period of the wire lift** over (unit circle) `× S¹_ℓ`, orientation `(∂_s, ∂_τ)`:
`-2πℓ`. -/
theorem wire_torusPeriod (ℓ : ℝ) :
    torusPeriod (hymLift (fluxField wireField)) loop 0 1 ℓ = -(2 * Real.pi * ℓ) := by
  rw [torusPeriod_hymLift_fluxField]
  have h : lineIntegral wireField loop 0 1 = 2 * Real.pi := wire_circulation
  rw [h]
  ring

/-- **Chern number of the wire lift** over (unit circle) `× S¹_ℓ`: `-ℓ`. -/
theorem wire_chernNumber (ℓ : ℝ) :
    chernNumber (hymLift (fluxField wireField)) loop 0 1 ℓ = -ℓ := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [chernNumber, wire_torusPeriod]
  field_simp

/-- **Integrality for the wire**: the Chern number is an integer exactly when `ℓ` is. -/
theorem wire_chernNumber_mem_int_iff (ℓ : ℝ) :
    (∃ n : ℤ, chernNumber (hymLift (fluxField wireField)) loop 0 1 ℓ = n) ↔ ∃ n : ℤ, ℓ = n := by
  rw [wire_chernNumber]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by push_cast; linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨-n, by push_cast; linarith⟩

/-- Accepted value: for `ℓ = 1` (the source's normalisation) the Chern number is `-1`. -/
theorem wire_chernNumber_one :
    chernNumber (hymLift (fluxField wireField)) loop 0 1 1 = -1 := wire_chernNumber 1

/-- Rejected value: for `ℓ = 1/2` the Chern number `-1/2` is not an integer. -/
theorem wire_chernNumber_half_not_int :
    ¬ ∃ n : ℤ, chernNumber (hymLift (fluxField wireField)) loop 0 1 (1 / 2) = n := by
  rw [wire_chernNumber_mem_int_iff]
  rintro ⟨n, hn⟩
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- Accepted trivial case: a uniform field has zero period over the same torus, for every
`ℓ`. -/
theorem uniform_torusPeriod (B₀ : Space) (ℓ : ℝ) :
    torusPeriod (hymLift (fluxField fun _ => B₀)) loop 0 1 ℓ = 0 := by
  rw [torusPeriod_hymLift_fluxField]
  have h : lineIntegral (fun _ => B₀) loop 0 1 = 0 := uniform_circulation B₀
  rw [h, mul_zero, neg_zero]

/-- The transition function `exp(i(lam - 2π τ))` of a potential jump `c = 2π` is `ℓ`-periodic
exactly when `ℓ` is an integer. -/
theorem transition_two_pi_periodic_iff (lam : Space → ℝ) (ℓ : ℝ) :
    (∀ (x : Space) (τ : ℝ), Circle.exp (transPotential lam (2 * Real.pi) (x, τ + ℓ)) =
        Circle.exp (transPotential lam (2 * Real.pi) (x, τ))) ↔ ∃ n : ℤ, ℓ = n := by
  rw [circleExp_transPotential_periodic_iff]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, mul_left_cancel₀ hpi hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]⟩

/-! ## The two angle branches -/

/-- The complex coordinate `x + i y` of the plane transverse to the wire. -/
noncomputable def wireZ : Space →L[ℝ] ℂ :=
  (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).smulRight (1 : ℂ) +
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).smulRight Complex.I

/-- Real part of the complex coordinate. -/
@[simp] theorem wireZ_re (x : Space) : (wireZ x).re = x 0 := by simp [wireZ]

/-- Imaginary part of the complex coordinate. -/
@[simp] theorem wireZ_im (x : Space) : (wireZ x).im = x 1 := by simp [wireZ]

/-- `|x + i y|² = r²`. -/
theorem normSq_wireZ (x : Space) : Complex.normSq (wireZ x) = wireR2 x := by
  rw [Complex.normSq_apply, wireZ_re, wireZ_im, wireR2]
  ring

/-- Derivative of a branch of the angle: for a real-linear `Z : ℝ³ → ℂ` with `Z x` off the
negative real axis, `d(arg ∘ Z)(v) = Im(Z v / Z x)`. -/
theorem hasFDerivAt_arg_comp (Z : Space →L[ℝ] ℂ) {x : Space} (hx : Z x ∈ Complex.slitPlane) :
    HasFDerivAt (fun y => Complex.arg (Z y))
      (Complex.imCLM ∘L ((Z x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) ∘L Z) x := by
  have h1 : HasFDerivAt (fun y => Complex.log (Z y)) (((Z x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) ∘L Z) x :=
    (Complex.hasStrictFDerivAt_log_real hx).hasFDerivAt.comp x Z.hasFDerivAt
  have h2 := Complex.imCLM.hasFDerivAt.comp x h1
  simpa [Function.comp_def, Complex.log_im] using h2

/-- A branch of the angle is `C¹` where it is defined. -/
theorem contDiffOn_arg_comp (Z : Space →L[ℝ] ℂ) :
    ContDiffOn ℝ 1 (fun y => Complex.arg (Z y)) {x | Z x ∈ Complex.slitPlane} := by
  intro x hx
  have h1 : ContDiffAt ℝ 1 Complex.log (Z x) := (Complex.contDiffAt_log hx).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ 1 (fun y => Complex.log (Z y)) x :=
    h1.comp x Z.contDiff.contDiffAt
  have h3 : ContDiffAt ℝ 1 (fun y => Complex.imCLM (Complex.log (Z y))) x :=
    Complex.imCLM.contDiff.contDiffAt.comp x h2
  simpa [Complex.log_im] using h3.contDiffWithinAt

/-- The chart bases: `true` is the complement of the half-plane `{y = 0, x ≤ 0}`, `false` the
complement of `{y = 0, x ≥ 0}`. -/
noncomputable def chartBase (b : Bool) : Set Space :=
  {x | (if b then wireZ else -wireZ) x ∈ Complex.slitPlane}

/-- The angle branches: `true` is `arg(x + i y) ∈ (-π, π)`, `false` is
`arg(-(x + i y)) + π ∈ (0, 2π)`. -/
noncomputable def angle (b : Bool) (x : Space) : ℝ :=
  Complex.arg ((if b then wireZ else -wireZ) x) + if b then 0 else Real.pi

/-- The chart bases are open. -/
theorem isOpen_chartBase (b : Bool) : IsOpen (chartBase b) :=
  Complex.isOpen_slitPlane.preimage (ContinuousLinearMap.continuous _)

/-- The chart bases lie in the wire region. -/
theorem chartBase_subset (b : Bool) : chartBase b ⊆ wireRegion := by
  intro x hx
  have hne : wireZ x ≠ 0 := by
    intro h0
    cases b
    · exact Complex.slitPlane_ne_zero hx (by simp [h0])
    · exact Complex.slitPlane_ne_zero hx (by simpa using h0)
  change 0 < wireR2 x
  rw [← normSq_wireZ]
  exact Complex.normSq_pos.2 hne

/-- The two chart bases cover the wire region. -/
theorem wireRegion_subset_iUnion : wireRegion ⊆ ⋃ b, chartBase b := by
  intro x hx
  have hpos : 0 < wireR2 x := hx
  rw [Set.mem_iUnion]
  by_cases h1 : x 1 = 0
  · have h0 : x 0 ≠ 0 := by
      intro h0
      simp [wireR2, h0, h1] at hpos
    rcases lt_or_gt_of_ne h0 with h | h
    · exact ⟨false, by simp [chartBase, Complex.mem_slitPlane_iff, h]⟩
    · exact ⟨true, by simp [chartBase, Complex.mem_slitPlane_iff, h]⟩
  · exact ⟨true, by simp [chartBase, Complex.mem_slitPlane_iff, h1]⟩

/-- **Each angle branch is a scalar potential of the wire field** on its chart base. -/
theorem formGrad_angle (b : Bool) {x : Space} (hx : x ∈ chartBase b) :
    formGrad (angle b) x = hodge (fluxField wireField x) := by
  have hne : wireR2 x ≠ 0 := (show 0 < wireR2 x from chartBase_subset b hx).ne'
  have hd := (hasFDerivAt_arg_comp (if b then wireZ else -wireZ) hx).add_const
    (if b then 0 else Real.pi)
  rw [fluxField_apply, hodge_flux]
  ext w
  rw [formGrad_apply, flat_apply]
  have he : angle b = fun y => Complex.arg ((if b then wireZ else -wireZ) y) +
      if b then 0 else Real.pi := rfl
  rw [he, hd.fderiv]
  obtain ⟨a0, a1, a2⟩ := rotationField_coords x
  rw [inner_coords3]
  simp only [wireField, PiLp.smul_apply, smul_eq_mul, a0, a1, a2]
  have hpos : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by simpa [wireR2] using hne
  cases b <;>
    simp only [Bool.false_eq_true, ↓reduceIte, neg_apply, inv_neg, neg_smul,
      ContinuousLinearMap.comp_neg, ContinuousLinearMap.neg_comp, ContinuousLinearMap.smul_comp,
      neg_neg, Fin.isValue, ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self,
      smul_eq_mul, Complex.imCLM_apply, Complex.mul_im, Complex.inv_re, wireZ_re, wireZ_im,
      Complex.inv_im, mul_neg, neg_mul, mul_zero, zero_mul, add_zero, normSq_wireZ] <;>
    unfold wireR2 <;> field_simp <;> ring

/-- The angle branches are `C¹` on their chart bases. -/
theorem contDiffOn_angle (b : Bool) : ContDiffOn ℝ 1 (angle b) (chartBase b) :=
  (contDiffOn_arg_comp (if b then wireZ else -wireZ)).add contDiffOn_const

/-- **The jump of the angle**: on the overlap of two chart bases the two branches differ by
`0` or `±2π`. -/
theorem angle_sub_mem (i j : Bool) {x : Space} (hx : x ∈ chartBase i ∩ chartBase j) :
    ∃ k : ℤ, angle j x - angle i x = 2 * Real.pi * k := by
  have hself : ∀ b : Bool, ∃ k : ℤ, angle b x - angle b x = 2 * Real.pi * k :=
    fun b => ⟨0, by simp⟩
  have hcross : x ∈ chartBase true → x ∈ chartBase false →
      ∃ k : ℤ, angle false x - angle true x = 2 * Real.pi * k := by
    intro ht hf
    have him : (wireZ x).im ≠ 0 := by
      simp only [chartBase, Set.mem_ofPred_eq, Complex.mem_slitPlane_iff, ite_true,
        Bool.false_eq_true, ite_false, neg_apply, Complex.neg_re, Complex.neg_im] at ht hf
      intro h0
      rcases ht with ht | ht
      · rcases hf with hf | hf
        · linarith
        · exact hf (by simp [h0])
      · exact ht h0
    simp only [angle, Bool.false_eq_true, ite_false, ite_true, neg_apply, add_zero]
    rcases lt_or_gt_of_ne him with h | h
    · exact ⟨1, by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]; push_cast; ring⟩
    · exact ⟨0, by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]; push_cast; ring⟩
  cases i <;> cases j
  · exact hself false
  · obtain ⟨k, hk⟩ := hcross hx.2 hx.1
    exact ⟨-k, by push_cast; linarith⟩
  · exact hcross hx.1 hx.2
  · exact hself true

/-! ## A global vector potential of the wire field -/

/-- The vector potential `A = -½ log(x² + y²) e_z` of the wire field. -/
noncomputable def wireA (y : Space) : Space := (-(1 / 2) * Real.log (wireR2 y)) • coordVec 2

/-- `curl A = B` for the wire field, off the axis. -/
theorem fieldCurl_wireA {x : Space} (hx : x ∈ wireRegion) :
    fieldCurl wireA x = wireField x := by
  have hne : wireR2 x ≠ 0 := (show 0 < wireR2 x from hx).ne'
  have h1 := ((Real.hasStrictDerivAt_log hne).hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_wireR2 x)).const_mul (-(1 / 2) : ℝ)
  have h2 : HasFDerivAt wireA _ x := h1.smul_const (coordVec 2)
  obtain ⟨a0, a1, a2⟩ := rotationField_coords x
  rw [fieldCurl, h2.fderiv]
  ext k
  fin_cases k <;> simp [curlOp, wireField, a0, a1, a2] <;> field_simp

/-- The 1-form `A♭` of the vector potential is `C¹` on the wire region. -/
theorem contDiffOn_flat_wireA : ContDiffOn ℝ 1 (fun y => flat (wireA y)) wireRegion := by
  have hr : ContDiff ℝ 1 wireR2 := by unfold wireR2; fun_prop
  have h1 : ContDiffOn ℝ 1 (fun y => Real.log (wireR2 y)) wireRegion :=
    (hr.contDiffOn (s := wireRegion)).log fun y hy => (show 0 < wireR2 y from hy).ne'
  have h2 : ContDiffOn ℝ 1 wireA wireRegion :=
    (contDiffOn_const.mul h1).smul contDiffOn_const
  exact flat.toContinuousLinearEquiv.contDiff.comp_contDiffOn h2

/-- `dA♭ = ω_B` for the wire field, off the axis. -/
theorem extDeriv_flat_wireA {x : Space} (hx : x ∈ wireRegion) :
    extDeriv (fun y => flat (wireA y)) x = fluxField wireField x := by
  rw [extDeriv_flat, fieldCurl_wireA hx, fluxField_apply]

/-! ## The line bundle of the wire lift as cocycle data -/

/-- **Cocycle data of the wire lift**: two cylinder charts over the complements of two
half-planes, the global vector potential `A`, the two branches of the angle as scalar
potentials, and the transition function `exp(i (φⱼ - φᵢ) τ)`, which is `1` on one component of
the overlap and `exp(±2πi τ)` on the other. -/
noncomputable def wireBundle : LiftBundleData Bool wireRegion (hymLift (fluxField wireField)) :=
  LiftBundleData.ofPotentials chartBase isOpen_chartBase wireRegion_subset_iUnion
    (fun y => flat (wireA y)) angle
    (fun b => contDiffOn_flat_wireA.mono (chartBase_subset b)) contDiffOn_angle
    (fun b _ hx => extDeriv_flat_wireA (chartBase_subset b hx)) (fun b _ hx => formGrad_angle b hx)

/-- **Accepted**: for an integer `ℓ` the cocycle data of the wire lift are `ℓ`-periodic, so they
define a `U(1)` bundle with connection of curvature `ℱ` on `Ω × S¹_ℓ`. -/
theorem wireBundle_isPeriodic (n : ℤ) : wireBundle.IsPeriodic n := by
  rw [wireBundle, LiftBundleData.ofPotentials_isPeriodic_iff]
  intro i j x hx
  obtain ⟨k, hk⟩ := angle_sub_mem i j hx
  exact ⟨k * n, by rw [hk]; push_cast; ring⟩

/-- **The transition function of the wire bundle is not trivial**: at the point `(0, -1, 0)` of
the overlap and `τ = 1/2` it is `exp(iπ) = -1`. (On the other component of the overlap it is
`1`.) -/
theorem wireBundle_trans_ne_one :
    wireBundle.trans true false (-coordVec 1, 1 / 2) ≠ 1 := by
  have hz : wireZ (-coordVec 1) = -Complex.I := by
    apply Complex.ext <;> simp
  have h1 : angle false (-coordVec 1) - angle true (-coordVec 1) = 2 * Real.pi := by
    simp only [angle, Bool.false_eq_true, ite_false, ite_true, neg_apply, hz,
      neg_neg, Complex.arg_I, Complex.arg_neg_I]
    ring
  have h2 : wireBundle.trans true false (-coordVec 1, 1 / 2) = Circle.exp Real.pi := by
    change Circle.exp ((angle false (-coordVec 1) - angle true (-coordVec 1)) * (1 / 2)) = _
    rw [h1]
    congr 1
    ring
  rw [h2]
  intro h
  have h3 := congrArg (fun c : Circle => (c : ℂ)) h
  simp only [Circle.coe_exp, Circle.coe_one] at h3
  rw [Complex.exp_pi_mul_I] at h3
  norm_num at h3

/-- **Quantisation for the wire, both directions.** Two-chart cocycle data with curvature the
wire lift that are `ℓ`-periodic exist exactly when `ℓ` is an integer. The direction `→` is the
integrality theorem `LiftBundleData.IsPeriodic.circulation_mem` (any data, any charts of
cylinder form); the direction `←` is `wireBundle`. -/
theorem wire_exists_periodic_iff (ℓ : ℝ) :
    (∃ L : LiftBundleData Bool wireRegion (hymLift (fluxField wireField)), L.IsPeriodic ℓ) ↔
      ∃ n : ℤ, ℓ = n := by
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨n, hn⟩ := hL.circulation_mem contDiff_loop zero_le_one (fun s _ => loop_mem s)
      loop_closed
    have h : lineIntegral wireField loop 0 1 = 2 * Real.pi := wire_circulation
    rw [h] at hn
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    exact ⟨n, mul_left_cancel₀ hpi (by linarith)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨wireBundle, wireBundle_isPeriodic n⟩

/-- **Rejected**: for `ℓ = 1/2` no cocycle data with curvature the wire lift, with any index
type and any cylinder charts, are `ℓ`-periodic. -/
theorem wire_half_not_isPeriodic {ι : Type*}
    (L : LiftBundleData ι wireRegion (hymLift (fluxField wireField))) :
    ¬ L.IsPeriodic (1 / 2) := by
  intro hL
  obtain ⟨n, hn⟩ := hL.circulation_mem contDiff_loop zero_le_one (fun s _ => loop_mem s)
    loop_closed
  have h : lineIntegral wireField loop 0 1 = 2 * Real.pi := wire_circulation
  rw [h] at hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2 : ((2 * n : ℤ) : ℝ) = 1 := by
    push_cast
    have : Real.pi * (2 * (n : ℝ) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hpi.ne'
    · linarith
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

/-- The Chern number of the wire bundle over (unit circle) `× S¹_n` is the integer `-n`. -/
theorem wireBundle_chernNumber (n : ℤ) :
    chernNumber (hymLift (fluxField wireField)) loop 0 1 n = ((-n : ℤ) : ℝ) := by
  rw [wire_chernNumber]
  push_cast
  rfl

/-- **The wire bundle is not trivial**: no single-chart cocycle data with a `τ`-periodic
connection have the wire lift as curvature on the whole wire region, for any `ℓ ≠ 0` — in
contrast with a star-convex region (`VacuumForm.exists_liftBundleData`). -/
theorem wire_not_one_chart {ℓ : ℝ} (hℓ : ℓ ≠ 0)
    (L : LiftBundleData Unit wireRegion (hymLift (fluxField wireField))) :
    ¬ L.IsPeriodic ℓ := by
  intro hL
  -- With one chart the period over the torus is exactly zero.
  have hbase : ∀ s, loop s ∈ L.base () := fun s => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (L.cover (loop_mem s))
    exact hi
  obtain ⟨-, hrect⟩ := hL.integral_rect contDiff_loop (i := ()) zero_le_one
    (fun s _ => hbase s)
  have hper := wire_torusPeriod ℓ
  unfold torusPeriod at hper
  rw [hrect, ← loop_closed, sub_self] at hper
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have : Real.pi * ℓ = 0 := by linarith
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hpi.ne' h0
  · exact hℓ h0

end PlasmaLean.Sanity.FormHYMBundle
