/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Hardy inequality and the Suydam localized-interchange form

Energies of localized perturbations near a resonant point reduce (Suydam 1958,
Newcomb 1960) to the model radial quadratic form

  Q(ξ) = ∫ (F x² ξ'² + G ξ²) dx,

where x is the distance from the resonant point, F ≥ 0 is a shear coefficient and
G a drive coefficient. Suydam's criterion F + 4G ≥ 0 (in
this normalization) is exactly the sharp one-dimensional Hardy inequality
∫ ξ² ≤ 4 ∫ x² ξ'² for displacements vanishing at the interval endpoints.

This module proves:

* `hardy_boundary`, `hardy`: the Hardy inequality on any interval, with or without
  boundary terms;
* `suydamForm_lower_bound`, `suydamForm_nonneg`, `suydamForm_coercive`: sufficiency of
  the criterion, with an explicit L² margin (G + F/4) when it holds strictly;
* `suydamForm_logMode`, `suydam_necessary`: sharpness — if F > 0 and F + 4G < 0, an
  explicit logarithmic oscillation mode has Q < 0;
* `suydamForm_scale`: dilation invariance, so destabilizing modes exist inside every
  neighbourhood of the resonant surface.

Scope: F and G are constants and the form is the model localized form. This is the
mathematical core of the Suydam criterion, NOT a full energy-principle certificate.
The asymptotic reduction from a full energy functional of a given problem (and the
identification of the coefficients F and G) is a separate obligation.
-/
public section

noncomputable section
namespace LeanTheory.Stability
open intervalIntegral Set

/-- The model localized-interchange (Suydam) quadratic form on `[x₀, x₁]` for a
displacement `ξ` with supplied derivative `ξ'`. -/
@[expose] def suydamForm (F G x₀ x₁ : ℝ) (ξ ξ' : ℝ → ℝ) : ℝ :=
  ∫ x in x₀..x₁, (F * x ^ 2 * ξ' x ^ 2 + G * ξ x ^ 2)

/-- Regularity hypothesis: `ξ` is differentiable on `[x₀, x₁]` with continuous
derivative `ξ'` there. -/
structure C1On (ξ ξ' : ℝ → ℝ) (x₀ x₁ : ℝ) : Prop where
  deriv : ∀ x ∈ uIcc x₀ x₁, HasDerivAt ξ (ξ' x) x
  cont : ContinuousOn ξ' (uIcc x₀ x₁)

namespace C1On
variable {ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ}

/-- A `C1On` displacement is continuous on the closed interval. -/
theorem continuousOn (h : C1On ξ ξ' x₀ x₁) : ContinuousOn ξ (uIcc x₀ x₁) :=
  fun x hx => (h.deriv x hx).continuousAt.continuousWithinAt

/-- The squared displacement is integrable. -/
theorem int_sq (h : C1On ξ ξ' x₀ x₁) :
    IntervalIntegrable (fun x => ξ x ^ 2) MeasureTheory.volume x₀ x₁ :=
  (h.continuousOn.pow 2).intervalIntegrable

/-- The shear-weighted squared derivative is integrable. -/
theorem int_weighted (h : C1On ξ ξ' x₀ x₁) :
    IntervalIntegrable (fun x => x ^ 2 * ξ' x ^ 2) MeasureTheory.volume x₀ x₁ :=
  ((continuousOn_id.pow 2).mul (h.cont.pow 2)).intervalIntegrable

end C1On

/-- Integrated identity behind Hardy: `∫ (ξ² + 2xξξ') = x₁ ξ(x₁)² − x₀ ξ(x₀)²`. -/
theorem hardy_identity {ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (h : C1On ξ ξ' x₀ x₁) :
    ∫ x in x₀..x₁, (ξ x ^ 2 + 2 * x * ξ x * ξ' x) = x₁ * ξ x₁ ^ 2 - x₀ * ξ x₀ ^ 2 := by
  apply integral_eq_sub_of_hasDerivAt (f := fun x => x * ξ x ^ 2)
  · intro x hx
    have := (hasDerivAt_id' x).mul ((h.deriv x hx).pow 2)
    convert this using 1
    simp only [Pi.pow_apply]; push_cast; ring
  · exact ((h.continuousOn.pow 2).add
      (((continuousOn_const.mul continuousOn_id).mul h.continuousOn).mul h.cont)).intervalIntegrable

/-- Hardy inequality with boundary term, on any interval `x₀ ≤ x₁` (which may contain
the resonant point `0`). -/
theorem hardy_boundary {ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁) (h : C1On ξ ξ' x₀ x₁) :
    ∫ x in x₀..x₁, ξ x ^ 2 ≤
      2 * (x₁ * ξ x₁ ^ 2 - x₀ * ξ x₀ ^ 2) + 4 * ∫ x in x₀..x₁, x ^ 2 * ξ' x ^ 2 := by
  have hid := hardy_identity h
  have hA : IntervalIntegrable (fun x => ξ x ^ 2 + 2 * x * ξ x * ξ' x)
      MeasureTheory.volume x₀ x₁ :=
    ((h.continuousOn.pow 2).add
      (((continuousOn_const.mul continuousOn_id).mul h.continuousOn).mul h.cont)).intervalIntegrable
  have hB : IntervalIntegrable (fun x => ξ x ^ 2 / 2 + 2 * (x ^ 2 * ξ' x ^ 2))
      MeasureTheory.volume x₀ x₁ :=
    (h.int_sq.div_const 2).add (h.int_weighted.const_mul 2)
  have hmono : ∫ x in x₀..x₁, ξ x ^ 2 ≤
      ∫ x in x₀..x₁, ((ξ x ^ 2 + 2 * x * ξ x * ξ' x) + (ξ x ^ 2 / 2 + 2 * (x ^ 2 * ξ' x ^ 2))) := by
    apply integral_mono_on hle h.int_sq (hA.add hB)
    intro x _
    nlinarith [sq_nonneg (ξ x + 2 * x * ξ' x)]
  rw [integral_add hA hB, integral_add (h.int_sq.div_const 2) (h.int_weighted.const_mul 2),
    integral_div, integral_const_mul, hid] at hmono
  linarith

/-- The sharp Hardy inequality `∫ ξ² ≤ 4 ∫ x² ξ'²` for displacements vanishing at both
endpoints. -/
theorem hardy {ξ ξ' : ℝ → ℝ} {x₀ x₁ : ℝ} (hle : x₀ ≤ x₁) (h : C1On ξ ξ' x₀ x₁)
    (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    ∫ x in x₀..x₁, ξ x ^ 2 ≤ 4 * ∫ x in x₀..x₁, x ^ 2 * ξ' x ^ 2 := by
  have := hardy_boundary hle h
  simp only [h₀, h₁] at this
  simpa using this

/-- Hardy on `[0, a]` needs only the outer endpoint condition: the boundary weight
vanishes at the resonant surface itself. -/
theorem hardy_resonant {ξ ξ' : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) (h : C1On ξ ξ' 0 a)
    (h₁ : ξ a = 0) :
    ∫ x in (0 : ℝ)..a, ξ x ^ 2 ≤ 4 * ∫ x in (0 : ℝ)..a, x ^ 2 * ξ' x ^ 2 := by
  have := hardy_boundary ha h
  simp only [h₁] at this
  simpa using this

/-- Splitting the Suydam form into its shear and drive parts. -/
theorem suydamForm_eq {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (h : C1On ξ ξ' x₀ x₁) :
    suydamForm F G x₀ x₁ ξ ξ' =
      F * (∫ x in x₀..x₁, x ^ 2 * ξ' x ^ 2) + G * ∫ x in x₀..x₁, ξ x ^ 2 := by
  unfold suydamForm
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (h.int_weighted.const_mul F) (h.int_sq.const_mul G)]
  congr 1; funext x; ring

/-- Suydam sufficiency with margin: for nonnegative shear and endpoint-vanishing
displacements, `Q(ξ) ≥ (G + F/4) ∫ ξ²`. -/
theorem suydamForm_lower_bound {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hF : 0 ≤ F)
    (hle : x₀ ≤ x₁) (h : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    (G + F / 4) * ∫ x in x₀..x₁, ξ x ^ 2 ≤ suydamForm F G x₀ x₁ ξ ξ' := by
  rw [suydamForm_eq h]
  have := mul_le_mul_of_nonneg_left (hardy hle h h₀ h₁) hF
  nlinarith

/-- Suydam's criterion `F + 4G ≥ 0` (with `F ≥ 0`) implies nonnegativity of the
localized form for every admissible displacement. -/
theorem suydamForm_nonneg {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hF : 0 ≤ F)
    (hS : 0 ≤ F + 4 * G) (hle : x₀ ≤ x₁) (h : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0)
    (h₁ : ξ x₁ = 0) : 0 ≤ suydamForm F G x₀ x₁ ξ ξ' := by
  refine le_trans ?_ (suydamForm_lower_bound hF hle h h₀ h₁)
  exact mul_nonneg (by linarith) (integral_nonneg hle (fun x _ => sq_nonneg _))

/-- Strict Suydam criterion gives L² coercivity with constant `(F + 4G)/4`. -/
theorem suydamForm_coercive {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hF : 0 ≤ F)
    (hle : x₀ ≤ x₁) (h : C1On ξ ξ' x₀ x₁) (h₀ : ξ x₀ = 0) (h₁ : ξ x₁ = 0) :
    (F + 4 * G) / 4 * ∫ x in x₀..x₁, ξ x ^ 2 ≤ suydamForm F G x₀ x₁ ξ ξ' := by
  have := suydamForm_lower_bound (G := G) hF hle h h₀ h₁
  calc (F + 4 * G) / 4 * ∫ x in x₀..x₁, ξ x ^ 2 = (G + F / 4) * ∫ x in x₀..x₁, ξ x ^ 2 := by
        ring
    _ ≤ _ := this

/-- Sanity: a nonnegative drive `G ≥ 0` with nonnegative shear is trivially stable,
without any endpoint condition. -/
theorem suydamForm_nonneg_of_drive_nonneg {F G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hF : 0 ≤ F)
    (hG : 0 ≤ G) (hle : x₀ ≤ x₁) : 0 ≤ suydamForm F G x₀ x₁ ξ ξ' :=
  integral_nonneg hle (fun x _ => by positivity)

/-- Sanity: the zero displacement has zero energy. -/
theorem suydamForm_zero (F G x₀ x₁ : ℝ) : suydamForm F G x₀ x₁ (fun _ => 0) (fun _ => 0) = 0 := by
  simp [suydamForm]

/-- Sanity: without shear (`F = 0`) the form is the pure drive `G ∫ ξ²`. -/
theorem suydamForm_shearless {G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} :
    suydamForm 0 G x₀ x₁ ξ ξ' = G * ∫ x in x₀..x₁, ξ x ^ 2 := by
  simp [suydamForm, integral_const_mul]

/-- Sanity: without shear any negative drive is unstable, for any displacement with
positive L² mass — the shear term is the only stabilizer. -/
theorem suydamForm_shearless_neg {G x₀ x₁ : ℝ} {ξ ξ' : ℝ → ℝ} (hG : G < 0)
    (hpos : 0 < ∫ x in x₀..x₁, ξ x ^ 2) : suydamForm 0 G x₀ x₁ ξ ξ' < 0 := by
  rw [suydamForm_shearless]; exact mul_neg_of_neg_of_pos hG hpos

/-- Sanity: the form is homogeneous of degree two in the amplitude. -/
theorem suydamForm_smul (F G x₀ x₁ c : ℝ) (ξ ξ' : ℝ → ℝ) :
    suydamForm F G x₀ x₁ (fun x => c * ξ x) (fun x => c * ξ' x) =
      c ^ 2 * suydamForm F G x₀ x₁ ξ ξ' := by
  unfold suydamForm
  rw [← integral_const_mul]; congr 1; funext x; ring

/-! ## Sharpness: the logarithmic oscillation mode -/

/-- The logarithmic oscillation mode `ξ(x) = x^{-1/2} sin(k log x)`, which vanishes at
`x = 1` and `x = exp(π/k)`. -/
@[expose] def logMode (k : ℝ) (x : ℝ) : ℝ := Real.sin (k * Real.log x) / Real.sqrt x

/-- Derivative of `logMode` for `x > 0`. -/
@[expose] def logMode' (k : ℝ) (x : ℝ) : ℝ :=
  (k * Real.cos (k * Real.log x) - Real.sin (k * Real.log x) / 2) / (x * Real.sqrt x)

/-- `logMode'` is the actual derivative of `logMode` on `x > 0`. -/
theorem logMode_hasDerivAt (k : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logMode k) (logMode' k x) x := by
  have hs : HasDerivAt (fun y => Real.sin (k * Real.log y))
      (Real.cos (k * Real.log x) * (k * x⁻¹)) x :=
    ((Real.hasDerivAt_log hx.ne').const_mul k).sin
  have hr : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have hq := hs.div hr (Real.sqrt_pos.mpr hx).ne'
  unfold logMode logMode'
  convert hq using 1
  have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  field_simp
  rw [h1]; ring

/-- The logarithmic mode is `C¹` on every interval `[1, x₁]`. -/
theorem logMode_C1On {k x₁ : ℝ} (hx₁ : 1 ≤ x₁) : C1On (logMode k) (logMode' k) 1 x₁ := by
  have pos : ∀ x ∈ uIcc 1 x₁, 0 < x := fun x hx => by
    rw [uIcc_of_le hx₁] at hx; linarith [hx.1]
  refine ⟨fun x hx => logMode_hasDerivAt k (pos x hx), ?_⟩
  intro x hx
  have hx0 := pos x hx
  apply ContinuousAt.continuousWithinAt
  unfold logMode'
  have hl : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
  apply ContinuousAt.div
  · exact (continuousAt_const.mul (Real.continuous_cos.continuousAt.comp
      (continuousAt_const.mul hl))).sub
      ((Real.continuous_sin.continuousAt.comp (continuousAt_const.mul hl)).div_const 2)
  · exact continuousAt_id.mul Real.continuous_sqrt.continuousAt
  · exact (mul_pos hx0 (Real.sqrt_pos.mpr hx0)).ne'

/-- The logarithmic mode vanishes at the inner endpoint `x = 1`. -/
theorem logMode_left (k : ℝ) : logMode k 1 = 0 := by simp [logMode]

/-- The logarithmic mode vanishes at the outer endpoint `x = exp(π/k)`. -/
theorem logMode_right {k : ℝ} (hk : k ≠ 0) : logMode k (Real.exp (Real.pi / k)) = 0 := by
  simp [logMode, Real.log_exp, mul_div_cancel₀ _ hk]

/-- Exact energy of the logarithmic mode:
`Q = (π / (2k)) (F k² + F/4 + G)` on `[1, exp(π/k)]`. -/
theorem suydamForm_logMode (F G : ℝ) {k : ℝ} (hk : 0 < k) :
    suydamForm F G 1 (Real.exp (Real.pi / k)) (logMode k) (logMode' k) =
      Real.pi / (2 * k) * (F * k ^ 2 + F / 4 + G) := by
  set b := Real.exp (Real.pi / k)
  have hb : 1 ≤ b := Real.one_le_exp (div_nonneg Real.pi_pos.le hk.le)
  have pos : ∀ x ∈ uIcc 1 b, 0 < x := fun x hx => by
    rw [uIcc_of_le hb] at hx; linarith [hx.1]
  let g : ℝ → ℝ := fun u =>
    F * (k * Real.cos u - Real.sin u / 2) ^ 2 + G * Real.sin u ^ 2
  have hpt : ∀ x ∈ uIcc 1 b, F * x ^ 2 * logMode' k x ^ 2 + G * logMode k x ^ 2 =
      k⁻¹ * ((g ∘ fun y => k * Real.log y) x * (k / x)) := by
    intro x hx
    have hx0 := pos x hx
    have h1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    simp only [logMode, logMode', g, Function.comp]
    field_simp
    rw [h1]
  unfold suydamForm
  rw [integral_congr hpt, integral_const_mul]
  have hsub := integral_comp_mul_deriv (a := 1) (b := b) (g := g)
    (f := fun y => k * Real.log y) (f' := fun y => k / y)
    (fun x hx => by
      have := ((Real.hasDerivAt_log (pos x hx).ne').const_mul k)
      simpa [div_eq_mul_inv] using this)
    (fun x hx => (continuousAt_const.div continuousAt_id (pos x hx).ne').continuousWithinAt)
    (by fun_prop)
  rw [hsub]
  have hend : k * Real.log b = Real.pi := by
    simp [b, Real.log_exp, mul_div_cancel₀ _ hk.ne']
  simp only [Real.log_one, mul_zero, hend, g]
  have i1 : IntervalIntegrable (fun u => F * (k * Real.cos u - Real.sin u / 2) ^ 2)
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable; fun_prop
  have i2 : IntervalIntegrable (fun u => G * Real.sin u ^ 2) MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
  have e : (fun u => (k * Real.cos u - Real.sin u / 2) ^ 2) =
      fun u => k ^ 2 * Real.cos u ^ 2 - k * (Real.sin u * Real.cos u) + Real.sin u ^ 2 / 4 := by
    funext u; ring
  have j1 : IntervalIntegrable (fun u => k ^ 2 * Real.cos u ^ 2)
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable; fun_prop
  have j2 : IntervalIntegrable (fun u => k * (Real.sin u * Real.cos u))
      MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable; fun_prop
  have j3 : IntervalIntegrable (fun u => Real.sin u ^ 2 / 4) MeasureTheory.volume 0 Real.pi := by
    apply Continuous.intervalIntegrable; fun_prop
  rw [e, integral_add (j1.sub j2) j3, integral_sub j1 j2, integral_const_mul,
    integral_const_mul, integral_div, integral_sin_sq, integral_cos_sq, integral_sin_mul_cos₁]
  simp
  field_simp

/-- Necessity of Suydam's criterion: if the shear is positive but `F + 4G < 0`, some
admissible displacement (vanishing at both ends) has negative localized energy. -/
theorem suydam_necessary {F G : ℝ} (hF : 0 < F) (hS : F + 4 * G < 0) :
    ∃ x₁ : ℝ, 1 ≤ x₁ ∧ C1On (logMode (min 1 (-(F + 4 * G) / (8 * F))))
      (logMode' (min 1 (-(F + 4 * G) / (8 * F)))) 1 x₁ ∧
      logMode (min 1 (-(F + 4 * G) / (8 * F))) 1 = 0 ∧
      logMode (min 1 (-(F + 4 * G) / (8 * F))) x₁ = 0 ∧
      suydamForm F G 1 x₁ (logMode (min 1 (-(F + 4 * G) / (8 * F))))
        (logMode' (min 1 (-(F + 4 * G) / (8 * F)))) < 0 := by
  set k := min 1 (-(F + 4 * G) / (8 * F))
  have hr : 0 < -(F + 4 * G) / (8 * F) := div_pos (by linarith) (by linarith)
  have hk : 0 < k := lt_min one_pos hr
  have hk1 : k ≤ 1 := min_le_left _ _
  have hkr : k ≤ -(F + 4 * G) / (8 * F) := min_le_right _ _
  have hb : 1 ≤ Real.exp (Real.pi / k) := Real.one_le_exp (div_nonneg Real.pi_pos.le hk.le)
  refine ⟨Real.exp (Real.pi / k), hb, logMode_C1On hb, logMode_left k,
    logMode_right hk.ne', ?_⟩
  rw [suydamForm_logMode F G hk]
  apply mul_neg_of_pos_of_neg (div_pos Real.pi_pos (by linarith))
  have hk2 : k ^ 2 ≤ k := by nlinarith
  have : F * k ≤ -(F + 4 * G) / 8 := by
    have := mul_le_mul_of_nonneg_left hkr hF.le
    rwa [mul_div_assoc', mul_comm (8 : ℝ) F, ← div_div, mul_div_cancel_left₀ _ hF.ne'] at this
  nlinarith

/-! ## Dilation invariance: localization at the resonant surface -/

/-- Dividing by `c > 0` maps the dilated interval back to the original one. -/
theorem mem_uIcc_div {a b x c : ℝ} (hc : 0 < c) (hx : x ∈ uIcc (c * a) (c * b)) :
    x / c ∈ uIcc a b := by
  rw [mem_uIcc] at hx ⊢
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; constructor
    · rw [le_div_iff₀ hc]; linarith
    · rw [div_le_iff₀ hc]; linarith
  · right; constructor
    · rw [le_div_iff₀ hc]; linarith
    · rw [div_le_iff₀ hc]; linarith

/-- Rescaling a displacement towards the resonant surface preserves regularity. -/
theorem C1On.scale {ξ ξ' : ℝ → ℝ} {x₀ x₁ c : ℝ} (hc : 0 < c) (h : C1On ξ ξ' x₀ x₁) :
    C1On (fun x => ξ (x / c)) (fun x => ξ' (x / c) / c) (c * x₀) (c * x₁) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have := (h.deriv _ (mem_uIcc_div hc hx)).comp x ((hasDerivAt_id x).div_const c)
    convert this using 1
    · rfl
    · rw [div_eq_mul_one_div]
  · have hm : MapsTo (fun x => x / c) (uIcc (c * x₀) (c * x₁)) (uIcc x₀ x₁) :=
      fun x hx => mem_uIcc_div hc hx
    exact (h.cont.comp (continuousOn_id.div_const c) hm).div_const c

/-- The localized form is dilation covariant: compressing a mode by the factor `c`
towards the resonant surface multiplies its energy by `c > 0`, preserving its sign. -/
theorem suydamForm_scale (F G x₀ x₁ : ℝ) (ξ ξ' : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    suydamForm F G (c * x₀) (c * x₁) (fun x => ξ (x / c)) (fun x => ξ' (x / c) / c) =
      c * suydamForm F G x₀ x₁ ξ ξ' := by
  unfold suydamForm
  have e : (fun x => F * x ^ 2 * (ξ' (x / c) / c) ^ 2 + G * ξ (x / c) ^ 2) =
      fun x => (fun y => F * y ^ 2 * ξ' y ^ 2 + G * ξ y ^ 2) (x / c) := by
    funext x; field_simp
  rw [e, intervalIntegral.integral_comp_div
    (f := fun y => F * y ^ 2 * ξ' y ^ 2 + G * ξ y ^ 2) hc.ne']
  simp [mul_div_cancel_left₀ _ hc.ne']

/-- Destabilizing modes concentrate at the resonant surface: if `F > 0` and
`F + 4G < 0`, every neighbourhood `(0, ε)` contains the support of a regular
displacement, vanishing at its endpoints, with negative localized energy. -/
theorem suydam_unstable_near_resonance {F G ε : ℝ} (hF : 0 < F) (hS : F + 4 * G < 0)
    (hε : 0 < ε) : ∃ x₀ x₁ : ℝ, ∃ ξ ξ' : ℝ → ℝ, 0 < x₀ ∧ x₀ ≤ x₁ ∧ x₁ < ε ∧
      C1On ξ ξ' x₀ x₁ ∧ ξ x₀ = 0 ∧ ξ x₁ = 0 ∧ suydamForm F G x₀ x₁ ξ ξ' < 0 := by
  obtain ⟨b, hb, hC, h0, h1, hneg⟩ := suydam_necessary hF hS
  set k := min 1 (-(F + 4 * G) / (8 * F))
  set c := ε / (2 * b)
  have hb0 : 0 < b := by linarith
  have hc : 0 < c := div_pos hε (by linarith)
  refine ⟨c * 1, c * b, fun x => logMode k (x / c), fun x => logMode' k (x / c) / c,
    by simpa using hc, mul_le_mul_of_nonneg_left hb hc.le, ?_, hC.scale hc, ?_, ?_, ?_⟩
  · have : c * b = ε / 2 := by simp only [c]; field_simp
    linarith
  · simpa [div_self hc.ne'] using h0
  · simpa [mul_div_cancel_left₀ _ hc.ne'] using h1
  · rw [suydamForm_scale _ _ _ _ _ _ hc]; exact mul_neg_of_pos_of_neg hc hneg

/-- Sharpness of the Hardy constant: no constant `C < 4` works, since the borderline
choice `G = -F/4 - δ` gives a negative form for some admissible mode. Stated as: for
every `C < 4` some regular endpoint-vanishing displacement violates
`∫ ξ² ≤ C ∫ x² ξ'²`. -/
theorem hardy_sharp {C : ℝ} (hC : C < 4) : ∃ x₁ : ℝ, ∃ ξ ξ' : ℝ → ℝ, 1 ≤ x₁ ∧
    C1On ξ ξ' 1 x₁ ∧ ξ 1 = 0 ∧ ξ x₁ = 0 ∧
    C * ∫ x in (1 : ℝ)..x₁, x ^ 2 * ξ' x ^ 2 < ∫ x in (1 : ℝ)..x₁, ξ x ^ 2 := by
  rcases le_or_gt C 0 with hC0 | hC0
  · -- Any nonzero mode works when `C ≤ 0`; use `F = 1, G = -1` (so `F + 4G < 0`).
    obtain ⟨b, hb, hC1, h0, h1, hneg⟩ := suydam_necessary (F := 1) (G := -1) one_pos
      (by norm_num)
    refine ⟨b, _, _, hb, hC1, h0, h1, ?_⟩
    rw [suydamForm_eq hC1] at hneg
    have hw := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hb
      (fun x _ => by positivity :
        ∀ x ∈ Icc 1 b, 0 ≤ x ^ 2 * logMode' (min 1 (-(1 + 4 * -1) / (8 * 1))) x ^ 2)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hC0 hw]
  · -- With `F = C`, `G = -1`: `F + 4G = C - 4 < 0` gives `C ∫x²ξ'² < ∫ξ²`.
    obtain ⟨b, hb, hC1, h0, h1, hneg⟩ := suydam_necessary (F := C) (G := -1) hC0
      (by linarith)
    refine ⟨b, _, _, hb, hC1, h0, h1, ?_⟩
    rw [suydamForm_eq hC1] at hneg
    linarith

end LeanTheory.Stability
