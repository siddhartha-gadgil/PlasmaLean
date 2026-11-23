/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellCriterion
public import PlasmaLean.Theory.Contract.StellaratorContract
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Regular mirrors from a trace with a positive speed

The numerical field-line clock can be geometric toroidal angle. On a compact bracket a
positive continuous arclength speed defines an increasing change of parameter fixing zero.
Only the speed on the supplied trace enters the arclength field line.
-/

public section
noncomputable section

open Set Filter Topology
namespace PlasmaLean.Kinetic.MirrorWell

/-- A continuous positive speed on a compact interval extends to an arclength clock.
The global order isomorphism is convenient for differentiating the inverse even at the
ends of the interval. Its derivative is prescribed only on the bracket. -/
theorem exists_arclength_clock {a b : ℝ} (hab : a ≤ b) {speed : ℝ → ℝ}
    (hc : ContinuousOn speed (Icc a b)) (hp : ∀ t ∈ Icc a b, 0 < speed t) :
    ∃ s : ℝ ≃o ℝ, s 0 = 0 ∧ ∀ t ∈ Icc a b, HasDerivAt s (speed t) t := by
  let v := IccExtend hab (fun t => speed t)
  have hv : Continuous v := continuous_IccExtend_iff.2
    (continuousOn_iff_continuous_domRestrict.mp hc)
  obtain ⟨p, hpm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  have hp0 := hp p hpm
  have hlow (x : ℝ) : speed p ≤ v x := hmin (projIcc a b hab x).property
  let f := fun t => ∫ x in (0 : ℝ)..t, v x
  have hf (x : ℝ) : HasDerivAt f (v x) x := (hv.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hf0 : f 0 = 0 := by simp [f]
  have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
  have hmono := strictMono_of_deriv_pos (f := f) (fun x => (hf x).deriv ▸ hp0.trans_le (hlow x))
  have hbound {x y : ℝ} (hxy : x ≤ y) : speed p * (y-x) ≤ f y - f x :=
    mul_sub_le_image_sub_of_le_deriv hdiff (fun t => (hf t).deriv ▸ hlow t) hxy
  have hsurj : Function.Surjective f := by
    intro y
    let d := |y| / speed p
    have hd : 0 ≤ d := div_nonneg (abs_nonneg _) hp0.le
    have hmul : speed p * d = |y| := by dsimp [d]; field_simp
    have hr := hbound (x := 0) hd
    have hl := hbound (y := 0) (neg_nonpos.mpr hd)
    rw [hf0, sub_zero, sub_zero, hmul] at hr
    rw [hf0, zero_sub, zero_sub, neg_neg, hmul] at hl
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith : -d ≤ d) hdiff.continuous.continuousOn
      (show y ∈ Icc (f (-d)) (f d) from ⟨by linarith [neg_le_abs y], (le_abs_self y).trans hr⟩)
    exact ⟨t, ht⟩
  refine ⟨StrictMono.orderIsoOfSurjective f hmono hsurj, hf0, fun t ht => ?_⟩
  change HasDerivAt f (speed t) t
  simpa only [v, IccExtend_of_mem hab _ ht] using hf t

open PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Kinetic.GCLittlejohn

/-- The physical components of a cylindrical field-line trace give its positive arclength
speed R ‖B‖ / Bφ per unit geometric angle. The additive offset is the launch azimuth. -/
theorem cylindrical_trace_speed (B : Space → Space) (R z : ℝ → ℝ) (α t : ℝ)
    (hR : 0 < R t) :
    let φ := α + t
    let X := fun x => cylPoint (R x) (α+x) (z x)
    let V := B (X t)
    let Br := Real.cos φ * V 0 + Real.sin φ * V 1
    let Bφ := -Real.sin φ * V 0 + Real.cos φ * V 1
    let speed := R t * ‖V‖ / Bφ
    0 < Bφ → HasDerivAt R (R t * Br / Bφ) t → HasDerivAt z (R t * V 2 / Bφ) t →
      0 < speed ∧ V ≠ 0 ∧ HasDerivAt X (speed • bhat B (X t)) t := by
  intro φ X V Br Bφ speed hp hr hz
  have hn : V ≠ 0 := by
    intro he
    simp [Bφ, he] at hp
  have hspeed : 0 < speed := div_pos (mul_pos hR (norm_pos_iff.mpr hn)) hp
  refine ⟨hspeed, hn, ?_⟩
  have hφ : HasDerivAt (fun x : ℝ => α+x) 1 t := (hasDerivAt_id t).const_add α
  have hcart := hasDerivAt_space3 (hr.mul hφ.cos) (hr.mul hφ.sin) hz
  change HasDerivAt X (speed • (‖V‖⁻¹ • V)) t
  have hs : speed * ‖V‖⁻¹ = R t / Bφ := by
    dsimp [speed]
    field_simp [norm_ne_zero_iff.mpr hn]
  rw [smul_smul, hs]
  apply hcart.congr_deriv
  have h0 : Real.cos φ * Br - Real.sin φ * Bφ = V 0 := by
    dsimp only [Br, Bφ]
    linear_combination V 0 * Real.sin_sq_add_cos_sq φ
  have h1 : Real.sin φ * Br + Real.cos φ * Bφ = V 1 := by
    dsimp only [Br, Bφ]
    linear_combination V 1 * Real.sin_sq_add_cos_sq φ
  ext i
  fin_cases i <;> simp [PiLp.smul_apply, smul_eq_mul] <;> field_simp [hp.ne']
  · simpa [φ, sub_eq_add_neg, mul_comm] using h0
  · simpa [φ, mul_comm] using h1

/-- On a positive-strength trace one can validate the derivative of the rational squared
strength. Passing to the physical norm preserves the sign of each simple crossing. -/
theorem strength_deriv_of_squared {F : ℝ → ℝ} (hn : ∀ t, 0 ≤ F t) {t d : ℝ}
    (hpos : 0 < F t) (hd : HasDerivAt (fun x => F x ^ 2) d t) :
    HasDerivAt F (d / (2 * F t)) t := by
  simpa only [Real.sqrt_sq (hn _)] using hd.sqrt (pow_ne_zero 2 hpos.ne')

/-- Two simple, oriented mirror endpoints in a geometric clock imply a regular mirror
birth in arclength. The physical field line derivative is allowed any positive speed. -/
theorem regularMirrorBirth_of_parametrized_roots {B : Space → Space} {X : ℝ → Space}
    {speed : ℝ → ℝ} {l r h : ℝ} (hlr : l < r) (h0 : 0 ∈ Icc l r)
    (hc : ContinuousOn speed (Icc l r))
    (hline : ∀ t ∈ Icc l r, 0 < speed t ∧ B (X t) ≠ 0 ∧
      HasDerivAt X (speed t • bhat B (X t)) t)
    (hl : ‖B (X l)‖ = h) (hr : ‖B (X r)‖ = h)
    (hi : ∀ t ∈ Ioo l r, ‖B (X t)‖ < h)
    (hdl : deriv (fun t => ‖B (X t)‖) l < 0) (hdr : 0 < deriv (fun t => ‖B (X t)‖) r) :
    RegularMirrorBirth B (X 0) h := by
  obtain ⟨s, hs0, hs⟩ := exists_arclength_clock hlr.le hc (fun t ht => (hline t ht).1)
  have inv (t) (ht : t ∈ Icc l r) : HasDerivAt s.symm (speed t)⁻¹ (s t) := by
    apply HasDerivAt.of_local_left_inverse s.symm.continuous.continuousAt
    · simpa only [OrderIso.symm_apply_apply] using hs t ht
    · exact (hline t ht).1.ne'
    · exact Eventually.of_forall s.apply_symm_apply
  have hs0' : s.symm 0 = 0 := (congrArg s.symm hs0.symm).trans (s.symm_apply_apply 0)
  refine ⟨X ∘ s.symm, s l, s r, s.strictMono hlr, ?_, by simp [hs0'], ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hs0]; exact ⟨s.monotone h0.1, s.monotone h0.2⟩
  · intro u hu
    obtain ⟨t, rfl⟩ := s.surjective u
    have ht : t ∈ Icc l r := ⟨s.le_iff_le.mp hu.1, s.le_iff_le.mp hu.2⟩
    obtain ⟨hp, hn, hx⟩ := hline t ht
    simp only [Function.comp_apply, OrderIso.symm_apply_apply]
    refine ⟨hn, ?_⟩
    have hx' : HasDerivAt X (speed t • bhat B (X t)) (s.symm (s t)) := by simpa using hx
    simpa [smul_smul, hp.ne'] using hx'.scomp (s t) (inv t ht)
  · simpa using hl
  · simpa using hr
  · intro u hu
    obtain ⟨t, rfl⟩ := s.surjective u
    simpa using hi t ⟨s.lt_iff_lt.mp hu.1, s.lt_iff_lt.mp hu.2⟩
  · have rootDeriv (t) (ht : t ∈ Icc l r) (hd : deriv (fun x => ‖B (X x)‖) t ≠ 0) :
        deriv (fun x => ‖B ((X ∘ s.symm) x)‖) (s t) =
          (speed t)⁻¹ * deriv (fun x => ‖B (X x)‖) t := by
      have ht' := (differentiableAt_of_deriv_ne_zero hd).hasDerivAt
      rw [← s.symm_apply_apply t] at ht'
      simpa [Function.comp_def, mul_comm] using (ht'.comp (s t) (inv t ht)).deriv
    have hlm := left_mem_Icc.mpr hlr.le
    have hrm := right_mem_Icc.mpr hlr.le
    rw [rootDeriv l hlm hdl.ne, rootDeriv r hrm hdr.ne']
    exact ⟨mul_neg_of_pos_of_neg (inv_pos.mpr (hline l hlm).1) hdl,
      mul_pos (inv_pos.mpr (hline r hrm).1) hdr⟩

/-- A bracket and oriented crossings tested in geometric time supply the arclength
mirror birth without requiring an independently constructed arclength orbit. -/
theorem regularMirrorBirth_of_parametrized_crossings {B : Space → Space} {X : ℝ → Space}
    {speed : ℝ → ℝ} {a b h : ℝ} (ha : a < 0) (hb : 0 < b)
    (hc : ContinuousOn speed (Icc a b))
    (hline : ∀ t ∈ Icc a b, 0 < speed t ∧ B (X t) ≠ 0 ∧
      HasDerivAt X (speed t • bhat B (X t)) t)
    (hf : ContinuousOn (fun t => ‖B (X t)‖) (Icc a b))
    (hl : h < ‖B (X a)‖) (hm : ‖B (X 0)‖ < h) (hr : h < ‖B (X b)‖)
    (hneg : ∀ t ∈ Icc a 0, ‖B (X t)‖ = h → deriv (fun x => ‖B (X x)‖) t < 0)
    (hpos : ∀ t ∈ Icc 0 b, ‖B (X t)‖ = h → 0 < deriv (fun x => ‖B (X x)‖) t) :
    RegularMirrorBirth B (X 0) h := by
  obtain ⟨l, hleft, r, hright, el, er, dl, dr, inside, _⟩ :=
    two_simple_mirrors ha hb hf hl hm hr hneg hpos
  have hsub := Icc_subset_Icc hleft.1.le hright.2.le
  exact regularMirrorBirth_of_parametrized_roots (hleft.2.trans hright.1)
    ⟨hleft.2.le, hright.1.le⟩ (hc.mono hsub) (fun t ht => hline t (hsub ht))
    el er inside dl dr

end PlasmaLean.Kinetic.MirrorWell
