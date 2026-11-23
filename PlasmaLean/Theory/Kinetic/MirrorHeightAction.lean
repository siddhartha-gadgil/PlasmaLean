/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellCriterion
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Linarith

/-!
# Inversion of the longitudinal action with respect to mirror height

On a fixed field-line bracket the positive-part integrand is continuous in height, including
at a turning point. If the outside portions of the bracket are forbidden, the integral equals
the single passage between mirror points. Positivity of the arclength density at one accessible
point makes the action strictly increasing and the bracketed inverse unique.
-/

public section
noncomputable section

open Set Real MeasureTheory
namespace PlasmaLean.Kinetic.MirrorHeightAction

/-- The real square root vanishes on negative arguments. Multiplication by the arclength
density expresses the dimensionless longitudinal action in the supplied trace parameter. -/
def action (f w : ℝ → ℝ) (a b h : ℝ) : ℝ :=
  ∫ t in a..b, w t * √(2 * (h - f t))

/-- On a fixed finite bracket, the action is continuous at every height. -/
private theorem continuous_action_global {f w : ℝ → ℝ}
    (hf : Continuous f) (hw : Continuous w) (a b : ℝ) :
    Continuous (action f w a b) := by
  unfold action
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : ℝ × ℝ => w p.2 * √(2 * (p.1 - f p.2)))
  fun_prop

/-- Joint continuity of the clipped integrand gives height continuity using only the
field and density on the finite trace. -/
theorem continuous_action {f w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
    Continuous (action f w a b) := by
  let F := IccExtend hab (fun t => f t)
  let W := IccExtend hab (fun t => w t)
  have hF : Continuous F := continuous_IccExtend_iff.2
    (continuousOn_iff_continuous_domRestrict.mp hf)
  have hW : Continuous W := continuous_IccExtend_iff.2
    (continuousOn_iff_continuous_domRestrict.mp hw)
  have eqn : action F W a b = action f w a b := by
    funext h
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp only [F, W, IccExtend_of_mem hab _ ht]
  exact eqn ▸ continuous_action_global hF hW a b

/-- A single accessible point yields strict growth in height on a nontrivial bracket. -/
theorem strictMonoOn_action {f w : ℝ → ℝ} {a b h₀ : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ w t) (hc : ∃ t ∈ Icc a b, f t < h₀ ∧ 0 < w t) :
    StrictMonoOn (action f w a b) (Ici h₀) := by
  intro x hx y _ hxy
  have cont (h : ℝ) : ContinuousOn (fun t => w t * √(2 * (h - f t))) (Icc a b) :=
    hw.mul ((continuousOn_const.mul (continuousOn_const.sub hf)).sqrt)
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (cont x) (cont y)
  · intro t ht
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by linarith)) (hn t (Ioc_subset_Icc_self ht))
  · obtain ⟨t, ht, hft, hwt⟩ := hc
    refine ⟨t, ht, mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt ?_ ?_) hwt⟩
    · change h₀ ≤ x at hx
      linarith
    · linarith

/-- Equality with the integral over the accessible well when the remaining caps are forbidden. -/
theorem action_eq_between {f w : ℝ → ℝ} {a l r b h : ℝ} (hal : a ≤ l) (hlr : l ≤ r)
    (hrb : r ≤ b) (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (left : ∀ t ∈ Icc a l, h ≤ f t) (right : ∀ t ∈ Icc r b, h ≤ f t) :
    action f w a b h = action f w l r h := by
  let g := fun t => w t * √(2 * (h - f t))
  have hg : ContinuousOn g (Icc a b) :=
    hw.mul ((continuousOn_const.mul (continuousOn_const.sub hf)).sqrt)
  have integrable {p q : ℝ} (hp : a ≤ p) (hpq : p ≤ q) (hq : q ≤ b) :
      IntervalIntegrable g volume p q :=
    (hg.mono (Icc_subset_Icc hp hq)).intervalIntegrable_of_Icc hpq
  have zero {p q : ℝ} (hpq : p ≤ q) (hcap : ∀ t ∈ Icc p q, h ≤ f t) :
      (∫ t in p..q, g t) = 0 := by
    calc
      _ = ∫ _ in p..q, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hpq] at ht
        simp only [g, sqrt_eq_zero_of_nonpos (show 2 * (h - f t) ≤ 0 by linarith [hcap t ht]),
          mul_zero]
      _ = _ := by simp
  have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
    (integrable le_rfl hal (hlr.trans hrb)) (integrable hal hlr hrb)
  have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
    (integrable le_rfl (hal.trans hlr) hrb) (integrable (hal.trans hlr) hrb le_rfl)
  change (∫ t in a..b, g t) = ∫ t in l..r, g t
  linarith only [hadd₁, hadd₂, zero hal left, zero hrb right]

/-- On a bracket with oriented crossings the clipped action is the single integral
between the two actual simple mirror points, including the launch in its open interior. -/
theorem action_eq_well_of_crossings {f w : ℝ → ℝ} {a c b h : ℝ}
    (hac : a < c) (hcb : c < b) (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (ha : h < f a) (hc : f c < h) (hb : h < f b)
    (hneg : ∀ x ∈ Icc a c, f x = h → deriv f x < 0)
    (hpos : ∀ x ∈ Icc c b, f x = h → 0 < deriv f x) :
    ∃ l ∈ Ioo a c, ∃ r ∈ Ioo c b, f l = h ∧ f r = h ∧ deriv f l < 0 ∧ 0 < deriv f r ∧
      (∀ x ∈ Ioo l r, f x < h) ∧ action f w a b h = action f w l r h := by
  obtain ⟨l, hl, r, hr, el, er, dl, dr, hin, hleft, hright⟩ :=
    MirrorWell.two_simple_mirrors_with_caps hac hcb hf ha hc hb hneg hpos
  refine ⟨l, hl, r, hr, el, er, dl, dr, hin,
    action_eq_between hl.1.le (hl.2.trans hr.1).le hr.2.le hf hw ?_ ?_⟩
  · intro t ht
    rcases ht.2.lt_or_eq with hn | rfl
    · exact (hleft t ⟨ht.1, hn⟩).le
    · exact el.ge
  · intro t ht
    rcases ht.1.lt_or_eq with hn | rfl
    · exact (hright t ⟨hn, ht.2⟩).le
    · exact er.ge

/-- A target strictly between the two endpoint actions selects a unique height in the
open height interval. This is pointwise in the launch, so the same bounds work for a cell. -/
theorem unique_height {f w : ℝ → ℝ} {a b low high j : ℝ} (hab : a < b) (hh : low ≤ high)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hn : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hc : ∃ t ∈ Icc a b, f t < low ∧ 0 < w t)
    (hlo : action f w a b low < j) (hhi : j < action f w a b high) :
    ∃! h, h ∈ Ioo low high ∧ action f w a b h = j := by
  have mono := strictMonoOn_action hab hf hw hn hc
  obtain ⟨h, hm, he⟩ := intermediate_value_Icc hh (continuous_action hab.le hf hw).continuousOn
    (show j ∈ Icc _ _ from ⟨hlo.le, hhi.le⟩)
  have hl : low < h := hm.1.lt_of_ne (fun eq => hlo.ne (eq ▸ he))
  have hr : h < high := hm.2.lt_of_ne (fun eq => hhi.ne ((eq ▸ he).symm))
  exact ⟨h, ⟨⟨hl, hr⟩, he⟩, fun x hx => mono.injOn hx.1.1.le hm.1 (hx.2.trans he.symm)⟩

end PlasmaLean.Kinetic.MirrorHeightAction
