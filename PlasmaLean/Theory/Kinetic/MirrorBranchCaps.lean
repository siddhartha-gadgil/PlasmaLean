/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorHeightBand
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.ProjIcc

/-! # Locating named mirror heights on an existing first-mirror branch -/

@[expose] public section
namespace PlasmaLean.Kinetic.MirrorHeightBand
open Set Filter
open scoped Topology

/-- A strictly superlevel observation at a nonnegative time puts the first root before it. -/
theorem Branch.time_lt_of_above {f : ℝ → ℝ} {a b L U k t : ℝ} (br : Branch f a b L U k)
    (h : Icc L U) (ht : 0 ≤ t) (above : (h : ℝ) < f t) : br.time h < t := by
  by_contra! before
  rcases lt_or_eq_of_le before with lt | eq
  · exact (br.before h t ⟨ht,lt⟩).not_gt above
  · rw [eq,br.hit] at above
    exact above.false

/-- A strictly sublevel observation up to the outer cap lies before the root. -/
theorem Branch.lt_time_of_below {f : ℝ → ℝ} {a b L U k t : ℝ} (br : Branch f a b L U k)
    (h : Icc L U) (ht : t ≤ b) (below : f t < h) : t < br.time h := by
  by_contra! after
  rcases lt_or_eq_of_le after with lt | eq
  · exact (br.after h t ⟨lt,ht⟩).not_gt below
  · rw [← eq,br.hit] at below
    exact below.false

/-- Extend the mirror time constantly outside its certified height band. -/
noncomputable def Branch.timeAt {f : ℝ → ℝ} {a b L U k : ℝ} (br : Branch f a b L U k)
    (ordered : L ≤ U) (h : ℝ) : ℝ := br.time (projIcc L U ordered h)

/-- At every interior height the mirror-time derivative is the reciprocal of the physical
field-strength derivative at the root. The squared-strength bound controls its size. -/
theorem Branch.timeAt_derivative {f : ℝ → ℝ} {a b L U k h : ℝ} (br : Branch f a b L U k)
    (hL : 0 ≤ L) (hk : 0 < k) (inside : h ∈ Ioo L U) :
    let order := inside.1.le.trans inside.2.le
    ∃ v > k / (2 * h), HasDerivAt f v (br.timeAt order h) ∧
      HasDerivAt (br.timeAt order) v⁻¹ h ∧ 0 < v⁻¹ ∧ v⁻¹ < 2 * h / k := by
  let order := inside.1.le.trans inside.2.le
  let x := projIcc L U order h
  have same : (x : ℝ) = h := by
    simp only [x,coe_projIcc,min_eq_right inside.2.le,max_eq_right inside.1.le]
  obtain ⟨v,hv,df⟩ := br.transverse x
  rw [same] at hv
  have positive : 0 < h := hL.trans_lt inside.1
  have lower : 0 < k / (2 * h) := by positivity
  have vpos := lower.trans hv
  have hc : Continuous (br.timeAt order) := (br.continuous_time hL hk).comp continuous_projIcc
  have inverse : ∀ᶠ z in 𝓝 h, f (br.timeAt order z) = z := by
    filter_upwards [Icc_mem_nhds inside.1 inside.2] with z hz
    simp only [timeAt,br.hit,coe_projIcc,min_eq_right hz.2,max_eq_right hz.1]
  refine ⟨v,hv,df,HasDerivAt.of_local_left_inverse hc.continuousAt df vpos.ne' inverse,
    inv_pos.mpr vpos,?_⟩
  simpa only [one_div,inv_div] using one_div_lt_one_div_of_lt lower hv

end PlasmaLean.Kinetic.MirrorHeightBand
