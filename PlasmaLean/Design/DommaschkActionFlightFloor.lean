/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeWellAction
public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import PlasmaLean.Design.DommaschkRowFlightBudget
public import PlasmaLean.Theory.Kinetic.MirrorTimeActionBounds

/-! # Physical first-well flight-time floors from the one-way action cap -/

@[expose] public section
noncomputable section
open Set MeasureTheory

namespace PlasmaLean.Kinetic.MirrorActionEnvelope
open MirrorHeightAction

/-- A common action ceiling and a density floor convert a strict lower bound on the
angular distance between two mirrors into a strict lower bound on flight time. -/
theorem LaunchWell.time_floor_of_action_cap {f w : ℝ → ℝ} {c h l r m d C : ℝ}
    (well : LaunchWell f c h l r) (density : ContinuousOn w (Icc l r))
    (profile : ContinuousOn f (Icc l r)) (hm : 0 < m) (hd : 0 ≤ d) (hC : 0 < C)
    (floor : ∀ t ∈ Ioo l r, m ≤ w t) (width : d < r - l)
    (cap : action f w l r h ≤ C)
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * (h - f t))) volume l r) :
    (d * m) ^ 2 / C < oneWayBounceTime w f h l r := by
  let v := fun t => Real.sqrt (2 * (h - f t))
  have lr := well.left_lt.trans well.lt_right
  have wi : IntervalIntegrable w volume l r := density.intervalIntegrable_of_Icc lr.le
  have cs : ContinuousOn v (Icc l r) :=
    (continuousOn_const.mul (continuousOn_const.sub profile)).sqrt
  have ji : IntervalIntegrable (fun t => w t * v t) volume l r :=
    (density.mul cs).intervalIntegrable_of_Icc lr.le
  have vp (t) (ht : t ∈ Ioo l r) : 0 < v t :=
    Real.sqrt_pos.mpr (mul_pos (by norm_num) (sub_pos.mpr (well.accessible t ht)))
  have jp := intervalIntegral.intervalIntegral_pos_of_pos_on ji
    (fun t ht => mul_pos (hm.trans_le (floor t ht)) (vp t ht)) lr
  have tp := intervalIntegral.intervalIntegral_pos_of_pos_on finite
    (fun t ht => div_pos (hm.trans_le (floor t ht)) (vp t ht)) lr
  have csq := length_sq_le_action_mul_time lr.le (fun t ht => (hm.trans_le (floor t ht)).le)
    vp wi ji finite jp
  have low := intervalIntegral.integral_mono_on_of_le_Ioo lr.le
    (intervalIntegrable_const (c := m)) wi floor
  have dl : d * m < ∫ t in l..r, w t := by
    exact (mul_lt_mul_of_pos_right width hm).trans_le (by simpa using low)
  have ds : (d * m) ^ 2 < (∫ t in l..r, w t) ^ 2 := by
    have pos : 0 < (∫ t in l..r, w t) + d * m := by linarith [mul_nonneg hd hm.le]
    nlinarith only [mul_pos (sub_pos.mpr dl) pos]
  exact (div_lt_iff₀ hC).mpr ((ds.trans_le csq).trans_le
    ((mul_le_mul_of_nonneg_right cap tp.le).trans_eq (mul_comm _ _)))

end PlasmaLean.Kinetic.MirrorActionEnvelope

namespace PlasmaLean.Design.DommaschkActionFlightFloor
open Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign DommaschkMirrorBandPassage
open DommaschkSignedObservable DommaschkSignedTraceDomain DommaschkPhysicalActionPanel
open DommaschkMirrorTubeCrossing DommaschkNativeWellAction Kinetic.MirrorActionEnvelope
open Kinetic.MirrorHeightAction

abbrev allFloor : ℝ := 9006443340496896 / 163793158879589
abbrev upperFloor : ℝ := 9468238224162816 / 163793158879589
abbrev weight (y : ℝ → Plane) (t : ℝ) := arcDensity (y t 0) t (y t 1)

/-- The moving first mirrors bound the birth, the one-way action lies below the original
rectangle sum at every height, and its reciprocal-speed time has the stated strict floors. -/
def TimeFloor (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-(325 / 64)) (-(316 / 64)), ∃ r ∈ Ioo (316 / 64) (325 / 64),
      φ ∈ Ioo l r ∧ LaunchWell (field y) 0 h l r ∧
      action (field y) (weight y) l r h ≤ DommaschkActionArchiveMass.mass ∧
      allFloor < oneWayBounceTime (weight y) (field y) h l r ∧
      (h = level → upperFloor < oneWayBounceTime (weight y) (field y) h l r)

theorem of_passage {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ : ℝ} (path : Path n fs bs fr br x y) (reached : 325 < n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (passage : Passage φ y) (upper : FirstWellAction y) : TimeFloor φ y := by
  let W := Icc (-(325 / 64) : ℝ) (325 / 64)
  have reach : (325 : ℝ) < n := by exact_mod_cast reached
  have inside : W ⊆ Ioo (-(n : ℝ) / 64) (n / 64) := by
    intro t ht
    dsimp [W] at ht
    constructor <;> linarith [ht.1, ht.2]
  have reg (t) (ht : t ∈ W) := region t (Ioo_subset_Icc_self (inside ht))
  have cs := continuous_inputs path inside reg
  have density_eq (t) (ht : t ∈ W) : density y t = weight y t := by
    have box := reg t ht
    have den := DommaschkSignedTraceDenominator.regular t box.1 box.2
    exact arcDensity_on_path path (inside ht) (by linarith [box.1.1]) (by linarith)
  have cw : ContinuousOn (weight y) W := cs.2.congr (fun t ht => (density_eq t ht).symm)
  obtain ⟨L, hL, R, hR, top, _, _, _, padded, _⟩ := upper
  have high_eq : (height true : ℝ) = level := by norm_num [height, level]
  have paddedW : action (field y) (weight y) (-(325 / 64)) (325 / 64) level ≤
      DommaschkActionArchiveMass.mass := by
    apply le_trans (le_of_eq ?_) padded
    rw [neg_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num)] at ht
    exact congrArg (fun u => u * _) (density_eq t ht).symm
  intro h hh
  obtain ⟨l, hl, r, hr, atBirth, well, finite, _⟩ := (passage.2.2 h hh).2.2
  have lr := well.left_lt.trans well.lt_right
  have sub : Icc l r ⊆ W := Icc_subset_Icc hl.1.le hr.2.le
  have wlo (t) (ht : t ∈ W) : 7 / 8 ≤ weight y t :=
    DommaschkSignedTraceDensity.density_lower t (reg t ht)
  have level_le := hh.2.trans_eq high_eq
  have cap : action (field y) (weight y) l r h ≤ DommaschkActionArchiveMass.mass := by
    have inner := action_mono_interval hl.1.le lr.le hr.2.le cs.1 cw
      (fun t ht => (by norm_num : (0 : ℝ) ≤ 7 / 8).trans (wlo t ht)) (h := h)
    apply inner.trans (le_trans ?_ paddedW)
    have cont (H : ℝ) : ContinuousOn
        (fun t => weight y t * Real.sqrt (2 * (H - field y t))) W :=
      cw.mul ((continuousOn_const.mul (continuousOn_const.sub cs.1)).sqrt)
    apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
      ((cont h).intervalIntegrable_of_Icc (by norm_num))
      ((cont level).intervalIntegrable_of_Icc (by norm_num))
    intro t ht
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
      ((by norm_num : (0 : ℝ) ≤ 7 / 8).trans (wlo t (Ioo_subset_Icc_self ht)))
  have bound {d : ℝ} (positive : 0 ≤ d) (wide : d < r - l) :=
    well.time_floor_of_action_cap (cw.mono sub) (cs.1.mono sub)
      (by norm_num : (0 : ℝ) < 7 / 8) positive (by norm_num [DommaschkActionArchiveMass.mass])
      (fun t ht => wlo t (sub (Ioo_subset_Icc_self ht))) wide cap finite
  refine ⟨l, hl, r, hr, atBirth, well, cap, ?_, ?_⟩
  · have a := bound (d := 2 * (316 / 64)) (by norm_num) (by linarith [hl.2, hr.1])
    norm_num [allFloor, DommaschkActionArchiveMass.mass] at a ⊢
    exact a
  · intro eq
    have same := (eq ▸ well : LaunchWell (field y) 0 level l r).unique top
    have a := bound (d := 2 * (324 / 64)) (by norm_num) (by linarith [same.1, same.2, hL.2, hR.1])
    norm_num [upperFloor, DommaschkActionArchiveMass.mass] at a ⊢
    exact a

/-- The lower and upper time estimates and the action cap all concern the same
two first mirrors at each height of the chosen physical path. -/
def TimeBounds (φ : ℝ) (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Icc (height false : ℝ) (height true),
    ∃ l ∈ Ioo (-(325 / 64)) (-(316 / 64)), ∃ r ∈ Ioo (316 / 64) (325 / 64),
      φ ∈ Ioo l r ∧ LaunchWell (field y) 0 h l r ∧
      action (field y) (weight y) l r h ≤ DommaschkActionArchiveMass.mass ∧
      IntervalIntegrable (DommaschkRowFlightBudget.integrand y h) volume l r ∧
      allFloor < oneWayBounceTime (weight y) (field y) h l r ∧
      oneWayBounceTime (weight y) (field y) h l r < 264 ∧
      (h = level → upperFloor < oneWayBounceTime (weight y) (field y) h l r)

theorem join_bounds {φ : ℝ} {y : ℝ → Plane} (lo : TimeFloor φ y)
    (hi : DommaschkRowFlightBudget.WholeTime φ y) : TimeBounds φ y := by
  intro h hh
  obtain ⟨l, hl, r, hr, birth, well, cap, low, top⟩ := lo h hh
  obtain ⟨L, _, R, _, _, first, finite, _, high⟩ := hi h hh
  obtain ⟨rfl, rfl⟩ := well.unique first
  exact ⟨l, hl, r, hr, birth, well, cap, finite, low, high, top⟩

end PlasmaLean.Design.DommaschkActionFlightFloor
