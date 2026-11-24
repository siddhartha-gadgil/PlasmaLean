/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkNativeActionColumns
public import PlasmaLean.Design.DommaschkNativeActionGeometry

/-! # Comparing physical field strength and arclength at two radial labels -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedActionProfiles
open Certificates.TrajectoryTaylorModel Certificates.PositionFrameSlabs DommaschkBounceField
open DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkMirrorEndpointSign

abbrev weight (φ : ℝ) (x : Plane) := arcDensity (x 0) φ (x 1)

/-- Two physical field-line observables at the same toroidal angle. -/
def Compared (φ : ℝ) (i o : Plane) : Prop :=
  strength φ i ≤ 17 / 16 ∧ strength φ o ≤ 17 / 16 ∧
  strength φ o ≤ strength φ i - 1 / 18000 ∧ 3999 / 4000 * weight φ i ≤ weight φ o

/-- Enclose a time model on the whole normalized interval in a rational interval. -/
theorem range {m : Model} {s x : ℝ} {lo hi : ℚ} (hs : |s| ≤ 1) (hx : m.Mem s x)
    (check : m.radius + magnitude (difference m.poly [(lo + hi) / 2]) ≤ (hi - lo) / 2) :
    (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ) := by
  have h := abs_le.mp (enclose (c := ⟨[(lo + hi) / 2], (hi - lo) / 2⟩) hs hx check)
  simp only [Certificates.QPoly.eval_cons, Certificates.QPoly.eval_nil, mul_zero,
    add_zero, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat] at h
  constructor <;> linarith only [h.1, h.2]

theorem weight_eq {x : Plane} {φ : ℝ} (hr : 0 < x 0)
    (hd : 0 < atPoint DommaschkKam.dD (x 0) φ (x 1)) :
    weight φ x = (x 0) ^ 8 * strength φ x / atPoint DommaschkKam.dD (x 0) φ (x 1) := by
  rw [(field_id hr φ (x 1)).1]
  unfold weight arcDensity strength
  field_simp [hr.ne', (toroidal_pos_of_den hr hd).ne']

/-- Direct bounds on a nonnegative field from its positive compensated numerator. -/
theorem field_range {f h p pl pu nl nu a b : ℝ} (hf : 0 ≤ f)
    (hp : pl ≤ p ∧ p ≤ pu) (n : nl ≤ p * (h ^ 2 - f ^ 2) ∧ p * (h ^ 2 - f ^ 2) ≤ nu)
    (positive : 0 < pl) (below : 0 ≤ h ^ 2 - b ^ 2) (ab : a ≤ b) (apos : 0 ≤ a)
    (low : nu ≤ pl * (h ^ 2 - a ^ 2)) (high : pu * (h ^ 2 - b ^ 2) ≤ nl) : a ≤ f ∧ f ≤ b := by
  have ppos := positive.trans_le hp.1
  have ar := below.trans (sub_le_sub_left (pow_le_pow_left₀ apos ab 2) _)
  have l := (n.2.trans low).trans (mul_le_mul_of_nonneg_right hp.1 ar)
  have u := ((mul_le_mul_of_nonneg_right hp.2 below).trans high).trans n.1
  have l' := le_of_mul_le_mul_left l ppos
  have u' := le_of_mul_le_mul_left u ppos
  exact ⟨le_of_sq_le_sq (by linarith only [l']) hf,
    le_of_sq_le_sq (by linarith only [u']) (apos.trans ab)⟩

/-- Direct arclength bounds through the identity (u=(D w) ^ 2). -/
theorem weight_range {D w dl du ul uu a b : ℝ} (hw : 0 ≤ w)
    (hd : dl ≤ D ∧ D ≤ du) (hu : ul ≤ (D * w) ^ 2 ∧ (D * w) ^ 2 ≤ uu)
    (positive : 0 < dl) (apos : 0 ≤ a) (bpos : 0 ≤ b)
    (low : (du * a) ^ 2 ≤ ul) (high : uu ≤ (dl * b) ^ 2) : a ≤ w ∧ w ≤ b := by
  have dpos := positive.trans_le hd.1
  have l := le_of_sq_le_sq (low.trans hu.1) (mul_nonneg dpos.le hw)
  have u := le_of_sq_le_sq (hu.2.trans high) (mul_nonneg positive.le bpos)
  exact ⟨le_of_mul_le_mul_left ((mul_le_mul_of_nonneg_right hd.2 apos).trans l) dpos,
    le_of_mul_le_mul_left (u.trans (mul_le_mul_of_nonneg_right hd.1 bpos)) dpos⟩

structure Bounds where
  fieldLo : ℚ
  fieldHi : ℚ
  weightLo : ℚ
  weightHi : ℚ

def Bounds.At (v : Bounds) (φ : ℝ) (x : Plane) : Prop :=
  ((v.fieldLo : ℝ) ≤ strength φ x ∧ strength φ x ≤ v.fieldHi) ∧
  ((v.weightLo : ℝ) ≤ weight φ x ∧ weight φ x ≤ v.weightHi)

theorem compare_ranges {a b : Bounds} {φ : ℝ} {x y : Plane}
    (ha : a.At φ x) (hb : b.At φ y)
    (hi : (a.fieldHi : ℝ) ≤ 17 / 16) (ho : (b.fieldHi : ℝ) ≤ 17 / 16)
    (drop : (b.fieldHi : ℝ) ≤ a.fieldLo - 1 / 18000)
    (ratio : 3999 / 4000 * (a.weightHi : ℝ) ≤ b.weightLo) : Compared φ x y := by
  refine ⟨ha.1.2.trans hi, hb.1.2.trans ho, ?_, ?_⟩
  · linarith only [drop, hb.1.2, ha.1.1]
  · linarith only [ratio, ha.2.2, hb.2.1]

end PlasmaLean.Design.DommaschkPairedActionProfiles
