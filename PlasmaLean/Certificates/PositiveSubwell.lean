/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.NativeLowerAction
public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # An accessible action core excludes a prescribed first-well action -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositiveSubwell

open Set MirrorActionQuadrature Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope

/-- Every directed squared-speed lower bound in the packed block is positive. -/
def positive : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, p => Nat.blt 0 (speedSq p) && positive n (p >>> 72)

private theorem cells_below {w f : ℝ → ℝ} {h : ℝ} {n p : ℕ} {a : ℝ}
    (checks : positive n p = true) (cells : Cells false w f h a n p) :
    ∀ t ∈ Ico a (a + n / 3072), f t < h := by
  induction n generalizing a p with
  | zero =>
    simp
  | succ n ih =>
    simp only [positive,Bool.and_eq_true,Nat.blt_eq] at checks
    obtain ⟨first,rest⟩ := cells
    intro t ht
    by_cases hit : t < a + 1/3072
    · have bound := (first t ⟨ht.1,hit.le⟩).2
      have posNat : (0 : ℝ) < speedSq p := by exact_mod_cast checks.1
      change (speedSq p : ℝ) / 67108864 ≤ max (2 * (h - f t)) 0 at bound
      by_contra! earlier
      rw [max_eq_right (by linarith)] at bound
      linarith
    · apply ih checks.2 rest t
      have last := ht.2
      push_cast at last
      exact ⟨le_of_not_gt hit,by linarith⟩

/-- Physical panel lower bounds exclude any mirror before the end of the positive core. -/
theorem below {w f : ℝ → ℝ} {h a : ℝ} {bs : List (Block false)}
    (checks : bs.all (fun b => positive 48 b.packed) = true) (cells : Covers false w f h a bs) :
    ∀ t ∈ Ico a (a + bs.length / 64), f t < h := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at checks
    obtain ⟨first,rest⟩ := cells
    intro t ht
    by_cases hit : t < a+1/64
    · apply cells_below checks.1 first t
      exact ⟨ht.1,by norm_num; linarith⟩
    · apply ih checks.2 rest t
      have last := ht.2
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at last
      exact ⟨le_of_not_gt hit,by linarith⟩

/-- A positive-speed subinterval containing the birth is inside any first well around it.
The strict lower mass then applies without knowing where either mirror occurs. -/
theorem floor_in_first_well {f w : ℝ → ℝ} {h φ l r : ℝ} {n m : ℕ} {bs : List (Block false)}
    (len : bs.length = n + m) (checks : bs.all (fun b => positive 48 b.packed) = true)
    (cells : Covers false w f h (-(n : ℝ) / 64) bs) (birth : φ ∈ Icc (-(n : ℝ) / 64) (m / 64))
    (well : LaunchWell f φ h l r) (hn : ∀ t ∈ Icc l r, 0 ≤ w t)
    (cf : ContinuousOn f (Icc l r)) (cw : ContinuousOn w (Icc l r)) :
    l ≤ -(n : ℝ)/64 ∧ (m : ℝ)/64 ≤ r ∧
    total bs / (3072*1099511627776 : ℝ) ≤ action f w l r h := by
  have raw := below checks cells
  rw [len,Nat.cast_add,show -(n : ℝ)/64+((n : ℝ)+m)/64 = m/64 by ring] at raw
  have left : l ≤ -(n : ℝ)/64 := by
    by_contra! after
    exact (raw l ⟨after.le,well.left_lt.trans_le birth.2⟩).ne well.left_hit
  have right : (m : ℝ)/64 ≤ r := by
    by_contra! before
    exact (raw r ⟨birth.1.trans well.lt_right.le,before⟩).ne well.right_hit
  have sub := Icc_subset_Icc left right
  have core := NativeActionInterval.exact_lower_mass len cells
    (fun t ht => hn t (sub ht)) (cf.mono sub) (cw.mono sub)
  have order := birth.1.trans birth.2
  exact ⟨left,right,core.trans (action_mono_interval left order right cf cw hn)⟩

end PlasmaLean.Certificates.PositiveSubwell
