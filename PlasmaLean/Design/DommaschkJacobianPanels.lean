/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkJacobianFrames

/-! # Panel-wise logarithmic norms for a Taylor-enclosed spatial Jacobian

Each panel checks both diagonal upper bounds of the transformed numerator,
the absolute value of its symmetric off-diagonal sum, and the positive
denominator. The determinant inequality is checked on their common panel.
-/

@[expose] public section
namespace PlasmaLean.Design.DommaschkJacobian

open Certificates.TrajectoryTaylorModel Certificates.QPoly

/-- Models for a common denominator and the three independent symmetric entries. -/
structure SymmetricModels where
  den : Model
  aa : Model
  dd : Model
  off : Model

def SymmetricModels.Mem (q : SymmetricModels) (t den : ℝ) (A : Entries) : Prop :=
  q.den.Mem t den ∧ q.aa.Mem t A.a ∧ q.dd.Mem t A.d ∧ q.off.Mem t (A.b + A.c)

/-- The three matrix bounds refer to the same closed interval of physical time. -/
structure MinorPanel (q : SymmetricModels) (mu l r : ℚ) where
  dl : ℚ
  a : ℚ
  d : ℚ
  w : ℚ
  denLow : checkOn q.den.poly (q.den.radius + dl) l r [r] = true
  aaHigh : checkOn (scale (-1) q.aa.poly) (q.aa.radius - a) l r [r] = true
  ddHigh : checkOn (scale (-1) q.dd.poly) (q.dd.radius - d) l r [r] = true
  offLow : checkOn q.off.poly (q.off.radius - w) l r [r] = true
  offHigh : checkOn (scale (-1) q.off.poly) (q.off.radius - w) l r [r] = true
  positive : 0 < dl
  muNonneg : 0 ≤ mu
  first : a ≤ mu * dl
  second : d ≤ mu * dl
  determinant : w ^ 2 ≤ 4 * (mu * dl - a) * (mu * dl - d)

private theorem lower_on {m : Model} {l r low : ℚ} {t y : ℝ}
    (h : checkOn m.poly (m.radius + low) l r [r] = true) (ht : t ∈ Set.Icc (l : ℝ) r)
    (hy : m.Mem t y) : (low : ℝ) ≤ y := by
  have b := checkOn_sound h t ht
  push_cast at b
  linarith only [b, (abs_le.mp hy).1]

private theorem upper_on {m : Model} {l r high : ℚ} {t y : ℝ}
    (h : checkOn (scale (-1) m.poly) (m.radius - high) l r [r] = true)
    (ht : t ∈ Set.Icc (l : ℝ) r) (hy : m.Mem t y) : y ≤ (high : ℝ) := by
  have b := checkOn_sound h t ht
  simp only [eval_scale, Rat.cast_sub, Rat.cast_neg, Rat.cast_one, neg_one_mul] at b
  linarith only [b, (abs_le.mp hy).2]

/-- An accepted panel proves the full quadratic estimate on every real point of the panel. -/
theorem MinorPanel.sound {q : SymmetricModels} {mu l r : ℚ} (p : MinorPanel q mu l r)
    {t den : ℝ} {A : Entries} (ht : t ∈ Set.Icc (l : ℝ) r) (h : q.Mem t den A) :
    0 < den ∧ ∀ x y : ℝ, A.quad x y / den ≤ (mu : ℝ) * (x ^ 2 + y ^ 2) := by
  obtain ⟨hden, ha, hd, hw⟩ := h
  have dlo := lower_on p.denLow ht hden
  have hpos : 0 < den := lt_of_lt_of_le (by exact_mod_cast p.positive) dlo
  have u := upper_on p.aaHigh ht ha
  have v := upper_on p.ddHigh ht hd
  have wo := upper_on p.offHigh ht hw
  have hl : checkOn q.off.poly (q.off.radius + -p.w) l r [r] = true := by
    simpa only [sub_eq_add_neg] using p.offLow
  have wi := lower_on hl ht hw
  have habs : |A.b + A.c| ≤ (p.w : ℝ) :=
    abs_le.mpr ⟨by simpa only [Rat.cast_neg] using wi, wo⟩
  have square := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at square
  have nonneg : (0 : ℝ) ≤ mu := by exact_mod_cast p.muNonneg
  have hh := mul_le_mul_of_nonneg_left dlo nonneg
  have a0 : (p.a : ℝ) ≤ mu * (p.dl : ℝ) := by exact_mod_cast p.first
  have d0 : (p.d : ℝ) ≤ mu * (p.dl : ℝ) := by exact_mod_cast p.second
  have small : (p.w : ℝ)^2 ≤ 4 * ((mu:ℝ)*p.dl-p.a) * ((mu:ℝ)*p.dl-p.d) := by
    exact_mod_cast p.determinant
  have ax := sub_le_sub hh u
  have dx := sub_le_sub hh v
  have product := mul_le_mul ax dx (sub_nonneg.mpr d0) (sub_nonneg.mpr (u.trans (a0.trans hh)))
  refine ⟨hpos,quadratic_le_of_minors A hpos (u.trans (a0.trans hh)) (v.trans (d0.trans hh)) ?_⟩
  nlinarith only [square, small, product]

/-- A finite collection of adjacent closed panels covers every time from left to right. -/
inductive MinorCover (q : SymmetricModels) (mu : ℚ) : ℚ → ℚ → Prop where
  | panel {l r : ℚ} (p : MinorPanel q mu l r) : MinorCover q mu l r
  | join {l m r : ℚ} (left : MinorCover q mu l m) (right : MinorCover q mu m r) :
      MinorCover q mu l r

theorem MinorCover.sound {q : SymmetricModels} {mu l r : ℚ} (p : MinorCover q mu l r)
    {t den : ℝ} {A : Entries} (ht : t ∈ Set.Icc (l : ℝ) r) (h : q.Mem t den A) :
    0 < den ∧ ∀ x y : ℝ, A.quad x y / den ≤ (mu : ℝ) * (x ^ 2 + y ^ 2) := by
  induction p with
  | panel p => exact p.sound ht h
  | @join a m b _ _ left right =>
    rcases le_total t (m : ℝ) with le | ge
    · exact left ⟨ht.1,le⟩
    · exact right ⟨ge,ht.2⟩

open Certificates.PositionFrameSlabs DommaschkKam DommaschkKam.DkPoly
open scoped RealInnerProductSpace

/-- A checked panel cover together with the real sparse-matrix memberships
bounds the actual moving-frame Euclidean quadratic form. -/
theorem spatial_log_norm_of_cover {q : SymmetricModels} {mu : ℚ}
    (accepted : MinorCover q mu (-1) 1) (l r : Frame) (t u z c s : ℝ) (ht : |t| ≤ 1)
    (h :
      let m := frameEntries l r t
      let D := evR u z c s dD * evR u z c s dD
      q.Mem t (m.det * D)
        (transformedNumerator (spatialNumerator u z c s) m (velocityEntries l r) D))
    (x : Plane) :
    ⟪x, Fields.LogNormTrajectory.MovingFrame.jacobian (spatialMatrix u z c s)
      (frameEquiv l r t) (frameVelocity l r) x⟫ ≤ (mu : ℝ) * ‖x‖ ^ 2 := by
  let D := evR u z c s dD * evR u z c s dD
  have time : t ∈ Set.Icc ((-1 : ℚ) : ℝ) ((1 : ℚ) : ℝ) := by
    simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using (abs_le.mp ht)
  have hh := accepted.sound time h
  obtain ⟨hm,hs⟩ := mul_ne_zero_iff.mp hh.1.ne'
  have hj : spatialMatrix u z c s = ((spatialNumerator u z c s).scale (1 / D)).toCLM := by
    unfold spatialMatrix Entries.toCLM Entries.scale spatialNumerator quotientEntry
    dsimp only [D]
    congr 1 <;> ring
  rw [hj, conjugate_quad _ _ _ _ _ hm hs, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  exact hh.2 (x 0) (x 1)

end PlasmaLean.Design.DommaschkJacobian
