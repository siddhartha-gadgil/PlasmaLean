/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameProjection
public import PlasmaLean.Design.DommaschkPhysicalTraceStep

/-! # Coordinatewise trial boxes for a moving QA2R frame

The two coordinate projections of an ellipsoid can have different widths.
Two endpoint row lengths per coordinate suffice for the whole affine frame.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameProjection
open PositionFrameSlabs

/-- Exact endpoint checks for separate radial and vertical widths. -/
structure Rectangle (l r : Frame) (w radial vertical : ℕ) : Prop where
  leftR : rowFits l.a l.b w radial
  rightR : rowFits r.a r.b w radial
  leftZ : rowFits l.c l.d w vertical
  rightZ : rowFits r.c r.d w vertical

/-- A trial ball of zero radius needs zero width in both coordinates. -/
theorem Rectangle.zero_trial (l r : Frame) : Rectangle l r 0 0 0 := by
  constructor <;> simp [rowFits]

/-- A frame with diagonal entries one and two exhibits distinct sharp widths. -/
theorem diagonal_widths :
    let m : Frame := ⟨2 ^ 40, 0, 0, 2 ^ 41⟩
    Rectangle m m 1 1 2 ∧ ¬ Rectangle m m 1 1 1 := by
  dsimp only
  constructor
  · constructor <;> norm_num [rowFits]
  · intro impossible
    have vertical := impossible.leftZ
    norm_num [rowFits] at vertical

private theorem row_bound {a b c d : ℤ} {w p : ℕ} (left : rowFits a b w p)
    (right : rowFits c d w p) {t : ℝ} (ht : |t| ≤ 1) {v : Plane}
    (hv : ‖v‖ ≤ (w : ℝ) / 2 ^ 80) :
    |entry a c t * v 0 + entry b d t * v 1| ≤ (p : ℝ) / 2 ^ 80 := by
  have endpoint {x y : ℤ} (ok : rowFits x y w p) :
      |(x : ℝ) / 2 ^ 40 * v 0 + (y : ℝ) / 2 ^ 40 * v 1| ≤ (p : ℝ) / 2 ^ 80 := by
    change (x ^ 2 + y ^ 2) * (w : ℤ) ^ 2 ≤ ((p : ℤ) * 2 ^ 40) ^ 2 at ok
    have hr : ((x : ℝ) ^ 2 + (y : ℝ) ^ 2) * (w : ℝ) ^ 2 ≤ ((p : ℝ) * 2 ^ 40) ^ 2 := by
      exact_mod_cast ok
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    calc
      _ ≤ (((x : ℝ) / 2 ^ 40) ^ 2 + ((y : ℝ) / 2 ^ 40) ^ 2) * ‖v‖^2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
        nlinarith only [sq_nonneg ((x : ℝ) / 2 ^ 40 * v 1 - (y : ℝ) / 2 ^ 40 * v 0)]
      _ ≤ (((x : ℝ) / 2 ^ 40) ^ 2 + ((y : ℝ) / 2 ^ 40) ^ 2) * ((w : ℝ) / 2 ^ 80) ^ 2 := by gcongr
      _ ≤ _ := by nlinarith only [hr]
  obtain ⟨lo,hi⟩ := abs_le.mp ht
  have al : 0 ≤ (1 - t) / 2 := by linarith
  have ar : 0 ≤ (1 + t) / 2 := by linarith
  rw [show entry a c t * v 0 + entry b d t * v 1 =
      (1 - t) / 2 * ((a : ℝ) / 2 ^ 40 * v 0 + (b : ℝ) / 2 ^ 40 * v 1) +
      (1 + t) / 2 * ((c : ℝ) / 2 ^ 40 * v 0 + (d : ℝ) / 2 ^ 40 * v 1) by
        unfold entry
        push_cast
        ring]
  apply (abs_add_le ..).trans
  rw [abs_mul, abs_mul, abs_of_nonneg al, abs_of_nonneg ar]
  linarith only [mul_le_mul_of_nonneg_left (endpoint left) al,
    mul_le_mul_of_nonneg_left (endpoint right) ar]

/-- Both coordinate widths hold at every intermediate time for every point of the ball. -/
theorem Rectangle.coordinates {l r : Frame} {w radial vertical : ℕ}
    (ok : Rectangle l r w radial vertical) {t : ℝ} (ht : |t| ≤ 1)
    (det : affineDet l r t ≠ 0) {v : Plane} (hv : ‖v‖ ≤ (w : ℝ) / 2 ^ 80) :
    |frameEquiv l r t v 0| ≤ (radial : ℝ) / 2 ^ 80 ∧
      |frameEquiv l r t v 1| ≤ (vertical : ℝ) / 2 ^ 80 := by
  change |(frameEquiv l r t).toContinuousLinearMap v 0| ≤ _ ∧
      |(frameEquiv l r t).toContinuousLinearMap v 1| ≤ _
  rw [frameEquiv_forward det]
  simpa only [forward, matrix_zero, matrix_one] using
    And.intro (row_bound ok.leftR ok.rightR ht hv) (row_bound ok.leftZ ok.rightZ ht hv)

end PlasmaLean.Certificates.PositionFrameProjection

namespace PlasmaLean.Design.DommaschkProjectedTrial
open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly Set
open DommaschkPhysicalTraceStep DommaschkKam DommaschkBounceTaylor

/-- A moving physical trial ball belongs to the Taylor - model rectangle with
separately certified widths and the actual recorded reference polynomial. -/
theorem trial_membership {lim : Limits} {s : State} {r : Step} {m : Inputs}
    {radial vertical : ℕ} (ok : test lim s r = true) (hm : CenterMatches r m)
    (box : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (hu : (m.u.radius : ℝ) = (radial : ℝ) / 2 ^ 80)
    (hz : (m.z.radius : ℝ) = (vertical : ℝ) / 2 ^ 80)
    {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    m.u.Mem (coord a t) (x 0 - dkR0) ∧ m.z.Mem (coord a t) (x 1) := by
  have hs := abs_coord_le ht
  obtain ⟨cu,cz⟩ := box.coordinates hs (det_ne_zero ((Bool.and_eq_true_iff.mp ok).1) hs)
    (by simpa using hv : ‖v‖ ≤ r.trial / (2 : ℝ) ^ 80)
  have x := congrFun (hm.position a t) 0
  have z := congrFun (hm.position a t) 1
  change reference a r t 0 = dkR0 + eval m.u.poly (coord a t) at x
  change reference a r t 1 = eval m.z.poly (coord a t) at z
  dsimp only
  constructor
  · rw [Model.Mem, hu, PiLp.add_apply, x]
    change |_ + moving s r a t v 0 - _ - _| ≤ _
    convert cu using 2
    unfold moving
    ring
  · rw [Model.Mem, hz, PiLp.add_apply, z, add_sub_cancel_left]
    exact cz

end PlasmaLean.Design.DommaschkProjectedTrial
