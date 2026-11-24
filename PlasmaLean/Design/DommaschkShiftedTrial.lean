/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkProjectedTrial

/-! # A reflected trial with unequal reference polynomials

The projected backward ball is enlarged by the coefficient ℓ¹ distance between
its reflected centre and the centre of the forward field-evaluation rectangle.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkShiftedTrial
open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly Set
open DommaschkKam DommaschkBounceTaylor

/-- The exact rational field-coordinate polynomials after reflecting the row. -/
def radialPoly (r : Step) : List ℚ := difference (polynomial r 0) [29 / 32]
def verticalPoly (r : Step) : List ℚ := scale (-1) (polynomial r 1)

/-- These two comparisons charge both the frame projection and the complete
polynomial-centre mismatch to the enclosing trial rectangle. -/
structure Fits (r : Step) (box : Inputs) (radial vertical : ℕ) : Prop where
  u : (radial : ℚ) / 2 ^ 80 + magnitude (difference (radialPoly r) box.u.poly) ≤ box.u.radius
  z : (vertical : ℚ) / 2 ^ 80 + magnitude (difference (verticalPoly r) box.z.poly) ≤ box.z.radius

/-- At each physical point of the full backward trial, the reflected point
belongs to the forward rectangle. Surplus width pays for any centre discrepancy. -/
theorem membership {lim : Limits} {s : State} {r : Step} {box : Inputs} {radial vertical : ℕ}
    (ok : test lim s r = true)
    (axes : PositionFrameProjection.Rectangle s.frame r.frame r.trial radial vertical)
    (fits : Fits r box radial vertical) {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    box.u.Mem (coord a t) (x 0 - dkR0) ∧ box.z.Mem (coord a t) (-x 1) := by
  have hs := abs_coord_le ht
  obtain ⟨u,z⟩ := axes.coordinates hs (det_ne_zero ((Bool.and_eq_true_iff.mp ok).1) hs)
    (by simpa using hv : ‖v‖ ≤ (r.trial : ℝ) / 2 ^ 80)
  dsimp only
  constructor
  · apply enclose (a := ⟨radialPoly r, (radial : ℚ) / 2 ^ 80⟩) hs _ fits.u
    simp only [Model.Mem, radialPoly, eval_difference, eval_cons, eval_nil, mul_zero, add_zero,
      Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, PiLp.add_apply]
    change |eval (polynomial r 0) _ + moving s r a t v 0 - dkR0 -
      (eval (polynomial r 0) _ - 29 / 32)| ≤ _
    convert u using 2
    unfold dkR0 moving
    ring
  · apply enclose (a := ⟨verticalPoly r, (vertical : ℚ) / 2 ^ 80⟩) hs _ fits.z
    simp only [Model.Mem, verticalPoly, eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
      PiLp.add_apply, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
    change |-(eval (polynomial r 1) _ + moving s r a t v 1) - -eval (polynomial r 1) _| ≤ _
    rw [show -(eval (polynomial r 1) (coord a t) + moving s r a t v 1) -
      -eval (polynomial r 1) (coord a t) = -moving s r a t v 1 by ring, abs_neg]
    exact z

end PlasmaLean.Design.DommaschkShiftedTrial
