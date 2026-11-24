/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorBracketSlab
public import PlasmaLean.Certificates.TrajectorySpatialSplit

/-! # Whole-slab coordinate inputs for a signed physical mirror-height certificate -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPreMirrorSigns
open Certificates Certificates.PositionFrameSlabs TrajectoryTaylorModel
open DommaschkBounceTaylor DommaschkMirrorEndpointSign DommaschkKam

/-- Equality of the coordinate polynomials and sufficient input radii on the physical tube. -/
structure Matches (back : Bool) (r : Step) (R : Model) (m : Inputs) : Prop where
  radiusPoly : polynomial r 0 = R.poly
  shiftedPoly : polynomial r 0 = QPoly.add [29 / 32] m.u.poly
  heightPoly : polynomial r 1 = if back then QPoly.scale (-1) m.z.poly else m.z.poly
  radiusError : (r.physicalOut : ℚ) / 2 ^ 80 ≤ R.radius
  uError : (r.physicalOut : ℚ) / 2 ^ 80 ≤ m.u.radius
  zError : (r.physicalOut : ℚ) / 2 ^ 80 ≤ m.z.radius

/-- Every point of the original recorded tube fits the spatial input of the norm certificate.
The reflected input on the negative clock has the identical physical field strength. -/
theorem Matches.mem {back : Bool} {r : Step} {prev : State} {R : Model} {m : Inputs}
    (h : Matches back r R m) {a t : ℝ} {x : Plane} (hx : x ∈ (physicalSlab prev r a).tube t) :
    R.Mem (coord a t) (x 0) ∧ m.u.Mem (coord a t) (x 0 - dkR0) ∧
      m.z.Mem (coord a t) (if back then -(x 1) else x 1) := by
  have cast {q : ℚ} (hq : (r.physicalOut : ℚ) / 2 ^ 80 ≤ q) :
      (r.physicalOut : ℝ) / 2 ^ 80 ≤ (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le.mpr hq : (((r.physicalOut : ℚ) / 2 ^ 80 : ℚ) : ℝ) ≤ (q : ℝ))
  have dr := coordinate hx 0
  have dz := coordinate hx 1
  change |x 0 - QPoly.eval (polynomial r 0) (coord a t)| ≤ _ at dr
  change |x 1 - QPoly.eval (polynomial r 1) (coord a t)| ≤ _ at dz
  refine ⟨?_, ?_, ?_⟩
  · rw [h.radiusPoly] at dr
    exact dr.trans (cast h.radiusError)
  · rw [h.shiftedPoly, QPoly.eval_add] at dr
    change |x 0 - dkR0 - QPoly.eval m.u.poly (coord a t)| ≤ _
    convert dr.trans (cast h.uError) using 2
    norm_num [QPoly.eval, dkR0]
    ring
  · rw [h.heightPoly] at dz
    cases back
    · exact dz.trans (cast h.zError)
    · simp only [↓reduceIte, QPoly.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul] at dz ⊢
      change |-(x 1) - QPoly.eval m.z.poly (coord a t)| ≤ _
      rw [show -(x 1) - QPoly.eval m.z.poly (coord a t) =
        -(x 1 - -QPoly.eval m.z.poly (coord a t)) by ring, abs_neg]
      exact dz.trans (cast h.zError)

/-- Translate a radial model into shifted cylindrical coordinates without changing its error. -/
theorem shifted_mem {r u : Model} {t R : ℝ} (h : r.Mem t R)
    (hc : r.poly = QPoly.add [29 / 32] u.poly) (he : r.radius ≤ u.radius) :
    u.Mem t (R - dkR0) := by
  rw [Model.Mem, hc, QPoly.eval_add] at h
  change |R - dkR0 - QPoly.eval u.poly t| ≤ _
  convert h.trans (Rat.cast_le.mpr he) using 2
  norm_num [QPoly.eval, dkR0]
  ring

end PlasmaLean.Design.DommaschkPreMirrorSigns
