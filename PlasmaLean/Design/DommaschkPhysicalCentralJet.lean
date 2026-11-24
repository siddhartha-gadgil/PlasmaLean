/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFramedTaylorResidual

/-! # Physical central defect from concrete field values on the signed angular clock -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalCentralJet

open Certificates.QPoly Certificates.TrajectoryTaylorModel DommaschkBounceTaylor
open FramedTaylorResidual DommaschkBounceField DommaschkKam

/-- The polynomial evaluator may exploit harmonic correlations on the physical clock.
The three pointwise model memberships suffice for the framed differential inequality. -/
theorem of_memberships {F : Format} {back : Bool} {k b x y l : ℚ} {grid : List ℚ}
    {m : Frame} {r : Inputs} {nr nz den : Model} {t phase s : ℝ}
    (cert : Accepts (build F back k m r.u r.z nr nz den) b x y l grid)
    (hs : |s| ≤ 1) (hr : 0 < position r s 0)
    (hnr : nr.Mem s (clockPoly phase (sign back) dnR (t, position r s)))
    (hnz : nz.Mem s (clockPoly phase (sign back) dnZ (t, position r s)))
    (hdn : den.Mem s (clockPoly phase (sign back) dD (t, position r s)))
    (hm : 0 ≤ m.a.radius ∧ 0 ≤ m.b.radius ∧ 0 ≤ m.c.radius ∧ 0 ≤ m.d.radius) :
    let v := physicalFlow phase (sign back) t (position r s) - velocity r k s
    let w := pulled m s v
    Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) ≤ (b : ℝ) := by
  have own (a : Model) (ha : 0 ≤ a.radius) : a.Mem s (eval a.poly s) := by
    simpa only [Model.Mem, sub_self, abs_zero, Rat.cast_nonneg] using ha
  have bound := framed_defect cert hs hnr hnz hdn
    (own _ hm.1) (own _ hm.2.1) (own _ hm.2.2.1) (own _ hm.2.2.2)
  dsimp only
  rw [← ratio_eq_physical phase (sign back) t _ hr (right_ne_zero_of_mul bound.1)]
  exact bound.2

end PlasmaLean.Design.DommaschkPhysicalCentralJet
