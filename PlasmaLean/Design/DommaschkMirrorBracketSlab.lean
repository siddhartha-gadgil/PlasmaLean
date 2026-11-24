/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorEndpointSign

/-! # A physical solution crossing a single signed mirror bracket -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorBracketSlab
open Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
open DommaschkMirrorEndpointSign DommaschkMirrorTubeCrossing Set

/-- Physical time at the start or the end of a recorded slab. -/
def endTime (right : Bool) (a : ℝ) : ℝ := if right then a + 1 / 64 else a

/-- Integer position encoded by the corresponding end of the reference. -/
def endPoint (right : Bool) (r : Step) := if right then (next r).point else firstPoint r

/-- The endpoint record transfers coordinatewise to the true closed tube. -/
theorem end_coordinates {r : Step} {prev : State} {a : ℝ} {right : Bool}
    {x : Plane} {R z : ℤ} {e : ℕ}
    (hpoint : endPoint right r = (⟨R,z⟩ : Point)) (cap : r.physicalOut ≤ e)
    (hx : x ∈ (physicalSlab prev r a).tube (endTime right a)) :
    |x 0 - (R : ℝ) / 2 ^ 80| ≤ (e : ℝ) / 2 ^ 80 ∧
    |x 1 - (z : ℝ) / 2 ^ 80| ≤ (e : ℝ) / 2 ^ 80 := by
  have q : reference a r (endTime right a) = point (endPoint right r) := by
    cases right
    · exact reference_start a r
    · exact reference_end a r
  rw [hpoint] at q
  have radial := coordinate hx 0
  have vertical := coordinate hx 1
  rw [q,point_radial] at radial
  rw [q,point_vertical] at vertical
  have bound : (r.physicalOut : ℝ) / 2 ^ 80 ≤ (e : ℝ) / 2 ^ 80 :=
    div_le_div_of_nonneg_right (by exact_mod_cast cap) (by positivity)
  exact ⟨radial.trans bound,vertical.trans bound⟩

/-- Two inexpensive inequalities keep every point in the cylindrical tube off the axis. -/
theorem positive_radius {r : Step} {prev : State} {a t : ℝ} {x : Plane}
    (ht : t ∈ Icc a (a + 1 / 64)) (hx : x ∈ (physicalSlab prev r a).tube t)
    (p : magnitude (difference (polynomial r 0) [1]) ≤ 1 / 2)
    (e : r.physicalOut ≤ 2 ^ 78) : 0 < x 0 := by
  have c := enclose (c := ⟨[1],1 / 2⟩) (abs_coord_le ht)
    (mem_exact (polynomial r 0) (coord a t)) (by simpa [exactPoly] using p)
  have estimate := coordinate hx 0
  change |x 0 - Certificates.QPoly.eval (polynomial r 0) (coord a t)| ≤ _ at estimate
  have e' : (r.physicalOut : ℝ) / 2 ^ 80 ≤ 1 / 4 := by
    have cap : (r.physicalOut : ℝ) ≤ (2 : ℝ) ^ 78 := by exact_mod_cast e
    linarith only [cap]
  norm_num [Model.Mem, Certificates.QPoly.eval_cons, Certificates.QPoly.eval_nil, abs_le] at c
  linarith [(abs_le.mp estimate).1, c.1]

/-- Strict endpoint signs force a level hit along every continuous solution contained in
this physical slab. The trajectory may have reached the same height on an earlier slab. -/
theorem hit {r : Step} {prev : State} {a h sign : ℝ} {y : ℝ → Plane}
    (hy : ContinuousOn y (Icc a (a + 1 / 64)))
    (inside : ∀ t ∈ Icc a (a + 1 / 64), y t ∈ (physicalSlab prev r a).tube t)
    (p : magnitude (difference (polynomial r 0) [1]) ≤ 1 / 2)
    (e : r.physicalOut ≤ 2 ^ 78)
    (below : ∀ x ∈ (physicalSlab prev r a).tube a, strength (sign * a) x < h)
    (above : ∀ x ∈ (physicalSlab prev r a).tube (a + 1 / 64),
      h < strength (sign * (a + 1 / 64)) x) :
    ∃ t ∈ Ioo a (a + 1 / 64), strength (sign * t) (y t) = h :=
  exists_on_tube (by linarith) hy inside (fun _ ht _ hx => positive_radius ht hx p e) below above

end PlasmaLean.Design.DommaschkMirrorBracketSlab
