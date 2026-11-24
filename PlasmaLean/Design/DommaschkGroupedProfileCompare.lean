/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkGroupedMirrorModels
public import PlasmaLean.Design.DommaschkNativeActionReflection
public import PlasmaLean.Design.DommaschkPairedArcRatio
public import PlasmaLean.Design.DommaschkCenteredStrength

/-! # Comparing two physical tubes on the same affine group clock -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkGroupedProfileCompare
open Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkGroupedMirrorModels
open DommaschkMirrorEndpointSign DommaschkMirrorTubeCrossing DommaschkPairedActionProfiles
open DommaschkJacobianReflection DommaschkPhysicalActionPanel Set

def InputsAt (g : Group) (s t : ℝ) (x : Plane) : Prop :=
  g.radial.Mem s (x 0) ∧ g.height.Mem s (x 1) ∧
  g.cosine.Mem s (Real.cos (2 * t)) ∧ g.sine.Mem s (Real.sin (2 * t))

def Comparison (inner outer : Group) : Prop :=
  ∀ {s t : ℝ} {x y : Plane}, |s| ≤ 1 → InputsAt inner s t x → InputsAt outer s t y →
    0 < x 0 ∧ 0 < y 0 ∧ Compared t x y

private theorem coordinate_mem {r : Step} {prev : State} {a t : ℝ} {x : Plane}
    (inside : x ∈ (physicalSlab prev r a).tube t) (back : Bool) (k : Fin 2) :
    (raw back r k).Mem (coord a t) (if back then -(x k) else x k) := by
  have h := coordinate inside k
  change |x k - QPoly.eval (polynomial r k) (coord a t)| ≤ _ at h
  cases back
  · simpa only [Model.Mem,raw,Bool.false_eq_true,↓reduceIte,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h
  · simp only [Model.Mem,raw,↓reduceIte,QPoly.eval_scale,Rat.cast_neg,Rat.cast_one,
      neg_one_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
    rwa [show -(x k) - -QPoly.eval (polynomial r k) (coord a t) =
      -(x k - QPoly.eval (polynomial r k) (coord a t)) by ring, abs_neg]

theorem row_inputs {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r : Step} {a b : ℚ} {g : Group} (h : Covers p back r a b g)
    {prev : State} {t : ℝ} {x : Plane} (ht : t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64))
    (hx : x ∈ (physicalSlab prev r (i / 64)).tube t) :
    let s := (a : ℝ) + b * coord (i / 64) t
    |s| ≤ 1 ∧ InputsAt g s t (if back then flip x else x) := by
  have hs : |coord (i / 64) t| ≤ 1 := abs_coord_le (by
    rwa [show (i : ℝ) / 64 + 1 / 64 = (i + 1 : ℝ) / 64 by ring])
  have cw : coord (i / 64) t = 128 * t - (2 * i + 1 : ℝ) := by unfold coord; ring
  have bound : |(a : ℝ) + b * coord (i / 64) t| ≤ 1 := calc
    _ ≤ |(a : ℝ)| + |(b : ℝ)| * |coord (i / 64) t| := by
      simpa [abs_mul] using abs_add_le (a : ℝ) ((b : ℝ)*coord (i / 64) t)
    _ ≤ |(a : ℝ)| + |(b : ℝ)| :=
      add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast h.clock
  have cosine : ((p false 0).model false).Mem (coord (i / 64) t) (Real.cos (2 * t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 false ht
  have sine : ((p false 0).model true).Mem (coord (i / 64) t) (Real.sin (2 * t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 true ht
  have hr := h.radial.mem hs (coordinate_mem hx false 0)
  have hz := h.height.mem hs (coordinate_mem hx back 1)
  refine ⟨bound,?_,?_,h.cosine.mem hs cosine,h.sine.mem hs sine⟩
  · cases back <;> simpa only [Bool.false_eq_true,↓reduceIte,flip_zero] using hr
  · cases back <;> simpa only [Bool.false_eq_true,↓reduceIte,flip_one] using hz

/-- The two group enclosures use the identical affine subclock; their original states,
outgoing tube radii and predecessors are independent. -/
theorem compare_rows {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r q : Step} {a b : ℚ} {g G : Group} (inner : Covers p back r a b g)
    (outer : Covers p back q a b G) (compare : Comparison g G)
    {prev prev' : State} {t : ℝ} {x y : Plane} (ht : t ∈ Icc ((i : ℝ) / 64) ((i + 1 : ℝ) / 64))
    (hx : x ∈ (physicalSlab prev r (i / 64)).tube t)
    (hy : y ∈ (physicalSlab prev' q (i / 64)).tube t) :
    Compared (if back then -t else t) x y := by
  obtain ⟨hw,mx⟩ := row_inputs inner ht hx
  have h := compare hw mx (row_inputs outer ht hy).2
  cases back
  · exact h.2.2
  · change 0 < (flip x) 0 ∧ 0 < (flip y) 0 ∧ Compared t (flip x) (flip y) at h
    rw [flip_zero,flip_zero] at h
    have weight_flip (v : Plane) (r : 0 < v 0) : weight (-t) v = weight t (flip v) := by
      simpa only [weight,neg_neg,flip_zero,flip_one] using arcDensity_reflected r t (-(v 1))
    change Compared (-t) x y
    unfold Compared
    rw [DommaschkNativeActionReflection.norm h.1 t,DommaschkNativeActionReflection.norm h.2.1 t,
      weight_flip x h.1,weight_flip y h.2.1]
    exact h.2.2

end PlasmaLean.Design.DommaschkGroupedProfileCompare
