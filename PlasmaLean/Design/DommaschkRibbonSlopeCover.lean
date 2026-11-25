/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCompensatedMirrorSlope
public import PlasmaLean.Design.DommaschkGroupedMirrorModels
public import PlasmaLean.Design.DommaschkSignedMirrorBand

/-! # Outward derivatives on both signed physical tubes from one harmonic bound -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRibbonSlopeCover
open Set Certificates PositionFrameSlabs TrajectoryTaylorModel DommaschkGroupedMirrorModels
open DommaschkMirrorStrengthSlope DommaschkMirrorEndpointSign DommaschkSignedMirrorBand
open DommaschkBounceField DommaschkKam

/-- A forward numerator margin and a strictly positive field denominator on the group. -/
def Outward (g : Group) (k : ℝ) : Prop :=
  ∀ {w R z t : ℝ}, |w| ≤ 1 → g.radial.Mem w R → g.height.Mem w z →
    g.cosine.Mem w (Real.cos (2*t)) → g.sine.Mem w (Real.sin (2*t)) →
    0 < atPoint dD R t z ∧
      k * (R^17 * atPoint dD R t z) < numerator R z (Real.cos (2*t)) (Real.sin (2*t))

private theorem original_mem {r : Step} {prev : PositionFrameSlabs.State} {a t : ℝ} {x : Plane}
    (inside : x ∈ (physicalSlab prev r a).tube t) (back : Bool) (j : Fin 2) :
    (raw back r j).Mem (coord a t) (if back then -(x j) else x j) := by
  have h := coordinate inside j
  change |x j - QPoly.eval (polynomial r j) (coord a t)| ≤ _ at h
  cases back
  · simpa only [Model.Mem,raw,Bool.false_eq_true,↓reduceIte,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat] using h
  · simp only [Model.Mem,raw,↓reduceIte,QPoly.eval_scale,Rat.cast_neg,Rat.cast_one,
      neg_one_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
    rwa [show -(x j) - -QPoly.eval (polynomial r j) (coord a t) =
      -(x j - QPoly.eval (polynomial r j) (coord a t)) by ring, abs_neg]

set_option maxHeartbeats 1200000 in
-- Elaborating both reflected field derivatives expands the finite coordinate maps.
set_option maxRecDepth 12000 in
/-- Each signed row uses its own tube radius and the original timing. At seams the full ODE
supplies an ordinary derivative. Reflection converts the negative clock to the same numerator. -/
theorem slope {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r : Step} {a b : ℚ} {g : Group} {k : ℝ} (fits : Covers p back r a b g)
    (estimate : Outward g k) :
    SlabSlope r (if back then -1 else 1) (i/64) (((i:ℝ)+1)/64) k := by
  intro t ht y prev inside ode
  have hs : |coord (i/64) t| ≤ 1 := abs_coord_le (by
    rwa [show (i : ℝ)/64 + 1/64 = (i+1 : ℝ)/64 by ring])
  have changeClock : coord (i/64) t = 128*t-(2*i+1 : ℝ) := by unfold coord; ring
  have hw : |(a : ℝ) + b * coord (i/64) t| ≤ 1 := calc
    _ ≤ |(a : ℝ)| + |(b : ℝ)| * |coord (i/64) t| := by
      simpa only [abs_mul] using abs_add_le (a : ℝ) ((b : ℝ) * coord (i/64) t)
    _ ≤ |(a : ℝ)| + |(b : ℝ)| := add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast fits.clock
  have radius := DommaschkMirrorBracketSlab.positive_radius
    (a := i/64) (by rwa [show (i : ℝ)/64+1/64 = (i+1:ℝ)/64 by ring]) inside fits.center fits.error
  have hc : ((p false 0).model false).Mem (coord (i/64) t) (Real.cos (2*t)) := by
    simpa [changeClock,TrajectoryTrig.wave] using
      TrajectoryHarmonicPacket.physical p false 0 false ht
  have hh : ((p false 0).model true).Mem (coord (i/64) t) (Real.sin (2*t)) := by
    simpa [changeClock,TrajectoryTrig.wave] using
      TrajectoryHarmonicPacket.physical p false 0 true ht
  have bounds := estimate hw (fits.radial.mem hs (original_mem inside false 0))
    (fits.height.mem hs (original_mem inside back 1)) (fits.cosine.mem hs hc) (fits.sine.mem hs hh)
  let z a := coordinates (y a)
  have eq : HasDerivAt z (physicalFlow 0 (if back then -1 else 1) t (z t)) t := by
    apply (coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ode).congr_deriv
    exact coordinates.apply_symm_apply _
  have coordEq (a : ℝ) (j : Fin 2) : z a j = y a j := rfl
  cases back
  · simpa only [coordEq,Bool.false_eq_true,↓reduceIte,one_mul,Rate,
      DommaschkMirrorTubeCrossing.strength]
      using forward_of_physical (y := z) eq radius bounds.1 bounds.2
  · simpa only [coordEq,↓reduceIte,neg_one_mul,Rate,DommaschkMirrorTubeCrossing.strength]
      using backward_of_physical (y := z) eq radius bounds.1 bounds.2

end PlasmaLean.Design.DommaschkRibbonSlopeCover
