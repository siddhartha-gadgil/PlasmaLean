/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkOppositeMirrorExclusion
public import PlasmaLean.Design.DommaschkRibbonSlopeCover
public import PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
public import PlasmaLean.Design.DommaschkEndpointMirrorBranch

/-! # Outward first-mirror slopes for both original clocks on the opposite section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOppositeMirrorSlope

open Set Real Certificates PositionFrameSlabs TrajectoryTaylorModel
open DommaschkMirrorTubeCrossing DommaschkMirrorEndpointSign DommaschkMirrorStrengthSlope
open DommaschkOppositeMirrorExclusion DommaschkRibbonSlopeCover DommaschkBounceField DommaschkKam
open DommaschkGroupedMirrorModels
open DommaschkJacobian (euclideanFlow)
open DommaschkSignedMirrorBand (Rate)
set_option maxRecDepth 12000

def direction (back : Bool) : ℝ := if back then -1 else 1
def shift (back : Bool) (phase : ℝ) : ℝ := if back then -phase else phase

/-- Translating the outward clock permits direct use of the physical zero-phase derivative
and its reflection at any section. The reflected spatial point uses the actual backward row. -/
theorem translated {y : ℝ → DommaschkBounceField.State} {phase t k : ℝ} (back : Bool)
    (ode : HasDerivAt y (physicalFlow phase (direction back) t (y t)) t)
    (hR : 0 < y t 0)
    (hD : 0 < atPoint dD (y t 0) (t+shift back phase) (if back then -(y t 1) else y t 1))
    (num : k * ((y t 0)^17 * atPoint dD (y t 0) (t+shift back phase)
      (if back then -(y t 1) else y t 1)) < numerator (y t 0) (if back then -(y t 1) else y t 1)
        (cos (2*(t+shift back phase))) (sin (2*(t+shift back phase)))) :
    Rate (fun a => ‖DommaschkQA2R.field DommaschkQA2R.candidate
      (Contract.cylPoint (y a 0) (phase+direction back*a) (y a 1))‖) k t := by
  let d := shift back phase
  let Y := fun s => y (s-d)
  have atY : Y (t+d) = y t := by simp [Y]
  have fields : physicalFlow 0 (direction back) (t+d) (y t) =
      physicalFlow phase (direction back) t (y t) := by
    unfold physicalFlow
    rw [show 0+direction back*(t+d)=phase+direction back*t by
      cases back <;> simp [direction,d,shift] <;> ring]
  have base : HasDerivAt Y (physicalFlow 0 (direction back) (t+d) (Y (t+d))) (t+d) := by
    rw [atY,fields]
    apply HasDerivAt.comp_sub_const (t+d) d
    simpa only [add_sub_cancel_right] using ode
  rw [← atY] at hR hD num
  cases back
  · obtain ⟨v,hv,hv'⟩ := forward_of_physical base hR hD num
    refine ⟨v,hv,?_⟩
    have h := HasDerivAt.comp_add_const t d hv'
    simpa [Y,d,shift,direction,add_comm] using h
  · obtain ⟨v,hv,hv'⟩ := backward_of_physical base hR hD num
    refine ⟨v,hv,?_⟩
    have h := HasDerivAt.comp_add_const t d hv'
    simpa [Y,d,shift,direction,sub_eq_add_neg,add_comm,add_left_comm,add_assoc] using h

def SlabSlope (back : Bool) (r : Step) (a b k : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ y : ℝ → Plane, ∀ prev : PositionFrameSlabs.State, y t ∈ (physicalSlab prev r a).tube t →
    HasDerivAt y (euclideanFlow (π/2) (direction back) t (y t)) t →
    Rate (fun s => strength (π/2+direction back*s) (y s)) k t

private theorem negative {m : Model} {s x : ℝ} (h : m.Mem s x) :
    (TrajectoryTrig.negative m).Mem s (-x) := by
  change |-x - QPoly.eval (QPoly.scale (-1) m.poly) s| ≤ _
  rw [QPoly.eval_scale]
  simp only [Rat.cast_neg,Rat.cast_one,neg_one_mul,neg_sub_neg]
  rw [abs_sub_comm]
  exact h

private theorem coordinate_mem {r : Step} {prev : PositionFrameSlabs.State} {t a : ℝ} {x : Plane}
    (hx : x ∈ (physicalSlab prev r a).tube t) (back : Bool) (j : Fin 2) :
    (raw back r j).Mem (coord a t) (if back then -(x j) else x j) := by
  have h := coordinate hx j
  change |x j-QPoly.eval (polynomial r j) (coord a t)| ≤ _ at h
  cases back
  · simpa [raw,Model.Mem] using h
  · exact negative (show (raw false r j).Mem (coord a t) (x j) by simpa [raw,Model.Mem] using h)

/-- The original row, clock, output radius and six harmonic relations certify the slope
on its entire physical tube, even at a numerical seam when the joined ODE is differentiable. -/
theorem slope {i : ℕ} {p : TrajectoryHarmonicPacket.Packet i} {back : Bool}
    {r : Step} {a b : ℚ} {g : Group} {k : ℝ} (h : FitsRow p back r a b g)
    (field : Outward g k) : SlabSlope back r (i/64) (((i:ℝ)+1)/64) k := by
  intro t ht y prev inside ode
  have row : t ∈ Icc ((i:ℝ)/64) ((i:ℝ)/64+1/64) := by
    rwa [show (i:ℝ)/64+1/64=(i+1:ℝ)/64 by ring]
  have hs := abs_coord_le row
  have cw : coord (i/64) t = 128*t-(2*i+1:ℝ) := by unfold coord; ring
  have hw : |(a:ℝ)+b*coord (i/64) t| ≤ 1 := calc
    _ ≤ |(a:ℝ)| + |(b:ℝ)| * |coord (i/64) t| := by simpa [abs_mul] using abs_add_le (a:ℝ) ((b:ℝ)*coord (i/64) t)
    _ ≤ |(a:ℝ)| + |(b:ℝ)| := add_le_add le_rfl (mul_le_of_le_one_right (abs_nonneg _) hs)
    _ ≤ 1 := by exact_mod_cast h.clock
  have hp := DommaschkMirrorBracketSlab.positive_radius row inside h.center h.error
  have hc : ((p false 0).model false).Mem (coord (i/64) t) (cos (2*t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 false ht
  have hsin : ((p false 0).model true).Mem (coord (i/64) t) (sin (2*t)) := by
    simpa [cw,TrajectoryTrig.wave] using TrajectoryHarmonicPacket.physical p false 0 true ht
  let θ := t+shift back (π/2)
  have waves : cos (2*θ) = -cos (2*t) ∧ sin (2*θ) = -sin (2*t) := by
    cases back <;> simp only [θ,shift,Bool.false_eq_true,↓reduceIte]
    · rw [show 2*(t+π/2)=2*t+π by ring]
      simp [cos_add,sin_add]
    · rw [show 2*(t+ -(π/2))=2*t-π by ring]
      simp [cos_sub,sin_sub]
  have bounds := field (t := θ) hw (h.radial.mem hs (coordinate_mem inside false 0))
    (h.height.mem hs (coordinate_mem inside back 1)) (waves.1.symm ▸ h.cosine.mem hs (negative hc))
    (waves.2.symm ▸ h.sine.mem hs (negative hsin))
  let z s := coordinates (y s)
  have zd : HasDerivAt z (physicalFlow (π/2) (direction back) t (z t)) t := by
    apply (coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ode).congr_deriv
    exact coordinates.apply_symm_apply _
  exact translated (y := z) back zd hp bounds.1 bounds.2

end PlasmaLean.Design.DommaschkOppositeMirrorSlope
