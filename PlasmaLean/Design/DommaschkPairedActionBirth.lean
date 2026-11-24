/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPairedActionProfiles
public import PlasmaLean.Design.DommaschkSignedBirthApproach
public import PlasmaLean.Design.DommaschkEndpointSignedTrace
public import PlasmaLean.Design.DommaschkPhysicalArcTrace

/-! # Original interpolated births and their paired phase-zero field lines -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedActionBirth
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkMirrorLaunch
open DommaschkEndpointSignedTrace DommaschkPairedActionProfiles
open DommaschkJacobian (euclideanFlow)
open DommaschkSignedBirthApproach Set Theory.KAM

abbrev halfWidth : ℝ := 1 / 64
abbrev window := Icc (-halfWidth) halfWidth

/-- The trajectory passes through the original torus interpolation at its actual birth angle. -/
structure Launch (e : MirrorEndpoint) (uC zC uA zA : FA) (φ : ℝ) (y : ℝ → Plane) : Prop where
  source : y φ = coordinates.symm (birth uC zC uA zA e.radius φ)
  ode : ∀ t ∈ window, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) window t
  regular : ∀ t ∈ window, 0 < y t 0 ∧ 0 < atPoint DommaschkKam.dD (y t 0) t (y t 1)

/-- The checked arclength weight is the actual Cartesian speed on the interior. -/
theorem Launch.weight {e : MirrorEndpoint} {uC zC uA zA : FA} {φ : ℝ} {y : ℝ → Plane}
    (p : Launch e uC zC uA zA φ y) {t : ℝ} (ht : t ∈ Ioo (-halfWidth) halfWidth) :
    ‖deriv (fun a => Contract.cylPoint (y a 0) a (y a 1)) t‖ = weight t (y t) := by
  have h := p.regular t (Ioo_subset_Icc_self ht)
  exact DommaschkPhysicalActionPanel.arcDensity_of_ode
    ((p.ode t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) h.1 h.2

def RegularRow (back : Bool) (r : Step) : Prop :=
  ∀ {prev : Certificates.PositionFrameSlabs.State} {t : ℝ} {x : Plane}, t ∈ Icc 0 halfWidth →
    x ∈ (physicalSlab prev r 0).tube t →
    0 < x 0 ∧ 0 < atPoint DommaschkKam.dD (x 0) (if back then -t else t) (x 1)

def OnRow (back : Bool) (e : MirrorEndpoint) (r : Step) (y : ℝ → Plane) : Prop :=
  ∀ t ∈ Icc 0 halfWidth, y (if back then -t else t) ∈ (physicalSlab e.start r 0).tube t

theorem from_launch {e : MirrorEndpoint} {f b : Step} {uC zC uA zA : FA} {φ : ℝ}
    (phase : azimuth e.opposite = 0) (room : |φ| ≤ halfWidth)
    (full : FromBirth e uC zC uA zA φ halfWidth (stateSet (next f)) (stateSet (next b))
      (physicalSlabs e.start 0 [f]) (physicalSlabs e.start 0 [b]))
    (rf : RegularRow false f) (rb : RegularRow true b) :
    ∃ y, Launch e uC zC uA zA φ y ∧ OnRow false e f y ∧ OnRow true e b y := by
  unfold FromBirth at full
  simp only [phase, sub_zero] at full
  obtain ⟨s,a,unit,finish,src,approach,y,at0,back,front,ode,fw,bw⟩ := full
  have fwd : OnRow false e f y := fun t ht =>
    fw _ (List.mem_cons_self) t (by simpa [physicalSlab] using ht)
  have bwd : OnRow true e b y := fun t ht =>
    bw _ (List.mem_cons_self) t (by simpa [physicalSlab] using ht)
  have regular (t : ℝ) (ht : t ∈ window) :
      0 < y t 0 ∧ 0 < atPoint DommaschkKam.dD (y t 0) t (y t 1) := by
    by_cases pos : 0 ≤ t
    · exact rf ⟨pos, ht.2⟩ (fwd t ⟨pos, ht.2⟩)
    · have time : -t ∈ Icc 0 halfWidth := ⟨by linarith, by linarith [ht.1]⟩
      simpa only [neg_neg, ↓reduceIte] using rb time (bwd (-t) time)
  -- The approach uniqueness lemma uses the ODE and both endpoints. Its spatial
  -- regularity hypothesis is supplied directly by the two actual endpoint tubes.
  have odePath : DommaschkSignedObservable.Path 1 (next f) (next b) [] []
      (coordinates.symm (a |φ|)) y := by
    refine ⟨at0, ?_, ?_, ?_, fun _ h => False.elim (List.not_mem_nil h),
      fun _ h => False.elim (List.not_mem_nil h)⟩
    · simpa only [Nat.cast_one, neg_div, halfWidth] using back
    · simpa only [Nat.cast_one, halfWidth] using front
    · simpa only [Nat.cast_one, neg_div, window, halfWidth] using ode
  have same := along odePath unit finish (by simpa only [Nat.cast_one] using room) approach
    (by
      intro t ht
      have reg := regular t (by simpa only [Nat.cast_one, neg_div, window, halfWidth] using ht)
      exact ⟨reg.1, reg.2.ne'⟩)
  have atBirth := same (show (0 : ℝ) ∈ Icc 0 |φ| from ⟨le_rfl, abs_nonneg _⟩)
  rw [src] at atBirth
  refine ⟨y, ⟨?_, ode, regular⟩, fwd, bwd⟩
  apply coordinates.injective
  simpa only [mul_zero, add_zero, ContinuousLinearEquiv.apply_symm_apply] using atBirth.symm

end PlasmaLean.Design.DommaschkPairedActionBirth
