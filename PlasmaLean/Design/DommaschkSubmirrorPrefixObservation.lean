/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameObservationPrefix
public import PlasmaLean.Design.DommaschkEndpointSignedTrace

/-! # Observe a common prefix of an independently certified field line and tube history -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSubmirrorPrefixObservation
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointSignedTrace
open DommaschkBounceField DommaschkKamC KamNewton Theory.KAM WEll1Z2 Set

/-- The approach and full signed physical field line are retained on their original time
horizon. The observable is required only on its own, possibly shorter, signed interval. -/
def Observed (e : MirrorEndpoint) (uC zC uA zA : FA) (φ T : ℝ) (fe be : Set Plane)
    (fr br : List Step) (n : ℕ) (P : ℝ → Plane → Prop) : Prop :=
  let phase := azimuth e.opposite
  let duration := |φ - phase|
  ∃ (s : ℝ) (a : ℝ → DommaschkBounceField.State) (y : ℝ → Plane),
    |s| = 1 ∧ φ + s * duration = phase ∧ a 0 = birth uC zC uA zA e.radius φ ∧
    (∀ t ∈ Icc 0 duration, HasDerivWithinAt a (physicalFlow φ s t (a t)) (Icc 0 duration) t) ∧
    y 0 = coordinates.symm (a duration) ∧ y (-T) ∈ be ∧ y T ∈ fe ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow phase 1 t (y t))
      (Icc (-T) T) t) ∧
    (∀ v ∈ physicalSlabs e.start 0 fr, ∀ t ∈ Icc v.start v.stop, y t ∈ v.tube t) ∧
    (∀ v ∈ physicalSlabs e.start 0 br, ∀ t ∈ Icc v.start v.stop, y (-t) ∈ v.tube t) ∧
    (n : ℝ) / 64 ≤ T ∧ (∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), P t (y t))

/-- Either input certificate can be longer; their shared time need only fit the physical path. -/
theorem of_birth {e : MirrorEndpoint} {uC zC uA zA : FA} {φ T : ℝ} {fe be : Set Plane}
    {fr br : List Step} {n : ℕ} {P : ℝ → Plane → Prop}
    (birth : FromBirth e uC zC uA zA φ T fe be
      (physicalSlabs e.start 0 fr) (physicalSlabs e.start 0 br))
    (hn : 0 < n) (hf : n ≤ fr.length) (hb : n ≤ br.length) (room : (n : ℝ) / 64 ≤ T)
    (forward : OnTubes P e.start 0 (fr.take n))
    (backward : OnTubes (fun t x => P (-t) x) e.start 0 (br.take n)) :
    Observed e uC zC uA zA φ T fe be fr br n P := by
  obtain ⟨s, a, hs, phase, src, approach, y, entry, left, right, ode, ft, bt⟩ := birth
  refine ⟨s, a, y, hs, phase, src, approach, entry, left, right, ode, ft, bt, room, ?_⟩
  have f := forward.on_initial (y := y) hn hf ft
  have b := backward.on_initial (y := fun t => y (-t)) hn hb bt
  simp only [zero_add] at f b
  intro t ht
  by_cases pos : 0 ≤ t
  · exact f t ⟨pos, ht.2⟩
  · simpa only [neg_neg] using b (-t) ⟨by linarith, by linarith [ht.1]⟩

end PlasmaLean.Design.DommaschkSubmirrorPrefixObservation
