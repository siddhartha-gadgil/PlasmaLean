/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
public import PlasmaLean.Certificates.PositionFrameObservationPrefix

/-! # Quantitative field clearances evaluated on the trajectory through an original birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkOriginalBirthMargin
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointTraceFamily
open DommaschkLowerActionPath DommaschkPhaseZeroRegularBirth DommaschkSignedTraceDomain
open DommaschkMirrorTubeCrossing Theory.KAM

/-- The complete signed physical ODE and both sets of tubes belong to the trajectory on
which the strength is bounded. Evaluation at the actual launch angle recovers the birth. -/
def AtBirth (e : MirrorEndpoint) (c : Checkpoint) (n : ℕ) (h : ℝ)
    (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
    Signed e.start c.forwardRows c.backwardRows (c.length / 64) y ∧
    ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), strength t (y t) < h

/-- A strict margin on a common nonempty initial segment follows the original physical
birth across both clocks. The observed segment may be shorter than the enclosing trajectory. -/
theorem from_passage {e : MirrorEndpoint} (phase : e.opposite = false)
    {c : Checkpoint} {n : ℕ} {h φ : ℝ} {uC zC uA zA : FA}
    (passage : c.Passage e uC zC uA zA φ) (room : |φ| ≤ c.length / 64)
    (positive : 0 < n) (fit : n ≤ c.length)
    (lf : c.forwardRows.length = c.length) (lb : c.backwardRows.length = c.length)
    (rf : c.forwardRows.all packed = true) (rb : c.backwardRows.all packed = true)
    (forward : OnTubes (fun t x => strength t x < h) e.start 0 (c.forwardRows.take n))
    (backward : OnTubes (fun t x => strength (-t) x < h) e.start 0 (c.backwardRows.take n)) :
    AtBirth e c n h uC zC uA zA φ := by
  apply at_original_birth phase passage room
  intro y path
  refine ⟨regions path.forward path.backward (positive.trans_le fit) lf lb rf rb, path, ?_⟩
  have plus := forward.on_initial (y := y) positive (lf ▸ fit) path.forward.contained
  have minus := backward.on_initial (y := fun s => y (-s)) positive (lb ▸ fit)
    path.backward.contained
  simp only [zero_add] at plus minus
  intro t ht
  rcases le_total 0 t with nonneg | nonpos
  · exact plus t ⟨nonneg, ht.2⟩
  · simpa only [neg_neg] using minus (-t) ⟨neg_nonneg.mpr nonpos, by linarith [ht.1]⟩

end PlasmaLean.Design.DommaschkOriginalBirthMargin
