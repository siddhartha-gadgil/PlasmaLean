/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCartesianMirrorBirth
public import PlasmaLean.Theory.Contract.TrappedBirthCoordinates

/-! # Realized position, velocity and magnetic moment at the QA2R pilot -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTrappedBirthCoordinates
open Set DommaschkCartesianAngleFlow DommaschkCartesianMirrorBirth DommaschkFirstMirrorWell
open DommaschkSignedTraceDomain DommaschkSignedMirrorBand DommaschkFirstMirrorLaunchSign
open DommaschkSignedObservable Contract Contract.TrappedBirthCoordinates
open Certificates.PositionFrameSlabs (Plane State Step)
set_option maxRecDepth 12000

theorem strict_at_birth {φ h : ℝ} {y : ℝ → Plane} (band : Branches y)
    (small : |φ| < 316 / 64) (height_mem : h ∈ Icc (height false : ℝ) (height true)) :
    ‖B (point y φ)‖ < h := by
  obtain ⟨⟨f⟩, ⟨b⟩⟩ := band
  let j : Icc (height false : ℝ) (height true) := ⟨h, height_mem⟩
  change DommaschkMirrorTubeCrossing.strength φ (y φ) < j.val
  rcases le_total 0 φ with pos | neg
  · exact f.before j φ ⟨pos, (abs_lt.mp small).2.trans (f.interior_time j).1⟩
  · have ht : -φ < b.time j := by linarith [(abs_lt.mp small).1, (b.interior_time j).1]
    simpa only [neg_neg] using b.before j (-φ) ⟨neg_nonneg.mpr neg, ht⟩

/-- The exact physical contracted reference has a five-dimensional open neighborhood
around each of the two velocity signs, for any cuts containing the specified birth data. -/
def Lifted (x : Fields.Space) : Prop :=
  ∀ (m e h : ℝ), 0 < m → 0 < e → h ∈ Icc (height false : ℝ) (height true) →
    ∀ (negative : Bool) (S : Set GCBirth) (energies pitches : Set ℝ),
      lift B m x e h negative ∈ interior S → e ∈ interior energies → 1 / h ∈ interior pitches →
        lift B m x e h negative ∈ interior (trappedReference B m S energies pitches)

theorem from_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    {φ : ℝ} (p : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) (small : |φ| < 316 / 64) : Lifted (point y φ) := by
  intro m e h hm he hh neg S energies pitches supp ener pitch
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have here : φ ∈ Icc (-(n : ℝ) / 64) (n / 64) :=
    ⟨by linarith [(abs_lt.mp small).1], by linarith [(abs_lt.mp small).2]⟩
  apply lift_mem_interior neg hm he (strict_at_birth band small hh)
    (strength_smooth (in_regular (region φ here) φ)).continuousAt supp ener pitch
  exact neighborhood p reached region band small hh

end PlasmaLean.Design.DommaschkTrappedBirthCoordinates
