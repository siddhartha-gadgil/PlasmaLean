/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFirstMirrorBounceTime
public import PlasmaLean.Design.DommaschkMirrorBandAction

/-! # Regular births, finite flight times and a continuous true action at every band height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorBandPassage

open DommaschkSignedObservable DommaschkSignedTraceDomain DommaschkSignedMirrorBand
open DommaschkMirrorBandAction DommaschkFirstMirrorWell DommaschkFirstMirrorBounceTime
open Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign Set

/-- One physical trajectory, before the height is chosen, has all three regular
well properties at every height in the closed interval. -/
def Passage (φ : ℝ) (y : ℝ → Plane) : Prop :=
  Branches y ∧ ActionFamily y ∧ ∀ h ∈ Icc (height false : ℝ) (height true),
    Identified (316 / 64) (325 / 64) h y ∧
    Contract.RegularMirrorBirth (DommaschkQA2R.field DommaschkQA2R.candidate) (point y φ) h ∧
    Flight (316 / 64) (325 / 64) h φ y

theorem on_path {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane}
    {y : ℝ → Plane} {φ : ℝ} (path : Path n fs bs fr br x y) (reached : 325 ≤ n)
    (central : |φ| ≤ 316 / 64)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (band : Branches y) : Passage φ y := by
  have size : (325 : ℝ) ≤ n := by exact_mod_cast reached
  have stop : (325 : ℝ) / 64 ≤ n / 64 := by linarith
  refine ⟨band, family path reached region band, ?_⟩
  intro h hh
  have pos := lt_of_lt_of_le (by norm_num [height] : (0 : ℝ) < height false) hh.1
  have crossings := band.first_transverse hh
  have well := identify path (by norm_num) stop pos (by norm_num) region crossings
  exact ⟨well, well.at_launch central, of_contacts path central stop pos (by norm_num)
    region crossings⟩

end PlasmaLean.Design.DommaschkMirrorBandPassage
