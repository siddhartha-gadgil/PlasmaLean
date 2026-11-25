/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialSectionAction

/-! # Strict upper-height action inequalities on both radial faces of a launch sector -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectorFaces
open Set Certificates.PositionFrameSlabs Theory.KAM
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkMirrorLaunch Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction

/-- Every family through the same physical births inherits the strict action inequalities
on its two radial faces for any choice of first-well endpoints. -/
def FaceSigns (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∀ Y : Radius → ℝ → Plane,
    (∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ)) →
    (∀ u, Enclosed (Y u) (-(331 / 64)) (331 / 64)) →
    ∀ l r L R, LaunchWell (field (Y inner)) 0 level l r →
      LaunchWell (field (Y outer)) 0 level L R →
      action (field (Y inner)) (density (Y inner)) l r level < target ∧
      target < action (field (Y outer)) (density (Y outer)) L R level

/-- ODE uniqueness over the endpoint wells and uniqueness of first-well endpoints identify
both endpoint actions, including the arclength weights, on every admissible family. -/
theorem of_endpoint_witnesses {uC zC uA zA : FA} {φ l r L R : ℝ} {y z : ℝ → Plane}
    (time : φ ∈ Icc (-(327 / 64)) (327 / 64))
    (py : Enclosed y (-(327 / 64)) (327 / 64)) (pz : Enclosed z (-(327 / 64)) (327 / 64))
    (leftBirth : y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ))
    (rightBirth : z φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ))
    (wy : LaunchWell (field y) 0 level l r) (wz : LaunchWell (field z) 0 level L R)
    (sy : Icc l r ⊆ Icc (-(327 / 64)) (327 / 64)) (sz : Icc L R ⊆ Icc (-(327 / 64)) (327 / 64))
    (low : action (field y) (density y) l r level < target)
    (high : target < action (field z) (density z) L R level) : FaceSigns uC zC uA zA φ := by
  intro Y born paths a b c d left right
  have sub : Icc (-(327 / 64) : ℝ) (327 / 64) ⊆ Icc (-(331 / 64)) (331 / 64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  obtain ⟨wa,ma⟩ := transfer_well py ((paths inner).mono sub) time
    (leftBirth.trans (born inner).symm) wy sy
  obtain ⟨wb,mb⟩ := transfer_well pz ((paths outer).mono sub) time
    (rightBirth.trans (born outer).symm) wz sz
  obtain ⟨aa,bb⟩ := left.unique wa
  obtain ⟨cc,dd⟩ := right.unique wb
  rw [aa,bb,cc,dd,← ma,← mb]
  exact ⟨low, high⟩

end PlasmaLean.Design.DommaschkSectorFaces
