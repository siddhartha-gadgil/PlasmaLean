/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkConnectedActionLevel

/-! # A common interval of prescribed actions on the original radial sector -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectorActionBand
open Set Theory.KAM DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkNativeWellAction DommaschkMirrorLaunch DommaschkSectorAction
open DommaschkConnectedActionLevel
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction DommaschkRadialAccessibleBirth

abbrev lowAction : ℝ := target - 21 / 10000
abbrev highAction : ℝ := target + 19 / 10000

theorem width : highAction - lowAction = 1 / 250 := by unfold highAction lowAction; ring

/-- Strict radial-face signs persist simultaneously for every action in the stated interval. -/
def BandFaces (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∀ j ∈ Icc lowAction highAction, FacesAt uC zC uA zA φ j

/-- The rational endpoint actions give the signs for a full target interval even when the
long radial family uses independent solutions at its two endpoints. -/
theorem of_endpoint_witnesses {uC zC uA zA : FA} {φ l r L R : ℝ} {y z : ℝ → Plane}
    (time : φ ∈ Icc (-(327 / 64)) (327 / 64))
    (py : Enclosed y (-(327 / 64)) (327 / 64)) (pz : Enclosed z (-(327 / 64)) (327 / 64))
    (leftBirth : y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ))
    (rightBirth : z φ = coordinates.symm (birth uC zC uA zA (239 / 500) φ))
    (wy : LaunchWell (field y) 0 level l r) (wz : LaunchWell (field z) 0 level L R)
    (sy : Icc l r ⊆ Icc (-(327 / 64)) (327 / 64)) (sz : Icc L R ⊆ Icc (-(327 / 64)) (327 / 64))
    (low : action (field y) (density y) l r level ≤ 1146552112157123 / 844424930131968)
    (high : 790254733800996141875465767 / 580284393415022003858964480 ≤
      action (field z) (density z) L R level) : BandFaces uC zC uA zA φ := by
  intro j hj Y born paths a b c d left right
  have sub : Icc (-(327 / 64) : ℝ) (327 / 64) ⊆ Icc (-(331 / 64)) (331 / 64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  obtain ⟨wa, ma⟩ := transfer_well py ((paths inner).mono sub) time
    (leftBirth.trans (born inner).symm) wy sy
  obtain ⟨wb, mb⟩ := transfer_well pz ((paths outer).mono sub) time
    (rightBirth.trans (born outer).symm) wz sz
  obtain ⟨aa, bb⟩ := left.unique wa
  obtain ⟨cc, dd⟩ := right.unique wb
  rw [aa, bb, cc, dd, ← ma, ← mb]
  have i : (1146552112157123 : ℝ) / 844424930131968 < lowAction := by norm_num [lowAction, target]
  have o : highAction < (790254733800996141875465767 : ℝ) / 580284393415022003858964480 := by
    norm_num [highAction, target]
  exact ⟨(low.trans_lt i).trans_le hj.1, (hj.2.trans_lt o).trans_le high⟩

/-- A continuous target may vary with the launch phase anywhere in the certified interval. -/
def Prescriptions (uC zC uA zA : FA) : Prop :=
  ∀ j : Phase → ℝ, Continuous j → (∀ φ, j φ ∈ Icc lowAction highAction) →
    CrossingFor uC zC uA zA j

theorem prescriptions_of_sector {uC zC uA zA : FA} (sector : Sector uC zC uA zA)
    (faces : ∀ φ : Phase, BandFaces uC zC uA zA φ)
    (access : ∀ p : Parameter, ∃ z : ℝ → Plane,
      z p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧ Accessible z) :
    Prescriptions uC zC uA zA := fun j cj bounds =>
  crossing_of_sector_profile cj sector (fun φ => faces φ (j φ) (bounds φ)) access

end PlasmaLean.Design.DommaschkSectorActionBand
