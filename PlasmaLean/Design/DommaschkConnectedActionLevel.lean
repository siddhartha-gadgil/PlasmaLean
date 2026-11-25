/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSectorAction
public import PlasmaLean.Design.DommaschkSectorFaces
public import PlasmaLean.Design.DommaschkRadialAccessibleBirth
public import PlasmaLean.Theory.Geometry.RectangleLevelCrossing

/-! # A connected locus of true birth-centered target actions on the QA2R launch sector -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkConnectedActionLevel
open Set Theory.KAM Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkSectorAction DommaschkRadialAccessibleBirth DommaschkRadialActionAlternative
open DommaschkMirrorLaunch DommaschkNativeWellAction DommaschkRadialFamilyContinuity
open DommaschkRadialSectionAction DommaschkSectorFaces

/-- A single compact connected set of original launch parameters covers all allowed phases.
Every parameter on it has the same true action and stays uniformly away from both radius faces. -/
def CrossingFor (uC zC uA zA : FA) (j : Phase → ℝ) : Prop :=
  ∃ (K : Set Parameter) (L R : Parameter → ℝ) (δ : ℝ),
    IsCompact K ∧ IsConnected K ∧ Prod.fst '' K = univ ∧ 0 < δ ∧ Continuous L ∧ Continuous R ∧
    ∀ p ∈ K, (p.2 : ℝ) ∈ Icc (47 / 100 + δ) (239 / 500 - δ) ∧
      ∃ y : ℝ → Plane, y p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧
        Enclosed y (-cap) cap ∧ LaunchWell (field y) p.1 level (L p) (R p) ∧
        deriv (field y) (L p) ≠ 0 ∧ deriv (field y) (R p) ≠ 0 ∧
        action (field y) (density y) (L p) (R p) level = j p.1

abbrev CrossingAt (uC zC uA zA : FA) (j : ℝ) := CrossingFor uC zC uA zA fun _ => j

abbrev Crossing (uC zC uA zA : FA) := CrossingAt uC zC uA zA target

/-- Strict physical action signs at any chosen target. -/
def FacesAt (uC zC uA zA : FA) (φ j : ℝ) : Prop :=
  ∀ Y : Radius → ℝ → Plane,
    (∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ)) →
    (∀ u, Enclosed (Y u) (-cap) cap) → ∀ l r L R,
    LaunchWell (field (Y inner)) 0 level l r → LaunchWell (field (Y outer)) 0 level L R →
    action (field (Y inner)) (density (Y inner)) l r level < j ∧
      j < action (field (Y outer)) (density (Y outer)) L R level

theorem crossing_of_sector_profile {uC zC uA zA : FA} {j : Phase → ℝ} (continuous : Continuous j)
    (sector : Sector uC zC uA zA)
    (faces : ∀ φ : Phase, FacesAt uC zC uA zA φ (j φ))
    (access : ∀ p : Parameter, ∃ z : ℝ → Plane,
      z p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧ Accessible z) :
    CrossingFor uC zC uA zA j := by
  obtain ⟨Y, L, R, J, physical, cl, cr, cj, _, _⟩ := sector
  have oriented (φ : Phase) : J (φ, inner) < j φ ∧ j φ < J (φ, outer) := by
    obtain ⟨_, _, left, _, _, jl⟩ := physical (φ, inner)
    obtain ⟨_, _, right, _, _, jr⟩ := physical (φ, outer)
    rw [jl, jr]
    exact faces φ (fun u => Y (φ, u)) (fun u => (physical (φ, u)).1)
      (fun u => (physical (φ, u)).2.1) _ _ _ _ left right
  obtain ⟨K, compact, connected, onLevel, projects⟩ :=
    RectangleLevelCrossing.interior_level_crossing_subtype (by norm_num) (by norm_num)
      (fun p => J p - j p.1) (cj.sub (continuous.comp continuous_fst))
      (fun φ => sub_neg.mpr (oriented φ).1) (fun φ => sub_pos.mpr (oriented φ).2)
  have radius : Continuous fun p : Parameter => (p.2 : ℝ) :=
    continuous_subtype_val.comp continuous_snd
  obtain ⟨a, ha, least⟩ := compact.exists_isMinOn connected.nonempty radius.continuousOn
  obtain ⟨b, hb, most⟩ := compact.exists_isMaxOn connected.nonempty radius.continuousOn
  let δ : ℝ := min ((a.2 : ℝ) - 47 / 100) (239 / 500 - (b.2 : ℝ))
  have pos : 0 < δ := lt_min (sub_pos.mpr (onLevel a ha).1.1) (sub_pos.mpr (onLevel b hb).1.2)
  refine ⟨K, L, R, δ, compact, connected, projects, pos, cl, cr, ?_⟩
  intro p hp
  have above : (a.2 : ℝ) ≤ (p.2 : ℝ) := least hp
  have below : (p.2 : ℝ) ≤ (b.2 : ℝ) := most hp
  have gapL : δ ≤ (a.2 : ℝ) - 47 / 100 := min_le_left _ _
  have gapR : δ ≤ 239 / 500 - (b.2 : ℝ) := min_le_right _ _
  obtain ⟨born, path, well, left, right, mass⟩ := physical p
  obtain ⟨z, bornZ, short⟩ := access p
  have actual := well_at_birth short (abs_le.mpr p.1.property)
    (path.mono (Icc_subset_Icc (by norm_num [cap]) (by norm_num [cap])))
    (bornZ.trans born.symm) well
  exact ⟨⟨by linarith, by linarith⟩, Y p, born, path, actual, left, right,
    mass.symm.trans (sub_eq_zero.mp (onLevel p hp).2)⟩

theorem crossing_of_sector_at {uC zC uA zA : FA} {j : ℝ} (sector : Sector uC zC uA zA)
    (faces : ∀ φ : Phase, FacesAt uC zC uA zA φ j)
    (access : ∀ p : Parameter, ∃ z : ℝ → Plane,
      z p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧ Accessible z) :
    CrossingAt uC zC uA zA j :=
  crossing_of_sector_profile continuous_const sector faces access

theorem crossing_of_sector {uC zC uA zA : FA} (sector : Sector uC zC uA zA)
    (faces : ∀ φ : Phase, FaceSigns uC zC uA zA φ)
    (access : ∀ p : Parameter, ∃ z : ℝ → Plane,
      z p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧ Accessible z) :
    Crossing uC zC uA zA := crossing_of_sector_at sector faces access

end PlasmaLean.Design.DommaschkConnectedActionLevel
