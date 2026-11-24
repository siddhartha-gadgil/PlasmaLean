/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkFrameLaunch
public import PlasmaLean.Design.DommaschkPhysicalFirstStep

/-!
# First validated forward step from a Q-16 birth

The section state reached by the birth trajectory is the initial value of the
enclosed forward solution. Each clock is signed separately, since a birth on
either side of zero must first travel towards the common section.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorLaunch

open Certificates.PositionFrameSlabs DommaschkPhysicalFirstStep DommaschkBounceField Set
open DommaschkKamC KamNewton
open PlasmaLean.Theory.KAM WEll1Z2
open PlasmaLean.Contract PlasmaLean.Forms PlasmaLean.Fields.VacuumBoozer

/-- A physical birth reaches zero phase and its forward trajectory follows the first
recorded reference within the stated Euclidean distance, in dimensionless coordinates. -/
def FirstPassage (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ (sign : ℝ) (approach : ℝ → DommaschkBounceField.State) (v : ℝ → Plane),
    |sign| = 1 ∧ φ + sign * |φ| = 0 ∧ approach 0 = birth uC zC uA zA (47 / 100) φ ∧
    (∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach (physicalFlow φ sign t (approach t))
      (Icc 0 |φ|) t) ∧ coordinates (v 0) = approach |φ| ∧
    v (1 / 64) ∈ stateSet (next row) ∧
    ∀ t ∈ Icc 0 (1 / 64 : ℝ),
      HasDerivWithinAt v (DommaschkJacobian.euclideanFlow 0 1 t (v t)) (Icc 0 (1 / 64)) t ∧
      dist (v t) (reference 0 row t) ≤ 123 / 10 ^ 8

/-- Physical entry and the field estimates on the first moving frame apply to the same point. -/
theorem firstPassage_of_entry {uC zC uA zA : FA} {φ : ℝ}
    (h : SectionEntry .q0r470 uC zC uA zA φ) : FirstPassage uC zC uA zA φ := by
  obtain ⟨sign, approach, hs, hangle, hb, ha, inside⟩ := h
  simp only [MirrorEndpoint.opposite, azimuth, Bool.false_eq_true, ↓reduceIte, sub_zero]
    at hangle ha inside
  have start : coordinates.symm (approach |φ|) ∈ stateSet seed :=
    (mem_stateSet_identity (s := seed) (by rfl) _).mpr inside
  obtain ⟨v, hv, exit, tube⟩ := physical_first_step.solve _ start
  have launch : coordinates (v 0) = approach |φ| :=
    (congrArg coordinates hv).trans (coordinates.apply_symm_apply _)
  refine ⟨sign, approach, v, hs, hangle, ?_, ha, launch, ?_, ?_⟩
  · have radius : MirrorEndpoint.radius .q0r470 = 47 / 100 := by
      norm_num [MirrorEndpoint.radius]
    simpa only [radius] using hb
  · simpa [physicalSlab] using exit
  · intro t ht
    obtain ⟨ode, enclosure⟩ := tube t (by simpa [physicalSlab] using ht)
    have budget : row.physicalOut / (2 : ℝ)^80 ≤ 123 / 10 ^ 8 := by
      change (1481700234749866732 : ℝ) / 2 ^ 80 ≤ _
      norm_num
    exact ⟨by simpa only [physicalSlab, zero_add] using ode, enclosure.2.trans budget⟩

/-- One nested pair of Q-16 tori realizes the first validated forward slab for all
births within 2⁻¹⁹ geometric radian of the section at radius 0.470. -/
theorem exists_nested_firstPassage :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → FirstPassage uC zC uA zA φ := by
  obtain ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, entries⟩ := exists_nested_section_entry
  refine ⟨uC, zC, uA, zA, R₀, z₀, ΘC, ΘA, ic, ia, nested, fun φ hp => ?_⟩
  exact firstPassage_of_entry (entries .q0r470 φ (by
    simpa [MirrorEndpoint.width, MirrorEndpoint.opposite, azimuth] using hp))

end PlasmaLean.Design.DommaschkMirrorLaunch
