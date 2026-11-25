/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialFamilyContinuity
public import PlasmaLean.Design.DommaschkRadialRibbonEntry
public import PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues

/-! # A physical prescribed-action birth from four signed section enclosures -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRadialSectionAction

open Set Certificates.PositionFrameSlabs Theory.KAM
open DommaschkRadialFamilyContinuity DommaschkRadialActionAlternative DommaschkNativeWellAction
open DommaschkRadialRibbonEntry DommaschkMirrorLaunch
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction

abbrev cap : ℝ := 331 / 64

/-- Physical signs on the selected line at the symmetry section and at both common caps. -/
structure Signs (y : ℝ → Plane) : Prop where
  low : field y 0 < level
  back : level < field y (-cap)
  front : level < field y cap

/-- Every first accessible well at the prescribed height has two transverse mirrors. -/
def Simple (y : ℝ → Plane) : Prop :=
  ∀ l r, LaunchWell (field y) 0 level l r →
    deriv (field y) l ≠ 0 ∧ deriv (field y) r ≠ 0

/-- A single solution starting from each possible section point suffices. -/
def Sections (P : (ℝ → Plane) → Prop) : Prop :=
  ∀ (k : Fin 4) (x : Plane), x ∈ stateSet (seed k) →
    ∃ y : ℝ → Plane, y 0 = x ∧ Enclosed y (-cap) cap ∧ P y

/-- Preserve any certified section observable while identifying the actual interpolated birth. -/
theorem from_section {uC zC uA zA : FA} {u φ : ℝ} {k : Fin 4} {P : (ℝ → Plane) → Prop}
    (small : |φ| ≤ 1 / 2 ^ 19) (entry : Passage uC zC uA zA u φ k) (sections : Sections P) :
    ∃ y : ℝ → Plane, y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
      Enclosed y (-cap) cap ∧ P y := by
  obtain ⟨σ, a, unit, clock, start, approach, ball, _⟩ := entry
  obtain ⟨y, atZero, path, observable⟩ := sections k (coordinates.symm (a |φ|))
    ((mem_stateSet_identity (s := seed k) (by rfl) _).mpr ball)
  have original := DommaschkPhysicalFirstMirrorValues.original_position
    (T := cap) (phase := 0) (φ := φ) (σ := σ) (a := a) (y := y) (by norm_num [cap])
    (by simpa only [sub_zero] using small.trans (by norm_num : (1 : ℝ) / 2 ^ 19 ≤ 1 / 64))
    unit (by simpa only [sub_zero] using clock) (by simpa only [sub_zero] using atZero)
    (by simpa only [sub_zero] using approach) (fun t ht => (path.ode t ht).hasDerivWithinAt)
    (fun t ht => path.region _ (Icc_subset_Icc (by norm_num [cap]) (by norm_num [cap]) ht))
  exact ⟨y, by simpa only [sub_zero, start] using original, path, observable⟩

/-- The same pair of embedded tori supplies the radial endpoints and all intermediate births. -/
def Entries (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∀ u : Radius, ∃ k, (u : ℝ) ∈ tile k ∧ Passage uC zC uA zA u φ k

/-- An interior interpolated birth at the specified phase, its field line, and a transverse
first well on that same line with exactly the specified action. -/
def Realized (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ (u : Radius) (y : ℝ → Plane) (l r : ℝ), (u : ℝ) ∈ Ioo (47 / 100) (239 / 500) ∧
    y φ = coordinates.symm (birth uC zC uA zA u φ) ∧ Enclosed y (-cap) cap ∧
    LaunchWell (field y) 0 level l r ∧ deriv (field y) l ≠ 0 ∧ deriv (field y) r ≠ 0 ∧
    action (field y) (density y) l r level = target

theorem realized_of_sections {uC zC uA zA : FA} {φ : ℝ} (small : |φ| ≤ 1 / 2 ^ 19)
    (entries : Entries uC zC uA zA φ) (sections : Sections fun y => Signs y ∧ Simple y)
    (compare : ∀ Y : Radius → ℝ → Plane,
      (∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ)) →
      (∀ u, Enclosed (Y u) (-cap) cap) → (∀ u, Signs (Y u)) → Alternative Y) :
    Realized uC zC uA zA φ := by
  have each (u : Radius) : ∃ y : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA u φ) ∧
      Enclosed y (-cap) cap ∧ (Signs y ∧ Simple y) := by
    obtain ⟨k, _, e⟩ := entries u
    exact from_section small e sections
  choose Y born paths obs using each
  have alt := compare Y born paths fun u => (obs u).1
  obtain ⟨u, l, r, interior, well, value⟩ := prescribed_of_regular alt fun u => (obs u).2
  obtain ⟨left, right⟩ := (obs u).2 l r well
  exact ⟨u, Y u, l, r, interior, born u, paths u, well, left, right, value⟩

end PlasmaLean.Design.DommaschkRadialSectionAction
