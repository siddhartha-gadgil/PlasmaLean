/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkEnclosedLaunchArcs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-! # One kinetic control time for physical birth arcs at several radial labels -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkJointLaunchArcs
open Set Fields Contract DommaschkSignedTraceDomain DommaschkPhaseZeroRegularBirth
open DommaschkFirstMirrorWell DommaschkEnclosedLaunchArcs
open Certificates.PositionFrameSlabs (Plane)

open Real in
/-- The compact Cartesian enclosure spans a complete turn. All azimuths therefore share it. -/
theorem in_positions {p : Plane} (reg : Region p) (t : ℝ) :
    cylPoint (p 0) t (p 1) ∈ positions := by
  let θ := (t : Angle).toReal
  have bound : |θ| ≤ π := Angle.abs_toReal_le_pi _
  have cs : cos θ = cos t := Angle.cos_toReal _
  have sn : sin θ = sin t := Angle.sin_toReal _
  refine ⟨(p 0,θ,p 1),⟨reg.1,?_,abs_le.mp reg.2⟩,?_⟩
  · exact abs_le.mp (bound.trans (by linarith [pi_lt_four] : π ≤ 316 / 64))
  · simp only [cylPoint,cs,sn]

/-- The two inputs furnished by a physical mirror calculation on a field-line arc. -/
def Admitted (a : ℝ) (y : ℝ → Plane) : Prop :=
  Population a y ∧ ∀ t ∈ Icc (-a) a, Region (y t)

/-- The union ranges over both the trajectory family and its closed central segments. -/
def arcUnion {ι : Type*} (a : ι → ℝ) (Y : ι → ℝ → Plane) : Set Space :=
  ⋃ i, point (Y i) '' Icc (-(a i)) (a i)

/-- Any collection of actual regular arcs in the enclosed cylinder shares one duration.
The index can range over several sections, radii, or continuously many launch angles. -/
theorem simultaneous {ι : Type*} [Nonempty ι] {a : ι → ℝ} {Y : ι → ℝ → Plane}
    (lengths : ∀ i, 0 ≤ a i) (arcs : ∀ i, Admitted (a i) (Y i)) :
    Simultaneous (arcUnion a Y) := by
  apply uniform_enclosed
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨_,mem_iUnion.mpr ⟨i,0,⟨neg_nonpos.mpr (lengths i),lengths i⟩,rfl⟩⟩
  · intro x hx
    obtain ⟨i,t,ht,rfl⟩ := mem_iUnion.mp hx
    exact in_positions ((arcs i).2 t ht) t
  · intro x hx
    obtain ⟨i,t,ht,rfl⟩ := mem_iUnion.mp hx
    exact ((arcs i).1.1 t ht).2.2.1

/-- Combine the two independent radial lines before identifying the common duration. All other
properties of the selected lines, including their original birth equations, are preserved. -/
theorem two_families {ι : Type*} [Nonempty ι] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {P : ι → (ℝ → Plane) → (ℝ → Plane) → Prop}
    (each : ∀ i, ∃ y z, P i y z ∧ Admitted a y ∧ Admitted b z) :
    ∃ Y Z : ι → ℝ → Plane, (∀ i, P i (Y i) (Z i) ∧ Admitted a (Y i) ∧ Admitted b (Z i)) ∧
      Simultaneous (arcUnion (fun _ : ι => a) Y ∪ arcUnion (fun _ : ι => b) Z) := by
  choose Y Z property first second using each
  refine ⟨Y,Z,fun i => ⟨property i,first i,second i⟩,?_⟩
  let radius : ι ⊕ ι → ℝ := Sum.elim (fun _ => a) (fun _ => b)
  let lines : ι ⊕ ι → ℝ → Plane := Sum.elim Y Z
  have all := simultaneous (a := radius) (Y := lines) (Sum.rec (fun _ => ha) (fun _ => hb))
    (Sum.rec first second)
  simpa only [arcUnion,iUnion_sum,lines,radius,Sum.elim_inl,Sum.elim_inr] using all

end PlasmaLean.Design.DommaschkJointLaunchArcs
