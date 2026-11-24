/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnCompact

/-! # Uniform guiding-centre time from a compact regular enclosure of the initial states -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.VacuumLittlejohnWindow
open Fields Contract Set Vacuum

/-- The compact regular enclosure fixes the control time before the subset of seeds or the
reference cuts are chosen. The final open neighborhood can depend on those cuts. -/
theorem common_enclosure_time {B : Space → Space} {Ω : Set Space} (vac : VacuumField Ω B)
    (m q : ℝ) {d : ℝ} (hd : 0 < d) {C : Set GCBirth} (compact : IsCompact C)
    (regular : ∀ b ∈ C, b.1 ∈ VacuumLittlejohnLocal.regular B Ω) :
    ∃ T > 0, ∀ K R : Set GCBirth, K ⊆ C → K ⊆ interior R →
      ∃ W : Set GCBirth, IsOpen W ∧ K ⊆ W ∧ W ⊆ R ∧ ∀ b ∈ W, Control B m q T d b := by
  obtain ⟨T,ht,V,op,contains,_,control⟩ :=
    exists_control_compact vac m q hd compact regular (R := univ) (by simp)
  refine ⟨T,ht,fun K R enclosed compatible => ?_⟩
  exact ⟨V ∩ interior R,op.inter isOpen_interior,
    fun b hb => ⟨contains (enclosed hb),compatible hb⟩,
    fun _ h => interior_subset h.2,fun b hb => control b hb.1⟩

/-- The birth family itself can be arbitrary. A compact regular enclosure supplies uniform
time for the equation. Compatibility of each actual seed supplies the open observation set. -/
theorem control_of_compact_enclosure {B : Space → Space} {Ω : Set Space} (vac : VacuumField Ω B)
    (m q : ℝ) {d : ℝ} (hd : 0 < d) {K C R : Set GCBirth} (compact : IsCompact C)
    (regular : ∀ b ∈ C, b.1 ∈ VacuumLittlejohnLocal.regular B Ω)
    (enclosed : K ⊆ C) (compatible : K ⊆ interior R) : FamilyControl B m q d R K := by
  obtain ⟨T,ht,applyTo⟩ := common_enclosure_time vac m q hd compact regular
  exact ⟨T,ht,applyTo K R enclosed compatible⟩

end PlasmaLean.Kinetic.VacuumLittlejohnWindow
