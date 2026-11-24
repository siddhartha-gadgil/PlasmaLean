/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnWindow

/-! # A common Littlejohn time and a single open neighborhood for a compact family -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.VacuumLittlejohnWindow
open Fields Contract Set MeasureTheory Vacuum
open scoped Topology

/-- The entire birth family is contained in one controlled open subset of the allowed set. -/
def FamilyControl (B : Space → Space) (m q d : ℝ) (R K : Set GCBirth) : Prop :=
  ∃ T > 0, ∃ W : Set GCBirth, IsOpen W ∧ K ⊆ W ∧ W ⊆ R ∧ ∀ b ∈ W, Control B m q T d b

/-- Pointwise local control on compatible open neighborhoods uniformizes over a compact
family. Passing to a union takes the smaller of the two positive times. -/
theorem familyControl_of_local {B : Space → Space} {m q d : ℝ} {R K : Set GCBirth}
    (compact : IsCompact K) (localControl : ∀ x ∈ K, FamilyControl B m q d R {x}) :
    FamilyControl B m q d R K := by
  apply compact.induction_on (p := FamilyControl B m q d R)
  · exact ⟨1,by norm_num,∅,isOpen_empty,Subset.rfl,empty_subset _,by simp⟩
  · rintro A C subset ⟨t,ht,W,op,inside,valid,good⟩
    exact ⟨t,ht,W,op,subset.trans inside,valid,good⟩
  · rintro A C ⟨t,ht,U,ou,au,ur,gu⟩ ⟨s,hs,V,ov,cv,vr,gv⟩
    refine ⟨min t s,lt_min ht hs,U ∪ V,ou.union ov,union_subset_union au cv,
      union_subset ur vr,?_⟩
    intro b hb
    exact hb.elim (fun h => (gu b h).mono (min_le_left _ _))
      (fun h => (gv b h).mono (min_le_right _ _))
  · intro x hx
    obtain ⟨t,ht,U,op,here,sub,control⟩ := localControl x hx
    have mem : x ∈ U := here (mem_singleton x)
    exact ⟨U,mem_nhdsWithin_of_mem_nhds (op.mem_nhds mem),
      t,ht,U,op,Subset.rfl,sub,control⟩

/-- The same duration controls a positive-radius closed metric neighborhood of the
entire compact family in birth space. The reference constraints hold throughout it. -/
theorem FamilyControl.thickening {B : Space → Space} {m q d : ℝ} {R K : Set GCBirth}
    (family : FamilyControl B m q d R K) (compact : IsCompact K) :
    ∃ T > 0, ∃ ε > 0, ∃ W : Set GCBirth, IsOpen W ∧ Metric.cthickening ε K ⊆ W ∧
      W ⊆ R ∧ ∀ b ∈ W, Control B m q T d b := by
  obtain ⟨T,ht,W,op,inc,ref,controls⟩ := family
  obtain ⟨ε,pos,tube⟩ := compact.exists_cthickening_subset_open op inc
  exact ⟨T,ht,ε,pos,W,op,tube,ref,controls⟩

/-- A compact set of births in the regular vacuum domain and the interior of a compatible
reference has a common positive control time for every prescribed positive displacement cap. -/
theorem exists_control_compact {B : Space → Space} {Ω : Set Space} (vac : VacuumField Ω B)
    (m q : ℝ) {d : ℝ} (hd : 0 < d) {K R : Set GCBirth} (compact : IsCompact K)
    (regular : ∀ b ∈ K, b.1 ∈ VacuumLittlejohnLocal.regular B Ω) (compatible : K ⊆ interior R) :
    FamilyControl B m q d R K := by
  apply familyControl_of_local compact
  intro b hb
  obtain ⟨U,op,mem,T,ht,control⟩ := exists_control vac m q (regular b hb) hd
  exact ⟨T,ht,U ∩ interior R,op.inter isOpen_interior,
    singleton_subset_iff.mpr ⟨mem,compatible hb⟩,
    fun _ h => interior_subset h.2,fun x hx => control x hx.1⟩

/-- Under an open-positive birth law and a measurable finite trapped reference, any nonempty
compact family in its compatible regular interior has a positive controlled measure fraction. -/
theorem compact_guidingCentreBand {B : Space → Space} {Ω : Set Space} (vac : VacuumField Ω B)
    {m q d : ℝ} (hm : 0 < m) (hq : q ≠ 0) (hd : 0 < d)
    {K S : Set GCBirth} {energies pitches : Set ℝ} (compact : IsCompact K) (present : K.Nonempty)
    (regular : ∀ b ∈ K, b.1 ∈ VacuumLittlejohnLocal.regular B Ω)
    (compatible : K ⊆ interior (trappedReference B m S energies pitches))
    (ν : Measure GCBirth) [Measure.IsOpenPosMeasure ν] {axis : Set Space}
    (axis_nonempty : axis.Nonempty) (axis_compact : IsCompact axis)
    (meas : MeasurableSet (trappedReference B m S energies pitches))
    (finite : ν (trappedReference B m S energies pitches) ≠ ⊤) :
    ∃ T > 0, ∃ W : Set GCBirth, IsOpen W ∧ K ⊆ W ∧ 0 < ν W ∧
      GuidingCentreBand B m q axis ν S W energies pitches
        (ν.real W / ν.real (trappedReference B m S energies pitches)) d T ∧
      ∀ b ∈ W, Control B m q T d b := by
  obtain ⟨T,ht,W,op,inc,ref,controls⟩ :=
    exists_control_compact vac m q hd compact regular compatible
  have hit := present.mono inc
  exact ⟨T,ht,W,op,inc,op.measure_pos ν hit,
    guidingCentreBand ν hm hq axis_nonempty axis_compact ht hd op hit ref meas finite controls,
    controls⟩

end PlasmaLean.Kinetic.VacuumLittlejohnWindow
