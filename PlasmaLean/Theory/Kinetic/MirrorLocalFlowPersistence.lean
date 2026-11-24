/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorFlowPersistence
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # An open set of physical births from one local transverse mirror trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorWellPersistence
open Set Function Filter MeasureTheory
open scoped Topology NNReal

private theorem smooth_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {χ : Fields.Space → ℝ} {f : Fields.Space → E} {U : Set Fields.Space}
    (smooth : ContDiff ℝ 1 χ) (op : IsOpen U) (within : tsupport χ ⊆ U)
    (regular : ContDiffOn ℝ 1 f U) : ContDiff ℝ 1 (χ • f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases h : x ∈ U
  · exact smooth.contDiffAt.smul ((regular x h).contDiffAt (op.mem_nhds h))
  · have off := notMem_tsupport_iff_eventuallyEq.mp (fun hx => h (within hx))
    apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [off] with y hy
    simp [Pi.smul_apply', hy]

/-- Only local field data on an open set and one integral curve are required.
A smooth cutoff on a compact neighborhood supplies the globally bounded model. -/
theorem regular_birth_open_of_local {B V : Fields.Space → Fields.Space} {F v : Fields.Space → ℝ}
    {U : Set Fields.Space} {a c b : ℝ} {z : Fields.Space × ℝ} (op : IsOpen U)
    (hac : a < c) (hcb : c < b) (velocity : ContDiffOn ℝ 1 V U) (scalar : ContDiffOn ℝ 1 F U)
    (speed : ContinuousOn v U) (field : ∀ x ∈ U, F x = ‖B x‖ ∧ 0 < v x ∧ B x ≠ 0 ∧
      V x = v x • GCLittlejohn.bhat B x) (one : FlowBracketIn V F U a c b z) :
    ∃ W : Set (Fields.Space × ℝ), IsOpen W ∧ z ∈ W ∧
      W ⊆ {q | Contract.RegularMirrorBirth B q.1 q.2} := by
  obtain ⟨X, start, ode, well, stays⟩ := one
  have cx : ContinuousOn X (Icc a b) := fun t ht => (ode t ht).continuousAt.continuousWithinAt
  have compact := isCompact_Icc.image_of_continuousOn cx
  obtain ⟨O, openO, imageO, clU, compactO⟩ :=
    exists_open_between_and_isCompact_closure compact op stays.image_subset
  obtain ⟨D, compactD, inner, subO⟩ := exists_compact_between compact openO imageO
  obtain ⟨χ, smooth, _, supp, unit⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) openO compactD.isClosed subO
  have support : tsupport χ = closure O := congrArg closure supp
  have compactχ : HasCompactSupport χ := by
    change IsCompact (tsupport χ)
    simpa only [support] using compactO
  have withinχ : tsupport χ ⊆ U := support ▸ clU
  have vs := smooth_cut smooth op withinχ velocity
  have fs := smooth_cut smooth op withinχ scalar
  have compactV : HasCompactSupport (χ • V) := compactχ.smul_right
  obtain ⟨K, lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport compactV vs (by norm_num)
  obtain ⟨M, magnitude⟩ := compactV.exists_bound_of_continuous vs.continuous
  let L : ℝ≥0 := ⟨max 0 M, le_max_left _ _⟩
  have bound (x) : ‖(χ • V) x‖ ≤ L := (magnitude x).trans (le_max_right _ _)
  have subU : interior D ⊆ U := interior_subset.trans (subO.trans (subset_closure.trans clU))
  have fixed (x) (hx : x ∈ interior D) : χ x = 1 := (unit x).mp (interior_subset hx)
  have inside : MapsTo X (Icc a b) (interior D) := fun t ht => inner (mem_image_of_mem _ ht)
  apply regular_birth_open_of_model (V := χ • V) (F := χ • F) isOpen_interior hac hcb
    lip bound fs (speed.mono subU)
  · intro x hx
    simpa only [Pi.smul_apply', fixed x hx, one_smul] using field x (subU hx)
  refine ⟨X, start, ?_, ?_, inside⟩
  · intro t ht
    simpa only [Pi.smul_apply', fixed _ (inside ht), one_smul] using ode t ht
  · have agree (t : ℝ) (ht : t ∈ Icc a b) : (F ∘ X) =ᶠ[𝓝 t] ((χ • F) ∘ X) := by
      filter_upwards [(ode t ht).continuousAt (isOpen_interior.mem_nhds (inside ht))] with s hs
      simp [Function.comp_apply, fixed _ hs]
    exact well.congrOn hac.le hcb.le (fun t ht => (agree t ht).self_of_nhds)
      (fun t ht => (agree t ht).deriv_eq)

/-- Any measure charging nonempty open sets gives positive mass to physical regular births
as soon as one local field-line window satisfies the transverse bracket. -/
theorem regular_birth_mass_of_local {B V : Fields.Space → Fields.Space} {F v : Fields.Space → ℝ}
    {U : Set Fields.Space} {a c b : ℝ} {z : Fields.Space × ℝ} (μ : Measure (Fields.Space × ℝ))
    [Measure.IsOpenPosMeasure μ] (op : IsOpen U) (hac : a < c) (hcb : c < b)
    (velocity : ContDiffOn ℝ 1 V U) (scalar : ContDiffOn ℝ 1 F U) (speed : ContinuousOn v U)
    (field : ∀ x ∈ U, F x = ‖B x‖ ∧ 0 < v x ∧ B x ≠ 0 ∧ V x = v x • GCLittlejohn.bhat B x)
    (one : FlowBracketIn V F U a c b z) :
    0 < μ {q | Contract.RegularMirrorBirth B q.1 q.2} := by
  obtain ⟨W, openW, here, sub⟩ :=
    regular_birth_open_of_local op hac hcb velocity scalar speed field one
  exact (openW.measure_pos μ ⟨z, here⟩).trans_le (measure_mono sub)

end PlasmaLean.Kinetic.MirrorWellPersistence
