/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellPersistence
public import Mathlib.Analysis.ODE.ExistUnique

/-! # Persistence of a transverse well under changes in initial position and height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorWellPersistence
open Set Metric MeasureTheory
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One initial position and height admit an integral curve with the two transverse
first mirrors in a prescribed time window. -/
def FlowBracketIn (V : E → E) (F : E → ℝ) (U : Set E) (a c b : ℝ) (z : E × ℝ) : Prop :=
  ∃ X : ℝ → E, X c = z.1 ∧
    (∀ t ∈ Icc a b, HasDerivAt X (V (X t)) t) ∧ Bracket (F ∘ X) a c b z.2 ∧
    MapsTo X (Icc a b) U

/-- Continuous dependence supplied by Picard–Lindelöf makes the regular-bracket
condition open in the full initial position and height. The scalar observable is C¹. -/
theorem isOpen_flowBracketIn {U : Set E} (openU : IsOpen U) {V : E → E} {F : E → ℝ} {K L : ℝ≥0}
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (lip : LipschitzWith K V) (bound : ∀ x, ‖V x‖ ≤ L)
    (smooth : ContDiff ℝ 1 F) : IsOpen {z | FlowBracketIn V F U a c b z} := by
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨x, h⟩ ⟨X, start, ode, bracket, inside⟩
  let A := a - 1
  let B := b + 1
  let width := max (B - c) (c - A)
  have width0 : 0 ≤ width := le_max_of_le_left (by dsimp [B]; linarith)
  let radius : ℝ≥0 := ⟨(L : ℝ) * width + 1, by positivity⟩
  have room : ∀ t ∈ Icc a b, t ∈ Ioo A B := by
    rintro t ⟨lo, hi⟩
    constructor <;> dsimp [A, B] <;> linarith
  have center := room c ⟨hac.le, hcb.le⟩
  have picard : IsPicardLindelof (fun _ => V) (⟨c, center.1.le, center.2.le⟩ : Icc A B)
      x radius 1 L K := by
    refine ⟨fun _ _ => lip.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ y _ => bound y, ?_⟩
    change (L : ℝ) * width ≤ (L : ℝ) * width + 1 - 1
    linarith
  obtain ⟨flow, sol, joint⟩ := picard.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  let P := ball x 1
  let Y (p : P) (t : ℝ) := flow (p, t)
  have near (p : P) : (p : E) ∈ closedBall x (1 : ℝ) := ball_subset_closedBall p.property
  have initial (p : P) : Y p c = p := (sol p (near p)).1
  have d (p : P) (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (Y p) (V (Y p t)) t :=
    ((sol p (near p)).2 t (Ioo_subset_Icc_self (room t ht))).hasDerivAt
      (Icc_mem_nhds (room t ht).1 (room t ht).2)
  have cy : ContinuousOn (fun z : P × ℝ => Y z.1 z.2) (univ ×ˢ Icc a b) :=
    joint.comp (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd).continuousOn
      fun z hz => ⟨near z.1, Ioo_subset_Icc_self (room z.2 hz.2)⟩
  have chain {Z : ℝ → E} {t : ℝ} (hz : HasDerivAt Z (V (Z t)) t) :
      deriv (F ∘ Z) t = fderiv ℝ F (Z t) (V (Z t)) :=
    ((smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hz).deriv
  let S := {z : P × ℝ | Bracket (F ∘ Y z.1) a c b z.2 ∧ MapsTo (Y z.1) (Icc a b) U}
  have op₁ : IsOpen {z : P × ℝ | Bracket (F ∘ Y z.1) a c b z.2} := by
    apply isOpen_bracket (F := fun p => F ∘ Y p) hac.le hcb.le
      (smooth.continuous.comp_continuousOn cy)
    apply ((smooth.continuous_fderiv (by norm_num)).clm_apply lip.continuous
      |>.comp_continuousOn cy).congr
    intro z hz
    exact chain (d z.1 z.2 hz.2)
  have op₂ : IsOpen {p : P | MapsTo (Y p) (Icc a b) U} := isOpen_stays openU cy
  have op : IsOpen S := op₁.inter (op₂.preimage continuous_fst)
  let p : P := ⟨x, mem_ball_self (by norm_num)⟩
  have eq : EqOn X (Y p) (Icc a b) :=
    ODE_solution_unique_of_mem_Icc (s := fun _ => univ) (v := fun _ => V)
      (fun _ _ => lip.lipschitzOnWith) ⟨hac, hcb⟩
      (fun t ht => (ode t ht).continuousAt.continuousWithinAt)
      (fun t ht => ode t (Ioo_subset_Icc_self ht)) (fun _ _ => mem_univ _)
      (fun t ht => (d p t ht).continuousAt.continuousWithinAt)
      (fun t ht => d p t (Ioo_subset_Icc_self ht)) (fun _ _ => mem_univ _)
      (start.trans (initial p).symm)
  have profile (t) (ht : t ∈ Icc a b) : (F ∘ X) t = (F ∘ Y p) t := congrArg F (eq ht)
  have slopes (t) (ht : t ∈ Icc a b) : deriv (F ∘ X) t = deriv (F ∘ Y p) t := by
    rw [chain (ode t ht), chain (d p t ht), eq ht]
  have here : (p, h) ∈ S :=
    ⟨bracket.congrOn hac.le hcb.le (fun _ ht => profile _ ht) (fun _ ht => slopes _ ht),
      fun _ ht => eq ht ▸ inside ht⟩
  let insert : P × ℝ → E × ℝ := Prod.map Subtype.val id
  have mapping : IsOpenMap insert := isOpen_ball.isOpenMap_subtype_val.prodMap IsOpenMap.id
  refine ⟨insert '' S, ?_, mapping _ op, ⟨(p, h), here, rfl⟩⟩
  rintro _ ⟨⟨q, k⟩, good, rfl⟩
  exact ⟨Y q, initial q, d q, good⟩

/-- The unrestricted window predicate. -/
abbrev FlowBracket (V : E → E) (F : E → ℝ) := FlowBracketIn V F univ

/-- In the unrestricted case the entire position-height incidence set is open. -/
theorem isOpen_flowBracket {V : E → E} {F : E → ℝ} {K L : ℝ≥0} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (lip : LipschitzWith K V) (bound : ∀ x, ‖V x‖ ≤ L)
    (smooth : ContDiff ℝ 1 F) : IsOpen {z | FlowBracket V F a c b z} :=
  isOpen_flowBracketIn isOpen_univ hac hcb lip bound smooth

/-- The analytical extensions need only agree with the physical field and its
strength on the open tube. The speed allows any positive field-line parameterization. -/
theorem regular_birth_open_of_model {V B : Fields.Space → Fields.Space}
    {F v : Fields.Space → ℝ} {K L : ℝ≥0} {U : Set Fields.Space} {a c b : ℝ}
    {z : Fields.Space × ℝ} (op : IsOpen U) (hac : a < c) (hcb : c < b)
    (lip : LipschitzWith K V) (bound : ∀ x, ‖V x‖ ≤ L) (smooth : ContDiff ℝ 1 F)
    (speed : ContinuousOn v U) (field : ∀ x ∈ U, F x = ‖B x‖ ∧ 0 < v x ∧ B x ≠ 0 ∧
      V x = v x • GCLittlejohn.bhat B x) (one : FlowBracketIn V F U a c b z) :
    ∃ W : Set (Fields.Space × ℝ), IsOpen W ∧ z ∈ W ∧
      W ⊆ {q | Contract.RegularMirrorBirth B q.1 q.2} := by
  refine ⟨_, isOpen_flowBracketIn op hac hcb lip bound smooth, one, ?_⟩
  rintro ⟨x, h⟩ ⟨X, hx, ode, well, inside⟩
  have cx : ContinuousOn X (Icc a b) := fun t ht => (ode t ht).continuousAt.continuousWithinAt
  let f (t : ℝ) := ‖B (X t)‖
  have agree (t : ℝ) (ht : t ∈ Icc a b) : (F ∘ X) =ᶠ[nhds t] f := by
    filter_upwards [(ode t ht).continuousAt (op.mem_nhds (inside ht))] with s hs
    exact (field (X s) hs).1
  have eq : EqOn (F ∘ X) f (Icc a b) := fun t ht => (agree t ht).self_of_nhds
  have actual := well.congrOn hac.le hcb.le eq (fun t ht => (agree t ht).deriv_eq)
  have cf : ContinuousOn f (Icc a b) := (smooth.continuous.comp_continuousOn cx).congr eq.symm
  change Contract.RegularMirrorBirth B x h
  change X c = x at hx
  rw [← hx]
  apply actual.regularBirth (speed := v ∘ X) hac hcb cf (speed.comp cx inside)
  intro t ht
  obtain ⟨_, pos, nz, move⟩ := field (X t) (inside ht)
  exact ⟨pos, nz, (ode t ht).congr_deriv move⟩

/-- A bounded Lipschitz, nowhere-zero C¹ magnetic field gives an open subset of
physical Cartesian launch positions and heights satisfying the arclength birth contract. -/
theorem regular_birth_open_neighborhood {B : Fields.Space → Fields.Space} {K L : ℝ≥0}
    {a c b : ℝ} {z : Fields.Space × ℝ} (hac : a < c) (hcb : c < b)
    (lip : LipschitzWith K B) (bound : ∀ x, ‖B x‖ ≤ L) (smooth : ContDiff ℝ 1 B)
    (nz : ∀ x, B x ≠ 0) (one : FlowBracket B (fun x => ‖B x‖) a c b z) :
    ∃ U : Set (Fields.Space × ℝ), IsOpen U ∧ z ∈ U ∧
      U ⊆ {q | Contract.RegularMirrorBirth B q.1 q.2} := by
  refine ⟨_, isOpen_flowBracket hac hcb lip bound (smooth.norm ℝ nz), one, ?_⟩
  rintro ⟨x, h⟩ ⟨X, hx, ode, well, _⟩
  have cont : ContinuousOn (fun t => ‖B (X t)‖) (Icc a b) :=
    smooth.continuous.norm.comp_continuousOn fun t ht => (ode t ht).continuousAt.continuousWithinAt
  change Contract.RegularMirrorBirth B x h
  change X c = x at hx
  rw [← hx]
  apply well.regularBirth (speed := fun t => ‖B (X t)‖) hac hcb cont cont
  intro t ht
  refine ⟨norm_pos_iff.mpr (nz _), nz _, ?_⟩
  simpa only [GCLittlejohn.bhat, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (nz _)),
    one_smul] using ode t ht

/-- A single transverse well gives positive mass to true regular births under
every measure on Cartesian position and height that charges nonempty open sets. -/
theorem regular_birth_mass_of_flow {B : Fields.Space → Fields.Space} {K L : ℝ≥0}
    {a c b : ℝ} {z : Fields.Space × ℝ} (μ : Measure (Fields.Space × ℝ))
    [Measure.IsOpenPosMeasure μ] (hac : a < c) (hcb : c < b)
    (lip : LipschitzWith K B) (bound : ∀ x, ‖B x‖ ≤ L) (smooth : ContDiff ℝ 1 B)
    (nz : ∀ x, B x ≠ 0) (one : FlowBracket B (fun x => ‖B x‖) a c b z) :
    0 < μ {q | Contract.RegularMirrorBirth B q.1 q.2} := by
  obtain ⟨U, op, here, sub⟩ := regular_birth_open_neighborhood hac hcb lip bound smooth nz one
  exact (op.measure_pos μ ⟨z, here⟩).trans_le (measure_mono sub)

end PlasmaLean.Kinetic.MirrorWellPersistence
