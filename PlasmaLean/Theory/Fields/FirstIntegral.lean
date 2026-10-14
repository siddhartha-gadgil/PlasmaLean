/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.BiotSavart
public import PlasmaLean.Theory.Kinetic.ApproximateInvariant
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact first integrals and all-time field-line barriers

A differentiable function ψ is a first integral of a vector field B on a region when
B · ∇ψ = 0 there, written as `fderiv ℝ ψ x (B x) = 0`. Along any supplied classical
field line γ' = B(γ) the value of ψ is then constant, so the line never leaves the
level set or any sublevel set {ψ ≤ c} containing its initial point. A bounded
sublevel set therefore gives a genuine all-time (forward) confinement statement for
field lines: a `FieldLineConfined` barrier in the sense of note 00.

Scope: the field-line parameter is not particle time, and no existence of field lines
is postulated (statements quantify over supplied curves). Field-line confinement is
distinct from guiding-centre or full-orbit particle confinement, from MHD equilibrium,
and from stability. A Clebsch field ∇ψ × ∇χ is a first-integral field for ψ and χ; it
is an analytic model field here, with no claim that it is curl-free or coil-produced.

The sanity theorem `uniform_no_bounded_firstIntegral` shows that a nonzero uniform
field admits no first integral with a bounded nonempty sublevel set, consistent with
`PlasmaLean.Sanity.no_forever_probe_fieldLine`.
-/
public section
noncomputable section
namespace PlasmaLean.Fields
open Matrix WithLp

/-- ψ is an exact first integral of B on U: differentiable there with B · ∇ψ = 0. -/
@[expose] def FirstIntegralOn (B : Space → Space) (ψ : Space → ℝ) (U : Set Space) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ fderiv ℝ ψ x (B x) = 0

/-- A classical forward field line of B: γ' = B(γ) at every nonnegative parameter. -/
@[expose] def IsForwardFieldLine (B : Space → Space) (γ : ℝ → Space) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt γ (B (γ t)) t

/-- The set S is a forward field-line barrier: every supplied forward field line of B
starting in S remains in S for all nonnegative parameter values. -/
@[expose] def FieldLineConfined (B : Space → Space) (S : Set Space) : Prop :=
  ∀ γ : ℝ → Space, IsForwardFieldLine B γ → γ 0 ∈ S → ∀ t, 0 ≤ t → γ t ∈ S

/-- Characterization through the gradient: B · ∇ψ = 0 in the Euclidean inner product. -/
theorem firstIntegralOn_iff_inner (B : Space → Space) (ψ : Space → ℝ) (U : Set Space) :
    FirstIntegralOn B ψ U ↔
      ∀ x ∈ U, DifferentiableAt ℝ ψ x ∧ inner ℝ (gradient ψ x) (B x) = 0 := by
  simp only [FirstIntegralOn, inner_gradient_left]

/-- Degenerate case: a constant function is a first integral of every field. -/
theorem firstIntegral_const (B : Space → Space) (k : ℝ) (U : Set Space) :
    FirstIntegralOn B (fun _ => k) U :=
  fun _ _ => ⟨differentiableAt_const k, by simp⟩

/-- Degenerate case: every differentiable function is a first integral of the zero field. -/
theorem firstIntegral_zero_field (ψ : Space → ℝ) (U : Set Space)
    (hψ : ∀ x ∈ U, DifferentiableAt ℝ ψ x) : FirstIntegralOn (fun _ => 0) ψ U :=
  fun x hx => ⟨hψ x hx, by simp⟩

/-- First integrals of two fields are first integrals of their sum. -/
theorem FirstIntegralOn.add {B₁ B₂ : Space → Space} {ψ : Space → ℝ} {U : Set Space}
    (h₁ : FirstIntegralOn B₁ ψ U) (h₂ : FirstIntegralOn B₂ ψ U) :
    FirstIntegralOn (fun x => B₁ x + B₂ x) ψ U :=
  fun x hx => ⟨(h₁ x hx).1, by simp [map_add, (h₁ x hx).2, (h₂ x hx).2]⟩

/-- First integrals are preserved by pointwise scalar rescaling of the field. -/
theorem FirstIntegralOn.smul {B : Space → Space} {ψ : Space → ℝ} {U : Set Space}
    (h : FirstIntegralOn B ψ U) (f : Space → ℝ) :
    FirstIntegralOn (fun x => f x • B x) ψ U :=
  fun x hx => ⟨(h x hx).1, by simp [map_smul, (h x hx).2]⟩

/-- Restriction of a first integral to a smaller region. -/
theorem FirstIntegralOn.mono {B : Space → Space} {ψ : Space → ℝ} {U V : Set Space}
    (h : FirstIntegralOn B ψ U) (hVU : V ⊆ U) : FirstIntegralOn B ψ V :=
  fun x hx => h x (hVU hx)

/-- Finite-parameter conservation: if the field line stays in U on [0,T], then ψ is
constant along it there. -/
theorem firstIntegral_conserved {B : Space → Space} {ψ : Space → ℝ} {U : Set Space}
    (hψ : FirstIntegralOn B ψ U) {γ : ℝ → Space} {T t : ℝ}
    (hγ : ∀ s ∈ Set.Icc 0 T, HasDerivAt γ (B (γ s)) s)
    (stays : ∀ s ∈ Set.Icc 0 T, γ s ∈ U) (ht : t ∈ Set.Icc 0 T) :
    ψ (γ t) = ψ (γ 0) := by
  have hd : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun u => ψ (γ u)) 0 s := by
    intro s hs
    have h := ((hψ (γ s) (stays s hs)).1.hasFDerivAt).comp_hasDerivAt s (hγ s hs)
    rwa [(hψ (γ s) (stays s hs)).2] at h
  exact Kinetic.exact_invariant hd (fun _ _ => by simp) ht

/-- A global first integral is conserved along every forward field line. -/
theorem firstIntegral_conserved_forward {B : Space → Space} {ψ : Space → ℝ}
    (hψ : FirstIntegralOn B ψ Set.univ) {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ)
    {t : ℝ} (ht : 0 ≤ t) : ψ (γ t) = ψ (γ 0) :=
  firstIntegral_conserved hψ (T := t) (fun s hs => hγ s hs.1) (fun _ _ => trivial) ⟨ht, le_rfl⟩

/-- Every sublevel set of a global first integral is a forward field-line barrier. -/
theorem sublevel_confined {B : Space → Space} {ψ : Space → ℝ}
    (hψ : FirstIntegralOn B ψ Set.univ) (c : ℝ) :
    FieldLineConfined B {x | ψ x ≤ c} := by
  intro γ hγ h0 t ht
  simp only [Set.mem_ofPred_eq] at h0 ⊢
  rw [firstIntegral_conserved_forward hψ hγ ht]
  exact h0

/-- Every level set of a global first integral is a forward field-line barrier. -/
theorem level_confined {B : Space → Space} {ψ : Space → ℝ}
    (hψ : FirstIntegralOn B ψ Set.univ) (c : ℝ) :
    FieldLineConfined B {x | ψ x = c} := by
  intro γ hγ h0 t ht
  simp only [Set.mem_ofPred_eq] at h0 ⊢
  rw [firstIntegral_conserved_forward hψ hγ ht]
  exact h0

/-- Barriers are preserved under intersection. -/
theorem FieldLineConfined.inter {B : Space → Space} {S S' : Set Space}
    (h : FieldLineConfined B S) (h' : FieldLineConfined B S') :
    FieldLineConfined B (S ∩ S') :=
  fun γ hγ h0 t ht => ⟨h γ hγ h0.1 t ht, h' γ hγ h0.2 t ht⟩

/-- Degenerate case: the whole space is trivially a barrier. -/
theorem fieldLineConfined_univ (B : Space → Space) : FieldLineConfined B Set.univ :=
  fun _ _ _ _ _ => trivial

/-- All-time boundedness: a field line starting in a sublevel set contained in a
closed ball stays in that ball for every nonnegative parameter. -/
theorem fieldLine_bounded {B : Space → Space} {ψ : Space → ℝ}
    (hψ : FirstIntegralOn B ψ Set.univ) {c R : ℝ}
    (hball : {x | ψ x ≤ c} ⊆ Metric.closedBall 0 R) {γ : ℝ → Space}
    (hγ : IsForwardFieldLine B γ) (h0 : ψ (γ 0) ≤ c) {t : ℝ} (ht : 0 ≤ t) :
    ‖γ t‖ ≤ R := by
  have h := hball (sublevel_confined hψ c γ hγ h0 t ht)
  simpa using h

/-- The straight line x + t v is a forward field line of the uniform field v. -/
theorem uniform_fieldLine (v x : Space) :
    IsForwardFieldLine (fun _ => v) (fun t => x + t • v) := by
  intro t _
  simpa using ((hasDerivAt_id t).smul_const v).const_add x

/-- Sanity: a nonzero uniform field has no global first integral with a bounded
nonempty sublevel set, so it has no bounded barrier of this form. This agrees with
the probe-escape theorem: a field with a fixed nonvanishing direction cannot trap
field lines forever. -/
theorem uniform_no_bounded_firstIntegral {v : Space} (hv : v ≠ 0) {ψ : Space → ℝ}
    (hψ : FirstIntegralOn (fun _ => v) ψ Set.univ) {c R : ℝ} {x : Space}
    (hx : ψ x ≤ c) : ¬ {y | ψ y ≤ c} ⊆ Metric.closedBall 0 R := by
  intro hball
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set t := (R + ‖x‖ + 1) / ‖v‖ with htdef
  have hR : 0 ≤ R := le_trans (norm_nonneg _) (by simpa using hball hx)
  have ht : 0 ≤ t := by positivity
  have hb := fieldLine_bounded hψ hball (uniform_fieldLine v x) (by simpa using hx) ht
  have htv : ‖t • v‖ = R + ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg ht, htdef, div_mul_cancel₀ _ hvpos.ne']
  have htri : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    have h := norm_sub_le (x + t • v) x
    simpa [add_sub_cancel_left] using h
  linarith

/-- The Clebsch field ∇ψ × ∇χ built from two scalar potentials. -/
@[expose] def clebschField (ψ χ : Space → ℝ) (x : Space) : Space :=
  cross (gradient ψ x) (gradient χ x)

/-- The Euclidean inner product agrees with the coordinate dot product. -/
theorem inner_eq_dot (u v : Space) : inner ℝ u v = ofLp u ⬝ᵥ ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The field ∇ψ × W for an arbitrary vector field W; Clebsch fields are W = ∇χ. -/
@[expose] def gradCross (ψ : Space → ℝ) (W : Space → Space) (x : Space) : Space :=
  cross (gradient ψ x) (W x)

/-- Clebsch fields are the gradient case of `gradCross`. -/
theorem clebschField_eq_gradCross (ψ χ : Space → ℝ) :
    clebschField ψ χ = gradCross ψ (gradient χ) := rfl

/-- Any field ∇ψ × W is tangent to the level sets of ψ. -/
theorem gradCross_firstIntegral (ψ : Space → ℝ) (W : Space → Space) (U : Set Space)
    (hψ : ∀ x ∈ U, DifferentiableAt ℝ ψ x) : FirstIntegralOn (gradCross ψ W) ψ U := by
  rw [firstIntegralOn_iff_inner]
  intro x hx
  refine ⟨hψ x hx, ?_⟩
  rw [inner_eq_dot, gradCross, cross]
  simp [dot_self_cross]

/-- A Clebsch field is tangent to the level sets of its first potential. -/
theorem clebsch_firstIntegral_left (ψ χ : Space → ℝ) (U : Set Space)
    (hψ : ∀ x ∈ U, DifferentiableAt ℝ ψ x) : FirstIntegralOn (clebschField ψ χ) ψ U :=
  gradCross_firstIntegral ψ (gradient χ) U hψ

/-- A Clebsch field is tangent to the level sets of its second potential. -/
theorem clebsch_firstIntegral_right (ψ χ : Space → ℝ) (U : Set Space)
    (hχ : ∀ x ∈ U, DifferentiableAt ℝ χ x) : FirstIntegralOn (clebschField ψ χ) χ U := by
  rw [firstIntegralOn_iff_inner]
  intro x hx
  refine ⟨hχ x hx, ?_⟩
  rw [inner_eq_dot, clebschField, cross]
  simp [dot_cross_self]

/-- Every sublevel set of a globally differentiable ψ is a barrier for ∇ψ × ∇χ. -/
theorem clebsch_sublevel_confined (ψ χ : Space → ℝ) (hψ : Differentiable ℝ ψ) (c : ℝ) :
    FieldLineConfined (clebschField ψ χ) {x | ψ x ≤ c} :=
  sublevel_confined (clebsch_firstIntegral_left ψ χ _ (fun x _ => hψ x)) c

end PlasmaLean.Fields
