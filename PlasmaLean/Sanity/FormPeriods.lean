/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormPeriods
public import PlasmaLean.Sanity.FormTopology

/-!
# Sanity checks for `Theory/Fields/FormPeriods`

The field of a straight wire, `B = e_z × x/(x² + y²)`, on the complement of its axis.

* `wire_circulation`: its circulation around the unit circle is `2π` (Ampère's law for a wire
  carrying the current `2π/μ₀`).
* `wire_period`: the de Rham period of `B♭` on the class of that loop is `2π`.
* `wire_periodHom_ne_zero`: so the period homomorphism of `B♭` is not zero. (For a field with a
  potential it would be zero; this is the rejected case.)
* `gradient_circulation_eq_zero`-type accepted case: `uniform_circulation`: the circulation of a
  uniform field around the same loop is `0`.
-/

@[expose] public section

namespace PlasmaLean.Sanity.FormPeriods

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
open PlasmaLean.Sanity.FormTopology PlasmaLean.Contract
open TauCeti TopologicalSpace Topology
open scoped RealInnerProductSpace Manifold

/-- The unit circle, traversed once for `t ∈ [0, 1]`, as a curve in the wire region. -/
noncomputable def wireLoop (t : ℝ) : wireOpens :=
  ⟨unitCircle (2 * Real.pi * t), unitCircle_mem _⟩

/-- The wire field has unit length on the unit circle. -/
theorem wireField_unitCircle_inner (s : ℝ) :
    ⟪wireField (unitCircle s), wireField (unitCircle s)⟫ = 1 := by
  obtain ⟨a0, a1, a2⟩ := rotationField_coords (unitCircle s)
  have h0 : unitCircle s 0 = Real.cos s := by simp [unitCircle]
  have h1 : unitCircle s 1 = Real.sin s := by simp [unitCircle]
  rw [inner_coords3]
  simp only [wireField, wireR2_unitCircle, inv_one, one_smul, a0, a1, a2, h0, h1]
  nlinarith [Real.sin_sq_add_cos_sq s]

/-- The loop has velocity `2π B`. -/
theorem wireLoop_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t => (wireLoop t : Space))
      ((2 * Real.pi) • wireField (unitCircle (2 * Real.pi * t))) t := by
  have h := (unitCircle_fieldLine (2 * Real.pi * t)).scomp t
    ((hasDerivAt_id t).const_mul (2 * Real.pi))
  simp only [mul_one] at h
  exact h

/-- **Ampère's law for the wire**: the circulation around the unit circle is `2π`. -/
theorem wire_circulation :
    lineIntegral wireField (fun t => (wireLoop t : Space)) 0 1 = 2 * Real.pi := by
  have hI : ∀ t : ℝ, ⟪wireField (wireLoop t : Space), deriv (fun t => (wireLoop t : Space)) t⟫
      = 2 * Real.pi := fun t => by
    rw [(wireLoop_hasDerivAt t).deriv, inner_smul_right]
    change 2 * Real.pi * ⟪wireField (unitCircle (2 * Real.pi * t)),
      wireField (unitCircle (2 * Real.pi * t))⟫ = _
    rw [wireField_unitCircle_inner, mul_one]
  simp [lineIntegral, hI]

/-- The loop closes up. -/
theorem wireLoop_one : wireLoop 1 = wireLoop 0 := by
  apply Subtype.ext
  change unitCircle (2 * Real.pi * 1) = unitCircle (2 * Real.pi * 0)
  rw [mul_one, mul_zero, unitCircle_two_pi]

/-- The unit circle as a loop in the wire region, based at `wireLoop 0`. -/
noncomputable def wirePath : Path (wireLoop 0) (wireLoop 0) where
  toFun t := wireLoop t
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold unitCircle
    fun_prop
  source' := rfl
  target' := by simpa using wireLoop_one

/-- **The de Rham period of the wire form on the unit circle is `2π`.** -/
theorem wire_period :
    periodHom (onOpens wireOpens fun y => flat (wireField y)) (wireLoop 0)
      (Additive.ofMul (.of (.mk wirePath))) = 2 * Real.pi := by
  rw [periodHom_onOpens_flat (U := wireOpens) (c := wireLoop)
    (wireField_vacuum.contDiffOn.of_le (by norm_num)) wireField_vacuum.curl_eq_zero
    (by
      change ContDiff ℝ 1 fun t : ℝ => unitCircle (2 * Real.pi * t)
      unfold unitCircle
      fun_prop)
    (fun _ => rfl)]
  exact wire_circulation

/-- The period homomorphism of the wire form is not zero. -/
theorem wire_periodHom_ne_zero :
    periodHom (onOpens wireOpens fun y => flat (wireField y)) (wireLoop 0) ≠ 0 := by
  intro h
  have := wire_period
  rw [h] at this
  simp at this

/-- Accepted case: a uniform field has zero circulation around the same loop. -/
theorem uniform_circulation (B₀ : Space) :
    lineIntegral (fun _ => B₀) (fun t => (wireLoop t : Space)) 0 1 = 0 := by
  have h := lineIntegral_eq_sub_of_potential (B := fun _ : Space => B₀) (g := fun _ => B₀)
    (γ := fun t => (wireLoop t : Space)) (Φ := fun y => ⟪B₀, y⟫) 0 1
    (by
      change ContDiff ℝ 1 fun t : ℝ => unitCircle (2 * Real.pi * t)
      unfold unitCircle
      fun_prop)
    (fun _ => continuousAt_const) (fun _ => rfl)
    (fun t => (innerSL ℝ B₀).hasFDerivAt)
  rw [h]
  change ⟪B₀, (wireLoop 1 : Space)⟫ - ⟪B₀, (wireLoop 0 : Space)⟫ = 0
  rw [wireLoop_one, sub_self]

end PlasmaLean.Sanity.FormPeriods
