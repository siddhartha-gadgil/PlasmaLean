/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Slab
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Analytic Cartesian equilibria depending on one coordinate

On R³ these fields depend only on z. The curl is (-B_y', B_x', 0), divergence
is B_z', and pressure gradient is (0,0,p'). This restricted geometry gives actual
derivative witnesses for the algebraic kernel. It is not a toroidal confinement
domain. The sinusoidal force-free example is note 02's B0=L0=1 SI sanity case.
-/
public section

noncomputable section
namespace PlasmaLean.Equilibrium
open Matrix

/-- Analytic slab laws supply the algebraic force-balance interface. -/
theorem slab_forceBalance (B J : ℝ → Vec3) (p : ℝ → ℝ) (μ₀ z : ℝ)
    [StaticSlab B J p μ₀] : ForceBalance (B z) (J z) ![0,0,deriv p z] :=
  ⟨StaticSlab.balance (B := B) (J := J) (p := p) (μ₀ := μ₀) z⟩

/-- A spatially uniform field and constant pressure solve the actual slab equations. -/
theorem uniform_slab (B : Vec3) (p₀ μ₀ : ℝ) (hμ : 0 < μ₀) :
    StaticSlab (fun _ => B) (fun _ => 0) (fun _ => p₀) μ₀ := by
  constructor
  · exact hμ
  · intro i; exact differentiable_const _
  · exact differentiable_const _
  · intro z
    ext i
    fin_cases i <;> simp
  · intro z; simp
  · intro z; simp [slabCurl]

/-- Unit-amplitude, unit-length Beltrami example, periodic in z. -/
@[expose] def helicalSlab (z : ℝ) : Vec3 := ![Real.cos z, Real.sin z, 0]

/-- The field has unit squared Euclidean magnitude everywhere. -/
theorem helicalSlab_unit (z : ℝ) : helicalSlab z ⬝ᵥ helicalSlab z = 1 := by
  simp [helicalSlab, ← sq, Real.cos_sq_add_sin_sq]

/-- The actual curl of the helical slab is its negative. -/
theorem helicalSlab_curl (z : ℝ) : slabCurl helicalSlab z = -helicalSlab z := by
  ext i
  fin_cases i <;> simp [slabCurl, helicalSlab, Real.deriv_sin, Real.deriv_cos]

/-- A smooth zero-pressure equilibrium with nonzero parallel current. -/
theorem helicalSlab_equilibrium (μ₀ : ℝ) (hμ : 0 < μ₀) :
    StaticSlab helicalSlab (fun z => (-μ₀⁻¹) • helicalSlab z) (fun _ => 0) μ₀ := by
  constructor
  · exact hμ
  · intro i; fin_cases i
    · simp [helicalSlab]
    · simp [helicalSlab]
    · simp [helicalSlab]
  · exact differentiable_const _
  · intro z
    simp only [map_smul, LinearMap.smul_apply, cross_self, smul_zero, deriv_const]
    ext i
    fin_cases i <;> rfl
  · intro z; simp [helicalSlab]
  · intro z
    rw [helicalSlab_curl]
    ext i
    simp [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hμ)]

/-- The force-free current is nonzero at z=0, so this zero-pressure model is not vacuum. -/
theorem helicalSlab_current_nonzero (μ₀ : ℝ) (hμ : 0 < μ₀) :
    (-μ₀⁻¹) • helicalSlab 0 ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [helicalSlab, ne_of_gt hμ] at hh

end PlasmaLean.Equilibrium
