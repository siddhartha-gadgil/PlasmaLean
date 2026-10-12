/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Equilibrium
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Static MHD in a Cartesian slab

Fields and pressure depend only on the Cartesian coordinate z. Derivatives here
are actual real derivatives, not uninterpreted symbols. The supplied laws are
restricted to this model; they do not assert existence of a toroidal equilibrium.
Dimensional inputs use one consistent unit system (SI in the examples).
-/
public section

noncomputable section
namespace PlasmaLean.Equilibrium
open Matrix

/-- Cartesian curl for a field depending only on the third coordinate. -/
@[expose] def slabCurl (B : ℝ → Vec3) (z : ℝ) : Vec3 :=
  ![-deriv (fun t => B t 1) z, deriv (fun t => B t 0) z, 0]

/-- Supplied static MHD laws in the differentiable, z-dependent class. -/
class StaticSlab (B J : ℝ → Vec3) (p : ℝ → ℝ) (μ₀ : ℝ) : Prop where
  permeability_pos : 0 < μ₀
  field_differentiable : ∀ i, Differentiable ℝ (fun z => B z i)
  pressure_differentiable : Differentiable ℝ p
  balance : ∀ z, J z ⨯₃ B z = ![0, 0, deriv p z]
  divergence : ∀ z, deriv (fun t => B t 2) z = 0
  ampere : ∀ z, slabCurl B z = μ₀ • J z

end PlasmaLean.Equilibrium
