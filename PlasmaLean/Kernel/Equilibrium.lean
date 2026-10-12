/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Basic.Real.Basic

/-!
# Algebraic static-MHD kernel

This is a domain kernel, not an extension of Lean's logical kernel. `ForceBalance`
is a supplied pointwise SI law: J × B = grad p. The vector `g` is supplied gradient
data. An analytic bridge must identify it with the derivative of an actual pressure
field; this module claims neither PDE existence nor pressure-surface topology.
-/

public section

namespace PlasmaLean
open Matrix

/-- Cartesian three-component real data. No norm convention is imposed here. -/
abbrev Vec3 := Fin 3 → ℝ

/-- Pointwise static isotropic force balance, with SI magnetic/current/gradient data. -/
class ForceBalance (B J g : Vec3) : Prop where
  balance : J ⨯₃ B = g

/-- The magnetic field is tangent to supplied pressure-gradient data. -/
theorem field_tangency (B J g : Vec3) [ForceBalance B J g] : B ⬝ᵥ g = 0 := by
  rw [← ForceBalance.balance (B := B) (J := J) (g := g)]
  exact dot_cross_self J B

/-- The current is tangent to supplied pressure-gradient data. -/
theorem current_tangency (B J g : Vec3) [ForceBalance B J g] : J ⬝ᵥ g = 0 := by
  rw [← ForceBalance.balance (B := B) (J := J) (g := g)]
  exact dot_self_cross J B

/-- Zero pressure gradient is equivalent to zero Lorentz force under force balance. -/
theorem gradient_zero_iff_force_free (B J g : Vec3) [ForceBalance B J g] :
    g = 0 ↔ J ⨯₃ B = 0 := by
  rw [ForceBalance.balance (B := B) (J := J) (g := g)]

end PlasmaLean
