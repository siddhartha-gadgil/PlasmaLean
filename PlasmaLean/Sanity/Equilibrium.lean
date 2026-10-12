/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Equilibrium
public import Mathlib.Tactic.NormNum

/-! # Nonvacuity and limiting cases for the algebraic force-balance kernel
These are pointwise witnesses, not assertions about spatial curls or coil fields.
-/
public section

namespace PlasmaLean.Sanity
open Matrix

/-- Any uniform magnetic datum with zero current and gradient satisfies force balance. -/
theorem uniformBalance (B : Vec3) : ForceBalance B 0 0 := ⟨by simp⟩

/-- Parallel nonzero magnetic/current data give an algebraic force-free witness. -/
theorem parallelBalance (B : Vec3) : ForceBalance B B 0 := ⟨cross_self B⟩

/-- Vanishing gradient does not force vanishing current, even for a nonzero field. -/
theorem force_free_nonvacuum :
    ∃ B J : Vec3, ForceBalance B J 0 ∧ B ≠ 0 ∧ J ≠ 0 := by
  refine ⟨![1, 0, 0], ![1, 0, 0], parallelBalance _, ?_, ?_⟩ <;>
    intro h <;> have hh := congrFun h 0 <;> norm_num at hh

/-- Zero field and zero current give a consistent degenerate model. -/
theorem zeroBalance : ForceBalance 0 0 0 := uniformBalance 0

end PlasmaLean.Sanity
