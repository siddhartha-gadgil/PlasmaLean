/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Equilibrium.Slab
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# Strict-audit checks for `Kernel/Equilibrium` and `Kernel/Slab` (audit of 30 October 2026)

Added by the first strict kernel audit (`notes/audit/2026-10-30-kernel-audit.md`, commit
`cda8bd0`). Existing coverage (`Sanity/Equilibrium`, `Theory/Equilibrium/Slab`) gave the
degenerate case and concrete instances; this module adds the missing counterexamples and
risk-specific checks.

`ForceBalance`:
* counterexample: a perpendicular current and field with zero gradient datum
  (`forceBalance_rejects_perp`);
* orientation (`J × B`, not `B × J`): for an axial current `J = e_z` and the azimuthal field
  `B = e_y` it produces at `x = e_x`, the Lorentz force is the inward pinch force `-e_x`
  (`pinch_force_inward`), and the reversed orientation is rejected
  (`forceBalance_rejects_reversed`);
* vacuity hazard (regression for finding E-1): every pair `B, J` satisfies the law with
  `g := J × B` (`forceBalance_of_cross`), so the law has content only through a separate
  identification of `g` with the derivative of an actual pressure field;
* scaling: the law is bilinear (`forceBalance_smul_field`, `forceBalance_smul_current`).

`StaticSlab`:
* conservation: the total pressure `p + (B_x² + B_y²)/(2μ₀)` is constant
  (`slab_total_pressure_deriv`);
* counterexample: a compressive field `B_z = z` violates `∇ · B = 0`
  (`slab_rejects_compressive`);
* missing bound (regression for finding S-1): the laws admit a negative pressure
  (`slab_negative_pressure`).
-/

public section

noncomputable section

namespace PlasmaLean.Sanity.Audit
open Matrix PlasmaLean.Equilibrium

/-! ### `ForceBalance` -/

/-- **Counterexample.** `J = e_x`, `B = e_z` have nonzero Lorentz force `J × B = -e_y`, so they
do not balance a zero pressure gradient. -/
theorem forceBalance_rejects_perp : ¬ ForceBalance ![0, 0, 1] ![1, 0, 0] 0 := by
  intro h
  have h1 := congrFun h.balance 1
  simp [cross_apply] at h1

/-- **Orientation check (pinch force).** At `x = e_x`, an axial current `J = e_z` produces the
azimuthal field direction `B = e_y`; the kernel's force `J × B = -e_x` points toward the axis,
so the balancing pressure gradient points inward (pressure decreasing outward), as for a
Bennett pinch. -/
theorem pinch_force_inward : ForceBalance ![0, 1, 0] ![0, 0, 1] ![-1, 0, 0] := by
  refine ⟨?_⟩
  ext i
  fin_cases i <;> simp [cross_apply]

/-- **Orientation check.** The reversed convention `B × J = ∇p` is rejected: for the pinch
data, the outward gradient `+e_x` does not satisfy the kernel law. -/
theorem forceBalance_rejects_reversed : ¬ ForceBalance ![0, 1, 0] ![0, 0, 1] ![1, 0, 0] := by
  intro h
  have h0 := congrFun h.balance 0
  simp [cross_apply] at h0
  norm_num at h0

/-- **Regression (finding E-1, vacuity hazard).** Every field and current satisfy the pointwise
law with the datum `g := J × B`. `ForceBalance` therefore carries no physics unless `g` is
separately proved to be the derivative of a pressure field (as `Design/Solovev`,
`Design/LandremanEquilibrium` do with `pressure_hasFDerivAt`). -/
theorem forceBalance_of_cross (B J : Vec3) : ForceBalance B J (J ⨯₃ B) := ⟨rfl⟩

/-- **Scaling.** Force balance is linear in the field: scaling `B` scales the gradient. -/
theorem forceBalance_smul_field {B J g : Vec3} [h : ForceBalance B J g] (a : ℝ) :
    ForceBalance (a • B) J (a • g) := ⟨by rw [LinearMap.map_smul, h.balance]⟩

/-- **Scaling.** Force balance is linear in the current. -/
theorem forceBalance_smul_current {B J g : Vec3} [h : ForceBalance B J g] (a : ℝ) :
    ForceBalance B (a • J) (a • g) := ⟨by rw [LinearMap.map_smul₂, h.balance]⟩

/-! ### `StaticSlab` -/

/-- **Conservation (total pressure).** For the slab laws,
`d/dz [p + (B_x² + B_y²)/(2μ₀)] = 0`: force balance with the Ampère current is exactly
conservation of total (kinetic plus magnetic) pressure. -/
theorem slab_total_pressure_deriv {B J : ℝ → Vec3} {p : ℝ → ℝ} {μ₀ : ℝ}
    [h : StaticSlab B J p μ₀] (z : ℝ) :
    HasDerivAt (fun t => p t + (B t 0 ^ 2 + B t 1 ^ 2) / (2 * μ₀)) 0 z := by
  have hμ := h.permeability_pos
  have hB0 := ((h.field_differentiable 0) z).hasDerivAt
  have hB1 := ((h.field_differentiable 1) z).hasDerivAt
  have hp := (h.pressure_differentiable z).hasDerivAt
  have hbal : J z 0 * B z 1 - J z 1 * B z 0 = deriv p z := by
    simpa [cross_apply] using congrFun (h.balance z) 2
  have ha0 : -deriv (fun t => B t 1) z = μ₀ * J z 0 := by
    simpa [slabCurl] using congrFun (h.ampere z) 0
  have ha1 : deriv (fun t => B t 0) z = μ₀ * J z 1 := by
    simpa [slabCurl] using congrFun (h.ampere z) 1
  have hd := hp.add (((hB0.pow 2).add (hB1.pow 2)).div_const (2 * μ₀))
  convert hd using 1
  simp only [Nat.cast_ofNat]
  field_simp
  have e0 : deriv (fun t => B t 0) z = μ₀ * J z 1 := ha1
  have e1 : deriv (fun t => B t 1) z = -(μ₀ * J z 0) := by linarith
  rw [e0, e1, ← hbal]
  ring

/-- **Counterexample.** The compressive field `B = (0, 0, z)` violates `∇ · B = 0`, so it is
not a slab equilibrium for any current, pressure and `μ₀`. -/
theorem slab_rejects_compressive (J : ℝ → Vec3) (p : ℝ → ℝ) (μ₀ : ℝ) :
    ¬ StaticSlab (fun z => ![0, 0, z]) J p μ₀ := by
  intro h
  have := h.divergence 0
  simp at this

/-- The sheared field `B = (0, z, 0)` used in `slab_negative_pressure`. -/
@[expose] def shearField (z : ℝ) : Vec3 := ![0, z, 0]

/-- The Ampère current of `shearField` for `μ₀ = 1`: `J = (-1, 0, 0)`. -/
@[expose] def shearCurrent (_ : ℝ) : Vec3 := ![-1, 0, 0]

/-- The pressure `-z²/2` balancing `shearField` (total pressure `0`). -/
@[expose] def shearPressure (z : ℝ) : ℝ := -(z ^ 2 / 2)

/-- **Regression (finding S-1, missing bound).** The slab laws hold for the sheared field
`B = (0, z, 0)`, current `(-1, 0, 0)`, `μ₀ = 1` and pressure `-z²/2`, which is negative
away from `z = 0`: `StaticSlab` does not require `p ≥ 0`. -/
theorem slab_negative_pressure :
    StaticSlab shearField shearCurrent shearPressure 1 ∧ shearPressure 1 < 0 := by
  have hp : ∀ z, deriv shearPressure z = -z := fun z => by
    have : HasDerivAt shearPressure (-z) z := by
      have h := ((hasDerivAt_pow 2 z).div_const 2).neg
      convert h using 1
      · funext x; simp [shearPressure]
      · norm_num
    exact this.deriv
  refine ⟨⟨one_pos, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    fin_cases i
    · simp [shearField]
    · simp [shearField]
    · simp [shearField]
  · unfold shearPressure; fun_prop
  · intro z
    ext i
    fin_cases i <;> simp [cross_apply, shearField, shearCurrent, hp]
  · intro z; simp [shearField]
  · intro z
    have h1 : deriv (fun t => shearField t 1) z = 1 := by simp [shearField]
    have h0 : deriv (fun t => shearField t 0) z = 0 := by simp [shearField]
    ext i
    fin_cases i <;> simp [slabCurl, h0, h1, shearCurrent]
  · norm_num [shearPressure]

end PlasmaLean.Sanity.Audit
