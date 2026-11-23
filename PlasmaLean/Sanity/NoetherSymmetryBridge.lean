/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherSymmetryBridge
public import PlasmaLean.Sanity.NoetherRotation

/-!
# Sanity checks for `Theory/Kinetic/NoetherSymmetryBridge`

The uniform field `B₀ e_z` in the symmetric gauge `symGauge B₀` and the Landau gauge
`landau B₀` of `Sanity/NoetherRotation` and `Sanity/NoetherLagrangian`.

* Accepted: `symGauge_rotZ_equivariant`: the symmetric gauge is equivariant under every
  finite rotation about the `z`-axis; `symGauge_infinitesimal_of_finite` recovers the
  infinitesimal equivariance from it.
* Accepted: `symGauge_flux`: `ψ = ⟪A, e_z × y⟫ = B₀ (x² + y²)/2`;
  `hasFDerivAt_symGauge_flux`, `symGauge_axisymmetricFlux`, `symGauge_symmetricFlux`: this
  explicit `ψ` and its gradient satisfy the hypotheses of the direct proofs for the uniform
  field; `symGauge_angular_momentum_conserved_direct`,
  `symGauge_angular_momentum_conserved_finite`: the conserved angular momentum by the direct
  route and from finite equivariance.
* Independent check: `symGauge_symmetricFlux_explicit`: the bridged hypothesis `SymmetricFlux`
  for the uniform field with the explicit gradient `G = B₀ (x, y, 0)`, proved in coordinates
  without the bridge; `symmetryFluxGrad_symGauge`: this `G` is
  `symmetryFluxGrad (symGauge B₀) rotGenZ`; `symGauge_symmetricFlux_of_explicit`: so
  `symGauge_symmetricFlux` holds by a second route that does not use the equivalence
  `symmetricFlux_symmetryFluxGrad_iff`.
* Rejected: `landau_not_rotZ_equivariant`: the Landau gauge is not equivariant under the
  rotation by `π/2` when `B₀ ≠ 0`; `landau_not_symmetricFlux`: it does not satisfy the bridged
  hypothesis either.
-/

@[expose] public section

namespace PlasmaLean.Sanity.NoetherSymmetryBridge

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open PlasmaLean.Sanity.NoetherLagrangian PlasmaLean.Sanity.NoetherRotation
open scoped RealInnerProductSpace

/-- **Accepted fixture**: the symmetric gauge is equivariant under every finite rotation
about the `z`-axis. -/
theorem symGauge_rotZ_equivariant (B₀ s : ℝ) (y : Space) :
    symGauge B₀ (rotZ s y) = rotZ s (symGauge B₀ y) := by
  obtain ⟨r0, r1, r2⟩ := rotZ_coords s y
  obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ (rotZ s y)
  obtain ⟨b0, b1, b2⟩ := symGauge_coords B₀ y
  obtain ⟨c0, c1, c2⟩ := rotZ_coords s (symGauge B₀ y)
  ext i
  fin_cases i
  · change symGauge B₀ (rotZ s y) 0 = rotZ s (symGauge B₀ y) 0
    rw [a0, c0, r1, b0, b1]
    ring
  · change symGauge B₀ (rotZ s y) 1 = rotZ s (symGauge B₀ y) 1
    rw [a1, c1, r0, b0, b1]
    ring
  · change symGauge B₀ (rotZ s y) 2 = rotZ s (symGauge B₀ y) 2
    rw [a2, c2, b2]

/-- The infinitesimal equivariance of the symmetric gauge, recovered from the finite one. -/
theorem symGauge_infinitesimal_of_finite (B₀ : ℝ) (y : Space) :
    fderiv ℝ (symGauge B₀) y (rotGenZ y) = rotGenZ (symGauge B₀ y) :=
  fderiv_rotGenZ_of_rotZ_equivariant (symGauge B₀).differentiable
    (symGauge_rotZ_equivariant B₀) y

/-- The flux function of the symmetric gauge: `⟪A, e_z × y⟫ = B₀ (x² + y²)/2`. -/
theorem symGauge_flux (B₀ : ℝ) (y : Space) :
    ⟪symGauge B₀ y, rotGenZ y⟫ = B₀ * (y 0 ^ 2 + y 1 ^ 2) / 2 := by
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ y
  rw [inner_coords3, h0, h1, h2, a0, a1, a2]
  ring

/-- The explicit `ψ = B₀ (x² + y²)/2` has gradient `symmetryFluxGrad (symGauge B₀) rotGenZ`. -/
theorem hasFDerivAt_symGauge_flux (B₀ : ℝ) (y : Space) :
    HasFDerivAt (fun z : Space => B₀ * (z 0 ^ 2 + z 1 ^ 2) / 2)
      (innerSL ℝ (symmetryFluxGrad (symGauge B₀) rotGenZ y)) y := by
  have h := hasFDerivAt_symmetryFlux (A := symGauge B₀) inner_rotGenZ_self
    ((symGauge B₀).differentiable y)
  have e : (fun z : Space => ⟪symGauge B₀ z, rotGenZ z⟫)
      = fun z : Space => B₀ * (z 0 ^ 2 + z 1 ^ 2) / 2 := funext (symGauge_flux B₀)
  rwa [e] at h

/-- **Accepted fixture**: the uniform field `B₀ e_z` satisfies the hypothesis
`AxisymmetricFlux` of `canonicalMomentum_conserved` with the gradient of
`ψ = B₀ (x² + y²)/2`. -/
theorem symGauge_axisymmetricFlux (B₀ : ℝ) :
    AxisymmetricFlux (fun _ => B₀ • coordVec 2) (symmetryFluxGrad (symGauge B₀) rotGenZ) :=
  axisymmetricFlux_of_equivariant (fun y => (curl_symGauge B₀ y).symm)
    (symGauge_equivariant B₀)

/-- **Accepted fixture**: the same in the form `SymmetricFlux` of
`noetherMomentum_conserved`. -/
theorem symGauge_symmetricFlux (B₀ : ℝ) :
    SymmetricFlux (fun _ => B₀ • coordVec 2) (symmetryFluxGrad (symGauge B₀) rotGenZ)
      (fun y => rotGenZ y) :=
  symmetricFlux_of_equivariant (fun y => (curl_symGauge B₀ y).symm) (symGauge_equivariant B₀)

/-- **Independent check**: the bridged hypothesis for the uniform field `B₀ e_z` with the
explicit gradient `G(y) = B₀ (x, y, 0)` of `ψ = B₀ (x² + y²)/2`, proved directly in
coordinates: `⟪e_z × y, v × B⟫ = −⟪G(y), v⟫`. The bridge theorems are not used. -/
theorem symGauge_symmetricFlux_explicit (B₀ : ℝ) :
    SymmetricFlux (fun _ => B₀ • coordVec 2)
      (fun y => B₀ • (y 0 • coordVec 0 + y 1 • coordVec 1)) (fun y => rotGenZ y) := by
  intro y v
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  obtain ⟨c0, c1, c2⟩ := cross_coords v (B₀ • coordVec 2)
  rw [inner_coords3, inner_coords3, h0, h1, h2, c0, c1, c2]
  simp
  ring

/-- **Independent check**: the gradient `symmetryFluxGrad (symGauge B₀) rotGenZ` of the bridge
is the explicit field `B₀ (x, y, 0)`, computed in coordinates. -/
theorem symmetryFluxGrad_symGauge (B₀ : ℝ) (y : Space) :
    symmetryFluxGrad (symGauge B₀) rotGenZ y = B₀ • (y 0 • coordVec 0 + y 1 • coordVec 1) := by
  refine ext_inner_right ℝ fun w => ?_
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ w
  obtain ⟨b0, b1, b2⟩ := symGauge_coords B₀ y
  obtain ⟨k0, k1, k2⟩ := rotGenZ_coords (symGauge B₀ y)
  rw [inner_symmetryFluxGrad, (symGauge B₀).fderiv, inner_coords3, inner_coords3,
    inner_coords3, h0, h1, h2, a0, a1, a2, k0, k1, k2, b0, b1]
  simp
  ring

/-- **Independent check**: `symGauge_symmetricFlux` by a second route, from the coordinate
computation `symGauge_symmetricFlux_explicit` and not from the equivalence
`symmetricFlux_symmetryFluxGrad_iff`. -/
theorem symGauge_symmetricFlux_of_explicit (B₀ : ℝ) :
    SymmetricFlux (fun _ => B₀ • coordVec 2) (symmetryFluxGrad (symGauge B₀) rotGenZ)
      (fun y => rotGenZ y) := by
  have h := symGauge_symmetricFlux_explicit B₀
  have e : symmetryFluxGrad (symGauge B₀) rotGenZ
      = fun y => B₀ • (y 0 • coordVec 0 + y 1 • coordVec 1) :=
    funext (symmetryFluxGrad_symGauge B₀)
  rwa [e]

/-- **Accepted fixture**: conservation of `m (x v_y − y v_x) + q B₀ (x² + y²)/2` in the
uniform field, from the direct theorem `canonicalMomentum_conserved` with the bridged
hypothesis. -/
theorem symGauge_angular_momentum_conserved_direct {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) :=
  canonicalMomentum_conserved h (hasFDerivAt_symGauge_flux B₀) (symGauge_axisymmetricFlux B₀)
    s t

/-- **Accepted fixture**: the same conservation law from equivariance under the finite
rotations, through `canonicalMomentum_conserved_of_rotZ_equivariant`. -/
theorem symGauge_angular_momentum_conserved_finite {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) := by
  have key := canonicalMomentum_conserved_of_rotZ_equivariant (A := symGauge B₀) h
    (symGauge B₀).differentiable (fun y => (curl_symGauge B₀ y).symm)
    (symGauge_rotZ_equivariant B₀) s t
  simp only [canonicalMomentum, angularZ, symGauge_flux] at key
  exact key

/-- **Rejected fixture**: the Landau gauge is not equivariant under the rotation by `π/2`
about the `z`-axis when `B₀ ≠ 0`. -/
theorem landau_not_rotZ_equivariant {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ ∀ y : Space, landau B₀ (rotZ (Real.pi / 2) y) = rotZ (Real.pi / 2) (landau B₀ y) := by
  intro h
  have h1 : landau B₀ (rotZ (Real.pi / 2) (coordVec 0)) 0
      = rotZ (Real.pi / 2) (landau B₀ (coordVec 0)) 0 := by rw [h (coordVec 0)]
  obtain ⟨c0, -, -⟩ := rotZ_coords (Real.pi / 2) (landau B₀ (coordVec 0))
  rw [c0, landau_apply, landau_apply] at h1
  have h2 : B₀ = 0 := by
    simpa using h1.symm
  exact hB h2

/-- **Rejected fixture**: the Landau gauge does not satisfy the bridged hypothesis
`SymmetricFlux` with `G = symmetryFluxGrad (landau B₀) rotGenZ` when `B₀ ≠ 0`, although its
curl is the same uniform field. -/
theorem landau_not_symmetricFlux {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ SymmetricFlux (fun _ => B₀ • coordVec 2) (symmetryFluxGrad (landau B₀) rotGenZ)
      (fun y => rotGenZ y) := fun h =>
  landau_not_equivariant hB
    ((symmetricFlux_symmetryFluxGrad_iff (fun y => (curl_landau B₀ y).symm)).mp h)

end PlasmaLean.Sanity.NoetherSymmetryBridge
