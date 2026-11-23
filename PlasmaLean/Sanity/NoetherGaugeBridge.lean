/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherGaugeBridge
public import PlasmaLean.Sanity.NoetherSymmetryBridge

/-!
# Sanity checks for `Theory/Kinetic/NoetherGaugeBridge`

The uniform field `B₀ e_z` in the symmetric gauge `symGauge B₀` and the Landau gauge
`landau B₀` of `Sanity/NoetherRotation` and `Sanity/NoetherLagrangian`.

* Accepted: `landau_symmetricFlux_gauge`, `landau_axisymmetricFlux_gauge`: the Landau gauge
  with the gradient of `landauGauge B₀` as gauge term satisfies the bridged hypotheses of the
  direct proofs; `landau_angular_momentum_conserved_direct`: the direct route gives the same
  conserved quantity as `landau_angular_momentum_conserved`.
* Gauge transformation: `landau_eq_symGauge_add_gradient`: `landau = symGauge + ∇Λ` with
  `Λ = gaugeFn B₀ = B₀ x y / 2` (`hasFDerivAt_gaugeFn`); `curl_landau_of_symGauge`: the curl
  is unchanged; `gauge_term_landau`: the transformed gauge term `0 + ⟪∇Λ, e_z × y⟫` is
  `landauGauge B₀`; `landau_defect_of_gauge_transformation`: the transformed defect is the
  defect of the Landau gauge; `landau_angular_momentum_conserved_gauge_transformation`: the
  conserved quantity obtained from the symmetric gauge by the gauge transformation.
* Rejected: `landau_not_symmetricFlux_zero_gauge`, `landau_not_symmetricFlux_neg_gauge`: with
  gauge term `0` or `−landauGauge` the bridged hypothesis fails for `B₀ ≠ 0`.
* Finite symmetry: `symGauge_commute`, `symGauge_rotZ_equivariant_of_commute`: the symmetric
  gauge commutes with `rotGenZ`, hence with every rotation; `landau_not_commute`: the Landau
  gauge does not.
-/

@[expose] public section

namespace PlasmaLean.Sanity.NoetherGaugeBridge

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open PlasmaLean.Sanity.NoetherLagrangian PlasmaLean.Sanity.NoetherRotation
open PlasmaLean.Sanity.NoetherSymmetryBridge
open scoped RealInnerProductSpace

/-- The defect `DA(y)(e_z × y) − e_z × A(y)` of the Landau gauge; it is the gradient of
`landauGauge B₀`. -/
noncomputable def landauDefect (B₀ : ℝ) (y : Space) : Space :=
  landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y)

/-- **Accepted fixture**: the uniform field satisfies the bridged hypothesis `SymmetricFlux`
for the Landau gauge with the gauge term `landauGauge B₀`. -/
theorem landau_symmetricFlux_gauge (B₀ : ℝ) :
    SymmetricFlux (fun _ => B₀ • coordVec 2)
      (fun y => symmetryFluxGrad (landau B₀) rotGenZ y - landauDefect B₀ y)
      (fun y => rotGenZ y) :=
  (symmetricFlux_gauge_iff (fun y => (curl_landau B₀ y).symm)).mpr
    (landau_equivariant_gauge B₀)

/-- **Accepted fixture**: the same in the form `AxisymmetricFlux` of
`canonicalMomentum_conserved`. -/
theorem landau_axisymmetricFlux_gauge (B₀ : ℝ) :
    AxisymmetricFlux (fun _ => B₀ • coordVec 2)
      (fun y => symmetryFluxGrad (landau B₀) rotGenZ y - landauDefect B₀ y) :=
  (axisymmetricFlux_gauge_iff (fun y => (curl_landau B₀ y).symm)).mpr
    (landau_equivariant_gauge B₀)

/-- The potential of the Landau gauge with its gauge term:
`⟪A, e_z × y⟫ − χ = B₀ (x² + y²)/2`. -/
theorem landau_flux (B₀ : ℝ) (y : Space) :
    ⟪landau B₀ y, rotGenZ y⟫ - landauGauge B₀ y = B₀ * (y 0 ^ 2 + y 1 ^ 2) / 2 := by
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  rw [inner_coords3, h0, h1, h2, landauGauge, landau_apply]
  simp
  ring

/-- **Accepted fixture**: the direct route (`canonicalMomentum_conserved` with the bridged
hypothesis) gives the same conserved quantity as `landau_angular_momentum_conserved`. -/
theorem landau_angular_momentum_conserved_direct {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) := by
  have key := canonicalMomentum_rotGenZ_gauge_conserved_direct (A := landau B₀) h
    (landau B₀).differentiable (fun y => (curl_landau B₀ y).symm)
    (hasFDerivAt_landauGauge B₀) (landau_equivariant_gauge B₀) s t
  simp only [canonicalMomentum, angularZ, landau_flux] at key
  exact key

/-! ### The gauge transformation from the symmetric to the Landau gauge -/

/-- The gauge function `Λ = B₀ x y / 2` taking the symmetric gauge to the Landau gauge. -/
noncomputable def gaugeFn (B₀ : ℝ) (y : Space) : ℝ := B₀ * (y 0 * y 1) / 2

/-- The gradient `∇Λ = (B₀/2)(y, x, 0)` of `gaugeFn`, as the difference of the two gauges. -/
noncomputable def gaugeGrad (B₀ : ℝ) : Space →L[ℝ] Space := landau B₀ - symGauge B₀

/-- Components of `gaugeGrad`. -/
theorem gaugeGrad_coords (B₀ : ℝ) (y : Space) :
    gaugeGrad B₀ y 0 = B₀ / 2 * y 1 ∧ gaugeGrad B₀ y 1 = B₀ / 2 * y 0
      ∧ gaugeGrad B₀ y 2 = 0 := by
  obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ y
  refine ⟨?_, ?_, ?_⟩
  · simp [gaugeGrad, landau_apply, a0]
  · simp [gaugeGrad, landau_apply, a1]
    ring
  · simp [gaugeGrad, landau_apply, a2]

/-- `gaugeFn B₀` has gradient `gaugeGrad B₀`. -/
theorem hasFDerivAt_gaugeFn (B₀ : ℝ) (y : Space) :
    HasFDerivAt (gaugeFn B₀) (innerSL ℝ (gaugeGrad B₀ y)) y := by
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt (x := y)
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).hasFDerivAt (x := y)
  have h := (p0.mul p1).const_mul (B₀ / 2)
  obtain ⟨d0, d1, d2⟩ := gaugeGrad_coords B₀ y
  convert h using 1
  · funext z
    simp [gaugeFn]
    ring
  · ext w
    rw [innerSL_apply_apply, inner_coords3, d0, d1, d2]
    simp
    ring

/-- The Landau gauge is the symmetric gauge plus the gradient of `gaugeFn`. -/
theorem landau_eq_symGauge_add_gradient (B₀ : ℝ) (y : Space) :
    landau B₀ y = symGauge B₀ y + gaugeGrad B₀ y := by
  simp [gaugeGrad]

/-- The curl of the Landau gauge, from the curl of the symmetric gauge and
`fieldCurl_add_gradient`. -/
theorem curl_landau_of_symGauge (B₀ : ℝ) (y : Space) :
    fieldCurl (fun z => symGauge B₀ z + gaugeGrad B₀ z) y = B₀ • coordVec 2 := by
  rw [fieldCurl_add_gradient ((symGauge B₀).differentiable y) (hasFDerivAt_gaugeFn B₀)
    ((gaugeGrad B₀).differentiable y), curl_symGauge]

/-- **The gauge term is reproduced.** The symmetric gauge has gauge term `0`; the rule
`χ' = χ + ⟪∇Λ, e_z × y⟫` of `hasFDerivAt_gauge_term_add_gradient` gives `landauGauge B₀`. -/
theorem gauge_term_landau (B₀ : ℝ) (y : Space) :
    (0 : ℝ) + ⟪gaugeGrad B₀ y, rotGenZ y⟫ = landauGauge B₀ y := by
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  obtain ⟨d0, d1, d2⟩ := gaugeGrad_coords B₀ y
  rw [inner_coords3, h0, h1, h2, d0, d1, d2, landauGauge]
  ring

/-- **The defect is reproduced.** The rule `G' = G + (DH(K y) − K(H y))` of
`equivariant_gauge_add_gradient`, applied to the symmetric gauge (`G = 0`), gives the defect
of the Landau gauge. -/
theorem landau_defect_of_gauge_transformation (B₀ : ℝ) (y : Space) :
    (0 : Space) + (fderiv ℝ (gaugeGrad B₀) y (rotGenZ y) - rotGenZ (gaugeGrad B₀ y))
      = landauDefect B₀ y := by
  have hs := symGauge_equivariant B₀ y
  rw [(symGauge B₀).fderiv] at hs
  rw [(gaugeGrad B₀).fderiv, landauDefect, zero_add]
  simp only [gaugeGrad, sub_apply, map_sub, hs]
  abel

/-- **Gauge-transformation fixture**: starting from the symmetric gauge (gauge term `0`) and
transforming by `∇Λ`, `noetherMomentum_linear_gauge_conserved_add_gradient` gives the
conservation of the same quantity `m (x v_y − y v_x) + q B₀ (x² + y²)/2`. -/
theorem landau_angular_momentum_conserved_gauge_transformation {m q B₀ : ℝ}
    {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) := by
  have key := noetherMomentum_linear_gauge_conserved_add_gradient (A := symGauge B₀)
    (G := fun _ => 0) (χ := fun _ => 0) (H := fun y => gaugeGrad B₀ y) (Λ := gaugeFn B₀)
    (K := rotGenZ) h inner_rotGenZ_self (symGauge B₀).differentiable
    (fun y => (curl_symGauge B₀ y).symm)
    (fun y => by simpa using hasFDerivAt_const (0 : ℝ) y)
    (fun y => by simpa using symGauge_equivariant B₀ y)
    (hasFDerivAt_gaugeFn B₀) (gaugeGrad B₀).differentiable s t
  have hψ : ∀ y : Space, ⟪symGauge B₀ y + gaugeGrad B₀ y, rotGenZ y⟫
      - (0 + ⟪gaugeGrad B₀ y, rotGenZ y⟫) = B₀ * (y 0 ^ 2 + y 1 ^ 2) / 2 := fun y => by
    rw [inner_add_left, symGauge_flux]
    ring
  simp only [noetherMomentum, inner_rotGenZ, angularZ, hψ] at key
  exact key

/-! ### Rejected gauge terms -/

/-- **Rejected fixture**: with gauge term `0` the bridged hypothesis fails for the Landau
gauge when `B₀ ≠ 0`. -/
theorem landau_not_symmetricFlux_zero_gauge {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ SymmetricFlux (fun _ => B₀ • coordVec 2)
      (fun y => symmetryFluxGrad (landau B₀) rotGenZ y - (fun _ => (0 : Space)) y)
      (fun y => rotGenZ y) := fun h =>
  landau_not_equivariant hB fun y => by
    simpa using (symmetricFlux_gauge_iff (fun y => (curl_landau B₀ y).symm)).mp h y

/-- **Rejected fixture**: with the gauge term of the wrong sign, `−landauGauge B₀` (gradient
`−landauDefect B₀`), the bridged hypothesis fails for the Landau gauge when `B₀ ≠ 0`. -/
theorem landau_not_symmetricFlux_neg_gauge {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ SymmetricFlux (fun _ => B₀ • coordVec 2)
      (fun y => symmetryFluxGrad (landau B₀) rotGenZ y - (fun z => -landauDefect B₀ z) y)
      (fun y => rotGenZ y) := fun h => by
  have h1 := (symmetricFlux_gauge_iff (fun y => (curl_landau B₀ y).symm)).mp h (coordVec 0)
  rw [landau_equivariant_gauge B₀ (coordVec 0), add_right_inj] at h1
  have h2 : landauDefect B₀ (coordVec 0) 0 = 0 := by
    have h3 : landauDefect B₀ (coordVec 0) = 0 := by
      have h4 : landauDefect B₀ (coordVec 0) = -landauDefect B₀ (coordVec 0) := h1
      have h5 : (2 : ℝ) • landauDefect B₀ (coordVec 0) = 0 := by
        rw [two_smul]
        nth_rewrite 2 [h4]
        exact add_neg_cancel _
      exact (smul_eq_zero.mp h5).resolve_left two_ne_zero
    rw [h3]
    rfl
  have h6 := (landau_defect_coords B₀ (coordVec 0)).1
  rw [landauDefect] at h2
  rw [h2] at h6
  have h7 : B₀ = 0 := by simpa using h6.symm
  exact hB h7

/-! ### Finite symmetry of linear potentials -/

/-- The symmetric gauge commutes with the generator `rotGenZ`. -/
theorem symGauge_commute (B₀ : ℝ) (y : Space) :
    symGauge B₀ (rotGenZ y) = rotGenZ (symGauge B₀ y) :=
  (clm_fderiv_equivariant_iff (symGauge B₀) (fun z => rotGenZ z) y).mp
    (symGauge_equivariant B₀ y)

/-- **Accepted fixture**: equivariance of the symmetric gauge under every finite rotation,
derived from the commutation with the generator by `rotZ_equivariant_of_commute`. -/
theorem symGauge_rotZ_equivariant_of_commute (B₀ s : ℝ) (y : Space) :
    symGauge B₀ (rotZ s y) = rotZ s (symGauge B₀ y) :=
  rotZ_equivariant_of_commute (symGauge B₀) (symGauge_commute B₀) s y

/-- **Rejected fixture**: the Landau gauge does not commute with `rotGenZ` when `B₀ ≠ 0`, so
`rotZ_equivariant_of_commute` does not apply to it. -/
theorem landau_not_commute {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ ∀ y : Space, landau B₀ (rotGenZ y) = rotGenZ (landau B₀ y) := fun h =>
  landau_not_equivariant hB fun y =>
    (clm_fderiv_equivariant_iff (landau B₀) (fun z => rotGenZ z) y).mpr (h y)

end PlasmaLean.Sanity.NoetherGaugeBridge
