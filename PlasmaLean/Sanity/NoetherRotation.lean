/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherRotation
public import PlasmaLean.Sanity.NoetherLagrangian

/-!
# Sanity checks for `Theory/Kinetic/NoetherRotation`

The uniform field `B₀ e_z` in the symmetric gauge `A = (B₀/2)(−y, x, 0)` and in the Landau
gauge `A = B₀ x e_y` of `Sanity/NoetherLagrangian`.

* `curl_symGauge`: `∇ × A = B₀ e_z` for the symmetric gauge; `symGauge_equivariant`: it is
  equivariant under the rotations about the `z`-axis.
* Accepted: `symGauge_angular_momentum_conserved`: along every Lorentz orbit in the uniform
  field, `m (x v_y − y v_x) + q B₀ (x² + y²)/2` is constant.
* Hypothesis check: `landau_not_equivariant`: the Landau gauge is not equivariant under the
  rotation (for `B₀ ≠ 0`), so `canonicalMomentum_rotGenZ_conserved` does not apply to it.
* Gauge term: `landau_equivariant_gauge`: the Landau gauge is equivariant up to the gradient
  of `χ = B₀ (x² − y²)/2`, and `landau_angular_momentum_conserved` recovers the same
  conserved quantity from `canonicalMomentum_rotGenZ_gauge_conserved`.
-/

@[expose] public section

namespace PlasmaLean.Sanity.NoetherRotation

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open PlasmaLean.Sanity.NoetherLagrangian
open scoped RealInnerProductSpace

/-- The symmetric gauge `A(x) = (B₀/2) e_z × x = (B₀/2)(−y, x, 0)`. -/
noncomputable def symGauge (B₀ : ℝ) : Space →L[ℝ] Space := (B₀ / 2) • rotGenZ

/-- Components of the symmetric gauge. -/
theorem symGauge_coords (B₀ : ℝ) (y : Space) :
    symGauge B₀ y 0 = -(B₀ / 2 * y 1) ∧ symGauge B₀ y 1 = B₀ / 2 * y 0
      ∧ symGauge B₀ y 2 = 0 := by
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  simp [symGauge, h0, h1, h2]

/-- `∇ × A = B₀ e_z` for the symmetric gauge. -/
theorem curl_symGauge (B₀ : ℝ) (y : Space) :
    fieldCurl (symGauge B₀) y = B₀ • coordVec 2 := by
  rw [fieldCurl, (symGauge B₀).fderiv]
  obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ (coordVec 0)
  obtain ⟨b0, b1, b2⟩ := symGauge_coords B₀ (coordVec 1)
  obtain ⟨c0, c1, c2⟩ := symGauge_coords B₀ (coordVec 2)
  ext i
  fin_cases i
  · simp [curlOp, b2, c1]
  · simp [curlOp, c0, a2]
  · simp [curlOp, a1, b0]

/-- The symmetric gauge is equivariant under the rotations about the `z`-axis. -/
theorem symGauge_equivariant (B₀ : ℝ) (y : Space) :
    fderiv ℝ (symGauge B₀) y (rotGenZ y) = rotGenZ (symGauge B₀ y) := by
  rw [(symGauge B₀).fderiv]
  simp [symGauge]

/-- **Accepted fixture**: in the uniform field `B₀ e_z`, the canonical angular momentum
`m (x v_y − y v_x) + q B₀ (x² + y²)/2` is constant along every Lorentz orbit. -/
theorem symGauge_angular_momentum_conserved {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) := by
  have key := canonicalMomentum_rotGenZ_conserved (A := symGauge B₀) h
    (symGauge B₀).differentiable (fun y => (curl_symGauge B₀ y).symm)
    (symGauge_equivariant B₀) s t
  have hψ : ∀ y : Space, ⟪symGauge B₀ y, rotGenZ y⟫
      = B₀ * (y 0 ^ 2 + y 1 ^ 2) / 2 := fun y => by
    obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
    obtain ⟨a0, a1, a2⟩ := symGauge_coords B₀ y
    rw [inner_coords3, h0, h1, h2, a0, a1, a2]
    ring
  simp only [canonicalMomentum, angularZ, hψ] at key
  exact key

/-- Components of the defect `DA(y)(e_z × y) − e_z × A(y)` of the Landau gauge. -/
theorem landau_defect_coords (B₀ : ℝ) (y : Space) :
    (landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y)) 0 = B₀ * y 0
      ∧ (landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y)) 1 = -(B₀ * y 1)
      ∧ (landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y)) 2 = 0 := by
  obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
  obtain ⟨c0, c1, c2⟩ := rotGenZ_coords (coordVec 1)
  simp [landau_apply, h0, c0, c1, c2]

/-- Hypothesis check: the Landau gauge is not equivariant under the rotations about the
`z`-axis when `B₀ ≠ 0`. -/
theorem landau_not_equivariant {B₀ : ℝ} (hB : B₀ ≠ 0) :
    ¬ ∀ y : Space, fderiv ℝ (landau B₀) y (rotGenZ y) = rotGenZ (landau B₀ y) := by
  intro h
  have h1 := h (coordVec 0)
  rw [(landau B₀).fderiv] at h1
  have h2 := (landau_defect_coords B₀ (coordVec 0)).1
  rw [h1, sub_self] at h2
  have h3 : B₀ = 0 := by simpa using h2.symm
  exact hB h3

/-- The gauge function `χ = B₀ (x² − y²)/2` of the Landau gauge. -/
noncomputable def landauGauge (B₀ : ℝ) (y : Space) : ℝ := B₀ * (y 0 ^ 2 - y 1 ^ 2) / 2

/-- The gradient of `landauGauge` is the defect of the Landau gauge. -/
theorem hasFDerivAt_landauGauge (B₀ : ℝ) (y : Space) :
    HasFDerivAt (landauGauge B₀)
      (innerSL ℝ (landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y))) y := by
  have p0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt (x := y)
  have p1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).hasFDerivAt (x := y)
  have h := ((p0.pow 2).sub (p1.pow 2)).const_mul (B₀ / 2)
  obtain ⟨d0, d1, d2⟩ := landau_defect_coords B₀ y
  convert h using 1
  · funext z
    simp [landauGauge]
    ring
  · ext w
    rw [innerSL_apply_apply, inner_coords3, d0, d1, d2]
    simp
    ring

/-- The Landau gauge is equivariant under the rotation up to the gradient of `landauGauge`. -/
theorem landau_equivariant_gauge (B₀ : ℝ) (y : Space) :
    fderiv ℝ (landau B₀) y (rotGenZ y)
      = rotGenZ (landau B₀ y) + (landau B₀ (rotGenZ y) - rotGenZ (landau B₀ y)) := by
  rw [(landau B₀).fderiv]
  abel

/-- **Gauge-term fixture**: the Landau gauge, with gauge term `q χ`, gives the same conserved
angular momentum `m (x v_y − y v_x) + q B₀ (x² + y²)/2` as the symmetric gauge. -/
theorem landau_angular_momentum_conserved {m q B₀ : ℝ} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (s t : ℝ) :
    m * (x s 0 * v s 1 - x s 1 * v s 0) + q * (B₀ * (x s 0 ^ 2 + x s 1 ^ 2) / 2)
      = m * (x t 0 * v t 1 - x t 1 * v t 0) + q * (B₀ * (x t 0 ^ 2 + x t 1 ^ 2) / 2) := by
  have key := canonicalMomentum_rotGenZ_gauge_conserved (A := landau B₀) h
    (landau B₀).differentiable (fun y => (curl_landau B₀ y).symm)
    (hasFDerivAt_landauGauge B₀) (landau_equivariant_gauge B₀) s t
  have hψ : ∀ y : Space, ⟪landau B₀ y, rotGenZ y⟫ - landauGauge B₀ y
      = B₀ * (y 0 ^ 2 + y 1 ^ 2) / 2 := fun y => by
    obtain ⟨h0, h1, h2⟩ := rotGenZ_coords y
    rw [inner_coords3, h0, h1, h2, landauGauge, landau_apply]
    simp
    ring
  simp only [canonicalMomentum, angularZ, hψ] at key
  exact key

end PlasmaLean.Sanity.NoetherRotation
