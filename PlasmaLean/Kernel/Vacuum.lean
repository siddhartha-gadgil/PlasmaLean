/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Vacuum magnetic fields (domain KERNEL file)

**This is a kernel file** of the PlasmaLean domain library (a domain kernel, not
an extension of Lean's logical kernel). It models a static magnetic field in a
current-free region: an open set `Ω ⊆ ℝ³` on which `B` is twice continuously
differentiable, `∇ · B = 0` (Gauss law for magnetism) and `∇ × B = 0` (Ampère's
law with no current and no displacement current).

Lean model.
* Physical space is `Euclid3 := EuclideanSpace ℝ (Fin 3)`, carrying the Euclidean
  norm. (The algebraic kernel's `Vec3 := Fin 3 → ℝ` carries the sup norm; the
  Euclidean model is used here so that Mathlib's Laplacian applies and so that
  `Euclid3` is definitionally the `Space` of `Theory/Fields/BiotSavart`.)
* The differential operators act on a derivative operator `L = DB(x)`, so that
  `L eⱼ = ∂ⱼ B`: `divOp L = ∑ᵢ (L eᵢ)ᵢ` and
  `curlOp L = (∂_y B_z - ∂_z B_y, ∂_z B_x - ∂_x B_z, ∂_x B_y - ∂_y B_x)`.
  These are the same conventions as `Fields.divergence`/`Fields.curl` in
  `Theory/Fields/Maxwell`; the kernel does not import the theory layer, and the
  agreement is proved in `Sanity/Vacuum`.
* `VacuumField Ω B` bundles the hypotheses. It is a `Prop`-valued structure,
  not an axiom; it is a supplied physical law to be discharged for each model
  field (constant fields, closed filament fields away from their coil, ...).

Not modelled: time dependence, material media (`μ ≠ μ₀`), boundary conditions.
-/

public section
noncomputable section

namespace PlasmaLean.Vacuum

/-- Physical space ℝ³ with the Euclidean norm (definitionally `Fields.Space`). -/
abbrev Euclid3 := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th Cartesian unit vector `eᵢ`. -/
abbrev coordVec (i : Fin 3) : Euclid3 := EuclideanSpace.single i (1 : ℝ)

/-- Divergence of a derivative operator `L = DB(x)`: `∑ᵢ (L eᵢ)ᵢ = ∑ᵢ ∂ᵢ Bᵢ`. -/
@[expose] def divOp (L : Euclid3 →L[ℝ] Euclid3) : ℝ := ∑ i : Fin 3, L (coordVec i) i

/-- Curl of a derivative operator `L = DB(x)`:
`(∂_y B_z - ∂_z B_y, ∂_z B_x - ∂_x B_z, ∂_x B_y - ∂_y B_x)`. -/
@[expose] def curlOp (L : Euclid3 →L[ℝ] Euclid3) : Euclid3 :=
  WithLp.toLp 2 ![L (coordVec 1) 2 - L (coordVec 2) 1,
    L (coordVec 2) 0 - L (coordVec 0) 2,
    L (coordVec 0) 1 - L (coordVec 1) 0]

/-- Pointwise divergence `∇ · B` of a vector field, via its Fréchet derivative. -/
@[expose] def fieldDiv (B : Euclid3 → Euclid3) (x : Euclid3) : ℝ := divOp (fderiv ℝ B x)

/-- Pointwise curl `∇ × B` of a vector field, via its Fréchet derivative. -/
@[expose] def fieldCurl (B : Euclid3 → Euclid3) (x : Euclid3) : Euclid3 :=
  curlOp (fderiv ℝ B x)

/-- **Vacuum magnetic field** on a region `Ω`: `Ω` is open, `B` is `C²` on `Ω`,
and `∇ · B = 0`, `∇ × B = 0` at every point of `Ω`. -/
structure VacuumField (Ω : Set Euclid3) (B : Euclid3 → Euclid3) : Prop where
  /-- The current-free region is open. -/
  isOpen : IsOpen Ω
  /-- The field is twice continuously differentiable on the region. -/
  contDiffOn : ContDiffOn ℝ 2 B Ω
  /-- Gauss law for magnetism. -/
  div_eq_zero : ∀ x ∈ Ω, fieldDiv B x = 0
  /-- Ampère's law with zero current. -/
  curl_eq_zero : ∀ x ∈ Ω, fieldCurl B x = 0

/-- Coordinate formula for the divergence operator. -/
theorem divOp_apply (L : Euclid3 →L[ℝ] Euclid3) :
    divOp L = L (coordVec 0) 0 + L (coordVec 1) 1 + L (coordVec 2) 2 := by
  simp [divOp, Fin.sum_univ_three]

/-- A derivative operator is curl free iff its Jacobian matrix `(L eⱼ)ᵢ = ∂ⱼ Bᵢ`
is symmetric. -/
theorem curlOp_eq_zero_iff (L : Euclid3 →L[ℝ] Euclid3) :
    curlOp L = 0 ↔ ∀ i j : Fin 3, L (coordVec j) i = L (coordVec i) j := by
  constructor
  · intro h i j
    have h0 := congrArg (fun v : Euclid3 => v 0) h
    have h1 := congrArg (fun v : Euclid3 => v 1) h
    have h2 := congrArg (fun v : Euclid3 => v 2) h
    simp only [curlOp, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.zero_apply] at h0 h1 h2
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · intro h
    ext k
    fin_cases k <;> simp [curlOp, h 2 1, h 0 2, h 1 0]

end PlasmaLean.Vacuum
