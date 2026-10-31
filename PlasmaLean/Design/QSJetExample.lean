/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.QSLinearSystem

/-!
# A certified jet obstruction: `B = ∇(xyz)` at `(1, 2, 3)`

Source: the colleague's brief `gpt/stellarator_holomorphic_research_brief.pdf`, §2 (explicit
check); note N-32 (`notes/theory/holomorphic-qs-brief.md`); research question Q-25 (b).

The field `B = ∇(xyz) = (yz, xz, xy)` is the gradient of a harmonic polynomial, hence a vacuum
field on all of `ℝ³` (`field_vacuum`, `field_eq_gradient`). At `p = (1, 2, 3)`:

* `Q = |B|² = 49`, `X = B = (6, 3, 2)`, `Y = B × ∇Q = (10, -128, 162)`,
  `Z = [X, Y] = (240, -768, 432)`, `det(X, Y, Z) = 564480` (`jet_values`);
* `η(p) = (-2201/720, 869/180, 463/240)` and `Dη(p) = S` (the matrix `etaJac`, computed in
  sympy and checked here by exact rational arithmetic, `jetSolution`);
* the `dx ∧ dy` coefficient of `dη(p)` is `1739/21600 ≠ 0` (`curl_etaJac_two`).

Main results:

* `strongQS_obstruction`: if `B` is strongly quasisymmetric (`StrongQSAt`) on a neighbourhood
  `U` of `p`, with any generator `u` and any potential `Ψ` of class `C²` at `p`, then `C = 0`
  and `∇Ψ = 0` near `p`;
* `not_strongQS_of_ne_zero`: so there is no strong QS with `C ≠ 0` on any neighbourhood of `p`.

This is a **local** example: it excludes exact strong QS on every domain containing `(1, 2, 3)`
(with flux function nondegenerate there), but it is **not** a solid-torus counterexample, and
`B = ∇(xyz)` is not a stellarator field.

The polynomial fields are encoded by lists of integer monomials (`polyEval`); their
derivatives are formal (`polyD0`, `polyD1`, `polyD2`), justified once by `polyEval_hasFDerivAt`.
All concrete facts are closed by `simp`/`norm_num`/`ring` on explicit rationals.
-/

open scoped RealInnerProductSpace Topology
open InnerProductSpace Filter

public section
noncomputable section

namespace PlasmaLean.Design.QSJetExample
open PlasmaLean.Fields PlasmaLean.Fields.QSLinear PlasmaLean.Vacuum

/-! ## Polynomials in three variables -/

/-- A monomial `c x^a y^b z^d`, stored as `(c, a, b, d)`. -/
abbrev Mono := ℤ × ℕ × ℕ × ℕ

/-- Evaluation of a monomial. -/
@[expose] def monoEval (m : Mono) (y : Space) : ℝ :=
  (m.1 : ℝ) * y 0 ^ m.2.1 * y 1 ^ m.2.2.1 * y 2 ^ m.2.2.2

/-- Evaluation of a polynomial (a list of monomials). -/
@[expose] def polyEval (P : List Mono) (y : Space) : ℝ := (P.map fun m => monoEval m y).sum

/-- Formal `∂ₓ` of a monomial. -/
@[expose] def monoD0 (m : Mono) : Mono := (m.1 * m.2.1, m.2.1 - 1, m.2.2.1, m.2.2.2)

/-- Formal `∂_y` of a monomial. -/
@[expose] def monoD1 (m : Mono) : Mono := (m.1 * m.2.2.1, m.2.1, m.2.2.1 - 1, m.2.2.2)

/-- Formal `∂_z` of a monomial. -/
@[expose] def monoD2 (m : Mono) : Mono := (m.1 * m.2.2.2, m.2.1, m.2.2.1, m.2.2.2 - 1)

/-- Formal `∂ₓ` of a polynomial. -/
@[expose] def polyD0 (P : List Mono) : List Mono := P.map monoD0

/-- Formal `∂_y` of a polynomial. -/
@[expose] def polyD1 (P : List Mono) : List Mono := P.map monoD1

/-- Formal `∂_z` of a polynomial. -/
@[expose] def polyD2 (P : List Mono) : List Mono := P.map monoD2

/-- Coordinate functional. -/
abbrev proj (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

/-- The formal derivative of a polynomial as a linear functional. -/
@[expose] def polyDeriv (P : List Mono) (y : Space) : Space →L[ℝ] ℝ :=
  polyEval (polyD0 P) y • proj 0 + polyEval (polyD1 P) y • proj 1 +
    polyEval (polyD2 P) y • proj 2

/-- Derivative of a monomial. -/
theorem monoEval_hasFDerivAt (m : Mono) (y : Space) :
    HasFDerivAt (monoEval m) (monoEval (monoD0 m) y • proj 0 +
      monoEval (monoD1 m) y • proj 1 + monoEval (monoD2 m) y • proj 2) y := by
  obtain ⟨c, a, b, d⟩ := m
  have h := ((((proj 0).hasFDerivAt (x := y)).pow a).mul
    (((proj 1).hasFDerivAt (x := y)).pow b)).mul (((proj 2).hasFDerivAt (x := y)).pow d)
  have h' := h.const_mul (c : ℝ)
  convert h' using 1
  · funext z
    simp [monoEval]
    ring
  · ext v
    simp [monoEval, monoD0, monoD1, monoD2]
    ring

/-- **Formal derivatives are derivatives.** -/
theorem polyEval_hasFDerivAt (P : List Mono) (y : Space) :
    HasFDerivAt (polyEval P) (polyDeriv P y) y := by
  induction P with
  | nil =>
    convert hasFDerivAt_const (0 : ℝ) y using 1
    · funext z; simp [polyEval]
    · ext v; simp [polyDeriv, polyEval, polyD0, polyD1, polyD2]
  | cons m P ih =>
    have h := (monoEval_hasFDerivAt m y).add ih
    convert h using 1
    · funext z; simp [polyEval]
    · ext v
      simp [polyDeriv, polyEval, polyD0, polyD1, polyD2]
      ring

/-- Polynomials are smooth. -/
theorem polyEval_contDiff (P : List Mono) : ContDiff ℝ 2 (polyEval P) := by
  have hc : ∀ i, ContDiff ℝ 2 (fun y : Space => y i) := fun i => (proj i).contDiff
  induction P with
  | nil =>
    have he : polyEval [] = fun _ => (0 : ℝ) := by funext y; simp [polyEval]
    rw [he]
    exact contDiff_const
  | cons m P ih =>
    have hm : ContDiff ℝ 2 (monoEval m) :=
      ((contDiff_const.mul ((hc 0).pow _)).mul ((hc 1).pow _)).mul ((hc 2).pow _)
    have he : polyEval (m :: P) = fun y => monoEval m y + polyEval P y := by
      funext y; simp [polyEval]
    rw [he]
    exact hm.add ih

/-- A polynomial vector field. -/
@[expose] def polyField (P₀ P₁ P₂ : List Mono) (y : Space) : Space :=
  vec3 (polyEval P₀ y) (polyEval P₁ y) (polyEval P₂ y)

/-- The formal Jacobian of a polynomial vector field. -/
@[expose] def polyFieldDeriv (P₀ P₁ P₂ : List Mono) (y : Space) : Space →L[ℝ] Space :=
  (polyDeriv P₀ y).smulRight (basis 0) + (polyDeriv P₁ y).smulRight (basis 1) +
    (polyDeriv P₂ y).smulRight (basis 2)

/-- `polyField` as a combination of basis vectors. -/
theorem polyField_eq (P₀ P₁ P₂ : List Mono) :
    polyField P₀ P₁ P₂ = fun y => polyEval P₀ y • basis 0 + polyEval P₁ y • basis 1 +
      polyEval P₂ y • basis 2 := by
  funext y
  apply space_ext <;> simp [polyField]

/-- Derivative of a polynomial vector field. -/
theorem polyField_hasFDerivAt (P₀ P₁ P₂ : List Mono) (y : Space) :
    HasFDerivAt (polyField P₀ P₁ P₂) (polyFieldDeriv P₀ P₁ P₂ y) y := by
  rw [polyField_eq]
  exact (((polyEval_hasFDerivAt P₀ y).smul_const _).add
    ((polyEval_hasFDerivAt P₁ y).smul_const _)).add ((polyEval_hasFDerivAt P₂ y).smul_const _)

/-- Polynomial vector fields are smooth. -/
theorem polyField_contDiff (P₀ P₁ P₂ : List Mono) : ContDiff ℝ 2 (polyField P₀ P₁ P₂) := by
  rw [polyField_eq]
  exact (((polyEval_contDiff P₀).smul contDiff_const).add
    ((polyEval_contDiff P₁).smul contDiff_const)).add ((polyEval_contDiff P₂).smul contDiff_const)

/-- Coordinates of the formal Jacobian applied to a vector. -/
theorem polyFieldDeriv_apply (P₀ P₁ P₂ : List Mono) (y v : Space) :
    polyFieldDeriv P₀ P₁ P₂ y v = vec3 (polyDeriv P₀ y v) (polyDeriv P₁ y v)
      (polyDeriv P₂ y v) := by
  apply space_ext <;> simp [polyFieldDeriv]

/-- Sanity check: `∂ₓ(x²y) = 2xy` formally. -/
example : polyD0 [(1, 2, 1, 0)] = [(2, 1, 1, 0)] := by simp [polyD0, monoD0]

/-! ## The field `B = ∇(xyz)` -/

/-- `B₀ = yz`. -/
@[expose] def PB0 : List Mono := [(1, 0, 1, 1)]
/-- `B₁ = xz`. -/
@[expose] def PB1 : List Mono := [(1, 1, 0, 1)]
/-- `B₂ = xy`. -/
@[expose] def PB2 : List Mono := [(1, 1, 1, 0)]

/-- **The field** `B = ∇(xyz) = (yz, xz, xy)`. -/
@[expose] def field : Space → Space := polyField PB0 PB1 PB2

/-- Coordinates of `B`. -/
theorem field_apply (y : Space) : field y = vec3 (y 1 * y 2) (y 0 * y 2) (y 0 * y 1) := by
  apply space_ext <;> simp [field, polyField, polyEval, monoEval, PB0, PB1, PB2]

/-- `B = ∇(xyz)`. -/
theorem field_eq_gradient : field = gradient (polyEval [(1, 1, 1, 1)]) := by
  funext y
  apply space_ext <;>
    rw [← fderiv_apply_basis, (polyEval_hasFDerivAt _ y).fderiv, field_apply] <;>
    simp [polyDeriv, polyEval, polyD0, polyD1, polyD2, monoEval, monoD0, monoD1, monoD2]

/-- **`B = ∇(xyz)` is a vacuum field on all of `ℝ³`**: smooth, divergence free (`xyz` is
harmonic) and curl free (a gradient). -/
theorem field_vacuum : VacuumField Set.univ field where
  isOpen := isOpen_univ
  contDiffOn := (polyField_contDiff _ _ _).contDiffOn
  div_eq_zero x _ := by
    rw [fieldDiv, field, (polyField_hasFDerivAt _ _ _ x).fderiv, divOp_apply]
    simp [polyFieldDeriv, polyDeriv, polyEval, polyD0, polyD1, polyD2, monoEval, monoD0,
      monoD1, monoD2, PB0, PB1, PB2]
  curl_eq_zero x _ := by
    rw [fieldCurl, field, (polyField_hasFDerivAt _ _ _ x).fderiv, curlOp_eq_zero_iff]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [polyFieldDeriv, polyDeriv, polyEval, polyD0, polyD1, polyD2, monoEval, monoD0,
        monoD1, monoD2, PB0, PB1, PB2]

/-! ## The jet fields `Y`, `h`, `Z`, `k` -/

/-- `Q = y²z² + x²z² + x²y²`. -/
@[expose] def PQ : List Mono := [(1, 0, 2, 2), (1, 2, 0, 2), (1, 2, 2, 0)]
/-- `Y₀ = 2x³(z² - y²)`. -/
@[expose] def PY0 : List Mono := [(-2, 3, 2, 0), (2, 3, 0, 2)]
/-- `Y₁ = 2y³(x² - z²)`. -/
@[expose] def PY1 : List Mono := [(2, 2, 3, 0), (-2, 0, 3, 2)]
/-- `Y₂ = 2z³(y² - x²)`. -/
@[expose] def PY2 : List Mono := [(-2, 2, 0, 3), (2, 0, 2, 3)]
/-- `h = 4xyz(x² + y² + z²)`. -/
@[expose] def Ph : List Mono := [(4, 3, 1, 1), (4, 1, 3, 1), (4, 1, 1, 3)]
/-- `Z₀ = -8x²yz(y² - z²)`. -/
@[expose] def PZ0 : List Mono := [(-8, 2, 3, 1), (8, 2, 1, 3)]
/-- `Z₁ = 8xy²z(x² - z²)`. -/
@[expose] def PZ1 : List Mono := [(8, 3, 2, 1), (-8, 1, 2, 3)]
/-- `Z₂ = -8xyz²(x² - y²)`. -/
@[expose] def PZ2 : List Mono := [(-8, 3, 1, 2), (8, 1, 3, 2)]
/-- `k = X h = 4(x⁴y² + x⁴z² + x²y⁴ + 9x²y²z² + x²z⁴ + y⁴z² + y²z⁴)`. -/
@[expose] def Pk : List Mono :=
  [(4, 4, 2, 0), (4, 4, 0, 2), (4, 2, 4, 0), (36, 2, 2, 2), (4, 2, 0, 4), (4, 0, 4, 2),
    (4, 0, 2, 4)]

/-- The bracket field `Z = [X, Y]`, as a polynomial field. -/
@[expose] def fieldZ : Space → Space := polyField PZ0 PZ1 PZ2

/-- The function `k = X h`, as a polynomial. -/
@[expose] def fieldK : Space → ℝ := polyEval Pk

/-- `Q = |B|²` is the polynomial `PQ`. -/
theorem fieldQ_eq : fieldQ field = polyEval PQ := by
  funext y
  rw [fieldQ, field_apply, inner_coords]
  simp [polyEval, monoEval, PQ]
  ring

/-- `∇Q` is the formal gradient of `PQ`. -/
theorem gradient_fieldQ (y : Space) :
    gradient (fieldQ field) y = polyField (polyD0 PQ) (polyD1 PQ) (polyD2 PQ) y := by
  rw [fieldQ_eq]
  apply space_ext <;> rw [← fderiv_apply_basis, (polyEval_hasFDerivAt _ y).fderiv] <;>
    simp [polyDeriv, polyField]

/-- `Y = B × ∇Q` is the polynomial field `(PY0, PY1, PY2)`. -/
theorem fieldY_eq : fieldY field = polyField PY0 PY1 PY2 := by
  funext y
  rw [fieldY, gradient_fieldQ, field_apply]
  apply space_ext <;>
    simp [polyField, polyEval, monoEval, polyD0, polyD1, polyD2, monoD0, monoD1, monoD2, PQ,
      PY0, PY1, PY2] <;> ring

/-- `h = B · ∇Q` is the polynomial `Ph`. -/
theorem fieldH_eq : fieldH field = polyEval Ph := by
  funext y
  rw [fieldH, gradient_fieldQ, field_apply, inner_coords]
  simp [polyField, polyEval, monoEval, polyD0, polyD1, polyD2, monoD0, monoD1, monoD2, PQ, Ph]
  ring

/-- `Z = [X, Y]` everywhere. -/
theorem fieldZ_eq (y : Space) :
    fieldZ y = VectorField.lieBracket ℝ field (fieldY field) y := by
  rw [VectorField.lieBracket, fieldY_eq, field, (polyField_hasFDerivAt _ _ _ y).fderiv,
    (polyField_hasFDerivAt _ _ _ y).fderiv, polyFieldDeriv_apply, polyFieldDeriv_apply]
  apply space_ext <;>
    simp [fieldZ, polyField, polyDeriv, polyEval, monoEval, polyD0, polyD1, polyD2, monoD0,
      monoD1, monoD2, PB0, PB1, PB2, PY0, PY1, PY2, PZ0, PZ1, PZ2] <;> ring

/-- `k = X h` everywhere. -/
theorem fieldK_eq (y : Space) : fieldK y = fderiv ℝ (fieldH field) y (field y) := by
  rw [fieldH_eq, (polyEval_hasFDerivAt _ y).fderiv, field_apply]
  simp [fieldK, polyDeriv, polyEval, monoEval, polyD0, polyD1, polyD2, monoD0, monoD1, monoD2,
    Ph, Pk]
  ring

/-! ## The jet at `p = (1, 2, 3)` -/

/-- The point `p = (1, 2, 3)`. -/
@[expose] def p₀ : Space := vec3 1 2 3

/-- `η(p) = (-2201/720, 869/180, 463/240)`. -/
@[expose] def etaVal : Space := vec3 (-2201 / 720) (869 / 180) (463 / 240)

/-- The linear map with columns `c₀`, `c₁`, `c₂` (`L eⱼ = cⱼ`). -/
@[expose] def colCLM (c₀ c₁ c₂ : Space) : Space →L[ℝ] Space :=
  (proj 0).smulRight c₀ + (proj 1).smulRight c₁ + (proj 2).smulRight c₂

/-- `Dη(p)`: column `j` is `∂ⱼη(p)` (computed in sympy, verified in `jetSolution`). -/
@[expose] def etaJac : Space →L[ℝ] Space :=
  colCLM (vec3 (-4591 / 8640) (-5789 / 2160) (-10243 / 2880))
    (vec3 (-59629 / 21600) (6109 / 1350) (36827 / 7200))
    (vec3 (87157 / 43200) (-22933 / 10800) (-3559 / 1600))

/-- Coordinates of `p₀`. -/
@[simp] theorem p₀_coords : p₀ 0 = 1 ∧ p₀ 1 = 2 ∧ p₀ 2 = 3 := ⟨rfl, rfl, rfl⟩

/-- **The jet values at `p`**: `Q = 49`, `X = (6, 3, 2)`, `Y = (10, -128, 162)`,
`Z = (240, -768, 432)`, `det(X, Y, Z) = 564480`. -/
theorem jet_values :
    fieldQ field p₀ = 49 ∧ field p₀ = vec3 6 3 2 ∧ fieldY field p₀ = vec3 10 (-128) 162 ∧
      fieldZ p₀ = vec3 240 (-768) 432 ∧
      ⟪field p₀, cross (fieldY field p₀) (fieldZ p₀)⟫ = 564480 := by
  have hX : field p₀ = vec3 6 3 2 := by
    rw [field_apply]; apply space_ext <;> (simp [p₀]; try norm_num)
  have hY : fieldY field p₀ = vec3 10 (-128) 162 := by
    rw [fieldY_eq]
    apply space_ext <;> simp [polyField, polyEval, monoEval, PY0, PY1, PY2, p₀] <;> norm_num
  have hZ : fieldZ p₀ = vec3 240 (-768) 432 := by
    apply space_ext <;> simp [fieldZ, polyField, polyEval, monoEval, PZ0, PZ1, PZ2, p₀] <;>
      norm_num
  refine ⟨?_, hX, hY, hZ, ?_⟩
  · rw [fieldQ, hX, inner_coords]; simp; norm_num
  · rw [hX, hY, hZ, inner_coords]; simp; norm_num

/-- **The linear data at `p`**: `η(p) = etaVal` and `Dη(p) = etaJac` solve the system of the
jet obstruction for `X = B`, `Y = B × ∇Q`, `Z = [X, Y]`, `h = B · ∇Q`, `k = X h`. -/
theorem jetSolution :
    JetSolution field (fieldY field) fieldZ (fieldH field) fieldK p₀
      (polyFieldDeriv PB0 PB1 PB2 p₀) (polyFieldDeriv PY0 PY1 PY2 p₀)
      (polyFieldDeriv PZ0 PZ1 PZ2 p₀) (polyDeriv Ph p₀) (polyDeriv Pk p₀) etaVal etaJac := by
  obtain ⟨-, hX, hY, hZ, -⟩ := jet_values
  refine ⟨?_, ?_, ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [hX, inner_coords]; simp [etaVal]; norm_num
  · rw [hY, inner_coords, fieldH_eq]
    simp [etaVal, polyEval, monoEval, Ph, p₀]; norm_num
  · rw [hZ, inner_coords]
    simp [etaVal, fieldK, polyEval, monoEval, Pk, p₀]; norm_num
  · rw [hX, inner_coords, inner_coords, polyFieldDeriv_apply]
    simp [etaVal, etaJac, colCLM, polyDeriv, polyEval, monoEval, polyD0, polyD1, polyD2,
      monoD0, monoD1, monoD2, PB0, PB1, PB2, p₀]
    ring
  · rw [hY, inner_coords, inner_coords, polyFieldDeriv_apply]
    simp [etaVal, etaJac, colCLM, polyDeriv, polyEval, monoEval, polyD0, polyD1, polyD2,
      monoD0, monoD1, monoD2, PY0, PY1, PY2, Ph, p₀]
    ring
  · rw [hZ, inner_coords, inner_coords, polyFieldDeriv_apply]
    simp [etaVal, etaJac, colCLM, polyDeriv, polyEval, monoEval, polyD0, polyD1, polyD2,
      monoD0, monoD1, monoD2, PZ0, PZ1, PZ2, Pk, p₀]
    ring

/-- **The `dx ∧ dy` coefficient of `dη(p)`** is `∂ₓη_y - ∂_yη_x = 1739/21600`. -/
theorem curl_etaJac_two : curlOp etaJac 2 = 1739 / 21600 := by
  simp [curlOp, etaJac, colCLM]
  norm_num

/-- `dη(p) ≠ 0`. -/
theorem curl_etaJac_ne_zero : curlOp etaJac ≠ 0 := by
  intro h
  have h2 := curl_etaJac_two
  rw [h] at h2
  norm_num at h2

/-! ## The obstruction -/

/-- **No strong QS near `(1, 2, 3)` with `C ≠ 0`, and `C = 0` forces `∇Ψ = 0`.** If
`B = ∇(xyz)` is strongly quasisymmetric (`B × u = ∇Ψ`, `B · u = C`, `div u = 0`) at every point
of a neighbourhood `U` of `(1, 2, 3)`, with `Ψ` of class `C²` at `(1, 2, 3)` (no regularity of
`u` is assumed), then `C = 0` and `∇Ψ` vanishes near `(1, 2, 3)`. Local statement only; this
is not a solid-torus counterexample. -/
theorem strongQS_obstruction {u : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {U : Set Space}
    (hU : U ∈ 𝓝 p₀) (hΨ : ContDiffAt ℝ 2 Ψ p₀) (h : ∀ y ∈ U, StrongQSAt field u Ψ C y) :
    C = 0 ∧ ∀ᶠ y in 𝓝 p₀, gradient Ψ y = 0 := by
  obtain ⟨-, hX, -, -, hdet⟩ := jet_values
  have hne : field p₀ ≠ 0 := by
    rw [hX]; intro h0
    have := congrArg (fun v : Space => v 0) h0
    norm_num at this
  have hYfun := fieldY_eq
  have hHfun := fieldH_eq
  refine strongQS_jet_obstruction field_vacuum (Set.mem_univ _) hne hU hΨ h
    (Eventually.of_forall fun y => (polyField_hasFDerivAt _ _ _ y).differentiableAt)
    (Eventually.of_forall fun y => by
      rw [hYfun]; exact (polyField_hasFDerivAt _ _ _ y).differentiableAt)
    (Eventually.of_forall fun y => by
      rw [hHfun]; exact (polyEval_hasFDerivAt _ y).differentiableAt)
    (polyField_hasFDerivAt _ _ _ p₀) (by rw [hYfun]; exact polyField_hasFDerivAt _ _ _ p₀)
    (polyField_hasFDerivAt _ _ _ p₀) (by rw [hHfun]; exact polyEval_hasFDerivAt _ p₀)
    (polyEval_hasFDerivAt _ p₀) (Eventually.of_forall fieldZ_eq)
    (Eventually.of_forall fieldK_eq)
    (by
      change ⟪field p₀, cross (fieldY field p₀) (fieldZ p₀)⟫ ≠ 0
      rw [hdet]; norm_num) jetSolution curl_etaJac_ne_zero

/-- **No strong QS with `C ≠ 0` on any neighbourhood of `(1, 2, 3)`.** -/
theorem not_strongQS_of_ne_zero {u : Space → Space} {Ψ : Space → ℝ} {C : ℝ} {U : Set Space}
    (hU : U ∈ 𝓝 p₀) (hΨ : ContDiffAt ℝ 2 Ψ p₀) (hC : C ≠ 0) :
    ¬ ∀ y ∈ U, StrongQSAt field u Ψ C y :=
  fun h => hC (strongQS_obstruction hU hΨ h).1

end PlasmaLean.Design.QSJetExample
