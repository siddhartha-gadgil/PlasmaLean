/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Summation-by-parts (SBP) operators and the discrete energy law

Track T5 (source: `notes/pde-bounds-and-verification-roadmap.md` §8). An SBP operator on
`N` grid points is a difference matrix `D` approximating `∂ₓ` together with a symmetric
positive-definite norm matrix `P` such that `P D + Dᵀ P = B`, where `B` is a boundary
matrix (classically `B = diag(-1, 0, …, 0, 1)`). This is the discrete analogue of
`∫ u u' dx = ½ [u²]`.

Main results:

* `SBPOperator.quadratic_identity`: `uᵀ (P D) u = ½ uᵀ B u`.
* `SBPOperator.energy_hasDerivAt`: along the semi-discrete advection `u' = -D u`, the
  discrete energy `uᵀ P u` has derivative `-uᵀ B u` (boundary terms only).
* `sbp2`: the classical second-order SBP operator on 4 points with spacing `h > 0`,
  `P = h·diag(1/2, 1, 1, 1/2)`, central interior rows and one-sided boundary rows, with
  `B = diag(-1, 0, 0, 1)` verified exactly. For it, `d/dt (uᵀPu) = u₀² - u₃²`: energy
  enters through the inflow (left) boundary and leaves through the outflow (right) one,
  as for `uₜ + uₓ = 0`.
* `naive_not_sbp`: a rejected fixture (central differences with zero boundary rows) for
  which the quadratic identity fails, so no SBP operator has these matrices.

Scope: only the semi-discrete (method-of-lines) energy law is proved; time stepping,
accuracy, and boundary penalty (SAT) terms are separate targets.
-/
public section

noncomputable section
namespace PlasmaLean.Certificates

open Matrix

/-- A summation-by-parts operator on `N` points: difference matrix `D`, symmetric positive
definite norm `P`, boundary matrix `B`, with `P D + Dᵀ P = B`. -/
structure SBPOperator (N : ℕ) where
  /-- The difference matrix approximating `∂ₓ`. -/
  D : Matrix (Fin N) (Fin N) ℝ
  /-- The norm (quadrature) matrix. -/
  P : Matrix (Fin N) (Fin N) ℝ
  /-- The boundary matrix. -/
  B : Matrix (Fin N) (Fin N) ℝ
  /-- The norm is symmetric. -/
  P_symm : Pᵀ = P
  /-- The norm is positive definite. -/
  P_posDef : ∀ u : Fin N → ℝ, u ≠ 0 → 0 < u ⬝ᵥ P *ᵥ u
  /-- The summation-by-parts identity. -/
  sbp_identity : P * D + Dᵀ * P = B

/-- A quadratic form is unchanged by transposing the matrix. -/
theorem dotProduct_transpose_mulVec {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (u : Fin N → ℝ) :
    u ⬝ᵥ Mᵀ *ᵥ u = u ⬝ᵥ M *ᵥ u := by
  rw [mulVec_transpose, dotProduct_mulVec, dotProduct_comm]

namespace SBPOperator

variable {N : ℕ} (S : SBPOperator N)

/-- Discrete integration by parts: `uᵀ (P D) u = ½ uᵀ B u`. -/
theorem quadratic_identity (u : Fin N → ℝ) :
    u ⬝ᵥ (S.P * S.D) *ᵥ u = (1 / 2) * (u ⬝ᵥ S.B *ᵥ u) := by
  have hT : (S.P * S.D)ᵀ = S.Dᵀ * S.P := by rw [transpose_mul, S.P_symm]
  have h := congrArg (fun M => u ⬝ᵥ M *ᵥ u) S.sbp_identity
  simp only [add_mulVec, dotProduct_add] at h
  rw [← hT, dotProduct_transpose_mulVec] at h
  linarith

/-- The discrete energy `uᵀ P u` is nonnegative. -/
theorem energy_nonneg (u : Fin N → ℝ) : 0 ≤ u ⬝ᵥ S.P *ᵥ u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (S.P_posDef u hu).le

/-- Derivative of a quadratic form along a differentiable vector path, for symmetric `P`:
`d/dt (uᵀ P u) = 2 uᵀ P u'`. -/
theorem quadForm_hasDerivAt {P : Matrix (Fin N) (Fin N) ℝ} (hP : Pᵀ = P)
    {u : ℝ → Fin N → ℝ} {u' : Fin N → ℝ} {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s => u s ⬝ᵥ P *ᵥ u s) (2 * (u t ⬝ᵥ P *ᵥ u')) t := by
  have hi : ∀ i, HasDerivAt (fun s => u s i) (u' i) t := hasDerivAt_pi.mp hu
  have hPu : ∀ i, HasDerivAt (fun s => (P *ᵥ u s) i) ((P *ᵥ u') i) t := by
    intro i
    simp only [mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hi j).const_mul (P i j)
  have hsum : HasDerivAt (fun s => u s ⬝ᵥ P *ᵥ u s)
      (∑ i, (u' i * (P *ᵥ u t) i + u t i * (P *ᵥ u') i)) t := by
    simp only [dotProduct]
    exact HasDerivAt.fun_sum fun i _ => (hi i).mul (hPu i)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i, u' i * (P *ᵥ u t) i = u t ⬝ᵥ P *ᵥ u' := by
    change u' ⬝ᵥ P *ᵥ u t = _
    rw [dotProduct_mulVec, ← mulVec_transpose, hP, dotProduct_comm]
  have h2 : ∑ i, u t i * (P *ᵥ u') i = u t ⬝ᵥ P *ᵥ u' := rfl
  rw [h1, h2]
  ring

/-- Discrete energy law: along the semi-discrete advection `u' = -D u`, the energy
`uᵀ P u` has derivative `-uᵀ B u`, i.e. only boundary terms. -/
theorem energy_hasDerivAt {u : ℝ → Fin N → ℝ} {t : ℝ}
    (hu : HasDerivAt u (-(S.D *ᵥ u t)) t) :
    HasDerivAt (fun s => u s ⬝ᵥ S.P *ᵥ u s) (-(u t ⬝ᵥ S.B *ᵥ u t)) t := by
  refine (quadForm_hasDerivAt S.P_symm hu).congr_deriv ?_
  rw [mulVec_neg, dotProduct_neg, mulVec_mulVec, S.quadratic_identity]
  ring

/-- Sanity: a zero boundary matrix makes the discrete energy exactly conserved. -/
theorem energy_conserved_of_B_zero (hB : S.B = 0) {u : ℝ → Fin N → ℝ} {t : ℝ}
    (hu : HasDerivAt u (-(S.D *ᵥ u t)) t) :
    HasDerivAt (fun s => u s ⬝ᵥ S.P *ᵥ u s) 0 t := by
  simpa [hB] using S.energy_hasDerivAt hu

end SBPOperator

/-! ### The classical second-order SBP operator on four points -/

/-- Norm matrix `P = h·diag(1/2, 1, 1, 1/2)` of the classical second-order SBP operator. -/
@[expose] def sbp2P (h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![h / 2, 0, 0, 0; 0, h, 0, 0; 0, 0, h, 0; 0, 0, 0, h / 2]

/-- Difference matrix: one-sided boundary rows `(-1, 1)/h`, central interior rows
`(-1/2, 0, 1/2)/h`. -/
@[expose] def sbp2D (h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1 / h, 1 / h, 0, 0;
     -1 / (2 * h), 0, 1 / (2 * h), 0;
     0, -1 / (2 * h), 0, 1 / (2 * h);
     0, 0, -1 / h, 1 / h]

/-- The classical boundary matrix `diag(-1, 0, 0, 1)`. -/
@[expose] def sbp2B : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1]

/-- The quadratic form of `sbp2P` written out. -/
theorem sbp2P_quadForm (h : ℝ) (u : Fin 4 → ℝ) :
    u ⬝ᵥ sbp2P h *ᵥ u = h * (u 0 ^ 2 / 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 / 2) := by
  simp [sbp2P, dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- The quadratic form of `sbp2B` is `u₃² - u₀²`. -/
theorem sbp2B_quadForm (u : Fin 4 → ℝ) : u ⬝ᵥ sbp2B *ᵥ u = u 3 ^ 2 - u 0 ^ 2 := by
  simp [sbp2B, dotProduct, mulVec, Fin.sum_univ_four]
  ring

/-- The classical second-order SBP operator on four points with spacing `h > 0`; the SBP
identity is checked exactly entry by entry. -/
def sbp2 (h : ℝ) (hh : 0 < h) : SBPOperator 4 where
  D := sbp2D h
  P := sbp2P h
  B := sbp2B
  P_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sbp2P]
  P_posDef := by
    intro u hu
    rw [sbp2P_quadForm]
    apply mul_pos hh
    by_contra hle
    apply hu
    have q0 := sq_nonneg (u 0)
    have q1 := sq_nonneg (u 1)
    have q2 := sq_nonneg (u 2)
    have q3 := sq_nonneg (u 3)
    have h0 : u 0 = 0 := by nlinarith
    have h1 : u 1 = 0 := by nlinarith
    have h2 : u 2 = 0 := by nlinarith
    have h3 : u 3 = 0 := by nlinarith
    ext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  sbp_identity := by
    have hh' : h ≠ 0 := hh.ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sbp2P, sbp2D, sbp2B, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

/-- Energy law for the classical operator: `d/dt (uᵀPu) = u₀² - u₃²` (inflow minus outflow
for `uₜ + uₓ = 0`). -/
theorem sbp2_energy_hasDerivAt {h : ℝ} (hh : 0 < h) {u : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hu : HasDerivAt u (-(sbp2D h *ᵥ u t)) t) :
    HasDerivAt (fun s => u s ⬝ᵥ sbp2P h *ᵥ u s) (u t 0 ^ 2 - u t 3 ^ 2) t := by
  have := (sbp2 h hh).energy_hasDerivAt (u := u) hu
  refine this.congr_deriv ?_
  change -(u t ⬝ᵥ sbp2B *ᵥ u t) = _
  rw [sbp2B_quadForm]
  ring

/-- Sanity: with zero inflow data `u₀(t) = 0`, the discrete energy is nonincreasing at `t`. -/
theorem sbp2_energy_deriv_nonpos_of_inflow_zero {h : ℝ} (hh : 0 < h) {u : ℝ → Fin 4 → ℝ}
    {t : ℝ} (hu : HasDerivAt u (-(sbp2D h *ᵥ u t)) t) (h0 : u t 0 = 0) :
    ∃ d, HasDerivAt (fun s => u s ⬝ᵥ sbp2P h *ᵥ u s) d t ∧ d ≤ 0 :=
  ⟨_, sbp2_energy_hasDerivAt hh hu, by rw [h0]; nlinarith [sq_nonneg (u t 3)]⟩

/-- Sanity (accepted fixture, discrete integration by parts): for `u = (1, 2, 3, 4)` and
`h = 1`, `uᵀ (P D) u = ½ (4² - 1²) = 15/2`. -/
theorem sbp2_fixture : ![(1 : ℝ), 2, 3, 4] ⬝ᵥ (sbp2P 1 * sbp2D 1) *ᵥ ![1, 2, 3, 4] = 15 / 2 := by
  refine ((sbp2 1 one_pos).quadratic_identity ![1, 2, 3, 4]).trans ?_
  change (1 / 2) * (![(1 : ℝ), 2, 3, 4] ⬝ᵥ sbp2B *ᵥ ![1, 2, 3, 4]) = 15 / 2
  rw [sbp2B_quadForm]
  norm_num

/-! ### Rejected fixture -/

/-- A non-SBP difference matrix: central interior rows but zero boundary rows. -/
@[expose] def naiveD : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; -1 / 2, 0, 1 / 2, 0; 0, -1 / 2, 0, 1 / 2; 0, 0, 0, 0]

/-- Rejected fixture: with `P = sbp2P 1` and `B = diag(-1,0,0,1)`, the quadratic identity
fails for `naiveD` at `u = e₀` (`0 ≠ -1/2`). -/
theorem naiveD_identity_fails :
    ¬ ∀ u : Fin 4 → ℝ, u ⬝ᵥ (sbp2P 1 * naiveD) *ᵥ u = (1 / 2) * (u ⬝ᵥ sbp2B *ᵥ u) := by
  intro h
  have := h ![1, 0, 0, 0]
  rw [sbp2B_quadForm] at this
  simp [sbp2P, naiveD, dotProduct, mulVec, Matrix.mul_apply, Fin.sum_univ_four] at this

/-- Rejected fixture: no SBP operator has `D = naiveD`, `P = sbp2P 1`, `B = diag(-1,0,0,1)`. -/
theorem naive_not_sbp :
    ¬ ∃ S : SBPOperator 4, S.D = naiveD ∧ S.P = sbp2P 1 ∧ S.B = sbp2B := by
  rintro ⟨S, hD, hP, hB⟩
  apply naiveD_identity_fails
  intro u
  have := S.quadratic_identity u
  rwa [hD, hP, hB] at this

end PlasmaLean.Certificates
