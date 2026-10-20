/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Discrete maximum and comparison principles for the radial transport scheme

Track T5 (implementation plan, M2: "discrete scheme with a verified maximum principle").
This is the discrete counterpart of `PlasmaLean.Theory.Transport.Comparison`.

## Abstract M-matrix lemmas (inverse positivity)

For a real square matrix `A` with nonpositive off-diagonal entries (`OffDiagNonpos`) and row sums
`rowSum A i = ∑ⱼ A i j` (i.e. `A·1`):

* `nonneg_of_mulVec_nonneg` (strict case): if every row sum is positive (`A·1 > 0`, equivalently
  strict diagonal dominance for a Z-matrix), then `A u ≥ 0 ⇒ u ≥ 0`.
* `pos_of_mulVec_pos`: if every row sum is nonnegative, then `A u > 0 ⇒ u > 0`.
* `nonneg_of_mulVec_nonneg_chain` (weakly chained case): if every row sum is nonnegative and
  every row with zero row sum has a negative entry to a *later* index (a chain to a strictly
  dominant row), then `A u ≥ 0 ⇒ u ≥ 0`. This covers a Dirichlet row at the end of a chain.

All proofs use the same minimum-point argument: at a minimizer `i` of `u`,
`(A u)ᵢ = ∑ⱼ Aᵢⱼ (uⱼ - uᵢ) + uᵢ · rowSum A i`, and the first sum is `≤ 0`.

## The conservative finite-volume radial operator

Nodes `ψ_i = i h` (`i = 0..N`, `h = 1/N`), unknowns `u_0..u_{N-1}`, edge value `u_N = T_edge`
(Dirichlet). The control volume of node `i` has (weighted) volume `vol i ≈ V'(ψ_i)·h` (half a
cell at the axis), and the face between nodes `i` and `i+1` has transmissibility
`κ i ≈ V'(ψ_{i+1/2}) D(ψ_{i+1/2}) / h`. There is no face to the left of node `0`
(Neumann/no-flux axis). The discretization of `(1/V')(V' D u')'` is
`(L u)_i = (κ_i (u_{i+1} - u_i) - κ_{i-1} (u_i - u_{i-1})) / vol_i`,
written as `FVGrid.L *ᵥ u + T_edge • FVGrid.bdry`.

* `FVGrid.rowSum_L`: `L·1 = -bdry` (conservation: constants are annihilated up to the edge).
* `FVGrid.ofCoeffs`, `FVGrid.ofCoeffs_valid`: the data built from `V'` and `D`, admissible
  when `V' > 0` and `D ≥ 0` on `[0,1]`. `V'(0) > 0` at the axis holds for the normalized
  toroidal flux coordinate `ψ` (as in the kernel), **not** for `ψ = r` (where `V'(0) = 0`).
* `FVGrid.backwardEuler_isMMatrix`: for `vol > 0`, `κ ≥ 0` and **any** `Δt ≥ 0`, the
  backward-Euler matrix `1 - Δt • L` is a Z-matrix with row sums `≥ 1`.
* `FVGrid.vol_mul_op`: conservative (flux-difference) form of the operator.
* `FVGrid.flux_telescope`: discrete conservation `∑ vol_i (L u)_i = κ_{N-1}(T_edge - u_{N-1})`.

## Discrete comparison

* `FVGrid.le_of_subsolution`: a backward-Euler subsolution stays below a supersolution for all
  time steps (non-strict data suffice in the discrete setting).
* `FVGrid.lt_of_strictSubsolution`: a strict subsolution stays strictly below.
* `FVGrid.le_const_of_isSub`, `FVGrid.const_le_of_isSuper`: the discrete maximum/minimum
  principle (bounds by initial and edge data) as corollaries.
* `FVGrid.steady_le`: stationary (semi-discrete steady-state) comparison via the weakly chained
  lemma, assuming `κ > 0`.

## Sanity

`FVGrid.constant_isSolution` (constants with matching edge data are preserved), a 3-node instance
with exact rationals (`g3`, `g3_backwardEuler`, `g3_step`, `g3_step_bounds`), and the rejected
instance `gNeg` with negative diffusivity: `gNeg_counterexample` exhibits `A u ≥ 0` with
`u ≱ 0`.

Scope: the reaction term is a supplied source `f` independent of the unknown (linear scheme);
the semi-discrete *time-continuous* ODE comparison and the consistency estimate linking discrete
and continuum barriers are not proved here.
-/

public section

noncomputable section
namespace PlasmaLean.Certificates.DiscreteMax

open Matrix Finset

variable {n : ℕ}

/-! ### Abstract M-matrix lemmas -/

/-- A Z-matrix: all off-diagonal entries are nonpositive. -/
@[expose] def OffDiagNonpos (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, i ≠ j → A i j ≤ 0

/-- Row sum `(A·1)ᵢ = ∑ⱼ A i j`. -/
@[expose] def rowSum (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  ∑ j, A i j

/-- Row-sum M-matrix: a Z-matrix with `A·1 > 0`. (Such a matrix has positive diagonal and is
strictly diagonally dominant by rows.) -/
structure IsRowMMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Prop where
  /-- Nonpositive off-diagonal entries. -/
  offDiag : OffDiagNonpos A
  /-- Positive row sums. -/
  rowSum_pos : ∀ i, 0 < rowSum A i

/-- Splitting of `(A u)ᵢ` around the value `uᵢ`. -/
theorem mulVec_apply_eq (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (i : Fin n) :
    (A *ᵥ u) i = ∑ j, A i j * (u j - u i) + u i * rowSum A i := by
  simp only [mulVec, dotProduct, rowSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- At a minimizer `i` of `u`, the off-diagonal part of `(A u)ᵢ` is nonpositive. -/
theorem sum_mul_sub_nonpos {A : Matrix (Fin n) (Fin n) ℝ} (hA : OffDiagNonpos A)
    {u : Fin n → ℝ} {i : Fin n} (hmin : ∀ j, u i ≤ u j) :
    ∑ j, A i j * (u j - u i) ≤ 0 := by
  refine Finset.sum_nonpos fun j _ => ?_
  by_cases hij : i = j
  · subst hij; simp
  · exact mul_nonpos_of_nonpos_of_nonneg (hA i j hij) (sub_nonneg.2 (hmin j))

/-- At a minimizer `i` of `u`, `(A u)ᵢ ≤ uᵢ · rowSum A i`. -/
theorem mulVec_le_at_min {A : Matrix (Fin n) (Fin n) ℝ} (hA : OffDiagNonpos A)
    {u : Fin n → ℝ} {i : Fin n} (hmin : ∀ j, u i ≤ u j) :
    (A *ᵥ u) i ≤ u i * rowSum A i := by
  rw [mulVec_apply_eq]; linarith [sum_mul_sub_nonpos hA hmin]

/-- **Discrete maximum principle, strict case.** For a Z-matrix with positive row sums,
`A u ≥ 0` implies `u ≥ 0`. -/
theorem nonneg_of_mulVec_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsRowMMatrix A)
    {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ (A *ᵥ u) i) : ∀ i, 0 ≤ u i := by
  intro k
  by_contra hk
  push Not at hk
  have : Nonempty (Fin n) := ⟨k⟩
  obtain ⟨i, hi⟩ := Finite.exists_min u
  have h1 := mulVec_le_at_min hA.offDiag hi
  have h2 : u i * rowSum A i < 0 := mul_neg_of_neg_of_pos ((hi k).trans_lt hk) (hA.rowSum_pos i)
  linarith [hu i]

/-- **Strict positivity.** For a Z-matrix with nonnegative row sums, `A u > 0` implies `u > 0`. -/
theorem pos_of_mulVec_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : OffDiagNonpos A)
    (hrow : ∀ i, 0 ≤ rowSum A i) {u : Fin n → ℝ} (hu : ∀ i, 0 < (A *ᵥ u) i) :
    ∀ i, 0 < u i := by
  intro k
  by_contra hk
  push Not at hk
  have : Nonempty (Fin n) := ⟨k⟩
  obtain ⟨i, hi⟩ := Finite.exists_min u
  have h1 := mulVec_le_at_min hA hi
  have h2 : u i * rowSum A i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ((hi k).trans hk) (hrow i)
  linarith [hu i]

/-- **Discrete maximum principle, weakly chained case.** Let `A` be a Z-matrix with nonnegative
row sums such that every row with zero row sum has a negative entry in a later column. Then
`A u ≥ 0` implies `u ≥ 0`. (Every chain of zero-sum rows ends at a strictly dominant row, e.g.
a Dirichlet row.) -/
theorem nonneg_of_mulVec_nonneg_chain {A : Matrix (Fin n) (Fin n) ℝ} (hA : OffDiagNonpos A)
    (hrow : ∀ i, 0 ≤ rowSum A i)
    (hchain : ∀ i, rowSum A i = 0 → ∃ j, i < j ∧ A i j < 0)
    {u : Fin n → ℝ} (hu : ∀ i, 0 ≤ (A *ᵥ u) i) : ∀ i, 0 ≤ u i := by
  intro k
  by_contra hk
  push Not at hk
  -- the set of minimizers, and its largest element
  set S : Finset (Fin n) := univ.filter fun j => ∀ l, u j ≤ u l with hS
  have : Nonempty (Fin n) := ⟨k⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min u
  have hne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  set i := S.max' hne
  have hiS : i ∈ S := S.max'_mem hne
  have hi : ∀ l, u i ≤ u l := by simpa [hS] using hiS
  have hneg : u i < 0 := (hi k).trans_lt hk
  have hT := sum_mul_sub_nonpos hA hi
  have hR : u i * rowSum A i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le (hrow i)
  have hAu := hu i
  rw [mulVec_apply_eq] at hAu
  have hT0 : ∑ j, A i j * (u j - u i) = 0 := by linarith
  have hR0 : u i * rowSum A i = 0 := by linarith
  have hrow0 : rowSum A i = 0 := by
    rcases mul_eq_zero.1 hR0 with h | h
    · exact absurd h hneg.ne
    · exact h
  obtain ⟨j, hij, hAij⟩ := hchain i hrow0
  have hterm : A i j * (u j - u i) = 0 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonpos fun l _ => ?_).1 hT0 j (mem_univ j)
    · exact hall
    · by_cases hil : i = l
      · subst hil; simp
      · exact mul_nonpos_of_nonpos_of_nonneg (hA i l hil) (sub_nonneg.2 (hi l))
  have huj : u j = u i := by
    rcases mul_eq_zero.1 hterm with h | h
    · exact absurd h hAij.ne
    · linarith
  have hjS : j ∈ S := by
    simp only [hS, mem_filter, mem_univ, true_and]
    intro l; rw [huj]; exact hi l
  exact absurd (S.le_max' j hjS) (not_le.2 hij)

/-! ### Index-sum helpers -/

/-- Summing a superdiagonal indicator over `Fin N`. -/
theorem sum_ite_succ (N i : ℕ) (x : ℝ) :
    ∑ j : Fin N, (if (j : ℕ) = i + 1 then x else 0) = if i + 1 < N then x else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j = i + 1 then x else 0) N]
  simp [Finset.sum_ite_eq']

/-- Summing a subdiagonal indicator over `Fin N` (for `i ≤ N`). -/
theorem sum_ite_pred (N i : ℕ) (hi : i ≤ N) (x : ℝ) :
    ∑ j : Fin N, (if (j : ℕ) + 1 = i then x else 0) = if i = 0 then 0 else x := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j + 1 = i then x else 0) N]
  rcases i with _ | k
  · simp
  · simp only [Nat.add_right_cancel_iff, Nat.add_one_ne_zero, ite_false]
    rw [Finset.sum_ite_eq']
    simp only [mem_range, ite_eq_left_iff, not_lt]
    intro h; omega

/-! ### The conservative finite-volume operator -/

/-- Finite-volume data on `N` unknown nodes: control-volume weights `vol i` and face
transmissibilities `κ i` (face between nodes `i` and `i+1`; `κ (N-1)` is the edge face). -/
structure FVGrid (N : ℕ) where
  /-- Control-volume weight of node `i`, approximately `V'(ψᵢ) h`. -/
  vol : ℕ → ℝ
  /-- Transmissibility of face `i + 1/2`, approximately `V'(ψ_{i+1/2}) D(ψ_{i+1/2}) / h`. -/
  κ : ℕ → ℝ

namespace FVGrid

variable {N : ℕ} (g : FVGrid N)

/-- Admissible data: positive volumes (`V' > 0`) and nonnegative transmissibilities (`D ≥ 0`). -/
structure Valid : Prop where
  /-- Volumes are positive. -/
  vol_pos : ∀ i < N, 0 < g.vol i
  /-- Transmissibilities are nonnegative. -/
  κ_nonneg : ∀ i < N, 0 ≤ g.κ i

/-- Left-face transmissibility of node `i`: zero at the axis (no-flux condition). -/
@[expose] def κL (i : ℕ) : ℝ := if i = 0 then 0 else g.κ (i - 1)

/-- Matrix of the finite-volume operator on the unknowns `u_0..u_{N-1}`:
`(L u)ᵢ = (κᵢ (u_{i+1} - uᵢ) - κ_{i-1} (uᵢ - u_{i-1})) / volᵢ`, with `κ_{-1} = 0` and the
edge value `u_N` moved to `bdry`. -/
@[expose] def L : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  ((if (j : ℕ) = i + 1 then g.κ i else 0) + (if (j : ℕ) + 1 = i then g.κ (i - 1) else 0)
    - (if j = i then g.κ i + g.κL i else 0)) / g.vol i

/-- Edge coupling vector: `κ_{N-1} / vol_{N-1}` in the last row, zero elsewhere. -/
@[expose] def bdry : Fin N → ℝ := fun i => if (i : ℕ) + 1 = N then g.κ i / g.vol i else 0

/-- The full discrete operator with Dirichlet edge value `Tedge`. -/
@[expose] def op (Tedge : ℝ) (u : Fin N → ℝ) : Fin N → ℝ := g.L *ᵥ u + Tedge • g.bdry

/-- Conservation: `L·1 = -bdry`. -/
theorem rowSum_L (i : Fin N) : rowSum g.L i = -g.bdry i := by
  have hi := i.isLt
  have hsum : rowSum g.L i =
      ((∑ j : Fin N, if (j : ℕ) = i + 1 then g.κ i else 0)
        + (∑ j : Fin N, if (j : ℕ) + 1 = i then g.κ (i - 1) else 0)
        - (∑ j : Fin N, if j = i then g.κ i + g.κL i else 0)) / g.vol i := by
    simp only [rowSum, L, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      add_div, sub_div]
  rw [hsum, sum_ite_succ, sum_ite_pred N i hi.le, Finset.sum_ite_eq', ite_eq_left (mem_univ i)]
  simp only [bdry, κL]
  split_ifs <;> first | omega | ring

/-- The edge coupling is nonnegative. -/
theorem bdry_nonneg (hg : g.Valid) (i : Fin N) : 0 ≤ g.bdry i := by
  unfold bdry
  split_ifs
  · exact div_nonneg (hg.κ_nonneg _ i.isLt) (hg.vol_pos _ i.isLt).le
  · exact le_rfl

/-- Off-diagonal entries of `L` are nonnegative. -/
theorem L_offDiag_nonneg (hg : g.Valid) {i j : Fin N} (hij : i ≠ j) : 0 ≤ g.L i j := by
  have hi := i.isLt
  unfold L
  rw [ite_eq_right (Ne.symm hij), sub_zero]
  apply div_nonneg _ (hg.vol_pos _ hi).le
  apply add_nonneg
  · split_ifs
    · exact hg.κ_nonneg _ hi
    · exact le_rfl
  · split_ifs
    · exact hg.κ_nonneg _ (by omega)
    · exact le_rfl

/-- The backward-Euler matrix `1 - Δt • L`. -/
@[expose] def backwardEuler (Δt : ℝ) : Matrix (Fin N) (Fin N) ℝ := 1 - Δt • g.L

/-- Row sums of the backward-Euler matrix: `1 + Δt · bdryᵢ`. -/
theorem rowSum_backwardEuler (Δt : ℝ) (i : Fin N) :
    rowSum (g.backwardEuler Δt) i = 1 + Δt * g.bdry i := by
  have h := g.rowSum_L i
  simp only [rowSum, backwardEuler, sub_apply, smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, one_apply, Finset.sum_ite_eq, mem_univ, ite_true] at h ⊢
  rw [h]; ring

/-- **The backward-Euler matrix is an M-matrix** for `vol > 0`, `κ ≥ 0` (i.e. `V' > 0`,
`D ≥ 0`) and every time step `Δt ≥ 0`: nonpositive off-diagonal entries and row sums `≥ 1`. -/
theorem backwardEuler_isMMatrix (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) :
    IsRowMMatrix (g.backwardEuler Δt) where
  offDiag i j hij := by
    simp only [backwardEuler, sub_apply, smul_apply, smul_eq_mul, one_apply_ne hij, zero_sub,
      neg_nonpos]
    exact mul_nonneg hΔt (g.L_offDiag_nonneg hg hij)
  rowSum_pos i := by
    rw [rowSum_backwardEuler]
    have := mul_nonneg hΔt (g.bdry_nonneg hg i)
    linarith

/-- `(1 - Δt L) v = v - Δt (L v)` pointwise. -/
theorem backwardEuler_mulVec (Δt : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    (g.backwardEuler Δt *ᵥ v) i = v i - Δt * (g.L *ᵥ v) i := by
  simp [backwardEuler, sub_mulVec, smul_mulVec]

/-- A backward-Euler **subsolution** with edge data `Tedge` and source `f`:
`s^{k+1} ≤ s^k + Δt (L s^{k+1} + Tedge^{k+1} bdry + f^{k+1})` componentwise. -/
@[expose] def IsSub (Δt : ℝ) (Tedge : ℕ → ℝ) (f : ℕ → Fin N → ℝ) (s : ℕ → Fin N → ℝ) :
    Prop :=
  ∀ k i, s (k + 1) i ≤ s k i + Δt * (g.op (Tedge (k + 1)) (s (k + 1)) i + f (k + 1) i)

/-- A backward-Euler **supersolution** (reverse inequality). -/
@[expose] def IsSuper (Δt : ℝ) (Tedge : ℕ → ℝ) (f : ℕ → Fin N → ℝ) (u : ℕ → Fin N → ℝ) :
    Prop :=
  ∀ k i, u k i + Δt * (g.op (Tedge (k + 1)) (u (k + 1)) i + f (k + 1) i) ≤ u (k + 1) i

/-- A **strict** backward-Euler subsolution. -/
@[expose] def IsStrictSub (Δt : ℝ) (Tedge : ℕ → ℝ) (f : ℕ → Fin N → ℝ) (s : ℕ → Fin N → ℝ) :
    Prop :=
  ∀ k i, s (k + 1) i < s k i + Δt * (g.op (Tedge (k + 1)) (s (k + 1)) i + f (k + 1) i)

/-- A backward-Euler **solution**:
`u^{k+1} = u^k + Δt (L u^{k+1} + Tedge^{k+1} bdry + f^{k+1})`. -/
@[expose] def IsSolution (Δt : ℝ) (Tedge : ℕ → ℝ) (f : ℕ → Fin N → ℝ) (u : ℕ → Fin N → ℝ) :
    Prop :=
  ∀ k i, u (k + 1) i = u k i + Δt * (g.op (Tedge (k + 1)) (u (k + 1)) i + f (k + 1) i)

/-- A solution is a supersolution. -/
theorem IsSolution.isSuper {Δt : ℝ} {Tedge : ℕ → ℝ} {f : ℕ → Fin N → ℝ} {u : ℕ → Fin N → ℝ}
    (h : g.IsSolution Δt Tedge f u) : g.IsSuper Δt Tedge f u := fun k i => (h k i).symm.le

/-- A solution is a subsolution. -/
theorem IsSolution.isSub {Δt : ℝ} {Tedge : ℕ → ℝ} {f : ℕ → Fin N → ℝ} {u : ℕ → Fin N → ℝ}
    (h : g.IsSolution Δt Tedge f u) : g.IsSub Δt Tedge f u := fun k i => (h k i).le

/-- A strict subsolution is a subsolution. -/
theorem IsStrictSub.isSub {Δt : ℝ} {Tedge : ℕ → ℝ} {f : ℕ → Fin N → ℝ} {s : ℕ → Fin N → ℝ}
    (h : g.IsStrictSub Δt Tedge f s) : g.IsSub Δt Tedge f s := fun k i => (h k i).le

/-- One comparison step: the backward-Euler matrix applied to `u^{k+1} - s^{k+1}` dominates
`(u^k - s^k) + Δt ((Tu - Ts) bdry + (fu - fs))`. -/
theorem step_lower_bound {Δt : ℝ} {Ts Tu : ℕ → ℝ} {fs fu : ℕ → Fin N → ℝ}
    {s u : ℕ → Fin N → ℝ} (hs : g.IsSub Δt Ts fs s) (hu : g.IsSuper Δt Tu fu u) (k : ℕ)
    (i : Fin N) :
    u k i - s k i + Δt * ((Tu (k + 1) - Ts (k + 1)) * g.bdry i + (fu (k + 1) i - fs (k + 1) i))
      ≤ (g.backwardEuler Δt *ᵥ (u (k + 1) - s (k + 1))) i := by
  have h1 := hs k i
  have h2 := hu k i
  simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rw [backwardEuler_mulVec, mulVec_sub, Pi.sub_apply, Pi.sub_apply]
  nlinarith

/-- **Discrete comparison principle (backward Euler).** If `s` is a subsolution and `u` a
supersolution with ordered edge data `Ts ≤ Tu`, ordered sources `fs ≤ fu` and ordered initial
data `s⁰ ≤ u⁰`, then `sᵏ ≤ uᵏ` for every time step `k`, for any `Δt ≥ 0`. -/
theorem le_of_subsolution (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) {Ts Tu : ℕ → ℝ}
    {fs fu : ℕ → Fin N → ℝ} {s u : ℕ → Fin N → ℝ} (hs : g.IsSub Δt Ts fs s)
    (hu : g.IsSuper Δt Tu fu u) (hT : ∀ k, Ts k ≤ Tu k) (hf : ∀ k i, fs k i ≤ fu k i)
    (h0 : ∀ i, s 0 i ≤ u 0 i) : ∀ k i, s k i ≤ u k i := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
    have hpos : ∀ i, 0 ≤ (g.backwardEuler Δt *ᵥ (u (k + 1) - s (k + 1))) i := by
      intro i
      refine le_trans ?_ (g.step_lower_bound hs hu k i)
      have := mul_nonneg (sub_nonneg.2 (hT (k + 1))) (g.bdry_nonneg hg i)
      have := mul_nonneg hΔt (add_nonneg this (sub_nonneg.2 (hf (k + 1) i)))
      linarith [ih i]
    intro i
    have := nonneg_of_mulVec_nonneg (g.backwardEuler_isMMatrix hg hΔt) hpos i
    simpa [sub_nonneg] using this

/-- **Strict discrete comparison.** Under the hypotheses of `le_of_subsolution` with a strict
subsolution, `sᵏ < uᵏ` at every step `k ≥ 1`; if moreover `s⁰ < u⁰`, then for all `k`. -/
theorem lt_of_strictSubsolution (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) {Ts Tu : ℕ → ℝ}
    {fs fu : ℕ → Fin N → ℝ} {s u : ℕ → Fin N → ℝ} (hs : g.IsStrictSub Δt Ts fs s)
    (hu : g.IsSuper Δt Tu fu u) (hT : ∀ k, Ts k ≤ Tu k) (hf : ∀ k i, fs k i ≤ fu k i)
    (h0 : ∀ i, s 0 i ≤ u 0 i) : ∀ k i, s (k + 1) i < u (k + 1) i := by
  have hle := g.le_of_subsolution hg hΔt hs.isSub hu hT hf h0
  intro k
  have hpos : ∀ i, 0 < (g.backwardEuler Δt *ᵥ (u (k + 1) - s (k + 1))) i := by
    intro i
    have h1 := hs k i
    have h2 := hu k i
    have h3 := hle k i
    have hb := mul_nonneg (sub_nonneg.2 (hT (k + 1))) (g.bdry_nonneg hg i)
    have hfi := hf (k + 1) i
    simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [backwardEuler_mulVec, mulVec_sub, Pi.sub_apply, Pi.sub_apply]
    nlinarith
  intro i
  have hM := g.backwardEuler_isMMatrix hg hΔt
  have := pos_of_mulVec_pos hM.offDiag (fun i => (hM.rowSum_pos i).le) hpos i
  simpa [sub_pos] using this

/-- Strict comparison for all steps when the initial data are strictly ordered. -/
theorem lt_of_strictSubsolution' (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) {Ts Tu : ℕ → ℝ}
    {fs fu : ℕ → Fin N → ℝ} {s u : ℕ → Fin N → ℝ} (hs : g.IsStrictSub Δt Ts fs s)
    (hu : g.IsSuper Δt Tu fu u) (hT : ∀ k, Ts k ≤ Tu k) (hf : ∀ k i, fs k i ≤ fu k i)
    (h0 : ∀ i, s 0 i < u 0 i) : ∀ k i, s k i < u k i := by
  intro k
  cases k with
  | zero => exact h0
  | succ k => exact g.lt_of_strictSubsolution hg hΔt hs hu hT hf (fun i => (h0 i).le) k

/-! ### Stationary (steady semi-discrete) comparison -/

/-- **Steady discrete maximum principle.** If all transmissibilities are positive (`D > 0`),
`L u + Tedge·bdry ≤ 0` (a discrete supersolution of the steady problem) and `Tedge ≥ 0`, then
`u ≥ 0`. Proved with the weakly chained lemma applied to `-L`. -/
theorem steady_nonneg (hg : g.Valid) (hκ : ∀ i < N, 0 < g.κ i) {Tedge : ℝ} (hT : 0 ≤ Tedge)
    {u : Fin N → ℝ} (hu : ∀ i, g.op Tedge u i ≤ 0) : ∀ i, 0 ≤ u i := by
  have hrow : ∀ i, rowSum (-g.L) i = g.bdry i := by
    intro i
    have := g.rowSum_L i
    simp only [rowSum, Matrix.neg_apply, Finset.sum_neg_distrib] at this ⊢
    linarith
  refine nonneg_of_mulVec_nonneg_chain (A := -g.L) ?_ ?_ ?_ ?_
  · intro i j hij
    simp only [Matrix.neg_apply, neg_nonpos]
    exact g.L_offDiag_nonneg hg hij
  · intro i; rw [hrow]; exact g.bdry_nonneg hg i
  · intro i h0
    rw [hrow] at h0
    have hi := i.isLt
    have hlast : ¬ ((i : ℕ) + 1 = N) := by
      intro h
      have : 0 < g.bdry i := by
        simp only [bdry, h, ite_true]
        exact div_pos (hκ _ hi) (hg.vol_pos _ hi)
      linarith
    refine ⟨⟨i + 1, by omega⟩, Fin.lt_def.2 (by simp), ?_⟩
    have hne : (⟨i + 1, by omega⟩ : Fin N) ≠ i := fun h => by simp [Fin.ext_iff] at h
    simp only [Matrix.neg_apply, L, neg_neg_iff_pos, ite_true, hne, ite_false,
      show ¬ ((i : ℕ) + 1 + 1 = i) by omega, add_zero, sub_zero]
    exact div_pos (hκ _ hi) (hg.vol_pos _ hi)
  · intro i
    have h := hu i
    simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [neg_mulVec, Pi.neg_apply]
    nlinarith [g.bdry_nonneg hg i]

/-- **Steady discrete comparison.** With `κ > 0`, if `L s + Ts·bdry + fs ≥ 0` and
`L u + Tu·bdry + fu ≤ 0` with `Ts ≤ Tu`, `fs ≤ fu`, then `s ≤ u`. -/
theorem steady_le (hg : g.Valid) (hκ : ∀ i < N, 0 < g.κ i) {Ts Tu : ℝ} {fs fu s u : Fin N → ℝ}
    (hs : ∀ i, 0 ≤ g.op Ts s i + fs i) (hu : ∀ i, g.op Tu u i + fu i ≤ 0) (hT : Ts ≤ Tu)
    (hf : ∀ i, fs i ≤ fu i) : ∀ i, s i ≤ u i := by
  have := g.steady_nonneg hg hκ (sub_nonneg.2 hT) (u := u - s) (fun i => by
    have h1 := hs i
    have h2 := hu i
    have h3 := hf i
    simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_sub, Pi.sub_apply] at h1 h2 ⊢
    nlinarith)
  intro i
  simpa [sub_nonneg] using this i

/-! ### Discrete conservation and constant states -/

/-- Constants are annihilated when the edge value matches: `L (c·1) + c·bdry = 0`. -/
theorem op_const (c : ℝ) : g.op c (fun _ => c) = 0 := by
  funext i
  have h := g.rowSum_L i
  simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mulVec, dotProduct]
  simp only [rowSum] at h
  rw [← Finset.sum_mul, h]; ring

/-- **Sanity: constant states are preserved.** The constant sequence `uᵏ = c` is a
backward-Euler solution with edge data `c` and zero source, for every `Δt`. -/
theorem constant_isSolution (Δt c : ℝ) :
    g.IsSolution Δt (fun _ => c) (fun _ _ => 0) (fun _ _ => c) := by
  intro k i
  simp [g.op_const c]

/-- Extension of the unknowns by the Dirichlet edge value: `uᵢ` for `i < N`, `Tedge` otherwise. -/
@[expose] def extend (u : Fin N → ℝ) (Tedge : ℝ) (j : ℕ) : ℝ :=
  if h : j < N then u ⟨j, h⟩ else Tedge

/-- Diffusive flux through the face `j - 1/2`, i.e. `κ_{j-1} (u_j - u_{j-1})`; zero for
`j = 0` (no-flux axis). -/
@[expose] def faceFlux (u : Fin N → ℝ) (Tedge : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else g.κ (j - 1) * (extend u Tedge j - extend u Tedge (j - 1))

/-- Weighted indicator sum over `Fin N`. -/
theorem sum_ite_mul (N a : ℕ) (c : ℝ) (f : ℕ → ℝ) :
    ∑ j : Fin N, (if (j : ℕ) = a then c else 0) * f j = if a < N then c * f a else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (if j = a then c else 0) * f j) N]
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- **Conservative form.** `vol_i (L u + Tedge·bdry)_i` is the difference of the fluxes through
the faces `i + 1/2` and `i - 1/2`. -/
theorem vol_mul_op (hg : g.Valid) (Tedge : ℝ) (u : Fin N → ℝ) (i : Fin N) :
    g.vol i * g.op Tedge u i = g.faceFlux u Tedge (i + 1) - g.faceFlux u Tedge i := by
  have hi := i.isLt
  have hv := (hg.vol_pos _ hi).ne'
  have hu : ∀ j : Fin N, u j = extend u Tedge j := fun j => by simp [extend, j.isLt]
  have hsum : (g.L *ᵥ u) i =
      ((∑ j : Fin N, (if (j : ℕ) = i + 1 then g.κ i else 0) * extend u Tedge j)
        + (∑ j : Fin N, (if (j : ℕ) = i - 1 then (if (i : ℕ) = 0 then 0 else g.κ (i - 1)) else 0)
            * extend u Tedge j)
        - (∑ j : Fin N, (if (j : ℕ) = i then g.κ i + g.κL i else 0) * extend u Tedge j))
        / g.vol i := by
    simp only [mulVec, dotProduct, L, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hu j]
    simp only [Fin.ext_iff]
    split_ifs <;> first | omega | ring
  simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsum, sum_ite_mul, faceFlux, bdry,
    κL]
  rw [mul_add, mul_div_cancel₀ _ hv]
  have hext : ∀ j, N ≤ j → extend u Tedge j = Tedge := fun j hj => by
    simp [extend, not_lt.2 hj]
  simp only [Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
  split_ifs <;> first | omega | contradiction |
    (rw [hext ((i : ℕ) + 1) (by omega)]; field_simp; ring) | (field_simp; ring)

/-- **Discrete conservation.** The volume-weighted sum of the operator telescopes to the flux
through the edge face: `∑ᵢ volᵢ (L u + Tedge·bdry)ᵢ = κ_{N-1} (Tedge - u_{N-1})`. The axis
contributes no flux. -/
theorem flux_telescope (hg : g.Valid) (hN : 0 < N) (Tedge : ℝ) (u : Fin N → ℝ) :
    ∑ i : Fin N, g.vol i * g.op Tedge u i = g.κ (N - 1) * (Tedge - u ⟨N - 1, by omega⟩) := by
  simp_rw [g.vol_mul_op hg]
  rw [Fin.sum_univ_eq_sum_range (fun i => g.faceFlux u Tedge (i + 1) - g.faceFlux u Tedge i) N,
    Finset.sum_range_sub]
  have h1 : extend u Tedge N = Tedge := by simp [extend]
  have h2 : extend u Tedge (N - 1) = u ⟨N - 1, by omega⟩ := by
    simp [extend, show N - 1 < N by omega]
  simp [faceFlux, show N ≠ 0 by omega, h1, h2]

/-- **Discrete maximum principle (upper bound).** A backward-Euler subsolution with
nonpositive source, edge data `≤ M` and initial data `≤ M` stays `≤ M` for all steps. -/
theorem le_const_of_isSub (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) {Tedge : ℕ → ℝ}
    {f : ℕ → Fin N → ℝ} {u : ℕ → Fin N → ℝ} {M : ℝ} (hu : g.IsSub Δt Tedge f u)
    (hT : ∀ k, Tedge k ≤ M) (hf : ∀ k i, f k i ≤ 0) (h0 : ∀ i, u 0 i ≤ M) :
    ∀ k i, u k i ≤ M :=
  g.le_of_subsolution hg hΔt hu (g.constant_isSolution Δt M).isSuper hT hf h0

/-- **Discrete minimum principle (lower bound).** A backward-Euler supersolution with
nonnegative source, edge data `≥ m` and initial data `≥ m` stays `≥ m` for all steps. -/
theorem const_le_of_isSuper (hg : g.Valid) {Δt : ℝ} (hΔt : 0 ≤ Δt) {Tedge : ℕ → ℝ}
    {f : ℕ → Fin N → ℝ} {u : ℕ → Fin N → ℝ} {m : ℝ} (hu : g.IsSuper Δt Tedge f u)
    (hT : ∀ k, m ≤ Tedge k) (hf : ∀ k i, 0 ≤ f k i) (h0 : ∀ i, m ≤ u 0 i) :
    ∀ k i, m ≤ u k i :=
  g.le_of_subsolution hg hΔt (g.constant_isSolution Δt m).isSub hu hT hf h0

end FVGrid

/-! ### Construction from coefficient functions -/

/-- The finite-volume data of `(1/V')(V' D u')'` on the uniform grid `ψᵢ = i/N`:
`vol i = V'(ψᵢ) h` (halved at the axis node) and `κ i = V'(ψ_{i+1/2}) D(ψ_{i+1/2}) / h`. -/
@[expose] def FVGrid.ofCoeffs (N : ℕ) (Vp D : ℝ → ℝ) : FVGrid N where
  vol i := (if i = 0 then (1 / N : ℝ) / 2 else 1 / N) * Vp (i / N)
  κ i := Vp ((i + 1 / 2) / N) * D ((i + 1 / 2) / N) * N

/-- The coefficient construction is admissible when `V' > 0` and `D ≥ 0` on `[0,1]`.
**Coordinate assumption:** `V' > 0` is required *including the axis* `ψ = 0` (the axis
control volume is `V'(0) h / 2`). This holds when `ψ` is the normalized toroidal flux, as in
the kernel `PlasmaLean.Transport`, but fails for the minor radius `ψ = r`, where `V'(0) = 0`;
that coordinate needs a different axis cell. -/
theorem FVGrid.ofCoeffs_valid {N : ℕ} {Vp D : ℝ → ℝ} (hVp : ∀ ψ, 0 ≤ ψ → ψ ≤ 1 → 0 < Vp ψ)
    (hD : ∀ ψ, 0 ≤ ψ → ψ ≤ 1 → 0 ≤ D ψ) : (FVGrid.ofCoeffs N Vp D).Valid := by
  constructor
  · intro i hi
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi.le
    have h1 : 0 < Vp (i / N) := hVp _ (by positivity) (by rw [div_le_one hN]; exact hiN)
    simp only [FVGrid.ofCoeffs]
    split_ifs <;> positivity
  · intro i hi
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hle : ((i : ℝ) + 1 / 2) / N ≤ 1 := by rw [div_le_one hN]; linarith
    have h1 := hVp _ (by positivity) hle
    have h2 := hD _ (by positivity) hle
    simp only [FVGrid.ofCoeffs]
    positivity

/-! ### Sanity: a 3-node instance with exact rationals -/

/-- Three nodes, `vol = (1/2, 1, 1)`, `κ = (1, 2, 3)`. -/
@[expose] def g3 : FVGrid 3 where
  vol i := if i = 0 then 1 / 2 else 1
  κ i := i + 1

/-- The 3-node data are admissible. -/
theorem g3_valid : g3.Valid where
  vol_pos i _ := by simp only [g3]; split_ifs <;> norm_num
  κ_nonneg i _ := by simp only [g3]; positivity

/-- The backward-Euler matrix of `g3` for `Δt = 1`, computed exactly. -/
theorem g3_backwardEuler : g3.backwardEuler 1 = !![3, -2, 0; -1, 4, -2; 0, -2, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FVGrid.backwardEuler, FVGrid.L, FVGrid.κL, g3, one_apply]

/-- The edge coupling of `g3` is `(0, 0, 3)`. -/
theorem g3_bdry : g3.bdry = ![0, 0, 3] := by
  ext i
  fin_cases i <;> norm_num [FVGrid.bdry, g3]

/-- One backward-Euler step from `u⁰ = 0` with edge value `1`: `u¹ = (1/4, 3/8, 5/8)`. -/
@[expose] def g3Seq : ℕ → Fin 3 → ℝ := fun k => if k = 0 then 0 else ![1 / 4, 3 / 8, 5 / 8]

/-- `g3Seq` satisfies the backward-Euler equation at the first step. -/
theorem g3_step : ∀ i, g3Seq 1 i = g3Seq 0 i + 1 * (g3.op 1 (g3Seq 1) i + 0) := by
  intro i
  have hL : g3.L = !![-2, 2, 0; 1, -3, 2; 0, 2, -5] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [FVGrid.L, FVGrid.κL, g3]
  simp only [FVGrid.op, hL, g3_bdry, g3Seq]
  fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_three]

/-- The discrete maximum principle in action: the first step lies strictly between the initial
value `0` and the edge value `1`. -/
theorem g3_step_bounds : ∀ i, 0 < g3Seq 1 i ∧ g3Seq 1 i < 1 := by
  intro i
  fin_cases i <;> norm_num [g3Seq]

/-! ### Rejected instance: negative diffusivity -/

/-- Three nodes with unit volumes and a **negative** first transmissibility `κ₀ = -1/4`. -/
@[expose] def gNeg : FVGrid 3 where
  vol _ := 1
  κ i := if i = 0 then -1 / 4 else 0

/-- `gNeg` is not admissible. -/
theorem gNeg_not_valid : ¬ gNeg.Valid := fun h => by
  have := h.κ_nonneg 0 (by norm_num)
  norm_num [gNeg] at this

/-- The backward-Euler matrix of `gNeg` for `Δt = 1` has a positive off-diagonal entry. -/
theorem gNeg_backwardEuler :
    gNeg.backwardEuler 1 = !![3 / 4, 1 / 4, 0; 1 / 4, 3 / 4, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [FVGrid.backwardEuler, FVGrid.L, FVGrid.κL, gNeg, one_apply]

/-- **Rejected fixture.** With negative diffusivity the maximum principle fails:
for `u = (3, -1, 0)`, `(1 - L) u = (2, 0, 0) ≥ 0` but `u₁ = -1 < 0`. -/
theorem gNeg_counterexample :
    (∀ i, 0 ≤ (gNeg.backwardEuler 1 *ᵥ ![3, -1, 0]) i) ∧ (![(3 : ℝ), -1, 0] 1 < 0) := by
  rw [gNeg_backwardEuler]
  refine ⟨fun i => ?_, by norm_num⟩
  fin_cases i <;> norm_num [mulVec, dotProduct, Fin.sum_univ_three]

/-- Consequently the backward-Euler matrix of `gNeg` is not an M-matrix. -/
theorem gNeg_not_isRowMMatrix : ¬ IsRowMMatrix (gNeg.backwardEuler 1) := fun h => by
  have := nonneg_of_mulVec_nonneg h gNeg_counterexample.1 1
  linarith [gNeg_counterexample.2]

end PlasmaLean.Certificates.DiscreteMax
