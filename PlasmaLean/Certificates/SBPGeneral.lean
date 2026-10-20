/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.SBP
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The classical second-order SBP operator on `N ≥ 3` points

Track T5. This generalizes the four-point operator `sbp2` of `PlasmaLean.Certificates.SBP` to
an arbitrary number `N ≥ 3` of grid points with spacing `h > 0`:

* `sbpGenP N h = h · diag(1/2, 1, …, 1, 1/2)`;
* `sbpGenD N h`: one-sided rows `(-1, 1)/h` at both ends, central rows `(-1/2, 0, 1/2)/h`
  in the interior;
* `sbpGenB N = diag(-1, 0, …, 0, 1)`.

The SBP identity `P D + Dᵀ P = B` is proved **structurally**, for all `N` at once, by a case
analysis on the natural-number values of the indices (no matrix is ever evaluated). The key
observation (`sbpGenP_mul_D`) is that `P D = S + ½ B` with `S` the skew matrix
`S i (i+1) = ½`, `S (i+1) i = -½`.

Main results:

* `sbpGen N h hN hh : SBPOperator N`, the operator for `3 ≤ N`, `0 < h`;
* `sbpGen_energy_hasDerivAt`: along `u' = -D u`, `d/dt (uᵀPu) = u₀² - u_{N-1}²`;
* sanity: `sbpGenD_four`, `sbpGenP_four` (agreement with the 4-point `sbp2`),
  `sbpGen_energy_deriv_nonpos_of_inflow_zero`, the accepted fixture `sbpGen_fixture_five`,
  and the rejected fixture `sbpGenDZeroRow_rejected` (zero boundary row breaks the identity).
-/

public section

noncomputable section
namespace PlasmaLean.Certificates

open Matrix

/-- Diagonal weights of the norm: `h/2` at the two end points, `h` in the interior. -/
@[expose] def sbpGenWeight (N : ℕ) (h : ℝ) (i : Fin N) : ℝ :=
  if (i : ℕ) = 0 ∨ (i : ℕ) + 1 = N then h / 2 else h

/-- The norm matrix `P = h · diag(1/2, 1, …, 1, 1/2)` on `N` points. -/
@[expose] def sbpGenP (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  diagonal (sbpGenWeight N h)

/-- The difference matrix on `N` points: rows `0` and `N-1` are the one-sided differences
`(u₁ - u₀)/h` and `(u_{N-1} - u_{N-2})/h`; interior rows are central differences
`(u_{i+1} - u_{i-1})/(2h)`. -/
@[expose] def sbpGenD (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if (i : ℕ) = 0 then
    (if (j : ℕ) = 0 then -1 / h else if (j : ℕ) = 1 then 1 / h else 0)
  else if (i : ℕ) + 1 = N then
    (if (j : ℕ) + 2 = N then -1 / h else if (j : ℕ) + 1 = N then 1 / h else 0)
  else
    (if (j : ℕ) + 1 = i then -1 / (2 * h) else if (j : ℕ) = (i : ℕ) + 1 then 1 / (2 * h) else 0)

/-- The boundary matrix `diag(-1, 0, …, 0, 1)`. -/
@[expose] def sbpGenB (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  diagonal fun i => if (i : ℕ) = 0 then -1 else if (i : ℕ) + 1 = N then 1 else 0

/-- The matrix `Q = P D` in closed form: `½` on the superdiagonal, `-½` on the subdiagonal,
plus `-½` at `(0,0)` and `½` at `(N-1,N-1)`. -/
@[expose] def sbpGenQ (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  (if (j : ℕ) = (i : ℕ) + 1 then 1 / 2 else 0) - (if (j : ℕ) + 1 = i then 1 / 2 else 0)
    + (if j = i then (if (i : ℕ) = 0 then -1 / 2 else if (i : ℕ) + 1 = N then 1 / 2 else 0)
       else 0)

/-- Structural form of `P D`: for `N ≥ 3` and `h ≠ 0`, `P D = Q` entrywise. -/
theorem sbpGenP_mul_D {N : ℕ} {h : ℝ} (hN : 3 ≤ N) (hh : h ≠ 0) :
    sbpGenP N h * sbpGenD N h = sbpGenQ N := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [sbpGenP, diagonal_mul, sbpGenWeight, sbpGenD, sbpGenQ, Fin.ext_iff]
  split_ifs <;> first | omega | (field_simp; ring)

/-- **SBP identity for all `N ≥ 3`**: `P D + Dᵀ P = diag(-1, 0, …, 0, 1)`. -/
theorem sbpGen_identity {N : ℕ} {h : ℝ} (hN : 3 ≤ N) (hh : h ≠ 0) :
    sbpGenP N h * sbpGenD N h + (sbpGenD N h)ᵀ * sbpGenP N h = sbpGenB N := by
  have hT : (sbpGenD N h)ᵀ * sbpGenP N h = (sbpGenP N h * sbpGenD N h)ᵀ := by
    rw [transpose_mul, sbpGenP, diagonal_transpose]
  rw [hT, sbpGenP_mul_D hN hh]
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.add_apply, transpose_apply, sbpGenQ, sbpGenB, diagonal_apply, Fin.ext_iff]
  split_ifs <;> first | omega | norm_num

/-- The weights are positive for `h > 0`. -/
theorem sbpGenWeight_pos {N : ℕ} {h : ℝ} (hh : 0 < h) (i : Fin N) : 0 < sbpGenWeight N h i := by
  unfold sbpGenWeight; split_ifs <;> positivity

/-- The quadratic form of a diagonal matrix. -/
theorem diagonal_quadForm {N : ℕ} (w u : Fin N → ℝ) :
    u ⬝ᵥ diagonal w *ᵥ u = ∑ i, w i * u i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The classical second-order SBP operator on `N ≥ 3` points with spacing `h > 0`. -/
def sbpGen (N : ℕ) (h : ℝ) (hN : 3 ≤ N) (hh : 0 < h) : SBPOperator N where
  D := sbpGenD N h
  P := sbpGenP N h
  B := sbpGenB N
  P_symm := diagonal_transpose _
  P_posDef := by
    intro u hu
    rw [sbpGenP, diagonal_quadForm]
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hu (funext hc)
    refine Finset.sum_pos' (fun i _ => mul_nonneg (sbpGenWeight_pos hh i).le (sq_nonneg _))
      ⟨k, Finset.mem_univ _, mul_pos (sbpGenWeight_pos hh k) (by positivity)⟩
  sbp_identity := sbpGen_identity hN hh.ne'

/-- The quadratic form of the boundary matrix: `uᵀ B u = u_{N-1}² - u₀²` (for `N ≥ 2`). -/
theorem sbpGenB_quadForm {N : ℕ} (hN : 2 ≤ N) (u : Fin N → ℝ) :
    u ⬝ᵥ sbpGenB N *ᵥ u = u ⟨N - 1, by omega⟩ ^ 2 - u ⟨0, by omega⟩ ^ 2 := by
  rw [sbpGenB, diagonal_quadForm]
  rw [Fintype.sum_eq_add (⟨0, by omega⟩ : Fin N) ⟨N - 1, by omega⟩
    (by simp only [ne_eq, Fin.mk.injEq]; omega)]
  · simp only [ite_true, show N - 1 ≠ 0 by omega, show N - 1 + 1 = N by omega, ite_false]
    ring
  · rintro x ⟨h0, h1⟩
    have h0' : (x : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    have h1' : (x : ℕ) ≠ N - 1 := fun h => h1 (Fin.ext h)
    simp [h0', show (x : ℕ) + 1 ≠ N by omega]

/-- **Energy law for all `N ≥ 3`**: along the semi-discrete advection `u' = -D u`,
`d/dt (uᵀPu) = u₀² - u_{N-1}²` (inflow minus outflow for `uₜ + uₓ = 0`). -/
theorem sbpGen_energy_hasDerivAt {N : ℕ} {h : ℝ} (hN : 3 ≤ N) (hh : 0 < h)
    {u : ℝ → Fin N → ℝ} {t : ℝ} (hu : HasDerivAt u (-(sbpGenD N h *ᵥ u t)) t) :
    HasDerivAt (fun s => u s ⬝ᵥ sbpGenP N h *ᵥ u s)
      (u t ⟨0, by omega⟩ ^ 2 - u t ⟨N - 1, by omega⟩ ^ 2) t := by
  refine ((sbpGen N h hN hh).energy_hasDerivAt (u := u) hu).congr_deriv ?_
  change -(u t ⬝ᵥ sbpGenB N *ᵥ u t) = _
  rw [sbpGenB_quadForm (by omega)]
  ring

/-- Sanity: with zero inflow data `u₀(t) = 0`, the discrete energy is nonincreasing at `t`,
for every `N ≥ 3`. -/
theorem sbpGen_energy_deriv_nonpos_of_inflow_zero {N : ℕ} {h : ℝ} (hN : 3 ≤ N) (hh : 0 < h)
    {u : ℝ → Fin N → ℝ} {t : ℝ} (hu : HasDerivAt u (-(sbpGenD N h *ᵥ u t)) t)
    (h0 : u t ⟨0, by omega⟩ = 0) :
    ∃ d, HasDerivAt (fun s => u s ⬝ᵥ sbpGenP N h *ᵥ u s) d t ∧ d ≤ 0 :=
  ⟨_, sbpGen_energy_hasDerivAt hN hh hu, by
    rw [h0]; nlinarith [sq_nonneg (u t ⟨N - 1, by omega⟩)]⟩

/-- Sanity (special case): for `N = 4` the general difference matrix is the 4-point `sbp2D`. -/
theorem sbpGenD_four (h : ℝ) : sbpGenD 4 h = sbp2D h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sbpGenD, sbp2D]

/-- Sanity (special case): for `N = 4` the general norm matrix is the 4-point `sbp2P`. -/
theorem sbpGenP_four (h : ℝ) : sbpGenP 4 h = sbp2P h := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sbpGenP, sbpGenWeight, sbp2P, diagonal]

/-- Sanity (accepted fixture, discrete integration by parts on 5 points): for
`u = (1, 2, 3, 4, 5)` and `h = 1`, `uᵀ (P D) u = ½ (5² - 1²) = 12`. -/
theorem sbpGen_fixture_five :
    ![(1 : ℝ), 2, 3, 4, 5] ⬝ᵥ (sbpGenP 5 1 * sbpGenD 5 1) *ᵥ ![1, 2, 3, 4, 5] = 12 := by
  refine ((sbpGen 5 1 (by norm_num) one_pos).quadratic_identity ![1, 2, 3, 4, 5]).trans ?_
  change (1 / 2) * (![(1 : ℝ), 2, 3, 4, 5] ⬝ᵥ sbpGenB 5 *ᵥ ![1, 2, 3, 4, 5]) = 12
  rw [sbpGenB_quadForm (by norm_num)]
  norm_num

/-- The difference matrix with its first (one-sided) row replaced by zeros. -/
@[expose] def sbpGenDZeroRow (N : ℕ) (h : ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  if (i : ℕ) = 0 then 0 else sbpGenD N h i j

/-- Rejected fixture: the identity `P D + Dᵀ P = B` fails if the first one-sided boundary row
is replaced by a zero row (5 points, `h = 1`): the `(0,0)` entry is `0 ≠ -1`. -/
theorem sbpGenDZeroRow_rejected :
    sbpGenP 5 1 * sbpGenDZeroRow 5 1 + (sbpGenDZeroRow 5 1)ᵀ * sbpGenP 5 1 ≠ sbpGenB 5 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [sbpGenDZeroRow, sbpGenP, sbpGenB, diagonal_mul, mul_diagonal] at this

end PlasmaLean.Certificates
