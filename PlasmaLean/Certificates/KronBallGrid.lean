/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBall

/-!
# Grid centres for the Kronecker ball arithmetic

Centres of `Certificates/KronBall` given by integer grids: `gridPolyNM N M g = ∑_{i ≤ 2N, j ≤ 2M}
g i j uⁱ vʲ`, with

* packed storage (`fieldW`, `halfGrid`) and the stellarator-symmetric completion `symGrid`
  (`g(2N − i, 2M − j) = s g(i, j)`, `symGrid_refl`);
* the degree box, the `ℓ¹` bound `gridL1NM` and the Kronecker image `packGridNM` (computable;
  `kron_gridPolyNM`);
* the coefficients (`coefZ2_gridPolyNM`), reality of symmetric centres (`isReal_ctr_sym`),
  analyticity (`ana_ctr_grid`) and the derivatives `dS a b` with integer symbols
  (`dS_ctr_grid`: multiply the grid by `a(i − N) + b(j − M)` and lower the phase by one);
* the data of a node polynomial `G = evH e − c T^{dd} V^{de} Q` (`node_box`, `node_l1`,
  `node_kron`).

**Sanity.** `fieldW_zero` (the offset field decodes to `0`), `symGrid_centre_odd` (odd grids
vanish at the centre).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Certificates.KronBall

open Polynomial Finset PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Theory.KAM WEll1Z2 Complex

/-! ## Packed grids -/

/-- Field `f` (width `F`, offset `2^{F−1}`) of a packed literal. -/
def fieldW (F data f : ℕ) : ℤ := (((data >>> (F * f)) % 2 ^ F : ℕ) : ℤ) - 2 ^ (F - 1)

/-- **Sanity**: the offset alone decodes to `0`. -/
theorem fieldW_zero (F : ℕ) (hF : 1 ≤ F) : fieldW F (2 ^ (F - 1)) 0 = 0 := by
  have h : 2 ^ (F - 1) < 2 ^ F := Nat.pow_lt_pow_right (by norm_num) (by omega)
  simp [fieldW, Nat.mod_eq_of_lt h]

/-- The half grid `i ≥ N` of a packed literal (rows of length `2M + 1`), zero for `i < N`. -/
def halfGrid (F N M data : ℕ) (i j : ℕ) : ℤ :=
  if N ≤ i then fieldW F data ((i - N) * (2 * M + 1) + j) else 0

/-- The half grid `i ≥ N` stored as one packed literal per row `i − N` (rows of `2M + 1` fields):
the kernel extracts a field from a short literal. -/
def halfGridR (F N : ℕ) (rows : List ℕ) (i j : ℕ) : ℤ :=
  if N ≤ i then fieldW F (rows.getD (i - N) 0) j else 0

/-- The symmetric completion `g(i, j) = h(i, j) + s h(2N − i, 2M − j)`. -/
def symGrid (N M : ℕ) (s : ℤ) (h : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  h i j + s * h (2 * N - i) (2 * M - j)

/-- Reflection symmetry of a completed grid (`s² = 1`). -/
theorem symGrid_refl (N M : ℕ) {s : ℤ} (hs : s * s = 1) (h : ℕ → ℕ → ℤ) {i j : ℕ}
    (hi : i ≤ 2 * N) (hj : j ≤ 2 * M) :
    symGrid N M s h (2 * N - i) (2 * M - j) = s * symGrid N M s h i j := by
  unfold symGrid
  rw [show 2 * N - (2 * N - i) = i by omega, show 2 * M - (2 * M - j) = j by omega]
  linear_combination (-(h (2 * N - i) (2 * M - j))) * hs

/-- **Sanity**: an odd grid vanishes at the centre. -/
theorem symGrid_centre_odd (N M : ℕ) (h : ℕ → ℕ → ℤ) : symGrid N M (-1) h N M = 0 := by
  simp [symGrid, show 2 * N - N = N by omega, show 2 * M - M = M by omega]

/-! ## Grid polynomials -/

/-- `∑_{i ≤ 2N, j ≤ 2M} g i j uⁱ vʲ`. -/
def gridPolyNM (N M : ℕ) (g : ℕ → ℕ → ℤ) : P2 :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), monomial j (monomial i (g i j))

/-- The degree box of a grid polynomial. -/
theorem box_gridPolyNM (N M : ℕ) (g : ℕ → ℕ → ℤ) : InBox (gridPolyNM N M g) (2 * N) (2 * M) :=
  InBox.sum _ fun i hi => InBox.sum _ fun j hj =>
    InBox.mono (InBox.monomial i j _) (by simp at hi; omega) (by simp at hj; omega)

/-- `∑_{i < n} f i` by structural recursion (kernel-friendly). -/
def rsumN (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rsumN f n + f n

theorem rsumN_eq (f : ℕ → ℕ) (n : ℕ) : rsumN f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rsumN, ih, sum_range_succ]

/-- `∑ |g i j|` over the grid (computable). -/
def gridL1NM (N M : ℕ) (g : ℕ → ℕ → ℤ) : ℕ :=
  rsumN (fun j => rsumN (fun i => (g i j).natAbs) (2 * N + 1)) (2 * M + 1)

/-- The `ℓ¹` norm of a grid polynomial is at most `gridL1NM`. -/
theorem l1_gridPolyNM_le (N M : ℕ) (g : ℕ → ℕ → ℤ) : l1 (gridPolyNM N M g) ≤ gridL1NM N M g := by
  refine (l1_sum_le _ _).trans ?_
  simp only [gridL1NM, rsumN_eq]
  rw [sum_comm (s := range (2 * M + 1))]
  refine sum_le_sum fun i _ => ?_
  refine (l1_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun j _ => by rw [l1_monomial]

/-- `∑_{i < n} f i 2^{b i}` (computable, shifts). -/
def packRowK (b : ℕ) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => packRowK b f n + f n * ((1 <<< (b * n) : ℕ) : ℤ)

/-- `∑_{j < m} (∑_{i ≤ 2N} g i j 2^{b i}) 2^{b W j}` (computable). -/
def packGridNM (b W N : ℕ) (g : ℕ → ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => packGridNM b W N g m +
      packRowK b (fun i => g i m) (2 * N + 1) * ((1 <<< (b * W * m) : ℕ) : ℤ)

theorem packRowK_eq (b : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    packRowK b f n = ∑ i ∈ range n, f i * (2 : ℤ) ^ (b * i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packRowK, ih, sum_range_succ, Nat.shiftLeft_eq, one_mul]; push_cast; rfl

theorem packGridNM_eq (b W N : ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ) :
    packGridNM b W N g m = ∑ j ∈ range m, ∑ i ∈ range (2 * N + 1),
      g i j * (2 : ℤ) ^ (b * (i + W * j)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [packGridNM, ih, sum_range_succ, packRowK_eq, sum_mul, Nat.shiftLeft_eq, one_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [mul_assoc, ← pow_add]; ring_nf

/-- **Kronecker image of a grid polynomial.** -/
theorem kron_gridPolyNM (b W N M : ℕ) (g : ℕ → ℕ → ℤ) :
    kron b W (gridPolyNM N M g) = packGridNM b W N g (2 * M + 1) := by
  rw [gridPolyNM, packGridNM_eq, map_sum, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact sum_congr rfl fun i _ => by rw [kron_monomial]

/-! ## Coefficients, reality, derivatives -/

/-- Coefficients of a grid polynomial. -/
theorem coeff_gridPolyNM (N M : ℕ) (g : ℕ → ℕ → ℤ) (i j : ℕ) :
    ((gridPolyNM N M g).coeff j).coeff i = if i ≤ 2 * N ∧ j ≤ 2 * M then g i j else 0 := by
  have h1 : ∀ i' j', ((monomial j' (monomial i' (g i' j')) : P2).coeff j).coeff i =
      if i' = i then (if j' = j then g i' j' else 0) else 0 := by
    intro i' j'
    rw [coeff_monomial]
    by_cases hj : j' = j
    · simp only [hj, ↓reduceIte, coeff_monomial]
    · simp [hj]
  simp only [gridPolyNM, finsetSum_coeff, h1]
  have h2 : ∀ x, (∑ y ∈ range (2 * M + 1), if x = i then (if y = j then g x y else 0) else 0) =
      if x = i then (if j ≤ 2 * M then g x j else 0) else 0 := by
    intro x
    split_ifs with hx hj
    · rw [Finset.sum_ite_eq' (range (2 * M + 1)) j]
      simp only [mem_range, show j < 2 * M + 1 by omega, ↓reduceIte]
    · rw [Finset.sum_ite_eq' (range (2 * M + 1)) j]
      simp only [mem_range, show ¬ j < 2 * M + 1 by omega, ↓reduceIte]
    · simp
  simp only [h2]
  rw [Finset.sum_ite_eq' (range (2 * N + 1)) i]
  by_cases hi : i ≤ 2 * N
  · simp only [mem_range, show i < 2 * N + 1 by omega, ↓reduceIte, hi, true_and]
  · simp only [mem_range, show ¬ i < 2 * N + 1 by omega, ↓reduceIte, hi, false_and]

/-- `coefZ2` of a grid polynomial, centred at `(N, M)`. -/
theorem coefZ2_gridPolyNM (N M : ℕ) (g : ℕ → ℕ → ℤ) (km : ℤ × ℤ) :
    coefZ2 (gridPolyNM N M g) N M km =
      if |km.1| ≤ N ∧ |km.2| ≤ M then g (km.1 + N).toNat (km.2 + M).toNat else 0 := by
  unfold coefZ2
  obtain ⟨k, m⟩ := km
  simp only
  by_cases h : |k| ≤ N ∧ |m| ≤ M
  · have h0 : 0 ≤ k + N ∧ 0 ≤ m + M := by
      obtain ⟨h1, h2⟩ := h; rw [abs_le] at h1 h2; omega
    have h3 : (k + N).toNat ≤ 2 * N ∧ (m + M).toNat ≤ 2 * M := by
      obtain ⟨h1, h2⟩ := h; rw [abs_le] at h1 h2; omega
    simp only [h0, and_self, ↓reduceIte, coeff_gridPolyNM, h3, h]
  · simp only [h, ↓reduceIte]
    split_ifs with h1
    · rw [coeff_gridPolyNM]
      have h3 : ¬ ((k + N).toNat ≤ 2 * N ∧ (m + M).toNat ≤ 2 * M) := by
        intro h3; apply h; rw [abs_le, abs_le]; omega
      simp only [h3, ↓reduceIte]
    · rfl

/-- The coefficients of a grid centre (weight `(1, 0, p)`). -/
theorem coeff_ctr_grid (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (km : ℤ × ℤ) :
    coeff (ctr S N M (1, 0, p) (gridPolyNM N M g)) km = ((2 : ℂ) ^ S * I ^ p)⁻¹ *
      ((if |km.1| ≤ N ∧ |km.2| ≤ M then g (km.1 + N).toNat (km.2 + M).toNat else 0 : ℤ) : ℂ) := by
  rw [coeff_ctr]
  simp only [one_mul, add_zero, scal, mul_one]
  rw [coefZ2_gridPolyNM]

/-- Grid centres lie in every `ℓ¹_r` (finitely many coefficients). -/
theorem inW_ctr_grid (S N M : ℕ) (w : ℕ × ℕ × ℕ) (g : ℕ → ℕ → ℤ) (r : ℝ) :
    InWeighted r (coeff (ctr S N M w (gridPolyNM N M g))) := by
  rw [coeff_ctr]
  refine inWeighted_smul ?_ _
  exact summable_coefZ2 (box_gridPolyNM N M g) (Nat.lt_succ_self _) le_rfl _ _
    (fun km c => ‖c‖ * weight r km) (by simp)

/-- Grid centres are analytic. -/
theorem ana_ctr_grid (S N M : ℕ) (w : ℕ × ℕ × ℕ) (g : ℕ → ℕ → ℤ) :
    Ana (ctr S N M w (gridPolyNM N M g)) :=
  ⟨1, _, one_pos, inW_ctr_grid S N M w g 1, le_rfl⟩

/-- `conj (2^S iᵖ)⁻¹ = (−1)ᵖ (2^S iᵖ)⁻¹`. -/
theorem conj_scal_inv (S p : ℕ) :
    (starRingEnd ℂ) (((2 : ℂ) ^ S * I ^ p)⁻¹) = (-1 : ℂ) ^ p * ((2 : ℂ) ^ S * I ^ p)⁻¹ := by
  rw [map_inv₀, map_mul, map_pow, map_pow, Complex.conj_I, map_ofNat, neg_pow, mul_inv, mul_inv,
    mul_inv]
  have : ((-1 : ℂ) ^ p)⁻¹ = (-1) ^ p := by rw [← inv_pow, inv_neg, inv_one]
  rw [this]; ring

/-- **Symmetric grid centres are real**: the completion with `s = (−1)ᵖ` of any half grid gives
a real element for the phase `p`. -/
theorem isReal_ctr_sym (S N M p : ℕ) (h : ℕ → ℕ → ℤ) :
    IsReal (ctr S N M (1, 0, p) (gridPolyNM N M (symGrid N M ((-1) ^ p) h))) := by
  refine IsReal.of_coeff fun km => ?_
  rw [coeff_ctr_grid, coeff_ctr_grid, map_mul, conj_scal_inv, map_intCast]
  obtain ⟨k, m⟩ := km
  simp only [Prod.fst_neg, Prod.snd_neg, abs_neg]
  by_cases hb : |k| ≤ N ∧ |m| ≤ M
  · simp only [hb, and_self, ↓reduceIte]
    obtain ⟨h1, h2⟩ := hb
    rw [abs_le] at h1 h2
    have e1 : (-k + N).toNat = 2 * N - (k + N).toNat := by omega
    have e2 : (-m + M).toNat = 2 * M - (m + M).toNat := by omega
    rw [e1, e2, symGrid_refl N M (by rw [← pow_add, ← two_mul, pow_mul]; norm_num) h
      (by omega) (by omega)]
    push_cast; ring
  · simp only [hb, ↓reduceIte, Int.cast_zero, mul_zero]

/-- **Derivatives of grid centres**: `dS a b` with integer symbols multiplies the grid by
`a (i − N) + b (j − M)` and lowers the phase by one. -/
theorem dS_ctr_grid (S N M p : ℕ) (g : ℕ → ℕ → ℤ) (a b : ℤ) :
    dS a b (ctr S N M (1, 0, p) (gridPolyNM N M g)) = ctr S N M (1, 0, (p + 3) % 4)
      (gridPolyNM N M (fun i j => (a * ((i : ℤ) - N) + b * ((j : ℤ) - M)) * g i j)) := by
  refine ext_coeff fun km => ?_
  rw [(ana_ctr_grid S N M _ g).coeff_dS, dsym, coeff_ctr_grid, coeff_ctr_grid, Ex.I_pow_mod4]
  obtain ⟨k, m⟩ := km
  simp only
  by_cases hb : |k| ≤ N ∧ |m| ≤ M
  · simp only [hb, and_self, ↓reduceIte]
    obtain ⟨h1, h2⟩ := hb
    rw [abs_le] at h1 h2
    have e1 : (((k + N).toNat : ℕ) : ℤ) - N = k := by omega
    have e2 : (((m + M).toNat : ℕ) : ℤ) - M = m := by omega
    rw [e1, e2, pow_add]
    have hI : (I ^ 3 : ℂ) = -I := by rw [pow_succ, I_sq]; ring
    rw [hI]
    have h2S : (2 : ℂ) ^ S ≠ 0 := pow_ne_zero _ two_ne_zero
    have hIp : (I ^ p : ℂ) ≠ 0 := pow_ne_zero _ I_ne_zero
    field_simp
    push_cast
    ring_nf
    rw [I_sq]; ring
  · simp only [hb, ↓reduceIte, Int.cast_zero, mul_zero]

/-! ## The data of a node polynomial -/

/-- The kernel image of `T = 2^S uᴺ vᴹ`. -/
theorem kron_Tpoly (S N M b W : ℕ) :
    kron b W (Tpoly S N M) = (2 : ℤ) ^ S * ((1 <<< (b * (N + W * M)) : ℕ) : ℤ) := by
  rw [Tpoly, kron_monomial, Nat.shiftLeft_eq, one_mul]; push_cast; ring

/-- The kernel image of `V = 2v`. -/
theorem kron_Vpoly (b W : ℕ) : kron b W Vpoly = 2 * ((1 <<< (b * W) : ℕ) : ℤ) := by
  rw [Vpoly, kron_monomial, Nat.shiftLeft_eq, one_mul]; push_cast; ring_nf

/-- `ℓ¹` of a power. -/
theorem l1_pow_le {P : P2} {a : ℕ} (h : l1 P ≤ a) : ∀ n : ℕ, l1 (P ^ n) ≤ a ^ n
  | 0 => by
    rw [pow_zero, pow_zero, show (1 : P2) = monomial 0 (monomial 0 1) by simp, l1_monomial]; rfl
  | n + 1 => by
    rw [pow_succ, pow_succ]; exact (l1_mul_le _ _).trans (Nat.mul_le_mul (l1_pow_le h n) h)

/-- Box of a power. -/
theorem InBox.pow {P : P2} {a J : ℕ} (h : InBox P a J) : ∀ n : ℕ, InBox (P ^ n) (n * a) (n * J)
  | 0 => by
    rw [pow_zero, show (1 : P2) = monomial 0 (monomial 0 1) by simp]
    simpa using InBox.monomial 0 0 1
  | n + 1 => by
    rw [pow_succ, show (n + 1) * a = n * a + a by ring, show (n + 1) * J = n * J + J by ring]
    exact (InBox.pow h n).mul h

/-- **The data of a node polynomial** `G = evH e − c T^{dd} V^{de} Q`: degree box, `ℓ¹` bound and
Kronecker image from those of the variables. -/
theorem node_facts {S N M : ℕ} {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P2} {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℤ} (hPbox : ∀ i, InBox (P i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (P i) ≤ L i) (hPk : ∀ b W i, kron b W (P i) = Kv b W i) (e : Ex) (c : ℤ)
    (n dd de A J b W : ℕ) (hA : (Ex.box Bx e).1 ≤ A) (hJ : (Ex.box Bx e).2 ≤ J)
    (hA' : dd * N + (Bx n).1 ≤ A) (hJ' : dd * M + de + (Bx n).2 ≤ J) :
    InBox (Ex.evH Wt P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * P n) A J ∧
    l1 (Ex.evH Wt P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * P n) ≤
      Ex.majN L e + c.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n) ∧
    kron b W (Ex.evH Wt P e - (c : P2) * (Tpoly S N M ^ dd * Vpoly ^ de) * P n) =
      Ex.evH Wt (Kv b W) e - c * (((2 : ℤ) ^ S * ((1 <<< (b * (N + W * M)) : ℕ) : ℤ)) ^ dd *
        (2 * ((1 <<< (b * W) : ℕ) : ℤ)) ^ de) * Kv b W n := by
  have hTb : InBox (Tpoly S N M) N M := InBox.monomial N M _
  have hVb : InBox Vpoly 0 1 := InBox.monomial 0 1 _
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (Ex.inBox_evH Wt hPbox e).mono hA hJ
    have h2 := (((Ex.inBox_intCast c).mul ((InBox.pow hTb dd).mul (InBox.pow hVb de))).mul
      (hPbox n))
    refine h1.sub (h2.mono ?_ ?_)
    · simp only [zero_add, mul_zero, add_zero]; linarith [mul_comm dd N]
    · simp only [zero_add]; nlinarith [mul_comm dd M]
  · refine (l1_sub_le _ _).trans (add_le_add (Ex.l1_evH Wt hPl1 e) ?_)
    rw [Ex.intCast_P2]
    refine (l1_mul_le _ _).trans ?_
    refine (Nat.mul_le_mul (l1_C_mul_le _ _) (hPl1 n)).trans ?_
    have hT : l1 (Tpoly S N M) ≤ 2 ^ S := by rw [Tpoly, l1_monomial]; simp
    have hV : l1 Vpoly ≤ 2 := by rw [Vpoly, l1_monomial]; simp
    have := (l1_mul_le _ _).trans (Nat.mul_le_mul (l1_pow_le hT dd) (l1_pow_le hV de))
    calc c.natAbs * l1 (Tpoly S N M ^ dd * Vpoly ^ de) * L n
        ≤ c.natAbs * ((2 ^ S) ^ dd * 2 ^ de) * L n :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ this) (le_refl _)
      _ = c.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n) := by ring
  · rw [map_sub, map_mul, map_mul, map_mul, map_pow, map_pow, kron_Tpoly, kron_Vpoly, hPk,
      Ex.evH_map, map_intCast]
    congr 1
    exact congrArg (fun y => Ex.evH Wt y e) (funext fun i => hPk b W i)

/-! ## Complete steps from kernel data -/

/-- The kernel quantity of a rounding node: the weighted digit sum of the Kronecker image of
`G = evH e − c T^{dd} V^{de} Q` (`Q` the polynomial of variable `n`). -/
def nodeK (S N M : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (e : Ex) (c : ℤ)
    (dd de n b W dc dr J Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (J + 1) (fun i => kwtS 74315 16 Ki (ndist i ((1 + dd) * N)))
    (fun j => kwtS 74315 16 Kj (ndist j ((1 + dd) * M + (0 + de))))
    (Ex.evH Wt (Kv b W) e - c * (((2 : ℤ) ^ S * ((1 <<< (b * (N + W * M)) : ℕ) : ℤ)) ^ dd *
      (2 * ((1 <<< (b * W) : ℕ) : ℤ)) ^ de) * Kv b W n)

/-- The kernel quantity of a norm node: the weighted digit sum of the Kronecker image of `evH e`
(weight `w`). -/
def normK (N M : ℕ) (Wt : ℕ → ℕ × ℕ × ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (e : Ex) (w : ℕ × ℕ × ℕ)
    (b W dc dr J Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (J + 1) (fun i => kwtS 74315 16 Ki (ndist i (w.1 * N)))
    (fun j => kwtS 74315 16 Kj (ndist j (w.1 * M + w.2.1))) (Ex.evH Wt (Kv b W) e)

/-- The kernel quantity of a centre (weight `(1, 0, p)`, box `(2N, 2M)`). -/
def centerK (N M : ℕ) (Kv : ℕ → ℕ → ℕ → ℤ) (i b W dc dr Ki Kj : ℕ) : ℕ :=
  wl1KronP b W dc dr (2 * M + 1) (fun i => kwtS 74315 16 Ki (ndist i (1 * N)))
    (fun j => kwtS 74315 16 Kj (ndist j (1 * M + 0))) (Kv b W i)


/-- The a priori `ℓ¹` bound of a node polynomial. -/
def nodeL1 (S : ℕ) (L : ℕ → ℕ) (e : Ex) (c : ℤ) (dd de n : ℕ) : ℕ :=
  Ex.majN L e + c.natAbs * ((2 ^ S) ^ dd * 2 ^ de * L n)

/-- The degree conditions of a node polynomial. -/
def nodeDims (N M : ℕ) (Bx : ℕ → ℕ × ℕ) (e : Ex) (dd de n A J b W dc dr : ℕ) : Prop :=
  (Ex.box Bx e).1 ≤ A ∧ (Ex.box Bx e).2 ≤ J ∧ dd * N + (Bx n).1 ≤ A ∧
    dd * M + de + (Bx n).2 ≤ J ∧ A < W ∧ W ≤ 2 ^ dc ∧ J + 1 ≤ 2 ^ dr ∧ 1 ≤ b

instance (N M : ℕ) (Bx : ℕ → ℕ × ℕ) (e : Ex) (dd de n A J b W dc dr : ℕ) :
    Decidable (nodeDims N M Bx e dd de n A J b W dc dr) := by
  unfold nodeDims; infer_instance

/-- The radius budget of a node: Lipschitz part plus truncation part. -/
def nodeFin (S : ℕ) (B E : ℕ → ℚ) (e : Ex) (K Ki Kj dd de : ℕ) : ℚ :=
  Ex.dmajQ B E e + (K : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * (1 + dd) + (0 + de))

/-- The radius budget of a norm node. -/
def normFin (S : ℕ) (B E : ℕ → ℚ) (e : Ex) (w : ℕ × ℕ × ℕ) (K Ki Kj : ℕ) : ℚ :=
  Ex.dmajQ B E e + (K : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1)

/-- The degree conditions of a norm node. -/
def normDims (Bx : ℕ → ℕ × ℕ) (e : Ex) (A J b W dc dr : ℕ) : Prop :=
  (Ex.box Bx e).1 ≤ A ∧ (Ex.box Bx e).2 ≤ J ∧ A < W ∧ W ≤ 2 ^ dc ∧ J + 1 ≤ 2 ^ dr ∧ 1 ≤ b

instance (Bx : ℕ → ℕ × ℕ) (e : Ex) (A J b W dc dr : ℕ) :
    Decidable (normDims Bx e A J b W dc dr) := by
  unfold normDims; infer_instance

/-- **One rounding node of a ball chain, from kernel data**: the radius `E n` of the new centre
`x n` of `X n` (`c · X n = eval X e`). -/
theorem node_full {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M : ℕ}
    {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P2} {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℤ} (hPbox : ∀ i, InBox (P i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (P i) ≤ L i) (hPk : ∀ b W i, kron b W (P i) = Kv b W i) {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (dd de p : ℕ) (c : ℤ) (A J b W dc dr Ki Kj K : ℕ)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some (1 + dd, 0 + de, p))
    (hWn : Wt n = (1, 0, p)) (hc0 : c ≠ 0)
    (hdims : nodeDims N M Bx e dd de n A J b W dc dr)
    (hl1 : nodeL1 S L e c dd de n < 2 ^ (b - 1))
    (hK : nodeK S N M Wt Kv e c dd de n b W dc dr J Ki Kj ≤ K)
    (hfin : nodeFin S B E e K Ki Kj dd de ≤ |(c : ℚ)| * E n)
    (hrel : (c : ℂ) • X n = Ex.eval X e) :
    Bd r (X n - x n) (E n) := by
  obtain ⟨hA, hJ, hA', hJ', hAW, hWd, hJd, hb⟩ := hdims
  obtain ⟨fb, fl, fk⟩ := node_facts (S := S) (N := N) (M := M) (Wt := Wt) hPbox hPl1 hPk e c n dd de
    A J b W hA hJ hA' hJ'
  have hG := Bd_ctr_kron (S := S) (N := N) (M := M) (w := (1 + dd, 0 + de, p)) hq hb fb hAW hWd hJd
    (lt_of_le_of_lt fl hl1) fk hK
  refine node_step hr hW hx hB hE hv hwt hWn hc0 hrel hG ?_
  have : |(c : ℚ)| = ((|c| : ℤ) : ℚ) := by push_cast; rfl
  rw [← this]; exact hfin

/-- **One norm node of a ball chain, from kernel data**: `‖eval X e‖ ≤ R`. -/
theorem norm_full {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M : ℕ}
    {Wt : ℕ → ℕ × ℕ × ℕ} (hW : ∀ i, (Wt i).2.2 < 4) {P : ℕ → P2} {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℤ} (hPbox : ∀ i, InBox (P i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (P i) ≤ L i) (hPk : ∀ b W i, kron b W (P i) = Kv b W i) {x X : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (P i)) {B E : ℕ → ℚ} {n : ℕ}
    (hB : ∀ i, i < n → Bd r (x i) (B i)) (hE : ∀ i, i < n → Bd r (X i - x i) (E i))
    (e : Ex) (w : ℕ × ℕ × ℕ) (A J b W dc dr Ki Kj K : ℕ) (Rq : ℚ)
    (hv : below n e = true) (hwt : Ex.wt Wt e = some w)
    (hdims : normDims Bx e A J b W dc dr)
    (hl1 : Ex.majN L e < 2 ^ (b - 1))
    (hK : normK N M Wt Kv e w b W dc dr J Ki Kj ≤ K)
    (hfin : normFin S B E e w K Ki Kj ≤ Rq) :
    Bd r (Ex.eval X e) Rq := by
  obtain ⟨hA, hJ, hAW, hWd, hJd, hb⟩ := hdims
  have fb := (Ex.inBox_evH Wt hPbox e).mono hA hJ
  have fl := Ex.l1_evH Wt hPl1 e
  have fk : kron b W (Ex.evH Wt P e) = Ex.evH Wt (Kv b W) e := by
    rw [Ex.evH_map]; exact congrArg (fun y => Ex.evH Wt y e) (funext fun i => hPk b W i)
  have hG := Bd_ctr_kron (S := S) (N := N) (M := M) (w := w) hq hb fb hAW hWd hJd
    (lt_of_le_of_lt fl hl1) fk hK
  have h := norm_step hr hW hx hB hE hv hwt hG
  refine h.le ?_
  have h2 : ((Ex.dmajQ B E e + ((K : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * w.1 + w.2.1) : ℚ) : ℚ) :
      ℝ) ≤ (Rq : ℝ) := by unfold normFin at hfin; exact_mod_cast hfin
  exact h2

/-- **The norm of one centre, from kernel data.** -/
theorem center_full {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {S N M : ℕ}
    {Wt : ℕ → ℕ × ℕ × ℕ} {P : ℕ → P2} {Bx : ℕ → ℕ × ℕ} {L : ℕ → ℕ}
    {Kv : ℕ → ℕ → ℕ → ℤ} (hPbox : ∀ i, InBox (P i) (Bx i).1 (Bx i).2)
    (hPl1 : ∀ i, l1 (P i) ≤ L i) (hPk : ∀ b W i, kron b W (P i) = Kv b W i) {x : ℕ → FA}
    (hx : ∀ i, x i = ctr S N M (Wt i) (P i)) (i p b W dc dr Ki Kj K : ℕ) (Bq : ℚ)
    (hWi : Wt i = (1, 0, p))
    (hdims : 2 * N < W ∧ W ≤ 2 ^ dc ∧ 2 * M + 1 ≤ 2 ^ dr ∧ 1 ≤ b)
    (hl1 : L i < 2 ^ (b - 1))
    (hBx : Bx i = (2 * N, 2 * M)) (hK : centerK N M Kv i b W dc dr Ki Kj ≤ K)
    (hfin : (K : ℚ) / 2 ^ (16 * (Ki + Kj)) / 2 ^ (S * 1 + 0) ≤ Bq) :
    Bd r (x i) Bq := by
  obtain ⟨hAW, hWd, hJd, hb⟩ := hdims
  have hbox := hPbox i
  rw [hBx] at hbox
  have h := Bd_ctr_kron (S := S) (N := N) (M := M) (w := (1, 0, p)) hq hb hbox hAW hWd hJd
    (lt_of_le_of_lt (hPl1 i) hl1) (hPk b W i) hK
  rw [hx i, hWi]
  refine h.le ?_
  exact_mod_cast hfin

/-- Extending a chain of facts by one index. -/
theorem chain_succ {Pr : ℕ → Prop} {n : ℕ} (h : ∀ i, i < n → Pr i) (hn : Pr n) :
    ∀ i, i < n + 1 → Pr i := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
  · exact h i h'
  · exact hn

/-! ## Embedding a grid into a larger layout -/

/-- The grid `g` (box `(2N, 2M)`, scale `2^S`) shifted by `(dN, dM)` and scaled by `2^s`, as a grid
of the layout `(N + dN, M + dM)`, scale `2^{S + s}`. -/
def embedGrid (N M dN dM s : ℕ) (g : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ :=
  if dN ≤ i ∧ i ≤ dN + 2 * N ∧ dM ≤ j ∧ j ≤ dM + 2 * M then 2 ^ s * g (i - dN) (j - dM) else 0

/-- **Embedding does not change the centre.** -/
theorem ctr_embedGrid (S N M p dN dM s : ℕ) (g : ℕ → ℕ → ℤ) :
    ctr (S + s) (N + dN) (M + dM) (1, 0, p) (gridPolyNM (N + dN) (M + dM) (embedGrid N M dN dM s g))
      = ctr S N M (1, 0, p) (gridPolyNM N M g) := by
  refine ext_coeff fun km => ?_
  rw [coeff_ctr_grid, coeff_ctr_grid]
  obtain ⟨k, m⟩ := km
  simp only
  by_cases hb : |k| ≤ N ∧ |m| ≤ M
  · obtain ⟨h1, h2⟩ := hb
    rw [abs_le] at h1 h2
    have hb' : |k| ≤ ((N + dN : ℕ) : ℤ) ∧ |m| ≤ ((M + dM : ℕ) : ℤ) := by
      push_cast; rw [abs_le, abs_le]; omega
    have hc : dN ≤ (k + ((N + dN : ℕ) : ℤ)).toNat ∧ (k + ((N + dN : ℕ) : ℤ)).toNat ≤ dN + 2 * N ∧
        dM ≤ (m + ((M + dM : ℕ) : ℤ)).toNat ∧ (m + ((M + dM : ℕ) : ℤ)).toNat ≤ dM + 2 * M := by
      omega
    have e1 : (k + ((N + dN : ℕ) : ℤ)).toNat - dN = (k + N).toNat := by omega
    have e2 : (m + ((M + dM : ℕ) : ℤ)).toNat - dM = (m + M).toNat := by omega
    simp only [hb', ↓reduceIte, embedGrid, hc, and_self, e1, e2, abs_le.2 h1, abs_le.2 h2]
    push_cast
    rw [pow_add]
    field_simp
  · simp only [hb, ↓reduceIte, Int.cast_zero, mul_zero]
    split_ifs with hb'
    · obtain ⟨h1, h2⟩ := hb'
      rw [abs_le] at h1 h2
      push_cast at h1 h2
      unfold embedGrid
      have hc : ¬ (dN ≤ (k + ((N + dN : ℕ) : ℤ)).toNat ∧
          (k + ((N + dN : ℕ) : ℤ)).toNat ≤ dN + 2 * N ∧ dM ≤ (m + ((M + dM : ℕ) : ℤ)).toNat ∧
          (m + ((M + dM : ℕ) : ℤ)).toNat ≤ dM + 2 * M) := by
        intro hc; apply hb; rw [abs_le, abs_le]; omega
      simp only [hc, ↓reduceIte, Int.cast_zero, mul_zero]
    · simp

/-! ## Helpers for environments -/

/-- A property of all entries of a list and of the default holds for every `getD`. -/
theorem getD_prop {α : Type*} {Pr : α → Prop} {l : List α} {d : α} (hl : ∀ w ∈ l, Pr w)
    (hd : Pr d) (i : ℕ) : Pr (l.getD i d) := by
  induction l generalizing i with
  | nil => simpa using hd
  | cons a l ih =>
    cases i with
    | zero => exact hl a (by simp)
    | succ i => exact ih (fun w hw => hl w (by simp [hw])) i

/-- `C = v² − 1 = 2 i v cos 2φ` (up to the phase). -/
def cPoly : P2 := monomial 2 (monomial 0 1) - monomial 0 (monomial 0 1)

/-- `S = v² + 1 = 2 v sin 2φ`. -/
def sPoly : P2 := monomial 2 (monomial 0 1) + monomial 0 (monomial 0 1)

theorem box_cPoly : InBox cPoly 0 2 :=
  (InBox.monomial 0 2 1).sub ((InBox.monomial 0 0 1).mono le_rfl (by norm_num))

theorem box_sPoly : InBox sPoly 0 2 :=
  (InBox.monomial 0 2 1).add ((InBox.monomial 0 0 1).mono le_rfl (by norm_num))

theorem l1_cPoly : l1 cPoly ≤ 2 :=
  (l1_sub_le _ _).trans (by rw [l1_monomial, l1_monomial]; rfl)

theorem l1_sPoly : l1 sPoly ≤ 2 :=
  (l1_add_le _ _).trans (by rw [l1_monomial, l1_monomial]; rfl)

theorem kron_cPoly (b W : ℕ) : kron b W cPoly = ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1 := by
  rw [cPoly, map_sub, kron_monomial, kron_monomial, Nat.shiftLeft_eq, one_mul]; push_cast; ring

theorem kron_sPoly (b W : ℕ) : kron b W sPoly = ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1 := by
  rw [sPoly, map_add, kron_monomial, kron_monomial, Nat.shiftLeft_eq, one_mul]; push_cast; ring

theorem l1_Tpoly (S N M : ℕ) : l1 (Tpoly S N M) ≤ 2 ^ S := by
  rw [Tpoly, l1_monomial]; simp

theorem l1_Vpoly : l1 Vpoly ≤ 2 := by rw [Vpoly, l1_monomial]; rfl

/-- The centre of `T` is `1`. -/
theorem ctr_Tpoly (S N M : ℕ) : ctr S N M (1, 0, 0) (Tpoly S N M) = 1 := by
  rw [ctr, phiK_Tpoly, Tc, smul_mul_assoc, mode_mul, smul_smul]
  simp only [scal, ofsW, one_mul, add_zero, pow_zero, mul_one, add_neg_cancel]
  rw [inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]
  exact mode_zero

/-- The centre of `V` is `1`. -/
theorem ctr_Vpoly (S N M : ℕ) : ctr S N M (0, 1, 0) Vpoly = 1 := by
  rw [ctr, phiK_Vpoly, Vc, smul_mul_assoc, mode_mul, smul_smul]
  have e1 : (scal S (0, 1, 0))⁻¹ * 2 = 1 := by
    simp only [scal]; norm_num
  have e2 : (0, 1) + -ofsW N M (0, 1, 0) = 0 := by ext <;> simp [ofsW]
  rw [e1, e2, one_smul, mode_zero]

/-! ## Static `ℓ¹` bounds of grids -/

/-- Packed fields lie in `[−2^{F−1}, 2^{F−1})`. -/
theorem abs_fieldW_le (F data f : ℕ) (hF : 1 ≤ F) : |fieldW F data f| ≤ 2 ^ (F - 1) := by
  unfold fieldW
  have h1 : ((data >>> (F * f)) % 2 ^ F : ℕ) < 2 ^ F := Nat.mod_lt _ (by positivity)
  have h2 : (2 : ℤ) ^ F = 2 * 2 ^ (F - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [abs_le]
  constructor
  · have : (0 : ℤ) ≤ (((data >>> (F * f)) % 2 ^ F : ℕ) : ℤ) := by positivity
    linarith
  · have : ((((data >>> (F * f)) % 2 ^ F : ℕ) : ℤ)) < 2 ^ F := by exact_mod_cast h1
    linarith

/-- Half grids are bounded by `2^{F−1}`. -/
theorem abs_halfGrid_le (F N M data : ℕ) (hF : 1 ≤ F) (i j : ℕ) :
    |halfGrid F N M data i j| ≤ 2 ^ (F - 1) := by
  unfold halfGrid
  split_ifs
  · exact abs_fieldW_le F data _ hF
  · simp

/-- Row-packed half grids are bounded by `2^{F−1}`. -/
theorem abs_halfGridR_le (F N : ℕ) (rows : List ℕ) (hF : 1 ≤ F) (i j : ℕ) :
    |halfGridR F N rows i j| ≤ 2 ^ (F - 1) := by
  unfold halfGridR
  split_ifs
  · exact abs_fieldW_le F _ _ hF
  · simp

/-- Completed grids with `s = ±1` are bounded by twice the half grid bound. -/
theorem abs_symGrid_le (N M : ℕ) {s : ℤ} (hs : |s| = 1) {h : ℕ → ℕ → ℤ} {C : ℤ}
    (hh : ∀ i j, |h i j| ≤ C) (i j : ℕ) : |symGrid N M s h i j| ≤ 2 * C := by
  unfold symGrid
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, hs, one_mul]
  linarith [hh i j, hh (2 * N - i) (2 * M - j)]

/-- `|(−1)ᵖ| = 1`. -/
theorem abs_neg_one_pow (p : ℕ) : |((-1 : ℤ) ^ p)| = 1 := by simp

/-- **Static `ℓ¹` bound** of a grid polynomial with bounded entries. -/
theorem l1_gridPolyNM_le_const (N M : ℕ) {g : ℕ → ℕ → ℤ} {C : ℕ}
    (hg : ∀ i j, i ≤ 2 * N → j ≤ 2 * M → |g i j| ≤ C) :
    l1 (gridPolyNM N M g) ≤ (2 * N + 1) * (2 * M + 1) * C := by
  refine (l1_gridPolyNM_le N M g).trans ?_
  unfold gridL1NM
  rw [rsumN_eq]
  calc ∑ j ∈ range (2 * M + 1), rsumN (fun i => (g i j).natAbs) (2 * N + 1)
      ≤ ∑ _j ∈ range (2 * M + 1), (2 * N + 1) * C := by
        refine sum_le_sum fun j hj => ?_
        rw [rsumN_eq]
        calc ∑ i ∈ range (2 * N + 1), (g i j).natAbs ≤ ∑ _i ∈ range (2 * N + 1), C := by
              refine sum_le_sum fun i hi => ?_
              have := hg i j (by simp at hi; omega) (by simp at hj; omega)
              have h2 : ((g i j).natAbs : ℤ) ≤ C := by rwa [Int.natCast_natAbs]
              exact_mod_cast h2
          _ = (2 * N + 1) * C := by simp
    _ = (2 * N + 1) * (2 * M + 1) * C := by simp; ring

/-- The packed data grids are bounded by `2^F`. -/
theorem abs_dataGrid_le (N M F : ℕ) (rows : List ℕ) (p : ℕ) (hF : 1 ≤ F) (i j : ℕ) :
    |symGrid N M ((-1) ^ p) (halfGridR F N rows) i j| ≤ ((2 ^ F : ℕ) : ℤ) := by
  have := abs_symGrid_le N M (abs_neg_one_pow p) (fun i j => abs_halfGridR_le F N rows hF i j) i j
  have e : (2 : ℤ) * 2 ^ (F - 1) = ((2 ^ F : ℕ) : ℤ) := by
    push_cast; rw [← pow_succ']; congr 1; omega
  linarith

/-- Weighted grids inside the box: `|(a (i − N) + b (j − M)) g i j| ≤ (|a| N + |b| M) C`. -/
theorem abs_wgrid_le (N M : ℕ) (a b : ℤ) {g : ℕ → ℕ → ℤ} {C : ℤ}
    (hg : ∀ i j, |g i j| ≤ C) {i j : ℕ} (hi : i ≤ 2 * N) (hj : j ≤ 2 * M) :
    |(a * ((i : ℤ) - N) + b * ((j : ℤ) - M)) * g i j| ≤ (|a| * N + |b| * M) * C := by
  rw [abs_mul]
  have h1 : |a * ((i : ℤ) - N) + b * ((j : ℤ) - M)| ≤ |a| * N + |b| * M := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have e1 : |((i : ℤ) - N)| ≤ N := by rw [abs_le]; constructor <;> omega
    have e2 : |((j : ℤ) - M)| ≤ M := by rw [abs_le]; constructor <;> omega
    gcongr
  exact mul_le_mul h1 (hg i j) (abs_nonneg _) (by positivity)

/-- Embedded grids are bounded by `2^s C`. -/
theorem abs_embedGrid_le (N M dN dM s : ℕ) {g : ℕ → ℕ → ℤ} {C : ℤ} (hC : 0 ≤ C)
    (hg : ∀ i j, |g i j| ≤ C) (i j : ℕ) : |embedGrid N M dN dM s g i j| ≤ 2 ^ s * C := by
  unfold embedGrid
  split_ifs
  · rw [abs_mul, abs_pow, abs_two]; gcongr; exact hg _ _
  · rw [abs_zero]; positivity

/-- Weighted grids with natural weights, bounds as natural numbers. -/
theorem abs_wgridN_le (N M a b : ℕ) {g : ℕ → ℕ → ℤ} {C : ℕ} (hg : ∀ i j, |g i j| ≤ (C : ℤ))
    {i j : ℕ} (hi : i ≤ 2 * N) (hj : j ≤ 2 * M) :
    |((a : ℤ) * ((i : ℤ) - N) + (b : ℤ) * ((j : ℤ) - M)) * g i j| ≤
      (((a * N + b * M) * C : ℕ) : ℤ) := by
  have := abs_wgrid_le N M a b hg hi hj
  simp only [Nat.abs_cast] at this
  push_cast
  exact this

/-- Embedded grids, bounds as natural numbers. -/
theorem abs_embedGridN_le (N M dN dM s : ℕ) {g : ℕ → ℕ → ℤ} {C : ℕ}
    (hg : ∀ i j, |g i j| ≤ (C : ℤ)) (i j : ℕ) :
    |embedGrid N M dN dM s g i j| ≤ ((2 ^ s * C : ℕ) : ℤ) := by
  have := abs_embedGrid_le N M dN dM s (by positivity) hg i j
  push_cast
  exact this

/-- Static `ℓ¹` bound of a packed data grid polynomial. -/
theorem l1_dataGrid_le (N M F : ℕ) (rows : List ℕ) (p : ℕ) (hF : 1 ≤ F) :
    l1 (gridPolyNM N M (symGrid N M ((-1) ^ p) (halfGridR F N rows))) ≤
      (2 * N + 1) * (2 * M + 1) * 2 ^ F :=
  l1_gridPolyNM_le_const N M fun i j _ _ => abs_dataGrid_le N M F rows p hF i j

end PlasmaLean.Certificates.KronBall
