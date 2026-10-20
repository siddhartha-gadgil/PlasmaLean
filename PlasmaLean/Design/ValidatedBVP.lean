/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.WeightedEll1
public import PlasmaLean.Certificates.RadiiPolynomial
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.FieldSimp

/-!
# A validated nonlinear periodic boundary-value problem (technique demonstration)

**Problem.** Find `2π`-periodic `u` with

  `u'' - u + u² = (4/5) cos x`.

This is a generic quadratic ODE, *not* a plasma equilibrium: it demonstrates the
radii-polynomial pipeline in `ℓ¹(ℤ)` (`ν = 1`) with genuine infinite tails. The forcing
`β = 4/5` lies close to the fold of the small-solution branch (numerically the branch
turns back between `β = 0.8` and `β = 0.9`), and `2‖ū‖ ≈ 1.21 > 1`, so the crude Picard
bound for `u ↦ Λ(f - u²)` does not give a contraction: the finite-block Newton inverse is
needed.

**Fourier formulation.** Writing `u = ∑ₖ uₖ e^{ikx}`, the equation reads
`-(1+k²) uₖ + (u ⋆ u)ₖ - fₖ = 0` with `f_{±1} = 2/5`. Dividing by `1 + k²`, it becomes
`F(u) = u - Λ(u ⋆ u - f) = 0` with `Λ = diag(1/(1+k²))`, a map `ℓ¹ → ℓ¹`
(`Fmap_eq_zero_iff`).

**Certificate data (exact rationals, found by an untrusted Python Newton solver).**
* `ū`: an even sequence with `ū₀, …, ū₃ = 0.12127, -0.23055, 0.01122, -0.00053`.
* `A`: on the block `|k| ≤ 3` a `7×7` rational matrix (three decimals) approximating the
  inverse of the Jacobian block `δ_{lm} - 2 λ_l ū_{l-m}`; the identity for `|k| > 3`.

**Bounds** (each proved by exact rational arithmetic, `decide +kernel` on `ℚ`):
* `Y₀ = 7·10⁻⁵ ≥ ‖A F(ū)‖` (`F(ū)` is supported on `|k| ≤ 6`, so this is exact);
* `Z₀ = 1/7 ≥ Z_block + 2 λ₄ ‖ū‖`, where `Z_block ≤ 7/100` bounds the column sums of
  `I - A DF(ū)` restricted to the rows `|k| ≤ 3` and columns `|m| ≤ 6`, and
  `2 λ₄ ‖ū‖ ≤ (2/17)(61/100)` bounds the tail `|k| > 3` of `2 Λ(ū ⋆ h)`;
* `Z₂ = 13/2 ≥ 2 max(maxₗ λₗ ∑ₖ |A_{kl}|, 1)`
  (the tail uses `λₖ ≤ 1`, see `norm_AL_le`), bounding `A Λ (s ⋆ h)` with `‖s‖ ≤ 2r`.

The Lipschitz estimate `‖T u - T v‖ ≤ (Z₀ + Z₂ r) ‖u - v‖` is obtained algebraically from
the difference of squares `u⋆u - v⋆v = (u+v)⋆(u-v)` (`T_lipschitz`).

**Result** (`validated_bvp`). `p(r) = Z₂ r² + (Z₀ - 1) r + Y₀` is negative at
`r₀ = 10⁻⁴` and at `r = 1/10`. Hence there is a sequence `u*` with `F(u*) = 0` and
`‖u* - ū‖₁ ≤ 10⁻⁴`, it is the only zero of `F` with `‖u - ū‖₁ ≤ 1/10`, and
`|∑ u*ₖ cos kθ - ū(θ)| ≤ 10⁻⁴` for all `θ` (`validated_bvp_uniform`).

**Sanity.** `rejected_small_radius` (the same bounds reject `r = 10⁻⁵`),
`rejected_zero_inverse` (`A = 0` can never pass), and the injectivity of `A` is itself
certified (`Aop_injective`), so the fixed point is a genuine zero.

**Evenness.** `zero_even`: by uniqueness and reflection symmetry, `u*₋ₖ = u*ₖ`, so `u*`
is a real cosine series and `evalCos u*` is the actual periodic function.

**Not proved here.** The step from the coefficient equation to a classical `C²` solution
(differentiating the Fourier series twice; note `(1+k²) u*ₖ = (u*⋆u*)ₖ - fₖ` is summable)
is standard but not formalized.
-/
public section
noncomputable section

namespace PlasmaLean.Design.ValidatedBVP

open PlasmaLean.Certificates Metric

/-! ### Exact rational data -/

/-- The finite block `|k| ≤ 3` on which `A` is a full matrix. -/
@[expose] def blk : Finset ℤ := Finset.Icc (-3) 3

/-- The doubled block `|k| ≤ 6`, the support of `F(ū)`. -/
@[expose] def blk2 : Finset ℤ := Finset.Icc (-6) 6

/-- Numerators (over `10⁵`) of the candidate coefficients `ū₀, …, ū₃`. -/
@[expose] def abarNum : List ℤ := [12127, -23055, 1122, -53]

/-- Candidate coefficient `ūₖ = ū_{|k|}` (zero for `|k| > 3`). -/
@[expose] def abarq (k : ℤ) : ℚ := (abarNum.getD k.natAbs 0 : ℚ) / 100000

/-- Forcing coefficients of `(4/5) cos x`: `f_{±1} = 2/5`. -/
@[expose] def fq (k : ℤ) : ℚ := if k.natAbs = 1 then 2 / 5 else 0

/-- Inverse symbol `λₖ = 1/(1+k²)` of `-(d²/dx² - 1)`. -/
@[expose] def lamq (k : ℤ) : ℚ := 1 / (1 + (k : ℚ) ^ 2)

/-- Numerators (over `10³`) of the block of the approximate inverse, rows and columns
`k, l = -3, …, 3`. -/
@[expose] def ANum : List (List ℤ) :=
  [[1030, -53, 11, -4, 3, -1, 0], [-105, 1094, -148, 63, -36, 10, -1],
   [53, -371, 1467, -545, 314, -90, 13], [-44, 314, -1090, 1987, -1090, 314, -44],
   [13, -90, 314, -545, 1467, -371, 53], [-1, 10, -36, 63, -148, 1094, -105],
   [0, -1, 3, -4, 11, -53, 1030]]

/-- Block entry `A_{kl}` of the approximate inverse. -/
@[expose] def Aq (k l : ℤ) : ℚ := ((ANum.getD (k + 3).toNat []).getD (l + 3).toNat 0 : ℚ) / 1000

/-- Rows `|k| ≤ 3` of `I - A DF(ū)`, columns `|m| ≤ 6`. -/
@[expose] def Cq (k m : ℤ) : ℚ := (if k = m then 1 else 0) -
  ∑ l ∈ blk, Aq k l * ((if l = m then 1 else 0) - 2 * lamq l * abarq (l - m))

/-- `(ū ⋆ ū)ₖ`, an exact finite sum. -/
@[expose] def convq (k : ℤ) : ℚ := ∑ j ∈ blk, abarq j * abarq (k - j)

/-- `F(ū)ₖ`. -/
@[expose] def Fq (k : ℤ) : ℚ := abarq k - lamq k * (convq k - fq k)

/-- `(A F(ū))ₖ`. -/
@[expose] def AFq (k : ℤ) : ℚ := if k ∈ blk then ∑ l ∈ blk, Aq k l * Fq l else Fq k

/-- The Jacobian block `δ_{kl} - 2 λₖ ū_{k-l}`, used only to certify injectivity of `A`. -/
@[expose] def Mq (k l : ℤ) : ℚ := (if k = l then 1 else 0) - 2 * lamq k * abarq (k - l)

/-- Entries `λₗ A_{kl}` of the block of `A Λ`. -/
@[expose] def ALq (k l : ℤ) : ℚ := Aq k l * lamq l

/-- Entries of `I - M A` on the block. -/
@[expose] def Dq (k m : ℤ) : ℚ := (if k = m then 1 else 0) - ∑ l ∈ blk, Mq k l * Aq l m

/-! ### The finite rational checks -/

/-- Block part of `Z₀`: column sums of `I - A DF(ū)` over rows `|k| ≤ 3`. -/
theorem check_Zblock : ∀ m ∈ blk2, ∑ k ∈ blk, |Cq k m| ≤ 7 / 100 := by decide +kernel

/-- The residual bound `Y₀`. -/
theorem check_Y0 : ∑ k ∈ blk2, |AFq k| ≤ 7 / 100000 := by decide +kernel

/-- `‖ū‖₁ ≤ 61/100`. -/
theorem check_normAbar : ∑ k ∈ blk, |abarq k| ≤ 61 / 100 := by decide +kernel

/-- Column sums of `A Λ` on the block, for `Z₂`. -/
theorem check_AL : ∀ l ∈ blk, ∑ k ∈ blk, |ALq k l| ≤ 13 / 4 := by decide +kernel

/-- `‖I - M A‖ ≤ 1/2` on the block: the block of `A` is injective. -/
theorem check_inj : ∀ m ∈ blk, ∑ k ∈ blk, |Dq k m| ≤ 1 / 2 := by decide +kernel

/-- Cast of a Kronecker-type indicator. -/
theorem cast_ite_one_zero (p : Prop) [Decidable p] :
    (((if p then 1 else 0 : ℚ)) : ℝ) = if p then 1 else 0 := by
  split_ifs <;> simp

/-- Transfer of a rational inequality to the reals. -/
theorem ratCast_le {q c : ℚ} (h : q ≤ c) : (q : ℝ) ≤ (c : ℝ) := Rat.cast_le.2 h

/-! ### Elementary facts about the data -/

/-- Membership in the block. -/
theorem mem_blk {k : ℤ} : k ∈ blk ↔ k.natAbs ≤ 3 := by
  simp only [blk, Finset.mem_Icc]; omega

/-- Membership in the doubled block. -/
theorem mem_blk2 {k : ℤ} : k ∈ blk2 ↔ k.natAbs ≤ 6 := by
  simp only [blk2, Finset.mem_Icc]; omega

/-- The candidate is truncated at `|k| ≤ 3`. -/
theorem abarq_eq_zero {k : ℤ} (hk : 3 < k.natAbs) : abarq k = 0 := by
  simp only [abarq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [abarNum]; omega)]
  simp

/-- The forcing has only the modes `k = ±1`. -/
theorem fq_eq_zero {k : ℤ} (hk : 1 < k.natAbs) : fq k = 0 := by
  simp only [fq]; rw [ite_eq_right_iff]; omega

/-- `λₖ > 0`. -/
theorem lamq_pos (k : ℤ) : 0 < lamq k := by unfold lamq; positivity

/-- `λₖ ≤ 1`. -/
theorem lamq_le_one (k : ℤ) : lamq k ≤ 1 := by
  unfold lamq
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg (k : ℚ)]

/-- Tail decay `λₖ ≤ λ₄ = 1/17` for `|k| > 3`. -/
theorem lamq_le_tail {k : ℤ} (hk : 3 < k.natAbs) : lamq k ≤ 1 / 17 := by
  unfold lamq
  have h4 : (4 : ℚ) ≤ |(k : ℚ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hk
  have hsq : (16 : ℚ) ≤ (k : ℚ) ^ 2 := by
    rw [← sq_abs]; nlinarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-! ### The candidate, the forcing and the operators on `ℓ¹(ℤ)` -/

/-- Coordinates of a finite sum of `lp.single`s. -/
theorem sum_single_apply (s : Finset ℤ) (c : ℤ → ℝ) (k : ℤ) :
    (∑ i ∈ s, lp.single 1 i (c i) : Ell1Z) k = if k ∈ s then c k else 0 := by
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]

/-- The numerical candidate `ū ∈ ℓ¹(ℤ)` (finitely supported, even). -/
@[expose] def abar : Ell1Z := ∑ i ∈ blk, lp.single 1 i ((abarq i : ℚ) : ℝ)

/-- Coordinates of the candidate. -/
theorem abar_apply (k : ℤ) : abar k = abarq k := by
  rw [abar, sum_single_apply]
  split_ifs with h
  · rfl
  · rw [abarq_eq_zero (by rw [mem_blk] at h; omega)]; simp

/-- The forcing `f = (4/5) cos x` as a sequence. -/
@[expose] def forcing : Ell1Z := ∑ i ∈ blk, lp.single 1 i ((fq i : ℚ) : ℝ)

/-- Coordinates of the forcing. -/
theorem forcing_apply (k : ℤ) : forcing k = fq k := by
  rw [forcing, sum_single_apply]
  split_ifs with h
  · rfl
  · rw [fq_eq_zero (by rw [mem_blk] at h; omega)]; simp

/-- The diagonal multiplier `Λ = diag(1/(1+k²))` as a function on `ℓ¹`. -/
@[expose] def lamFun (x : Ell1Z) : Ell1Z :=
  ⟨fun k => (lamq k : ℝ) * x k, (memℓp_one_iff _).2 <|
    (summable_abs x).of_nonneg_of_le (fun _ => abs_nonneg _) fun k => by
      rw [abs_mul]
      have h0 : (0 : ℝ) ≤ lamq k := by exact_mod_cast (lamq_pos k).le
      have h1 : (lamq k : ℝ) ≤ 1 := by exact_mod_cast lamq_le_one k
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1⟩

/-- Coordinates of `Λ x`. -/
theorem lamFun_apply (x : Ell1Z) (k : ℤ) : lamFun x k = (lamq k : ℝ) * x k := rfl

/-- `Λ` as an additive map. -/
@[expose] def lamOp : Ell1Z →+ Ell1Z where
  toFun := lamFun
  map_zero' := by ext k; simp [lamFun_apply]
  map_add' x y := by ext k; simp [lamFun_apply, mul_add]

/-- Coordinates of `Λ x`. -/
theorem lamOp_apply (x : Ell1Z) (k : ℤ) : lamOp x k = (lamq k : ℝ) * x k := rfl

/-- The approximate inverse: the matrix `A_{kl}` on the block, the identity on the tail. -/
@[expose] def Afun (x : Ell1Z) : Ell1Z :=
  x + ∑ k ∈ blk, lp.single 1 k ((∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l) - x k)

/-- Coordinates of `A x`. -/
theorem Afun_apply (x : Ell1Z) (k : ℤ) :
    Afun x k = if k ∈ blk then ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l else x k := by
  rw [Afun, lp.coeFn_add, Pi.add_apply, sum_single_apply]
  split_ifs <;> ring

/-- `A` as an additive map. -/
@[expose] def Aop : Ell1Z →+ Ell1Z where
  toFun := Afun
  map_zero' := by ext k; simp [Afun_apply]
  map_add' x y := by
    ext k
    simp only [Afun_apply, lp.coeFn_add, Pi.add_apply]
    split_ifs
    · rw [← Finset.sum_add_distrib]; simp [mul_add]
    · rfl

/-- Coordinates of `A x`. -/
theorem Aop_apply (x : Ell1Z) (k : ℤ) :
    Aop x k = if k ∈ blk then ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l else x k :=
  Afun_apply x k

/-- The zero-finding map `F(u) = u - Λ(u ⋆ u - f)`. -/
@[expose] def Fmap (u : Ell1Z) : Ell1Z := u - lamOp (conv 1 u u - forcing)

/-- `F(u) = 0` is exactly the Fourier form of `u'' - u + u² = (4/5) cos x`:
`-(1+k²) uₖ + (u⋆u)ₖ - fₖ = 0` for every `k`. -/
theorem Fmap_eq_zero_iff (u : Ell1Z) :
    Fmap u = 0 ↔ ∀ k : ℤ, -(1 + (k : ℝ) ^ 2) * u k + conv 1 u u k - fq k = 0 := by
  have hcoord : ∀ k, Fmap u k = u k - (1 / (1 + (k : ℝ) ^ 2)) * (conv 1 u u k - fq k) := by
    intro k
    simp only [Fmap, lp.coeFn_sub, Pi.sub_apply, lamOp_apply, forcing_apply, lamq]
    push_cast; ring
  constructor
  · intro h k
    have := hcoord k
    rw [h] at this
    have hpos : (0 : ℝ) < 1 + (k : ℝ) ^ 2 := by positivity
    simp only [lp.coeFn_zero, Pi.zero_apply] at this
    field_simp at this
    linarith
  · intro h
    ext k
    rw [hcoord k, lp.coeFn_zero, Pi.zero_apply]
    have hpos : (0 : ℝ) < 1 + (k : ℝ) ^ 2 := by positivity
    have := h k
    field_simp
    linarith

/-! ### Exact evaluation of the residual `Y₀` -/

/-- The block is contained in the doubled block. -/
theorem blk_subset_blk2 {k : ℤ} (hk : k ∈ blk) : k ∈ blk2 := by
  rw [mem_blk] at hk; rw [mem_blk2]; omega

/-- Convolution with the candidate at a block index is a finite sum over `|m| ≤ 6`. -/
theorem conv_abar_apply (h : Ell1Z) {l : ℤ} (hl : l ∈ blk) :
    conv 1 abar h l = ∑ m ∈ blk2, h m * ((abarq (l - m) : ℚ) : ℝ) := by
  rw [conv_comm, conv_one_apply]
  rw [tsum_eq_sum (s := blk2) (fun m hm => by
    rw [mem_blk] at hl; rw [mem_blk2] at hm
    rw [abar_apply, abarq_eq_zero (by omega)]; simp)]
  simp only [abar_apply]

/-- `(ū ⋆ ū)ₖ` is the exact rational `convq k`. -/
theorem conv_abar_abar_apply (k : ℤ) : conv 1 abar abar k = convq k := by
  rw [conv_eq_sum_of_support le_rfl abar abar blk (fun j hj => by
    rw [abar_apply, abarq_eq_zero (by rw [mem_blk] at hj; omega)]; simp)]
  simp only [nuWeight_one, div_one, one_mul, abar_apply, convq]
  push_cast; rfl

/-- `F(ū)ₖ` is the exact rational `Fq k`. -/
theorem Fmap_abar_apply (k : ℤ) : Fmap abar k = Fq k := by
  simp only [Fmap, lp.coeFn_sub, Pi.sub_apply, lamOp_apply, conv_abar_abar_apply,
    forcing_apply, abar_apply, Fq]
  push_cast; ring

/-- `(A F(ū))ₖ` is the exact rational `AFq k`. -/
theorem AF_abar_apply (k : ℤ) : Aop (Fmap abar) k = AFq k := by
  rw [Aop_apply, AFq]
  split_ifs
  · push_cast; simp only [Fmap_abar_apply]
  · rw [Fmap_abar_apply]

/-- `A F(ū)` is supported on `|k| ≤ 6`. -/
theorem AFq_eq_zero {k : ℤ} (hk : k ∉ blk2) : AFq k = 0 := by
  rw [mem_blk2] at hk
  have hnb : k ∉ blk := by rw [mem_blk]; omega
  have hc : convq k = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [mem_blk] at hj
    rw [abarq_eq_zero (k := k - j) (by omega)]; ring
  simp only [AFq, hnb, ite_false, Fq, hc, abarq_eq_zero (k := k) (by omega),
    fq_eq_zero (k := k) (by omega)]
  ring

/-- **Residual bound** `‖A F(ū)‖₁ ≤ Y₀ = 7·10⁻⁵`. -/
theorem residual_bound : ‖Aop (Fmap abar)‖ ≤ 7 / 100000 := by
  rw [norm_eq_sum_of_support _ blk2 (fun k hk => by rw [AF_abar_apply, AFq_eq_zero hk]; simp)]
  simp only [AF_abar_apply]
  have := ratCast_le check_Y0
  push_cast at this
  exact this

/-- `‖ū‖₁ ≤ 61/100`. -/
theorem norm_abar_le : ‖abar‖ ≤ 61 / 100 := by
  rw [norm_eq_sum_of_support _ blk (fun k hk => by
    rw [abar_apply, abarq_eq_zero (by rw [mem_blk] at hk; omega)]; simp)]
  simp only [abar_apply]
  have := ratCast_le check_normAbar
  push_cast at this
  exact this

/-! ### The linear defect `I - A DF(ū)` -/

/-- `h ↦ (I - A DF(ū)) h = h - A (h - 2 Λ (ū ⋆ h))`. -/
@[expose] def Lin (h : Ell1Z) : Ell1Z :=
  h - Aop (h - lamOp (conv 1 abar h) - lamOp (conv 1 abar h))

/-- On the block, the linear defect is the exact rational matrix `Cq`. -/
theorem Lin_apply_blk (h : Ell1Z) {k : ℤ} (hk : k ∈ blk) :
    Lin h k = ∑ m ∈ blk2, ((Cq k m : ℚ) : ℝ) * h m := by
  have hδ : ∀ l ∈ blk, ∑ m ∈ blk2, (if l = m then (1:ℝ) else 0) * h m = h l := by
    intro l hl
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq, ite_eq_left (blk_subset_blk2 hl)]
  have hL : Lin h k = h k - ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) *
      (h l - 2 * ((lamq l : ℚ) : ℝ) * ∑ m ∈ blk2, h m * ((abarq (l - m) : ℚ) : ℝ)) := by
    simp only [Lin, lp.coeFn_sub, Pi.sub_apply, Aop_apply, hk, ite_true, lamOp_apply]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [conv_abar_apply h hl]; ring
  have hterm : ∀ l ∈ blk, ∑ m ∈ blk2, ((Aq k l : ℚ) : ℝ) *
      ((if l = m then (1:ℝ) else 0) - 2 * ((lamq l : ℚ) : ℝ) * ((abarq (l - m) : ℚ) : ℝ)) * h m
      = ((Aq k l : ℚ) : ℝ) *
      (h l - 2 * ((lamq l : ℚ) : ℝ) * ∑ m ∈ blk2, h m * ((abarq (l - m) : ℚ) : ℝ)) := by
    intro l hl
    rw [← hδ l hl]
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hL, ← hδ k hk]
  simp only [Cq, Rat.cast_sub, cast_ite_one_zero, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_ofNat]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l hl => (hterm l hl).symm

/-- Off the block, the linear defect is `2 λₖ (ū ⋆ h)ₖ`. -/
theorem Lin_apply_tail (h : Ell1Z) {k : ℤ} (hk : k ∉ blk) :
    Lin h k = 2 * ((lamq k : ℚ) : ℝ) * conv 1 abar h k := by
  simp only [Lin, lp.coeFn_sub, Pi.sub_apply, Aop_apply, hk, ite_false, lamOp_apply]
  ring

/-- **`Z₀` bound**: `‖(I - A DF(ū)) h‖ ≤ (1/7) ‖h‖`. -/
theorem norm_Lin_le (h : Ell1Z) : ‖Lin h‖ ≤ 1 / 7 * ‖h‖ := by
  rw [norm_eq_sum_add_tail (Lin h) blk]
  have hblock : ∑ k ∈ blk, |Lin h k| ≤ 7 / 100 * ‖h‖ := by
    calc ∑ k ∈ blk, |Lin h k| = ∑ k ∈ blk, |∑ m ∈ blk2, ((Cq k m : ℚ) : ℝ) * h m| :=
          Finset.sum_congr rfl fun k hk => by rw [Lin_apply_blk h hk]
      _ ≤ 7 / 100 * ∑ m ∈ blk2, |h m| :=
          sum_abs_matrix_mul_le _ _ _ _ fun m hm => by
            have := ratCast_le (check_Zblock m hm)
            push_cast at this
            exact this
      _ ≤ 7 / 100 * ‖h‖ := by gcongr; exact sum_abs_le_norm h blk2
  have htail : ∑' k, (if k ∈ blk then 0 else |Lin h k|) ≤
      2 / 17 * ‖conv 1 abar h‖ := by
    rw [norm_eq_tsum_abs, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((summable_abs _).mul_left _)
    · split_ifs with hk
      · positivity
      · rw [Lin_apply_tail h hk, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2),
          abs_of_pos (by exact_mod_cast lamq_pos k)]
        have hl : ((lamq k : ℚ) : ℝ) ≤ 1 / 17 := by
          have := ratCast_le (lamq_le_tail (k := k) (by rw [mem_blk] at hk; omega))
          push_cast at this
          exact this
        have := abs_nonneg (conv 1 abar h k)
        nlinarith
    · exact (summable_abs (Lin h)).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
  have hconv := norm_conv_le le_rfl abar h
  have hn := norm_abar_le
  have hh := norm_nonneg h
  have : ‖conv 1 abar h‖ ≤ 61 / 100 * ‖h‖ :=
    hconv.trans (mul_le_mul_of_nonneg_right hn hh)
  linarith

/-! ### The quadratic term `A Λ (s ⋆ h)` -/

/-- **`Z₂` bound**: `‖A Λ w‖ ≤ (13/4) ‖w‖`. -/
theorem norm_AL_le (w : Ell1Z) : ‖Aop (lamOp w)‖ ≤ 13 / 4 * ‖w‖ := by
  rw [norm_eq_sum_add_tail _ blk, norm_eq_sum_add_tail w blk, mul_add]
  have hblock : ∑ k ∈ blk, |Aop (lamOp w) k| ≤ 13 / 4 * ∑ k ∈ blk, |w k| := by
    calc ∑ k ∈ blk, |Aop (lamOp w) k|
        = ∑ k ∈ blk, |∑ l ∈ blk, ((ALq k l : ℚ) : ℝ) * w l| := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Aop_apply, ite_eq_left hk]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [lamOp_apply, ALq]; push_cast; ring
      _ ≤ 13 / 4 * ∑ l ∈ blk, |w l| :=
          sum_abs_matrix_mul_le _ _ _ _ fun l hl => by
            have := ratCast_le (check_AL l hl)
            push_cast at this
            exact this
  have htail : ∑' k, (if k ∈ blk then 0 else |Aop (lamOp w) k|) ≤
      13 / 4 * ∑' k, (if k ∈ blk then 0 else |w k|) := by
    have hs : Summable fun k => (if k ∈ blk then 0 else |w k|) :=
      (summable_abs w).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hs.mul_left _)
    · split_ifs with hk
      · simp
      · rw [Aop_apply, ite_eq_right hk, lamOp_apply, abs_mul,
          abs_of_pos (by exact_mod_cast lamq_pos k)]
        have hl : ((lamq k : ℚ) : ℝ) ≤ 1 := by exact_mod_cast lamq_le_one k
        have := abs_nonneg (w k)
        nlinarith
    · exact (summable_abs (Aop (lamOp w))).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
  linarith

/-! ### The Lipschitz estimate on balls -/

/-- Exact splitting `T u - T v = (I - A DF(ū))(u - v) + A Λ (s ⋆ (u - v))` with
`s = (u - ū) + (v - ū)`, from the difference of squares. -/
theorem T_sub_eq (u v : Ell1Z) :
    (u - Aop (Fmap u)) - (v - Aop (Fmap v)) =
      Lin (u - v) + Aop (lamOp (conv 1 ((u - abar) + (v - abar)) (u - v))) := by
  have hsum : u + v = abar + abar + ((u - abar) + (v - abar)) := by abel
  have hF : Fmap u - Fmap v = (u - v) - lamOp (conv 1 abar (u - v)) -
      lamOp (conv 1 abar (u - v)) - lamOp (conv 1 ((u - abar) + (v - abar)) (u - v)) := by
    have h1 : (conv 1 u u - forcing) - (conv 1 v v - forcing) = conv 1 (u + v) (u - v) := by
      rw [sub_sub_sub_cancel_right, conv_self_sub_conv_self]
    have h2 : Fmap u - Fmap v = (u - v) - lamOp (conv 1 (u + v) (u - v)) := by
      simp only [Fmap]
      rw [← h1, map_sub lamOp (conv 1 u u - forcing) (conv 1 v v - forcing)]; abel
    rw [h2, hsum, conv_add_left, conv_add_left, map_add, map_add]
    abel
  have : (u - Aop (Fmap u)) - (v - Aop (Fmap v)) = (u - v) - Aop (Fmap u - Fmap v) := by
    rw [map_sub]; abel
  rw [this, hF, map_sub, Lin]
  abel

/-- **Lipschitz bound** `‖T u - T v‖ ≤ (Z₀ + Z₂ r) ‖u - v‖` on `B̄(ū, r)`, with
`Z₀ = 1/7`, `Z₂ = 13/2`. -/
theorem T_lipschitz (r : ℝ) :
    ∀ u ∈ closedBall abar r, ∀ v ∈ closedBall abar r,
      ‖(u - Aop (Fmap u)) - (v - Aop (Fmap v))‖ ≤ (1 / 7 + 13 / 2 * r) * ‖u - v‖ := by
  intro u hu v hv
  rw [mem_closedBall, dist_eq_norm] at hu hv
  rw [T_sub_eq]
  have hs : ‖(u - abar) + (v - abar)‖ ≤ 2 * r := (norm_add_le _ _).trans (by linarith)
  have h1 := norm_Lin_le (u - v)
  have h2 := norm_AL_le (conv 1 ((u - abar) + (v - abar)) (u - v))
  have h3 := norm_conv_le le_rfl ((u - abar) + (v - abar)) (u - v)
  have hh := norm_nonneg (u - v)
  have h4 : ‖conv 1 ((u - abar) + (v - abar)) (u - v)‖ ≤ 2 * r * ‖u - v‖ :=
    h3.trans (mul_le_mul_of_nonneg_right hs hh)
  calc _ ≤ ‖Lin (u - v)‖ + ‖Aop (lamOp (conv 1 ((u - abar) + (v - abar)) (u - v)))‖ :=
        norm_add_le _ _
    _ ≤ 1 / 7 * ‖u - v‖ + 13 / 4 * (2 * r * ‖u - v‖) := by gcongr; exact h2.trans (by gcongr)
    _ = (1 / 7 + 13 / 2 * r) * ‖u - v‖ := by ring

/-! ### Injectivity of the approximate inverse -/

/-- `A` is injective (certified by `‖I - M A‖ ≤ 1/2` on the block), so fixed points of
`T = I - A F` are zeros of `F`. -/
theorem Aop_injective : Function.Injective Aop := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hz : ∀ k, Aop x k = 0 := fun k => by rw [hx]; rfl
  have htail : ∀ k ∉ blk, x k = 0 := fun k hk => by
    have := hz k; rwa [Aop_apply, ite_eq_right hk] at this
  have hblkA : ∀ k ∈ blk, ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l = 0 := fun k hk => by
    have := hz k; rwa [Aop_apply, ite_eq_left hk] at this
  -- `x = (I - M A) x` on the block
  have hfix : ∀ k ∈ blk, x k = ∑ m ∈ blk, ((Dq k m : ℚ) : ℝ) * x m := by
    intro k hk
    simp only [Dq, Rat.cast_sub, cast_ite_one_zero, Rat.cast_sum,
      Rat.cast_mul]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, hk, ite_true, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∑ l ∈ blk, ∑ m ∈ blk, ((Mq k l : ℚ) : ℝ) * ((Aq l m : ℚ) : ℝ) * x m = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      simp only [mul_assoc, ← Finset.mul_sum, hblkA l hl, mul_zero]
    rw [this, sub_zero]
  have hS : ∑ k ∈ blk, |x k| ≤ 1 / 2 * ∑ k ∈ blk, |x k| := by
    calc ∑ k ∈ blk, |x k| = ∑ k ∈ blk, |∑ m ∈ blk, ((Dq k m : ℚ) : ℝ) * x m| :=
          Finset.sum_congr rfl fun k hk => by rw [← hfix k hk]
      _ ≤ 1 / 2 * ∑ k ∈ blk, |x k| :=
          sum_abs_matrix_mul_le _ _ _ _ fun m hm => by
            have := ratCast_le (check_inj m hm)
            push_cast at this
            exact this
  have hS0 : ∑ k ∈ blk, |x k| = 0 := by
    have := Finset.sum_nonneg (s := blk) fun k _ => abs_nonneg (x k)
    linarith
  ext k
  rw [lp.coeFn_zero, Pi.zero_apply]
  by_cases hk : k ∈ blk
  · exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => abs_nonneg (x k)).1
      hS0 k hk)
  · exact htail k hk

/-! ### The validated solution -/

/-- The radii polynomial with the certified bounds is negative at `r₀ = 10⁻⁴`. -/
theorem radii_neg_small : radiiPoly (7 / 100000) (1 / 7) (13 / 2) (1 / 10000) < 0 := by
  norm_num [radiiPoly]

/-- The radii polynomial is also negative at `r = 1/10` (uniqueness radius). -/
theorem radii_neg_large : radiiPoly (7 / 100000) (1 / 7) (13 / 2) (1 / 10) < 0 := by
  norm_num [radiiPoly]

/-- **Validated nonlinear BVP.** There is `u* ∈ ℓ¹(ℤ)` solving the Fourier form of
`u'' - u + u² = (4/5) cos x` with `‖u* - ū‖₁ ≤ 10⁻⁴`, and it is the unique solution
with `‖u - ū‖₁ ≤ 1/10`. -/
theorem validated_bvp :
    ∃ u ∈ closedBall abar (1 / 10000), Fmap u = 0 ∧
      ∀ v ∈ closedBall abar (1 / 10), Fmap v = 0 → v = u := by
  obtain ⟨u₁, hu₁, hF₁, -⟩ := radii_polynomial_zero Fmap Aop Aop_injective abar
    (by norm_num : (0:ℝ) < 1 / 10000) (by norm_num) (by norm_num) residual_bound
    (T_lipschitz _) radii_neg_small
  obtain ⟨u₂, -, -, huniq⟩ := radii_polynomial_zero Fmap Aop Aop_injective abar
    (by norm_num : (0:ℝ) < 1 / 10) (by norm_num) (by norm_num) residual_bound
    (T_lipschitz _) radii_neg_large
  have hsub : closedBall abar (1 / 10000) ⊆ closedBall abar (1 / 10) :=
    closedBall_subset_closedBall (by norm_num)
  have h12 : u₁ = u₂ := huniq u₁ (hsub hu₁) hF₁
  refine ⟨u₁, hu₁, hF₁, fun v hv hFv => ?_⟩
  rw [h12]; exact huniq v hv hFv

/-- The candidate as a function: `ū(θ) = ∑_{|k| ≤ 3} ūₖ cos kθ`. -/
theorem evalCos_abar (θ : ℝ) :
    evalCos abar θ = ∑ k ∈ blk, ((abarq k : ℚ) : ℝ) * Real.cos (k * θ) := by
  rw [evalCos, tsum_eq_sum (s := blk) (fun k hk => by
    rw [abar_apply, abarq_eq_zero (by rw [mem_blk] at hk; omega)]; simp)]
  simp only [abar_apply]

/-! ### Evenness: the solution is a genuine cosine series -/

/-- `Λ` commutes with the reflection `k ↦ -k`. -/
theorem lamOp_refl (x : Ell1Z) :
    lamOp (Certificates.refl x) = Certificates.refl (lamOp x) := by
  ext k; simp [lamOp_apply, refl_apply, lamq]

/-- `F` commutes with the reflection (the data `ū`, `f`, `Λ` are even). -/
theorem Fmap_refl (u : Ell1Z) :
    Fmap (Certificates.refl u) = Certificates.refl (Fmap u) := by
  ext k
  simp only [Fmap, lp.coeFn_sub, Pi.sub_apply, lamOp_apply, conv_refl, refl_apply,
    forcing_apply]
  simp [lamq, fq]

/-- The candidate is even. -/
theorem refl_abar : Certificates.refl abar = abar := by
  ext k; rw [refl_apply, abar_apply, abar_apply]; simp [abarq]

/-- **Evenness from uniqueness.** Every zero of `F` within `1/10` of `ū` is even, so the
validated solution is a real cosine series `u₀ + 2 ∑_{k ≥ 1} uₖ cos kx`. -/
theorem zero_even {u : Ell1Z} (hu : ‖u - abar‖ ≤ 1 / 10) (hF : Fmap u = 0) :
    ∀ k : ℤ, u (-k) = u k := by
  obtain ⟨w, -, -, huniq⟩ := validated_bvp
  have hball : ∀ v : Ell1Z, ‖v - abar‖ ≤ 1 / 10 → v ∈ closedBall abar (1 / 10) :=
    fun v hv => by rw [mem_closedBall, dist_eq_norm]; exact hv
  have h1 : u = w := huniq u (hball u hu) hF
  have hr : ‖Certificates.refl u - abar‖ ≤ 1 / 10 := by
    rw [← refl_abar, ← refl_sub, norm_refl]; exact hu
  have h2 : Certificates.refl u = w :=
    huniq (Certificates.refl u) (hball _ hr) (by rw [Fmap_refl, hF, refl_zero])
  intro k
  have := congrArg (fun x : Ell1Z => x k) (h2.trans h1.symm)
  simpa [refl_apply] using this

/-- **Uniform closeness, evenness and the coefficient equation.** The validated solution is
an even sequence satisfying `-(1+k²) uₖ + (u⋆u)ₖ = fₖ` for all `k`; its cosine series (the
real function `∑ₖ uₖ e^{ikθ}`) is within `10⁻⁴` of the candidate `ū(θ)` at every `θ`; and
it is the only zero of `F` within `1/10` of `ū` in `ℓ¹`. -/
theorem validated_bvp_uniform :
    ∃ u : Ell1Z, (∀ k : ℤ, -(1 + (k : ℝ) ^ 2) * u k + conv 1 u u k - fq k = 0) ∧
      (∀ k : ℤ, u (-k) = u k) ∧
      ‖u - abar‖ ≤ 1 / 10000 ∧
      (∀ θ : ℝ, |evalCos u θ - ∑ k ∈ blk, ((abarq k : ℚ) : ℝ) * Real.cos (k * θ)| ≤
        1 / 10000) ∧
      ∀ v : Ell1Z, ‖v - abar‖ ≤ 1 / 10 → Fmap v = 0 → v = u := by
  obtain ⟨u, hu, hF, huniq⟩ := validated_bvp
  rw [mem_closedBall, dist_eq_norm] at hu
  refine ⟨u, (Fmap_eq_zero_iff u).1 hF, zero_even (hu.trans (by norm_num)) hF, hu,
    fun θ => ?_, fun v hv hFv =>
    huniq v (by rw [mem_closedBall, dist_eq_norm]; exact hv) hFv⟩
  rw [← evalCos_abar, ← evalCos_sub]
  exact (abs_evalCos_le _ θ).trans hu

/-! ### Sanity: rejected certificates -/

/-- With the same `Y₀, Z₀, Z₂`, the radius `10⁻⁵ < Y₀` is rejected. -/
theorem rejected_small_radius : ¬ radiiPoly (7 / 100000) (1 / 7) (13 / 2) (1 / 100000) < 0 :=
  radii_polynomial_rejects_small (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- With the degenerate approximate inverse `A = 0` (so `T = id`, the setting of
`zero_inverse_counterexample`), no bounds `Y₀, Z₀, Z₂` pass the radii test on any ball
of positive radius around `ū` in `ℓ¹(ℤ)`. -/
theorem rejected_zero_inverse {Y₀ Z₀ Z₂ r : ℝ} (hr : 0 < r)
    (hY : ‖(abar - (0 : Ell1Z →+ Ell1Z) (Fmap abar)) - abar‖ ≤ Y₀)
    (hlip : ∀ u ∈ closedBall abar r, ∀ v ∈ closedBall abar r,
      ‖(u - (0 : Ell1Z →+ Ell1Z) (Fmap u)) - (v - (0 : Ell1Z →+ Ell1Z) (Fmap v))‖ ≤
        (Z₀ + Z₂ * r) * ‖u - v‖) :
    ¬ radiiPoly Y₀ Z₀ Z₂ r < 0 := by
  have : Nontrivial Ell1Z := ⟨⟨lp.single 1 0 1, 0, fun h => by
    have := congrArg (fun x : Ell1Z => x 0) h
    simp at this⟩⟩
  refine radii_polynomial_rejects_identity abar hr (by simpa using hY) fun u hu v hv => ?_
  simpa using hlip u hu v hv

end PlasmaLean.Design.ValidatedBVP
