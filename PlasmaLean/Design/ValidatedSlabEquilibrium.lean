/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.ValidatedSlabData
public import PlasmaLean.Certificates.ConvAlgebra
public import PlasmaLean.Theory.Equilibrium.Slab
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A validated slab equilibrium with an exponential pressure profile

**Physics.** In a Cartesian slab with fields depending on `z` only, take
`B(z) = (ψ'(z), B₀, 0)` (a sheared field from a flux function `ψ` plus a uniform guide
field) and a pressure that is a function of the flux, `p = P(ψ)`. Then `J = curl B/μ₀ =
(0, ψ''/μ₀, 0)` and the kernel force balance `J × B = ∇p` reduces to the slab
Grad–Shafranov equation `ψ'' = -μ₀ P'(ψ)`. We use the **non-polynomial profile**

  `P(ψ) = (a/μ₀) (e^ψ - ψ)`,  `a = 51/50`,

(positive, with minimum `a/μ₀` at `ψ = 0`), which gives the Liouville/Bratu-type equation

  `ψ'' + a (e^ψ - 1) = 0`.

It is autonomous, so its periodic solutions come in translation families. Heuristically
(not formalized), the small-amplitude period is `2π/√a` and grows with the amplitude, which is
why `a > 1` is taken. We validate the even solution near the oracle candidate.

**Validation (radii polynomial in `ℓ¹(ℤ)`, `ν = 1`).** The Fourier form is
`-k² φₖ + a((e^φ)ₖ - δₖ) = 0`, where `e^φ` is the exponential in the convolution Banach
algebra (`Certificates.ConvAlgebra`). With `Λ = diag(1/(1+k²))`:
* `F(φ) = -φ + Λ(φ + a(e^φ - 1))`;
* the translation symmetry is removed by `F̃(u) = F(P_e u) - P_o u` (even/odd parts). A zero
  of `F̃` is even and a zero of `F` (`Ftil_zero`), because `F` commutes with reflection.
* `T(u) = u - A F̃(u)` with `A` a rational `21×21` block plus `-I` on the tail.

The exponential of the candidate is enclosed rigorously: rounded Taylor terms `Pₙ` with
certified one-step defects give `‖e^ū - Ē‖₁ ≤ δ = 8·10⁻¹⁴` (`exp_enclosure`,
`norm_exp_ubar_sub_Ebar`). The second-order bound
`‖e^φ - e^ψ - e^ū(φ - ψ)‖ ≤ r e^{‖ū‖+r} ‖φ - ψ‖` (`norm_exp_sub_exp_sub_mul_le`) gives
`Z₂`. Bounds: `Y₀ = 6·10⁻¹²`, `Z₀ = 0.0245`, `Z₂ = 95`; `p(10⁻¹¹) < 0` and `p(1/200) < 0`.

**Results.**
* `validated_slab_profile`: there is a `C²`, even, `2π`-periodic `Φ` with
  `Φ'' + a(e^Φ - 1) = 0` everywhere and `|Φ - ū| ≤ 10⁻¹¹` uniformly; its coefficient
  sequence is the unique zero of `F̃` within `1/200` of `ū` in `ℓ¹`.
* `validated_slab_equilibrium`: for every `μ₀ > 0` and guide field `B₀`, the fields
  `B = (Φ', B₀, 0)`, `J = (0, Φ''/μ₀, 0)` and `p = (a/μ₀)(e^Φ - Φ)` satisfy the kernel slab
  laws `StaticSlab` (hence pointwise `ForceBalance`, `slab_forceBalance`), with `p ≥ a/μ₀ > 0`
  and `Φ(0) - Φ(π) ≥ 9/10` (non-trivial shear).
* `validated_slab_equilibrium_scaled`: the same with physical scales `L` (length) and `B⋆`
  (field): `ψ(z) = B⋆ L Φ(z/L)`, `p = (a B⋆²/μ₀)(e^{ψ/(B⋆L)} - ψ/(B⋆L))`.

**Scope and honesty.** Normalized units with an arbitrary `μ₀ > 0`; the scaled version is a
change of variables, not a calibrated device. This is a 1-D slab, not a toroidal
Grad–Shafranov equilibrium; stability is not addressed. Uniqueness is in coefficient space.
-/
public section
noncomputable section

namespace PlasmaLean.Design.ValidatedSlab

open PlasmaLean.Certificates PlasmaLean.Certificates.ConvAlgebra Metric
open scoped BigOperators

/-! ### Finite rational sequences in `ℓ¹(ℤ)` -/

/-- Embed a rational sequence supported in `S` into `ℓ¹(ℤ)`. -/
@[expose] def embed (q : ℤ → ℚ) (S : Finset ℤ) : Ell1Z :=
  ∑ i ∈ S, lp.single 1 i ((q i : ℚ) : ℝ)

/-- Coordinates of an embedded sequence. -/
theorem embed_apply (q : ℤ → ℚ) (S : Finset ℤ) (hq : ∀ k ∉ S, q k = 0) (k : ℤ) :
    embed q S k = q k := by
  rw [embed, ValidatedBVP.sum_single_apply]
  split_ifs with h
  · rfl
  · rw [hq k h]; simp

/-- Norm of an embedded sequence. -/
theorem norm_embed (q : ℤ → ℚ) (S : Finset ℤ) (hq : ∀ k ∉ S, q k = 0) :
    ‖embed q S‖ = ∑ k ∈ S, |((q k : ℚ) : ℝ)| := by
  rw [norm_eq_sum_of_support _ S (fun k hk => by rw [embed_apply q S hq, hq k hk]; simp)]
  simp only [embed_apply q S hq]

/-- Membership in `blk`. -/
theorem mem_blk {k : ℤ} : k ∈ blk ↔ k.natAbs ≤ 10 := by
  simp only [blk, Finset.mem_Icc]; omega

/-- Membership in `blkK`. -/
theorem mem_blkK {k : ℤ} : k ∈ blkK ↔ k.natAbs ≤ 16 := by
  simp only [blkK, Finset.mem_Icc]; omega

/-- Membership in `blk2`. -/
theorem mem_blk2 {k : ℤ} : k ∈ blk2 ↔ k.natAbs ≤ 26 := by
  simp only [blk2, Finset.mem_Icc]; omega

/-- The candidate vanishes off `|k| ≤ 10`. -/
theorem ubarq_eq_zero {k : ℤ} (hk : 10 < k.natAbs) : ubarq k = 0 := by
  simp only [ubarq, show ¬ k.natAbs ≤ 10 by omega, ite_false]

/-- The Taylor terms vanish off `|k| ≤ 16`. -/
theorem Pq_eq_zero (n : ℕ) {k : ℤ} (hk : 16 < k.natAbs) : Pq n k = 0 := by
  simp only [Pq, show ¬ k.natAbs ≤ 16 by omega, ite_false]

/-- `Ē` vanishes off `|k| ≤ 16`. -/
theorem Ebarq_eq_zero {k : ℤ} (hk : 16 < k.natAbs) : Ebarq k = 0 := by
  simp only [Ebarq, show ¬ k.natAbs ≤ 16 by omega, ite_false]

/-- The candidate is even. -/
theorem ubarq_neg (k : ℤ) : ubarq (-k) = ubarq k := by simp [ubarq]

/-- `Ē` is even. -/
theorem Ebarq_neg (k : ℤ) : Ebarq (-k) = Ebarq k := by simp [Ebarq]

/-- The candidate `ū ∈ ℓ¹(ℤ)`. -/
@[expose] def ubar : Ell1Z := embed ubarq blk

/-- Rounded Taylor terms `Pₙ ∈ ℓ¹(ℤ)`. -/
@[expose] def Pv (n : ℕ) : Ell1Z := embed (Pq n) blkK

/-- The enclosure centre `Ē ∈ ℓ¹(ℤ)`. -/
@[expose] def Ebar : Ell1Z := embed Ebarq blkK

/-- Coordinates of `ū`. -/
theorem ubar_apply (k : ℤ) : ubar k = ubarq k :=
  embed_apply _ _ (fun k hk => ubarq_eq_zero (by rw [mem_blk] at hk; omega)) k

/-- Coordinates of `Pₙ`. -/
theorem Pv_apply (n : ℕ) (k : ℤ) : Pv n k = Pq n k :=
  embed_apply _ _ (fun k hk => Pq_eq_zero n (by rw [mem_blkK] at hk; omega)) k

/-- Coordinates of `Ē`. -/
theorem Ebar_apply (k : ℤ) : Ebar k = Ebarq k :=
  embed_apply _ _ (fun k hk => Ebarq_eq_zero (by rw [mem_blkK] at hk; omega)) k

/-- `ū` is even. -/
theorem ubar_even (k : ℤ) : ubar (-k) = ubar k := by rw [ubar_apply, ubar_apply, ubarq_neg]

/-- `‖ū‖ ≤ 0.572`. -/
theorem norm_ubar_le : ‖ubar‖ ≤ 572 / 1000 := by
  rw [ubar, norm_embed _ _ (fun k hk => ubarq_eq_zero (by rw [mem_blk] at hk; omega))]
  have := ValidatedBVP.ratCast_le check_normU
  push_cast at this ⊢
  exact this

/-- `‖Ē‖ ≤ 1.571`. -/
theorem norm_Ebar_le : ‖Ebar‖ ≤ 1571 / 1000 := by
  rw [Ebar, norm_embed _ _ (fun k hk => Ebarq_eq_zero (by rw [mem_blkK] at hk; omega))]
  have := ValidatedBVP.ratCast_le check_normE
  push_cast at this ⊢
  exact this

/-! ### Enclosure of the exponential of the candidate -/

/-- **Taylor enclosure of the Banach-algebra exponential.** If `‖x‖ ≤ m < 1`, `P₀ = 1`
and the one-step defects satisfy `‖x Pₙ/(n+1) - P_{n+1}‖ ≤ ρ` for `n < N`, then
`‖e^x - ∑_{n ≤ N} Pₙ‖ ≤ (N+1) ρ/(1-m) + m^{N+1}/((N+1)! (1-m))`. -/
theorem exp_enclosure {x : Ell1Z} {P : ℕ → Ell1Z} {m ρ : ℝ} (N : ℕ) (hm : ‖x‖ ≤ m)
    (hm1 : m < 1) (hρ : 0 ≤ ρ) (hP0 : P 0 = 1)
    (hstep : ∀ n < N, ‖((n : ℝ) + 1)⁻¹ • (x * P n) - P (n + 1)‖ ≤ ρ) :
    ‖NormedSpace.exp x - ∑ n ∈ Finset.range (N + 1), P n‖ ≤
      (N + 1) * (ρ / (1 - m)) + m ^ (N + 1) / ((N + 1).factorial * (1 - m)) := by
  have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
  have h1m : 0 < 1 - m := by linarith
  set f : ℕ → Ell1Z := fun n => ((n.factorial : ℝ))⁻¹ • x ^ n with hf
  -- (i) termwise errors
  have hterm : ∀ n ≤ N, ‖f n - P n‖ ≤ ρ / (1 - m) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [show f 0 - P 0 = 0 by simp [hf, hP0], norm_zero]
      positivity
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hstep' := hstep n (by omega)
      have hrec : f (n + 1) = ((n : ℝ) + 1)⁻¹ • (x * f n) := by
        simp only [hf, Nat.factorial_succ, Nat.cast_mul, mul_inv, smul_smul, pow_succ',
          mul_smul_comm]
        congr 1; push_cast; ring
      have hsplit : f (n + 1) - P (n + 1) = ((n : ℝ) + 1)⁻¹ • (x * (f n - P n)) +
          (((n : ℝ) + 1)⁻¹ • (x * P n) - P (n + 1)) := by
        rw [hrec, mul_sub, smul_sub]; abel
      rw [hsplit]
      have hn1 : 0 < (n : ℝ) + 1 := by positivity
      have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
      calc _ ≤ ‖((n : ℝ) + 1)⁻¹ • (x * (f n - P n))‖ +
            ‖((n : ℝ) + 1)⁻¹ • (x * P n) - P (n + 1)‖ := norm_add_le _ _
        _ ≤ 1 * (m * (ρ / (1 - m))) + ρ := by
            gcongr
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn1)]
            gcongr
            exact (norm_mul_le _ _).trans (mul_le_mul hm ih' (norm_nonneg _) hm0)
        _ = ρ / (1 - m) := by field_simp; ring
  -- (ii) splitting the series
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hsplit := (hsum.summable.sum_add_tsum_nat_add (N + 1)).symm
  rw [hsum.tsum_eq] at hsplit
  -- (iii) tail bound
  have htail : ‖∑' n, f (n + (N + 1))‖ ≤ m ^ (N + 1) / ((N + 1).factorial * (1 - m)) := by
    have hgeom : HasSum (fun n : ℕ => m ^ (N + 1) / (N + 1).factorial * m ^ n)
        (m ^ (N + 1) / (N + 1).factorial * (1 - m)⁻¹) :=
      (hasSum_geometric_of_lt_one hm0 hm1).mul_left _
    have hval : m ^ (N + 1) / (N + 1).factorial * (1 - m)⁻¹ =
        m ^ (N + 1) / ((N + 1).factorial * (1 - m)) := by field_simp
    rw [← hval]
    refine tsum_of_norm_bounded hgeom fun n => ?_
    simp only [hf]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hfac : ((N + 1).factorial : ℝ) ≤ (n + (N + 1)).factorial := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hpow : ‖x ^ (n + (N + 1))‖ ≤ m ^ (N + 1) * m ^ n := by
      calc ‖x ^ (n + (N + 1))‖ ≤ ‖x‖ ^ (n + (N + 1)) := norm_pow_le' x (by omega)
        _ ≤ m ^ (n + (N + 1)) := by gcongr
        _ = m ^ (N + 1) * m ^ n := by rw [pow_add, mul_comm]
    calc ((n + (N + 1)).factorial : ℝ)⁻¹ * ‖x ^ (n + (N + 1))‖
        ≤ ((N + 1).factorial : ℝ)⁻¹ * (m ^ (N + 1) * m ^ n) := by
          gcongr
      _ = m ^ (N + 1) / (N + 1).factorial * m ^ n := by ring
  -- (iv) combine
  have hfin : ‖∑ n ∈ Finset.range (N + 1), (f n - P n)‖ ≤ (N + 1) * (ρ / (1 - m)) := by
    calc _ ≤ ∑ n ∈ Finset.range (N + 1), ‖f n - P n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N + 1), ρ / (1 - m) :=
          Finset.sum_le_sum fun n hn => hterm n (by rw [Finset.mem_range] at hn; omega)
      _ = (N + 1) * (ρ / (1 - m)) := by simp
  have heq : NormedSpace.exp x - ∑ n ∈ Finset.range (N + 1), P n =
      ∑ n ∈ Finset.range (N + 1), (f n - P n) + ∑' n, f (n + (N + 1)) := by
    rw [hsplit, Finset.sum_sub_distrib]; abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hfin htail)

/-- `P₀ = 1` in the convolution algebra. -/
theorem Pv_zero : Pv 0 = 1 := by
  ext k
  rw [Pv_apply, one_apply]
  by_cases hk : k ∈ blkK
  · rw [check_P0 k hk, dq]; split_ifs <;> simp
  · have hk0 : k ≠ 0 := by rintro rfl; simp [blkK] at hk
    rw [Pq_eq_zero 0 (by rw [mem_blkK] at hk; omega)]
    simp [hk0]

/-- `∑ₙ Pₙ = Ē`. -/
theorem sum_Pv : ∑ n ∈ Finset.range 17, Pv n = Ebar := by
  ext k
  rw [lp.coeFn_sum, Finset.sum_apply, Ebar_apply]
  simp only [Pv_apply]
  by_cases hk : k ∈ blkK
  · rw [check_Ebar k hk]; push_cast; rfl
  · rw [Ebarq_eq_zero (by rw [mem_blkK] at hk; omega)]
    simp [Pq_eq_zero _ (show 16 < k.natAbs by rw [mem_blkK] at hk; omega)]

/-- Coordinates of `ū Pₙ`: the rational convolution `convPq`. -/
theorem ubar_mul_Pv_apply (n : ℕ) (k : ℤ) : (ubar * Pv n) k = convPq n k := by
  rw [mul_def, conv_eq_sum_of_support le_rfl ubar (Pv n) blk (fun j hj => by
    rw [ubar_apply, ubarq_eq_zero (by rw [mem_blk] at hj; omega)]; simp)]
  simp only [nuWeight_one, div_one, one_mul, ubar_apply, Pv_apply, convPq]
  push_cast; rfl

/-- One-step Taylor defects in `ℓ¹`. -/
theorem taylor_step (n : ℕ) (hn : n < 16) :
    ‖((n : ℝ) + 1)⁻¹ • (ubar * Pv n) - Pv (n + 1)‖ ≤ 2 / 10 ^ 15 := by
  have hsupp : ∀ k ∉ blk2, (((n : ℝ) + 1)⁻¹ • (ubar * Pv n) - Pv (n + 1)) k = 0 := by
    intro k hk
    rw [mem_blk2] at hk
    rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, Pv_apply,
      Pq_eq_zero _ (by omega), mul_def,
      conv_support (N := 10) (M := 16) ubar (Pv n)
        (fun j hj => by rw [ubar_apply, ubarq_eq_zero hj]; simp)
        (fun j hj => by rw [Pv_apply, Pq_eq_zero n hj]; simp) k (by omega)]
    simp
  rw [norm_eq_sum_of_support _ blk2 hsupp]
  have := ValidatedBVP.ratCast_le (check_taylor n (Finset.mem_range.2 hn))
  push_cast at this
  convert this using 2 with k
  rw [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, Pv_apply,
    ubar_mul_Pv_apply, smul_eq_mul]
  push_cast; rw [div_eq_inv_mul]

/-- The enclosure radius `δ = 8·10⁻¹⁴`. -/
theorem delta_bound : ((16 : ℕ) + 1 : ℝ) * ((2 / 10 ^ 15) / (1 - 572 / 1000)) +
    (572 / 1000 : ℝ) ^ (16 + 1) / ((16 + 1).factorial * (1 - 572 / 1000)) ≤ 8 / 10 ^ 14 := by
  simp only [Nat.factorial]
  norm_num

/-- **Rigorous enclosure of `e^ū`:** `‖e^ū - Ē‖₁ ≤ 8·10⁻¹⁴`. -/
theorem norm_exp_ubar_sub_Ebar : ‖NormedSpace.exp ubar - Ebar‖ ≤ 8 / 10 ^ 14 := by
  have h := exp_enclosure (x := ubar) (P := Pv) (m := 572 / 1000) (ρ := 2 / 10 ^ 15) 16
    norm_ubar_le (by norm_num) (by norm_num) Pv_zero (fun n hn => taylor_step n hn)
  rw [sum_Pv] at h
  exact h.trans (by exact_mod_cast delta_bound)

/-! ### The operators `Λ`, `A`, `F`, `F̃` -/

/-- The parameter `a` as a real number. -/
abbrev aR : ℝ := ((aq : ℚ) : ℝ)

/-- `a = 51/50`. -/
theorem aR_eq : aR = 51 / 50 := by simp [aR, aq]

/-- Shorthand for the multiplier `Λ = diag(1/(1+k²))` of `PlasmaLean.Design.ValidatedBVP`. -/
abbrev lamOp : Ell1Z →+ Ell1Z := ValidatedBVP.lamOp

/-- Coordinates of `Λ x`. -/
theorem lamOp_apply (x : Ell1Z) (k : ℤ) : lamOp x k = (lamq k : ℝ) * x k := rfl

/-- `Λ` commutes with scalars. -/
theorem lamOp_smul (c : ℝ) (x : Ell1Z) : lamOp (c • x) = c • lamOp x := by
  ext k; simp only [lamOp_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- `0 < λₖ`. -/
theorem lamq_pos' (k : ℤ) : (0 : ℝ) < (lamq k : ℝ) := by
  exact_mod_cast ValidatedBVP.lamq_pos k

/-- `λₖ ≤ 1`. -/
theorem lamq_le_one' (k : ℤ) : (lamq k : ℝ) ≤ 1 := by
  exact_mod_cast ValidatedBVP.lamq_le_one k

/-- Tail decay `λₖ ≤ λ₁₁ = 1/122` for `|k| > 10`. -/
theorem lamq_le_tail {k : ℤ} (hk : 10 < k.natAbs) : (lamq k : ℝ) ≤ 1 / 122 := by
  have h : lamq k ≤ 1 / 122 := by
    simp only [lamq, ValidatedBVP.lamq]
    have h4 : (11 : ℚ) ≤ |(k : ℚ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hk
    have hsq : (121 : ℚ) ≤ (k : ℚ) ^ 2 := by
      rw [← sq_abs]; nlinarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 := ValidatedBVP.ratCast_le h
  rw [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h2
  exact h2

/-- The approximate inverse: the matrix `A_{kl}` on `|k| ≤ 10`, minus the identity on the
tail. -/
@[expose] def Afun (x : Ell1Z) : Ell1Z :=
  -x + ∑ k ∈ blk, lp.single 1 k ((∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l) + x k)

/-- Coordinates of `A x`. -/
theorem Afun_apply (x : Ell1Z) (k : ℤ) :
    Afun x k = if k ∈ blk then ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l else -x k := by
  rw [Afun, lp.coeFn_add, Pi.add_apply, ValidatedBVP.sum_single_apply, lp.coeFn_neg,
    Pi.neg_apply]
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
    · ring

/-- Coordinates of `A x`. -/
theorem Aop_apply (x : Ell1Z) (k : ℤ) :
    Aop x k = if k ∈ blk then ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l else -x k :=
  Afun_apply x k

/-- `A` commutes with scalars. -/
theorem Aop_smul (c : ℝ) (x : Ell1Z) : Aop (c • x) = c • Aop x := by
  ext k
  simp only [Aop_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · rw [Finset.mul_sum]; congr 1; funext l; ring
  · ring

/-- The zero-finding map `F(φ) = -φ + Λ(φ + a(e^φ - 1))`. -/
@[expose] def Fmap (φ : Ell1Z) : Ell1Z := -φ + lamOp (φ + aR • (NormedSpace.exp φ - 1))

/-- The symmetrized map `F̃(u) = F(P_e u) - P_o u`. -/
@[expose] def Ftil (u : Ell1Z) : Ell1Z := Fmap (evenPart u) - oddPart u

/-- Coordinates of `F(φ)`. -/
theorem Fmap_apply (φ : Ell1Z) (k : ℤ) :
    Fmap φ k = -φ k + (lamq k : ℝ) *
      (φ k + aR * (NormedSpace.exp φ k - if k = 0 then 1 else 0)) := by
  simp only [Fmap, lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply, lamOp_apply,
    lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, smul_eq_mul, one_apply]

/-! ### The linear part `I - A DF̃(ū)` -/

/-- `h ↦ h - A(-h + Λ(P_e h + a Ē ⋆ P_e h))`: the linear defect with `Ē` in place of
`e^ū`. -/
@[expose] def Lbar (h : Ell1Z) : Ell1Z :=
  h - Aop (-h + lamOp (evenPart h + aR • (Ebar * evenPart h)))

/-- The true linear defect `I - A DF̃(ū)`, `DF̃(ū)h = -h + Λ(P_e h + a e^ū ⋆ P_e h)`. -/
@[expose] def Lin (h : Ell1Z) : Ell1Z :=
  h - Aop (-h + lamOp (evenPart h + aR • (NormedSpace.exp ubar * evenPart h)))

/-- `Ē ⋆ P_e h` at a block index, as a finite sum over `|m| ≤ 26`. -/
theorem Ebar_mul_evenPart_apply (h : Ell1Z) {l : ℤ} (hl : l ∈ blk) :
    (Ebar * evenPart h) l =
      ∑ m ∈ blk2, (((Ebarq (l - m) + Ebarq (l + m)) / 2 : ℚ) : ℝ) * h m := by
  rw [mem_blk] at hl
  rw [mul_comm, mul_def, conv_one_apply]
  rw [tsum_eq_sum (s := blk2) (fun m hm => by
    rw [mem_blk2] at hm
    rw [Ebar_apply, Ebarq_eq_zero (by omega)]; simp)]
  simp only [evenPart_apply, Ebar_apply]
  have hsplit : ∀ m, (h m + h (-m)) / 2 * ((Ebarq (l - m) : ℚ) : ℝ) =
      1 / 2 * (h m * ((Ebarq (l - m) : ℚ) : ℝ)) + 1 / 2 * (h (-m) * ((Ebarq (l - m) : ℚ) : ℝ)) :=
    fun m => by ring
  simp only [hsplit, Finset.sum_add_distrib]
  have hneg : ∑ m ∈ blk2, h (-m) * ((Ebarq (l - m) : ℚ) : ℝ) =
      ∑ m ∈ blk2, h m * ((Ebarq (l + m) : ℚ) : ℝ) := by
    refine Finset.sum_nbij' (fun m => -m) (fun m => -m) ?_ ?_ ?_ ?_ ?_
    · intro m hm; simp only [mem_blk2, Int.natAbs_neg] at hm ⊢; omega
    · intro m hm; simp only [mem_blk2, Int.natAbs_neg] at hm ⊢; omega
    · intro m _; simp
    · intro m _; simp
    · intro m _; rw [← sub_eq_add_neg]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hneg, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast; ring

/-- Kronecker sums. -/
theorem sum_dq_mul (h : Ell1Z) {l : ℤ} (hl : l ∈ blk2) :
    ∑ m ∈ blk2, ((dq l m : ℚ) : ℝ) * h m = h l := by
  simp only [dq, ValidatedBVP.cast_ite_one_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, ite_eq_left hl]

/-- Reflected Kronecker sums. -/
theorem sum_dq_neg_mul (h : Ell1Z) {l : ℤ} (hl : -l ∈ blk2) :
    ∑ m ∈ blk2, ((dq l (-m) : ℚ) : ℝ) * h m = h (-l) := by
  rw [Finset.sum_eq_single (-l)]
  · simp [dq]
  · intro m _ hm
    have : l ≠ -m := fun h' => hm (by omega)
    simp [dq, this]
  · intro h'; exact absurd hl h'

/-- At a block index, the inner vector `-h + Λ(P_e h + a Ē ⋆ P_e h)` is the rational
matrix `J` applied to `h`. -/
theorem inner_apply_blk (h : Ell1Z) {l : ℤ} (hl : l ∈ blk) :
    (-h + lamOp (evenPart h + aR • (Ebar * evenPart h))) l =
      ∑ m ∈ blk2, ((Jq l m : ℚ) : ℝ) * h m := by
  have hl2 : l ∈ blk2 := by rw [mem_blk] at hl; rw [mem_blk2]; omega
  have hl2' : -l ∈ blk2 := by rw [mem_blk] at hl; rw [mem_blk2]; omega
  have hpt : ∀ m, ((Jq l m : ℚ) : ℝ) * h m = -(((dq l m : ℚ) : ℝ) * h m) +
      (lamq l : ℝ) * (1 / 2 * (((dq l m : ℚ) : ℝ) * h m) + 1 / 2 * (((dq l (-m) : ℚ) : ℝ) * h m) +
        aR * ((((Ebarq (l - m) + Ebarq (l + m)) / 2 : ℚ) : ℝ) * h m)) := by
    intro m; simp only [Jq, aR]; push_cast; ring
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    sum_dq_mul h hl2, sum_dq_neg_mul h hl2', ← Ebar_mul_evenPart_apply h hl]
  simp only [lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply, lamOp_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, evenPart_apply]
  ring

/-- On the block, `Lbar` is the rational matrix `C = I - A J`. -/
theorem Lbar_apply_blk (h : Ell1Z) {k : ℤ} (hk : k ∈ blk) :
    Lbar h k = ∑ m ∈ blk2, ((Cq k m : ℚ) : ℝ) * h m := by
  have hk2 : k ∈ blk2 := by rw [mem_blk] at hk; rw [mem_blk2]; omega
  have hL : Lbar h k = h k - ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) *
      ∑ m ∈ blk2, ((Jq l m : ℚ) : ℝ) * h m := by
    simp only [Lbar, lp.coeFn_sub, Pi.sub_apply, Aop_apply, hk, ite_true]
    congr 1
    exact Finset.sum_congr rfl fun l hl => by rw [inner_apply_blk h hl]
  rw [hL, ← sum_dq_mul h hk2]
  simp only [Cq, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => by ring

/-- Off the block, `Lbar h = Λ(P_e h + a Ē ⋆ P_e h)`. -/
theorem Lbar_apply_tail (h : Ell1Z) {k : ℤ} (hk : k ∉ blk) :
    Lbar h k = (lamq k : ℝ) * (evenPart h + aR • (Ebar * evenPart h)) k := by
  simp only [Lbar, lp.coeFn_sub, Pi.sub_apply, Aop_apply, hk, ite_false, lp.coeFn_add,
    lp.coeFn_neg, Pi.add_apply, Pi.neg_apply, lamOp_apply]
  ring

/-- **Block-plus-tail bound** `‖Lbar h‖ ≤ (31/10⁴ + (1 + a·1.571)/122) ‖h‖`. -/
theorem norm_Lbar_le (h : Ell1Z) :
    ‖Lbar h‖ ≤ (31 / 10000 + (1 + aR * (1571 / 1000)) / 122) * ‖h‖ := by
  rw [norm_eq_sum_add_tail (Lbar h) blk]
  have hblock : ∑ k ∈ blk, |Lbar h k| ≤ 31 / 10000 * ‖h‖ := by
    calc ∑ k ∈ blk, |Lbar h k| = ∑ k ∈ blk, |∑ m ∈ blk2, ((Cq k m : ℚ) : ℝ) * h m| :=
          Finset.sum_congr rfl fun k hk => by rw [Lbar_apply_blk h hk]
      _ ≤ 31 / 10000 * ∑ m ∈ blk2, |h m| :=
          sum_abs_matrix_mul_le _ _ _ _ fun m hm => by
            have := ValidatedBVP.ratCast_le (check_Zblock m hm)
            push_cast at this
            exact this
      _ ≤ 31 / 10000 * ‖h‖ := by gcongr; exact sum_abs_le_norm h blk2
  set w : Ell1Z := evenPart h + aR • (Ebar * evenPart h) with hw
  have hwn : ‖w‖ ≤ (1 + aR * (1571 / 1000)) * ‖h‖ := by
    have h1 := norm_evenPart_le h
    have h2 : ‖Ebar * evenPart h‖ ≤ 1571 / 1000 * ‖h‖ :=
      (norm_mul_le _ _).trans (mul_le_mul norm_Ebar_le h1 (norm_nonneg _) (by norm_num))
    have ha : (0 : ℝ) ≤ aR := by rw [aR_eq]; norm_num
    calc ‖w‖ ≤ ‖evenPart h‖ + ‖aR • (Ebar * evenPart h)‖ := norm_add_le _ _
      _ = ‖evenPart h‖ + aR * ‖Ebar * evenPart h‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      _ ≤ ‖h‖ + aR * (1571 / 1000 * ‖h‖) := by gcongr
      _ = (1 + aR * (1571 / 1000)) * ‖h‖ := by ring
  have htail : ∑' k, (if k ∈ blk then 0 else |Lbar h k|) ≤ 1 / 122 * ‖w‖ := by
    rw [norm_eq_tsum_abs, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ ((summable_abs _).mul_left _)
    · split_ifs with hk
      · positivity
      · rw [Lbar_apply_tail h hk, ← hw, abs_mul, abs_of_pos (lamq_pos' k)]
        have hl := lamq_le_tail (k := k) (by rw [mem_blk] at hk; omega)
        have := abs_nonneg (w k)
        nlinarith
    · exact (summable_abs (Lbar h)).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
  have : 1 / 122 * ‖w‖ ≤ (1 + aR * (1571 / 1000)) / 122 * ‖h‖ := by
    have := hwn; nlinarith
  linarith

/-- **`AΛ` bound** `‖A Λ w‖ ≤ 34 ‖w‖`. -/
theorem norm_AL_le (w : Ell1Z) : ‖Aop (lamOp w)‖ ≤ 34 * ‖w‖ := by
  rw [norm_eq_sum_add_tail _ blk, norm_eq_sum_add_tail w blk, mul_add]
  have hblock : ∑ k ∈ blk, |Aop (lamOp w) k| ≤ 34 * ∑ k ∈ blk, |w k| := by
    calc ∑ k ∈ blk, |Aop (lamOp w) k|
        = ∑ k ∈ blk, |∑ l ∈ blk, (((Aq k l * lamq l : ℚ)) : ℝ) * w l| := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Aop_apply, ite_eq_left hk]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [lamOp_apply]; push_cast; ring
      _ ≤ 34 * ∑ l ∈ blk, |w l| :=
          sum_abs_matrix_mul_le _ _ _ _ fun l hl => by
            have := ValidatedBVP.ratCast_le (check_AL l hl)
            push_cast at this ⊢
            exact this
  have htail : ∑' k, (if k ∈ blk then 0 else |Aop (lamOp w) k|) ≤
      34 * ∑' k, (if k ∈ blk then 0 else |w k|) := by
    have hs : Summable fun k => (if k ∈ blk then 0 else |w k|) :=
      (summable_abs w).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hs.mul_left _)
    · split_ifs with hk
      · simp
      · rw [Aop_apply, ite_eq_right hk, lamOp_apply, abs_neg, abs_mul, abs_of_pos (lamq_pos' k)]
        have hl := lamq_le_one' k
        have := abs_nonneg (w k)
        nlinarith
    · exact (summable_abs (Aop (lamOp w))).of_nonneg_of_le (fun k => by split_ifs <;> simp)
        (fun k => by split_ifs <;> simp)
  linarith

/-- `Lin = Lbar - a A Λ((e^ū - Ē) ⋆ P_e h)`. -/
theorem Lin_eq (h : Ell1Z) :
    Lin h = Lbar h - aR • Aop (lamOp ((NormedSpace.exp ubar - Ebar) * evenPart h)) := by
  simp only [Lin, Lbar, sub_mul, smul_sub, map_sub, ← lamOp_smul, ← Aop_smul, map_add]
  abel

/-- The certified `Z₀ = 0.0245`. -/
theorem Z0_bound : 31 / 10000 + (1 + aR * (1571 / 1000)) / 122 + aR * 34 * (8 / 10 ^ 14) ≤
    245 / 10000 := by
  rw [aR_eq]; norm_num

/-- **`Z₀` bound** `‖(I - A DF̃(ū)) h‖ ≤ 0.0245 ‖h‖`. -/
theorem norm_Lin_le (h : Ell1Z) : ‖Lin h‖ ≤ 245 / 10000 * ‖h‖ := by
  rw [Lin_eq]
  have ha : (0 : ℝ) ≤ aR := by rw [aR_eq]; norm_num
  have h1 := norm_Lbar_le h
  have h2 : ‖aR • Aop (lamOp ((NormedSpace.exp ubar - Ebar) * evenPart h))‖ ≤
      aR * 34 * (8 / 10 ^ 14) * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    have h3 := norm_AL_le ((NormedSpace.exp ubar - Ebar) * evenPart h)
    have h4 : ‖(NormedSpace.exp ubar - Ebar) * evenPart h‖ ≤ 8 / 10 ^ 14 * ‖h‖ :=
      (norm_mul_le _ _).trans (mul_le_mul norm_exp_ubar_sub_Ebar (norm_evenPart_le h)
        (norm_nonneg _) (by norm_num))
    calc aR * ‖Aop (lamOp ((NormedSpace.exp ubar - Ebar) * evenPart h))‖
        ≤ aR * (34 * (8 / 10 ^ 14 * ‖h‖)) := by gcongr; exact h3.trans (by gcongr)
      _ = aR * 34 * (8 / 10 ^ 14) * ‖h‖ := by ring
  have hZ := Z0_bound
  have hn := norm_nonneg h
  calc _ ≤ ‖Lbar h‖ + ‖aR • Aop (lamOp ((NormedSpace.exp ubar - Ebar) * evenPart h))‖ :=
        norm_sub_le _ _
    _ ≤ (31 / 10000 + (1 + aR * (1571 / 1000)) / 122) * ‖h‖ + aR * 34 * (8 / 10 ^ 14) * ‖h‖ :=
        add_le_add h1 h2
    _ ≤ 245 / 10000 * ‖h‖ := by nlinarith

/-! ### The residual `Y₀` -/

/-- The rational residual vector `F̄ = -ū + Λ(ū + a(Ē - 1))`. -/
@[expose] def Fbar : Ell1Z := -ubar + lamOp (ubar + aR • (Ebar - 1))

/-- Coordinates of `F̄`. -/
theorem Fbar_apply (k : ℤ) : Fbar k = Fbarq k := by
  simp only [Fbar, lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply, lamOp_apply,
    lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, smul_eq_mul, one_apply,
    ubar_apply, Ebar_apply, Fbarq, dq, aR]
  by_cases hk : k = 0 <;> simp [hk]

/-- `F̄` vanishes off `|k| ≤ 16`. -/
theorem Fbarq_eq_zero {k : ℤ} (hk : k ∉ blkK) : Fbarq k = 0 := by
  rw [mem_blkK] at hk
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  simp [Fbarq, ubarq_eq_zero (k := k) (by omega), Ebarq_eq_zero (k := k) (by omega), dq, hk0]

/-- `(A F̄)ₖ` is the exact rational `AFq k`. -/
theorem AFbar_apply (k : ℤ) : Aop Fbar k = AFq k := by
  rw [Aop_apply, AFq]
  split_ifs
  · push_cast; simp only [Fbar_apply]
  · rw [Fbar_apply]; push_cast; rfl

/-- `‖A F̄‖ ≤ 2.5·10⁻¹²`. -/
theorem norm_AFbar_le : ‖Aop Fbar‖ ≤ 25 / 10 ^ 13 := by
  rw [norm_eq_sum_of_support _ blkK (fun k hk => by
    have hkb : k ∉ blk := by rw [mem_blk]; rw [mem_blkK] at hk; omega
    rw [AFbar_apply, AFq, ite_eq_right hkb, Fbarq_eq_zero hk]; simp)]
  simp only [AFbar_apply]
  have := ValidatedBVP.ratCast_le check_Y
  push_cast at this
  exact this

/-- `F(ū) = F̄ + a Λ(e^ū - Ē)`. -/
theorem Fmap_ubar : Fmap ubar = Fbar + aR • lamOp (NormedSpace.exp ubar - Ebar) := by
  simp only [Fmap, Fbar, ← lamOp_smul, add_assoc, ← map_add, smul_sub]
  congr 2
  abel

/-- `F̃(ū) = F(ū)` since `ū` is even. -/
theorem Ftil_ubar : Ftil ubar = Fmap ubar := by
  rw [Ftil, evenPart_of_even ubar_even, oddPart_of_even ubar_even, sub_zero]

/-- **Residual bound** `‖A F̃(ū)‖ ≤ Y₀ = 6·10⁻¹²`. -/
theorem residual_bound : ‖Aop (Ftil ubar)‖ ≤ 6 / 10 ^ 12 := by
  rw [Ftil_ubar, Fmap_ubar, map_add, Aop_smul]
  have ha : (0 : ℝ) ≤ aR := by rw [aR_eq]; norm_num
  have h1 := norm_AFbar_le
  have h2 : ‖aR • Aop (lamOp (NormedSpace.exp ubar - Ebar))‖ ≤ aR * (34 * (8 / 10 ^ 14)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    gcongr
    exact (norm_AL_le _).trans (by gcongr; exact norm_exp_ubar_sub_Ebar)
  calc _ ≤ ‖Aop Fbar‖ + ‖aR • Aop (lamOp (NormedSpace.exp ubar - Ebar))‖ := norm_add_le _ _
    _ ≤ 25 / 10 ^ 13 + aR * (34 * (8 / 10 ^ 14)) := add_le_add h1 h2
    _ ≤ 6 / 10 ^ 12 := by rw [aR_eq]; norm_num

/-! ### The Lipschitz estimate -/

/-- Exact splitting `T u - T v = (I - A DF̃(ū))(u - v) - a A Λ R` with the second-order
remainder `R = e^{P_e u} - e^{P_e v} - e^ū (P_e u - P_e v)`. -/
theorem T_sub_eq (u v : Ell1Z) :
    (u - Aop (Ftil u)) - (v - Aop (Ftil v)) = Lin (u - v) - aR • Aop (lamOp
      (NormedSpace.exp (evenPart u) - NormedSpace.exp (evenPart v) -
        NormedSpace.exp ubar * (evenPart u - evenPart v))) := by
  simp only [Lin, Ftil, Fmap, evenPart_sub, map_add, map_sub, map_neg, lamOp_smul, Aop_smul,
    smul_sub, mul_sub]
  have e1 := evenPart_add_oddPart u
  have e2 := evenPart_add_oddPart v
  generalize evenPart u = eu at e1 ⊢
  generalize oddPart u = ou at e1 ⊢
  generalize evenPart v = ev at e2 ⊢
  generalize oddPart v = ov at e2 ⊢
  subst e1 e2
  simp only [map_add]
  abel

/-- `e^x ≤ 2.72` for `x ≤ 1`. -/
theorem exp_le_272 {x : ℝ} (hx : x ≤ 1) : Real.exp x ≤ 272 / 100 :=
  (Real.exp_le_exp.2 hx).trans (Real.exp_one_lt_d9.le.trans (by norm_num))

/-- **Lipschitz bound** on `B̄(ū, r)` for `r ≤ 1/100`, with `Z₀ = 0.0245`, `Z₂ = 95`. -/
theorem T_lipschitz (r : ℝ) (hr : r ≤ 1 / 100) :
    ∀ u ∈ closedBall ubar r, ∀ v ∈ closedBall ubar r,
      ‖(u - Aop (Ftil u)) - (v - Aop (Ftil v))‖ ≤ (245 / 10000 + 95 * r) * ‖u - v‖ := by
  intro u hu v hv
  rw [mem_closedBall, dist_eq_norm] at hu hv
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hu
  have hPe : ∀ w : Ell1Z, ‖w - ubar‖ ≤ r → ‖evenPart w - ubar‖ ≤ r := fun w hw => by
    calc ‖evenPart w - ubar‖ = ‖evenPart (w - ubar)‖ := by
          rw [evenPart_sub, evenPart_of_even ubar_even]
      _ ≤ ‖w - ubar‖ := norm_evenPart_le _
      _ ≤ r := hw
  have hR := norm_exp_sub_exp_sub_mul_le (hPe u hu) (hPe v hv)
  have hexp : Real.exp (‖ubar‖ + r) ≤ 272 / 100 :=
    exp_le_272 (by have := norm_ubar_le; linarith)
  have hd : ‖evenPart u - evenPart v‖ ≤ ‖u - v‖ := by
    rw [← evenPart_sub]; exact norm_evenPart_le _
  set R := NormedSpace.exp (evenPart u) - NormedSpace.exp (evenPart v) -
    NormedSpace.exp ubar * (evenPart u - evenPart v) with hRdef
  have hRn : ‖R‖ ≤ r * (272 / 100) * ‖u - v‖ := by
    calc ‖R‖ ≤ r * Real.exp (‖ubar‖ + r) * ‖evenPart u - evenPart v‖ := hR
      _ ≤ r * (272 / 100) * ‖u - v‖ := by gcongr
  have ha : (0 : ℝ) ≤ aR := by rw [aR_eq]; norm_num
  rw [T_sub_eq]
  have h1 := norm_Lin_le (u - v)
  have h2 : ‖aR • Aop (lamOp R)‖ ≤ 95 * r * ‖u - v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    calc aR * ‖Aop (lamOp R)‖ ≤ aR * (34 * (r * (272 / 100) * ‖u - v‖)) := by
          gcongr; exact (norm_AL_le R).trans (by gcongr)
      _ ≤ 95 * r * ‖u - v‖ := by
          rw [aR_eq]
          have := norm_nonneg (u - v)
          nlinarith [mul_nonneg hr0 this]
  calc _ ≤ ‖Lin (u - v)‖ + ‖aR • Aop (lamOp R)‖ := norm_sub_le _ _
    _ ≤ 245 / 10000 * ‖u - v‖ + 95 * r * ‖u - v‖ := add_le_add h1 h2
    _ = (245 / 10000 + 95 * r) * ‖u - v‖ := by ring

/-! ### Injectivity of the approximate inverse -/

/-- `A` is injective (certified by `‖I - J A‖ ≤ 1/2` on the block, `-I` on the tail). -/
theorem Aop_injective : Function.Injective Aop := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hz : ∀ k, Aop x k = 0 := fun k => by rw [hx]; rfl
  have htail : ∀ k ∉ blk, x k = 0 := fun k hk => by
    have := hz k; rw [Aop_apply, ite_eq_right hk] at this; linarith
  have hblkA : ∀ k ∈ blk, ∑ l ∈ blk, ((Aq k l : ℚ) : ℝ) * x l = 0 := fun k hk => by
    have := hz k; rwa [Aop_apply, ite_eq_left hk] at this
  have hfix : ∀ k ∈ blk, x k = ∑ m ∈ blk, ((Dq k m : ℚ) : ℝ) * x m := by
    intro k hk
    simp only [Dq, dq, Rat.cast_sub, ValidatedBVP.cast_ite_one_zero, Rat.cast_sum,
      Rat.cast_mul]
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, hk, ite_true, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∑ l ∈ blk, ∑ m ∈ blk, ((Jq k l : ℚ) : ℝ) * ((Aq l m : ℚ) : ℝ) * x m = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      simp only [mul_assoc, ← Finset.mul_sum, hblkA l hl, mul_zero]
    rw [this, sub_zero]
  have hS : ∑ k ∈ blk, |x k| ≤ 1 / 2 * ∑ k ∈ blk, |x k| := by
    calc ∑ k ∈ blk, |x k| = ∑ k ∈ blk, |∑ m ∈ blk, ((Dq k m : ℚ) : ℝ) * x m| :=
          Finset.sum_congr rfl fun k hk => by rw [← hfix k hk]
      _ ≤ 1 / 2 * ∑ k ∈ blk, |x k| :=
          sum_abs_matrix_mul_le _ _ _ _ fun m hm => by
            have := ValidatedBVP.ratCast_le (check_inj m hm)
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

/-! ### The validated coefficient solution -/

/-- `p(10⁻¹¹) < 0`. -/
theorem radii_neg_small : radiiPoly (6 / 10 ^ 12) (245 / 10000) 95 (1 / 10 ^ 11) < 0 := by
  norm_num [radiiPoly]

/-- `p(1/200) < 0` (uniqueness radius). -/
theorem radii_neg_large : radiiPoly (6 / 10 ^ 12) (245 / 10000) 95 (1 / 200) < 0 := by
  norm_num [radiiPoly]

/-- Sanity: the same bounds reject the radius `10⁻¹² < Y₀`. -/
theorem rejected_small_radius : ¬ radiiPoly (6 / 10 ^ 12) (245 / 10000) 95 (1 / 10 ^ 12) < 0 :=
  radii_polynomial_rejects_small (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Validated coefficient solution.** `F̃` has a zero within `10⁻¹¹` of `ū` in `ℓ¹`,
unique within `1/200`. -/
theorem validated_coeff :
    ∃ u ∈ closedBall ubar (1 / 10 ^ 11), Ftil u = 0 ∧
      ∀ v ∈ closedBall ubar (1 / 200), Ftil v = 0 → v = u := by
  obtain ⟨u₁, hu₁, hF₁, -⟩ := radii_polynomial_zero Ftil Aop Aop_injective ubar
    (by norm_num : (0:ℝ) < 1 / 10 ^ 11) (by norm_num) (by norm_num) residual_bound
    (T_lipschitz _ (by norm_num)) radii_neg_small
  obtain ⟨u₂, -, -, huniq⟩ := radii_polynomial_zero Ftil Aop Aop_injective ubar
    (by norm_num : (0:ℝ) < 1 / 200) (by norm_num) (by norm_num) residual_bound
    (T_lipschitz _ (by norm_num)) radii_neg_large
  have hsub : closedBall ubar (1 / 10 ^ 11) ⊆ closedBall ubar (1 / 200) :=
    closedBall_subset_closedBall (by norm_num)
  have h12 : u₁ = u₂ := huniq u₁ (hsub hu₁) hF₁
  refine ⟨u₁, hu₁, hF₁, fun v hv hFv => ?_⟩
  rw [h12]; exact huniq v hv hFv

/-! ### From a zero of `F̃` to the coefficient equation -/

/-- `λ` is even. -/
theorem lamq_neg (k : ℤ) : lamq (-k) = lamq k := by simp [lamq, ValidatedBVP.lamq]

/-- `F` maps even sequences to even sequences. -/
theorem Fmap_even {φ : Ell1Z} (hφ : ∀ k, φ (-k) = φ k) (k : ℤ) : Fmap φ (-k) = Fmap φ k := by
  rw [Fmap_apply, Fmap_apply, hφ, exp_even hφ, lamq_neg]
  simp only [neg_eq_zero]

/-- **A zero of `F̃` is even and a zero of `F`.** -/
theorem Ftil_zero {u : Ell1Z} (h : Ftil u = 0) : (∀ k, u (-k) = u k) ∧ Fmap u = 0 := by
  have h1 : Fmap (evenPart u) = oddPart u := sub_eq_zero.1 h
  have heven : ∀ k, u (-k) = u k := by
    intro k
    have h2 := Fmap_even (evenPart_even u) k
    rw [h1, oddPart_apply, oddPart_apply, neg_neg] at h2
    linarith
  refine ⟨heven, ?_⟩
  rw [← evenPart_of_even heven, h1, oddPart_of_even heven]

/-- The coefficient equation `-k² uₖ = -a ((e^u)ₖ - δₖ)` from `F(u) = 0`. -/
theorem coeff_of_Fmap {u : Ell1Z} (h : Fmap u = 0) (k : ℤ) :
    -((k : ℝ) ^ 2 * u k) = (-aR • (NormedSpace.exp u - 1)) k := by
  have hk := congrArg (fun z : Ell1Z => z k) h
  simp only [Fmap_apply, lp.coeFn_zero, Pi.zero_apply] at hk
  have hl : (lamq k : ℝ) = 1 / (1 + (k : ℝ) ^ 2) := by
    simp [lamq, ValidatedBVP.lamq]
  rw [hl] at hk
  have hpos : (0 : ℝ) < 1 + (k : ℝ) ^ 2 := by positivity
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, one_apply, smul_eq_mul]
  field_simp at hk
  linarith

/-- The candidate as a function: `ū(z) = ∑_{|k| ≤ 10} ūₖ cos kz`. -/
@[expose] def ubarFun (z : ℝ) : ℝ := ∑ k ∈ blk, ((ubarq k : ℚ) : ℝ) * Real.cos (k * z)

/-- `evalCos ū = ū(z)`. -/
theorem evalCos_ubar (z : ℝ) : evalCos ubar z = ubarFun z := by
  rw [evalCos, tsum_eq_sum (s := blk) (fun k hk => by
    rw [ubar_apply, ubarq_eq_zero (by rw [mem_blk] at hk; omega)]; simp)]
  simp only [ubar_apply, ubarFun]

/-- **Validated classical profile.** There is a `C²`, even, `2π`-periodic function `Φ` with
`Φ'' + a (e^Φ - 1) = 0` everywhere (`a = 51/50`), uniformly within `10⁻¹¹` of the candidate
`ū`. It is the cosine series of an even `u ∈ ℓ¹(ℤ)` with `‖u - ū‖₁ ≤ 10⁻¹¹`, the unique zero
of `F̃` within `1/200` of `ū`. -/
theorem validated_slab_profile :
    ∃ u : Ell1Z, ‖u - ubar‖ ≤ 1 / 10 ^ 11 ∧ (∀ k, u (-k) = u k) ∧
      (∀ v ∈ closedBall ubar (1 / 200), Ftil v = 0 → v = u) ∧
      ContDiff ℝ 2 (evalCos u) ∧ Function.Periodic (evalCos u) (2 * Real.pi) ∧
      (∀ z, evalCos u (-z) = evalCos u z) ∧
      Differentiable ℝ (evalCos u) ∧ Differentiable ℝ (deriv (evalCos u)) ∧
      (∀ z, deriv (deriv (evalCos u)) z + aR * (Real.exp (evalCos u z) - 1) = 0) ∧
      ∀ z, |evalCos u z - ubarFun z| ≤ 1 / 10 ^ 11 := by
  obtain ⟨u, hu, hF, huniq⟩ := validated_coeff
  rw [mem_closedBall, dist_eq_norm] at hu
  obtain ⟨heven, hF0⟩ := Ftil_zero hF
  obtain ⟨hC2, hper, hd1, hd2, hdd⟩ := classical_of_coeff u _ (coeff_of_Fmap hF0)
  have hderiv : deriv (evalCos u) = dCosSum u := funext fun z => (hd1 z).deriv
  refine ⟨u, hu, heven, huniq, hC2, hper, fun z => ?_, fun z => (hd1 z).differentiableAt,
    ?_, fun z => ?_, fun z => ?_⟩
  · unfold evalCos
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1; funext k
    simp only [Equiv.neg_apply, heven, Int.cast_neg]
    congr 1
    rw [show -(k : ℝ) * -z = k * z by ring]
  · rw [hderiv]; exact fun z => (hd2 z).differentiableAt
  · rw [hdd z, evalCos_smul, evalCos_sub, evalCos_exp u heven, evalCos_one]; ring
  · rw [← evalCos_ubar, ← evalCos_sub]
    exact (abs_evalCos_le _ z).trans hu

/-! ### The kernel slab equilibrium -/

open PlasmaLean.Equilibrium Matrix

/-- Slab magnetic field `B(z) = (Φ'(z), B₀, 0)` from a flux function `Φ` and a guide field. -/
@[expose] def slabB (Φ : ℝ → ℝ) (B₀ : ℝ) (z : ℝ) : Vec3 := ![deriv Φ z, B₀, 0]

/-- Slab current `J(z) = (0, Φ''(z)/μ₀, 0)`. -/
@[expose] def slabJ (Φ : ℝ → ℝ) (μ₀ : ℝ) (z : ℝ) : Vec3 := ![0, deriv (deriv Φ) z / μ₀, 0]

/-- The exponential pressure profile `P(ψ) = (a/μ₀)(e^ψ - ψ)` as a function of the flux. -/
@[expose] def presProfile (μ₀ ψ : ℝ) : ℝ := aR / μ₀ * (Real.exp ψ - ψ)

/-- **Slab Grad–Shafranov solutions are kernel equilibria.** Let `P` be a pressure profile
with derivative `P'`, and let `ψ` be twice differentiable with `ψ'' = -μ₀ P'(ψ)`. Then
`B = (ψ', B₀, 0)`, `J = (0, ψ''/μ₀, 0)` and `p = P(ψ)` satisfy the static slab MHD laws
`StaticSlab` (force balance `J × B = ∇p`, `div B = 0`, `curl B = μ₀ J`). -/
theorem staticSlab_of_GS (ψ P P' : ℝ → ℝ) (μ₀ B₀ : ℝ) (hμ : 0 < μ₀)
    (hd1 : Differentiable ℝ ψ) (hd2 : Differentiable ℝ (deriv ψ))
    (hP : ∀ x, HasDerivAt P (P' x) x)
    (hgs : ∀ z, deriv (deriv ψ) z = -μ₀ * P' (ψ z)) :
    StaticSlab (slabB ψ B₀) (slabJ ψ μ₀) (fun z => P (ψ z)) μ₀ := by
  have hp : ∀ z, HasDerivAt (fun z => P (ψ z)) (P' (ψ z) * deriv ψ z) z := fun z =>
    (hP (ψ z)).comp z (hd1 z).hasDerivAt
  constructor
  · exact hμ
  · intro i
    fin_cases i
    · simpa [slabB] using hd2
    · simp [slabB]
    · simp [slabB]
  · exact fun z => (hp z).differentiableAt
  · intro z
    rw [(hp z).deriv]
    have h := hgs z
    ext i
    fin_cases i
    · simp [cross_apply, slabJ, slabB]
    · simp [cross_apply, slabJ, slabB]
    · simp only [cross_apply, slabJ, slabB, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        cons_val_one, cons_val_zero, cons_val, mul_zero, zero_mul, sub_self, zero_sub,
        Fin.reduceFinMk]
      rw [h]
      field_simp
  · intro z; simp [slabB]
  · intro z
    ext i
    fin_cases i
    · simp [slabCurl, slabB, slabJ]
    · simp [slabCurl, slabB, slabJ]
      field_simp
    · simp [slabCurl, slabB, slabJ]

/-- Derivative of the exponential profile: `P'(ψ) = (a/μ₀)(e^ψ - 1)`. -/
theorem hasDerivAt_presProfile (μ₀ x : ℝ) :
    HasDerivAt (presProfile μ₀) (aR / μ₀ * (Real.exp x - 1)) x := by
  have := ((Real.hasDerivAt_exp x).sub (hasDerivAt_id' x)).const_mul (aR / μ₀)
  exact this

/-- **Any classical solution of `Φ'' + a(e^Φ - 1) = 0` gives a kernel equilibrium** with the
exponential profile `p = (a/μ₀)(e^Φ - Φ)`. -/
theorem staticSlab_of_profile (Φ : ℝ → ℝ) (μ₀ B₀ : ℝ) (hμ : 0 < μ₀)
    (hd1 : Differentiable ℝ Φ) (hd2 : Differentiable ℝ (deriv Φ))
    (hode : ∀ z, deriv (deriv Φ) z + aR * (Real.exp (Φ z) - 1) = 0) :
    StaticSlab (slabB Φ B₀) (slabJ Φ μ₀) (fun z => presProfile μ₀ (Φ z)) μ₀ := by
  refine staticSlab_of_GS Φ (presProfile μ₀) (fun x => aR / μ₀ * (Real.exp x - 1)) μ₀ B₀ hμ
    hd1 hd2 (hasDerivAt_presProfile μ₀) fun z => ?_
  have := hode z
  field_simp
  linarith

/-- The pressure profile is bounded below by `a/μ₀ > 0` (`e^ψ ≥ 1 + ψ`). -/
theorem presProfile_ge (μ₀ ψ : ℝ) (hμ : 0 < μ₀) : aR / μ₀ ≤ presProfile μ₀ ψ := by
  unfold presProfile
  have h := Real.add_one_le_exp ψ
  have ha : 0 < aR / μ₀ := div_pos (by rw [aR_eq]; norm_num) hμ
  nlinarith

/-- `ū(0) - ū(π) ≥ 0.98` (exact rational check). -/
theorem ubar_shear : 98 / 100 ≤ ∑ k ∈ blk, ubarq k - ∑ k ∈ blk, ubarq k * (-1) ^ k := by
  decide +kernel

/-- **Validated slab equilibrium with exponential pressure.** For every `μ₀ > 0` and guide
field `B₀`, there is a `C²`, even, `2π`-periodic flux function `Φ`, uniformly within `10⁻¹¹` of
the explicit candidate `ū`, such that

* `B = (Φ', B₀, 0)`, `J = (0, Φ''/μ₀, 0)`, `p = (a/μ₀)(e^Φ - Φ)` satisfy the kernel slab laws
  `StaticSlab` (so `J × B = ∇p` pointwise, `div B = 0`, `curl B = μ₀ J`);
* the pressure is a non-polynomial function of the flux, `p = P(Φ)`, with `p ≥ a/μ₀ > 0`;
* the equilibrium is non-trivial: `Φ(0) - Φ(π) ≥ 9/10`. -/
theorem validated_slab_equilibrium (μ₀ B₀ : ℝ) (hμ : 0 < μ₀) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ 2 Φ ∧ Function.Periodic Φ (2 * Real.pi) ∧
      (∀ z, |Φ z - ubarFun z| ≤ 1 / 10 ^ 11) ∧
      StaticSlab (slabB Φ B₀) (slabJ Φ μ₀) (fun z => presProfile μ₀ (Φ z)) μ₀ ∧
      (∀ z, ForceBalance (slabB Φ B₀ z) (slabJ Φ μ₀ z)
        ![0, 0, deriv (fun z => presProfile μ₀ (Φ z)) z]) ∧
      (∀ z, aR / μ₀ ≤ presProfile μ₀ (Φ z)) ∧
      9 / 10 ≤ Φ 0 - Φ Real.pi := by
  obtain ⟨u, -, -, -, hC2, hper, -, hd1, hd2, hode, hclose⟩ := validated_slab_profile
  have hS := staticSlab_of_profile (evalCos u) μ₀ B₀ hμ hd1 hd2 hode
  refine ⟨evalCos u, hC2, hper, hclose, hS, fun z => slab_forceBalance _ _ _ μ₀ z,
    fun z => presProfile_ge μ₀ _ hμ, ?_⟩
  have h0 := hclose 0
  have hπ := hclose Real.pi
  have hb0 : ubarFun 0 = ∑ k ∈ blk, ((ubarq k : ℚ) : ℝ) := by simp [ubarFun]
  have hbπ : ubarFun Real.pi = ∑ k ∈ blk, ((ubarq k : ℚ) : ℝ) * (-1) ^ k := by
    simp only [ubarFun, Real.cos_int_mul_pi]
  have hs := ValidatedBVP.ratCast_le ubar_shear
  push_cast at hs
  rw [hb0] at h0
  rw [hbπ] at hπ
  have := (abs_le.1 h0).1
  have := (abs_le.1 hπ).2
  linarith

/-! ### Physical scaling -/

/-- Scaled flux `ψ(z) = B⋆ L Φ(z/L)` (field scale `B⋆`, length scale `L`). -/
@[expose] def scaledFlux (Φ : ℝ → ℝ) (Bs L z : ℝ) : ℝ := Bs * L * Φ (z / L)

/-- Scaled exponential profile `P(ψ) = (a B⋆²/μ₀)(e^{ψ/(B⋆L)} - ψ/(B⋆L))`. -/
@[expose] def scaledProfile (μ₀ Bs L ψ : ℝ) : ℝ :=
  aR * Bs ^ 2 / μ₀ * (Real.exp (ψ / (Bs * L)) - ψ / (Bs * L))

/-- **Scaled validated slab equilibrium.** For field scale `B⋆ > 0`, length scale `L > 0`,
`μ₀ > 0` and guide field `B₀`, the flux `ψ(z) = B⋆ L Φ(z/L)` (period `2πL`) built from the
validated profile gives a kernel slab equilibrium with the exponential pressure
`p = (a B⋆²/μ₀)(e^{ψ/(B⋆L)} - ψ/(B⋆L)) ≥ a B⋆²/μ₀`. E.g. `B⋆ = 1 T`, `L = 1 m`,
`μ₀ = 4π·10⁻⁷` gives a sheared field `|Bₓ| ≲ 0.5 T` and `p ≈ 0.8 MPa`; this is a change of
variables, not a calibrated device. -/
theorem validated_slab_equilibrium_scaled (μ₀ B₀ Bs L : ℝ) (hμ : 0 < μ₀) (hB : 0 < Bs)
    (hL : 0 < L) :
    ∃ Φ : ℝ → ℝ, (∀ z, |Φ z - ubarFun z| ≤ 1 / 10 ^ 11) ∧
      Function.Periodic Φ (2 * Real.pi) ∧
      StaticSlab (slabB (scaledFlux Φ Bs L) B₀) (slabJ (scaledFlux Φ Bs L) μ₀)
        (fun z => scaledProfile μ₀ Bs L (scaledFlux Φ Bs L z)) μ₀ ∧
      ∀ z, aR * Bs ^ 2 / μ₀ ≤ scaledProfile μ₀ Bs L (scaledFlux Φ Bs L z) := by
  obtain ⟨u, -, -, -, -, hper, -, hd1, hd2, hode, hclose⟩ := validated_slab_profile
  set Φ := evalCos u with hΦ
  have hLne : L ≠ 0 := hL.ne'
  have hBne : Bs ≠ 0 := hB.ne'
  have hlin : ∀ z, HasDerivAt (fun z : ℝ => z / L) (1 / L) z := fun z => by
    simpa using (hasDerivAt_id' z).div_const L
  have hψ1 : ∀ z, HasDerivAt (scaledFlux Φ Bs L) (Bs * deriv Φ (z / L)) z := by
    intro z
    have := ((hd1 (z / L)).hasDerivAt.comp z (hlin z)).const_mul (Bs * L)
    convert this using 1
    · rfl
    · field_simp
  have hD1 : deriv (scaledFlux Φ Bs L) = fun z => Bs * deriv Φ (z / L) :=
    funext fun z => (hψ1 z).deriv
  have hψ2 : ∀ z, HasDerivAt (fun z => Bs * deriv Φ (z / L))
      (Bs / L * deriv (deriv Φ) (z / L)) z := by
    intro z
    have := ((hd2 (z / L)).hasDerivAt.comp z (hlin z)).const_mul Bs
    convert this using 1
    · rfl
    · field_simp
  have hD2 : deriv (deriv (scaledFlux Φ Bs L)) = fun z => Bs / L * deriv (deriv Φ) (z / L) := by
    rw [hD1]; exact funext fun z => (hψ2 z).deriv
  have hP : ∀ x, HasDerivAt (scaledProfile μ₀ Bs L)
      (aR * Bs ^ 2 / μ₀ * (Real.exp (x / (Bs * L)) * (1 / (Bs * L)) - 1 / (Bs * L))) x := by
    intro x
    have hx : HasDerivAt (fun x : ℝ => x / (Bs * L)) (1 / (Bs * L)) x := by
      simpa using (hasDerivAt_id' x).div_const (Bs * L)
    exact ((hx.exp).sub hx).const_mul _
  have hratio : ∀ z, scaledFlux Φ Bs L z / (Bs * L) = Φ (z / L) := fun z => by
    simp only [scaledFlux]; field_simp
  refine ⟨Φ, hclose, hper, ?_, fun z => ?_⟩
  · refine staticSlab_of_GS _ _ _ μ₀ B₀ hμ (fun z => (hψ1 z).differentiableAt) ?_ hP ?_
    · rw [hD1]; exact fun z => (hψ2 z).differentiableAt
    · intro z
      rw [hD2, hratio]
      have := hode (z / L)
      simp only
      field_simp
      linear_combination this
  · simp only [scaledProfile, hratio]
    have h := Real.add_one_le_exp (Φ (z / L))
    have ha : 0 < aR * Bs ^ 2 / μ₀ := div_pos (mul_pos (by rw [aR_eq]; norm_num) (by positivity)) hμ
    nlinarith

end PlasmaLean.Design.ValidatedSlab
