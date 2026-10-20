/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAFrame

/-!
# The twist of torus A (KAM route, K3 lemma 5, part 2)

Certifies the twist (non-degeneracy) hypothesis (H-twist) of the K3 plan
(`notes/theory/kam-k3-plan.md` §2) for torus A: the torsion density `T₀` of the symplectic frame
of `Design/KamTorusAFrame` satisfies, **at every point of the torus**,

  `T₀(θ, φ) + g(θ, φ) > 3/10`  (`torusA_torsion_shifted`),

for an explicit trigonometric polynomial `g` with zero mean (`gF`, `tG_centre`). Hence the
average of the torsion over the torus is `⟨T₀⟩ ≥ 3/10` (`Design/KamTorusATwistAvg`). The
numerical value is `⟨T₀⟩ ≈ 0.39864 ≈ 2π · dι/dΦ` (`dι/dΦ ≈ 0.063`, the shear of the oracle).

**Method.**
1. A low-degree surrogate torus `(1 + rS, zS)` with derivatives `aS, bS` (`Design/
   KamTorusAFrameData`) is within `2.3 × 10⁻⁷` of torus A (`close_r`, `close_z`, `close_a`,
   `close_b`; `ℓ¹` norms of coefficient differences computed in the kernel).
2. On the surrogate, `s² F ≥ 0.9` where `F = 10 · 16 R³ G + D_l³ W₀² (10 g − 3)` and `s` is a
   trigonometric multiplier (`phiS_ge`): `s² F` is the value on the unit torus of the integer
   polynomial `−Φ̂` (`evalC_PhiP`, the phase bridge `Ex.evH_phase`), whose `ℓ¹` distance to its
   centre monomial is an exact Kronecker digit sum (`check_phi`).
3. Moving to torus A changes `s² F` by at most `0.3` (`Ex.abs_eval_sub_le`, `dmaj_phi`).
4. `s² F = 10 s² D_l³ W₀² (T₀ + g − 3/10)` (`phiA_eq`) with `D_l, W₀ ≠ 0`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamTorusA.Frame

open Finset Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr

/-! ## The surrogate torus and the certificate functions -/

/-- `r̃ = R̃ − 1` of the surrogate torus. -/
def rS (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (tA i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)
/-- `z̃` of the surrogate torus. -/
def zS (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (tB i j : ℝ) / 2 ^ pS * Real.sin (ang i j θ φ)
/-- `∂_θ R̃`. -/
def aS (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (tA i j : ℝ) / 2 ^ pS * (-Real.sin (ang i j θ φ) * ((i : ℝ) - N))
/-- `∂_θ z̃`. -/
def bS (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
    (tB i j : ℝ) / 2 ^ pS * (Real.cos (ang i j θ φ) * ((i : ℝ) - N))
/-- The zero-mean certificate function `g`. -/
def gF (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (tG i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)
/-- The positivity multiplier `s`. -/
def sF (θ φ : ℝ) : ℝ :=
  ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (tS i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ)

/-! ## Sup bounds from `ℓ¹` norms -/

/-- `gridL1` as a real double sum of absolute values. -/
theorem gridL1_eq (d : ℕ → ℕ → ℤ) :
    (gridL1 d : ℝ) = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), |(d i j : ℝ)| := by
  simp only [gridL1, rsum_eq, Nat.cast_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [Nat.cast_natAbs, Int.cast_abs]

/-- `|∑ (d i j / s) fᵢⱼ| ≤ ‖d‖₁ / s` when `|fᵢⱼ| ≤ 1`. -/
theorem abs_gridSum_le (d : ℕ → ℕ → ℤ) (f : ℕ → ℕ → ℝ) (hf : ∀ i j, |f i j| ≤ 1) {s : ℝ}
    (hs : 0 < s) :
    |∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), (d i j : ℝ) / s * f i j| ≤
      gridL1 d / s := by
  rw [gridL1_eq, sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [sum_div]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_div, abs_of_pos hs]
  calc |(d i j : ℝ)| / s * |f i j| ≤ |(d i j : ℝ)| / s * 1 :=
        mul_le_mul_of_nonneg_left (hf i j) (by positivity)
    _ = |(d i j : ℝ)| / s := mul_one _

/-- `|−sin x · y| ≤ 1` for `|y| ≤ 1`. -/
theorem abs_sin_mul_le {x y : ℝ} (hy : |y| ≤ 1) : |-Real.sin x * y| ≤ 1 := by
  rw [abs_mul, abs_neg]
  exact (mul_le_mul (Real.abs_sin_le_one x) hy (abs_nonneg _) zero_le_one).trans (by norm_num)

/-- `2^P = 2^{P−pS} 2^{pS}`. -/
theorem P_sub_pS : (2 : ℝ) ^ P = 2 ^ (P - pS) * 2 ^ pS := by
  rw [← pow_add]; norm_num [P, pS]

/-- `|g| ≤ 12.446`. -/
theorem abs_gF_le (θ φ : ℝ) : |gF θ φ| ≤ 6223 / 500 := by
  have h := abs_gridSum_le tG (fun i j => Real.cos (ang i j θ φ))
    (fun i j => Real.abs_cos_le_one _) (show (0 : ℝ) < 2 ^ pS by positivity)
  have c : (500 : ℝ) * gridL1 tG ≤ 6223 * 2 ^ pS := by exact_mod_cast l1_tG
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-- `|s| ≤ 1.91`. -/
theorem abs_sF_le (θ φ : ℝ) : |sF θ φ| ≤ 191 / 100 := by
  have h := abs_gridSum_le tS (fun i j => Real.cos (ang i j θ φ))
    (fun i j => Real.abs_cos_le_one _) (show (0 : ℝ) < 2 ^ pS by positivity)
  have c : (100 : ℝ) * gridL1 tS ≤ 191 * 2 ^ pS := by exact_mod_cast l1_tS
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-- The centre mode has phase `0`. -/
theorem ang_centre (θ φ : ℝ) : ang N M θ φ = 0 := by simp [ang]

/-- `|R − (1 + r̃)| ≤ 7.3 × 10⁻⁸`. -/
theorem close_r (θ φ : ℝ) : |rS θ φ - (torusR θ φ - 1)| ≤ 73 / 10 ^ 9 := by
  set d : ℕ → ℕ → ℤ := fun i j => cA i j - 2 ^ (P - pS) * tA i j -
    (if i = N ∧ j = M then 2 ^ P else 0) with hd
  have e : torusR θ φ - 1 - rS θ φ = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
      (d i j : ℝ) / 2 ^ P * Real.cos (ang i j θ φ) := by
    have h1 : (1 : ℝ) = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        ((if i = N ∧ j = M then (2 : ℤ) ^ P else 0 : ℤ) : ℝ) / 2 ^ P * Real.cos (ang i j θ φ) := by
      rw [sum_eq_single N, sum_eq_single M]
      · simp only [and_self, ite_true, ang_centre, Real.cos_zero]; push_cast; field_simp
      · intro j _ hj; simp [hj]
      · intro h; simp [M] at h
      · intro i _ hi; refine sum_eq_zero fun j _ => by simp [hi]
      · intro h; simp [N] at h
    rw [h1, torusR, rS, ← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hd]
    push_cast
    rw [P_sub_pS]
    field_simp
    ring
  have h := abs_gridSum_le d (fun i j => Real.cos (ang i j θ φ))
    (fun i j => Real.abs_cos_le_one _) (show (0 : ℝ) < 2 ^ P by positivity)
  rw [← e] at h
  have c := (Nat.cast_le (α := ℝ)).mpr close_R
  rw [← hd] at c
  push_cast at c
  rw [abs_sub_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-- `|z − z̃| ≤ 6.3 × 10⁻⁸`. -/
theorem close_z (θ φ : ℝ) : |zS θ φ - torusZ θ φ| ≤ 63 / 10 ^ 9 := by
  set d : ℕ → ℕ → ℤ := fun i j => cB i j - 2 ^ (P - pS) * tB i j with hd
  have e : torusZ θ φ - zS θ φ = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
      (d i j : ℝ) / 2 ^ P * Real.sin (ang i j θ φ) := by
    rw [torusZ, zS, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hd]; push_cast; rw [P_sub_pS]; field_simp
  have h := abs_gridSum_le d (fun i j => Real.sin (ang i j θ φ))
    (fun i j => Real.abs_sin_le_one _) (show (0 : ℝ) < 2 ^ P by positivity)
  rw [← e] at h
  have c := (Nat.cast_le (α := ℝ)).mpr close_Z
  rw [← hd] at c
  push_cast at c
  rw [abs_sub_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-- `|∂_θ R − ∂_θ R̃| ≤ 2.23 × 10⁻⁷`. -/
theorem close_a (θ φ : ℝ) : |aS θ φ - torusRθ θ φ| ≤ 223 / 10 ^ 9 := by
  set d : ℕ → ℕ → ℤ := fun i j => ((i : ℤ) - N) * (cA i j - 2 ^ (P - pS) * tA i j -
    (if i = N ∧ j = M then 2 ^ P else 0)) with hd
  have e : torusRθ θ φ - aS θ φ = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
      (d i j : ℝ) / 2 ^ P * (-Real.sin (ang i j θ φ)) := by
    rw [torusRθ, aS, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hd]
    by_cases hc : i = N ∧ j = M
    · obtain ⟨rfl, rfl⟩ := hc; simp
    · simp only [hc, ↓reduceIte]; push_cast; rw [P_sub_pS]; field_simp; ring
  have h := abs_gridSum_le d (fun i j => -Real.sin (ang i j θ φ))
    (fun i j => by rw [abs_neg]; exact Real.abs_sin_le_one _)
    (show (0 : ℝ) < 2 ^ P by positivity)
  rw [← e] at h
  have c := (Nat.cast_le (α := ℝ)).mpr close_Rθ
  rw [← hd] at c
  push_cast at c
  rw [abs_sub_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-- `|∂_θ z − ∂_θ z̃| ≤ 2.17 × 10⁻⁷`. -/
theorem close_b (θ φ : ℝ) : |bS θ φ - torusZθ θ φ| ≤ 217 / 10 ^ 9 := by
  set d : ℕ → ℕ → ℤ := fun i j => ((i : ℤ) - N) * (cB i j - 2 ^ (P - pS) * tB i j) with hd
  have e : torusZθ θ φ - bS θ φ = ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
      (d i j : ℝ) / 2 ^ P * Real.cos (ang i j θ φ) := by
    rw [torusZθ, bS, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [hd]; push_cast; rw [P_sub_pS]; field_simp
  have h := abs_gridSum_le d (fun i j => Real.cos (ang i j θ φ))
    (fun i j => Real.abs_cos_le_one _) (show (0 : ℝ) < 2 ^ P by positivity)
  rw [← e] at h
  have c := (Nat.cast_le (α := ℝ)).mpr close_Zθ
  rw [← hd] at c
  push_cast at c
  rw [abs_sub_comm]
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]; linarith

/-! ## Compact grid polynomials -/

/-- `∑_{i ≤ 2n₁, j ≤ 2m₁} g i j uⁱ vʲ`. -/
noncomputable def gridPoly1 (g : ℕ → ℕ → ℤ) : P2 :=
  ∑ i ∈ range (2 * n1 + 1), ∑ j ∈ range (2 * m1 + 1), monomial j (monomial i (g i j))

/-- Degree box of a compact grid polynomial. -/
theorem box_gridPoly1 (g : ℕ → ℕ → ℤ) : InBox (gridPoly1 g) (2 * n1) (2 * m1) :=
  InBox.sum _ fun i hi => InBox.sum _ fun j hj =>
    InBox.mono (InBox.monomial i j _) (by simp at hi; omega) (by simp at hj; omega)

/-- `ℓ¹` of a compact grid polynomial. -/
theorem l1_gridPoly1_le (g : ℕ → ℕ → ℤ) : l1 (gridPoly1 g) ≤ gridL1c g := by
  refine (l1_sum_le _ _).trans ?_
  simp only [gridL1c, rsum_eq]
  rw [sum_comm (s := range (2 * m1 + 1))]
  refine sum_le_sum fun i _ => ?_
  refine (l1_sum_le _ _).trans (le_of_eq ?_)
  exact sum_congr rfl fun j _ => by rw [l1_monomial]

/-- `packRow1` as a sum. -/
theorem packRow1_eq (b : ℕ) (f : ℕ → ℤ) (n : ℕ) :
    packRow1 b f n = ∑ i ∈ range n, f i * (2 : ℤ) ^ (b * i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [packRow1, ih, sum_range_succ]; push_cast; rfl

/-- `packGrid1` as a double sum. -/
theorem packGrid1_eq (b W : ℕ) (g : ℕ → ℕ → ℤ) (m : ℕ) :
    packGrid1 b W g m = ∑ j ∈ range m, ∑ i ∈ range (2 * n1 + 1),
      g i j * (2 : ℤ) ^ (b * (i + W * j)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [packGrid1, ih, sum_range_succ, packRow1_eq, sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    push_cast
    rw [mul_assoc, ← pow_add]; ring_nf

/-- Kronecker image of a compact grid polynomial. -/
theorem kron_gridPoly1 (b W : ℕ) (g : ℕ → ℕ → ℤ) :
    kron b W (gridPoly1 g) = packGrid1 b W g (2 * m1 + 1) := by
  rw [gridPoly1, packGrid1_eq, map_sum, sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [map_sum]
  exact sum_congr rfl fun i _ => by rw [kron_monomial]

/-- `t₁ = σ₁ u^{n₁} v^{m₁}`. -/
noncomputable def tP1 : P2 := monomial m1 (monomial n1 (sig1 : ℤ))
/-- `V̂ = 2v`. -/
noncomputable def vP2 : P2 := monomial 1 (monomial 0 2)

/-- Degree box of `t₁`. -/
theorem box_tP1 : InBox tP1 n1 m1 := InBox.monomial _ _ _
/-- Degree box of `2v`. -/
theorem box_vP2 : InBox vP2 0 1 := InBox.monomial _ _ _
/-- `ℓ¹` of `t₁`. -/
theorem l1_tP1 : l1 tP1 ≤ sig1 := by rw [tP1, l1_monomial]; simp
/-- `ℓ¹` of `2v`. -/
theorem l1_vP2 : l1 vP2 ≤ 2 := by rw [vP2, l1_monomial]; simp
/-- Kronecker image of `t₁`. -/
theorem kron_tP1 (b W : ℕ) : kron b W tP1 = tInt b W := by
  rw [tP1, kron_monomial, tInt]; push_cast; ring
/-- Kronecker image of `2v`. -/
theorem kron_vP2 (b W : ℕ) : kron b W vP2 = ((2 * 2 ^ (b * W) : ℕ) : ℤ) := by
  rw [vP2, kron_monomial]; push_cast; ring_nf

/-! ## Evaluation of the compact grid polynomials on the unit torus -/

/-- `w₁ = u^{n₁} v^{m₁}`. -/
def w1 (θ φ : ℝ) : ℂ := uu θ ^ n1 * vv φ ^ m1
/-- The scale `T₁ = σ₁ w₁` of one Fourier factor. -/
def T1 (θ φ : ℝ) : ℂ := (sig1 : ℂ) * w1 θ φ
/-- The scale `V₁ = 2v` of `cos 2φ`, `sin 2φ`. -/
def V1 (φ : ℝ) : ℂ := 2 * vv φ

/-- `σ₁ = 2 · 2^{pS}` in `ℂ`. -/
theorem sig1_eq : (sig1 : ℂ) = 2 * 2 ^ pS := by simp [sig1, pow_succ]; ring

/-- Compact monomials on the unit torus in terms of the big-grid phases. -/
theorem uv_pow1 (i j : ℕ) (θ φ : ℝ) :
    uu θ ^ i * vv φ ^ j =
      w1 θ φ * Complex.exp (ang (i + (N - n1)) (j + (M - m1)) θ φ * Complex.I) := by
  simp only [uu, vv, w1, ← Complex.exp_nat_mul, ← Complex.exp_add, ang]
  congr 1
  simp only [N, M, n1, m1]
  push_cast
  ring

/-- Restricting a sum over `[0, L)` to a window `[a, a + n)` outside which the terms vanish. -/
theorem sum_window1 {β : Type*} [AddCommMonoid β] (L a n : ℕ) (f : ℕ → β) (h : a + n ≤ L)
    (hf : ∀ i, i < L → (i < a ∨ a + n ≤ i) → f i = 0) :
    ∑ i ∈ range L, f i = ∑ k ∈ range n, f (k + a) := by
  have e : ∑ k ∈ range n, f (k + a) = ∑ i ∈ Ico a (a + n), f i := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact sum_congr rfl fun k _ => by rw [add_comm]
  rw [e]
  symm
  refine sum_subset (fun i hi => ?_) (fun i hi hni => ?_)
  · simp only [mem_Ico, mem_range] at hi ⊢; omega
  · simp only [mem_Ico, mem_range, not_and_or, not_le, not_lt] at hi hni
    exact hf i hi (by omega)

/-- The window of the surrogate data in big-grid indices. -/
def inWin (i j : ℕ) : Prop := N - n1 ≤ i ∧ i ≤ N + n1 ∧ M - m1 ≤ j ∧ j ≤ M + m1

/-- Reindexing a big-grid sum supported on the window. -/
theorem sum_window {β : Type*} [AddCommMonoid β] (F : ℕ → ℕ → β)
    (hF : ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → F i j = 0) :
    ∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1), F i j =
      ∑ i ∈ range (2 * n1 + 1), ∑ j ∈ range (2 * m1 + 1), F (i + (N - n1)) (j + (M - m1)) := by
  rw [sum_window1 (2 * N + 1) (N - n1) (2 * n1 + 1) _ (by norm_num [N, n1])]
  · refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    refine sum_window1 (2 * M + 1) (M - m1) (2 * m1 + 1) _ (by norm_num [M, m1]) ?_
    intro j hj hj'
    refine hF _ _ (by simp only [N, n1] at *; omega) hj ?_
    simp only [inWin, N, M, n1, m1] at *; omega
  · intro i hi hi'
    refine sum_eq_zero fun j hj => ?_
    simp only [mem_range] at hj
    refine hF _ _ hi hj ?_
    simp only [inWin, N, M, n1, m1] at *; omega

/-- Evaluation of a compact grid polynomial as a big-grid exponential sum. -/
theorem evalC_gridPoly1_cpt (G : ℕ → ℕ → ℤ)
    (hG : ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → G i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 (cpt G)) = w1 θ φ * ∑ i ∈ range (2 * N + 1),
      ∑ j ∈ range (2 * M + 1), (G i j : ℂ) * Complex.exp (ang i j θ φ * Complex.I) := by
  rw [sum_window (fun i j => (G i j : ℂ) * Complex.exp (ang i j θ φ * Complex.I))
    (fun i j hi hj hw => by simp [hG i j hi hj hw])]
  rw [gridPoly1, map_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_sum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [evalC_monomial, mul_assoc, uv_pow1, cpt]; ring

/-- The half window, where the stored coefficients live. -/
def inHalf (i j : ℕ) : Prop := N ≤ i ∧ i ≤ N + n1 ∧ M - m1 ≤ j ∧ j ≤ M + m1

/-- Window lookups vanish outside the half window. -/
theorem win_zero (l : List ℤ) {i j : ℕ} (h : ¬ inHalf i j) : win l i j = 0 := by
  simp only [inHalf] at h
  unfold win
  split_ifs
  rfl

/-- Support of a reflected half-window grid. -/
theorem refl_support {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) :
    ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j →
      c i j = 0 ∧ c (2 * N - i) (2 * M - j) = 0 := by
  intro i j hi hj hw
  refine ⟨hc _ _ fun h => hw ?_, hc _ _ fun h => hw ?_⟩ <;>
    simp only [inHalf, inWin, N, M, n1, m1] at * <;> omega

/-- Support of a cosine-symmetrized half-window grid. -/
theorem symC_support {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) :
    ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → symC c i j = 0 := by
  intro i j hi hj hw
  obtain ⟨h1, h2⟩ := refl_support hc i j hi hj hw
  simp [symC, h1, h2]

/-- Support of a sine-symmetrized half-window grid. -/
theorem symS_support {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) :
    ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → symS c i j = 0 := by
  intro i j hi hj hw
  obtain ⟨h1, h2⟩ := refl_support hc i j hi hj hw
  simp [symS, h1, h2]

/-- Support of a weighted grid. -/
theorem wsym_support {G : ℕ → ℕ → ℤ}
    (hG : ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → G i j = 0) :
    ∀ i j, i < 2 * N + 1 → j < 2 * M + 1 → ¬ inWin i j → ((i : ℤ) - N) * G i j = 0 := by
  intro i j hi hj hw; rw [hG i j hi hj hw, mul_zero]

/-- The compact weight `i − n₁` is the big-grid weight `i − N`. -/
theorem cpt_weight (G : ℕ → ℕ → ℤ) (i j : ℕ) :
    ((i : ℤ) - n1) * cpt G i j = cpt (fun i j => ((i : ℤ) - N) * G i j) i j := by
  simp only [cpt, N, n1]; push_cast; ring

/-- A cosine series on the half window: `evalC = T₁ · ∑ c/2^p cos`. -/
theorem evalC_cos {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 (cpt (symC c))) = T1 θ φ *
      ((∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        (c i j : ℝ) / 2 ^ pS * Real.cos (ang i j θ φ) : ℝ) : ℂ) := by
  rw [evalC_gridPoly1_cpt _ (symC_support hc), sum_sym (symC c) c (fun _ _ => 1) 1 1
    (by norm_num) (fun i j => by simp only [symC]; ring) (fun _ _ _ _ => by simp)]
  simp only [T1, sig1_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

/-- A sine series: `evalC = i T₁ · ∑ c/2^p sin`. -/
theorem evalC_sin {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 (cpt (symS c))) = Complex.I * T1 θ φ *
      ((∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        (c i j : ℝ) / 2 ^ pS * Real.sin (ang i j θ φ) : ℝ) : ℂ) := by
  rw [evalC_gridPoly1_cpt _ (symS_support hc), sum_sym (symS c) c (fun _ _ => 1) (-1) 1
    (by norm_num) (fun i j => by simp only [symS]; ring) (fun _ _ _ _ => by simp)]
  simp only [T1, sig1_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

/-- The `θ`-derivative of a cosine series: `evalC = −i T₁ · ∂_θ(∑ c/2^p cos)`. -/
theorem evalC_cosθ {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 (cpt (fun i j => ((i : ℤ) - N) * symC c i j))) =
      -Complex.I * T1 θ φ * ((∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        (c i j : ℝ) / 2 ^ pS * (-Real.sin (ang i j θ φ) * ((i : ℝ) - N)) : ℝ) : ℂ) := by
  rw [evalC_gridPoly1_cpt _ (wsym_support (symC_support hc)),
    sum_sym (fun i j => ((i : ℤ) - N) * symC c i j) c (fun i _ => (i : ℤ) - N) 1 (-1)
    (by norm_num) (fun i j => by simp only [symC]; ring) (fun i j hi _ => wtθ_refl hi)]
  simp only [T1, sig1_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

/-- The `θ`-derivative of a sine series: `evalC = T₁ · ∂_θ(∑ c/2^p sin)`. -/
theorem evalC_sinθ {c : ℕ → ℕ → ℤ} (hc : ∀ i j, ¬ inHalf i j → c i j = 0) (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 (cpt (fun i j => ((i : ℤ) - N) * symS c i j))) =
      T1 θ φ * ((∑ i ∈ range (2 * N + 1), ∑ j ∈ range (2 * M + 1),
        (c i j : ℝ) / 2 ^ pS * (Real.cos (ang i j θ φ) * ((i : ℝ) - N)) : ℝ) : ℂ) := by
  rw [evalC_gridPoly1_cpt _ (wsym_support (symS_support hc)),
    sum_sym (fun i j => ((i : ℤ) - N) * symS c i j) c (fun i _ => (i : ℤ) - N) (-1) (-1)
    (by norm_num) (fun i j => by simp only [symS]; ring) (fun i j hi _ => wtθ_refl hi)]
  simp only [T1, sig1_eq, Complex.ofReal_sum, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  mode_close

/-- `tA` vanishes outside the half window. -/
theorem tA_supp : ∀ i j, ¬ inHalf i j → tA i j = 0 := fun _ _ h => win_zero _ h
/-- `tB` vanishes outside the half window. -/
theorem tB_supp : ∀ i j, ¬ inHalf i j → tB i j = 0 := fun _ _ h => win_zero _ h
/-- `tG` vanishes outside the half window. -/
theorem tG_supp : ∀ i j, ¬ inHalf i j → tG i j = 0 := fun _ _ h => win_zero _ h
/-- `tS` vanishes outside the half window. -/
theorem tS_supp : ∀ i j, ¬ inHalf i j → tS i j = 0 := fun _ _ h => win_zero _ h

/-- `gAc` is the restriction of the weighted big grid. -/
theorem gAc_eq : gAc = cpt (fun i j => ((i : ℤ) - N) * symC tA i j) := by
  funext i j; rw [gAc, gRc, cpt_weight]
/-- `gBc` is the restriction of the weighted big grid. -/
theorem gBc_eq : gBc = cpt (fun i j => ((i : ℤ) - N) * symS tB i j) := by
  funext i j; rw [gBc, gZc, cpt_weight]

/-- `r̂ = T₁ r̃` on the unit torus. -/
theorem evalC_rS (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly1 gRc) = T1 θ φ * rS θ φ :=
  evalC_cos tA_supp θ φ
/-- `ẑ = i T₁ z̃` on the unit torus. -/
theorem evalC_zS (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 gZc) = Complex.I * T1 θ φ * zS θ φ :=
  evalC_sin tB_supp θ φ
/-- `â = −i T₁ ∂_θ R̃` on the unit torus. -/
theorem evalC_aS (θ φ : ℝ) :
    evalC (uu θ) (vv φ) (gridPoly1 gAc) = -Complex.I * T1 θ φ * aS θ φ := by
  rw [gAc_eq]; exact evalC_cosθ tA_supp θ φ
/-- `b̂ = T₁ ∂_θ z̃` on the unit torus. -/
theorem evalC_bS (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly1 gBc) = T1 θ φ * bS θ φ := by
  rw [gBc_eq]; exact evalC_sinθ tB_supp θ φ
/-- `ŷ = T₁ g` on the unit torus. -/
theorem evalC_gF (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly1 gYc) = T1 θ φ * gF θ φ :=
  evalC_cos tG_supp θ φ
/-- `ŝ = T₁ s` on the unit torus. -/
theorem evalC_sF (θ φ : ℝ) : evalC (uu θ) (vv φ) (gridPoly1 gSc) = T1 θ φ * sF θ φ :=
  evalC_cos tS_supp θ φ
/-- `t̂ = T₁` on the unit torus. -/
theorem evalC_tP1 (θ φ : ℝ) : evalC (uu θ) (vv φ) tP1 = T1 θ φ := by
  rw [tP1, evalC_monomial, T1, w1]; push_cast; ring
/-- `V̂ = 2v` on the unit torus. -/
theorem evalC_vP2 (θ φ : ℝ) : evalC (uu θ) (vv φ) vP2 = V1 φ := by
  rw [vP2, evalC_monomial, V1]; push_cast; ring

/-! ## The polynomial `Φ̂` and its three readings -/

/-- The base polynomials `r̂, ẑ, Ĉ, Ŝ, t̂, V̂`. -/
noncomputable def baseP : ℕ → P2 := envB (gridPoly1 gRc) (gridPoly1 gZc) SvP ChP tP1 vP2

/-- The top-tree polynomials (atoms first). -/
noncomputable def topP : ℕ → P2 :=
  envT (fun k => Ex.evH WB baseP (atom k)) (gridPoly1 gRc) (gridPoly1 gZc) (gridPoly1 gAc)
    (gridPoly1 gBc) (gridPoly1 gYc) (gridPoly1 gSc) tP1 vP2

/-- `Φ̂ ∈ ℤ[u][v]`, the phased polynomial of `s² F` on the surrogate torus. -/
noncomputable def PhiP : P2 := Ex.evH WT topP phiEx

/-- Kronecker images of the base polynomials. -/
theorem kron_baseP (b W : ℕ) : (fun i => kron b W (baseP i)) = baseInt b W := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact kron_gridPoly1 b W gRc
  · exact kron_gridPoly1 b W gZc
  · exact kron_SvP b W
  · exact kron_ChP b W
  · exact kron_tP1 b W
  · exact kron_vP2 b W
  · exact map_zero _

/-- Kronecker images of the atoms. -/
theorem kron_atom (b W k : ℕ) :
    kron b W (Ex.evH WB baseP (atom k)) = Ex.evH WB (baseInt b W) (atom k) := by
  rw [Ex.evH_map, kron_baseP]

/-- Kronecker images of the top-tree polynomials. -/
theorem kron_topP (b W : ℕ) : (fun i => kron b W (topP i)) = topInt b W := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  any_goals exact kron_atom b W _
  · exact kron_gridPoly1 b W gRc
  · exact kron_gridPoly1 b W gZc
  · exact kron_gridPoly1 b W gAc
  · exact kron_gridPoly1 b W gBc
  · exact kron_gridPoly1 b W gYc
  · exact kron_gridPoly1 b W gSc
  · exact kron_tP1 b W
  · exact kron_vP2 b W
  · exact map_zero _

/-- **Kronecker reading**: `kron Φ̂ = phiInt` (the integer computed in the kernel). -/
theorem kron_PhiP : kron 752 309 PhiP = phiInt 752 309 := by
  rw [PhiP, Ex.evH_map, kron_topP]; rfl

/-- `0` lies in every box. -/
theorem inBox_zero (a b : ℕ) : InBox (0 : P2) a b := ⟨by simp, fun j => by simp⟩

/-- Degree boxes of the base polynomials. -/
theorem box_baseP : ∀ i, InBox (baseP i) (BxB i).1 (BxB i).2
  | 0 => box_gridPoly1 _
  | 1 => box_gridPoly1 _
  | 2 => box_SvP
  | 3 => box_ChP
  | 4 => box_tP1
  | 5 => box_vP2
  | _ + 6 => inBox_zero _ _

/-- Degree boxes of the top-tree polynomials. -/
theorem box_topP : ∀ i, InBox (topP i) (BxT i).1 (BxT i).2
  | 0 => Ex.inBox_evH WB box_baseP _
  | 1 => Ex.inBox_evH WB box_baseP _
  | 2 => Ex.inBox_evH WB box_baseP _
  | 3 => Ex.inBox_evH WB box_baseP _
  | 4 => Ex.inBox_evH WB box_baseP _
  | 5 => Ex.inBox_evH WB box_baseP _
  | 6 => Ex.inBox_evH WB box_baseP _
  | 7 => Ex.inBox_evH WB box_baseP _
  | 8 => Ex.inBox_evH WB box_baseP _
  | 9 => box_gridPoly1 _
  | 10 => box_gridPoly1 _
  | 11 => box_gridPoly1 _
  | 12 => box_gridPoly1 _
  | 13 => box_gridPoly1 _
  | 14 => box_gridPoly1 _
  | 15 => box_tP1
  | 16 => box_vP2
  | _ + 17 => inBox_zero _ _

/-- `ℓ¹ 0 = 0`. -/
theorem l1_zero_le (a : ℕ) : l1 (0 : P2) ≤ a := by simp [l1, liftN]

/-- `ℓ¹` bounds of the base polynomials. -/
theorem l1_baseP : ∀ i, l1 (baseP i) ≤ LB i
  | 0 => l1_gridPoly1_le _
  | 1 => l1_gridPoly1_le _
  | 2 => l1_SvP
  | 3 => l1_ChP
  | 4 => l1_tP1
  | 5 => l1_vP2
  | _ + 6 => l1_zero_le _

/-- `ℓ¹` bounds of the top-tree polynomials. -/
theorem l1_topP : ∀ i, l1 (topP i) ≤ LT i
  | 0 => Ex.l1_evH WB l1_baseP _
  | 1 => Ex.l1_evH WB l1_baseP _
  | 2 => Ex.l1_evH WB l1_baseP _
  | 3 => Ex.l1_evH WB l1_baseP _
  | 4 => Ex.l1_evH WB l1_baseP _
  | 5 => Ex.l1_evH WB l1_baseP _
  | 6 => Ex.l1_evH WB l1_baseP _
  | 7 => Ex.l1_evH WB l1_baseP _
  | 8 => Ex.l1_evH WB l1_baseP _
  | 9 => l1_gridPoly1_le _
  | 10 => l1_gridPoly1_le _
  | 11 => l1_gridPoly1_le _
  | 12 => l1_gridPoly1_le _
  | 13 => l1_gridPoly1_le _
  | 14 => l1_gridPoly1_le _
  | 15 => l1_tP1
  | 16 => l1_vP2
  | _ + 17 => l1_zero_le _

/-- The centre monomial `c0Phi u^{154} v^{113}`. -/
noncomputable def PhiMono : P2 := monomial 113 (monomial 154 (c0Phi : ℤ))

/-- **Exact `ℓ¹` distance of `−Φ̂` to its centre monomial**, by the Kronecker digit sum. -/
theorem l1_PhiP_sub : l1 (-PhiP - PhiMono) = l1Kron 752 17
    (-phiInt 752 309 - (c0Phi : ℤ) * ((pow2F (752 * (154 + 309 * 113)) : ℕ) : ℤ)) := by
  have hk : kron 752 309 (-PhiP - PhiMono) =
      -phiInt 752 309 - (c0Phi : ℤ) * ((pow2F (752 * (154 + 309 * 113)) : ℕ) : ℤ) := by
    rw [map_sub, map_neg, kron_PhiP, PhiMono, kron_monomial, pow2F_eq, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [← hk]
  have hbox : InBox PhiP 308 226 := by
    have := Ex.inBox_evH WT box_topP phiEx
    rwa [box_phiEx] at this
  refine l1_eq_l1Kron (a := 308) (J := 226) (by norm_num)
    ((InBox.neg hbox).sub ((InBox.monomial _ _ _).mono (by norm_num) (by norm_num)))
    (by norm_num) (by norm_num) ?_
  have h1 : l1 PhiP ≤ Ex.majN LT phiEx := Ex.l1_evH WT l1_topP phiEx
  have h2 : l1 PhiMono = c0Phi := by rw [PhiMono, l1_monomial]; rfl
  calc l1 (-PhiP - PhiMono) ≤ l1 (-PhiP) + l1 PhiMono := l1_sub_le _ _
    _ = l1 PhiP + c0Phi := by rw [l1_neg, h2]
    _ < 2 ^ (752 - 1) := lt_of_le_of_lt (Nat.add_le_add_right h1 _) apriori_phi

/-! ## The real assignments -/

/-- Base variables on the surrogate torus. -/
def xBS (θ φ : ℝ) : ℕ → ℝ :=
  envB (rS θ φ) (zS θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)) 1 1

/-- Top-tree variables on the surrogate torus. -/
def xTS (θ φ : ℝ) : ℕ → ℝ :=
  envT (fun k => Ex.eval (xBS θ φ) (atom k)) (rS θ φ) (zS θ φ) (aS θ φ) (bS θ φ) (gF θ φ)
    (sF θ φ) 1 1

/-- Base variables on torus A. -/
def xBA (θ φ : ℝ) : ℕ → ℝ :=
  xB (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ))

/-- Top-tree variables on torus A. -/
def xTA (θ φ : ℝ) : ℕ → ℝ :=
  envT (fun k => aval k (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ)) (Real.sin (2 * φ)))
    (torusR θ φ - 1) (torusZ θ φ) (torusRθ θ φ) (torusZθ θ φ) (gF θ φ) (sF θ φ) 1 1

/-- Base phases are below `4`. -/
theorem WB_ph (i : ℕ) : (WB i).2.2 < 4 := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [WB]

/-- Top-tree phases are below `4`. -/
theorem WT_ph (i : ℕ) : (WT i).2.2 < 4 := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp [WT]

/-- The base polynomials represent the surrogate variables with their weights. -/
theorem evalC_baseP (θ φ : ℝ) (i : ℕ) :
    evalC (uu θ) (vv φ) (baseP i) = Ex.lam (T1 θ φ) (V1 φ) (WB i) * (xBS θ φ i : ℂ) := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_rS]; ring
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_zS]; ring
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_SvP, cos_two_mul_eq, V1]
    push_cast; rw [I_pow3]; ring
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_ChP, sin_two_mul_eq, V1]
    push_cast; ring
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_tP1]; push_cast; ring
  · simp only [baseP, envB, WB, xBS, Ex.lam, evalC_vP2]; push_cast; ring
  · simp only [baseP, envB, WB, xBS, map_zero, Complex.ofReal_zero, mul_zero]

/-- The top-tree polynomials represent the surrogate variables with their weights. -/
theorem evalC_topP (θ φ : ℝ) (i : ℕ) :
    evalC (uu θ) (vv φ) (topP i) = Ex.lam (T1 θ φ) (V1 φ) (WT i) * (xTS θ φ i : ℂ) := by
  have ha : ∀ k, k < 9 → evalC (uu θ) (vv φ) (Ex.evH WB baseP (atom k)) =
      Ex.lam (T1 θ φ) (V1 φ) (WT k) * ((Ex.eval (xBS θ φ) (atom k) : ℝ) : ℂ) := by
    intro k hk
    rw [Ex.evH_map]
    exact Ex.evH_phase WB_ph (T1 θ φ) (V1 φ) (evalC_baseP θ φ) (atom k) (WT k) (wt_atoms k hk)
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i
  any_goals exact ha _ (by norm_num)
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_rS]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_zS]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_aS, I_pow3]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_bS]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_gF]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_sF]; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_tP1]; push_cast; ring
  · simp only [topP, envT, WT, xTS, Ex.lam, evalC_vP2]; push_cast; ring
  · simp only [topP, envT, WT, xTS, map_zero, Complex.ofReal_zero, mul_zero]

/-- **Unit-torus reading**: `Φ̂(e^{iθ}, e^{iψ}) = T₁²² (2v)³ i² · (s² F)(surrogate)`. -/
theorem evalC_PhiP (θ φ : ℝ) :
    evalC (uu θ) (vv φ) PhiP =
      Ex.lam (T1 θ φ) (V1 φ) (22, 3, 2) * ((Ex.eval (xTS θ φ) phiEx : ℝ) : ℂ) := by
  rw [PhiP, Ex.evH_map]
  exact Ex.evH_phase WT_ph (T1 θ φ) (V1 φ) (evalC_topP θ φ) phiEx _ wt_phiEx

/-- **`s² F ≥ 0.9` on the surrogate torus** (the Kronecker certificate). -/
theorem phiS_ge (θ φ : ℝ) : 9 / 10 ≤ Ex.eval (xTS θ φ) phiEx := by
  set f := Ex.eval (xTS θ φ) phiEx
  have hs : (0 : ℝ) < sig1 := by unfold sig1; positivity
  have hκ : (0 : ℝ) < (sig1 : ℝ) ^ 22 * 8 := by positivity
  have hev : evalC (uu θ) (vv φ) (-PhiP) =
      (((sig1 : ℝ) ^ 22 * 8 * f : ℝ) : ℂ) * (uu θ ^ 154 * vv φ ^ 113) := by
    rw [map_neg, evalC_PhiP]
    simp only [Ex.lam, T1, V1, w1, n1, m1, Complex.I_sq]
    push_cast; ring
  have h := le_of_evalC (norm_uu θ) (norm_vv φ) hκ (c0Phi : ℤ) hev
  rw [show (-PhiP - monomial 113 (monomial 154 ((c0Phi : ℕ) : ℤ)) : P2) = -PhiP - PhiMono
    from rfl, l1_PhiP_sub] at h
  have c := (Nat.cast_le (α := ℝ)).mpr check_phi
  push_cast at c h
  refine le_trans ?_ h
  rw [le_div_iff₀ hκ]; linarith

/-! ## From the surrogate to torus A -/

/-- Sup bounds of the base variables on torus A. -/
theorem abs_xBA_le (θ φ : ℝ) (i : ℕ) : |xBA θ φ i| ≤ BB i := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp only [xBA, xB, envB, BB] <;> push_cast
  · exact abs_torusR_sub_one_le θ φ
  · exact abs_torusZ_le θ φ
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _
  all_goals norm_num

/-- Surrogate–torus A distance of the base variables. -/
theorem abs_xBS_sub_le (θ φ : ℝ) (i : ℕ) : |xBS θ φ i - xBA θ φ i| ≤ EB i := by
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp only [xBA, xBS, xB, envB, EB] <;> push_cast
  · exact close_r θ φ
  · exact close_z θ φ
  all_goals norm_num

/-- Sup bounds of the top-tree variables on torus A. -/
theorem abs_xTA_le (θ φ : ℝ) (i : ℕ) : |xTA θ φ i| ≤ BT i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp only [xTA, BT, envT]
  any_goals exact Ex.abs_eval_le (abs_xBA_le θ φ) _
  all_goals push_cast
  · exact abs_torusR_sub_one_le θ φ
  · exact abs_torusZ_le θ φ
  · exact torusRθ_le θ φ
  · exact torusZθ_le θ φ
  · exact abs_gF_le θ φ
  · exact abs_sF_le θ φ
  all_goals norm_num

/-- Surrogate–torus A distance of the top-tree variables. -/
theorem abs_xTS_sub_le (θ φ : ℝ) (i : ℕ) : |xTS θ φ i - xTA θ φ i| ≤ ET i := by
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp only [xTA, xTS, ET, envT]
  any_goals exact Ex.abs_eval_sub_le (abs_xBA_le θ φ) (abs_xBS_sub_le θ φ) _
  all_goals push_cast
  · exact close_r θ φ
  · exact close_z θ φ
  · exact close_a θ φ
  · exact close_b θ φ
  all_goals norm_num

/-- **`s² F ≥ 0.6` on torus A.** -/
theorem phiA_ge (θ φ : ℝ) : 6 / 10 ≤ Ex.eval (xTA θ φ) phiEx := by
  have h1 := phiS_ge θ φ
  have h2 := Ex.abs_eval_sub_le (abs_xTA_le θ φ) (abs_xTS_sub_le θ φ) phiEx
  have h3 := (Rat.cast_le (K := ℝ)).mpr dmaj_phi
  push_cast at h3
  have := abs_sub_abs_le_abs_sub (Ex.eval (xTS θ φ) phiEx) (Ex.eval (xTA θ φ) phiEx)
  rw [abs_le] at h2
  linarith [h2.2]

/-! ## The torsion -/

/-- **The certified expression in terms of the torsion**:
`s² F = 10 s² D_l³ W₀² (T₀ + y − 3/10)` (`t = V = 1`). -/
theorem phi_identity (R z a b C S y s : ℝ) (hA : aval 0 R z C S ≠ 0)
    (hW : a * z - b * (R - 1) ≠ 0) :
    Ex.eval (envT (fun k => aval k R z C S) (R - 1) z a b y s 1 1) phiEx =
      s ^ 2 * (10 * aval 0 R z C S ^ 3 * (a * z - b * (R - 1)) ^ 2 *
        (torsion R z a b C S + y - 3 / 10)) := by
  have hD : Dfun R z C S = aval 0 R z C S / 16 := by rw [aval_Dl]; ring
  simp only [Ex.eval, phiEx, eF, eY, eG, eW0, eR, eT5V, envT]
  simp only [torsion, XR, XZ, dXRR, dXRz, dXZR, dXZz, hD]
  generalize a * z - b * (R - 1) = W at hW ⊢
  field_simp
  push_cast
  ring

/-- `s² F` on torus A. -/
theorem phiA_eq (θ φ : ℝ) :
    Ex.eval (xTA θ φ) phiEx = sF θ φ ^ 2 * (10 * aval 0 (torusR θ φ) (torusZ θ φ)
      (Real.cos (2 * φ)) (Real.sin (2 * φ)) ^ 3 * wind θ φ ^ 2 * (T0 θ φ + gF θ φ - 3 / 10)) := by
  have hA := aval0_torus_pos θ φ
  have hW : torusRθ θ φ * torusZ θ φ - torusZθ θ φ * (torusR θ φ - 1) = -wind θ φ := by
    unfold wind; ring
  have hW0 : torusRθ θ φ * torusZ θ φ - torusZθ θ φ * (torusR θ φ - 1) ≠ 0 := by
    rw [hW]; linarith [wind_pos θ φ]
  rw [xTA, phi_identity _ _ _ _ _ _ _ _ hA.ne' hW0, hW, T0]
  ring

/-- **The shifted torsion is positive at every point of torus A**: `T₀ + g > 3/10`, where `g`
is the explicit zero-mean trigonometric polynomial `gF`. -/
theorem torusA_torsion_shifted (θ φ : ℝ) : 3 / 10 < T0 θ φ + gF θ φ := by
  have h := phiA_ge θ φ
  rw [phiA_eq] at h
  have hA := aval0_torus_pos θ φ
  have hW : 0 < wind θ φ := by linarith [wind_pos θ φ]
  have hK : 0 ≤ sF θ φ ^ 2 * (10 * aval 0 (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ))
      (Real.sin (2 * φ)) ^ 3 * wind θ φ ^ 2) := by positivity
  by_contra hc
  push Not at hc
  have : sF θ φ ^ 2 * (10 * aval 0 (torusR θ φ) (torusZ θ φ) (Real.cos (2 * φ))
      (Real.sin (2 * φ)) ^ 3 * wind θ φ ^ 2 * (T0 θ φ + gF θ φ - 3 / 10)) ≤ 0 := by
    rw [← mul_assoc]
    exact mul_nonpos_of_nonneg_of_nonpos hK (by linarith)
  linarith

end PlasmaLean.Design.KamTorusA.Frame
