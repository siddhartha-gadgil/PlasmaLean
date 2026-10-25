/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCBoxPert
public import PlasmaLean.Theory.KAM.ParamInterp

/-!
# Interpolation of guiding-centre tori in the gyro-length

The energy window of the passing alpha guiding centres is the interval `|ρ − 1/256| ≤ h`,
`h = hEw = 2⁻³²`, of gyro-lengths; we write `ρ = 1/256 + s h` with `s ∈ [−1, 1]`. Four node tori
`K_j` (certified at `s = t_j ∈ {−1, −5/16, 5/16, 1}`) are combined into the **Lagrange family**
`K(s) = ∑_j ℓ_j(s) K_j` (`combEw`), a cubic polynomial in `s` with coefficients
`C_k = ∑_j V⁻¹_{kj} K_j` (`coefEw`, `combEw_eq`), equal to `K_j` at the nodes (`combEw_node`).

**Residual of the family** (`ewRes_interp`). The flow-form residual of `gcFlowMu ρ λ` is affine in
`ρ` (`resR_gcFlowMu_sub`), so `s ↦ resR(1/256 + s h)(K(s))` is `T₀(x(s)) + h s T₁(x(s))` with the
polynomial inputs `x(s) = xK ι K(s)`, i.e. `interpF` of `Theory/KAM/ParamInterp`. With strip bounds
of the coefficients `C_k`, validity of `T₀, T₁` on the complex disc `|s| ≤ R` and the node residuals
`e_j`, `Bd_interp` gives, for every `|s| ≤ 1`,
`‖resR(1/256 + s h)(K(s))‖_r ≤ ∑_j |ℓ_j(s)| e_j + 3 M R⁻⁴/(1 − R⁻¹)`, and `∑_j |ℓ_j(s)| ≤ 2`
(`wEw_leb`; the exact Lebesgue constant is `≈ 1.70`).

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `wEw_node`: the weights are the Lagrange basis at the nodes; `wEw_exact`: they
reproduce cubic polynomials; `combEw_node`: the family passes through the node tori.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex

/-- The half-width of the energy window in the gyro-length, `2⁻³²`. -/
def hEw : ℝ := 1 / 2 ^ 32

/-- The interpolation nodes `t_j` (in units of `hEw`). -/
def tEw : Fin 4 → ℝ := ![-1, -5 / 16, 5 / 16, 1]

/-- The Lagrange weights of the nodes `tEw`. -/
def wEw (s : ℝ) : Fin 4 → ℝ :=
  ![-(s - 1) * (256 * s ^ 2 - 25) / 462, 128 * (s ^ 2 - 1) * (16 * s - 5) / 1155,
  -(128 * (s ^ 2 - 1) * (16 * s + 5)) / 1155, (s + 1) * (256 * s ^ 2 - 25) / 462]

/-- The inverse Vandermonde matrix `V⁻¹_{kj}` of the nodes. -/
def ViEw : Fin 4 → Fin 4 → ℝ := ![![-25 / 462, 128 / 231, 128 / 231, -25 / 462],
  ![25 / 462, -2048 / 1155, 2048 / 1155, -25 / 462],
  ![128 / 231, -128 / 231, -128 / 231, 128 / 231],
  ![-128 / 231, 2048 / 1155, -2048 / 1155, 128 / 231]]

/-- The weights in monomial form. -/
theorem wEw_eq (s : ℝ) (j : Fin 4) : wEw s j = ∑ k : Fin 4, ViEw k j * s ^ k.val := by
  fin_cases j <;> simp [wEw, ViEw, Fin.sum_univ_four] <;> ring

/-- **Sanity**: the weights reproduce the monomials of degree `≤ 3`. -/
theorem wEw_exact (s : ℝ) : ∀ n < 4, ∑ j, wEw s j * tEw j ^ n = s ^ n := by
  intro n hn
  interval_cases n <;> simp [wEw, tEw, Fin.sum_univ_four] <;> ring

/-- **Sanity**: the weights are the Lagrange basis at the nodes. -/
theorem wEw_node (j k : Fin 4) : wEw (tEw j) k = if j = k then 1 else 0 := by
  fin_cases j <;> fin_cases k <;> norm_num [wEw, tEw]

/-- **The Lebesgue bound** `∑_j |ℓ_j(s)| ≤ 2` on `[−1, 1]`. -/
theorem wEw_leb (s : ℝ) (h1 : -1 ≤ s) (h2 : s ≤ 1) : ∑ j, |wEw s j| ≤ 2 := by
  simp only [Fin.sum_univ_four, wEw, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  have p1 : 0 ≤ 1 - s := by linarith
  have p2 : 0 ≤ s + 1 := by linarith
  have e1 : 256 * s ^ 2 - 25 = (16 * s - 5) * (16 * s + 5) := by ring
  have e2 : s ^ 2 - 1 = -((1 - s) * (s + 1)) := by ring
  have hpq : 0 ≤ (1 - s) * (s + 1) := mul_nonneg p1 p2
  rcases le_total s (-5 / 16) with ha | ha
  · have q1 : 0 ≤ -(16 * s - 5) := by linarith
    have q2 : 0 ≤ -(16 * s + 5) := by linarith
    have hqq : 0 ≤ (-(16 * s - 5)) * (-(16 * s + 5)) := mul_nonneg q1 q2
    have h5 : 0 ≤ -5 / 16 - s := by linarith
    rw [abs_of_nonneg (by rw [e1]; nlinarith [mul_nonneg p1 hqq]),
      abs_of_nonneg (by rw [e2]; nlinarith [mul_nonneg hpq q1]),
      abs_of_nonpos (by rw [e2]; nlinarith [mul_nonneg hpq q2]),
      abs_of_nonneg (by rw [e1]; nlinarith [mul_nonneg p2 hqq])]
    nlinarith [mul_nonneg p2 h5, mul_nonneg (mul_nonneg p2 h5) h5, mul_nonneg (mul_nonneg p2 h5) p2,
      sq_nonneg (s + 3 / 5)]
  rcases le_total s (5 / 16) with hb | hb
  · have q1 : 0 ≤ -(16 * s - 5) := by linarith
    have q2 : 0 ≤ 16 * s + 5 := by linarith
    have hqq : 0 ≤ (-(16 * s - 5)) * (16 * s + 5) := mul_nonneg q1 q2
    rw [abs_of_nonpos (by rw [e1]; nlinarith [mul_nonneg p1 hqq]),
      abs_of_nonneg (by rw [e2]; nlinarith [mul_nonneg hpq q1]),
      abs_of_nonneg (by rw [e2]; nlinarith [mul_nonneg hpq q2]),
      abs_of_nonpos (by rw [e1]; nlinarith [mul_nonneg p2 hqq])]
    nlinarith [sq_nonneg s]
  · have q1 : 0 ≤ 16 * s - 5 := by linarith
    have q2 : 0 ≤ 16 * s + 5 := by linarith
    have hqq : 0 ≤ (16 * s - 5) * (16 * s + 5) := mul_nonneg q1 q2
    have h5 : 0 ≤ s - 5 / 16 := by linarith
    rw [abs_of_nonneg (by rw [e1]; nlinarith [mul_nonneg p1 hqq]),
      abs_of_nonpos (by rw [e2]; nlinarith [mul_nonneg hpq q1]),
      abs_of_nonneg (by rw [e2]; nlinarith [mul_nonneg hpq q2]),
      abs_of_nonneg (by rw [e1]; nlinarith [mul_nonneg p2 hqq])]
    nlinarith [mul_nonneg p1 h5, mul_nonneg (mul_nonneg p1 h5) h5, mul_nonneg (mul_nonneg p1 h5) p1,
      sq_nonneg (s - 3 / 5)]

/-- **The Lagrange family** `K(s) = ∑_j ℓ_j(s) K_j` of node values `X_j`. -/
def combEw (X : Fin 4 → FA) (s : ℝ) : FA := ∑ j, ((wEw s j : ℝ) : ℂ) • X j

/-- The monomial coefficients `C_k = ∑_j V⁻¹_{kj} K_j`. -/
def coefEw (X : Fin 4 → FA) (k : Fin 4) : FA := ∑ j, ((ViEw k j : ℝ) : ℂ) • X j

/-- The family in monomial form: `K(s) = ∑_k s^k C_k`. -/
theorem combEw_eq (X : Fin 4 → FA) (s : ℝ) :
    combEw X s = ∑ k : Fin 4, ((s : ℂ) ^ k.val) • coefEw X k := by
  simp only [combEw, coefEw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [wEw_eq]; push_cast
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Sanity**: the family passes through the node values. -/
theorem combEw_node (X : Fin 4 → FA) (j : Fin 4) : combEw X (tEw j) = X j := by
  simp only [combEw, wEw_node]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  simp

/-- The family is analytic if the node values are. -/
theorem ana_combEw {X : Fin 4 → FA} (h : ∀ j, Ana (X j)) (s : ℝ) : Ana (combEw X s) := by
  simp only [combEw, Fin.sum_univ_four]
  exact (((h 0).smul _).add ((h 1).smul _)).add ((h 2).smul _) |>.add ((h 3).smul _)

/-- The coefficients are analytic if the node values are. -/
theorem ana_coefEw {X : Fin 4 → FA} (h : ∀ j, Ana (X j)) (k : Fin 4) : Ana (coefEw X k) := by
  simp only [coefEw, Fin.sum_univ_four]
  exact (((h 0).smul _).add ((h 1).smul _)).add ((h 2).smul _) |>.add ((h 3).smul _)

/-- The family is real if the node values are. -/
theorem isReal_combEw {X : Fin 4 → FA} (h : ∀ j, IsReal (X j)) (s : ℝ) : IsReal (combEw X s) := by
  simp only [combEw, Fin.sum_univ_four]
  exact (((h 0).smul _).add ((h 1).smul _)).add ((h 2).smul _) |>.add ((h 3).smul _)

/-- `dS` commutes with the family (for analytic node values). -/
theorem dS_combEw {X : Fin 4 → FA} (h : ∀ j, Ana (X j)) (a b : ℂ) (s : ℝ) :
    dS a b (combEw X s) = combEw (fun j => dS a b (X j)) s := by
  simp only [combEw, Fin.sum_univ_four]
  rw [dS_add a b (((h 0).smul _).add ((h 1).smul _) |>.add ((h 2).smul _)) ((h 3).smul _),
    dS_add a b (((h 0).smul _).add ((h 1).smul _)) ((h 2).smul _),
    dS_add a b ((h 0).smul _) ((h 1).smul _), dS_smul a b _ (h 0), dS_smul a b _ (h 1),
    dS_smul a b _ (h 2), dS_smul a b _ (h 3)]

/-- `dS` commutes with the coefficients (for analytic node values). -/
theorem dS_coefEw {X : Fin 4 → FA} (h : ∀ j, Ana (X j)) (a b : ℂ) (k : Fin 4) :
    dS a b (coefEw X k) = coefEw (fun j => dS a b (X j)) k := by
  simp only [coefEw, Fin.sum_univ_four]
  rw [dS_add a b (((h 0).smul _).add ((h 1).smul _) |>.add ((h 2).smul _)) ((h 3).smul _),
    dS_add a b (((h 0).smul _).add ((h 1).smul _)) ((h 2).smul _),
    dS_add a b ((h 0).smul _) ((h 1).smul _), dS_smul a b _ (h 0), dS_smul a b _ (h 1),
    dS_smul a b _ (h 2), dS_smul a b _ (h 3)]

/-- The correction expression of the `R`-residual per unit `ρ`: `F Y_D 𝓛u − F Y_R`. -/
def corrR (lm : ℝ) : PolyExprS ℂ (Fin 6) := .sub (.mul (eYDF lm) (.var 4)) (eYRF lm)

/-- The correction expression of the `z`-residual per unit `ρ`: `F Y_D 𝓛z − F Y_z`. -/
def corrZ (lm : ℝ) : PolyExprS ℂ (Fin 6) := .sub (.mul (eYDF lm) (.var 5)) (eYZF lm)

/-- The polynomial inputs: coefficient `k` of `xK ι K(s)`. -/
def inputsEw (U Z : Fin 4 → FA) (k : Fin 4) : Fin 6 → FA :=
  ![coefEw U k, coefEw Z k, if k = 0 then cS else 0, if k = 0 then sS else 0,
    Lt KamTorusA.iota (coefEw U k), Lt KamTorusA.iota (coefEw Z k)]

/-- The inputs sum to `xK ι K(s)`. -/
theorem inputsEw_sum {U Z : Fin 4 → FA} (hU : ∀ j, Ana (U j)) (hZ : ∀ j, Ana (Z j)) (s : ℝ) :
    (fun i => ∑ k : Fin 4, ((s : ℂ) ^ k.val) • inputsEw U Z k i) =
      xK KamTorusA.iota (combEw U s) (combEw Z s) := by
  funext i
  have hLU : Lt KamTorusA.iota (combEw U s) =
      ∑ k : Fin 4, ((s : ℂ) ^ k.val) • Lt KamTorusA.iota (coefEw U k) := by
    rw [Lt, dS_combEw hU, combEw_eq]; simp only [Lt, dS_coefEw hU]
  have hLZ : Lt KamTorusA.iota (combEw Z s) =
      ∑ k : Fin 4, ((s : ℂ) ^ k.val) • Lt KamTorusA.iota (coefEw Z k) := by
    rw [Lt, dS_combEw hZ, combEw_eq]; simp only [Lt, dS_coefEw hZ]
  fin_cases i
  · simp [inputsEw, xK, combEw_eq]
  · simp [inputsEw, xK, combEw_eq]
  · simp [inputsEw, xK]
  · simp [inputsEw, xK]
  · simp [inputsEw, xK, hLU]
  · simp [inputsEw, xK, hLZ]

/-- The `R`-residual of the family is `interpF` of its inputs. -/
theorem resR_combEw {U Z : Fin 4 → FA} (hU : ∀ j, Ana (U j)) (hZ : ∀ j, Ana (Z j)) (lm s : ℝ) :
    (gcFlowMu (1 / 256 + s * hEw) lm).resR KamTorusA.iota (combEw U s) (combEw Z s) =
      interpF (inputsEw U Z) (gcFlowMu (1 / 256) lm).resRp (corrR lm) hEw s := by
  have h := resR_gcFlowMu_sub (1 / 256 + s * hEw) lm KamTorusA.iota (combEw U s) (combEw Z s)
  have hn : NoWS (eYDF lm) ∧ NoWS (eYRF lm) :=
    ⟨(gcMu_noW 0 lm).1.2.2, (gcMu_noW 0 lm).2.1.2.2⟩
  rw [interpF, inputsEw_sum hU hZ]
  rw [sub_eq_iff_eq_add] at h
  rw [h, FlowFieldS.resR, add_comm]
  congr 1
  simp only [corrR, PolyExprS.eval, eval_xK_xB_S _ _ _ hn.1, eval_xK_xB_S _ _ _ hn.2, dA,
    Algebra.smul_def]
  simp [xK]
  ring_nf

/-- The `z`-residual of the family is `interpF` of its inputs. -/
theorem resZ_combEw {U Z : Fin 4 → FA} (hU : ∀ j, Ana (U j)) (hZ : ∀ j, Ana (Z j)) (lm s : ℝ) :
    (gcFlowMu (1 / 256 + s * hEw) lm).resZ KamTorusA.iota (combEw U s) (combEw Z s) =
      interpF (inputsEw U Z) (gcFlowMu (1 / 256) lm).resZp (corrZ lm) hEw s := by
  have h := resZ_gcFlowMu_sub (1 / 256 + s * hEw) lm KamTorusA.iota (combEw U s) (combEw Z s)
  have hn : NoWS (eYDF lm) ∧ NoWS (eYZF lm) :=
    ⟨(gcMu_noW 0 lm).1.2.2, (gcMu_noW 0 lm).2.2.2.2⟩
  rw [interpF, inputsEw_sum hU hZ]
  rw [sub_eq_iff_eq_add] at h
  rw [h, FlowFieldS.resZ, add_comm]
  congr 1
  simp only [corrZ, PolyExprS.eval, eval_xK_xB_S _ _ _ hn.1, eval_xK_xB_S _ _ _ hn.2, dA,
    Algebra.smul_def]
  simp [xK]
  ring_nf

end PlasmaLean.Design.RationalStellaratorGC
