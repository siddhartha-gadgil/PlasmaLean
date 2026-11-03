/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCQS
public import PlasmaLean.Theory.KAM.CauchyTwoVar

/-!
# The certified QA defect of the C1 torus by the `L²(J)` route (N-34, D7, strong tier)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamCQSL2` after its on-demand dependencies
(`Design/DommaschkKamCQS` and its closure; build stale dependencies one at a time). Axioms are
checked in `scripts/check_axioms_heavy.lean`. Research note `notes/theory/dommaschk-qs-defect.md`.

**The torus average is the strip average** (`torusAvg_eval_psi`, `integral_box_eval_psi`): for
every `x` of the strip algebra `𝔸 = ℓ¹(ℤ²)`, the mean of `F_x(θ, ψ(φ))`, `ψ = 2φ − π/2`, over the
two-field-period box `[0, 2π] × [0, π]` of the Boozer chart is the constant Fourier coefficient
`avg x = x₀₀`: Fubini, the substitution `ψ = 2φ − π/2` (`dψ = 2 dφ`, `[0, π] ↦ [−π/2, 3π/2]`),
`2π`-periodicity in `ψ`, and `avg_eq_integral`.

**The pointwise identity** (`ExactTorusC.four_mul_sqJ_eq`): on the exact torus, with
`g = torusQADefect = N_g/(2Q√Q R⁹)`, `J = boozerJac = Q/(R⁸D)`, the D4/D5 integrand
`F = (q_G N_g)² R⁸ q_D` (`qsFX`) and the values `a = q_G`, `b = q_D` of the approximate inverses,
`F = 4 g² J · (a Q R¹⁷)² (b D)`. With `|a Q R¹⁷ − 1| ≤ ε_G`, `|b D − 1| ≤ ε_D` (from `heG`, `heD`),
`Re((a Q R¹⁷)²(b D)) ≥ c_L = 2 − (1 + ε_G)²(1 + ε_D) > 0` (`re_sq_mul_ge`), hence
`4 c_L g² J ≤ Re F` pointwise (`ExactTorusC.sqJ_le`) and, averaging,
**`⟨g² J⟩ ≤ |⟨F⟩|/(4 c_L) ≤ m_F/(4 c_L) ≤ δ₂²`** (`ExactTorusC.weightedL2Sq_le_mF`,
`l2_numbers`; `δ₂ = 0.002244`). (`c_L` is slightly below `(1 − ε_G)²(1 − ε_D)` of `qsd_numbers`;
it does not assume that the approximate inverses are real.)

**Main results.**
* `dommaschk_C1_oracleDefect_L2`: the exact Dommaschk field has a certified invariant torus with
  rotational transform `ι_C` on which, for every finite set of half-lattice off-QA modes, the
  oracle-normalised Boozer defect is `≤ (√2/2) δ₂/B_min`;
* `oracleDefect_L2_num`: `(√2/2) δ₂/B_min < 0.0016`, `≤ (1/100)(6/25)` (strong tier of Q-16,
  `|ι| ≥ 6/25`) and `≤ 0.0063 |ι_C|` (`abs_dkIotaC_ge`).

Scope as in `Design/DommaschkKamCQS`: one thin certified torus; no C2 statement (audit AC-1).

**Sanity.** `torusAvg_eval_psi_one` (degenerate: the constant `1`), `re_sq_mul_ge_one`
(concrete: `α = β = 1`), `l2_numbers` (accepted fixture), `not_l2_tiny` (rejected: the
certified `δ₂` does not prove `⟨g² J⟩ ≤ 10⁻⁶`, consistent with the sharp value `2.1e-3`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
  MeasureTheory
open PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Design.KamTorusA (psi)

/-! ## The torus average is the strip average -/

/-- `(θ, φ) ↦ F_x(θ, ψ(φ))` is continuous. -/
theorem continuous_eval_psi (x : FA) : Continuous fun p : ℝ × ℝ => eval x p.1 (psi p.2) :=
  (CauchyTwoVar.continuous_eval x).comp (f := fun p : ℝ × ℝ => (p.1, psi p.2))
    (continuous_fst.prodMk ((continuous_const.mul continuous_snd).sub continuous_const))

/-- **The box integral of a strip element** (two field periods): `∫∫_{[0,2π]×[0,π]} F_x(θ, ψ(φ))
dθ dφ = 2π² · avg x`. -/
theorem integral_box_eval_psi (x : FA) :
    ∫ p in torusBox 2, eval x p.1 (psi p.2) = ((2 * Real.pi ^ 2 : ℝ) : ℂ) * avg x := by
  have hc := continuous_eval_psi x
  set G : ℝ → ℂ := fun ψ => ∫ θ in (0 : ℝ)..(2 * Real.pi), eval x θ ψ with hG
  have hGp : Function.Periodic G (2 * Real.pi) := fun ψ => by
    simp only [hG, eval_periodic_ψ]
  rw [torusBox, perPhi_two, Measure.volume_eq_prod, ← setIntegral_prod_swap,
    setIntegral_prod (fun z : ℝ × ℝ => eval x z.swap.1 (psi z.swap.2))
      ((hc.comp continuous_swap).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc))]
  have e1 : ∀ φ : ℝ, ∫ θ in Set.Icc 0 (2 * Real.pi), eval x (φ, θ).swap.1 (psi (φ, θ).swap.2)
      = G (psi φ) := fun φ => by
    simp only [Prod.swap_prod_mk, hG]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp_rw [e1]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  have e2 : ∫ φ in (0 : ℝ)..Real.pi, G (psi φ) =
      (2 : ℝ)⁻¹ • ∫ ψ in (2 * 0 - Real.pi / 2)..(2 * Real.pi - Real.pi / 2), G ψ :=
    intervalIntegral.integral_comp_mul_sub (f := G) two_ne_zero _
  have e3 : ∫ ψ in (2 * 0 - Real.pi / 2)..(2 * Real.pi - Real.pi / 2), G ψ =
      ∫ ψ in (0 : ℝ)..(2 * Real.pi), G ψ := by
    have := hGp.intervalIntegral_add_eq (2 * 0 - Real.pi / 2) 0
    rw [show 2 * 0 - Real.pi / 2 + 2 * Real.pi = 2 * Real.pi - Real.pi / 2 by ring,
      zero_add] at this
    exact this
  rw [e2, e3, avg_eq_integral x]
  have hp : ((4 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (4 * Real.pi ^ 2) ≠ 0)
  rw [Complex.real_smul]
  field_simp
  push_cast
  ring

/-- `torusArea 2 = 2π²`. -/
theorem torusArea_two : torusArea 2 = 2 * Real.pi ^ 2 := by
  rw [torusArea, perPhi_two]; ring

/-- **The torus average is the strip average** (two field periods): the mean of
`F_x(θ, ψ(φ))`, `ψ = 2φ − π/2`, over the Boozer-chart box `[0, 2π] × [0, π]` is
`avg x = x₀₀`. -/
theorem torusAvg_eval_psi (x : FA) : torusAvg 2 (fun p => eval x p.1 (psi p.2)) = avg x := by
  have hp : ((2 * Real.pi ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi ^ 2) ≠ 0)
  rw [torusAvg, integral_box_eval_psi, torusArea_two, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- Sanity (degenerate): the constant `1` has torus average `1`. -/
theorem torusAvg_eval_psi_one : torusAvg 2 (fun p => eval (1 : FA) p.1 (psi p.2)) = 1 := by
  rw [torusAvg_eval_psi, avg_one]

/-! ## Approximate inverses -/

/-- `|α²β − 1| ≤ (1 + e)²(1 + e') − 1` if `|α − 1| ≤ e`, `|β − 1| ≤ e'`. -/
theorem norm_sq_mul_sub_one_le {α β : ℂ} {e e' : ℝ} (hα : ‖α - 1‖ ≤ e) (hβ : ‖β - 1‖ ≤ e') :
    ‖α ^ 2 * β - 1‖ ≤ (1 + e) ^ 2 * (1 + e') - 1 := by
  have he : 0 ≤ e := (norm_nonneg _).trans hα
  have h1 : ‖α + 1‖ ≤ 2 + e := by
    calc ‖α + 1‖ = ‖(α - 1) + 2‖ := by ring_nf
      _ ≤ ‖α - 1‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 + e := by rw [Complex.norm_ofNat]; linarith
  have h2 : ‖β‖ ≤ 1 + e' := by
    calc ‖β‖ = ‖(β - 1) + 1‖ := by ring_nf
      _ ≤ ‖β - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 + e' := by rw [norm_one]; linarith
  rw [show α ^ 2 * β - 1 = (α - 1) * (α + 1) * β + (β - 1) by ring]
  calc ‖(α - 1) * (α + 1) * β + (β - 1)‖ ≤ ‖α - 1‖ * ‖α + 1‖ * ‖β‖ + ‖β - 1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ e * (2 + e) * (1 + e') + e' := by gcongr
    _ = (1 + e) ^ 2 * (1 + e') - 1 := by ring

/-- `Re(α²β) ≥ 2 − (1 + e)²(1 + e')` if `|α − 1| ≤ e`, `|β − 1| ≤ e'`. -/
theorem re_sq_mul_ge {α β : ℂ} {e e' : ℝ} (hα : ‖α - 1‖ ≤ e) (hβ : ‖β - 1‖ ≤ e') :
    2 - (1 + e) ^ 2 * (1 + e') ≤ (α ^ 2 * β).re := by
  have h := norm_sq_mul_sub_one_le hα hβ
  have h2 := Complex.abs_re_le_norm (α ^ 2 * β - 1)
  rw [Complex.sub_re, Complex.one_re] at h2
  linarith [(abs_le.1 h2).1]

/-- Sanity (concrete): `α = β = 1`, `e = e' = 0` gives `Re 1 ≥ 1`. -/
theorem re_sq_mul_ge_one : 2 - (1 + 0) ^ 2 * (1 + 0) ≤ ((1 : ℂ) ^ 2 * 1).re :=
  re_sq_mul_ge (by simp) (by simp)

/-! ## The certified constants of the `L²` route -/

/-- `c_L = 2 − (1 + ε_G)²(1 + ε_D)`: the lower bound of `Re((q_G Q R¹⁷)²(q_D D))`. -/
def cLq : ℚ := 2 - (1 + epsGq) ^ 2 * (1 + epsDq)

/-- **The certified numbers of the `L²` route**: `c_L > 0`, `m_F/(4 c_L) ≤ δ₂²`, and the
oracle-normalised bound `(√2/2) δ₂/B_min < 0.0016` with `√2/2 ≤ 0.70715`. -/
theorem l2_numbers :
    0 < cLq ∧ mFq / (4 * cLq) ≤ delta2q ^ 2 ∧ 14143 / 20000 * delta2q / Bminq < 16 / 10000 ∧
      14143 / 20000 * delta2q / Bminq ≤ 1 / 100 * (6 / 25) ∧
      14143 / 20000 * delta2q / Bminq ≤ 63 / 10000 * ((85 + 2236 / 1000) / 361) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [cLq, epsGq, epsDq, mFq, delta2q, Bminq]

/-- **Sanity (rejected fixture)**: the certified bound does not give `⟨g² J⟩ ≤ 10⁻⁶`. -/
theorem not_l2_tiny : ¬ mFq / (4 * cLq) ≤ 1 / 10 ^ 6 := by
  norm_num [cLq, epsGq, epsDq, mFq]

/-- The integrand `F = (q_G N_g)² R⁸ q_D` of `QSDefBounds.hF`. -/
def qsFX (u z : FA) : FA :=
  (qGs * qsNg (lvS u z) iotaF (dTh u) (dTh z)) ^ 2 * (lvS u z 12 ^ 8 * qDs)

/-! ## The pointwise identity and the `L²(J)` bound on the exact torus -/

/-- The field `B = ∇φ + Σ a_k ∇V_k` of the Dommaschk target (local notation). -/
local notation "Bdk" => DommaschkQA2R.field DommaschkQA2R.candidate

/-- The potential `V = Σ a_k V_k` of the Dommaschk target (local notation). -/
local notation "Vdk" => DommaschkQA2R.potential DommaschkQA2R.candidate

/-- The rotational transform `ι_C = −(85 + √5)/361` of torus C (local notation). -/
local notation "ιC" => DommaschkKamDio.dkIotaC

/-- **The algebraic identity** behind the `L²` route (real `n, Q, R, D`, complex `a, b`):
`(a n)²(R⁸ b) = 4 g² J · (a Q R¹⁷)²(b D)` with `g = n/(2Q√Q R⁹)`, `J = Q/(R⁸D)`. -/
theorem four_mul_sqJ_eq_aux {n Q r d : ℝ} (a b : ℂ) (hQ : 0 < Q) (hr : 0 < r) (hd : d ≠ 0) :
    (a * (n : ℂ)) ^ 2 * ((r : ℂ) ^ 8 * b) =
      4 * (((n / (2 * Q * Real.sqrt Q * r ^ 9)) ^ 2 * (Q / (r ^ 8 * d)) : ℝ) : ℂ) *
        ((a * ((Q * r ^ 17 : ℝ) : ℂ)) ^ 2 * (b * (d : ℂ))) := by
  have hs : (n / (2 * Q * Real.sqrt Q * r ^ 9)) ^ 2 * (Q / (r ^ 8 * d)) =
      n ^ 2 / (4 * Q ^ 2 * r ^ 26 * d) := by
    have hs0 : 0 < Real.sqrt Q := Real.sqrt_pos.2 hQ
    rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hQ.le]
    field_simp
    ring
  rw [hs]
  have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  push_cast
  field_simp

namespace ExactTorusC

variable {u z : FA} (h : ExactTorusC u z)
include h

/-- The value of `F` at a torus point in terms of the real leaves and the approximate inverses. -/
theorem eval_qsFX (θ φ : ℝ) :
    eval (qsFX u z) θ (psi φ) =
      (eval qGs θ (psi φ) * (ngC u z θ φ : ℂ)) ^ 2 *
        (((lvC u z θ φ 12 : ℝ) : ℂ) ^ 8 * eval qDs θ (psi φ)) := by
  rw [qsFX, eval_mul, eval_pow', eval_mul, eval_mul, eval_pow', lvS_eq_lvI,
    show iotaF = algebraMap ℂ FA (ιC : ℂ) from rfl, h.eval_Ng, h.eval_leaf 12]

/-- `|q_G Q R¹⁷ − 1| ≤ ε_G` at every torus point. -/
theorem norm_qG_sub_le (θ φ : ℝ) :
    ‖eval qGs θ (psi φ) * ((qsQ (lvC u z θ φ) * lvC u z θ φ 12 ^ 17 : ℝ) : ℂ) - 1‖ ≤
      (epsGq : ℝ) := by
  have h1 := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.qsDefBounds.heG θ (psi φ)
  rw [eval_sub', eval_mul, eval_one, eval_mul, lvS_eq_lvI, h.eval_Q, eval_pow',
    h.eval_leaf 12] at h1
  push_cast
  exact h1

/-- `|q_D D − 1| ≤ ε_D` at every torus point. -/
theorem norm_qD_sub_le (θ φ : ℝ) :
    ‖eval qDs θ (psi φ) * ((lvC u z θ φ 0 : ℝ) : ℂ) - 1‖ ≤ (epsDq : ℝ) := by
  have h1 := AnalyticComposition.norm_eval_le_of_Bd le_rfl h.qsDefBounds.heD θ (psi φ)
  rw [eval_sub', eval_mul, eval_one, lvS_eq_lvI, h.eval_leaf 0] at h1
  exact h1

/-- **The pointwise identity** `F = 4 g² J · (q_G Q R¹⁷)²(q_D D)` on the exact torus
(`g = N_g/(2Q√Q R⁹) = torusQADefect`, `J = Q/(R⁸D) = boozerJac`). -/
theorem four_mul_sqJ_eq (θ φ : ℝ) :
    eval (qsFX u z) θ (psi φ) =
      4 * ((qsDefC u z θ φ ^ 2 *
          (qsQ (lvC u z θ φ) / (lvC u z θ φ 12 ^ 8 * lvC u z θ φ 0)) : ℝ) : ℂ) *
        ((eval qGs θ (psi φ) * ((qsQ (lvC u z θ φ) * lvC u z θ φ 12 ^ 17 : ℝ) : ℂ)) ^ 2 *
          (eval qDs θ (psi φ) * ((lvC u z θ φ 0 : ℝ) : ℂ))) := by
  rw [h.eval_qsFX, qsDefC]
  exact four_mul_sqJ_eq_aux _ _ (h.Q_pos θ φ) (h.lvC_R_pos θ φ) (h.lvC_D_ne θ φ)

/-- **The pointwise `L²(J)` bound**: `4 c_L g² J ≤ Re F` on the exact torus. -/
theorem sqJ_le (θ φ : ℝ) :
    4 * (cLq : ℝ) * (qsDefC u z θ φ ^ 2 *
        (qsQ (lvC u z θ φ) / (lvC u z θ φ 12 ^ 8 * lvC u z θ φ 0))) ≤
      (eval (qsFX u z) θ (psi φ)).re := by
  have hre := re_sq_mul_ge (h.norm_qG_sub_le θ φ) (h.norm_qD_sub_le θ φ)
  have hc : ((cLq : ℚ) : ℝ) = 2 - (1 + (epsGq : ℝ)) ^ 2 * (1 + (epsDq : ℝ)) := by
    rw [cLq]; push_cast; ring
  have hJ : 0 ≤ qsDefC u z θ φ ^ 2 *
      (qsQ (lvC u z θ φ) / (lvC u z θ φ 12 ^ 8 * lvC u z θ φ 0)) := by
    have := h.Q_pos θ φ
    have := h.lvC_R_pos θ φ
    have := h.D_pos θ φ
    positivity
  rw [h.four_mul_sqJ_eq, show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, hc]
  have := mul_le_mul_of_nonneg_left hre hJ
  nlinarith

/-- The chart quantities on the exact torus: `chartDefect = qsDefC`, `chartJac = Q/(R⁸D)`. -/
theorem chart_eq (p : ℝ × ℝ) :
    chartDefect ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (torusModB Bdk (cylTorus (RofC u) (Zof z))) p = qsDefC u z p.1 p.2 ∧
      chartJac ιC (torusPot Vdk (cylTorus (RofC u) (Zof z))) p =
        qsQ (lvC u z p.1 p.2) / (lvC u z p.1 p.2 12 ^ 8 * lvC u z p.1 p.2 0) := by
  have H := h.boozerChartHyp'
  obtain ⟨e1, e2⟩ := boozerJac_eq_chartJac_and_torusQADefect_eq h.vacuumPotentialOn
    h.fieldTorus.R_pos (fun θ φ => (h.hasDerivAt_torus_θ θ φ).differentiableAt)
    h.fieldTorus.differentiableAt_line (H.v_smooth.differentiable (by norm_num))
    (H.f_smooth.differentiable one_ne_zero) p.1 p.2
  exact ⟨by rw [← e2, h.torusQADefect_eq], by rw [← e1, h.boozerJac_eq]⟩

/-- **The certified `L²(J)` mean square of the QA defect on the exact torus**:
`⟨g² J⟩ ≤ m_F/(4 c_L)` (`g = ∂_{φ_B}|B|`, the average over the Boozer-chart box). -/
theorem weightedL2Sq_le_mF :
    weightedL2Sq 2 ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (chartDefect ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
          (torusModB Bdk (cylTorus (RofC u) (Zof z)))) ≤ (mFq : ℝ) / (4 * cLq) := by
  have H := h.boozerChartHyp'
  have hcL : (0 : ℝ) < cLq := by exact_mod_cast l2_numbers.1
  have hA : (0 : ℝ) < 2 * Real.pi ^ 2 := by have := Real.pi_pos; positivity
  have hJc := continuous_chartJac (ι := ιC) H.v_smooth
  have hgc := H.continuous_chartDefect
  have hFc : Continuous fun p : ℝ × ℝ => eval (qsFX u z) p.1 (psi p.2) := continuous_eval_psi _
  have hmono : ∫ p in torusBox 2, chartDefect ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (torusModB Bdk (cylTorus (RofC u) (Zof z))) p ^ 2 *
          chartJac ιC (torusPot Vdk (cylTorus (RofC u) (Zof z))) p ≤
      ∫ p in torusBox 2, (4 * (cLq : ℝ))⁻¹ * (eval (qsFX u z) p.1 (psi p.2)).re := by
    refine setIntegral_mono_on (integrableOn_torusBox (by fun_prop))
      (integrableOn_torusBox (by fun_prop)) (measurableSet_torusBox 2) fun p _ => ?_
    rw [(h.chart_eq p).1, (h.chart_eq p).2, le_inv_mul_iff₀ (by positivity)]
    exact h.sqJ_le p.1 p.2
  have hre : ∫ p in torusBox 2, (eval (qsFX u z) p.1 (psi p.2)).re =
      (∫ p in torusBox 2, eval (qsFX u z) p.1 (psi p.2)).re :=
    Complex.reCLM.integral_comp_comm (integrableOn_torusBox hFc)
  rw [integral_const_mul, hre, integral_box_eval_psi, Complex.re_ofReal_mul] at hmono
  have hF : (avg (qsFX u z)).re ≤ (mFq : ℝ) :=
    (Complex.re_le_norm _).trans h.qsDefBounds.hF
  unfold weightedL2Sq
  rw [torusArea_two, inv_mul_le_iff₀ hA]
  calc _ ≤ (4 * (cLq : ℝ))⁻¹ * (2 * Real.pi ^ 2 * (avg (qsFX u z)).re) := hmono
    _ ≤ (4 * (cLq : ℝ))⁻¹ * (2 * Real.pi ^ 2 * (mFq : ℝ)) := by gcongr
    _ = 2 * Real.pi ^ 2 * ((mFq : ℝ) / (4 * cLq)) := by ring

/-- `√⟨g² J⟩ ≤ δ₂ = 0.002244` on the exact torus. -/
theorem sqrt_weightedL2Sq_le :
    Real.sqrt (weightedL2Sq 2 ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (chartDefect ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
          (torusModB Bdk (cylTorus (RofC u) (Zof z))))) ≤ (delta2q : ℝ) := by
  have hn : ((mFq / (4 * cLq) : ℚ) : ℝ) ≤ ((delta2q ^ 2 : ℚ) : ℝ) :=
    Rat.cast_le.mpr l2_numbers.2.1
  push_cast at hn
  have hd : (0 : ℝ) ≤ delta2q := by exact_mod_cast (show (0 : ℚ) ≤ delta2q by norm_num [delta2q])
  rw [Real.sqrt_le_left hd]
  exact h.weightedL2Sq_le_mF.trans hn

/-- **The oracle-normalised Boozer defect of the exact torus, `L²` route**: for every finite set
`S` of half-lattice off-QA modes, `defect ≤ (√2/2) δ₂/B_min`. -/
theorem oracleDefect_le_L2 (S : Finset (ℤ × ℤ)) (hS : ∀ q ∈ S, OracleOffQA q) :
    oracleDefect 2 ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (torusModB Bdk (cylTorus (RofC u) (Zof z))) S ≤
      Real.sqrt 2 / 2 * delta2q / Bminq := by
  have H := h.boozerChartHyp'
  have hb : (0 : ℝ) < Bminq := by exact_mod_cast (show (0 : ℚ) < Bminq by norm_num [Bminq])
  have hB00 := H.le_boozerB00 (Bmin := Bminq) fun p => h.Bmin_le p.1 p.2
  have h1 := H.sqrt_sum_oracle_le S hS
  have h2 : Real.sqrt 2 / (2 : ℕ) *
      Real.sqrt (weightedL2Sq 2 ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
        (chartDefect ιC (torusPot Vdk (cylTorus (RofC u) (Zof z)))
          (torusModB Bdk (cylTorus (RofC u) (Zof z))))) ≤ Real.sqrt 2 / 2 * delta2q := by
    push_cast
    exact mul_le_mul_of_nonneg_left h.sqrt_weightedL2Sq_le (by positivity)
  unfold oracleDefect
  calc _ ≤ Real.sqrt 2 / 2 * delta2q / boozerB00 2 ιC
        (torusPot Vdk (cylTorus (RofC u) (Zof z))) (torusModB Bdk (cylTorus (RofC u) (Zof z))) :=
        div_le_div_of_nonneg_right (h1.trans h2) (hb.trans_le hB00).le
    _ ≤ _ := div_le_div_of_nonneg_left (by
        have : (0 : ℝ) ≤ delta2q := by
          exact_mod_cast (show (0 : ℚ) ≤ delta2q by norm_num [delta2q])
        positivity) hb hB00

end ExactTorusC

/-! ## The unconditional statement and its numbers -/

/-- **Oracle-normalised off-QA Boozer spectral defect on the C1 torus, `L²` route** (N-34 D7,
strong tier): the exact Dommaschk vacuum field has an invariant torus `cylTorus R Z` with
rotational transform `ι_C`, and for every finite set `S` of half-lattice off-QA modes
(`OracleOffQA`), `oracleDefect ≤ (√2/2) δ₂/B_min` with the certified `δ₂ = delta2q = 0.002244`
and `B_min = Bminq = 1.04259`. -/
theorem dommaschk_C1_oracleDefect_L2 :
    ∃ R Z : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R Z DommaschkKamDio.dkIotaC ∧
      ∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 DommaschkKamDio.dkIotaC
          (torusPot (DommaschkQA2R.potential DommaschkQA2R.candidate) (cylTorus R Z))
          (torusModB (DommaschkQA2R.field DommaschkQA2R.candidate) (cylTorus R Z)) S ≤
          Real.sqrt 2 / 2 * delta2q / Bminq := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ :=
    dk_exact_of_res (Bd_weaken dk_e0R e0q_le_budget) (Bd_weaken dk_e0Z e0q_le_budget)
  have h : ExactTorusC u z := ⟨hu, hz, hur, hzr, hR, hZ, hC⟩
  exact ⟨_, _, h.iotaOnTorus, fun S hS => h.oracleDefect_le_L2 S hS⟩

/-- `|ι_C| = (85 + √5)/361 ≥ (85 + 2.236)/361 ≥ 6/25`. -/
theorem abs_dkIotaC_ge :
    (85 + 2236 / 1000) / 361 ≤ |DommaschkKamDio.dkIotaC| ∧
      (6 / 25 : ℝ) ≤ |DommaschkKamDio.dkIotaC| := by
  have h5 : (2236 / 1000 : ℝ) ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : 0 ≤ (85 + Real.sqrt 5) / 361 := by positivity
  rw [DommaschkKamDio.dkIotaC, abs_neg, abs_of_nonneg hpos]
  constructor <;> linarith

/-- **The certified strong-tier number**: `(√2/2) δ₂/B_min < 0.0016`, `≤ (1/100)(6/25)` (the
strong tier `≤ 0.01 |ι|` of Q-16, since `|ι_C| ≥ 6/25`) and `≤ 0.0063 |ι_C|`. -/
theorem oracleDefect_L2_num :
    Real.sqrt 2 / 2 * delta2q / Bminq < (16 : ℝ) / 10000 ∧
      Real.sqrt 2 / 2 * delta2q / Bminq ≤ (1 / 100 : ℝ) * (6 / 25) ∧
      Real.sqrt 2 / 2 * delta2q / Bminq ≤ (63 / 10000 : ℝ) * |DommaschkKamDio.dkIotaC| := by
  have h2 : Real.sqrt 2 < 14143 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hB : (0 : ℝ) < Bminq := by norm_num [Bminq]
  have hd : (0 : ℝ) < delta2q := by norm_num [delta2q]
  have hle : Real.sqrt 2 / 2 * delta2q / Bminq ≤ 14143 / 20000 * delta2q / Bminq := by
    have h2' : Real.sqrt 2 / 2 ≤ 14143 / 20000 := by linarith
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hd.le) hB.le
  have n := l2_numbers
  have n3 : ((14143 / 20000 * delta2q / Bminq : ℚ) : ℝ) < ((16 / 10000 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr n.2.2.1
  have n4 : ((14143 / 20000 * delta2q / Bminq : ℚ) : ℝ) ≤ ((1 / 100 * (6 / 25) : ℚ) : ℝ) :=
    Rat.cast_le.mpr n.2.2.2.1
  have n5 : ((14143 / 20000 * delta2q / Bminq : ℚ) : ℝ) ≤
      ((63 / 10000 * ((85 + 2236 / 1000) / 361) : ℚ) : ℝ) :=
    Rat.cast_le.mpr n.2.2.2.2
  push_cast at n3 n4 n5
  refine ⟨hle.trans_lt n3, hle.trans n4, (hle.trans n5).trans ?_⟩
  exact mul_le_mul_of_nonneg_left abs_dkIotaC_ge.1 (by norm_num)

end PlasmaLean.Design.DommaschkKamC
