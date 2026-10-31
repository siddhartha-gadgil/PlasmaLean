/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Transport.RelativeEntropy
public import PlasmaLean.Theory.Stability.RiccatiComparison
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Coercivity of the 1-D relative-entropy dissipation and exponential decay (N-2)

Source: `notes/theory/relative-entropy-dissipation.md` (N-2). This module continues
`PlasmaLean.Theory.Transport.RelativeEntropy`, where the corrected identity
`rate = −𝓕 + 𝓒 + 𝓡 + 𝓑` (the rate of the relative entropy `H` for supplied data, not a time
derivative of a constructed solution) and the case 1 statement (constant reference: `rate = −𝓕`)
are proved for supplied data `RelEntSetup a b`.

## Model

`H = ∫ₐᵇ n T* φ(T/T*)` with `φ(s) = s − 1 − log s`, and `𝓕 = ∫ₐᵇ κ T* (∂ₓ log(T/T*))²`.
Write `ℓ = log(T/T*)`.

## Main results

* `RelEntSetup.ratio_eq_of_fisher_eq_zero`, `RelEntSetup.exists_const_of_fisher_eq_zero`
  (**equality case**): if `κ > 0` on `[a, b]` (`a < b`) and `𝓕 = 0`, then `T/T*` is constant.
* `phi_le_half_mul_sq_log`: `φ(s) ≤ (M/2) (log s)²` for `0 < s ≤ M`, `M ≥ 1` (Taylor with the
  exponential remainder, proved by monotonicity).
* `sq_integral_le`: the 1-D Cauchy–Schwarz/Wirtinger step `(∫ₐˣ g)² ≤ (x − a) ∫ₐˣ g²`.
* `RelEntSetup.sq_log_ratio_le` (Poincaré step): with `T(a) = T*(a)`,
  `ℓ(x)² ≤ (x − a) ∫ₐᵇ (ℓ')²` on `[a, b]`.
* `RelEntSetup.relEnt_le_mul_fisher` (**coercivity**): with `T(a) = T*(a)`, `k₀ ≤ κT*`,
  `nT* ≤ N`, `T ≤ M T*` (`k₀ > 0`, `N ≥ 0`, `M ≥ 1`):
  `H ≤ N M (b − a)² / (4 k₀) · 𝓕`.
* `exp_decay_of_deriv_le_neg_fisher`, `RelEntSetup.relEnt_exp_decay` and
  `RelEntSetup.relEnt_exp_decay_const_ref` (**exponential decay**): `dH/dt ≤ −𝓕` and `H ≤ C𝓕` give
  `H(t) ≤ H(0) e^{−t/C}`, via `PlasmaLean.Stability.riccati_exp_decay`.
* Sanity: `constSetup` (`T ≡ c`, `T* ≡ 1`); `constSetup_one_equality` (equality `0 = C · 0`),
  `sq_integral_const` (equality in the Wirtinger step), and `no_coercivity_without_boundary`:
  `T = 2T*` has `𝓕 = 0` but `H = 1 − log 2 > 0`, and satisfies every hypothesis of
  `relEnt_le_mul_fisher` except `T(a) = T*(a)` (`constSetup_two_other_hyps`).

## Scope

The time derivative of `H` (differentiation under the integral sign) is a **hypothesis** of the
decay theorems, as is the existence of the solution; the coercivity constant uses the bound
`T ≤ M T*` (an `L∞` bound on the ratio), which is necessary for a quadratic bound since `φ(e^ℓ)`
grows exponentially in `ℓ`. The constant `(b − a)²/2` in the Poincaré step is not sharp (the
mixed Dirichlet–Neumann optimum is `4(b − a)²/π²`). Mathlib (pinned version) has no 1-D
Poincaré or Wirtinger inequality; the step is proved here directly.
-/

public section

noncomputable section

namespace PlasmaLean.Transport.RelativeEntropy

open Real Set MeasureTheory intervalIntegral

/-! ## Scalar bounds on `φ` -/

/-- For `x ≤ 0`: `eˣ − 1 − x ≤ x²/2`. -/
theorem exp_sub_one_sub_le_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    Real.exp x - 1 - x ≤ x ^ 2 / 2 := by
  set g : ℝ → ℝ := fun y => y ^ 2 / 2 - Real.exp y + 1 + y with hg
  have hd : ∀ y, HasDerivAt g (y - Real.exp y + 1) y := by
    intro y
    have h := (((hasDerivAt_pow 2 y).div_const 2).sub (Real.hasDerivAt_exp y)).add_const 1
    convert h.add (hasDerivAt_id y) using 1
    · funext z; simp [hg]
    · simp
  have hanti : AntitoneOn g (Iic 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y _ => ?_
    rw [(hd y).deriv]
    linarith [Real.add_one_le_exp y]
  have := hanti hx (show (0 : ℝ) ∈ Iic 0 from le_rfl) hx
  simp only [hg, Real.exp_zero] at this
  linarith

/-- For `x ≥ 0`: `eˣ − 1 − x ≤ eˣ x²/2`. -/
theorem exp_sub_one_sub_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp x - 1 - x ≤ Real.exp x * (x ^ 2 / 2) := by
  set k : ℝ → ℝ := fun y => y ^ 2 / 2 - 1 + Real.exp (-y) * (1 + y) with hk
  have hd : ∀ y, HasDerivAt k (y * (1 - Real.exp (-y))) y := by
    intro y
    have he : HasDerivAt (fun y => Real.exp (-y)) (-Real.exp (-y)) y := by
      convert (hasDerivAt_neg y).exp using 1; ring
    have h := (((hasDerivAt_pow 2 y).div_const 2).sub_const 1).add
      (he.mul ((hasDerivAt_id y).const_add 1))
    convert h using 1
    · funext z; simp [hk]
    · simp; ring
  have hmono : MonotoneOn k (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) fun y hy => ?_
    rw [interior_Ici] at hy
    rw [(hd y).deriv]
    have : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [mem_Ioi.1 hy])
    exact mul_nonneg (le_of_lt (mem_Ioi.1 hy)) (by linarith)
  have h0 := hmono (show (0 : ℝ) ∈ Ici 0 from le_rfl) hx hx
  simp only [hk, neg_zero, Real.exp_zero] at h0
  have hex : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  nlinarith [mul_le_mul_of_nonneg_left h0 hpos.le]

/-- **Quadratic bound on `φ`.** For `0 < s ≤ M` with `M ≥ 1`: `φ(s) ≤ (M/2) (log s)²`. -/
theorem phi_le_half_mul_sq_log {s M : ℝ} (hs : 0 < s) (hM : 1 ≤ M) (hsM : s ≤ M) :
    phi s ≤ M / 2 * Real.log s ^ 2 := by
  have hes : Real.exp (Real.log s) = s := Real.exp_log hs
  unfold phi
  rcases le_total (Real.log s) 0 with h | h
  · have := exp_sub_one_sub_le_of_nonpos h
    rw [hes] at this
    nlinarith [sq_nonneg (Real.log s)]
  · have := exp_sub_one_sub_le_of_nonneg h
    rw [hes] at this
    nlinarith [sq_nonneg (Real.log s)]

/-! ## The 1-D Wirtinger (Cauchy–Schwarz) step -/

/-- **Cauchy–Schwarz on an interval.** For `g` continuous on `[a, x]`:
`(∫ₐˣ g)² ≤ (x − a) ∫ₐˣ g²`. Proof: integrate `2 m g − m² ≤ g²` with `m = (∫ g)/(x − a)`. -/
theorem sq_integral_le {g : ℝ → ℝ} {a x : ℝ} (hax : a ≤ x) (hg : ContinuousOn g (uIcc a x)) :
    (∫ y in a..x, g y) ^ 2 ≤ (x - a) * ∫ y in a..x, g y ^ 2 := by
  rcases hax.eq_or_lt with h | h
  · subst h; simp
  set G := ∫ y in a..x, g y with hG
  set L := x - a with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  set m := G / L with hm
  have hgi : IntervalIntegrable g volume a x := hg.intervalIntegrable
  have hg2 : IntervalIntegrable (fun y => g y ^ 2) volume a x := (hg.pow 2).intervalIntegrable
  have hlin : IntervalIntegrable (fun y => 2 * m * g y - m ^ 2) volume a x :=
    (hgi.const_mul (2 * m)).sub intervalIntegrable_const
  have hle := integral_mono_on (μ := volume) hax hlin hg2 fun y _ => by
    nlinarith [sq_nonneg (g y - m)]
  rw [integral_sub (hgi.const_mul (2 * m)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, ← hG,
    ← hL] at hle
  have heq : 2 * m * G - L * m ^ 2 = G ^ 2 / L := by
    rw [hm]; field_simp; ring
  rw [heq, div_le_iff₀ hLpos] at hle
  linarith

/-- Sanity: equality holds in `sq_integral_le` for a constant integrand. -/
theorem sq_integral_const (c a x : ℝ) :
    (∫ _ in a..x, c) ^ 2 = (x - a) * ∫ _ in a..x, c ^ 2 := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]; ring

/-! ## Relative entropy, equality case and coercivity -/

namespace RelEntSetup

variable {a b : ℝ} (S : RelEntSetup a b)

/-- The relative entropy `H = ∫ₐᵇ n T* φ(T/T*)` of the data at the fixed time. -/
@[expose] def relEnt (n : ℝ → ℝ) : ℝ := ∫ x in a..b, relEntDensity (n x) (S.Ts x) (S.T x)

/-- The log-ratio derivative `∂ₓ log(T/T*) = T'/T − T*'/T*`. -/
@[expose] def logRatioDeriv (x : ℝ) : ℝ := S.dT x / S.T x - S.dTs x / S.Ts x

/-- `log(T/T*)` has derivative `logRatioDeriv` on the interval. -/
theorem hasDerivAt_logRatio {x : ℝ} (hx : x ∈ uIcc a b) :
    HasDerivAt (fun y => Real.log (S.T y / S.Ts y)) (S.logRatioDeriv x) x :=
  hasDerivAt_log_ratio (S.T_pos x hx) (S.Ts_pos x hx) (S.hT x hx) (S.hTs x hx)

/-- `logRatioDeriv` is continuous on the interval. -/
theorem cont_logRatioDeriv : ContinuousOn S.logRatioDeriv (uIcc a b) :=
  (S.cont_dT.div S.contT fun x hx => (S.T_pos x hx).ne').sub
    (S.cont_dTs.div S.contTs fun x hx => (S.Ts_pos x hx).ne')

/-- The relative-entropy density is continuous on the interval when `n` is. -/
theorem cont_density {n : ℝ → ℝ} (hn : ContinuousOn n (uIcc a b)) :
    ContinuousOn (fun x => relEntDensity (n x) (S.Ts x) (S.T x)) (uIcc a b) := by
  unfold relEntDensity phi
  exact (hn.mul S.contTs).mul (((S.contT.div S.contTs fun x hx => (S.Ts_pos x hx).ne').sub
    continuousOn_const).sub S.cont_log)

/-- `H ≥ 0` for `n ≥ 0` and `a ≤ b`. -/
theorem relEnt_nonneg (hab : a ≤ b) {n : ℝ → ℝ} (hn0 : ∀ x ∈ uIcc a b, 0 ≤ n x) :
    0 ≤ S.relEnt n := by
  unfold relEnt
  refine integral_nonneg hab fun x hx => ?_
  have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
  exact relEntDensity_nonneg (hn0 x hx') (S.Ts_pos x hx') (S.T_pos x hx')

/-- **Equality case.** If `a < b`, `κ > 0` on `[a, b]` and `𝓕 = 0`, then `T/T*` is constant on
`[a, b]`: `T(x)/T*(x) = T(a)/T*(a)`. -/
theorem ratio_eq_of_fisher_eq_zero (hab : a < b) (hκ : ∀ x ∈ uIcc a b, 0 < S.κ x)
    (h : S.fisher = 0) : ∀ x ∈ Icc a b, S.T x / S.Ts x = S.T a / S.Ts a := by
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  set f := fun x => S.κ x * S.Ts x * (S.dT x / S.T x - S.dTs x / S.Ts x) ^ 2 with hf
  have hfnn : ∀ x ∈ uIcc a b, 0 ≤ f x := fun x hx =>
    mul_nonneg (mul_nonneg (hκ x hx).le (S.Ts_pos x hx).le) (sq_nonneg _)
  have hae : 0 ≤ᵐ[volume.restrict (Ioc a b)] f :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun x hx =>
      hfnn x (by rw [hIcc]; exact Ioc_subset_Icc_self hx)
  have hzero := (integral_eq_zero_iff_of_le_of_nonneg_ae hab.le hae
    (S.cont_fisher.intervalIntegrable (μ := volume))).1 h
  have hzero' : f =ᵐ[volume.restrict (Ioo a b)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hzero
  have hIoo : Ioo a b ⊆ uIcc a b := by rw [hIcc]; exact Ioo_subset_Icc_self
  have heq := Measure.eqOn_open_of_ae_eq hzero' isOpen_Ioo (S.cont_fisher.mono hIoo)
    continuousOn_const
  have hu : ∀ x ∈ Ioo a b, S.logRatioDeriv x = 0 := by
    intro x hx
    have h0 : f x = 0 := heq hx
    have hk := mul_pos (hκ x (hIoo hx)) (S.Ts_pos x (hIoo hx))
    simp only [hf, mul_eq_zero, hk.ne', false_or, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h0
    · unfold logRatioDeriv; exact h0
  intro x hx
  have hxu : x ∈ uIcc a b := by rw [hIcc]; exact hx
  have hau : a ∈ uIcc a b := left_mem_uIcc
  have hlog : Real.log (S.T x / S.Ts x) = Real.log (S.T a / S.Ts a) := by
    rcases hx.1.eq_or_lt with hxa | hxa
    · subst hxa; rfl
    have hsub : Icc a x ⊆ uIcc a b := by rw [hIcc]; exact Icc_subset_Icc le_rfl hx.2
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun y => Real.log (S.T y / S.Ts y))
      S.logRatioDeriv hxa (S.cont_log.mono hsub)
      fun y hy => S.hasDerivAt_logRatio (hsub (Ioo_subset_Icc_self hy))
    rw [hu c ⟨hc.1, hc.2.trans_le hx.2⟩, eq_comm, div_eq_zero_iff] at hcd
    rcases hcd with hcd | hcd
    · linarith
    · linarith
  exact Real.log_injOn_pos (mem_Ioi.2 (div_pos (S.T_pos x hxu) (S.Ts_pos x hxu)))
    (mem_Ioi.2 (div_pos (S.T_pos a hau) (S.Ts_pos a hau))) hlog

/-- **Equality case, multiplicative form.** Under the hypotheses of
`ratio_eq_of_fisher_eq_zero`, there is `c > 0` with `T = c T*` on `[a, b]`. -/
theorem exists_const_of_fisher_eq_zero (hab : a < b) (hκ : ∀ x ∈ uIcc a b, 0 < S.κ x)
    (h : S.fisher = 0) : ∃ c > 0, ∀ x ∈ Icc a b, S.T x = c * S.Ts x := by
  have hau : a ∈ uIcc a b := left_mem_uIcc
  refine ⟨S.T a / S.Ts a, div_pos (S.T_pos a hau) (S.Ts_pos a hau), fun x hx => ?_⟩
  have hxu : x ∈ uIcc a b := by rw [uIcc_of_le hab.le]; exact hx
  rw [← S.ratio_eq_of_fisher_eq_zero hab hκ h x hx]
  field_simp [(S.Ts_pos x hxu).ne']

/-- **Poincaré step.** If `T(a) = T*(a)` and `a ≤ b`, then for `x ∈ [a, b]`:
`log(T/T*)(x)² ≤ (x − a) ∫ₐᵇ (∂ₓ log(T/T*))²`. -/
theorem sq_log_ratio_le (hab : a ≤ b) (ha : S.T a = S.Ts a) {x : ℝ} (hx : x ∈ Icc a b) :
    Real.log (S.T x / S.Ts x) ^ 2 ≤ (x - a) * ∫ y in a..b, S.logRatioDeriv y ^ 2 := by
  have hIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hsub : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, hIcc]; exact Icc_subset_Icc le_rfl hx.2
  have hftc : ∫ y in a..x, S.logRatioDeriv y =
      Real.log (S.T x / S.Ts x) - Real.log (S.T a / S.Ts a) :=
    integral_eq_sub_of_hasDerivAt (fun y hy => S.hasDerivAt_logRatio (hsub hy))
      ((S.cont_logRatioDeriv.mono hsub).intervalIntegrable)
  have ha0 : Real.log (S.T a / S.Ts a) = 0 := by
    rw [ha, div_self (S.Ts_pos a left_mem_uIcc).ne', Real.log_one]
  rw [ha0, sub_zero] at hftc
  have hcs := sq_integral_le hx.1 (S.cont_logRatioDeriv.mono hsub)
  rw [hftc] at hcs
  have hmono : ∫ y in a..x, S.logRatioDeriv y ^ 2 ≤ ∫ y in a..b, S.logRatioDeriv y ^ 2 :=
    integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun y => sq_nonneg _)
      ((S.cont_logRatioDeriv.pow 2).intervalIntegrable)
  nlinarith [mul_le_mul_of_nonneg_left hmono (sub_nonneg.2 hx.1)]

/-- The Fisher information bounds `k₀ ∫ (ℓ')²` when `k₀ ≤ κ T*`. -/
theorem mul_integral_sq_le_fisher (hab : a ≤ b) {k₀ : ℝ}
    (hκ : ∀ x ∈ uIcc a b, k₀ ≤ S.κ x * S.Ts x) :
    k₀ * ∫ y in a..b, S.logRatioDeriv y ^ 2 ≤ S.fisher := by
  rw [← intervalIntegral.integral_const_mul]
  unfold fisher
  refine integral_mono_on hab ((S.cont_logRatioDeriv.pow 2).intervalIntegrable.const_mul k₀)
    (S.cont_fisher.intervalIntegrable) fun x hx => ?_
  have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
  unfold logRatioDeriv
  exact mul_le_mul_of_nonneg_right (hκ x hx') (sq_nonneg _)

/-- **Coercivity (relative-entropy/Fisher inequality).** Let `a ≤ b`, `n` continuous, and
suppose `T(a) = T*(a)` (Dirichlet match at one endpoint), `k₀ ≤ κ T*`, `n T* ≤ N` and
`T ≤ M T*` on `[a, b]`, with `k₀ > 0`, `N ≥ 0`, `M ≥ 1`. Then
`H = ∫ n T* φ(T/T*) ≤ N M (b − a)² / (4 k₀) · 𝓕`. -/
theorem relEnt_le_mul_fisher (hab : a ≤ b) {n : ℝ → ℝ} (hn : ContinuousOn n (uIcc a b))
    {k₀ N M : ℝ} (hk₀ : 0 < k₀) (hN : 0 ≤ N) (hM : 1 ≤ M)
    (hκ : ∀ x ∈ uIcc a b, k₀ ≤ S.κ x * S.Ts x) (hnTs : ∀ x ∈ uIcc a b, n x * S.Ts x ≤ N)
    (hTM : ∀ x ∈ uIcc a b, S.T x ≤ M * S.Ts x) (ha : S.T a = S.Ts a) :
    S.relEnt n ≤ N * M * (b - a) ^ 2 / (4 * k₀) * S.fisher := by
  set I := ∫ y in a..b, S.logRatioDeriv y ^ 2 with hI
  have hI0 : 0 ≤ I := integral_nonneg hab fun y _ => sq_nonneg _
  have hpt : ∀ x ∈ Icc a b,
      relEntDensity (n x) (S.Ts x) (S.T x) ≤ N * M / 2 * I * (x - a) := by
    intro x hx
    have hx' : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hx
    have hT := S.T_pos x hx'
    have hTs := S.Ts_pos x hx'
    have hs : 0 < S.T x / S.Ts x := div_pos hT hTs
    have hsM : S.T x / S.Ts x ≤ M := by rw [div_le_iff₀ hTs]; exact hTM x hx'
    have hphi := phi_le_half_mul_sq_log hs hM hsM
    have hphi0 := phi_nonneg hs
    have hl := S.sq_log_ratio_le hab ha hx
    unfold relEntDensity
    calc n x * S.Ts x * phi (S.T x / S.Ts x) ≤ N * phi (S.T x / S.Ts x) :=
          mul_le_mul_of_nonneg_right (hnTs x hx') hphi0
      _ ≤ N * (M / 2 * Real.log (S.T x / S.Ts x) ^ 2) := mul_le_mul_of_nonneg_left hphi hN
      _ ≤ N * (M / 2 * ((x - a) * I)) := by
          gcongr
      _ = N * M / 2 * I * (x - a) := by ring
  have hint : S.relEnt n ≤ ∫ x in a..b, N * M / 2 * I * (x - a) := by
    unfold relEnt
    exact integral_mono_on hab (S.cont_density hn).intervalIntegrable
      ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _) hpt
  have hcalc : ∫ x in a..b, N * M / 2 * I * (x - a) = N * M / 2 * I * ((b - a) ^ 2 / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_comp_sub_right (fun x => x) a, integral_id]
    ring
  have hfis := S.mul_integral_sq_le_fisher hab hκ
  rw [hcalc] at hint
  have hc0 : 0 ≤ N * M * (b - a) ^ 2 := by
    have : 0 ≤ M := by linarith
    positivity
  have hfinal : N * M / 2 * I * ((b - a) ^ 2 / 2) ≤ N * M * (b - a) ^ 2 / (4 * k₀) * S.fisher := by
    have : N * M / 2 * I * ((b - a) ^ 2 / 2) = N * M * (b - a) ^ 2 / (4 * k₀) * (k₀ * I) := by
      field_simp
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hfis (by positivity)
  linarith

end RelEntSetup

/-! ## Exponential decay -/

/-- **Exponential decay from dissipation and coercivity.** If `H ≥ 0` is continuous on `[0, τ]`,
has right derivative `H'` on `[0, τ)` with `H' ≤ −𝓕` and `H ≤ C 𝓕` there (`C > 0`), then
`H(t) ≤ H(0) e^{−t/C}` on `[0, τ]`. Proved by `PlasmaLean.Stability.riccati_exp_decay` with no
quadratic term. -/
theorem exp_decay_of_deriv_le_neg_fisher {H H' 𝓕 : ℝ → ℝ} {τ C : ℝ} (hC : 0 < C)
    (hcont : ContinuousOn H (Icc 0 τ))
    (hderiv : ∀ t ∈ Ico 0 τ, HasDerivWithinAt H (H' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 τ, H' t ≤ -𝓕 t) (hcoer : ∀ t ∈ Ico 0 τ, H t ≤ C * 𝓕 t)
    (hnonneg : ∀ t ∈ Icc 0 τ, 0 ≤ H t) :
    ∀ t ∈ Icc 0 τ, H t ≤ H 0 * Real.exp (-t / C) := by
  have hineq : ∀ t ∈ Ico 0 τ, H' t ≤ -(1 / C) * H t + 0 * 0 * H t ^ 2 := by
    intro t ht
    have h1 := hdiss t ht
    have h2 : H t / C ≤ 𝓕 t := by rw [div_le_iff₀ hC]; linarith [hcoer t ht]
    have : -(1 / C) * H t + 0 * 0 * H t ^ 2 = -(H t / C) := by ring
    rw [this]; linarith
  have h := PlasmaLean.Stability.riccati_exp_decay (C := 0) (ε := 0) hcont hderiv hineq hnonneg
    (by norm_num) (by simpa using one_div_pos.2 hC)
  intro t ht
  have := h t ht
  have he : -(1 / C - 0 * 0 * H 0) * t = -t / C := by ring
  rwa [he] at this

namespace RelEntSetup

variable {a b : ℝ}

/-- **Exponential decay of the relative entropy (conditional).** Let `S t` be the supplied data at
time `t` and `H(t) = (S t).relEnt n`. Assume the coercivity hypotheses of `relEnt_le_mul_fisher`
at every time in `[0, τ)` (uniform `k₀`, `N`, `M`), `n ≥ 0`, continuity of `H` on `[0, τ]`, and the
**hypothesis** that `H` has right derivative `H'` with `H' ≤ −𝓕` (as given by
`rate_le_neg_fisher_const_ref` once differentiation under the integral is justified). Then
`H(t) ≤ H(0) e^{−t/C}` with `C = N M (b − a)² / (4 k₀)`. -/
theorem relEnt_exp_decay (hab : a < b) {S : ℝ → RelEntSetup a b} {n H' : ℝ → ℝ} {τ k₀ N M : ℝ}
    (hn : ContinuousOn n (uIcc a b)) (hn0 : ∀ x ∈ uIcc a b, 0 ≤ n x)
    (hk₀ : 0 < k₀) (hN : 0 < N) (hM : 1 ≤ M)
    (hκ : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, k₀ ≤ (S t).κ x * (S t).Ts x)
    (hnTs : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, n x * (S t).Ts x ≤ N)
    (hTM : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, (S t).T x ≤ M * (S t).Ts x)
    (ha : ∀ t ∈ Ico 0 τ, (S t).T a = (S t).Ts a)
    (hcont : ContinuousOn (fun t => (S t).relEnt n) (Icc 0 τ))
    (hderiv : ∀ t ∈ Ico 0 τ, HasDerivWithinAt (fun t => (S t).relEnt n) (H' t) (Ici t) t)
    (hdiss : ∀ t ∈ Ico 0 τ, H' t ≤ -(S t).fisher) :
    ∀ t ∈ Icc 0 τ, (S t).relEnt n ≤
      (S 0).relEnt n * Real.exp (-t / (N * M * (b - a) ^ 2 / (4 * k₀))) := by
  have hC : 0 < N * M * (b - a) ^ 2 / (4 * k₀) := by
    have : 0 < b - a := by linarith
    have : 0 < M := by linarith
    positivity
  exact exp_decay_of_deriv_le_neg_fisher (𝓕 := fun t => (S t).fisher) hC hcont hderiv hdiss
    (fun t ht => (S t).relEnt_le_mul_fisher hab.le hn hk₀ hN.le hM (hκ t ht) (hnTs t ht)
      (hTM t ht) (ha t ht))
    (fun t _ => (S t).relEnt_nonneg hab.le hn0)

/-- **Exponential decay, constant reference (note case 1, conditional on differentiating under
the integral).** Suppose at each time `t ∈ [0, τ)` the data `S t` satisfy `n ∂ₜT = F'`, `T*' = 0`,
`F*' = 0`, `T = T*` at `a`, and `T = T*` or `F = 0` at `b`, together with the coercivity bounds,
and suppose (**hypothesis**) that `H(t) = (S t).relEnt n` has right derivative
`∫ n (1 − T*/T) ∂ₜT` (the pointwise rate, i.e. differentiation under the integral sign). Then
`H(t) ≤ H(0) e^{−t/C}` with `C = N M (b − a)² / (4 k₀)`. -/
theorem relEnt_exp_decay_const_ref (hab : a < b) {S : ℝ → RelEntSetup a b} {n : ℝ → ℝ}
    {Tt : ℝ → ℝ → ℝ} {τ k₀ N M : ℝ}
    (hn : ContinuousOn n (uIcc a b)) (hn0 : ∀ x ∈ uIcc a b, 0 ≤ n x)
    (hk₀ : 0 < k₀) (hN : 0 < N) (hM : 1 ≤ M)
    (hκ : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, k₀ ≤ (S t).κ x * (S t).Ts x)
    (hnTs : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, n x * (S t).Ts x ≤ N)
    (hTM : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, (S t).T x ≤ M * (S t).Ts x)
    (hpde : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, n x * Tt t x = (S t).dF x)
    (hdTs : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, (S t).dTs x = 0)
    (hdFs : ∀ t ∈ Ico 0 τ, ∀ x ∈ uIcc a b, (S t).dFs x = 0)
    (ha : ∀ t ∈ Ico 0 τ, (S t).T a = (S t).Ts a)
    (hb : ∀ t ∈ Ico 0 τ, (S t).T b = (S t).Ts b ∨ (S t).F b = 0)
    (hcont : ContinuousOn (fun t => (S t).relEnt n) (Icc 0 τ))
    (hderiv : ∀ t ∈ Ico 0 τ, HasDerivWithinAt (fun t => (S t).relEnt n)
      (∫ x in a..b, n x * (1 - (S t).Ts x / (S t).T x) * Tt t x) (Ici t) t) :
    ∀ t ∈ Icc 0 τ, (S t).relEnt n ≤
      (S 0).relEnt n * Real.exp (-t / (N * M * (b - a) ^ 2 / (4 * k₀))) := by
  refine relEnt_exp_decay hab hn hn0 hk₀ hN hM hκ hnTs hTM ha hcont hderiv fun t ht => ?_
  have hκ0 : ∀ x ∈ uIcc a b, 0 ≤ (S t).κ x := fun x hx => by
    have h1 := hκ t ht x hx
    have h2 := (S t).Ts_pos x hx
    by_contra hneg
    have hlt : (S t).κ x < 0 := lt_of_not_ge hneg
    nlinarith [mul_neg_of_neg_of_pos hlt h2]
  exact ((S t).rate_le_neg_fisher_const_ref hab.le (hpde t ht) hκ0 (hdTs t ht) (hdFs t ht)
    (Or.inl (ha t ht)) (hb t ht)).1.le

end RelEntSetup

/-! ## Sanity checks -/

/-- Constant data on `[0, 1]`: `κ = 1`, `T* ≡ 1`, `T ≡ c` (`c > 0`); all derivatives vanish. -/
@[expose] def constSetup (c : ℝ) (hc : 0 < c) : RelEntSetup 0 1 where
  κ := fun _ => 1
  T := fun _ => c
  Ts := fun _ => 1
  dT := fun _ => 0
  dTs := fun _ => 0
  F := fun _ => 0
  Fs := fun _ => 0
  dF := fun _ => 0
  dFs := fun _ => 0
  T_pos := fun _ _ => hc
  Ts_pos := fun _ _ => one_pos
  hT := fun x _ => hasDerivAt_const x c
  hTs := fun x _ => hasDerivAt_const x 1
  hF := fun x _ => hasDerivAt_const x 0
  hFs := fun x _ => hasDerivAt_const x 0
  F_eq := fun _ _ => by simp
  Fs_eq := fun _ _ => by simp
  cont_κ := continuousOn_const
  cont_dT := continuousOn_const
  cont_dTs := continuousOn_const
  cont_dF := continuousOn_const
  cont_dFs := continuousOn_const

/-- The constant data have zero Fisher information. -/
theorem constSetup_fisher (c : ℝ) (hc : 0 < c) : (constSetup c hc).fisher = 0 := by
  simp [RelEntSetup.fisher, constSetup]

/-- The constant data have relative entropy `φ(c) = c − 1 − log c` (with `n ≡ 1`). -/
theorem constSetup_relEnt (c : ℝ) (hc : 0 < c) :
    (constSetup c hc).relEnt (fun _ => 1) = phi c := by
  simp [RelEntSetup.relEnt, constSetup, relEntDensity]

/-- **Equality case of the coercivity bound.** For `T = T* ≡ 1` both sides vanish:
`H = 0 = C · 𝓕` for every `C`. -/
theorem constSetup_one_equality (C : ℝ) :
    (constSetup 1 one_pos).relEnt (fun _ => 1) = C * (constSetup 1 one_pos).fisher := by
  rw [constSetup_relEnt, constSetup_fisher, phi_one, mul_zero]

/-- `T = 2T*` satisfies every hypothesis of `relEnt_le_mul_fisher` (with `k₀ = N = 1`, `M = 2`,
`n ≡ 1`) except the endpoint condition `T(a) = T*(a)`, which fails. -/
theorem constSetup_two_other_hyps :
    (∀ x ∈ uIcc (0 : ℝ) 1, (1 : ℝ) ≤ (constSetup 2 two_pos).κ x * (constSetup 2 two_pos).Ts x) ∧
    (∀ x ∈ uIcc (0 : ℝ) 1, (1 : ℝ) * (constSetup 2 two_pos).Ts x ≤ 1) ∧
    (∀ x ∈ uIcc (0 : ℝ) 1, (constSetup 2 two_pos).T x ≤ 2 * (constSetup 2 two_pos).Ts x) ∧
    (constSetup 2 two_pos).T 0 ≠ (constSetup 2 two_pos).Ts 0 := by
  refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ _ => ?_, ?_⟩ <;> norm_num [constSetup]

/-- **The boundary condition is necessary.** For `T = 2T*` (constant), `𝓕 = 0` but
`H = 1 − log 2 > 0`, so no inequality `H ≤ C 𝓕` holds for any `C`. -/
theorem no_coercivity_without_boundary :
    ¬ ∃ C : ℝ, (constSetup 2 two_pos).relEnt (fun _ => 1) ≤ C * (constSetup 2 two_pos).fisher := by
  rintro ⟨C, hC⟩
  rw [constSetup_relEnt, constSetup_fisher, mul_zero] at hC
  have : phi 2 = 1 - Real.log 2 := by unfold phi; ring
  rw [this] at hC
  linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num)]

end PlasmaLean.Transport.RelativeEntropy
