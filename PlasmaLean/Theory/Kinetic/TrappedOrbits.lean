/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trapped (banana) orbits in the Boozer guiding-centre model: per-bounce steps (rung M4)

Companion to `notes/theory/near-qa-trapped-particles.md` (targets T1, T3 and the discrete
averaging lemma). Everything is about the vacuum Boozer guiding-centre **model** of
`Theory/Kinetic/BoozerGuidingCentre` (QA helicity `(N, M) = (0, 1)`, `ξ = ∂_φ`); orbits are
supplied, not constructed.

Results:

* `band_of_approx_first_integral`: abstract band lemma. If `|I(t) − I(t₀)| ≤ δ` and the flux label
  is controlled by `I` (`|ψ − f(I)| ≤ w`, `f` `L`-Lipschitz), then `|ψ(t) − ψ(t₀)| ≤ 2w + Lδ`;
  `band_of_approx_first_integral_inv` is the inverse form `K = H₀(P) + ε h` with
  `ω |x − y| ≤ |H₀ x − H₀ y|`, giving `|P(t) − P(t₀)| ≤ (2ε + δ)/ω`.
* `psip_step`: exact integral identity over any time interval for QA momentum,
  `q Δψ_p = q G Δρ + ∫ (q²ρ²B/m + μ) ∂_φB dt` (fundamental theorem of calculus applied to the
  momentum identity; needs continuity of `∂_φB` along the orbit for integrability).
* `bounce_psip_step`: between two turning points (`v_∥ = 0`, so `ρ = 0`) the orbit-width term
  drops out: `q Δψ_p = ∫ (q²ρ²B/m + μ) ∂_φB dt`.
* `bounce_psip_step_exactQA`: in exact QA (`∂_φB ≡ 0`) the bounce returns to the same `ψ_p`,
  and inside the bounce `|q| |ψ_p(ψ(t)) − ψ_p(ψ(t₀))| = |q G| |ρ(t)|` (orbit width only).
* `bounce_psip_step_le`: near QA, `|q Δψ_p| ≤ (2H/B_min) ε (t₁ − t₀)` per bounce.
* `sum_bounce_psip`: summing over consecutive turning points `τ 0 ≤ τ 1 ≤ … ≤ τ N`.
* `abs_sum_sin_arith_le`: `|Σ_{k<N} sin(kα + β)| ≤ 1/|sin(α/2)|` (discrete averaging);
  `abs_sum_kicks_le`: kicks `A sin(kα+β) + O(R)` sum to at most `|A|/|sin(α/2)| + N R`.
* `bounce_drift_nonresonant`: if the per-bounce kick integrals have the leading-order form
  `A sin(kα + β)` up to `R` (a **hypothesis**, not derived here: it is the bounce-averaged
  `b₁`-term over the exact-QA banana with the toroidal phase advancing by `α` per bounce), and
  `sin(α/2) ≠ 0` (non-resonance), then `|q| |ψ_p(ψ(τ N)) − ψ_p(ψ(τ 0))| ≤ |A|/|sin(α/2)| + N R`:
  no secular drift at order `A`, only the remainder accumulates.

What is **not** proved: the leading-order kick form (needs validated bounce integrals over the
exact-QA banana and control of the phase shear, i.e. the Chirikov/GWB parameter), existence of
turning points, and the exclusion of separatrix crossings (obstruction O1).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Kinetic Real

/-! ## Abstract band lemmas -/

/-- **Band from an approximate first integral.** On a time set `S ∋ t₀`, if `I` drifts by at
most `δ` from `I(t₀)` and the flux label is controlled by `I` up to `w` (`|ψ − f(I)| ≤ w`, with
`f` `L`-Lipschitz), then `ψ` stays in the band `|ψ(t) − ψ(t₀)| ≤ 2w + Lδ`. -/
theorem band_of_approx_first_integral {I ψ f : ℝ → ℝ} {S : Set ℝ} {t₀ δ w L : ℝ}
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) (ht₀ : t₀ ∈ S)
    (hI : ∀ t ∈ S, |I t - I t₀| ≤ δ) (hψ : ∀ t ∈ S, |ψ t - f (I t)| ≤ w) :
    ∀ t ∈ S, |ψ t - ψ t₀| ≤ 2 * w + L * δ := by
  intro t ht
  have h1 := hψ t ht
  have h2 := hψ t₀ ht₀
  have hL0 : 0 ≤ L := by
    have h := hL 1 0
    norm_num at h
    exact (abs_nonneg _).trans h
  have h3 : |f (I t) - f (I t₀)| ≤ L * δ :=
    (hL _ _).trans (mul_le_mul_of_nonneg_left (hI t ht) hL0)
  calc |ψ t - ψ t₀| = |(ψ t - f (I t)) + (f (I t) - f (I t₀)) - (ψ t₀ - f (I t₀))| := by
        ring_nf
    _ ≤ |(ψ t - f (I t)) + (f (I t) - f (I t₀))| + |ψ t₀ - f (I t₀)| := abs_sub _ _
    _ ≤ 2 * w + L * δ := by linarith [abs_add_le (ψ t - f (I t)) (f (I t) - f (I t₀))]

/-- **Inverse form of the band lemma** (target T3 of the note, global version). If
`K = H₀ ∘ P + ε h` with `|h| ≤ 1`, `H₀` is uniformly expanding (`ω |x − y| ≤ |H₀ x − H₀ y|`,
`ω > 0`; e.g. `H₀' ≥ ω`), and `|K(t) − K(t₀)| ≤ δ` on `S`, then `|P(t) − P(t₀)| ≤ (2ε + δ)/ω`. -/
theorem band_of_approx_first_integral_inv {K P h H₀ : ℝ → ℝ} {S : Set ℝ} {t₀ ε δ ω : ℝ}
    (hω : 0 < ω) (hH : ∀ x y, ω * |x - y| ≤ |H₀ x - H₀ y|) (hε : 0 ≤ ε) (ht₀ : t₀ ∈ S)
    (hK : ∀ t ∈ S, K t = H₀ (P t) + ε * h t) (hh : ∀ t ∈ S, |h t| ≤ 1)
    (hdrift : ∀ t ∈ S, |K t - K t₀| ≤ δ) :
    ∀ t ∈ S, |P t - P t₀| ≤ (2 * ε + δ) / ω := by
  intro t ht
  rw [le_div_iff₀ hω, mul_comm]
  have e : H₀ (P t) - H₀ (P t₀) = (K t - K t₀) - ε * h t + ε * h t₀ := by
    rw [hK t ht, hK t₀ ht₀]; ring
  have a1 : |ε * h t| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε]; nlinarith [hh t ht, abs_nonneg (h t)]
  have a2 : |ε * h t₀| ≤ ε := by
    rw [abs_mul, abs_of_nonneg hε]; nlinarith [hh t₀ ht₀, abs_nonneg (h t₀)]
  calc ω * |P t - P t₀| ≤ |H₀ (P t) - H₀ (P t₀)| := hH _ _
    _ = |(K t - K t₀) - ε * h t + ε * h t₀| := by rw [e]
    _ ≤ |(K t - K t₀) - ε * h t| + |ε * h t₀| := abs_add_le _ _
    _ ≤ |K t - K t₀| + |ε * h t| + |ε * h t₀| := by
        linarith [abs_sub (K t - K t₀) (ε * h t)]
    _ ≤ 2 * ε + δ := by linarith [hdrift t ht]

/-! ## Per-bounce momentum step -/

variable {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- The QA kick integrand `(q²ρ²B/m + μ) ∂_φB` along an orbit (`= −dP/dt`). -/
@[expose] def qaKick (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t / m + μ) * along F.Bφ ψ θ φ t

/-- The kick integrand is continuous on `[t₀, t₁] ⊆ [0, T]` when `∂_φB` is continuous there
along the orbit. -/
theorem qaKick_continuousOn {T t₀ t₁ : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T)
    (h0 : 0 ≤ t₀) (h1T : t₁ ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc t₀ t₁)) :
    ContinuousOn (qaKick F m q μ ψ θ φ ρ) (Set.Icc t₀ t₁) := by
  have hsub : ∀ s ∈ Set.Icc t₀ t₁, s ∈ Set.Icc 0 T := fun s hs =>
    ⟨h0.trans hs.1, hs.2.trans h1T⟩
  have hρ : ContinuousOn ρ (Set.Icc t₀ t₁) :=
    fun s hs => (h.dρ s (hsub s hs)).continuousAt.continuousWithinAt
  have hB : ContinuousOn (along F.B ψ θ φ) (Set.Icc t₀ t₁) :=
    fun s hs => (h.hasDerivAt_B (hsub s hs)).continuousAt.continuousWithinAt
  unfold qaKick
  exact ((((continuousOn_const.mul (hρ.pow 2)).mul hB).div_const m).add continuousOn_const).mul hc

/-- **Momentum step over a time interval** (QA, exact identity in the model):
`q (ψ_p(ψ t₁) − ψ_p(ψ t₀)) = q G (ρ t₁ − ρ t₀) + ∫_{t₀}^{t₁} (q²ρ²B/m + μ) ∂_φB dt`.
This is the fundamental theorem of calculus for `helicalMomentum_hasDerivAt_on`. -/
theorem psip_step (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t₀ t₁ : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc t₀ t₁)) :
    q * (F.ψp (ψ t₁) - F.ψp (ψ t₀)) =
      q * F.G * (ρ t₁ - ρ t₀) + ∫ t in t₀..t₁, qaKick F m q μ ψ θ φ ρ t := by
  have hderiv : ∀ x ∈ Set.uIcc t₀ t₁,
      HasDerivAt (fun t => -helicalMomentum F q 0 1 ψ ρ t) (qaKick F m q μ ψ θ φ ρ x) x := by
    intro x hx
    rw [Set.uIcc_of_le h01] at hx
    have := (helicalMomentum_hasDerivAt_on hm hq hG 0 1 h
      ⟨h0.trans hx.1, hx.2.trans h1T⟩).neg
    convert this using 1
    simp only [qaKick, symmetryDefect, along]
    ring
  have hint : IntervalIntegrable (qaKick F m q μ ψ θ φ ρ) MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h01]
    exact qaKick_continuousOn h h0 h1T hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [helicalMomentum]
  ring

/-- At a turning point (`v_∥ = 0`) with `B ≠ 0`, the parallel gyroradius vanishes. -/
theorem rho_eq_zero_of_turning (hm : m ≠ 0) (hq : q ≠ 0) {t : ℝ}
    (hB : along F.B ψ θ φ t ≠ 0) (hv : parallelVelocity F m q ψ θ φ ρ t = 0) : ρ t = 0 := by
  unfold parallelVelocity at hv
  rcases mul_eq_zero.mp (div_eq_zero_iff.mp hv |>.resolve_right hm) with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' hq
    · exact h''
  · exact absurd h' hB

/-- **Per-bounce step** (target T1). Between two turning points `t₀ ≤ t₁` of an orbit on
`[0, T]` (`v_∥ = 0` at both, `B > 0` there), the orbit-width term cancels:
`q (ψ_p(ψ t₁) − ψ_p(ψ t₀)) = ∫_{t₀}^{t₁} (q²ρ²B/m + μ) ∂_φB dt`. The turning points are
hypotheses; nothing is assumed about the motion in between. -/
theorem bounce_psip_step (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t₀ t₁ : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc t₀ t₁))
    (hB₀ : 0 < along F.B ψ θ φ t₀) (hB₁ : 0 < along F.B ψ θ φ t₁)
    (hv₀ : parallelVelocity F m q ψ θ φ ρ t₀ = 0) (hv₁ : parallelVelocity F m q ψ θ φ ρ t₁ = 0) :
    q * (F.ψp (ψ t₁) - F.ψp (ψ t₀)) = ∫ t in t₀..t₁, qaKick F m q μ ψ θ φ ρ t := by
  rw [psip_step hm hq hG h h0 h01 h1T hc, rho_eq_zero_of_turning hm hq hB₀.ne' hv₀,
    rho_eq_zero_of_turning hm hq hB₁.ne' hv₁]
  ring

/-- **Exact QA bounce** (`∂_φB ≡ 0` on `ψ > 0`). Inside the bounce the flux excursion is pure
orbit width, `q (ψ_p(ψ t) − ψ_p(ψ t₀)) = q G ρ(t)` for `t ∈ [t₀, t₁]` (`ρ(t₀) = 0`), and at the
next turning point the orbit returns to the same `ψ_p`. -/
theorem bounce_psip_step_exactQA (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T t₀ t₁ : ℝ}
    (hQA : ∀ x θ φ, 0 < x → F.Bφ x θ φ = 0)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hB₀ : 0 < along F.B ψ θ φ t₀) (hB₁ : 0 < along F.B ψ θ φ t₁)
    (hv₀ : parallelVelocity F m q ψ θ φ ρ t₀ = 0) (hv₁ : parallelVelocity F m q ψ θ φ ρ t₁ = 0) :
    (∀ t ∈ Set.Icc t₀ t₁, q * (F.ψp (ψ t) - F.ψp (ψ t₀)) = q * F.G * ρ t) ∧
      F.ψp (ψ t₁) = F.ψp (ψ t₀) := by
  have hzero : ∀ s ∈ Set.Icc t₀ t₁, along F.Bφ ψ θ φ s = 0 := fun s hs =>
    hQA _ _ _ (h.pos s ⟨h0.trans hs.1, hs.2.trans h1T⟩)
  have hρ₀ := rho_eq_zero_of_turning hm hq hB₀.ne' hv₀
  have step : ∀ t ∈ Set.Icc t₀ t₁, q * (F.ψp (ψ t) - F.ψp (ψ t₀)) = q * F.G * ρ t := by
    intro t ht
    have hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc t₀ t) :=
      (continuousOn_const (c := (0 : ℝ))).congr fun s hs => hzero s ⟨hs.1, hs.2.trans ht.2⟩
    rw [psip_step hm hq hG h h0 ht.1 (ht.2.trans h1T) hc, hρ₀]
    have : ∫ s in t₀..t, qaKick F m q μ ψ θ φ ρ s = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [Set.uIcc_of_le ht.1] at hs
        simp only [qaKick, hzero s ⟨hs.1, hs.2.trans ht.2⟩, mul_zero]
    rw [this]; ring
  refine ⟨step, ?_⟩
  have := step t₁ ⟨h01, le_rfl⟩
  rw [rho_eq_zero_of_turning hm hq hB₁.ne' hv₁, mul_zero] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq)

/-- **Near-QA per-bounce bound.** Between turning points, if `B ≥ B_min > 0` and `|∂_φB| ≤ ε`
along the orbit, then `|q (ψ_p(ψ t₁) − ψ_p(ψ t₀))| ≤ (2H(0)/B_min) ε (t₁ − t₀)`. -/
theorem bounce_psip_step_le (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {T t₀ t₁ Bmin ε : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc t₀ t₁)) (hBmin : 0 < Bmin)
    (hB : ∀ s ∈ Set.Icc t₀ t₁, Bmin ≤ along F.B ψ θ φ s)
    (hξ : ∀ s ∈ Set.Icc t₀ t₁, |along F.Bφ ψ θ φ s| ≤ ε)
    (hv₀ : parallelVelocity F m q ψ θ φ ρ t₀ = 0) (hv₁ : parallelVelocity F m q ψ θ φ ρ t₁ = 0) :
    |q * (F.ψp (ψ t₁) - F.ψp (ψ t₀))| ≤
      2 * boozerEnergy F m q μ ψ θ φ ρ 0 / Bmin * ε * (t₁ - t₀) := by
  have hB₀ := hBmin.trans_le (hB t₀ ⟨le_rfl, h01⟩)
  have hB₁ := hBmin.trans_le (hB t₁ ⟨h01, le_rfl⟩)
  rw [bounce_psip_step hm.ne' hq hG h h0 h01 h1T hc hB₀ hB₁ hv₀ hv₁]
  have hb : ∀ s ∈ Set.uIoc t₀ t₁, ‖qaKick F m q μ ψ θ φ ρ s‖ ≤
      2 * boozerEnergy F m q μ ψ θ φ ρ 0 / Bmin * ε := by
    intro s hs
    rw [Set.uIoc_of_le h01] at hs
    have hs' : s ∈ Set.Icc t₀ t₁ := ⟨hs.1.le, hs.2⟩
    have hsT : s ∈ Set.Icc 0 T := ⟨h0.trans hs'.1, hs'.2.trans h1T⟩
    obtain ⟨r0, r1⟩ := momentum_rate_le (q := q) (ρ := ρ s) hm hμ hBmin (hB s hs')
    have hE := boozerEnergy_eq_on hm.ne' hq hG h hsT
    unfold boozerEnergy at hE
    rw [hE] at r1
    rw [Real.norm_eq_abs, qaKick, abs_mul, abs_of_nonneg r0]
    exact mul_le_mul r1 (hξ s hs') (abs_nonneg _) (r0.trans r1)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h01)] at this
  exact this

/-- **Sum over consecutive bounces.** If `τ` is monotone, `0 ≤ τ 0`, `τ N ≤ T`, every `τ k`
(`k ≤ N`) is a turning point with `B > 0`, and `∂_φB` is continuous along the orbit, then
`q (ψ_p(ψ(τ N)) − ψ_p(ψ(τ 0))) = Σ_{k<N} ∫_{τ k}^{τ (k+1)} (q²ρ²B/m + μ) ∂_φB dt`. -/
theorem sum_bounce_psip (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T : ℝ} {τ : ℕ → ℝ} {N : ℕ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0) (hNT : τ N ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc 0 T))
    (hB : ∀ k ≤ N, 0 < along F.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity F m q ψ θ φ ρ (τ k) = 0) :
    q * (F.ψp (ψ (τ N)) - F.ψp (ψ (τ 0))) =
      ∑ k ∈ Finset.range N, ∫ t in τ k..τ (k + 1), qaKick F m q μ ψ θ φ ρ t := by
  rw [← Finset.sum_range_sub (fun k => F.ψp (ψ (τ k))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have h1T : τ (k + 1) ≤ T := (hτ (by omega : k + 1 ≤ N)).trans hNT
  exact bounce_psip_step hm hq hG h (h0.trans (hτ (Nat.zero_le k))) (hτ (Nat.le_succ k)) h1T
    (hc.mono (Set.Icc_subset_Icc (h0.trans (hτ (Nat.zero_le k))) h1T))
    (hB k hk'.le) (hB (k + 1) hk') (hv k hk'.le) (hv (k + 1) hk')

/-! ## Discrete averaging -/

/-- Telescoping identity: `2 sin(α/2) Σ_{k<N} sin(kα + β) = cos(β − α/2) − cos(Nα + β − α/2)`. -/
theorem two_sin_mul_sum_sin (α β : ℝ) (N : ℕ) :
    2 * sin (α / 2) * ∑ k ∈ Finset.range N, sin (k * α + β) =
      cos (β - α / 2) - cos (N * α + β - α / 2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e2 : ((n + 1 : ℕ) * α + β - α / 2) = (n * α + β) + α / 2 := by push_cast; ring
    have key : ∀ y x : ℝ, 2 * sin x * sin y = cos (y - x) - cos (y + x) := fun y x => by
      rw [cos_sub, cos_add]; ring
    rw [e2, key]
    ring

/-- **Discrete averaging lemma.** If `sin(α/2) ≠ 0` (the phase advance `α` per step is not a
multiple of `2π`), then `|Σ_{k<N} sin(kα + β)| ≤ 1/|sin(α/2)|`, uniformly in `N` and `β`. -/
theorem abs_sum_sin_arith_le (α β : ℝ) (hα : sin (α / 2) ≠ 0) (N : ℕ) :
    |∑ k ∈ Finset.range N, sin (k * α + β)| ≤ 1 / |sin (α / 2)| := by
  have hs : 0 < |sin (α / 2)| := abs_pos.mpr hα
  rw [le_div_iff₀ hs]
  have e := two_sin_mul_sum_sin α β N
  have : |2 * sin (α / 2) * ∑ k ∈ Finset.range N, sin (k * α + β)| ≤ 2 := by
    rw [e]
    have := abs_sub (cos (β - α / 2)) (cos (N * α + β - α / 2))
    linarith [abs_cos_le_one (β - α / 2), abs_cos_le_one (N * α + β - α / 2)]
  rw [abs_mul, abs_mul, abs_two] at this
  linarith

/-- **Non-resonant kicks do not drift secularly.** If `|Δ_k − A sin(kα + β)| ≤ R` for `k < N`
and `sin(α/2) ≠ 0`, then `|Σ_{k<N} Δ_k| ≤ |A|/|sin(α/2)| + N R`. -/
theorem abs_sum_kicks_le {Δ : ℕ → ℝ} {A α β R : ℝ} (hα : sin (α / 2) ≠ 0) (N : ℕ)
    (hΔ : ∀ k < N, |Δ k - A * sin (k * α + β)| ≤ R) :
    |∑ k ∈ Finset.range N, Δ k| ≤ |A| / |sin (α / 2)| + N * R := by
  have e : ∑ k ∈ Finset.range N, Δ k =
      A * ∑ k ∈ Finset.range N, sin (k * α + β) +
        ∑ k ∈ Finset.range N, (Δ k - A * sin (k * α + β)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h1 : |A * ∑ k ∈ Finset.range N, sin (k * α + β)| ≤ |A| / |sin (α / 2)| := by
    rw [abs_mul, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left (abs_sum_sin_arith_le α β hα N) (abs_nonneg _)
  have h2 : |∑ k ∈ Finset.range N, (Δ k - A * sin (k * α + β))| ≤ N * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range N, |Δ k - A * sin (k * α + β)|
        ≤ ∑ _k ∈ Finset.range N, R :=
          Finset.sum_le_sum fun k hk => hΔ k (Finset.mem_range.mp hk)
      _ = N * R := by simp
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **Bounded secular drift of a trapped orbit over `N` bounces (conditional).** Let
`τ 0 ≤ … ≤ τ N` be turning points of an orbit on `[0, T]` (QA helicity). **Assume** the
per-bounce kick integrals have the leading-order form
`|∫_{τ k}^{τ(k+1)} (q²ρ²B/m + μ) ∂_φB dt − A sin(kα + β)| ≤ R` (the bounce-averaged defect with
toroidal phase advancing by `α` per bounce, remainder `R`), and non-resonance
`sin(α/2) ≠ 0`. Then `|q| |ψ_p(ψ(τ N)) − ψ_p(ψ(τ 0))| ≤ |A|/|sin(α/2)| + N R`. -/
theorem bounce_drift_nonresonant (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T A α β R : ℝ}
    {τ : ℕ → ℝ} {N : ℕ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0) (hNT : τ N ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Set.Icc 0 T))
    (hB : ∀ k ≤ N, 0 < along F.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity F m q ψ θ φ ρ (τ k) = 0)
    (hα : sin (α / 2) ≠ 0)
    (hkick : ∀ k < N,
      |(∫ t in τ k..τ (k + 1), qaKick F m q μ ψ θ φ ρ t) - A * sin (k * α + β)| ≤ R) :
    |q| * |F.ψp (ψ (τ N)) - F.ψp (ψ (τ 0))| ≤ |A| / |sin (α / 2)| + N * R := by
  rw [← abs_mul, sum_bounce_psip hm hq hG h hτ h0 hNT hc hB hv]
  exact abs_sum_kicks_le hα N hkick

/-! ## Sanity checks -/

/-- Sanity: with `α = π` the sine sum `Σ_{k<N} sin(kπ + π/2) = Σ (−1)^k` is bounded by `1`, the
lemma's bound `1/|sin(π/2)| = 1`. -/
theorem abs_sum_sin_pi_le (N : ℕ) :
    |∑ k ∈ Finset.range N, sin (k * π + π / 2)| ≤ 1 := by
  have := abs_sum_sin_arith_le π (π / 2) (by rw [sin_pi_div_two]; norm_num) N
  rwa [sin_pi_div_two, abs_one, div_one] at this

/-- Sanity (resonance is a genuine exclusion): with `α = 2π` and `β = π/2` every term equals
`1`, so the sum is `N` and grows without bound; the hypothesis `sin(α/2) ≠ 0` fails. -/
theorem sum_sin_resonant (N : ℕ) :
    ∑ k ∈ Finset.range N, sin (k * (2 * π) + π / 2) = N ∧ sin (2 * π / 2) = 0 := by
  constructor
  · have : ∀ k : ℕ, sin (k * (2 * π) + π / 2) = 1 := fun k => by
      rw [add_comm, show (k : ℝ) * (2 * π) = (k : ℤ) * (2 * π) by push_cast; ring,
        sin_add_int_mul_two_pi, sin_pi_div_two]
    simp [this]
  · rw [show 2 * π / 2 = π by ring, sin_pi]

/-- Sanity for the band lemma: an exactly conserved `I` with `ψ = f(I)` exactly (`δ = w = 0`)
keeps `ψ` constant. -/
theorem band_exact {I ψ f : ℝ → ℝ} {L t₀ : ℝ} (hL : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hI : ∀ t, I t = I t₀) (hψ : ∀ t, ψ t = f (I t)) (t : ℝ) : ψ t = ψ t₀ := by
  have := band_of_approx_first_integral (I := I) (ψ := ψ) (S := Set.univ) (δ := 0) (w := 0) hL
    (Set.mem_univ t₀)
    (fun t _ => by simp [hI t]) (fun t _ => by simp [hψ t]) t (Set.mem_univ t)
  simp only [mul_zero, add_zero] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

end PlasmaLean.Kinetic.Boozer
