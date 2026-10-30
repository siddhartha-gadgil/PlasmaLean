/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Omnigeneity in the Boozer guiding-centre model, and quasisymmetry ⇒ omnigeneity (Q-23)

Research note: `notes/theory/omnigeneity-bridge.md` (N-29); question Q-23 (clause C2 of the
stellarator contract). Everything is about the vacuum Boozer guiding-centre **model** of
`Theory/Kinetic/BoozerGuidingCentre` (supplied equations of motion, supplied orbits, chart
`ψ > 0`), not about the Lorentz force or a physical field.

## Definitions

* `IsBounce ρ τ`: `τ > 0` is a **bounce period** of a trajectory that starts at a turning point:
  the parallel gyroradius `ρ = m v_∥/(qB)` vanishes at `0`, at an intermediate time `σ` and at
  `τ`, and has opposite signs on the two legs `(0, σ)` and `(σ, τ)` (one full banana: out along
  one leg, back along the other). `IsBounce.unique`: the bounce period is determined by `ρ`.
  Starting at time `0` loses nothing, since the model is autonomous.
* `TrappedBounce F m q μ c ψ θ φ ρ τ`: an orbit on `[0, τ]` with bounce period `τ` that stays in
  the region `0 < ψ ≤ c` (the **radial bounce map** is `ψ(0) ↦ ψ(τ)`).
* `bounceAvgDrift ψ τ = (ψ(τ) − ψ(0))/τ`, equal to the time average `τ⁻¹ ∫₀^τ ψ̇` of the radial
  drift `radialDrift` (`bounceAvgDrift_eq_avg_radialDrift`, when `ψ̇` is continuous).
* `OmnigenousOn F c`: for every species (`m > 0`, `q ≠ 0`), every `μ ≥ 0` and every trapped
  bounce in the region, `ψ(τ) = ψ(0)`: zero net radial displacement per bounce, i.e. zero
  bounce-averaged radial drift (`omnigenousOn_iff_bounceAvgDrift`).
* `ApproxOmnigenousOn F c κ`: `|ψ(τ) − ψ(0)| ≤ κ (H/|q|) τ` per bounce; the case `κ = 0` is
  omnigeneity (`omnigenousOn_iff_approx_zero`).
* `TwistOn F N M c ι_min`: `ι_min |x − y| ≤ |f(x) − f(y)|` for `f(x) = N x − M ψ_p(x)` on
  `(0, c]` (for QA, `f = −ψ_p`, implied by `ι ≥ ι_min`: `twistOn_qa_of_iota_ge`).

## Theorems

* `psi_return_of_QS` (exact): `ξB ≡ 0` on the region and `f` injective there; then for every
  orbit on `[0, τ]` in the region with `ρ(τ) = ρ(0)`, `ψ(τ) = ψ(0)`. Proof: the helical momentum
  `P = q (f(ψ) + M G ρ)` is conserved and the correction `M G ρ` returns.
  `omnigenousOn_of_exactQS`: an exactly quasisymmetric Boozer field is omnigenous.
* `psi_drift_le_of_defect` (quantitative): if `B ≥ B_min > 0`, `|ξB| ≤ δ` on the region and
  the twist holds, then `|ψ(τ) − ψ(0)| ≤ 2 H(0)/(|q| B_min ι_min) · δ · τ` whenever
  `ρ(τ) = ρ(0)`. `bounce_psi_drift_le` (per bounce), `bounceAvgDrift_le` (bounce average
  `≤ 2H δ/(|q| B_min ι_min)`), `approxOmnigenousOn_of_defect_le` (`κ = 2δ/(B_min ι_min)`).

## Sanity

* degenerate: `constField_omnigenousOn` (constant `B`);
* counterexample: `driftMirror k` (`B = 1 + φ² + k sin θ`, `ι = 0`, `G = 1`) with the explicit
  orbit `dmψ, dmθ, dmφ, dmρ` (`m = q = 1`, `μ = 3/2`, energy `H = 2`): `dm_isBounce` (a full
  bounce of period `π`), `dm_displacement` (`ψ(π) − ψ(0) = −2πk`), `driftMirror_not_omnigenous`
  for `0 < k ≤ 1/2`. The displacement is linear in the defect amplitude `k`, so the linear
  dependence on `δ` of the quantitative theorem cannot be improved; `driftMirror_zero_omnigenous`
  is the symmetric member `k = 0`;
* `dm_quantitative_check`: the quantitative theorem applies to the drifting bounce (non-vacuous)
  and gives `8πk` against the actual `2πk`;
* `IsBounce.unique`, `omnigenousOn_iff_approx_zero`, `isBounce_dm_fixture`.

Concrete instances (`exactQA` omnigenous, a numerical bound for `reactorQA`) are in
`Design/NearAxisQAOmnigeneity`.

**Not done here**: the connection to the effective ripple `ε_eff` and `1/ν` transport (needs the
bounce-averaged drift as a function on velocity space and a collision model), existence of
trapped bounces for a given field (here they are supplied), and the identification of the Boozer
`ξB` with the Cartesian `qsError` of `Fields.WeakQS`.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Kinetic Real Set

/-! ## Bounce periods -/

/-- `τ` is a **bounce period** of a trajectory with parallel gyroradius `ρ` starting at a
turning point (`ρ(0) = 0`): there is an intermediate turning point `σ ∈ (0, τ)`, `ρ(τ) = 0`, and
`ρ` has opposite (nonzero) signs on the two legs `(0, σ)` and `(σ, τ)`. -/
@[expose] def IsBounce (ρ : ℝ → ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ ρ 0 = 0 ∧ ρ τ = 0 ∧
    ∃ σ ∈ Ioo 0 τ, ρ σ = 0 ∧ ∀ s ∈ Ioo 0 σ, ∀ t ∈ Ioo σ τ, ρ s * ρ t < 0

/-- On the legs of a bounce the parallel gyroradius does not vanish. -/
theorem legs_ne_zero {ρ : ℝ → ℝ} {τ σ : ℝ} (hσ : σ ∈ Ioo 0 τ)
    (hopp : ∀ s ∈ Ioo 0 σ, ∀ t ∈ Ioo σ τ, ρ s * ρ t < 0) :
    (∀ s ∈ Ioo 0 σ, ρ s ≠ 0) ∧ ∀ t ∈ Ioo σ τ, ρ t ≠ 0 := by
  have ht : (σ + τ) / 2 ∈ Ioo σ τ := ⟨by linarith [hσ.2], by linarith [hσ.2]⟩
  have hs : σ / 2 ∈ Ioo 0 σ := ⟨by linarith [hσ.1], by linarith [hσ.1]⟩
  refine ⟨fun s hs' h0 => ?_, fun t ht' h0 => ?_⟩
  · have := hopp s hs' _ ht; rw [h0, zero_mul] at this; exact lt_irrefl _ this
  · have := hopp _ hs t ht'; rw [h0, mul_zero] at this; exact lt_irrefl _ this

/-- **Uniqueness of the bounce period**: `τ` is determined by `ρ` (it is the second zero of `ρ`
after `0`). -/
theorem IsBounce.unique {ρ : ℝ → ℝ} {τ τ' : ℝ} (h : IsBounce ρ τ) (h' : IsBounce ρ τ') :
    τ = τ' := by
  obtain ⟨hτ, -, hτ0, σ, hσ, hσ0, hopp⟩ := h
  obtain ⟨hτ', -, hτ0', σ', hσ', hσ0', hopp'⟩ := h'
  obtain ⟨l1, l2⟩ := legs_ne_zero hσ hopp
  obtain ⟨l1', l2'⟩ := legs_ne_zero hσ' hopp'
  have hσσ : σ = σ' := by
    rcases lt_trichotomy σ σ' with hlt | heq | hgt
    · exact absurd hσ0 (l1' σ ⟨hσ.1, hlt⟩)
    · exact heq
    · exact absurd hσ0' (l1 σ' ⟨hσ'.1, hgt⟩)
  subst hσσ
  rcases lt_trichotomy τ τ' with hlt | heq | hgt
  · exact absurd hτ0 (l2' τ ⟨hσ.2, hlt⟩)
  · exact heq
  · exact absurd hτ0' (l2 τ' ⟨hσ'.2, hgt⟩)

/-- A bounce returns the parallel gyroradius to its initial value. -/
theorem IsBounce.rho_return {ρ : ℝ → ℝ} {τ : ℝ} (h : IsBounce ρ τ) : ρ τ = ρ 0 := by
  rw [h.2.1, h.2.2.1]

/-- A bounce period is positive. -/
theorem IsBounce.pos {ρ : ℝ → ℝ} {τ : ℝ} (h : IsBounce ρ τ) : 0 < τ := h.1

/-! ## Omnigeneity -/

variable {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- A **trapped bounce in the region** `0 < ψ ≤ c`: an orbit on `[0, τ]` with bounce period `τ`
(`IsBounce`) that stays at `ψ ≤ c`. The radial bounce map is `ψ(0) ↦ ψ(τ)`. -/
structure TrappedBounce (F : BoozerField) (m q μ c : ℝ) (ψ θ φ ρ : ℝ → ℝ) (τ : ℝ) : Prop where
  /-- The guiding-centre equations hold on `[0, τ]` (and `ψ > 0` there). -/
  orbit : BoozerGCOrbitOn F m q μ ψ θ φ ρ τ
  /-- `τ` is a bounce period. -/
  bounce : IsBounce ρ τ
  /-- The orbit stays in the region `ψ ≤ c` during the bounce. -/
  inRegion : ∀ t ∈ Icc 0 τ, ψ t ≤ c

/-- Bounce-averaged radial drift `(ψ(τ) − ψ(0))/τ`. -/
@[expose] def bounceAvgDrift (ψ : ℝ → ℝ) (τ : ℝ) : ℝ := (ψ τ - ψ 0) / τ

/-- The radial drift `ψ̇ = −(mμ + q²ρ²B) ∂_θB/(mq)` along a trajectory. -/
@[expose] def radialDrift (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  -(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) * along F.Bθ ψ θ φ t / (m * q)

/-- **Omnigeneity** on the region `0 < ψ ≤ c` (Boozer guiding-centre model): for every species
(`m > 0`, `q ≠ 0`), every magnetic moment `μ ≥ 0` and every trapped bounce in the region (any
energy), the flux label returns after one bounce period. -/
@[expose] def OmnigenousOn (F : BoozerField) (c : ℝ) : Prop :=
  ∀ (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (τ : ℝ), 0 < m → q ≠ 0 → 0 ≤ μ →
    TrappedBounce F m q μ c ψ θ φ ρ τ → ψ τ = ψ 0

/-- **Approximate omnigeneity** with constant `κ`: the radial displacement per bounce is at most
`κ (H(0)/|q|) τ` (`H/q` is the energy per charge, so `κ` is dimensionless). -/
@[expose] def ApproxOmnigenousOn (F : BoozerField) (c κ : ℝ) : Prop :=
  ∀ (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (τ : ℝ), 0 < m → q ≠ 0 → 0 ≤ μ →
    TrappedBounce F m q μ c ψ θ φ ρ τ →
      |ψ τ - ψ 0| ≤ κ * (boozerEnergy F m q μ ψ θ φ ρ 0 / |q|) * τ

/-- Omnigeneity is approximate omnigeneity with `κ = 0`. -/
theorem omnigenousOn_iff_approx_zero {c : ℝ} : OmnigenousOn F c ↔ ApproxOmnigenousOn F c 0 := by
  constructor
  · intro h m q μ ψ θ φ ρ τ hm hq hμ hb
    rw [h m q μ ψ θ φ ρ τ hm hq hμ hb]; simp
  · intro h m q μ ψ θ φ ρ τ hm hq hμ hb
    have := h m q μ ψ θ φ ρ τ hm hq hμ hb
    rw [zero_mul, zero_mul] at this
    exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- Omnigeneity is the vanishing of the bounce-averaged radial drift. -/
theorem omnigenousOn_iff_bounceAvgDrift {c : ℝ} : OmnigenousOn F c ↔
    ∀ (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (τ : ℝ), 0 < m → q ≠ 0 → 0 ≤ μ →
      TrappedBounce F m q μ c ψ θ φ ρ τ → bounceAvgDrift ψ τ = 0 := by
  refine forall_congr' fun m => forall_congr' fun q => forall_congr' fun μ => forall_congr'
    fun ψ => forall_congr' fun θ => forall_congr' fun φ => forall_congr' fun ρ =>
      forall_congr' fun τ => forall_congr' fun _ => forall_congr' fun _ => forall_congr'
        fun _ => forall_congr' fun hb => ?_
  have hτ := hb.bounce.pos.ne'
  rw [bounceAvgDrift, div_eq_zero_iff, sub_eq_zero]
  exact ⟨Or.inl, fun h => h.resolve_right hτ⟩

/-- The bounce average is the time average of the velocity (fundamental theorem of calculus). -/
theorem bounceAvgDrift_eq_average {ψ v : ℝ → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (hd : ∀ t ∈ Icc 0 τ, HasDerivAt ψ (v t) t) (hv : ContinuousOn v (Icc 0 τ)) :
    bounceAvgDrift ψ τ = τ⁻¹ * ∫ t in (0 : ℝ)..τ, v t := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by rwa [uIcc_of_le hτ] at ht)) (hv.intervalIntegrable_of_Icc hτ),
    bounceAvgDrift, div_eq_inv_mul]

/-- Along an orbit, the bounce average is the time average of the radial drift `ψ̇`. -/
theorem bounceAvgDrift_eq_avg_radialDrift {τ : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ τ)
    (hτ : 0 ≤ τ) (hc : ContinuousOn (radialDrift F m q μ ψ θ φ ρ) (Icc 0 τ)) :
    bounceAvgDrift ψ τ = τ⁻¹ * ∫ t in (0 : ℝ)..τ, radialDrift F m q μ ψ θ φ ρ t :=
  bounceAvgDrift_eq_average hτ (fun t ht => h.dψ t ht) hc

/-! ## Twist -/

/-- **Twist** on `(0, c]` for helicity `(N, M)`: `ι_min |x − y| ≤ |f(x) − f(y)|` with
`f(x) = N x − M ψ_p(x)` (the flux part of the helical momentum). -/
@[expose] def TwistOn (F : BoozerField) (N M c ιmin : ℝ) : Prop :=
  ∀ x ∈ Ioc 0 c, ∀ y ∈ Ioc 0 c,
    ιmin * |x - y| ≤ |(N * x - M * F.ψp x) - (N * y - M * F.ψp y)|

/-- A positive twist makes `f` injective on `(0, c]`. -/
theorem TwistOn.injOn {N M c ιmin : ℝ} (h : TwistOn F N M c ιmin) (hι : 0 < ιmin) :
    InjOn (fun x => N * x - M * F.ψp x) (Ioc 0 c) := by
  intro x hx y hy hxy
  have := h x hx y hy
  simp only at hxy
  rw [hxy, sub_self, abs_zero] at this
  have h0 : |x - y| ≤ 0 := by nlinarith [abs_nonneg (x - y)]
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

/-- **QA twist from the rotational transform**: if `ι ≥ ι_min` on `(0, c]`, then
`ι_min |x − y| ≤ |ψ_p(x) − ψ_p(y)|` there (mean value theorem). -/
theorem twistOn_qa_of_iota_ge {c ιmin : ℝ} (hι : ∀ x ∈ Ioc 0 c, ιmin ≤ F.ι x) :
    TwistOn F 0 1 c ιmin := by
  have key : ∀ x ∈ Ioc 0 c, ∀ y ∈ Ioc 0 c, y < x → ιmin * (x - y) ≤ F.ψp x - F.ψp y := by
    intro x hx y hy hyx
    have hcont : ContinuousOn F.ψp (Icc y x) := fun t ht =>
      (F.hasDerivAt_ψp t (hy.1.trans_le ht.1)).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F.ψp F.ι hyx hcont
      (fun t ht => F.hasDerivAt_ψp t (hy.1.trans ht.1))
    have hιξ := hι ξ ⟨hy.1.trans hξ.1, hξ.2.le.trans hx.2⟩
    have hpos : 0 < x - y := sub_pos.mpr hyx
    rw [eq_div_iff hpos.ne'] at hslope
    rw [← hslope]
    exact mul_le_mul_of_nonneg_right hιξ hpos.le
  intro x hx y hy
  simp only [zero_mul, one_mul, zero_sub, sub_neg_eq_add]
  rcases lt_trichotomy y x with hlt | heq | hgt
  · rw [abs_of_pos (sub_pos.mpr hlt), show -F.ψp x + F.ψp y = -(F.ψp x - F.ψp y) by ring,
      abs_neg]
    exact (key x hx y hy hlt).trans (le_abs_self _)
  · subst heq; simp
  · rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hgt),
      show -F.ψp x + F.ψp y = F.ψp y - F.ψp x by ring]
    exact (key y hy x hx hgt).trans (le_abs_self _)

/-! ## Exact quasisymmetry ⇒ omnigeneity -/

/-- The helical momentum is conserved along an orbit on `[0, T]` that stays in a region where
`ξB = 0`. -/
theorem helicalMomentum_eq_of_QS_on (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {N M c T t : ℝ}
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hc : ∀ s ∈ Icc 0 T, ψ s ≤ c)
    (ht : t ∈ Icc 0 T) :
    helicalMomentum F q N M ψ ρ t = helicalMomentum F q N M ψ ρ 0 := by
  have := invariant_drift (ε := 0)
    (fun s hs => helicalMomentum_hasDerivAt_on hm hq hG N M h hs)
    (fun s hs => by rw [hQS _ _ _ (h.pos s hs) (hc s hs), mul_zero, abs_zero]) ht
  rw [zero_mul] at this
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

/-- Helical-momentum difference when `ρ` returns: `P(τ) − P(0) = q (f(ψ(τ)) − f(ψ(0)))`. -/
theorem helicalMomentum_sub_of_rho_return {N M τ : ℝ} (hρ : ρ τ = ρ 0) :
    helicalMomentum F q N M ψ ρ τ - helicalMomentum F q N M ψ ρ 0 =
      q * ((N * ψ τ - M * F.ψp (ψ τ)) - (N * ψ 0 - M * F.ψp (ψ 0))) := by
  unfold helicalMomentum; rw [hρ]; ring

/-- **Exact theorem (return of the flux label).** If `ξB = 0` on `0 < ψ ≤ c` and
`f(x) = N x − M ψ_p(x)` is injective on `(0, c]`, then every orbit on `[0, τ]` that stays in the
region and has `ρ(τ) = ρ(0)` (in particular one full bounce) has `ψ(τ) = ψ(0)`. -/
theorem psi_return_of_QS (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {N M c τ : ℝ}
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (hinj : InjOn (fun x => N * x - M * F.ψp x) (Ioc 0 c))
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ τ) (hτ : 0 ≤ τ) (hc : ∀ t ∈ Icc 0 τ, ψ t ≤ c)
    (hρ : ρ τ = ρ 0) : ψ τ = ψ 0 := by
  have hτm : τ ∈ Icc 0 τ := ⟨hτ, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ⟩
  have hP := sub_eq_zero.mpr (helicalMomentum_eq_of_QS_on hm hq hG hQS h hc hτm)
  rw [helicalMomentum_sub_of_rho_return hρ] at hP
  have hf := sub_eq_zero.mp ((mul_eq_zero.mp hP).resolve_left hq)
  exact hinj ⟨h.pos τ hτm, hc τ hτm⟩ ⟨h.pos 0 h0, hc 0 h0⟩ hf

/-- **Quasisymmetry ⇒ omnigeneity (exact).** An exactly quasisymmetric Boozer field (`ξB = 0` on
`0 < ψ ≤ c`, the hypothesis of `helicalMomentum_conserved`) with `f(x) = N x − M ψ_p(x)`
injective on `(0, c]` is omnigenous on the region. -/
theorem omnigenousOn_of_exactQS (hG : F.G ≠ 0) {N M c : ℝ}
    (hQS : ∀ x θ φ, 0 < x → x ≤ c → symmetryDefect F N M x θ φ = 0)
    (hinj : InjOn (fun x => N * x - M * F.ψp x) (Ioc 0 c)) : OmnigenousOn F c :=
  fun _ _ _ _ _ _ _ _ hm hq _ hb =>
    psi_return_of_QS hm.ne' hq hG hQS hinj hb.orbit hb.bounce.pos.le hb.inRegion
      hb.bounce.rho_return

/-! ## Quantitative theorem: symmetry defect `≤ δ` -/

/-- **Quantitative theorem.** On the region `0 < ψ ≤ c` let `B ≥ B_min > 0`, `|ξB| ≤ δ` and the
twist `TwistOn F N M c ι_min` hold, `ι_min > 0`. Then every orbit on `[0, τ]` (`m > 0`,
`q ≠ 0`, `μ ≥ 0`) that stays in the region and has `ρ(τ) = ρ(0)` satisfies
`|ψ(τ) − ψ(0)| ≤ 2 H(0)/(|q| B_min ι_min) · δ · τ`. -/
theorem psi_drift_le_of_defect (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c τ Bmin δ ιmin : ℝ} (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ τ) (hτ : 0 ≤ τ)
    (hc : ∀ t ∈ Icc 0 τ, ψ t ≤ c) (hBmin : 0 < Bmin) (hι : 0 < ιmin)
    (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ δ)
    (htw : TwistOn F N M c ιmin) (hρ : ρ τ = ρ 0) :
    |ψ τ - ψ 0| ≤ 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / (|q| * Bmin * ιmin) * δ * τ := by
  have hτm : τ ∈ Icc 0 τ := ⟨hτ, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc 0 τ := ⟨le_rfl, hτ⟩
  have hdrift := helicalMomentum_drift_le hm hq hG hμ (N := N) (M := M) (ε := δ) h hBmin hτ
    (fun s hs => hBlow _ _ _ (h.pos s hs) (hc s hs))
    (fun s hs => hξ _ _ _ (h.pos s hs) (hc s hs))
  rw [helicalMomentum_sub_of_rho_return hρ, abs_mul] at hdrift
  have htw' := htw (ψ τ) ⟨h.pos τ hτm, hc τ hτm⟩ (ψ 0) ⟨h.pos 0 h0, hc 0 h0⟩
  have hqp : 0 < |q| := abs_pos.mpr hq
  have e : 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / (|q| * Bmin * ιmin) * δ * τ =
      2 * boozerEnergy F m q μ ψ θ φ ρ 0 / Bmin * δ * τ / (|q| * ιmin) := by
    field_simp
  rw [e, le_div_iff₀ (mul_pos hqp hι)]
  calc |ψ τ - ψ 0| * (|q| * ιmin) = |q| * (ιmin * |ψ τ - ψ 0|) := by ring
    _ ≤ |q| * |N * ψ τ - M * F.ψp (ψ τ) - (N * ψ 0 - M * F.ψp (ψ 0))| :=
        mul_le_mul_of_nonneg_left htw' hqp.le
    _ ≤ _ := hdrift

/-- **Per-bounce bound**: over one bounce period of a trapped bounce in the region,
`|ψ(τ) − ψ(0)| ≤ 2 H(0)/(|q| B_min ι_min) · δ · τ`. -/
theorem bounce_psi_drift_le (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c τ Bmin δ ιmin : ℝ} (hb : TrappedBounce F m q μ c ψ θ φ ρ τ) (hBmin : 0 < Bmin)
    (hι : 0 < ιmin) (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ δ)
    (htw : TwistOn F N M c ιmin) :
    |ψ τ - ψ 0| ≤ 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / (|q| * Bmin * ιmin) * δ * τ :=
  psi_drift_le_of_defect hm hq hG hμ hb.orbit hb.bounce.pos.le hb.inRegion hBmin hι hBlow hξ
    htw hb.bounce.rho_return

/-- **Bounce-averaged drift bound**: `|(ψ(τ) − ψ(0))/τ| ≤ 2 H(0) δ/(|q| B_min ι_min)`. -/
theorem bounceAvgDrift_le (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : 0 ≤ μ)
    {N M c τ Bmin δ ιmin : ℝ} (hb : TrappedBounce F m q μ c ψ θ φ ρ τ) (hBmin : 0 < Bmin)
    (hι : 0 < ιmin) (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ δ)
    (htw : TwistOn F N M c ιmin) :
    |bounceAvgDrift ψ τ| ≤ 2 * boozerEnergy F m q μ ψ θ φ ρ 0 / (|q| * Bmin * ιmin) * δ := by
  have hτ := hb.bounce.pos
  rw [bounceAvgDrift, abs_div, abs_of_pos hτ, div_le_iff₀ hτ]
  exact bounce_psi_drift_le hm hq hG hμ hb hBmin hι hBlow hξ htw

/-- **Quasisymmetry defect ⇒ approximate omnigeneity**, with `κ = 2δ/(B_min ι_min)`. -/
theorem approxOmnigenousOn_of_defect_le (hG : F.G ≠ 0) {N M c Bmin δ ιmin : ℝ}
    (hBmin : 0 < Bmin) (hι : 0 < ιmin) (hBlow : ∀ x θ φ, 0 < x → x ≤ c → Bmin ≤ F.B x θ φ)
    (hξ : ∀ x θ φ, 0 < x → x ≤ c → |symmetryDefect F N M x θ φ| ≤ δ)
    (htw : TwistOn F N M c ιmin) : ApproxOmnigenousOn F c (2 * δ / (Bmin * ιmin)) := by
  intro m q μ ψ θ φ ρ _ hm hq hμ hb
  have := bounce_psi_drift_le hm hq hG hμ hb hBmin hι hBlow hξ htw
  have hqp : 0 < |q| := abs_pos.mpr hq
  convert this using 1
  field_simp

/-! ## Sanity: degenerate case -/

/-- **Degenerate case**: a constant field strength is omnigenous on every region (helicity
`(1, 0)`, for which `f(x) = x`). -/
theorem constField_omnigenousOn {B₀ ι₀ G : ℝ} (hG : G ≠ 0) (c : ℝ) :
    OmnigenousOn (constField B₀ ι₀ G) c :=
  omnigenousOn_of_exactQS (N := 1) (M := 0) hG
    (fun x θ φ _ _ => symmetryDefect_zero_of_const B₀ ι₀ G 1 0 x θ φ)
    (fun x _ y _ hxy => by simpa using hxy)

/-! ## Sanity: a non-omnigenous field with an explicit bounce orbit -/

/-- Counterexample field: `B = 1 + φ² + k sin θ` (a mirror well in `φ` plus a poloidal
variation of amplitude `k`), `ψ_p = 0`, `ι = 0`, `G = 1`. Its symmetry defect for helicity
`(1, 0)` is `∂_θB = k cos θ`. A model object, not a stellarator (no rotational transform). -/
@[expose] def driftMirror (k : ℝ) : BoozerField where
  B _ θ φ := 1 + φ ^ 2 + k * sin θ
  Bψ _ _ _ := 0
  Bθ _ θ _ := k * cos θ
  Bφ _ _ φ := 2 * φ
  ψp _ := 0
  ι _ := 0
  G := 1
  hasFDerivAt_B p _ := by
    have hy : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_snd.fst
    have hz : HasFDerivAt (fun p : ℝ × ℝ × ℝ => p.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      hasFDerivAt_snd.snd
    have hall := ((hasFDerivAt_const (1 : ℝ) p).add (hz.pow 2)).add (hy.sin.const_mul k)
    convert hall using 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_comp,
      Function.comp_apply, gradCLM_apply, Pi.add_apply]
    simp
    ring
  hasDerivAt_ψp x _ := hasDerivAt_const x 0

/-- The auxiliary amplitude `D(t) = √(1 − cos²(2t)/4)` of the explicit orbit. -/
@[expose] def dmD (t : ℝ) : ℝ := √(1 - cos (2 * t) ^ 2 / 4)

/-- `D(t)² = 1 − cos²(2t)/4`. -/
theorem dmD_sq (t : ℝ) : dmD t ^ 2 = 1 - cos (2 * t) ^ 2 / 4 :=
  sq_sqrt (by nlinarith [cos_sq_le_one (2 * t)])

/-- `D(t) > 0`. -/
theorem dmD_pos (t : ℝ) : 0 < dmD t :=
  sqrt_pos.mpr (by nlinarith [cos_sq_le_one (2 * t)])

/-- `Ḋ = sin(2t) cos(2t)/(2D)`. -/
theorem dmD_hasDerivAt (t : ℝ) :
    HasDerivAt dmD (sin (2 * t) * cos (2 * t) / (2 * dmD t)) t := by
  have hc := ((hasDerivAt_id t).const_mul 2).cos
  have hg := ((hc.pow 2).div_const 4).const_sub 1
  have hne : 1 - cos (2 * t) ^ 2 / 4 ≠ 0 := by nlinarith [cos_sq_le_one (2 * t)]
  refine (hg.sqrt hne).congr_deriv ?_
  simp only [id, Pi.pow_apply]
  unfold dmD
  field_simp
  ring

/-- Explicit orbit, flux: `ψ(t) = 10 − k (2t − sin(4t)/8)`. -/
@[expose] def dmψ (k t : ℝ) : ℝ := 10 - k * (2 * t - sin (4 * t) / 8)
/-- Explicit orbit, poloidal angle: `θ ≡ 0`. -/
@[expose] def dmθ (_t : ℝ) : ℝ := 0
/-- Explicit orbit, toroidal angle: `φ(t) = cos(2t)/(2 D(t))`. -/
@[expose] def dmφ (t : ℝ) : ℝ := cos (2 * t) / (2 * dmD t)
/-- Explicit orbit, parallel gyroradius: `ρ(t) = −sin(2t) D(t)`. -/
@[expose] def dmρ (t : ℝ) : ℝ := -(sin (2 * t) * dmD t)

/-- Along the orbit `B = 1/D²`. -/
theorem dm_B (k t : ℝ) : along (driftMirror k).B (dmψ k) dmθ dmφ t = 1 / dmD t ^ 2 := by
  have hD := dmD_pos t
  have h2 := dmD_sq t
  simp only [along, driftMirror, dmθ, dmφ, sin_zero, mul_zero, add_zero]
  field_simp
  rw [h2]; ring

/-- `sin²(2t) + cos²(2t) = 1` in the form used below. -/
theorem dm_sc (t : ℝ) : sin (2 * t) ^ 2 + cos (2 * t) ^ 2 = 1 := sin_sq_add_cos_sq _

/-- **The explicit orbit solves the guiding-centre equations** (`m = q = 1`, `μ = 3/2`) on
`[0, π]` for `0 ≤ k ≤ 1/2`. -/
theorem dm_orbit {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2) :
    BoozerGCOrbitOn (driftMirror k) 1 1 (3 / 2) (dmψ k) dmθ dmφ dmρ π where
  pos t ht := by
    have hs := neg_one_le_sin (4 * t)
    have hπ := pi_le_four
    unfold dmψ
    nlinarith [ht.2, ht.1]
  dψ t _ := by
    have h1 := ((hasDerivAt_id t).const_mul 2)
    have h2 := ((hasDerivAt_id t).const_mul 4).sin.div_const 8
    refine (((h1.sub h2).const_mul k).const_sub 10).congr_deriv ?_
    rw [dm_B]
    have hD := dmD_pos t
    have hD2 := dmD_sq t
    have hc4 : cos (4 * t) = 1 - 2 * sin (2 * t) ^ 2 := by
      rw [show 4 * t = 2 * (2 * t) by ring, cos_two_mul]; linarith [dm_sc t]
    simp only [driftMirror, along, dmθ, dmρ, cos_zero, id, hc4]
    field_simp
    ring
  dθ t _ := by
    refine (hasDerivAt_const t (0 : ℝ)).congr_deriv ?_
    simp [driftMirror, along]
  dφ t _ := by
    have hD := dmD_pos t
    have hD2 := dmD_sq t
    refine (((hasDerivAt_id t).const_mul 2).cos.div ((dmD_hasDerivAt t).const_mul 2)
      (by positivity)).congr_deriv ?_
    rw [dm_B]
    simp only [driftMirror, dmρ, id]
    field_simp
    linear_combination (-4 * sin (2 * t)) * hD2
  dρ t _ := by
    have hD := dmD_pos t
    have hD2 := dmD_sq t
    refine ((((hasDerivAt_id t).const_mul 2).sin.mul (dmD_hasDerivAt t)).neg).congr_deriv ?_
    rw [dm_B]
    simp only [driftMirror, along, dmθ, dmφ, dmρ, id]
    field_simp
    linear_combination (-4 * cos (2 * t)) * hD2 + (cos (2 * t)) * dm_sc t

/-- The explicit orbit performs one **full bounce** of period `π`: turning points at `0`,
`π/2`, `π`, with `ρ < 0` on `(0, π/2)` and `ρ > 0` on `(π/2, π)`. -/
theorem dm_isBounce : IsBounce dmρ π := by
  refine ⟨pi_pos, by simp [dmρ], ?_, π / 2, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩,
    ?_, ?_⟩
  · simp [dmρ, sin_two_pi]
  · simp [dmρ, show 2 * (π / 2) = π by ring]
  · intro s hs t ht
    have h1 : 0 < sin (2 * s) := sin_pos_of_pos_of_lt_pi (by linarith [hs.1])
      (by linarith [hs.2])
    have h2 : sin (2 * t) < 0 := by
      have : 0 < sin (2 * t - π) := sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
        (by linarith [ht.2])
      rw [sin_sub_pi] at this; linarith
    have hDs := dmD_pos s
    have hDt := dmD_pos t
    simp only [dmρ]
    have : 0 < sin (2 * s) * dmD s * (-(sin (2 * t)) * dmD t) :=
      mul_pos (mul_pos h1 hDs) (mul_pos (neg_pos.mpr h2) hDt)
    nlinarith

/-- The orbit stays in the region `ψ ≤ 11` on `[0, π]` (`0 ≤ k ≤ 1/2`). -/
theorem dm_inRegion {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2) : ∀ t ∈ Icc 0 π, dmψ k t ≤ 11 := by
  intro t ht
  have := sin_le_one (4 * t)
  unfold dmψ
  nlinarith [ht.1]

/-- **Net radial displacement over the bounce**: `ψ(π) − ψ(0) = −2πk`. -/
theorem dm_displacement (k : ℝ) : dmψ k π - dmψ k 0 = -(2 * π * k) := by
  have : sin (4 * π) = 0 := by
    rw [show 4 * π = ((4 : ℕ) : ℝ) * π by norm_num]; exact sin_nat_mul_pi 4
  simp [dmψ, this]
  ring

/-- The explicit trapped bounce of `driftMirror k` in the region `ψ ≤ 11`. -/
theorem dm_trappedBounce {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2) :
    TrappedBounce (driftMirror k) 1 1 (3 / 2) 11 (dmψ k) dmθ dmφ dmρ π :=
  ⟨dm_orbit hk0 hk, dm_isBounce, dm_inRegion hk0 hk⟩

/-- **Counterexample**: for `0 < k ≤ 1/2` the field `driftMirror k` is **not** omnigenous on any
region `ψ ≤ c` with `c ≥ 11`. -/
theorem driftMirror_not_omnigenous {k c : ℝ} (hk0 : 0 < k) (hk : k ≤ 1 / 2) (hc : 11 ≤ c) :
    ¬ OmnigenousOn (driftMirror k) c := by
  intro h
  have hb := dm_trappedBounce hk0.le hk
  have := h 1 1 (3 / 2) _ _ _ _ π one_pos one_ne_zero (by norm_num)
    ⟨hb.orbit, hb.bounce, fun t ht => (hb.inRegion t ht).trans hc⟩
  have hd := dm_displacement k
  rw [this, sub_self] at hd
  nlinarith [pi_pos]

/-- The symmetric member `k = 0` of the counterexample family is omnigenous (its `∂_θB`
vanishes, helicity `(1, 0)`). -/
theorem driftMirror_zero_omnigenous (c : ℝ) : OmnigenousOn (driftMirror 0) c :=
  omnigenousOn_of_exactQS (N := 1) (M := 0) one_ne_zero
    (fun x θ φ _ _ => by simp [symmetryDefect, driftMirror])
    (fun x _ y _ hxy => by simpa using hxy)

/-- The explicit orbit has energy `H = 2` (`ρ(0) = 0`, `B(0) = 4/3`, `μ = 3/2`). -/
theorem dm_energy (k : ℝ) : boozerEnergy (driftMirror k) 1 1 (3 / 2) (dmψ k) dmθ dmφ dmρ 0 = 2 := by
  have h2 := dmD_sq 0
  have hD := dmD_pos 0
  simp only [mul_zero, cos_zero] at h2
  simp only [boozerEnergy, dm_B, dmρ, mul_zero, sin_zero, zero_mul, neg_zero]
  rw [h2]; norm_num

/-- **Non-vacuity and sharpness of the quantitative theorem.** Applied to the explicit drifting
bounce (helicity `(1, 0)`, `δ = k`, `B_min = 1/2`, `ι_min = 1`, `H = 2`) the theorem gives
`|ψ(π) − ψ(0)| ≤ 8πk`, while the actual displacement is `2πk` (`dm_displacement`): the bound is
attained up to the factor `4`, and both are linear in the defect amplitude `k`. -/
theorem dm_quantitative_check {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2) :
    |dmψ k π - dmψ k 0| ≤ 8 * π * k ∧ |dmψ k π - dmψ k 0| = 2 * π * k := by
  have hb := dm_trappedBounce hk0 hk
  refine ⟨?_, ?_⟩
  · have := bounce_psi_drift_le (N := 1) (M := 0) (Bmin := 1 / 2) (δ := k) (ιmin := 1)
      one_pos one_ne_zero one_ne_zero (by norm_num) hb (by norm_num) one_pos
      (fun x θ φ _ _ => by
        have := neg_one_le_sin θ
        simp only [driftMirror]; nlinarith [sq_nonneg φ])
      (fun x θ φ _ _ => by
        simp only [symmetryDefect, driftMirror, zero_mul, add_zero, one_mul, abs_mul,
          abs_of_nonneg hk0]
        nlinarith [abs_cos_le_one θ])
      (fun x _ y _ => by simp)
    rw [dm_energy] at this
    convert this using 1
    norm_num; ring
  · rw [dm_displacement, abs_neg, abs_of_nonneg (by positivity)]

/-- Fixture: the bounce period of the explicit orbit is exactly `π` (no other period). -/
theorem isBounce_dm_fixture {τ : ℝ} (h : IsBounce dmρ τ) : τ = π := h.unique dm_isBounce

end PlasmaLean.Kinetic.Boozer
