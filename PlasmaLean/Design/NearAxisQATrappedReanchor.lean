/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedPeriodic
public import PlasmaLean.Theory.Kinetic.BounceShear

/-!
# Trapped 3.5 MeV alphas: all-time (exact QA), finite-time (near QA), re-anchored bounce map

Companion to `notes/theory/trapped-alpha-status.md`. Model only: the reactor near-axis QA family
(`reactorQA`, `exactQA = qaField 0`) in the vacuum Boozer guiding-centre model
(`Kinetic.BoozerGuidingCentre`); orbits are supplied. Pitch window: tip field
`E/μ ∈ [5.4, 5.5] T` (`μ ∈ [muLo, muHi]`), moderately deep bananas.

Results:

* `exactQA_trapped_confined_forever`: **exact QA confines trapped alphas for all time.** Every
  all-time exact-QA orbit of the pitch window starting at a turning point with
  `ψ(0) ∈ [4.75, 5.79] T m²` stays in `ψ ∈ [ψ_lo, ψ_a]` with `|ρ| ≤ 1.77 cm` for every `t ≥ 0`.
  This is `exactQA_band` (momentum conservation, `boozerGC_trapped` with the trapped orbit width
  `Δρ = ρ_max`) restated for `BoozerGCOrbit`; `boozerGC_trapped` covers trapped particles because
  it only uses `|ρ(t) − ρ(0)| ≤ Δρ`.
* `reactorQA_trapped_confined_until`: **unconditional near-QA confinement time.** In `reactorQA`
  (`ε_QS(a) = 2.49 × 10⁻³ T`) every orbit of the pitch window starting at a turning point with
  `ψ(0) ≤ 5 T m²` stays at `ψ ≤ 8.23 < ψ_a` for `0 ≤ t ≤ 1.8 × 10⁻⁴ s` (about three simulated
  bounce periods of `6.5 × 10⁻⁵ s`). `reactorQA_trapped_band_until`: two-sided band
  `ψ ∈ [ψ_lo, ψ_a]` for `ψ(0) ∈ [5.2, 5.3]` and `t ≤ 10⁻⁴ s`. These use the worst-case linear
  momentum drift; the time is short because the trapped orbit width `G ρ_max/ι₀ ≈ 2.44 T m²`
  uses up most of the room.
* `reference_kick_decomp`: every exact-QA reference bounce of the start window (as produced by
  re-anchoring at a tip) has precession `Δ ∈ [0.7, 2.6]`, `|sin Δ| ≥ 1/2`, and its `sin 2φ`
  kick is exactly `C sin 2φ(0) + S cos 2φ(0)` with `|C / sin Δ|, |S / sin Δ| ≤ 2 ∫₀ᴾ |g|`. These are
  the data `(C k, S k, Δ k, dC k, dS k)` of the abstract re-anchored scheme.
* `reactorQA_trapped_reanchored`: **re-anchored N-bounce bound** for `reactorQA`. Along the
  upper turning points `τ k`, if the actual kick over `[τ k, τ (k+1)]` is within `R` of the fresh
  reference kick, the actual precession within `e` of `2Δ k`, and the reference data shear by at
  most `σ` (precession) and `γ` (amplitude) from one anchor to the next, all **while the anchors
  stay in the start window**, then the anchors stay in `[4.75, 5.79]` for all `k ≤ N` provided
  `2M + N (R + γ + M (e + σ)) + (2M + R) ≤ min (ψ(0) − 4.75) (5.79 − ψ(0))`, and
  `|ψ(τ k) − ψ(0)| ≤ 2M + k (R + γ + M (e + σ))`.
* `reanchored_budget_simulated`: with untrusted RK4 values of the per-bounce constants
  (`scripts/trapped_reanchor/reanchor_sim.py`: `R ≤ 2.1 × 10⁻⁴`, `γ ≤ 7 × 10⁻⁴`,
  `M ≤ 0.023 T m²`, `e ≤ 0.0141`, `σ ≤ 0.0076`) the gap closes for `N = 300` bounces from
  `ψ(0) = 5.27`, i.e. about `0.02 s`. **The constants `R, e, σ, γ` are not proved.**

**Not proved** (see the status note): the one-bounce remainders `R` and `e` (a Lipschitz–Grönwall
comparison is useless here: the reduced field has Lipschitz constant `≈ 4.5 × 10⁸ s⁻¹` in the
`(ψ, θ, ρ)` sup norm, so `e^{K P}` is astronomically large over one bounce) and the shears
`σ, γ` (Lipschitz dependence of the exact-QA bounce on the anchor, a cell-certificate target).
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQATrappedReanchor
open PlasmaLean.Kinetic.Boozer PlasmaLean.Kinetic.BounceShear PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce PlasmaLean.Design.NearAxisQATrappedResonance
  PlasmaLean.Design.NearAxisQATrappedPeriodic Real Set

/-! ## Exact QA: all time -/

/-- **Trapped alphas are confined for all time in exact QA** (model). An all-time exact-QA
guiding-centre orbit with `E = 3.5 MeV`, tip field `E/μ ∈ [5.4, 5.5] T`, starting at a turning
point (`ρ(0) = 0`) with `ψ(0) ∈ [4.75, 5.79] T m²`, satisfies `ψ(t) ∈ [ψ_lo, ψ_a]` and
`|ρ(t)| ≤ 1.77 cm` for every `t ≥ 0`. -/
theorem exactQA_trapped_confined_forever {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbit exactQA mα qα μ ψ θ φ ρ)
    (hE : boozerEnergy exactQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0)
    (hψ0 : ψ 0 ∈ Icc (475 / 100) (579 / 100)) (t : ℝ) (ht : 0 ≤ t) :
    ψ t ∈ Icc psiLo psiEdge ∧ |ρ t| ≤ rhoMax :=
  exactQA_band hμ (h.on t) hE hρ0 hψ0 t ⟨ht, le_rfl⟩

/-! ## Near QA: unconditional finite time -/

/-- `reactorQA` is the member `b₁ = −4.3 × 10⁻⁴` of the family, and `|b₁| ≤ 4.3 × 10⁻⁴`. -/
theorem reactorQA_b₁ : |(-43 / 100000 : ℝ)| ≤ 43 / 100000 := by norm_num [abs_of_neg]

/-- The symmetry defect of `reactorQA` is at most `ε_QS(a) = 0.0024854 T` on `0 < ψ ≤ ψ_a`. -/
theorem reactorQA_defect_le {x θ φ : ℝ} (hx : 0 < x) (hxc : x ≤ psiEdge) :
    |symmetryDefect reactorQA 0 1 x θ φ| ≤ 0.0024854 := by
  have := nearAxis_symmetryDefect_le (η := -7 / 100) (b₀ := -137 / 10000)
    (b₁ := -43 / 100000) (B₂c := 33 / 2000) (ι₀ := 211 / 500) (G := 581 / 10) (θ := θ)
    (φ := φ) (by norm_num : (0 : ℝ) < 57 / 10) hx.le (radius_le_edge hxc)
  refine this.trans (le_of_eq ?_)
  norm_num [abs_of_neg]

/-- Gyroradius bound along a `reactorQA` orbit of the pitch window, wherever `ψ ≤ ψ_a`. -/
theorem reactorQA_abs_rho_le {μ T t : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) (ht : t ∈ Icc 0 T)
    (hψt : ψ t ≤ psiEdge) : |ρ t| ≤ rhoMax := by
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hG : reactorQA.G ≠ 0 := by rw [reactorQA_eq, qaField_G]; norm_num
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have W := qaField_window reactorQA_b₁ hμ
  exact abs_rho_le_of_energy hm hq hμ0.le (by norm_num) (by norm_num [rhoMax])
    (qaField_B_ge reactorQA_b₁ (h.pos t ht).le hψt (θ t) (φ t))
    (energy_along hm.ne' hq hG h hE ht) W.rho_bound

/-- Upper confinement for `reactorQA` orbits of the pitch window, starting at a turning point
with `ψ(0) ≤ ψ_s`, on `[0, T]`, provided the gap `G ρ_max + (2E/(q B_min)) ε_QS T ≤ ι₀ (8.23 − ψ_s)`
holds (`T ≥ 0`). -/
theorem reactorQA_upper {μ T ψs : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0) (hψ0 : ψ 0 ≤ ψs)
    (hT : 0 ≤ T) (hgap : 581 / 10 * rhoMax + 2 * Eα / (|qα| * (493 / 100)) * 0.0024854 * T ≤
      211 / 500 * (823 / 100 - ψs)) :
    ∀ t ∈ Icc 0 T, ψ t ≤ 823 / 100 := by
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hG : reactorQA.G ≠ 0 := by rw [reactorQA_eq, qaField_G]; norm_num
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hψs : ψs < 823 / 100 := by
    have : 0 < 581 / 10 * rhoMax := by norm_num [rhoMax]
    have : 0 ≤ 2 * Eα / (|qα| * (493 / 100)) * 0.0024854 * T := by
      have : (0 : ℝ) ≤ 2 * Eα / (|qα| * (493 / 100)) * 0.0024854 := by
        norm_num [Eα, qα, abs_of_pos]
      positivity
    nlinarith
  refine boozerGC_trapped_until (N := 0) (M := 1) (c := psiEdge) (c' := 823 / 100)
    (ιmin := 211 / 500) (Bmin := 493 / 100) (ε := 0.0024854) (Δρ := rhoMax) hm hq hG hμ0.le h
    (by norm_num [psiEdge]) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (fun x θ φ hx hxc => qaField_B_ge reactorQA_b₁ hx.le hxc θ φ)
    (fun x θ φ hx hxc => reactorQA_defect_le hx hxc)
    (fun x hx _ => by
      have hp : ∀ y, reactorQA.ψp y = 211 / 500 * y := fun _ => rfl
      rw [hp, hp, le_abs]; right; linarith)
    (fun t ht hhist => by
      rw [hρ0, sub_zero]; exact reactorQA_abs_rho_le hμ h hE ht (hhist t ⟨ht.1, le_rfl⟩))
    ?_
  rw [hE, show reactorQA.G = 581 / 10 from rfl]
  have : 211 / 500 * (823 / 100 - ψs) ≤ 211 / 500 * (823 / 100 - ψ 0) := by linarith
  have e1 : |(1 : ℝ) * (581 / 10)| = 581 / 10 := by norm_num
  rw [e1]
  linarith

/-- **Unconditional confinement time of trapped alphas in `reactorQA`.** Every guiding-centre
orbit (on `[0, 1.8 × 10⁻⁴ s]`) of the model with `E = 3.5 MeV`, tip field `E/μ ∈ [5.4, 5.5] T`,
starting at a turning point with `ψ(0) ≤ 5 T m²` (`r₀ ≤ 1.32 m`), satisfies
`ψ(t) ≤ 8.23 T m² < ψ_a` (`r < a`) and `|ρ(t)| ≤ 1.77 cm` for `0 ≤ t ≤ 1.8 × 10⁻⁴ s`. -/
theorem reactorQA_trapped_confined_until {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ 1.8e-4)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0) (hψ0 : ψ 0 ≤ 5) :
    ∀ t ∈ Icc 0 1.8e-4, ψ t ≤ 823 / 100 ∧ |ρ t| ≤ rhoMax := by
  have hup := reactorQA_upper hμ h hE hρ0 hψ0 (by norm_num)
    (by norm_num [rhoMax, Eα, qα, abs_of_pos])
  intro t ht
  have hψt := hup t ht
  exact ⟨hψt, reactorQA_abs_rho_le hμ h hE ht (hψt.trans (by norm_num [psiEdge]))⟩

/-- **Two-sided band for `reactorQA`.** As `reactorQA_trapped_confined_until`, for starts
`ψ(0) ∈ [5.2, 5.3] T m²` and `0 ≤ t ≤ 10⁻⁴ s`: `ψ(t) ∈ [ψ_lo, ψ_a]` and `|ρ(t)| ≤ 1.77 cm`
(the band on which the bounce window `qaField_window` holds). -/
theorem reactorQA_trapped_band_until {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : μ ∈ Icc muLo muHi)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ 1e-4)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) (hρ0 : ρ 0 = 0)
    (hψ0 : ψ 0 ∈ Icc (52 / 10) (53 / 10)) :
    ∀ t ∈ Icc 0 1e-4, ψ t ∈ Icc psiLo psiEdge ∧ |ρ t| ≤ rhoMax := by
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hqp : (0 : ℝ) < qα := by norm_num [qα]
  have hG : reactorQA.G ≠ 0 := by rw [reactorQA_eq, qaField_G]; norm_num
  have hμ0 : 0 < μ := muLo_pos.trans_le hμ.1
  have hup := reactorQA_upper hμ h hE hρ0 hψ0.2 (by norm_num)
    (by norm_num [rhoMax, Eα, qα, abs_of_pos])
  intro t ht
  have hψt : ψ t ≤ psiEdge := (hup t ht).trans (by norm_num [psiEdge])
  have hρt := reactorQA_abs_rho_le hμ h hE ht hψt
  refine ⟨⟨?_, hψt⟩, hρt⟩
  -- lower side: momentum drift
  have hdrift := helicalMomentum_drift_le hm hq hG hμ0.le (N := 0) (M := 1)
    (Bmin := 493 / 100) (ε := 0.0024854) (h.mono ht.2) (by norm_num) ht.1
    (fun s hs => qaField_B_ge reactorQA_b₁ (h.pos s ⟨hs.1, hs.2.trans ht.2⟩).le
      ((hup s ⟨hs.1, hs.2.trans ht.2⟩).trans (by norm_num [psiEdge])) _ _)
    (fun s hs => reactorQA_defect_le (h.pos s ⟨hs.1, hs.2.trans ht.2⟩)
      ((hup s ⟨hs.1, hs.2.trans ht.2⟩).trans (by norm_num [psiEdge])))
  rw [hE] at hdrift
  have e1 : helicalMomentum reactorQA qα 0 1 ψ ρ t - helicalMomentum reactorQA qα 0 1 ψ ρ 0 =
      qα * (211 / 500 * (ψ 0 - ψ t) + 581 / 10 * ρ t) := by
    simp only [helicalMomentum, show reactorQA.ψp = fun y => 211 / 500 * y from rfl,
      show reactorQA.G = 581 / 10 from rfl, hρ0]
    ring
  rw [e1, abs_mul, abs_of_pos hqp] at hdrift
  have hk : 2 * Eα / (493 / 100) * 0.0024854 * t ≤ qα * (1765 / 10000) := by
    have : 2 * Eα / (493 / 100) * 0.0024854 * t ≤ 2 * Eα / (493 / 100) * 0.0024854 * 1e-4 := by
      have : (0 : ℝ) ≤ 2 * Eα / (493 / 100) * 0.0024854 := by norm_num [Eα]
      exact mul_le_mul_of_nonneg_left ht.2 this
    refine this.trans ?_
    norm_num [Eα, qα]
  have h1 : 211 / 500 * (ψ 0 - ψ t) + 581 / 10 * ρ t ≤ 1765 / 10000 := by
    have := (abs_le.mp (le_of_mul_le_mul_left (hdrift.trans hk) hqp)).2
    linarith
  have h2 := (abs_le.mp hρt).1
  unfold psiLo
  unfold rhoMax at h2
  nlinarith [hψ0.1]

/-! ## The exact-QA reference bounce in kick form -/

/-- **Reference data of a re-anchored bounce.** For an exact-QA reference orbit of the start
window (`Setup` on `[0, T]`, `T ≥ 1.6 ms`), there is a bounce period `0 < P ≤ 1.6 ms` with
precession `Δ = φ(P) − φ(0) ∈ [0.7, 2.6]`, `|sin Δ| ≥ 1/2`, and with
`g = refAmp b₁ μ ψ θ ρ`, `C = ∫₀ᴾ g cos 2(φ − φ(0))`, `S = ∫₀ᴾ g sin 2(φ − φ(0))`:

* the reference kick is `∫₀ᴾ g sin 2φ = C sin 2φ(0) + S cos 2φ(0)`;
* `|C / sin Δ| ≤ 2 ∫₀ᴾ |g|` and `|S / sin Δ| ≤ 2 ∫₀ᴾ |g|`.

So `(C, S, Δ, C / sin Δ, S / sin Δ)` are admissible data `(C k, S k, Δ k, dC k, dS k)` of the
re-anchored scheme with `M = 2 ∫₀ᴾ |g|`. -/
theorem reference_kick_decomp (b₁ : ℝ) {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ P ≤ 2 * Lhalf ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) ∧
      1 / 2 ≤ |sin (φ P - φ 0)| ∧
      (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t)) =
        (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) * sin (2 * φ 0) +
          (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) * cos (2 * φ 0) ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| := by
  obtain ⟨P, hP0, hP, hφ, hsin, -⟩ := exactQA_reference_bounce S hT
  refine ⟨P, hP0, hP, hφ, hsin, ?_⟩
  have hPT : P ≤ T := hP.trans hT
  have hsub : Icc 0 P ⊆ Icc 0 T := Icc_subset_Icc le_rfl hPT
  have hψc := S.cont_psi.mono hsub
  have hθc := S.cont_theta.mono hsub
  have hρc := S.cont_rho.mono hsub
  have hφc : ContinuousOn φ (Icc 0 P) :=
    fun t ht => (S.orbit.dφ t (hsub ht)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn (refAmp b₁ μ ψ θ ρ) (Icc 0 P) := by
    have hB : ContinuousOn (fun t => Bf (ψ t) (θ t)) (Icc 0 P) := by
      unfold Bf
      have hc := continuous_cos.comp_continuousOn hθc
      exact (continuousOn_const.sub ((continuousOn_const.mul
        (continuousOn_const.mul hψc).sqrt).mul hc)).add
        ((continuousOn_const.mul hψc).mul (continuousOn_const.add
          (continuousOn_const.mul (hc.pow 2))))
    unfold refAmp
    exact ((((((continuousOn_const.mul (hρc.pow 2)).mul hB).div_const _).add
      continuousOn_const).mul ((continuousOn_const.mul hψc).div_const _)).mul
        continuousOn_const).neg
  have hcosc : ContinuousOn (fun t => cos (2 * (φ t - φ 0))) (Icc 0 P) :=
    continuous_cos.comp_continuousOn (continuousOn_const.mul (hφc.sub continuousOn_const))
  have hsinc : ContinuousOn (fun t => sin (2 * (φ t - φ 0))) (Icc 0 P) :=
    continuous_sin.comp_continuousOn (continuousOn_const.mul (hφc.sub continuousOn_const))
  have hu : Set.uIcc 0 P = Icc 0 P := uIcc_of_le hP0.le
  have hI1 : IntervalIntegrable (fun t => refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0)))
      MeasureTheory.volume 0 P := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hgc.mul hcosc
  have hI2 : IntervalIntegrable (fun t => refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0)))
      MeasureTheory.volume 0 P := by
    apply ContinuousOn.intervalIntegrable; rw [hu]; exact hgc.mul hsinc
  have hs0 : 0 < |sin (φ P - φ 0)| := by linarith
  have habs : ∀ f : ℝ → ℝ, (∀ t, |f t| ≤ 1) → ContinuousOn f (Icc 0 P) →
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * f t) / sin (φ P - φ 0)| ≤
        2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| := by
    intro f hf _
    rw [abs_div, div_le_iff₀ hs0]
    have h1 : |∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * f t| ≤
        ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| := by
      refine (intervalIntegral.abs_integral_le_integral_abs hP0.le).trans ?_
      apply intervalIntegral.integral_mono_on hP0.le
      · apply ContinuousOn.intervalIntegrable
        rw [hu]
        exact (hgc.mul ‹ContinuousOn f (Icc 0 P)›).abs
      · apply ContinuousOn.intervalIntegrable; rw [hu]; exact hgc.abs
      · intro t _
        rw [abs_mul]
        have := hf t
        nlinarith [abs_nonneg (refAmp b₁ μ ψ θ ρ t), abs_nonneg (f t)]
    have h2 : 0 ≤ ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| :=
      intervalIntegral.integral_nonneg hP0.le (fun t _ => abs_nonneg _)
    nlinarith
  refine ⟨?_, habs _ (fun t => abs_cos_le_one _) hcosc, habs _ (fun t => abs_sin_le_one _) hsinc⟩
  have e : ∀ t, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t) =
      refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0)) * sin (2 * φ 0) +
        refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0)) * cos (2 * φ 0) := by
    intro t
    have : 2 * φ t = 2 * φ 0 + 2 * (φ t - φ 0) := by ring
    rw [this, sin_add]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_add (hI1.mul_const _) (hI2.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

/-! ## The re-anchored N-bounce bound for `reactorQA` -/

/-- **Re-anchored bounce map for trapped alphas in `reactorQA`** (conditional on the one-bounce
remainders and the shears). Let `τ 0 = 0 ≤ τ 1 ≤ … ≤ τ N ≤ T` be turning points (`v_∥ = 0`,
`B > 0`) of a `reactorQA` orbit on `[0, T]`. Write `ψ_k = ψ(τ k)`, `φ_k = φ(τ k)`. Suppose that
while the anchors `ψ_0, …, ψ_k` lie in the exact-QA start window `[4.75, 5.79]`:

* the kick over `[τ k, τ (k+1)]`, divided by `q ι₀`, is within `R` of
  `C k sin 2φ_k + S k cos 2φ_k`, with `C k = dC k sin Δ k`, `S k = dS k sin Δ k`,
  `|dC k|, |dS k| ≤ M` (for the fresh exact-QA reference at the anchor these data exist with
  `|sin Δ k| ≥ 1/2`: `reference_kick_decomp`);
* for consecutive anchors, `|2φ_{k+1} − 2φ_k − 2Δ k| ≤ e`, `|Δ (k+1) − Δ k| ≤ σ`,
  `|dC (k+1) − dC k|, |dS (k+1) − dS k| ≤ γ`.

If `2M + N (R + γ + M (e + σ)) + (2M + R) ≤ min (ψ(0) − 4.75) (5.79 − ψ(0))`, then every anchor
`ψ_k`, `k ≤ N`, stays in `[4.75, 5.79]` and `|ψ_k − ψ(0)| ≤ 2M + k (R + γ + M (e + σ))`. -/
theorem reactorQA_trapped_reanchored {μ T R M γ e σ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {τ : ℕ → ℝ} {N : ℕ}
    {C S Δ dC dS : ℕ → ℝ}
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : τ 0 = 0)
    (hNT : τ N ≤ T) (hB : ∀ k ≤ N, 0 < along reactorQA.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity reactorQA mα qα ψ θ φ ρ (τ k) = 0)
    (hstep : ∀ k < N, (∀ j ≤ k, ψ (τ j) ∈ Icc (475 / 100) (579 / 100)) →
      |(∫ t in τ k..τ (k + 1), qaKick reactorQA mα qα μ ψ θ φ ρ t) / (qα * (211 / 500)) -
          (C k * sin (2 * φ (τ k)) + S k * cos (2 * φ (τ k)))| ≤ R ∧
        C k = dC k * sin (Δ k) ∧ S k = dS k * sin (Δ k) ∧ |dC k| ≤ M ∧ |dS k| ≤ M)
    (hpair : ∀ k, k + 1 < N → (∀ j ≤ k + 1, ψ (τ j) ∈ Icc (475 / 100) (579 / 100)) →
      |2 * φ (τ (k + 1)) - 2 * φ (τ k) - 2 * Δ k| ≤ e ∧ |Δ (k + 1) - Δ k| ≤ σ ∧
        |dC (k + 1) - dC k| ≤ γ ∧ |dS (k + 1) - dS k| ≤ γ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    (hgap : 2 * M + N * (R + γ + M * (e + σ)) + (2 * M + R) ≤
      min (ψ 0 - 475 / 100) (579 / 100 - ψ 0)) :
    ∀ k ≤ N, ψ (τ k) ∈ Icc (475 / 100) (579 / 100) ∧
      |ψ (τ k) - ψ 0| ≤ 2 * M + k * (R + γ + M * (e + σ)) := by
  have hm : mα ≠ 0 := by norm_num [mα]
  have hq : qα ≠ 0 := by norm_num [qα]
  have hqι : qα * (211 / 500) ≠ 0 := by norm_num [qα]
  -- the flux step between consecutive tips is the kick divided by `q ι₀`
  have hjump : ∀ k < N, ψ (τ (k + 1)) - ψ (τ k) =
      (∫ t in τ k..τ (k + 1), qaKick reactorQA mα qα μ ψ θ φ ρ t) / (qα * (211 / 500)) := by
    intro k hk
    have h0k : 0 ≤ τ k := by rw [← h0]; exact hτ (Nat.zero_le k)
    have h1T : τ (k + 1) ≤ T := (hτ (by omega : k + 1 ≤ N)).trans hNT
    have := reactorQA_bounce_step hm hq h h0k (hτ (Nat.le_succ k)) h1T (hB k hk.le)
      (hB (k + 1) hk) (hv k hk.le) (hv (k + 1) hk)
    rw [eq_div_iff hqι, ← this]; ring
  have hψ00 : ψ (τ 0) = ψ 0 := by rw [h0]
  have key := reanchored_band (y := fun k => ψ (τ k)) (φ := fun k => φ (τ k)) (C := C) (S := S)
    (Δ := Δ) (dC := dC) (dS := dS) (R := R) (M := M) (γ := γ) (e := e) (σ := σ)
    (D := 2 * M + R) (lo := 475 / 100) (hi := 579 / 100) N
    (fun k hk hin => by
      obtain ⟨hk1, hC, hS, hMC, hMS⟩ := hstep k hk hin
      rw [hjump k hk]
      refine ⟨hk1, hC, hS, hMC, hMS, ?_⟩
      -- one-step bound `|Δψ| ≤ |C| + |S| + R ≤ 2M + R`
      have hCk : |C k * sin (2 * φ (τ k))| ≤ M := by
        rw [hC, abs_mul, abs_mul]
        have h1 := abs_sin_le_one (Δ k); have h2 := abs_sin_le_one (2 * φ (τ k))
        have := mul_le_mul hMC h1 (abs_nonneg _) hM
        nlinarith [abs_nonneg (dC k), abs_nonneg (sin (Δ k)), abs_nonneg (sin (2 * φ (τ k)))]
      have hSk : |S k * cos (2 * φ (τ k))| ≤ M := by
        rw [hS, abs_mul, abs_mul]
        have h1 := abs_sin_le_one (Δ k); have h2 := abs_cos_le_one (2 * φ (τ k))
        have := mul_le_mul hMS h1 (abs_nonneg _) hM
        nlinarith [abs_nonneg (dS k), abs_nonneg (sin (Δ k)), abs_nonneg (cos (2 * φ (τ k)))]
      set X := (∫ t in τ k..τ (k + 1), qaKick reactorQA mα qα μ ψ θ φ ρ t) / (qα * (211 / 500))
      have e1 : X = (X - (C k * sin (2 * φ (τ k)) + S k * cos (2 * φ (τ k)))) +
          C k * sin (2 * φ (τ k)) + S k * cos (2 * φ (τ k)) := by ring
      rw [e1]
      have := abs_add_le (X - (C k * sin (2 * φ (τ k)) + S k * cos (2 * φ (τ k))))
        (C k * sin (2 * φ (τ k)))
      have := abs_add_le (X - (C k * sin (2 * φ (τ k)) + S k * cos (2 * φ (τ k))) +
        C k * sin (2 * φ (τ k))) (S k * cos (2 * φ (τ k)))
      linarith)
    (fun k hk hin => hpair k hk hin) hR hM hγ he hσ (by positivity)
    (by rw [hψ00]; exact hgap)
  intro k hk
  have := key k hk
  rw [hψ00] at this
  exact this

/-! ## Numbers -/

/-- **Budget with the simulated per-bounce constants** (untrusted RK4,
`scripts/trapped_reanchor/reanchor_sim.py`, starts `ψ(0) ∈ {4.85, 5.27, 5.7}`): with
`R = 2.1 × 10⁻⁴`, `γ = 7 × 10⁻⁴`, `M = 0.023`, `e = 0.0141`, `σ = 0.0076` (all in `T m²` or rad)
and `ψ(0) = 5.27`, the gap of `reactorQA_trapped_reanchored` closes for `N = 300` bounces; with
the simulated bounce period `6.55 × 10⁻⁵ s` this is about `0.0197 s`, roughly 110 times the
unconditional `1.8 × 10⁻⁴ s` and `1/20` of the slowing-down time `0.4 s`. -/
theorem reanchored_budget_simulated :
    2 * 0.023 + (300 : ℝ) * (2.1e-4 + 7e-4 + 0.023 * (0.0141 + 0.0076)) + (2 * 0.023 + 2.1e-4) ≤
      min ((527 : ℝ) / 100 - 475 / 100) (579 / 100 - 527 / 100) ∧
    (300 : ℝ) * 6.55e-5 < 0.0197 ∧ (0.0197 : ℝ) / 1.8e-4 > 109 := by
  norm_num

/-- **Honest comparison.** With the crude proved bounce-period bound `P ≤ 1.6 ms` instead of the
simulated `6.5 × 10⁻⁵ s`, the available worst-case amplitude bound
`M ≤ 2 ∫₀ᴾ |g| ≤ 2 P sup|g|/(q ι₀)`, with `sup|g|/(q ι₀) ≈ 4.2 × 10³ T m²/s` from
`|g| ≤ (2E/B_min)(2ψ_a/B₀)(2|b₁|)`, exceeds the width `1.04 T m²` of the start window by an order
of magnitude (`2 · 1.6 × 10⁻³ · 4000 = 12.8`): a validated bounce-time enclosure (or a sharper
kick bound) is a prerequisite for any proved instance of the re-anchored bound. -/
theorem crude_amplitude_exceeds_window : (2 : ℝ) * 1.6e-3 * 4000 > 579 / 100 - 475 / 100 := by
  norm_num

end PlasmaLean.Design.NearAxisQATrappedReanchor
