/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQAAveragedStage

/-!
# Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model

Source: `notes/theory/guiding-centre-averaging.md` §1, §4 (iterated Lemma A); the model is
`Design/NearAxisQA.reactorQA` in the vacuum Boozer guiding-centre model of
`Theory/Kinetic/BoozerGuidingCentre`.

**Main result** (`alpha_trapped_reactorQA_averaged`): with the hypotheses of
`NearAxisQA.alpha_trapped_reactorQA` (3.5 MeV alpha, any `μ ≥ 0`, `|v_∥/v| ≥ 0.9` at `t = 0`,
start at `r ≤ a/4`; only the orbit horizon is longer), the orbit stays at `ψ ≤ 8.2 T m² < ψ_a`
for `0 ≤ t ≤ T = 0.19 s` (`Tav`), instead of `0.8 ms`. `alpha_trapped_reactorQA_averaged_of_le`
gives every horizon `T ≤ 0.19 s`; the earlier `0.11 s` statement is the corollary
`alpha_trapped_reactorQA_averaged_011`.

**Structure of the forcing.** The only symmetry-breaking term of the model is `r² b₁ cos 2φ`, so
`dP/dt = −(q²ρ²B/m + μ) ∂_φB = 2 b₁ c R² sin 2φ` with `c = μ + m v_∥²/B`: the defect is purely in
`φ` and the phase is `Φ = 2σφ` (`σ = sign v_∥`, constant for passing alphas), with phase speed
`Ω = 2|v_∥|B/G ≥ Ω₀ = 2 · 1.12 × 10⁷ · 4.93/58.1 ≈ 1.90 × 10⁶ s⁻¹`. The `θ`-dependence of `B`
(the `η r cos θ` and `B₂c r² cos 2θ` terms) does **not** create resonances at this order: Lemma A
only divides by the full phase speed `Ω`, never by `Ω − j ι φ̇`. The `θ` coupling enters through
the amplitudes, which contain `θ`-harmonics (frequency `ι φ̇ ≈ 0.4 Ω/2`); these are included
exactly in the Lie derivatives and are why the amplitudes decrease only by factors `≈ 0.1–0.5`
per step instead of `ν/Ω`.

**Method.**
1. State variables `x = r cos θ, y = r sin θ, R² = 2ψ/B₀, C = cos 2φ, S = sin 2φ,
   W = σ v_∥/10⁷, 1/W, B, 1/B, U = μ/10⁻¹⁴, σ` (`orbX`). Along every model orbit they satisfy a
   **polynomial** ODE `ẋᵢ = flowsᵢ(x)` (`hasDerivAt_orbX`, proved from the Boozer equations; the
   `1/r` singularities of the `(ψ, θ)` chart cancel exactly).
2. The amplitudes `amp 0 = σ 2 b₁ c R²`, `amp (j+1) = ± L(amp j · 1/Ω)` (`amp`) are computed
   exactly in `ℚ` by the kernel (`LiePoly.lie`, 2, 15, 121 and 458 monomials). The expensive
   one, `amp 3`, is evaluated **once**: `amp3Lit_eq` checks it against a literal.
3. Bounds (in units of `q` T m²/s): `|amp 0| ≤ 1935`, `|amp 1| ≤ 218`, `|amp 2| ≤ 93` (one
   ball over the whole region, `glob_j`) and `|amp 3| ≤ 11` (`amp3_bound`). The last is a
   two-stage enclosure: `LiePoly.stage1` encloses the dependence on `cos 2φ, sin 2φ, W, 1/W, U`
   once per sign of `σ` (a `214`-term polynomial in `x, y, R², B, 1/B` with ball
   coefficients, `S3pos_eq`, `S3neg_eq`), which is then enclosed on the `324` rectangles of an
   adaptive bisection of the disc `r ≤ a` (`CoverCert`, proof term built by the `meta`
   tactic `cover_cert` from an untrusted plan; `cover_pos`, `cover_neg`). All checks are
   kernel evaluations of exact integer/rational arithmetic.
4. `Kinetic.Boozer.boozerGC_trapped_until_averaged` with `k = 3`: gap
   `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 11 T) ≤ ι₀ (8.2 − ψ(0))`, `Δρ ≈ 1.88 cm`
   (`averaged_gap`), which holds for `T = 0.19 s` and fails for `T = 0.20 s`
   (`averaged_gap_fails_late`).

**Caveats (model only).**
* The Boozer guiding-centre equations are a supplied model (not derived from the Lorentz
  force); orbits are supplied and must stay in the chart `ψ > 0` (off the magnetic axis).
* The field is the truncated second-order near-axis expansion, which agrees with a real vacuum
  field only to the order of the expansion; the `O(r³)` remainder has no rigorous bound.
* Passing particles only (`|v_∥/v| ≥ 0.9` at `t = 0`, hence `|v_∥| ≥ 1.12 × 10⁷ m/s` throughout):
  trapped and barely passing alphas have a phase speed that changes sign and are not covered.
* No collisions or slowing down; `T = 0.19 s` is about half of the slowing-down time
  (`≈ 0.4 s`), not the full time.

**What limits `T`.** The secular rate `11` is a sup over the whole disc and both `σ` (the
sampled sup along the region is `≈ 6`). Refining the cover further stalls near `10.5`, because
the variables `cos 2φ, sin 2φ, W, U` are enclosed globally in stage one. A fourth integration
by parts would need `amp 4` (`1901` monomials); its exact kernel evaluation did not finish
within 15 minutes in experiments, so it is not used. The constant term
`2 ∑ Aⱼ/Ω₀ ≈ 2.4 × 10⁻³ T m²` is negligible; the orbit-width term `|G| Δρ ≈ 1.09 T m²` uses
about a third of the gap `ι₀ (8.2 − ψ(0)) ≈ 3.24 T m²`.
-/

public section
noncomputable section

namespace PlasmaLean.Design.NearAxisQAAveraged

open PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer PlasmaLean.Kinetic.LiePoly
  PlasmaLean.Design.NearAxisQA Real

variable {μ σ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ}


set_option maxHeartbeats 4000000 in
-- The `244` leaf goals are elaborated (and kernel-checked) within one tactic block.
/-- Kernel-checked cover of the disc for `σ = +1` (`244` leaves, `|amp 3/q| ≤ 11`). -/
theorem cover_pos : CoverCert S3pos 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) := by
  cover_cert
    "XYXYXYLLYYLLLLYXYYXLLLLYYXLLLLLXYLXYLLYLYLLYLXYLYLXLLYLYLXLLYXYXYYXLYXLXLLLLLYYXYXXYLLYL
    LXYLYLLYLYLLXLYXLLLYLXYXYLLYLXLLXLYLLYLXXLYLLYLXLLXLXYLLYXYLLYYLLLLXLLLYXYYLXXYXYYXLLLLY
    XYLLLXLLXLLYXYLXLYLLLXYLLYXLLLXYLXYLLYLLLXYXLYLLLYXYXLYLLLYXYLLYLLLYLLYLXYXYLXLLLYXLLLLX
    LYXYLLYLLLXYLXYLYLXLYLXLXLLYXLLYXLXYLLYLXYLLYLYLLXYXLYLXLLXXYLLYLLXYYLLLYYLLLYXYXLYLLXYL
    LYXLLLYXXLYLLYXLLLLLYXLYLXYLLYLLXYXYLXLYLLYYLLXYLXLYLLYLXYLLYLLYXXYXLLXYLYLXLLYXLLXYLLLY
    XYLLYLXLLXYXLYLLLLXYXYLLYLLLLLYXYYLXLLXYXLLLLLL"
  all_goals decide +kernel

/-- Kernel-checked cover of the disc for `σ = −1` (`80` leaves, `|amp 3/q| ≤ 11`). -/
theorem cover_neg : CoverCert S3neg 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) := by
  cover_cert
    "XYXYXYLLYYLLLLYXYYXLLLLYLLLXYLXYLLYLYLLYLXYLYLXLLYLLYXYXYYLLLYYXLYLLXLLLLYXYYLXXLLXLLXLY
    LLYLXYXLLLLXLYXLLLXYLXYLYLLYLYXLLXLYLLYXLYLXLLXYXLYLLYXXLLXLLLYXYLXLLLL"
  all_goals decide +kernel

/-- **Secular amplitude bound**: `|amp 3| ≤ 11 q` on the region. -/
theorem amp3_bound {x : ℕ → ℝ} (hx : InRegion x) : |eval (amp 3) x| ≤ 11 * cq := by
  have hq : (0 : ℝ) < cq := by norm_num [cq]
  have hxi : ((-17 / 10 : ℚ) : ℝ) ≤ x 0 ∧ x 0 ≤ ((17 / 10 : ℚ) : ℝ) := by
    have := abs_le.mp hx.1; push_cast; constructor <;> linarith
  have hyj : ((-17 / 10 : ℚ) : ℝ) ≤ x 1 ∧ x 1 ≤ ((17 / 10 : ℚ) : ℝ) := by
    have := abs_le.mp hx.2.1; push_cast; constructor <;> linarith
  have hσ : x 10 = 1 ∨ x 10 = -1 := hx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have key : |eval (amp 3) x / cq| ≤ ((11 : ℕ) : ℝ) := by
    rcases hσ with h | h
    · have hS := BPoly.holds_stage1 cellMask cq (by norm_num [cq]) (amp 3)
        (globalS_mem hx (sg := 1) (by simp [h]))
      rw [amp3Lit_eq, S3pos_eq] at hS
      exact cover_pos.sound x hx hS hxi hyj
    · have hS := BPoly.holds_stage1 cellMask cq (by norm_num [cq]) (amp 3)
        (globalS_mem hx (sg := -1) (by simp [h]))
      rw [amp3Lit_eq, S3neg_eq] at hS
      exact cover_neg.sound x hx hS hxi hyj
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq] at key
  simpa using key

/-- Global bound `|amp 0/q| ≤ 1935`. -/
theorem glob_0 : boundOK (evalT (toFix cq (amp 0)) globalF) 1935 = true := by decide +kernel
/-- Global bound `|amp 1/q| ≤ 218`. -/
theorem glob_1 : boundOK (evalT (toFix cq (amp 1)) globalF) 218 = true := by decide +kernel
/-- Global bound `|amp 2/q| ≤ 93`. -/
theorem glob_2 : boundOK (evalT (toFix cq (amp 2)) globalF) 93 = true := by decide +kernel

/-! ## Passing-alpha analysis along the orbit -/

/-- Sign of the initial parallel velocity (`σ = ±1`). -/
@[expose] def sgn0 (ψ θ φ ρ : ℝ → ℝ) : ℝ := if 0 < vel ψ θ φ ρ 0 then 1 else -1

theorem sgn0_sq : sgn0 ψ θ φ ρ ^ 2 = 1 := by unfold sgn0; split_ifs <;> norm_num

theorem sgn0_cases : sgn0 ψ θ φ ρ = 1 ∨ sgn0 ψ θ φ ρ = -1 := by
  unfold sgn0; split_ifs <;> simp

theorem mα_pos : (0 : ℝ) < mα := by norm_num [mα]
theorem qα_ne : qα ≠ 0 := by norm_num [qα]
theorem G_ne : reactorQA.G ≠ 0 := by
  change (581 / 10 : ℝ) ≠ 0; norm_num

/-- Energy conservation in the form `m v²/2 + μ B = E`. -/
theorem energy_eq (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα) {s : ℝ} (hs : s ∈ Set.Icc 0 T) :
    mα * vel ψ θ φ ρ s ^ 2 / 2 + μ * Bt ψ θ φ s = Eα := by
  have := boozerEnergy_eq_on mα_pos.ne' qα_ne G_ne h hs
  rw [boozerEnergy_eq_parallel mα_pos.ne', hE] at this
  simpa [vel, Bt] using this

/-- Sign persistence by the intermediate value theorem. -/
theorem sign_persist {u : ℝ → ℝ} {t w : ℝ} (hc : ContinuousOn u (Set.Icc 0 t)) (hw : 0 < w)
    (ht : 0 ≤ t) (hlow : ∀ s ∈ Set.Icc 0 t, w ^ 2 ≤ u s ^ 2) : 0 < u t * u 0 := by
  by_contra hneg
  push Not at hneg
  have h00 : 0 < u 0 * u 0 := by nlinarith [hlow 0 ⟨le_rfl, ht⟩]
  have hg : ContinuousOn (fun r => u r * u 0) (Set.Icc 0 t) := hc.mul continuousOn_const
  obtain ⟨σ, hσ, hσ0⟩ := intermediate_value_Icc' ht hg
    (show (0 : ℝ) ∈ Set.Icc (u t * u 0) (u 0 * u 0) from ⟨hneg, h00.le⟩)
  have hu0 : u 0 ≠ 0 := by rintro h0; simp [h0] at h00
  have huσ : u σ = 0 := by
    rcases mul_eq_zero.mp hσ0 with h' | h'
    · exact h'
    · exact absurd h' hu0
  have := hlow σ hσ
  rw [huσ] at this
  nlinarith

/-- Numerical facts used for the passing analysis. -/
theorem passing_numerics :
    19 / 100 * Eα / 4.93 * 10 ^ 14 ≤ (21612 / 10000 : ℝ) ∧
    ((112 / 100 : ℝ) * 10 ^ 7) ^ 2 ≤ 2 / mα * (Eα - 19 / 100 * Eα / 4.93 * 6.47) ∧
    2 * Eα / mα ≤ ((13 / 10 : ℝ) * 10 ^ 7) ^ 2 := by
  norm_num [Eα, mα]

/-- **Region facts** for a passing alpha whose orbit has stayed in `ψ ≤ ψ_a` up to time `s`:
the state vector satisfies `InRegion` (with `σ = sgn0`), and `B ≠ 0`, `W ≠ 0`. -/
theorem region_facts {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 T) (hhist : ∀ s' ∈ Set.Icc 0 s, ψ s' ≤ psiEdge) :
    InRegion (orbX (sgn0 ψ θ φ ρ) μ ψ θ φ ρ s) ∧ Bt ψ θ φ s ≠ 0 ∧
      orbX (sgn0 ψ θ φ ρ) μ ψ θ φ ρ s 5 ≠ 0 := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hsub : ∀ s' ∈ Set.Icc 0 s, s' ∈ Set.Icc 0 T := fun s' hs' => ⟨hs'.1, hs'.2.trans hs.2⟩
  have hBb : ∀ s' ∈ Set.Icc 0 s, 4.93 ≤ Bt ψ θ φ s' ∧ Bt ψ θ φ s' ≤ 6.47 := fun s' hs' =>
    reactorQA_B_bounds (h.pos s' (hsub s' hs')) (hhist s' hs')
  have h0s : (0 : ℝ) ∈ Set.Icc 0 s := ⟨le_rfl, hs.1⟩
  obtain ⟨n1, n2, n3⟩ := passing_numerics
  -- magnetic moment bound from the initial pitch
  have hE0 := energy_eq h hE (hsub 0 h0s)
  have hB0 := hBb 0 h0s
  have hμle : μ ≤ 19 / 100 * Eα / 4.93 := by
    have hv0 : 81 / 100 * (2 * Eα / mα) ≤ vel ψ θ φ ρ 0 ^ 2 := hpitch
    have hm := mα_pos
    have : μ * Bt ψ θ φ 0 ≤ 19 / 100 * Eα := by
      have : mα * (81 / 100 * (2 * Eα / mα)) ≤ mα * vel ψ θ φ ρ 0 ^ 2 :=
        mul_le_mul_of_nonneg_left hv0 hm.le
      field_simp at this
      nlinarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hB0.1 hμ]
  -- speed bounds
  have hvsq : ∀ s' ∈ Set.Icc 0 s, ((112 / 100 : ℝ) * 10 ^ 7) ^ 2 ≤ vel ψ θ φ ρ s' ^ 2 ∧
      vel ψ θ φ ρ s' ^ 2 ≤ ((13 / 10 : ℝ) * 10 ^ 7) ^ 2 := by
    intro s' hs'
    have hEs := energy_eq h hE (hsub s' hs')
    have hB := hBb s' hs'
    have hm := mα_pos
    have hv : vel ψ θ φ ρ s' ^ 2 = 2 / mα * (Eα - μ * Bt ψ θ φ s') := by
      field_simp; linarith
    have hμB : μ * Bt ψ θ φ s' ≤ 19 / 100 * Eα / 4.93 * 6.47 := by
      have := mul_le_mul hμle hB.2 (by linarith) (by norm_num [Eα])
      linarith
    have hμB0 : 0 ≤ μ * Bt ψ θ φ s' := mul_nonneg hμ (by linarith)
    constructor
    · rw [hv]; refine n2.trans ?_
      gcongr
    · rw [hv]; refine le_trans ?_ n3
      rw [show 2 * Eα / mα = 2 / mα * Eα by ring]
      gcongr; linarith
  -- sign persistence
  have hvc : ContinuousOn (vel ψ θ φ ρ) (Set.Icc 0 s) := by
    intro s' hs'
    have hd := (((h.dρ s' (hsub s' hs')).const_mul qα).mul
      (h.hasDerivAt_B (hsub s' hs'))).div_const mα
    exact (show ContinuousAt (fun r => qα * ρ r * along reactorQA.B ψ θ φ r / mα) s' from
      hd.continuousAt).continuousWithinAt
  have hsign := sign_persist hvc (by norm_num : (0 : ℝ) < 112 / 100 * 10 ^ 7) hs.1
    (fun s' hs' => (hvsq s' hs').1)
  have hσv : 0 < σ * vel ψ θ φ ρ s := by
    rw [hσdef]; unfold sgn0
    split_ifs with hp
    · nlinarith
    · have : vel ψ θ φ ρ 0 ≠ 0 := by
        intro h0; rw [h0] at hsign; simp at hsign
      have hneg : vel ψ θ φ ρ 0 < 0 := lt_of_le_of_ne (not_lt.mp hp) this
      nlinarith
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  have hW2 : (σ * vel ψ θ φ ρ s) ^ 2 = vel ψ θ φ ρ s ^ 2 := by rw [mul_pow, hσ2, one_mul]
  obtain ⟨hvl, hvh⟩ := hvsq s ⟨hs.1, le_rfl⟩
  have hWl : 112 / 100 * 10 ^ 7 ≤ σ * vel ψ θ φ ρ s := by
    rw [← hW2] at hvl
    nlinarith
  have hWh : σ * vel ψ θ φ ρ s ≤ 13 / 10 * 10 ^ 7 := by
    rw [← hW2] at hvh
    nlinarith
  have hψs := h.pos s hs
  have hψc := hhist s ⟨hs.1, le_rfl⟩
  have hr := radius_le_edge hψc
  have hr0 : 0 ≤ radius (57 / 10) (ψ s) := sqrt_nonneg _
  have hr2 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψs.le
  have hBs := hBb s ⟨hs.1, le_rfl⟩
  refine ⟨?_, by linarith [hBs.1], ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [orbX, List.getD_cons_zero]
      rw [abs_mul, abs_of_nonneg hr0]
      nlinarith [abs_cos_le_one (θ s), abs_nonneg (cos (θ s))]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      rw [abs_mul, abs_of_nonneg hr0]
      nlinarith [abs_sin_le_one (θ s), abs_nonneg (sin (θ s))]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one, hr2]
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      unfold psiEdge at hψc
      linarith
    · simpa [orbX] using abs_cos_le_one _
    · simpa [orbX] using abs_sin_le_one _
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; linarith
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; linarith
    · exact orbX_6 s
    · rw [eval_Bpoly]
      simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, Bt, along, reactorQA, field,
        nearAxisB, cB0, cEta, cb0, cb1, cB2c]
      push_cast
      rw [cos_two_mul (θ s)]
      have hsc := sin_sq_add_cos_sq (θ s)
      have : radius (57 / 10) (ψ s) ^ 2 = 2 * ψ s / (57 / 10) := hr2
      linear_combination (33 / 2000 * (2 * ψ s / (57 / 10))) * hsc -
        (33 / 2000 * (cos (θ s) ^ 2 - sin (θ s) ^ 2)) * this
    · have h1 := hBs.1; norm_num at h1; simpa [orbX, Bt] using h1
    · have h1 := hBs.2; norm_num at h1; simpa [orbX, Bt] using h1
    · exact orbX_8 s
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]; positivity
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      nlinarith
    · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
      exact sgn0_cases
    · intro i hi; exact orbX_ge11 s hi
  · simp only [orbX, List.getD_cons_succ, List.getD_cons_zero]
    positivity

theorem eval_amp0 (x : ℕ → ℝ) : eval (amp 0) x =
    2 * cb1 * (x 10 * ((cmus * x 9 + cm * cvs ^ 2 * x 5 ^ 2 * x 8) * x 2)) := by
  simp only [amp, cP, V, eval_scP, eval_mulP, eval_addP, eval_varP (show 10 < 11 by norm_num),
    eval_varP (show 9 < 11 by norm_num), eval_varP (show 8 < 11 by norm_num),
    eval_varP (show 5 < 11 by norm_num), eval_varP (show 2 < 11 by norm_num)]
  push_cast; ring

/-- Orbit-width constant `Δρ = (m/q) 10⁷ (W_hi/B_min − W_lo/B_max) ≈ 1.88 cm`. -/
@[expose] def Δρv : ℝ :=
  (cm / cq : ℚ) * 10 ^ 7 * ((13 / 10) / (493 / 100) - (112 / 100) / (647 / 100))

/-- Lower bound for the phase speed `Ω = 2 v_∥ B/G ≥ Ω₀ ≈ 1.90 × 10⁶ s⁻¹`. -/
@[expose] def Om0 : ℝ := 2 * 10 ^ 7 * (112 / 100) * (493 / 100) / (581 / 10)

theorem rho_eq {σ : ℝ} (hσ : σ ^ 2 = 1) {s : ℝ} (hB : Bt ψ θ φ s ≠ 0) :
    ρ s = (cm / cq : ℚ) * 10 ^ 7 * σ * (orbX σ μ ψ θ φ ρ s 5 / orbX σ μ ψ θ φ ρ s 7) := by
  simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, mα_eq, qα_eq,
    Bt] at hB ⊢
  have hq : (cq : ℝ) ≠ 0 := by norm_num [cq]
  have hm : (cm : ℝ) ≠ 0 := by norm_num [cm]
  push_cast
  field_simp
  rw [hσ]; ring

/-- **Orbit width** for passing alphas: `|ρ(t) − ρ(0)| ≤ Δρ` while the orbit stays in `ψ ≤ ψ_a`. -/
theorem rho_dev {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (hhist : ∀ s ∈ Set.Icc 0 t, ψ s ≤ psiEdge) :
    |ρ t - ρ 0| ≤ Δρv := by
  set σ := sgn0 ψ θ φ ρ
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  obtain ⟨⟨-, -, -, -, -, -, ht5l, ht5h, -, -, ht7l, ht7h, -⟩, hBt, -⟩ :=
    region_facts hμ h hE hpitch ht hhist
  obtain ⟨⟨-, -, -, -, -, -, h05l, h05h, -, -, h07l, h07h, -⟩, hB0, -⟩ :=
    region_facts hμ h hE hpitch ⟨le_rfl, ht.1.trans ht.2⟩
      (fun s hs => hhist s ⟨hs.1, hs.2.trans ht.1⟩)
  rw [rho_eq (μ := μ) (ρ := ρ) hσ2 hBt, rho_eq (μ := μ) (ρ := ρ) hσ2 hB0, ← mul_sub, abs_mul]
  have hσ1 : |σ| = 1 := by
    rcases sgn0_cases (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) with h1 | h1 <;> simp [σ, h1]
  have hk : |((cm / cq : ℚ) : ℝ) * 10 ^ 7 * σ| = ((cm / cq : ℚ) : ℝ) * 10 ^ 7 := by
    rw [abs_mul, hσ1, mul_one, abs_of_pos (by norm_num [cm, cq])]
  rw [hk, Δρv]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num [cm, cq])
  have hb1 : ∀ w b : ℝ, 112 / 100 ≤ w → w ≤ 13 / 10 → 493 / 100 ≤ b → b ≤ 647 / 100 →
      (112 / 100) / (647 / 100) ≤ w / b ∧ w / b ≤ (13 / 10) / (493 / 100) := by
    intro w b hw1 hw2 hb1 hb2
    constructor
    · rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  obtain ⟨a1, a2⟩ := hb1 _ _ ht5l ht5h ht7l ht7h
  obtain ⟨b1, b2⟩ := hb1 _ _ h05l h05h h07l h07h
  rw [abs_le]; constructor <;> linarith

/-- The averaged confinement time `T = 0.19 s`. -/
@[expose] def Tav : ℝ := 19 / 100

/-- Numerical gap: `|G| Δρ + (2 (1935 + 218 + 93)/Ω₀ + 11 T) ≤ ι₀ (8.2 − ψ_start)` at `T = Tav`. -/
theorem averaged_gap :
    |(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * Tav) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, Tav, abs_of_pos]

/-- **Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model,
for every horizon `T ≤ 0.19 s`.** Every guiding-centre orbit (solving the vacuum Boozer equations
on `[0, T]`) of the model with field `reactorQA` (a = 1.7 m, B₀ = 5.7 T) for an alpha
(`m = 6.6447 × 10⁻²⁷ kg`, `q = 2e`) of energy `3.5 MeV`, any `μ ≥ 0`, passing pitch
`v_∥² ≥ 0.81 v²` at `t = 0`, starting at `ψ ≤ B₀(a/4)²/2`, satisfies `ψ(t) ≤ 8.2 T m² < ψ_a` for
`0 ≤ t ≤ T`. The hypotheses are exactly those of the worst-case bound
`NearAxisQA.alpha_trapped_reactorQA`, except that the orbit is supplied on `[0, T]` instead of
`[0, 0.8 ms]`.

Proof: `dP/dt = a₀ sin(2σφ)` with `Ω = 2|v_∥|B/G ≥ Ω₀ ≈ 1.9 × 10⁶ s⁻¹`; three oscillatory
integrations by parts (`osc_ibp_drift_iter`, `k = 3`) with exact polynomial Lie-derivative
amplitudes bounded by `1935, 218, 93` (global) and `11` T m²/s (`amp3_bound`: kernel-checked
adaptive ball cover of the disc, `324` rectangles, both signs of `v_∥`); the gap
`|G| Δρ + (2 ∑_{j<3} Aⱼ/Ω₀ + A₃ T)/|q| ≤ ι₀ (8.2 − ψ(0))` with `Δρ ≈ 1.88 cm`.

**Caveats.** This is a theorem about the model only: (i) the Boozer guiding-centre equations are
assumed (their derivation from the Lorentz force is not formalized), orbits are supplied and
must stay off the magnetic axis; (ii) the field is the truncated second-order near-axis expansion,
accurate only to the order of the expansion (no bound on the `O(r³)` remainder); (iii) passing
particles only (`|v_∥/v| ≥ 0.9` initially): the phase speed must stay positive, so trapped and
barely passing alphas are not covered; (iv) collisions and slowing down are ignored. -/
theorem alpha_trapped_reactorQA_averaged_of_le {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} {T : ℝ} (hT : T ≤ Tav)
    (hμ : 0 ≤ μ) (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 T, ψ t ≤ 8.2 := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  set X := orbX σ μ ψ θ φ ρ with hX
  let a : ℕ → ℝ → ℝ := fun j r => if j % 2 = 0 then eval (amp j) (X r) else 0
  let b : ℕ → ℝ → ℝ := fun j r => if j % 2 = 1 then eval (amp j) (X r) else 0
  let A : ℕ → ℝ := fun j => ([1935, 218, 93, 11] : List ℝ).getD j 0 * cq
  have hs0 : ψ 0 ≤ 0.51478125 := by norm_num [psiStart] at hstart; linarith
  refine boozerGC_trapped_until_averaged (F := reactorQA) (N := 0) (M := 1) (c := psiEdge)
    (ιmin := 211 / 500) (Δρ := Δρv) (Ω₀ := Om0) (η := 0) (k := 3) (Φ := fun r => 2 * σ * φ r)
    (Ω := Omf σ μ ψ θ φ ρ) (e := fun _ => 0) (a := a) (b := b) (A := A) qα_ne h
    (by norm_num [psiEdge]) (by linarith) (by norm_num) (by norm_num [Om0])
    (by simp [A, cq]; norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- twist
    intro x hx _
    have hp : ∀ y, reactorQA.ψp y = 211 / 500 * y := fun _ => rfl
    rw [hp, hp, le_abs]
    right; linarith
  · exact fun t ht hhist => rho_dev hμ h hE hpitch ht hhist
  · -- `dP/dt = a₀ sin Φ`
    intro s hs hhist
    obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs hhist
    refine (helicalMomentum_hasDerivAt_on mα_pos.ne' qα_ne G_ne 0 1 h hs).congr_deriv ?_
    simp only [a, b, Nat.zero_mod, ite_true, show ¬ (0 % 2 = 1) by norm_num, ite_false, zero_mul,
      add_zero]
    rw [hX, eval_amp0, orbX_sq5 hσ2, orbX_8]
    simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt, along,
      symmetryDefect, reactorQA, field, nearAxisBφ, mα_eq, qα_eq, cm, cq, cmus, cvs, cb1]
    simp only [Bt, along] at hB
    rcases sgn0_cases (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) with h1 | h1
    · rw [show σ = 1 from hσdef.trans h1]; push_cast; field_simp; ring
    · rw [show σ = -1 from hσdef.trans h1]
      simp only [mul_neg, neg_mul, mul_one, sin_neg]
      push_cast; field_simp; ring
  · intro s _ _; simp
  · -- phase speed
    intro s hs hhist
    obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs hhist
    refine ((h.dφ s hs).const_mul (2 * σ)).congr_deriv ?_
    simp only [Omf, orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt,
      along, reactorQA, field]
    field_simp
  · intro s hs hhist
    obtain ⟨⟨-, -, -, -, -, -, h5, -, -, -, h7, -⟩, -, -⟩ := region_facts hμ h hE hpitch hs hhist
    simp only [Om0, Omf]
    gcongr
  · intro j hj s hs hhist
    obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs hhist
    have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
    interval_cases j
    · simpa [a, b] using hd
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
    · simpa [a, b] using hd
  · intro j hj s hs hhist
    obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs hhist
    have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
    interval_cases j
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
    · simpa [a, b] using hd
    · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
  · intro j hj s hs hhist
    obtain ⟨hreg, -, -⟩ := region_facts hμ h hE hpitch hs hhist
    interval_cases j
    · simpa [a, b, A] using global_bound glob_0 hreg
    · simpa [a, b, A] using global_bound glob_1 hreg
    · simpa [a, b, A] using global_bound glob_2 hreg
    · simpa [a, b, A] using amp3_bound hreg
  · have hG : reactorQA.G = 581 / 10 := rfl
    have hc : (0 : ℝ) ≤ 11 * cq + 0 := by norm_num [cq]
    have hmono : |(1 : ℝ) * (581 / 10)| * Δρv +
        (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * T) / |qα| ≤
        |(1 : ℝ) * (581 / 10)| * Δρv +
        (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * Tav) / |qα| := by
      gcongr
    have h2 : 211 / 500 * (8.2 - psiStart) ≤ 211 / 500 * (8.2 - ψ 0) := by linarith
    refine le_trans (le_of_eq ?_) (hmono.trans (averaged_gap.trans h2))
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, A, hG]
    norm_num
    ring

/-- **Averaged confinement of passing 3.5 MeV alphas in the reactor-scale near-axis QA model**
on `[0, 0.19 s]`: the case `T = Tav` of `alpha_trapped_reactorQA_averaged_of_le`. The hypotheses
are exactly those of the worst-case bound `NearAxisQA.alpha_trapped_reactorQA`, except for the
longer orbit horizon (`0.19 s` instead of `0.8 ms`): `237.5` times the worst-case time. See
`alpha_trapped_reactorQA_averaged_of_le` for the proof outline and the caveats (model only:
assumed guiding-centre equations, truncated near-axis field, passing alphas only, no
collisions or slowing down). -/
theorem alpha_trapped_reactorQA_averaged {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ Tav)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 Tav, ψ t ≤ 8.2 :=
  alpha_trapped_reactorQA_averaged_of_le le_rfl hμ h hE hpitch hstart

/-- The earlier `0.11 s` statement, as a corollary (`0.11 ≤ Tav`). -/
theorem alpha_trapped_reactorQA_averaged_011 {μ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ (11 / 100))
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (hstart : ψ 0 ≤ psiStart) :
    ∀ t ∈ Set.Icc 0 (11 / 100), ψ t ≤ 8.2 :=
  alpha_trapped_reactorQA_averaged_of_le (by norm_num [Tav]) hμ h hE hpitch hstart

/-! ## Sanity checks and fixtures -/

/-- Rejected fixture: the bound `10` fails on the leaf `[51/80, 221/320] × [1003/640, 51/32]`
of the `σ = +1` cover (its enclosure is `≈ 10.98`): the cover does not certify `|amp 3/q| ≤ 10`.
-/
theorem rect_rejected : rectOK S3pos 10 (51 / 80) (221 / 320) (1003 / 640) (51 / 32) = false := by
  decide +kernel

/-- Rejected fixture: a single rectangle (the whole square `[−a, a]²`) does not certify the bound
`11`; the subdivision is needed (its enclosure is `≈ 50`). -/
theorem rect_whole_rejected :
    rectOK S3pos 11 (-17 / 10) (17 / 10) (-17 / 10) (17 / 10) = false := by
  decide +kernel

/-- Accepted fixture: a rectangle outside the disc `r ≤ a` passes trivially. -/
theorem rect_outside : rectOK [] 0 (3 / 2) (17 / 10) (3 / 2) (17 / 10) = true := by
  decide +kernel

/-- Rejected fixture: the global bound `1900` for `amp 0` (true sup `≈ 1934`) is not certified. -/
theorem glob_0_rejected : boundOK (evalT (toFix cq (amp 0)) globalF) 1900 = false := by
  decide +kernel

/-- The gap of the main theorem fails at `T = 0.20 s`: `0.19 s` is essentially what the
certified constants give (the exact limit is `≈ 0.195 s`). -/
theorem averaged_gap_fails_late :
    ¬ (|(1 : ℝ) * (581 / 10)| * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + (11 * cq + 0) * 0.2) /
      |qα| ≤ 211 / 500 * (8.2 - psiStart)) := by
  norm_num [Δρv, Om0, cq, cm, qα, psiStart, abs_of_pos]

/-- Comparison: the averaged time is `237.5` times the worst-case `0.8 ms`. -/
theorem averaged_vs_worstCase : Tav = 237.5 * 8e-4 := by norm_num [Tav]

/-- Honest comparison: the averaged time is still below the `0.4 s` slowing-down time. -/
theorem averaged_vs_slowingDown : Tav < 0.4 := by norm_num [Tav]

/-- Special case: the zeroth amplitude is the `sin 2φ` forcing `σ 2 b₁ c R²` with
`c = μ + m v_∥²/B`; it vanishes on the magnetic axis (`R² = 0`). -/
theorem amp0_axis (x : ℕ → ℝ) (h2 : x 2 = 0) : eval (amp 0) x = 0 := by
  rw [eval_amp0, h2]; ring

end PlasmaLean.Design.NearAxisQAAveraged
