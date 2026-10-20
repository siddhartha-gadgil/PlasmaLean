/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.TrappedOrbits
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Bounce (banana) orbits: existence of turning points, precession, kick form (rung M4)

Companion to `notes/theory/near-qa-trapped-particles.md` (target T4, step 1). This file
discharges the **turning-point hypotheses** of `bounce_drift_nonresonant` from checkable
inequalities on the field, and reduces the remaining hypotheses (non-resonance and the kick
form) to explicit statements about one exact-QA reference bounce.

Results:

* Level-crossing tools: `lt_of_level_deriv_neg` (a function whose derivative is negative
  whenever it equals `c` cannot cross `c` upwards), `first_hit`.
* `half_bounce` (abstract ODE/IVT argument on a pair `(θ, ρ)`): if `ρ̇ ≤ −c₁` for `θ ≥ δ`,
  `ρ̇ ≥ c₁` for `θ ≤ −δ`, `ρ ≠ 0` for `|θ| ≤ δ`, `θ̇ ≤ −c₂` for `|θ| ≤ δ, ρ < 0`, and `|ρ| ≤ ρ_max`,
  then from a turning point (`ρ = 0`, `θ > 0`) the next turning point (`ρ = 0`, `θ < −δ`) comes
  within `L = 4ρ_max/c₁ + 2δ/c₂`, with `ρ < 0` in between. `half_bounce'` is the mirror image.
* `bounce_sequence`: by induction, a monotone sequence of turning points `τ 0 < τ 1 < … < τ N`
  with alternating sides, `τ (k+1) − τ k ≤ L`, as long as `t₀ + N L ≤ T`.
* `boozer_bounce_sequence`: the same for a QA Boozer guiding-centre orbit (near-QA allowed:
  `∂_φB` enters only through `∂_φB + ι ∂_θB ≥ κ` on the poloidal flanks), from **field
  inequalities on a flux band** (`BounceWindow`) plus energy conservation; the poloidal angle is
  confined to `(−θ₊, θ₊)` by energy (`theta_confined`). The band itself (`ψ` stays in
  `[ψ_lo, ψ_hi]`) is a hypothesis here; for exact QA it is derived from momentum conservation in
  `Design/NearAxisQATrappedBounce`.
* `half_bounce_time_ge`: lower bound `2δ/Θ` on each half bounce from `|θ̇| ≤ Θ`.
* `theta_sub_iota_phi_hasDerivAt`, `precession_step`: the exact identity
  `ι (φ(t₁) − φ(t₀)) = θ(t₁) − θ(t₀) − ∫ (μ/q + qρ²B/m) ∂_ψB dt` (constant `ι`); with
  `−(μ/q + qρ²B/m) ∂_ψB ∈ [Ω_lo, Ω_hi]` it gives two-sided bounds on the toroidal advance
  (`precession_bounds`).
* `tip_psi_eq`, `tip_theta_eq`: **tip rigidity** in exact QA: every turning point of the same
  orbit on the upper flank has the same `ψ` (momentum) and the same `θ` (energy + single well).
* `abs_sin_ge_of_mem`: quantitative non-resonance, `|sin x| ≥ min (sin a) (sin b)` for
  `x ∈ [a, b] ⊆ [0, π]`.
* `periodic_kick_form`: for a reference orbit that is periodic up to a toroidal shift `Δ` per
  bounce, the kick integrals of any `sin 2φ` defect are **exactly** `A sin(2kΔ + β)` (`R = 0`).
  `bounce_drift_of_reference`: the drift theorem with the kick hypothesis replaced by closeness
  `R` of the actual kicks to the periodic reference kicks, and `α = 2Δ`.

**Not proved here** (see the design file for the precise residual list): periodicity of the
exact-QA reference orbit (tip rigidity is proved; the remaining step is ODE uniqueness), an
enclosure of the precession per bounce `Δ` tight enough for `|sin Δ| ≥ c` (needs a validated
bounce-time quadrature), and the per-bounce remainder `R` (Grönwall comparison with the
reference orbit and control of the phase shear, i.e. the GWB/Chirikov parameter).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Kinetic Real Set Filter Topology

/-! ## Level-crossing tools -/

/-- If `f` has negative derivative at `u` and `f < f u` on `[a', u)`, contradiction. -/
theorem false_of_hasDerivAt_neg_left {f : ℝ → ℝ} {u d a' : ℝ} (hd : HasDerivAt f d u)
    (hneg : d < 0) (ha' : a' < u) (hlt : ∀ y ∈ Ico a' u, f y < f u) : False := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE u)
  have h1 : ∀ᶠ y in 𝓝[<] u, slope f u y < 0 := ht.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ y in 𝓝[<] u, y ∈ Ico a' u := Ico_mem_nhdsLT ha'
  obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
  rw [slope_def_field] at hy1
  have hyu : y - u < 0 := by linarith [hy2.2]
  have hf : f y - f u < 0 := by linarith [hlt y hy2]
  have : 0 < (f y - f u) / (y - u) := div_pos_of_neg_of_neg hf hyu
  linarith

/-- If `f` has negative derivative at `a`, then `f < f a` just to the right of `a`. -/
theorem eventually_lt_right_of_hasDerivAt_neg {f : ℝ → ℝ} {a d : ℝ} (hd : HasDerivAt f d a)
    (hneg : d < 0) : ∀ᶠ y in 𝓝[>] a, f y < f a := by
  have ht := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE a)
  have h1 : ∀ᶠ y in 𝓝[>] a, slope f a y < 0 := ht.eventually (gt_mem_nhds hneg)
  filter_upwards [h1, self_mem_nhdsWithin] with y hy hya
  rw [slope_def_field] at hy
  have hya' : 0 < y - a := sub_pos.mpr hya
  by_contra hcon
  push Not at hcon
  have : 0 ≤ (f y - f a) / (y - a) := div_nonneg (by linarith) hya'.le
  linarith

/-- **First hitting time.** If `g` is continuous on `[a, b]`, `g a > c` and `g b ≤ c`, there is a
first time `s ∈ (a, b]` with `g s = c` and `g > c` on `[a, s)`. -/
theorem first_hit {g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (ha : c < g a) (hb : g b ≤ c) :
    ∃ s ∈ Ioc a b, g s = c ∧ ∀ t ∈ Ico a s, c < g t := by
  set K := {t | t ∈ Icc a b ∧ g t ≤ c} with hK
  have hcl : IsClosed K := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : K.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  have hbdd : BddBelow K := ⟨a, fun t ht => ht.1.1⟩
  set s := sInf K
  have hs : s ∈ K := hcl.csInf_mem hne hbdd
  have before : ∀ t ∈ Ico a s, c < g t := fun t ht => by
    by_contra hct
    push Not at hct
    exact absurd (csInf_le hbdd ⟨⟨ht.1, ht.2.le.trans hs.1.2⟩, hct⟩) (not_le.mpr ht.2)
  have has : a < s := by
    rcases hs.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hs.2; rw [← h] at this; linarith
  refine ⟨s, ⟨has, hs.1.2⟩, le_antisymm hs.2 ?_, before⟩
  -- `g s ≥ c` by continuity from the left
  have hcw : ContinuousWithinAt g (Ico a s) s :=
    (hg s hs.1).mono (fun t ht => ⟨ht.1, ht.2.le.trans hs.1.2⟩)
  have hmem : Ico a s ∈ 𝓝[<] s := Ico_mem_nhdsLT has
  have hlim : Tendsto g (𝓝[<] s) (𝓝 (g s)) :=
    (hcw.mono_of_mem_nhdsWithin hmem).tendsto
  have hev : ∀ᶠ t in 𝓝[<] s, c ≤ g t := by
    filter_upwards [hmem] with t ht using (before t ht).le
  exact ge_of_tendsto hlim hev

/-- **Level-crossing lemma.** Let `f` be continuous on `[a, b]` with `f a ≤ c`, and suppose that
at every `t ∈ [a, b]` with `f t = c` the function `f` has a negative derivative. Then `f < c`
on `(a, b]`. -/
theorem lt_of_level_deriv_neg {f : ℝ → ℝ} {a b c : ℝ} (hf : ContinuousOn f (Icc a b))
    (ha : f a ≤ c) (hlev : ∀ t ∈ Icc a b, f t = c → ∃ d, d < 0 ∧ HasDerivAt f d t) :
    ∀ t ∈ Ioc a b, f t < c := by
  intro t ht
  by_contra hct
  push Not at hct
  -- a point `a' ∈ [a, t)` with `f a' < c`
  obtain ⟨a', ha'1, ha'2⟩ : ∃ a' ∈ Ico a t, f a' < c := by
    rcases ha.lt_or_eq with h | h
    · exact ⟨a, ⟨le_rfl, ht.1⟩, h⟩
    · obtain ⟨d, hd, hD⟩ := hlev a ⟨le_rfl, ht.1.le.trans ht.2⟩ h
      have h1 := eventually_lt_right_of_hasDerivAt_neg hD hd
      have h2 : ∀ᶠ y in 𝓝[>] a, y ∈ Ioo a t := Ioo_mem_nhdsGT ht.1
      obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
      exact ⟨y, ⟨hy2.1.le, hy2.2⟩, h ▸ hy1⟩
  -- first time after `a'` where `f ≥ c`
  have hsub : Icc a' t ⊆ Icc a b := Icc_subset_Icc ha'1.1 ht.2
  obtain ⟨u, hu, hfu, hbefore⟩ := first_hit (g := fun x => -f x) (c := -c) ha'1.2.le
    (hf.mono hsub).neg (by linarith) (by linarith)
  have hfu' : f u = c := by linarith
  obtain ⟨d, hd, hD⟩ := hlev u (hsub ⟨hu.1.le, hu.2⟩) hfu'
  exact false_of_hasDerivAt_neg_left hD hd hu.1 fun y hy => by
    have := hbefore y hy; linarith

/-- Mean value bound: if `f' ≤ −c` on `(a, b)` then `f b ≤ f a − c (b − a)`. -/
theorem mvt_le_neg {f f' : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hc : ∀ x ∈ Ioo a b, f' x ≤ -c) :
    f b ≤ f a - c * (b - a) := by
  obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope f f' hab hf hd
  have := hc ξ hξ
  rw [e, div_le_iff₀ (sub_pos.mpr hab)] at this
  linarith

/-- Mean value bound: if `f' ≥ c` on `(a, b)` then `f b ≥ f a + c (b − a)`. -/
theorem mvt_ge {f f' : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hc : ∀ x ∈ Ioo a b, c ≤ f' x) :
    f a + c * (b - a) ≤ f b := by
  obtain ⟨ξ, hξ, e⟩ := exists_hasDerivAt_eq_slope f f' hab hf hd
  have := hc ξ hξ
  rw [e, le_div_iff₀ (sub_pos.mpr hab)] at this
  linarith

/-! ## Half bounce: abstract turning-point theorem -/

/-- Upper bound on the duration of a half bounce: `4 ρ_max/c₁ + 2δ/c₂`. -/
@[expose] def halfBounceTime (ρmax c₁ c₂ δ : ℝ) : ℝ := 4 * ρmax / c₁ + 2 * δ / c₂

/-- **Half bounce** (abstract turning-point theorem). Let `θ, ρ` have derivatives `θ', ρ'` on
`I = [t₀, t₀ + L]`, `L = halfBounceTime ρ_max c₁ c₂ δ`, and assume on `I`:
`|ρ| ≤ ρ_max`; `ρ' ≤ −c₁` where `θ ≥ δ`; `ρ' ≥ c₁` where `θ ≤ −δ`; `ρ ≠ 0` where `|θ| ≤ δ`;
`θ' ≤ −c₂` where `|θ| ≤ δ` and `ρ < 0`. If `t₀` is a turning point (`ρ t₀ = 0`) with `θ t₀ > 0`,
then there is a next turning point `t₁ ∈ (t₀, t₀ + L]` with `θ t₁ < −δ` and `ρ < 0` on
`(t₀, t₁)`. -/
theorem half_bounce {θ ρ θ' ρ' : ℝ → ℝ} {t₀ δ c₁ c₂ ρmax : ℝ}
    (hδ : 0 < δ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hρmax : 0 < ρmax)
    (hθd : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), HasDerivAt θ (θ' t) t)
    (hρd : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), HasDerivAt ρ (ρ' t) t)
    (H1 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |ρ t| ≤ ρmax)
    (H2 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), δ ≤ θ t → ρ' t ≤ -c₁)
    (H5 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), θ t ≤ -δ → c₁ ≤ ρ' t)
    (H3 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |θ t| ≤ δ → ρ t ≠ 0)
    (H4 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |θ t| ≤ δ → ρ t < 0 → θ' t ≤ -c₂)
    (hρ0 : ρ t₀ = 0) (hθ0 : 0 < θ t₀) :
    ∃ t₁ ∈ Ioc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), ρ t₁ = 0 ∧ θ t₁ < -δ ∧
      ∀ s ∈ Ioo t₀ t₁, ρ s < 0 := by
  set L := halfBounceTime ρmax c₁ c₂ δ with hL
  set L₁ := 2 * ρmax / c₁ with hL₁
  set L₂ := 2 * δ / c₂ with hL₂
  have hL₁p : 0 < L₁ := by positivity
  have hL₂p : 0 < L₂ := by positivity
  have hLe : L = 2 * L₁ + L₂ := by rw [hL, hL₁, hL₂, halfBounceTime]; ring
  have hc₁L₁ : c₁ * L₁ = 2 * ρmax := by rw [hL₁]; field_simp
  have hc₂L₂ : c₂ * L₂ = 2 * δ := by rw [hL₂]; field_simp
  have hI : ∀ {t}, t₀ ≤ t → t ≤ t₀ + L → t ∈ Icc t₀ (t₀ + L) := fun h1 h2 => ⟨h1, h2⟩
  have hθc : ContinuousOn θ (Icc t₀ (t₀ + L)) :=
    fun t ht => (hθd t ht).continuousAt.continuousWithinAt
  have hρc : ContinuousOn ρ (Icc t₀ (t₀ + L)) :=
    fun t ht => (hρd t ht).continuousAt.continuousWithinAt
  have ht₀I : t₀ ∈ Icc t₀ (t₀ + L) := hI le_rfl (by linarith)
  have hθδ : δ < θ t₀ := by
    by_contra h
    push Not at h
    exact H3 t₀ ht₀I (abs_le.mpr ⟨by linarith, h⟩) hρ0
  -- `ρ < 0` after `t₀` as long as `θ ≥ −δ`
  have rho_neg : ∀ s, t₀ ≤ s → s ≤ t₀ + L → (∀ t ∈ Icc t₀ s, -δ ≤ θ t) →
      ∀ t ∈ Ioc t₀ s, ρ t < 0 := by
    intro s hs0 hsL hθs
    refine lt_of_level_deriv_neg (hρc.mono (Icc_subset_Icc le_rfl hsL)) hρ0.le ?_
    intro t ht hρt
    have htI := hI ht.1 (ht.2.trans hsL)
    have hθt : δ < θ t := by
      by_contra h
      push Not at h
      exact H3 t htI (abs_le.mpr ⟨hθs t ht, h⟩) hρt
    exact ⟨ρ' t, by linarith [H2 t htI hθt.le], hρd t htI⟩
  -- Step A: `θ` reaches `−δ` within `L₁ + L₂`
  have stepA : ∃ s' ∈ Icc t₀ (t₀ + L₁ + L₂), θ s' ≤ -δ := by
    by_contra hA
    push Not at hA
    have hall : ∀ t ∈ Icc t₀ (t₀ + L₁ + L₂), -δ ≤ θ t := fun t ht => (hA t ht).le
    have hEnd : t₀ + L₁ + L₂ ≤ t₀ + L := by linarith
    have hneg := rho_neg (t₀ + L₁ + L₂) (by linarith) hEnd hall
    -- A2: `θ ≤ δ` somewhere in `[t₀, t₀ + L₁]`
    obtain ⟨a₁, ha₁, hθa₁⟩ : ∃ a₁ ∈ Icc t₀ (t₀ + L₁), θ a₁ ≤ δ := by
      by_contra h2
      push Not at h2
      have hm := mvt_le_neg (f := ρ) (f' := ρ') (c := c₁) (by linarith : t₀ < t₀ + L₁)
        (hρc.mono (Icc_subset_Icc le_rfl (by linarith)))
        (fun x hx => hρd x (hI hx.1.le (by linarith [hx.2])))
        (fun x hx => H2 x (hI hx.1.le (by linarith [hx.2])) (h2 x ⟨hx.1.le, hx.2.le⟩).le)
      have := H1 (t₀ + L₁) (hI (by linarith) (by linarith))
      rw [hρ0] at hm
      have := (abs_le.mp this).1
      nlinarith
    -- A3: `θ < δ` on `(a₁, t₀ + L₁ + L₂]`
    have hlt : ∀ t ∈ Ioc a₁ (t₀ + L₁ + L₂), θ t < δ := by
      refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc ha₁.1 hEnd)) hθa₁ ?_
      intro t ht hθt
      have htI := hI (ha₁.1.trans ht.1) (ht.2.trans hEnd)
      have ht0 : t₀ < t := by
        rcases (ha₁.1.trans ht.1).lt_or_eq with h | h
        · exact h
        · rw [← h] at hθt; linarith
      have hρt := hneg t ⟨ht0, ht.2⟩
      exact ⟨θ' t, by linarith [H4 t htI (abs_le.mpr ⟨hall t ⟨ht0.le, ht.2⟩, hθt.le⟩) hρt],
        hθd t htI⟩
    -- A4: mean value theorem on `[a₁, t₀ + L₁ + L₂]`
    have ha₁e : a₁ < t₀ + L₁ + L₂ := by linarith [ha₁.2]
    have hm := mvt_le_neg (f := θ) (f' := θ') (c := c₂) ha₁e
      (hθc.mono (Icc_subset_Icc ha₁.1 hEnd))
      (fun x hx => hθd x (hI (ha₁.1.trans hx.1.le) (by linarith [hx.2])))
      (fun x hx => by
        have hxI := hI (ha₁.1.trans hx.1.le) (by linarith [hx.2])
        have hx0 : t₀ < x := lt_of_le_of_lt ha₁.1 hx.1
        exact H4 x hxI (abs_le.mpr ⟨hall x ⟨hx0.le, hx.2.le⟩, (hlt x ⟨hx.1, hx.2.le⟩).le⟩)
          (hneg x ⟨hx0, hx.2.le⟩))
    have := hA (t₀ + L₁ + L₂) ⟨by linarith, le_rfl⟩
    have h2 : c₂ * L₂ ≤ c₂ * (t₀ + L₁ + L₂ - a₁) :=
      mul_le_mul_of_nonneg_left (by linarith [ha₁.2]) hc₂.le
    linarith
  -- Step B: first time `θ = −δ`
  obtain ⟨s', hs', hθs'⟩ := stepA
  obtain ⟨s, hs, hθs, hθbefore⟩ := first_hit (g := θ) (c := -δ) hs'.1
    (hθc.mono (Icc_subset_Icc le_rfl (by linarith [hs'.2]))) (by linarith) hθs'
  have hsL₁ : s ≤ t₀ + L₁ + L₂ := hs.2.trans hs'.2
  have hθge : ∀ t ∈ Icc t₀ s, -δ ≤ θ t := fun t ht => by
    rcases ht.2.lt_or_eq with h | h
    · exact (hθbefore t ⟨ht.1, h⟩).le
    · rw [h, hθs]
  have hnegs := rho_neg s hs.1.le (by linarith) hθge
  have hρs : ρ s < 0 := hnegs s ⟨hs.1, le_rfl⟩
  have hsI := hI hs.1.le (by linarith)
  -- Step C: `ρ` returns to `0` within `L₁` after `s`
  have hsEnd : s + L₁ ≤ t₀ + L := by linarith
  have stepC : ∃ u ∈ Icc s (s + L₁), 0 ≤ ρ u := by
    by_contra hC
    push Not at hC
    have hθlt : ∀ t ∈ Ioc s (s + L₁), θ t < -δ := by
      refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc hs.1.le hsEnd)) hθs.le ?_
      intro t ht hθt
      have htI := hI (hs.1.le.trans ht.1) (ht.2.trans hsEnd)
      exact ⟨θ' t, by linarith [H4 t htI (abs_le.mpr ⟨hθt.ge, by linarith⟩) (hC t ht)],
        hθd t htI⟩
    have hm := mvt_ge (f := ρ) (f' := ρ') (c := c₁) (by linarith : s < s + L₁)
      (hρc.mono (Icc_subset_Icc hs.1.le hsEnd))
      (fun x hx => hρd x (hI (hs.1.le.trans hx.1.le) (by linarith [hx.2])))
      (fun x hx => H5 x (hI (hs.1.le.trans hx.1.le) (by linarith [hx.2]))
        (hθlt x ⟨hx.1, hx.2.le⟩).le)
    have := (abs_le.mp (H1 s hsI)).1
    have := hC (s + L₁) ⟨by linarith, le_rfl⟩
    nlinarith
  -- Step D: first return of `ρ` to `0`
  obtain ⟨u, hu, hρu⟩ := stepC
  obtain ⟨t₁, ht₁, hρt₁, hρbefore⟩ := first_hit (g := fun x => -ρ x) (c := 0) hu.1
    (hρc.mono (Icc_subset_Icc hs.1.le (hu.2.trans hsEnd))).neg (by linarith) (by linarith)
  have hρt₁' : ρ t₁ = 0 := by linarith
  have ht₁End : t₁ ≤ t₀ + L := ht₁.2.trans (hu.2.trans hsEnd)
  have hθt₁ : θ t₁ < -δ := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc hs.1.le ht₁End)) hθs.le ?_ t₁
      ⟨ht₁.1, le_rfl⟩
    intro t ht hθt
    have htI := hI (hs.1.le.trans ht.1) (ht.2.trans ht₁End)
    rcases ht.2.lt_or_eq with h | h
    · have hρt : ρ t < 0 := by have := hρbefore t ⟨ht.1, h⟩; linarith
      exact ⟨θ' t, by linarith [H4 t htI (abs_le.mpr ⟨hθt.ge, by linarith⟩) hρt], hθd t htI⟩
    · exact absurd (h ▸ hρt₁') (H3 t htI (abs_le.mpr ⟨hθt.ge, by linarith⟩))
  refine ⟨t₁, ⟨hs.1.trans ht₁.1, ht₁End⟩, hρt₁', hθt₁, fun x hx => ?_⟩
  rcases le_or_gt x s with h | h
  · exact hnegs x ⟨hx.1, h⟩
  · have := hρbefore x ⟨h.le, hx.2⟩; linarith

/-- **Mirror half bounce**: the same with `θ ↦ −θ`, `ρ ↦ −ρ`. From a turning point with
`θ t₀ < 0`, the next turning point `t₁ ∈ (t₀, t₀ + L]` has `θ t₁ > δ` and `ρ > 0` on `(t₀, t₁)`;
the hypothesis on `θ'` is `θ' ≥ c₂` where `|θ| ≤ δ` and `ρ > 0`. -/
theorem half_bounce' {θ ρ θ' ρ' : ℝ → ℝ} {t₀ δ c₁ c₂ ρmax : ℝ}
    (hδ : 0 < δ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hρmax : 0 < ρmax)
    (hθd : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), HasDerivAt θ (θ' t) t)
    (hρd : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), HasDerivAt ρ (ρ' t) t)
    (H1 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |ρ t| ≤ ρmax)
    (H2 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), δ ≤ θ t → ρ' t ≤ -c₁)
    (H5 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), θ t ≤ -δ → c₁ ≤ ρ' t)
    (H3 : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |θ t| ≤ δ → ρ t ≠ 0)
    (H4' : ∀ t ∈ Icc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), |θ t| ≤ δ → 0 < ρ t → c₂ ≤ θ' t)
    (hρ0 : ρ t₀ = 0) (hθ0 : θ t₀ < 0) :
    ∃ t₁ ∈ Ioc t₀ (t₀ + halfBounceTime ρmax c₁ c₂ δ), ρ t₁ = 0 ∧ δ < θ t₁ ∧
      ∀ s ∈ Ioo t₀ t₁, 0 < ρ s := by
  obtain ⟨t₁, ht₁, h1, h2, h3⟩ := half_bounce (θ := fun t => -θ t) (ρ := fun t => -ρ t)
    (θ' := fun t => -θ' t) (ρ' := fun t => -ρ' t) hδ hc₁ hc₂ hρmax
    (fun t ht => (hθd t ht).neg) (fun t ht => (hρd t ht).neg)
    (fun t ht => by rw [abs_neg]; exact H1 t ht)
    (fun t ht h => by linarith [H5 t ht (by linarith)])
    (fun t ht h => by linarith [H2 t ht (by linarith)])
    (fun t ht h => by rw [abs_neg] at h; exact neg_ne_zero.mpr (H3 t ht h))
    (fun t ht h h' => by rw [abs_neg] at h; linarith [H4' t ht h (by linarith)])
    (by simp [hρ0]) (by linarith)
  exact ⟨t₁, ht₁, by linarith, by linarith, fun s hs => by linarith [h3 s hs]⟩

/-- `halfBounceTime` is positive. -/
theorem halfBounceTime_pos {ρmax c₁ c₂ δ : ℝ} (hρ : 0 < ρmax) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hδ : 0 < δ) : 0 < halfBounceTime ρmax c₁ c₂ δ := by
  unfold halfBounceTime; positivity

/-- **Sequence of turning points.** Under the hypotheses of `half_bounce` and `half_bounce'` on
`[t₀, T]`, starting from a turning point with `θ t₀ > 0`: for every `N` with `t₀ + N L ≤ T` there
is a monotone sequence `τ` with `τ 0 = t₀`, `τ k < τ (k+1) ≤ τ k + L` for `k < N`, all `τ k`
(`k ≤ N`) turning points (`ρ = 0`) on alternating sides (`(−1)^k θ(τ k) > 0`), `(−1)^k ρ < 0`
strictly between `τ k` and `τ (k+1)`, `τ k ≤ t₀ + k L`, and `τ` constant from `N` on. -/
theorem bounce_sequence {θ ρ θ' ρ' : ℝ → ℝ} {t₀ T δ c₁ c₂ ρmax : ℝ}
    (hδ : 0 < δ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hρmax : 0 < ρmax)
    (hθd : ∀ t ∈ Icc t₀ T, HasDerivAt θ (θ' t) t)
    (hρd : ∀ t ∈ Icc t₀ T, HasDerivAt ρ (ρ' t) t)
    (H1 : ∀ t ∈ Icc t₀ T, |ρ t| ≤ ρmax)
    (H2 : ∀ t ∈ Icc t₀ T, δ ≤ θ t → ρ' t ≤ -c₁)
    (H5 : ∀ t ∈ Icc t₀ T, θ t ≤ -δ → c₁ ≤ ρ' t)
    (H3 : ∀ t ∈ Icc t₀ T, |θ t| ≤ δ → ρ t ≠ 0)
    (H4 : ∀ t ∈ Icc t₀ T, |θ t| ≤ δ → ρ t < 0 → θ' t ≤ -c₂)
    (H4' : ∀ t ∈ Icc t₀ T, |θ t| ≤ δ → 0 < ρ t → c₂ ≤ θ' t)
    (hρ0 : ρ t₀ = 0) (hθ0 : 0 < θ t₀) (N : ℕ)
    (hN : t₀ + N * halfBounceTime ρmax c₁ c₂ δ ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = t₀ ∧ Monotone τ ∧
      (∀ k < N, τ k < τ (k + 1) ∧ τ (k + 1) ≤ τ k + halfBounceTime ρmax c₁ c₂ δ) ∧
      (∀ k ≤ N, ρ (τ k) = 0 ∧ 0 < (-1) ^ k * θ (τ k)) ∧
      (∀ k < N, ∀ s ∈ Ioo (τ k) (τ (k + 1)), (-1) ^ k * ρ s < 0) ∧
      (∀ k ≤ N, τ k ≤ t₀ + k * halfBounceTime ρmax c₁ c₂ δ) ∧
      (∀ k, N ≤ k → τ k = τ N) := by
  set L := halfBounceTime ρmax c₁ c₂ δ with hL
  have hLp : 0 < L := halfBounceTime_pos hρmax hc₁ hc₂ hδ
  induction N with
  | zero =>
    refine ⟨fun _ => t₀, rfl, monotone_const, fun k hk => absurd hk (Nat.not_lt_zero _),
      fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => ?_,
      fun _ _ => rfl⟩
    · obtain rfl : k = 0 := Nat.le_zero.mp hk; simp [hρ0, hθ0]
    · obtain rfl : k = 0 := Nat.le_zero.mp hk; simp
  | succ n ih =>
    have hn : t₀ + n * L ≤ T := by push_cast at hN; nlinarith
    obtain ⟨τ, h0, hmono, hstep, htp, hsgn, hle, hconst⟩ := ih hn
    obtain ⟨hρn, hθn⟩ := htp n le_rfl
    have hτn0 : t₀ ≤ τ n := h0 ▸ hmono (Nat.zero_le n)
    have hτnL : τ n + L ≤ T := by
      have := hle n le_rfl; push_cast at hN; linarith
    have hsub : Icc (τ n) (τ n + L) ⊆ Icc t₀ T := Icc_subset_Icc hτn0 hτnL
    -- the next turning point
    obtain ⟨t₁, ht₁, hρt₁, hθt₁, hρbetween⟩ : ∃ t₁ ∈ Ioc (τ n) (τ n + L), ρ t₁ = 0 ∧
        0 < (-1) ^ (n + 1) * θ t₁ ∧ ∀ s ∈ Ioo (τ n) t₁, (-1) ^ n * ρ s < 0 := by
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_one_pow, one_mul] at hθn
        obtain ⟨t₁, ht₁, h1, h2, h3⟩ := half_bounce (θ' := θ') (ρ' := ρ') hδ hc₁ hc₂ hρmax
          (fun t ht => hθd t (hsub ht)) (fun t ht => hρd t (hsub ht))
          (fun t ht => H1 t (hsub ht)) (fun t ht => H2 t (hsub ht))
          (fun t ht => H5 t (hsub ht)) (fun t ht => H3 t (hsub ht))
          (fun t ht => H4 t (hsub ht)) hρn hθn
        refine ⟨t₁, ht₁, h1, ?_, fun s hs => ?_⟩
        · rw [pow_succ, he.neg_one_pow]; linarith
        · rw [he.neg_one_pow, one_mul]; exact h3 s hs
      · rw [ho.neg_one_pow] at hθn
        obtain ⟨t₁, ht₁, h1, h2, h3⟩ := half_bounce' (θ' := θ') (ρ' := ρ') hδ hc₁ hc₂ hρmax
          (fun t ht => hθd t (hsub ht)) (fun t ht => hρd t (hsub ht))
          (fun t ht => H1 t (hsub ht)) (fun t ht => H2 t (hsub ht))
          (fun t ht => H5 t (hsub ht)) (fun t ht => H3 t (hsub ht))
          (fun t ht => H4' t (hsub ht)) hρn (by linarith)
        refine ⟨t₁, ht₁, h1, ?_, fun s hs => ?_⟩
        · rw [pow_succ, ho.neg_one_pow]; linarith
        · rw [ho.neg_one_pow]; linarith [h3 s hs]
    set τ' : ℕ → ℝ := fun k => if k ≤ n then τ k else t₁ with hτ'
    have hτ'le : ∀ k ≤ n, τ' k = τ k := fun k hk => by simp [hτ', hk]
    have hτ'gt : ∀ k, n < k → τ' k = t₁ := fun k hk => by simp [hτ', not_le.mpr hk]
    refine ⟨τ', by rw [hτ'le 0 (Nat.zero_le n), h0], ?_, fun k hk => ?_, fun k hk => ?_,
      fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · refine monotone_nat_of_le_succ fun k => ?_
      rcases lt_trichotomy k n with h | h | h
      · rw [hτ'le k h.le, hτ'le (k + 1) h]; exact hmono (Nat.le_succ k)
      · rw [hτ'le k h.le, hτ'gt (k + 1) (by omega), h]; exact ht₁.1.le
      · rw [hτ'gt k h, hτ'gt (k + 1) (by omega)]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [hτ'le k h.le, hτ'le (k + 1) h]; exact hstep k h
      · rw [h, hτ'le n le_rfl, hτ'gt (n + 1) (by omega)]; exact ⟨ht₁.1, ht₁.2⟩
    · rcases Nat.lt_or_ge n k with h | h
      · have hk' : k = n + 1 := by omega
        rw [hτ'gt k h, hk']; exact ⟨hρt₁, hθt₁⟩
      · rw [hτ'le k h]; exact htp k h
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · rw [hτ'le k h.le, hτ'le (k + 1) h]; exact hsgn k h
      · rw [h, hτ'le n le_rfl, hτ'gt (n + 1) (by omega)]; exact hρbetween
    · rcases Nat.lt_or_ge n k with h | h
      · have hk' : k = n + 1 := by omega
        rw [hτ'gt k h, hk']
        have := hle n le_rfl
        push_cast
        linarith [ht₁.2]
      · rw [hτ'le k h]; exact hle k h
    · rw [hτ'gt k (by omega), hτ'gt (n + 1) (by omega)]

/-! ## Turning points of Boozer guiding-centre orbits -/

/-- **Bounce window**: field inequalities on the flux band `ψ ∈ [ψ_lo, ψ_hi]` (all `φ`) that make
every orbit of energy `E` and magnetic moment `μ` a banana with turning points on the flanks
`δ ≤ |θ| < θ₊`:
* `B ≥ B_lo > 0` for `|θ| ≤ θ₊`;
* `μ B > E` at `θ = ±θ₊` (the orbit cannot reach `θ = ±θ₊`: trapped);
* `∂_φB + ι₀ ∂_θB ≥ κ` on `[δ, θ₊]` and `≤ −κ` on `[−θ₊, −δ]` (the mirror force pushes back;
  near-QA `∂_φB` is allowed);
* `μ B < E` for `|θ| ≤ δ` (the orbit passes the well bottom with `v_∥ ≠ 0`);
* `((2E/B − μ)|∂_ψB|/q + c₂)² ≤ (B ι₀/G)² · 2(E − μB)/m` for `|θ| ≤ δ` (the parallel streaming
  `v_∥ B ι₀/G` beats the poloidal drift by `c₂`);
* `2m(E − μ B_lo)/(q² B_lo²) ≤ ρ_max²` (bound on the parallel gyroradius). -/
structure BounceWindow (F : BoozerField) (m q μ E ι₀ ψlo ψhi δ θp κ c₂ Blo ρmax : ℝ) : Prop where
  /-- Positive lower bound on `B`. -/
  Blo_pos : 0 < Blo
  /-- `B ≥ B_lo` on the band for `|θ| ≤ θ₊`. -/
  B_ge : ∀ x ∈ Icc ψlo ψhi, ∀ θ ∈ Icc (-θp) θp, ∀ φ, Blo ≤ F.B x θ φ
  /-- The orbit cannot reach `θ = θ₊`. -/
  forbid_pos : ∀ x ∈ Icc ψlo ψhi, ∀ φ, E < μ * F.B x θp φ
  /-- The orbit cannot reach `θ = −θ₊`. -/
  forbid_neg : ∀ x ∈ Icc ψlo ψhi, ∀ φ, E < μ * F.B x (-θp) φ
  /-- Mirror force on the upper flank. -/
  flank_pos : ∀ x ∈ Icc ψlo ψhi, ∀ θ ∈ Icc δ θp, ∀ φ, κ ≤ F.Bφ x θ φ + ι₀ * F.Bθ x θ φ
  /-- Mirror force on the lower flank. -/
  flank_neg : ∀ x ∈ Icc ψlo ψhi, ∀ θ ∈ Icc (-θp) (-δ), ∀ φ, F.Bφ x θ φ + ι₀ * F.Bθ x θ φ ≤ -κ
  /-- The orbit passes the bottom of the well. -/
  bottom_pass : ∀ x ∈ Icc ψlo ψhi, ∀ θ ∈ Icc (-δ) δ, ∀ φ, μ * F.B x θ φ < E
  /-- Streaming beats drift at the bottom of the well. -/
  bottom_speed : ∀ x ∈ Icc ψlo ψhi, ∀ θ ∈ Icc (-δ) δ, ∀ φ,
    ((2 * E / F.B x θ φ - μ) * |F.Bψ x θ φ| / q + c₂) ^ 2 ≤
      (F.B x θ φ * ι₀ / F.G) ^ 2 * (2 * (E - μ * F.B x θ φ) / m)
  /-- Gyroradius bound. -/
  rho_bound : 2 * m * (E - μ * Blo) / (q ^ 2 * Blo ^ 2) ≤ ρmax ^ 2

variable {F : BoozerField} {m q μ : ℝ} {ψ θ φ ρ : ℝ → ℝ}

/-- Energy in the form `q²ρ²B²/(2m) + μB = E` along an orbit on `[0, T]`. -/
theorem energy_along (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T E t : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hE : boozerEnergy F m q μ ψ θ φ ρ 0 = E)
    (ht : t ∈ Icc 0 T) :
    q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t ^ 2 / (2 * m) + μ * along F.B ψ θ φ t = E := by
  have := boozerEnergy_eq_on hm hq hG h ht
  rw [hE] at this
  exact this

/-- **Gyroradius bound from energy.** At a time where `B ≥ B_lo > 0`, with `μ ≥ 0` and
`2m(E − μ B_lo)/(q² B_lo²) ≤ ρ_max²`, energy conservation gives `|ρ| ≤ ρ_max`. -/
theorem abs_rho_le_of_energy (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ μ) {E Blo ρmax t : ℝ}
    (hBlo : 0 < Blo) (hρmax : 0 ≤ ρmax) (hB : Blo ≤ along F.B ψ θ φ t)
    (hEt : q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t ^ 2 / (2 * m) + μ * along F.B ψ θ φ t = E)
    (hbd : 2 * m * (E - μ * Blo) / (q ^ 2 * Blo ^ 2) ≤ ρmax ^ 2) : |ρ t| ≤ ρmax := by
  set B := along F.B ψ θ φ t
  have hB0 : 0 < B := hBlo.trans_le hB
  have hkin : 0 ≤ E - μ * B := by
    have : 0 ≤ q ^ 2 * ρ t ^ 2 * B ^ 2 / (2 * m) := by positivity
    linarith
  have hE2 : q ^ 2 * ρ t ^ 2 * B ^ 2 = 2 * m * (E - μ * B) := by
    have := hEt; field_simp at this; linarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hρ2 : ρ t ^ 2 = 2 * m * (E - μ * B) / (q ^ 2 * B ^ 2) := by
    rw [eq_div_iff (by positivity)]; linarith
  have : ρ t ^ 2 ≤ ρmax ^ 2 := by
    rw [hρ2]
    refine le_trans ?_ hbd
    have hμB : μ * Blo ≤ μ * B := mul_le_mul_of_nonneg_left hB hμ
    apply div_le_div₀ (by nlinarith) (by nlinarith) (by positivity)
    have := pow_le_pow_left₀ hBlo.le hB 2
    nlinarith
  exact abs_le_of_sq_le_sq' this hρmax |> abs_le.mpr

/-- **Energy confines the poloidal angle.** If `μ B > E` at `θ = ±θ₊` on the band, the orbit
stays in the band, and `θ 0 ∈ (−θ₊, θ₊)`, then `θ t ∈ (−θ₊, θ₊)` on `[0, T]`. -/
theorem theta_confined (hm : 0 < m) (hq : q ≠ 0) (hG : F.G ≠ 0) {T E ψlo ψhi θp : ℝ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hE : boozerEnergy F m q μ ψ θ φ ρ 0 = E)
    (hband : ∀ t ∈ Icc 0 T, ψ t ∈ Icc ψlo ψhi)
    (hfp : ∀ x ∈ Icc ψlo ψhi, ∀ φ, E < μ * F.B x θp φ)
    (hfn : ∀ x ∈ Icc ψlo ψhi, ∀ φ, E < μ * F.B x (-θp) φ)
    (hθ0 : θ 0 ∈ Ioo (-θp) θp) : ∀ t ∈ Icc 0 T, θ t ∈ Ioo (-θp) θp := by
  have hθc : ContinuousOn θ (Icc 0 T) := fun s hs => (h.dθ s hs).continuousAt.continuousWithinAt
  have hkin : ∀ s ∈ Icc 0 T, 0 ≤ q ^ 2 * ρ s ^ 2 * along F.B ψ θ φ s ^ 2 / (2 * m) :=
    fun s _ => by positivity
  intro t ht
  by_contra hout
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at hout
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  rcases hout with h1 | h1
  · obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc' ht.1 (hθc.mono hsub)
      (show -θp ∈ Icc (θ t) (θ 0) from ⟨h1, hθ0.1.le⟩)
    have hsT := hsub hs
    have hEs := energy_along hm.ne' hq hG h hE hsT
    have := hfn (ψ s) (hband s hsT) (φ s)
    have hk := hkin s hsT
    simp only [along, hθs] at hEs hk
    linarith
  · obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc ht.1 (hθc.mono hsub)
      (show θp ∈ Icc (θ 0) (θ t) from ⟨hθ0.2.le, h1⟩)
    have hsT := hsub hs
    have hEs := energy_along hm.ne' hq hG h hE hsT
    have := hfp (ψ s) (hband s hsT) (φ s)
    have hk := hkin s hsT
    simp only [along, hθs] at hEs hk
    linarith

/-- **Turning points of a Boozer guiding-centre orbit** (QA helicity, constant transform `ι₀`).
Let the orbit (energy `E`, moment `μ > 0`) stay in a flux band on which the `BounceWindow`
inequalities hold, and start at a turning point (`ρ 0 = 0`) on the upper flank
(`θ 0 ∈ (0, θ₊)`). Then for every `N` with `N L ≤ T`, `L = halfBounceTime ρ_max c₁ c₂ δ`,
`c₁ = μκ/(Gq)`, there is a monotone sequence of turning points `τ 0 = 0 < τ 1 < … < τ N`
(`v_∥ = 0`, `B > 0`) on alternating flanks, with `τ (k+1) − τ k ≤ L` and `τ k ≤ k L`;
the sequence is constant from `N` on. -/
theorem boozer_bounce_sequence (hm : 0 < m) (hq : 0 < q) (hG : 0 < F.G) {ι₀ : ℝ}
    (hι : ∀ x, F.ι x = ι₀) (hι₀ : 0 < ι₀) (hμ : 0 < μ)
    {T E ψlo ψhi δ θp κ c₂ Blo ρmax : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hc₂ : 0 < c₂)
    (hρmax : 0 < ρmax) (W : BounceWindow F m q μ E ι₀ ψlo ψhi δ θp κ c₂ Blo ρmax)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hE : boozerEnergy F m q μ ψ θ φ ρ 0 = E)
    (hband : ∀ t ∈ Icc 0 T, ψ t ∈ Icc ψlo ψhi) (hρ0 : ρ 0 = 0) (hθ0 : θ 0 ∈ Ioo 0 θp)
    (N : ℕ) (hN : N * halfBounceTime ρmax (μ * κ / (F.G * q)) c₂ δ ≤ T) :
    ∃ τ : ℕ → ℝ, τ 0 = 0 ∧ Monotone τ ∧
      (∀ k < N, τ k < τ (k + 1) ∧
        τ (k + 1) ≤ τ k + halfBounceTime ρmax (μ * κ / (F.G * q)) c₂ δ) ∧
      (∀ k ≤ N, parallelVelocity F m q ψ θ φ ρ (τ k) = 0 ∧ 0 < along F.B ψ θ φ (τ k) ∧
        0 < (-1) ^ k * θ (τ k)) ∧
      (∀ k ≤ N, τ k ≤ k * halfBounceTime ρmax (μ * κ / (F.G * q)) c₂ δ) ∧
      (∀ k, N ≤ k → τ k = τ N) := by
  set L := halfBounceTime ρmax (μ * κ / (F.G * q)) c₂ δ with hL
  set c₁ := μ * κ / (F.G * q) with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  have hLp : 0 < L := halfBounceTime_pos hρmax hc₁ hc₂ hδ
  have hT : 0 ≤ T := le_trans (by positivity) hN
  have hθin := theta_confined hm hq.ne' hG.ne' h hE hband W.forbid_pos W.forbid_neg
    ⟨by linarith [hθ0.1, hθ0.2], hθ0.2⟩
  -- pointwise facts
  have hBpos : ∀ t ∈ Icc 0 T, Blo ≤ along F.B ψ θ φ t := fun t ht =>
    W.B_ge (ψ t) (hband t ht) (θ t) ⟨(hθin t ht).1.le, (hθin t ht).2.le⟩ (φ t)
  have hEn := fun t (ht : t ∈ Icc 0 T) => energy_along hm.ne' hq.ne' hG.ne' h hE ht
  set θ' : ℝ → ℝ := fun t => (μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) *
      along F.Bψ ψ θ φ t + q * ρ t * along F.B ψ θ φ t ^ 2 * F.ι (ψ t) / (F.G * m) with hθ'
  set ρ' : ℝ → ℝ := fun t => -(m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t) *
      (along F.Bφ ψ θ φ t + F.ι (ψ t) * along F.Bθ ψ θ φ t) / (F.G * m * q) with hρ'
  have hB0 : ∀ t ∈ Icc 0 T, 0 < along F.B ψ θ φ t := fun t ht => W.Blo_pos.trans_le (hBpos t ht)
  -- H1
  have H1 : ∀ t ∈ Icc 0 T, |ρ t| ≤ ρmax := by
    intro t ht
    have hB := hB0 t ht
    have hBl := hBpos t ht
    have hEt := hEn t ht
    set B := along F.B ψ θ φ t
    have hkin : 0 ≤ E - μ * B := by
      have : 0 ≤ q ^ 2 * ρ t ^ 2 * B ^ 2 / (2 * m) := by positivity
      linarith
    have hE2 : q ^ 2 * ρ t ^ 2 * B ^ 2 = 2 * m * (E - μ * B) := by
      have := hEt; field_simp at this; linarith
    have hρ2 : ρ t ^ 2 = 2 * m * (E - μ * B) / (q ^ 2 * B ^ 2) := by
      rw [eq_div_iff (by positivity)]; linarith
    have : ρ t ^ 2 ≤ ρmax ^ 2 := by
      rw [hρ2]
      refine le_trans ?_ W.rho_bound
      have hBlo := W.Blo_pos
      have hq2 : 0 < q ^ 2 := by positivity
      have hμB : μ * Blo ≤ μ * B := mul_le_mul_of_nonneg_left hBl hμ.le
      apply div_le_div₀ (by nlinarith) (by nlinarith) (by positivity)
      have := pow_le_pow_left₀ hBlo.le hBl 2
      nlinarith
    exact abs_le_of_sq_le_sq' this hρmax.le |> abs_le.mpr
  -- H2 / H5
  have hfac : ∀ t ∈ Icc 0 T, m * μ ≤ m * μ + q ^ 2 * ρ t ^ 2 * along F.B ψ θ φ t := fun t ht => by
    have := hB0 t ht; nlinarith [sq_nonneg (q * ρ t), mul_nonneg (sq_nonneg (q * ρ t)) this.le]
  have H2 : ∀ t ∈ Icc 0 T, δ ≤ θ t → ρ' t ≤ -c₁ := by
    intro t ht hθt
    have hk := W.flank_pos (ψ t) (hband t ht) (θ t) ⟨hθt, (hθin t ht).2.le⟩ (φ t)
    have hX := hfac t ht
    have hmμ : 0 < m * μ := mul_pos hm hμ
    simp only [hρ', hι, hc₁def, along] at hX ⊢
    rw [div_le_iff₀ (by positivity)]
    have e : -(μ * κ / (F.G * q)) * (F.G * m * q) = -(m * μ * κ) := by field_simp
    rw [e]
    nlinarith [mul_le_mul hX hk hκ.le (by linarith)]
  have H5 : ∀ t ∈ Icc 0 T, θ t ≤ -δ → c₁ ≤ ρ' t := by
    intro t ht hθt
    have hk := W.flank_neg (ψ t) (hband t ht) (θ t) ⟨(hθin t ht).1.le, hθt⟩ (φ t)
    have hX := hfac t ht
    have hmμ : 0 < m * μ := mul_pos hm hμ
    simp only [hρ', hι, hc₁def, along] at hX ⊢
    rw [le_div_iff₀ (by positivity)]
    have e : μ * κ / (F.G * q) * (F.G * m * q) = m * μ * κ := by field_simp
    rw [e]
    nlinarith [mul_le_mul hX (show κ ≤ -(F.Bφ (ψ t) (θ t) (φ t) + ι₀ * F.Bθ (ψ t) (θ t) (φ t))
      by linarith) hκ.le (by linarith)]
  -- H3
  have H3 : ∀ t ∈ Icc 0 T, |θ t| ≤ δ → ρ t ≠ 0 := by
    intro t ht hθt hρt
    have := W.bottom_pass (ψ t) (hband t ht) (θ t) (abs_le.mp hθt) (φ t)
    have hEt := hEn t ht
    rw [hρt] at hEt
    simp only [along] at hEt
    linarith [show q ^ 2 * 0 ^ 2 * F.B (ψ t) (θ t) (φ t) ^ 2 / (2 * m) = 0 by ring]
  -- H4 / H4'
  have hθ'eq : ∀ t ∈ Icc 0 T, θ' t = (2 * E / along F.B ψ θ φ t - μ) * along F.Bψ ψ θ φ t / q +
      parallelVelocity F m q ψ θ φ ρ t * (along F.B ψ θ φ t * ι₀ / F.G) := by
    intro t ht
    have hB := (hB0 t ht).ne'
    have hEt := hEn t ht
    simp only [hθ', hι, parallelVelocity]
    rw [← hEt]
    field_simp
    ring
  have hv2 : ∀ t ∈ Icc 0 T, parallelVelocity F m q ψ θ φ ρ t ^ 2 =
      2 * (E - μ * along F.B ψ θ φ t) / m := by
    intro t ht
    have hEt := hEn t ht
    simp only [parallelVelocity]
    rw [← hEt]; field_simp; ring
  have hstream : ∀ t ∈ Icc 0 T, |θ t| ≤ δ →
      (2 * E / along F.B ψ θ φ t - μ) * |along F.Bψ ψ θ φ t| / q + c₂ ≤
        |parallelVelocity F m q ψ θ φ ρ t| * (along F.B ψ θ φ t * ι₀ / F.G) := by
    intro t ht hθt
    have hs := W.bottom_speed (ψ t) (hband t ht) (θ t) (abs_le.mp hθt) (φ t)
    have hp := W.bottom_pass (ψ t) (hband t ht) (θ t) (abs_le.mp hθt) (φ t)
    have hB := hB0 t ht
    have hv := hv2 t ht
    simp only [along] at hs hp hB hv ⊢
    rw [← hv] at hs
    have hK : 0 ≤ (2 * E / F.B (ψ t) (θ t) (φ t) - μ) * |F.Bψ (ψ t) (θ t) (φ t)| / q + c₂ := by
      have : μ < 2 * E / F.B (ψ t) (θ t) (φ t) := by
        rw [lt_div_iff₀ hB]; nlinarith
      have : 0 ≤ 2 * E / F.B (ψ t) (θ t) (φ t) - μ := by linarith
      positivity
    have hR : 0 ≤ |parallelVelocity F m q ψ θ φ ρ t| * (F.B (ψ t) (θ t) (φ t) * ι₀ / F.G) := by
      positivity
    rw [← pow_le_pow_iff_left₀ hK hR two_ne_zero, mul_pow, sq_abs]
    linarith
  have H4 : ∀ t ∈ Icc 0 T, |θ t| ≤ δ → ρ t < 0 → θ' t ≤ -c₂ := by
    intro t ht hθt hρt
    have hst := hstream t ht hθt
    have hB := hB0 t ht
    have hvneg : parallelVelocity F m q ψ θ φ ρ t < 0 := by
      simp only [parallelVelocity]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hq hρt) hB) hm
    rw [hθ'eq t ht, abs_of_neg hvneg] at *
    have hRp : 0 < along F.B ψ θ φ t * ι₀ / F.G := by positivity
    have hdrift : (2 * E / along F.B ψ θ φ t - μ) * along F.Bψ ψ θ φ t / q ≤
        (2 * E / along F.B ψ θ φ t - μ) * |along F.Bψ ψ θ φ t| / q := by
      have hp := W.bottom_pass (ψ t) (hband t ht) (θ t) (abs_le.mp hθt) (φ t)
      have : 0 ≤ 2 * E / along F.B ψ θ φ t - μ := by
        have : μ < 2 * E / along F.B ψ θ φ t := by
          rw [lt_div_iff₀ hB]; simp only [along] at hB ⊢; nlinarith
        linarith
      gcongr
      exact le_abs_self _
    linarith
  have H4' : ∀ t ∈ Icc 0 T, |θ t| ≤ δ → 0 < ρ t → c₂ ≤ θ' t := by
    intro t ht hθt hρt
    have hst := hstream t ht hθt
    have hB := hB0 t ht
    have hvpos : 0 < parallelVelocity F m q ψ θ φ ρ t := by
      simp only [parallelVelocity]; positivity
    rw [hθ'eq t ht, abs_of_pos hvpos] at *
    have hdrift : -((2 * E / along F.B ψ θ φ t - μ) * |along F.Bψ ψ θ φ t| / q) ≤
        (2 * E / along F.B ψ θ φ t - μ) * along F.Bψ ψ θ φ t / q := by
      have hp := W.bottom_pass (ψ t) (hband t ht) (θ t) (abs_le.mp hθt) (φ t)
      have : 0 ≤ 2 * E / along F.B ψ θ φ t - μ := by
        have : μ < 2 * E / along F.B ψ θ φ t := by
          rw [lt_div_iff₀ hB]; simp only [along] at hB ⊢; nlinarith
        linarith
      rw [← neg_div, ← mul_neg]
      gcongr
      exact neg_abs_le _
    linarith
  -- apply the abstract sequence theorem
  have hθd : ∀ t ∈ Icc 0 T, HasDerivAt θ (θ' t) t := fun t ht => h.dθ t ht
  have hρd : ∀ t ∈ Icc 0 T, HasDerivAt ρ (ρ' t) t := fun t ht => h.dρ t ht
  obtain ⟨τ, h0, hmono, hstep, htp, -, hle, hconst⟩ := bounce_sequence (t₀ := 0) hδ hc₁ hc₂
    hρmax hθd hρd H1 H2 H5 H3 H4 H4' hρ0 hθ0.1 N (by rw [zero_add]; exact hN)
  have hτT : ∀ k ≤ N, τ k ∈ Icc 0 T := fun k hk =>
    ⟨h0 ▸ hmono (Nat.zero_le k), (hle k hk).trans (by
      rw [zero_add]; exact le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hLp.le) hN)⟩
  refine ⟨τ, h0, hmono, hstep, fun k hk => ⟨?_, hB0 _ (hτT k hk), (htp k hk).2⟩,
    fun k hk => by simpa using hle k hk, hconst⟩
  simp only [parallelVelocity, (htp k hk).1]; ring

/-- **Lower bound on a half bounce.** If `|θ'| ≤ Θ` on `[t₀, t₁]`, `θ t₀ > δ` and `θ t₁ < −δ`,
then `t₁ − t₀ ≥ 2δ/Θ`. -/
theorem half_bounce_time_ge {θ θ' : ℝ → ℝ} {t₀ t₁ δ Θ : ℝ} (hΘ : 0 < Θ) (h01 : t₀ < t₁)
    (hθd : ∀ t ∈ Icc t₀ t₁, HasDerivAt θ (θ' t) t) (hbd : ∀ t ∈ Icc t₀ t₁, |θ' t| ≤ Θ)
    (h0 : δ < θ t₀) (h1 : θ t₁ < -δ) : 2 * δ / Θ ≤ t₁ - t₀ := by
  have hm := mvt_ge (f := θ) (f' := θ') (c := -Θ) h01
    (fun t ht => (hθd t ht).continuousAt.continuousWithinAt)
    (fun x hx => hθd x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => by linarith [(abs_le.mp (hbd x ⟨hx.1.le, hx.2.le⟩)).1])
  rw [div_le_iff₀ hΘ]
  linarith

/-! ## Toroidal precession -/

/-- Poloidal drift rate `(μ/q + qρ²B/m) ∂_ψB` along an orbit (the part of `θ̇` not due to
parallel streaming); its negative is the precession rate of `φ − θ/ι`. -/
@[expose] def poloidalDrift (F : BoozerField) (m q μ : ℝ) (ψ θ φ ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (μ / q + q * ρ t ^ 2 * along F.B ψ θ φ t / m) * along F.Bψ ψ θ φ t

/-- `d/dt (θ − ι₀ φ) = (μ/q + qρ²B/m) ∂_ψB` (constant transform `ι₀`): parallel streaming moves
`θ` and `ι₀ φ` together, so only the drift separates them. -/
theorem theta_sub_iota_phi_hasDerivAt {ι₀ T t : ℝ} (hι : ∀ x, F.ι x = ι₀)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun s => θ s - ι₀ * φ s) (poloidalDrift F m q μ ψ θ φ ρ t) t := by
  have := (h.dθ t ht).sub ((h.dφ t ht).const_mul ι₀)
  convert this using 1
  simp only [poloidalDrift, hι]
  ring

/-- **Precession identity** (exact in the model): for `0 ≤ t₀ ≤ t₁ ≤ T`,
`ι₀ (φ t₁ − φ t₀) = (θ t₁ − θ t₀) − ∫_{t₀}^{t₁} (μ/q + qρ²B/m) ∂_ψB dt`. Over a full bounce of
an exact-QA orbit `θ` returns (`tip_theta_eq`), so the toroidal advance per bounce is
`Δφ = −(1/ι₀) ∫ (μ/q + qρ²B/m) ∂_ψB dt`. Needs continuity of `∂_ψB` along the orbit. -/
theorem precession_step {ι₀ T t₀ t₁ : ℝ} (hι : ∀ x, F.ι x = ι₀)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T)
    (hc : ContinuousOn (along F.Bψ ψ θ φ) (Icc t₀ t₁)) :
    ι₀ * (φ t₁ - φ t₀) =
      (θ t₁ - θ t₀) - ∫ t in t₀..t₁, poloidalDrift F m q μ ψ θ φ ρ t := by
  have hsub : ∀ s ∈ Icc t₀ t₁, s ∈ Icc 0 T := fun s hs => ⟨h0.trans hs.1, hs.2.trans h1T⟩
  have hderiv : ∀ x ∈ uIcc t₀ t₁,
      HasDerivAt (fun s => θ s - ι₀ * φ s) (poloidalDrift F m q μ ψ θ φ ρ x) x := by
    intro x hx
    rw [uIcc_of_le h01] at hx
    exact theta_sub_iota_phi_hasDerivAt hι h (hsub x hx)
  have hρ : ContinuousOn ρ (Icc t₀ t₁) :=
    fun s hs => (h.dρ s (hsub s hs)).continuousAt.continuousWithinAt
  have hB : ContinuousOn (along F.B ψ θ φ) (Icc t₀ t₁) :=
    fun s hs => (h.hasDerivAt_B (hsub s hs)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (poloidalDrift F m q μ ψ θ φ ρ) MeasureTheory.volume t₀ t₁ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le h01]
    unfold poloidalDrift
    exact ((continuousOn_const.add
      (((continuousOn_const.mul (hρ.pow 2)).mul hB).div_const m))).mul hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **Two-sided precession bounds.** If the precession rate `−(μ/q + qρ²B/m) ∂_ψB` lies in
`[Ω_lo, Ω_hi]` on `[t₀, t₁]`, then
`(θ t₁ − θ t₀) + Ω_lo (t₁ − t₀) ≤ ι₀ (φ t₁ − φ t₀) ≤ (θ t₁ − θ t₀) + Ω_hi (t₁ − t₀)`. -/
theorem precession_bounds {ι₀ T t₀ t₁ Ωlo Ωhi : ℝ} (hι : ∀ x, F.ι x = ι₀)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ < t₁) (h1T : t₁ ≤ T)
    (hrate : ∀ t ∈ Icc t₀ t₁, Ωlo ≤ -poloidalDrift F m q μ ψ θ φ ρ t ∧
      -poloidalDrift F m q μ ψ θ φ ρ t ≤ Ωhi) :
    (θ t₁ - θ t₀) + Ωlo * (t₁ - t₀) ≤ ι₀ * (φ t₁ - φ t₀) ∧
      ι₀ * (φ t₁ - φ t₀) ≤ (θ t₁ - θ t₀) + Ωhi * (t₁ - t₀) := by
  have hsub : ∀ s ∈ Icc t₀ t₁, s ∈ Icc 0 T := fun s hs => ⟨h0.trans hs.1, hs.2.trans h1T⟩
  set f : ℝ → ℝ := fun s => ι₀ * φ s - θ s with hf
  have hd : ∀ x ∈ Icc t₀ t₁, HasDerivAt f (-poloidalDrift F m q μ ψ θ φ ρ x) x := by
    intro x hx
    have := (theta_sub_iota_phi_hasDerivAt hι h (hsub x hx)).neg
    convert this using 1
    funext s; simp [hf]
  have hfc : ContinuousOn f (Icc t₀ t₁) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have h1 := mvt_ge (f := f) (c := Ωlo) h01 hfc (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => (hrate x ⟨hx.1.le, hx.2.le⟩).1)
  have h2 := mvt_le_neg (f := f) (c := -Ωhi) h01 hfc (fun x hx => hd x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => by linarith [(hrate x ⟨hx.1.le, hx.2.le⟩).2])
  simp only [hf] at h1 h2
  constructor <;> linarith

/-! ## Tip rigidity in exact QA -/

/-- In exact QA (`∂_φB ≡ 0` on `ψ > 0`) the field strength does not depend on `φ`. -/
theorem B_indep_phi_of_exactQA (hQA : ∀ x θ φ, 0 < x → F.Bφ x θ φ = 0) {x : ℝ} (hx : 0 < x)
    (θ φ φ' : ℝ) : F.B x θ φ = F.B x θ φ' := by
  have hd : ∀ y, HasDerivAt (fun y => F.B x θ y) 0 y := by
    intro y
    have hc : HasDerivAt (fun y : ℝ => ((x, θ, y) : ℝ × ℝ × ℝ)) (0, 0, 1) y :=
      (hasDerivAt_const y x).prodMk ((hasDerivAt_const y θ).prodMk (hasDerivAt_id y))
    have := (F.hasFDerivAt_B (x, θ, y) hx).comp_hasDerivAt y hc
    simp only [Function.comp_def, gradCLM_apply, mul_zero, zero_add, mul_one] at this
    rwa [hQA x θ y hx] at this
  exact is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) φ φ'

/-- **Tip rigidity, flux.** In exact QA with `ψ_p' = ι₀ > 0`, any two turning points
(`v_∥ = 0`, `B > 0`) of the same orbit on `[0, T]` have the same flux `ψ` (momentum
conservation with `ρ = 0` at both). -/
theorem tip_psi_eq (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {ι₀ T ta tb : ℝ}
    (hι : ∀ x, F.ι x = ι₀) (hι₀ : 0 < ι₀) (hQA : ∀ x θ φ, 0 < x → F.Bφ x θ φ = 0)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ha : ta ∈ Icc 0 T) (hb : tb ∈ Icc 0 T)
    (hab : ta ≤ tb) (hBa : 0 < along F.B ψ θ φ ta) (hBb : 0 < along F.B ψ θ φ tb)
    (hva : parallelVelocity F m q ψ θ φ ρ ta = 0) (hvb : parallelVelocity F m q ψ θ φ ρ tb = 0) :
    ψ tb = ψ ta := by
  have hstep := (bounce_psip_step_exactQA hm hq hG hQA h ha.1 hab hb.2 hBa hBb hva hvb).2
  have hmono : StrictMonoOn F.ψp (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun x hx => (F.hasDerivAt_ψp x hx).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Ioi] at hx
    rw [(F.hasDerivAt_ψp x hx).deriv, hι]; exact hι₀
  exact hmono.injOn (h.pos tb hb) (h.pos ta ha) hstep

/-- **Tip rigidity, angle.** In exact QA, two turning points of the same orbit at the same flux
`ψ*` whose poloidal angles lie in a set `S` on which `θ ↦ B(ψ*, θ, ·)` is strictly monotone
(e.g. the single-well flank `[0, π]`, `NearAxisQA.reactorQA_single_well`) have the same `θ`:
energy conservation gives `μ B(ψ*, θ_a) = E = μ B(ψ*, θ_b)`. Together with `tip_psi_eq` and
`ρ = 0`, the reduced state `(ψ, θ, ρ)` is the same at every upper turning point. -/
theorem tip_theta_eq (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) (hμ : μ ≠ 0) {T ta tb : ℝ}
    {S : Set ℝ} (hQA : ∀ x θ φ, 0 < x → F.Bφ x θ φ = 0)
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (ha : ta ∈ Icc 0 T) (hb : tb ∈ Icc 0 T)
    (hψ : ψ tb = ψ ta) (hBa : 0 < along F.B ψ θ φ ta) (hBb : 0 < along F.B ψ θ φ tb)
    (hva : parallelVelocity F m q ψ θ φ ρ ta = 0) (hvb : parallelVelocity F m q ψ θ φ ρ tb = 0)
    (hmono : StrictMonoOn (fun θ => F.B (ψ ta) θ 0) S) (hSa : θ ta ∈ S) (hSb : θ tb ∈ S) :
    θ tb = θ ta := by
  have hρa := rho_eq_zero_of_turning hm hq hBa.ne' hva
  have hρb := rho_eq_zero_of_turning hm hq hBb.ne' hvb
  have hEa := boozerEnergy_eq_on hm hq hG h ha
  have hEb := boozerEnergy_eq_on hm hq hG h hb
  have e : μ * along F.B ψ θ φ tb = μ * along F.B ψ θ φ ta := by
    have := hEb.trans hEa.symm
    simp only [boozerEnergy, hρa, hρb] at this
    linarith [show q ^ 2 * 0 ^ 2 * along F.B ψ θ φ ta ^ 2 / (2 * m) = 0 by ring,
      show q ^ 2 * 0 ^ 2 * along F.B ψ θ φ tb ^ 2 / (2 * m) = 0 by ring]
  have e2 : F.B (ψ ta) (θ tb) 0 = F.B (ψ ta) (θ ta) 0 := by
    have := mul_left_cancel₀ hμ e
    simp only [along, hψ] at this
    rw [B_indep_phi_of_exactQA hQA (h.pos ta ha) (θ tb) 0 (φ tb),
      B_indep_phi_of_exactQA hQA (h.pos ta ha) (θ ta) 0 (φ ta)]
    exact this
  exact hmono.injOn hSb hSa e2

/-! ## Non-resonance and the kick form -/

/-- **Quantitative non-resonance.** For `x ∈ [a, b] ⊆ [0, π]`,
`|sin x| ≥ min (sin a) (sin b)` (sine is unimodal on `[0, π]`). -/
theorem abs_sin_ge_of_mem {a b x : ℝ} (ha : 0 ≤ a) (hb : b ≤ π) (hx : x ∈ Icc a b) :
    min (sin a) (sin b) ≤ |sin x| := by
  have hx0 : 0 ≤ sin x := sin_nonneg_of_nonneg_of_le_pi (ha.trans hx.1) (hx.2.trans hb)
  rw [abs_of_nonneg hx0]
  rcases le_total x (π / 2) with h | h
  · exact (min_le_left _ _).trans
      (sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h hx.1)
  · refine (min_le_right _ _).trans ?_
    rw [← sin_pi_sub b, ← sin_pi_sub x]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith)
      (by linarith [hx.2])

/-- `a cos x + b sin x = A sin(x + β)` with `A = ‖b + a i‖ ≥ 0`. -/
theorem exists_amp_phase (a b : ℝ) :
    ∃ A β : ℝ, 0 ≤ A ∧ ∀ x, a * cos x + b * sin x = A * sin (x + β) := by
  refine ⟨‖(⟨b, a⟩ : ℂ)‖, Complex.arg ⟨b, a⟩, norm_nonneg _, fun x => ?_⟩
  have h1 := Complex.norm_mul_cos_arg (⟨b, a⟩ : ℂ)
  have h2 := Complex.norm_mul_sin_arg (⟨b, a⟩ : ℂ)
  simp only at h1 h2
  rw [sin_add]
  linear_combination (-(sin x)) * h1 - cos x * h2

/-- **Exact kick form for a periodic reference orbit.** If on the reference bounce
`[t₀, t₀ + P]` the amplitude `g` is `P`-periodic and the toroidal angle advances by `Δ` per
period (`φ(t + kP) = φ(t) + kΔ`), then the kick integrals of the `sin 2φ` defect over the
successive periods are exactly `A sin(k · 2Δ + β)` (remainder `R = 0`). This is the form assumed
in `bounce_drift_nonresonant`, with phase advance `α = 2Δ`. -/
theorem periodic_kick_form {g φ : ℝ → ℝ} {t₀ P Δ : ℝ} (hP : 0 ≤ P)
    (hgc : ContinuousOn g (Icc t₀ (t₀ + P))) (hφc : ContinuousOn φ (Icc t₀ (t₀ + P)))
    (hg : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), g (t + k * P) = g t)
    (hφ : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), φ (t + k * P) = φ t + k * Δ) :
    ∃ A β : ℝ, 0 ≤ A ∧ ∀ k : ℕ,
      ∫ t in (t₀ + k * P)..(t₀ + (k + 1) * P), g t * sin (2 * φ t) =
        A * sin (k * (2 * Δ) + β) := by
  set Sn := ∫ t in t₀..(t₀ + P), g t * sin (2 * φ t)
  set Cs := ∫ t in t₀..(t₀ + P), g t * cos (2 * φ t)
  obtain ⟨A, β, hA, hAβ⟩ := exists_amp_phase Sn Cs
  refine ⟨A, β, hA, fun k => ?_⟩
  rw [← hAβ]
  have hsub : uIcc t₀ (t₀ + P) = Icc t₀ (t₀ + P) := uIcc_of_le (by linarith)
  have hS : ContinuousOn (fun t => g t * sin (2 * φ t)) (uIcc t₀ (t₀ + P)) := by
    rw [hsub]; exact hgc.mul (continuous_sin.comp_continuousOn (continuousOn_const.mul hφc))
  have hC : ContinuousOn (fun t => g t * cos (2 * φ t)) (uIcc t₀ (t₀ + P)) := by
    rw [hsub]; exact hgc.mul (continuous_cos.comp_continuousOn (continuousOn_const.mul hφc))
  have e1 := intervalIntegral.integral_comp_add_right
    (fun t => g t * sin (2 * φ t)) (a := t₀) (b := t₀ + P) (k * P)
  have e2 : t₀ + k * P = t₀ + ↑k * P := rfl
  rw [show t₀ + ((k : ℝ) + 1) * P = t₀ + P + k * P by ring, ← e1]
  rw [intervalIntegral.integral_congr (g := fun t => cos (k * (2 * Δ)) * (g t * sin (2 * φ t)) +
    sin (k * (2 * Δ)) * (g t * cos (2 * φ t))) ?_]
  · rw [intervalIntegral.integral_add (hS.intervalIntegrable.const_mul _)
      (hC.intervalIntegrable.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    ring
  · intro t ht
    rw [hsub] at ht
    simp only
    rw [hg k t ht, hφ k t ht, show 2 * (φ t + k * Δ) = 2 * φ t + k * (2 * Δ) by ring, sin_add]
    ring

/-- **Drift theorem with a periodic reference orbit.** Under the hypotheses of
`bounce_drift_nonresonant` except the kick form: if a reference orbit is periodic as in
`periodic_kick_form` (period `P`, toroidal advance `Δ` per period, amplitude `g`), the actual
kicks are within `R` of the reference kicks, and `sin Δ ≠ 0`, then
`|q| |ψ_p(ψ(τ N)) − ψ_p(ψ(τ 0))| ≤ A/|sin Δ| + N R` for the reference amplitude `A`. -/
theorem bounce_drift_of_reference (hm : m ≠ 0) (hq : q ≠ 0) (hG : F.G ≠ 0) {T R t₀ P Δ : ℝ}
    {g φr : ℝ → ℝ} {τ : ℕ → ℝ} {N : ℕ}
    (h : BoozerGCOrbitOn F m q μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0) (hNT : τ N ≤ T)
    (hc : ContinuousOn (along F.Bφ ψ θ φ) (Icc 0 T))
    (hB : ∀ k ≤ N, 0 < along F.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity F m q ψ θ φ ρ (τ k) = 0)
    (hP : 0 ≤ P) (hgc : ContinuousOn g (Icc t₀ (t₀ + P)))
    (hφc : ContinuousOn φr (Icc t₀ (t₀ + P)))
    (hg : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), g (t + k * P) = g t)
    (hφ : ∀ k : ℕ, ∀ t ∈ Icc t₀ (t₀ + P), φr (t + k * P) = φr t + k * Δ)
    (hΔ : sin Δ ≠ 0)
    (hclose : ∀ k < N, |(∫ t in τ k..τ (k + 1), qaKick F m q μ ψ θ φ ρ t) -
      ∫ t in (t₀ + k * P)..(t₀ + (k + 1) * P), g t * sin (2 * φr t)| ≤ R) :
    ∃ A : ℝ, 0 ≤ A ∧
      |q| * |F.ψp (ψ (τ N)) - F.ψp (ψ (τ 0))| ≤ A / |sin Δ| + N * R := by
  obtain ⟨A, β, hA, hkick⟩ := periodic_kick_form hP hgc hφc hg hφ
  refine ⟨A, hA, ?_⟩
  have hα : sin (2 * Δ / 2) ≠ 0 := by rwa [mul_div_cancel_left₀ _ two_ne_zero]
  have := bounce_drift_nonresonant (A := A) (α := 2 * Δ) (β := β) (R := R) hm hq hG h hτ h0 hNT
    hc hB hv hα (fun k hk => by rw [← hkick k]; exact hclose k hk)
  rwa [mul_div_cancel_left₀ _ two_ne_zero, abs_of_nonneg hA] at this

/-! ## Sanity checks -/

/-- Sanity (`halfBounceTime` value): `ρ_max = c₁ = c₂ = δ = 1` gives `4 + 2 = 6`. -/
theorem halfBounceTime_one : halfBounceTime 1 1 1 1 = 6 := by norm_num [halfBounceTime]

/-- Sanity (level-crossing lemma, accepted fixture): `f t = −t` on `[0, 1]` starts at the level
`0` with derivative `−1`, so it stays strictly below `0` on `(0, 1]`. -/
theorem level_fixture : ∀ t ∈ Ioc (0 : ℝ) 1, -t < 0 := by
  have := lt_of_level_deriv_neg (f := fun t : ℝ => -t) (a := 0) (b := 1) (c := 0)
    continuous_neg.continuousOn (by norm_num)
    (fun t _ _ => ⟨-1, by norm_num, (hasDerivAt_id t).neg⟩)
  simpa using this

/-- Sanity (non-resonance fixture): on `[π/6, 5π/6]`, `|sin x| ≥ 1/2`. -/
theorem abs_sin_ge_half {x : ℝ} (hx : x ∈ Icc (π / 6) (5 * π / 6)) : 1 / 2 ≤ |sin x| := by
  have h := abs_sin_ge_of_mem (by positivity) (by linarith [pi_pos]) hx
  have e : sin (5 * π / 6) = 1 / 2 := by
    rw [show 5 * π / 6 = π - π / 6 by ring, sin_pi_sub, sin_pi_div_six]
  rwa [sin_pi_div_six, e, min_self] at h

/-- Sanity (degenerate kick form): a zero amplitude gives zero kicks. -/
theorem periodic_kick_zero {φ : ℝ → ℝ} {t₀ P : ℝ} (k : ℕ) :
    ∫ t in (t₀ + k * P)..(t₀ + (k + 1) * P), (0 : ℝ) * sin (2 * φ t) = 0 := by simp

/-- Sanity (non-vacuity of `precession_step`): for the explicit constant-field orbit
`constField_orbit` (no `∂_ψB`, so no drift) the identity reduces to
`ι₀ (φ t₁ − φ t₀) = θ t₁ − θ t₀`. -/
theorem precession_constField {B₀ ι₀ G m q μ ψ₀ θ₀ φ₀ ρ₀ T : ℝ} (hψ₀ : 0 < ψ₀) {t₀ t₁ : ℝ}
    (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁) (h1T : t₁ ≤ T) :
    ι₀ * ((φ₀ + q * ρ₀ * B₀ ^ 2 / (G * m) * t₁) - (φ₀ + q * ρ₀ * B₀ ^ 2 / (G * m) * t₀)) =
      (θ₀ + ι₀ * (q * ρ₀ * B₀ ^ 2 / (G * m)) * t₁) -
        (θ₀ + ι₀ * (q * ρ₀ * B₀ ^ 2 / (G * m)) * t₀) := by
  have := precession_step (F := constField B₀ ι₀ G) (m := m) (q := q) (μ := μ) (ι₀ := ι₀)
    (fun _ => rfl) ((constField_orbit (μ := μ) (θ₀ := θ₀) (φ₀ := φ₀) (ρ₀ := ρ₀) hψ₀).on T)
    h0 h01 h1T (by simp only [constField]; exact continuousOn_const)
  simpa [poloidalDrift, constField, along] using this

end PlasmaLean.Kinetic.Boozer
