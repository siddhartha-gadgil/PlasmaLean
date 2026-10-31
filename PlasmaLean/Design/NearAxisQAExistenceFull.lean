/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQAExistence
public import PlasmaLean.Theory.Kinetic.BoozerGCForward

/-!
# Near-QA alpha orbits on a prescribed horizon (audit finding MA-M1, note N-26)

`NearAxisQAExistence` constructs off-axis orbits of `reactorQA` only on some unquantified
`[0, T]`. This file proves existence on **prescribed** horizons, by an a priori bound in the chart
`ψ > 0` (route (ii) of `notes/theory/orbit-existence.md`) and by an explicit radial-speed bound
(route (i)).

**Method.** A solution of the first-order system (`boozerVF`) is continued forward
(`Boozer.boozerGCOrbitOn_exists_of_region`) as long as it stays in a closed band
`ψ₀ − D' ≤ ψ ≤ ψ₀ + D'`, `|ρ| ≤ 0.055` m, on which the vector field is bounded
(`reactorQA_VF_bounded`, by `2π`-periodicity in the angles; `orbit_exists_of_forward_band`).
That solutions stay in the band is a bootstrap (`Boozer.boozer_bootstrap`): while a solution has
stayed in a slightly larger band it is a genuine orbit, and an estimate for orbits pins it to the
smaller band.

* **Route (ii), band estimate** (`averaged_drift`, `band_estimate`): for a passing 3.5 MeV alpha
  (`v_∥² ≥ 0.81 v²`) the averaged drift bound of `NearAxisQAAveraged` and the orbit width give
  the two-sided bound `|ψ t − ψ 0| ≤ D(t)`, `D(t) = (|G| Δρ + (2 ∑ Aⱼ/Ω₀ + 11 t))/ι₀`
  (`Dpsi`, ≈ `2.593 + 26.07 t` T m²). Hence (`alpha_band_orbit_exists`): births with
  `D(T) < ψ₀` and `ψ₀ + D(T) < ψ_a` have an orbit on all of `[0, T]` staying in
  `|ψ − ψ₀| ≤ D(T)`. Instances: `alpha_band_orbit_exists_short` (`T = 8 × 10⁻⁴ s`,
  `2.75 ≤ ψ₀ ≤ 5.5`), `alpha_band_orbit_exists_005` (`T = 0.05 s`, `4 ≤ ψ₀ ≤ 4.3`), with the
  constructed witness `alpha_band_nonvacuous_005`.
* **Route (i), explicit horizon** (`radius_lipschitz`, `alpha_orbit_exists_explicit`): for every
  birth of the original class (`0 < ψ₀ ≤ ψ_start`, energy `E_α`, `μ ≥ 0`, any pitch) the radius
  `r = √(2ψ/B₀)` moves at most `57000` m/s, so an orbit exists on `[0, r₀/285000]` (`1.49 μs` at
  `r₀ = a/4`); `alpha_trapped_reactorQA_averaged_explicit` combines this with the averaged
  confinement theorem.
* **Limits** (sanity theorems): `Dpsi_gt_psiStart` (the band method never reaches births with
  `ψ₀ ≤ ψ_start`, the class of `alpha_trapped_reactorQA*`, because the orbit-width term
  `|G| Δρ/ι₀ ≈ 2.59 T m²` already exceeds `ψ_start ≈ 0.51 T m²`); `band_empty_of_ge`,
  `band_empty_Tav` (no band survives for `T ≥ 0.06 s`, in particular not for `T_av = 0.19 s`).

**Not proved.** Existence on `[0, 0.19 s]` (or `[0, 8 × 10⁻⁴ s]`) for the original class
`ψ₀ ≤ ψ_start`. `Dpsi_gt_psiStart` and `band_empty_Tav` are proved limits of the band method, not
obstructions to existence: whether orbits of the original class leave the chart `ψ > 0` before
0.19 s is not proved (the orbit width in `ψ` is comparable to `ψ_start`); coordinates through
the axis (route (iii)) are the proposed route. All statements are about the supplied
guiding-centre model and the truncated near-axis field (see `NearAxisQA`).
-/

public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQAExistenceFull
open PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer PlasmaLean.Kinetic.LiePoly
  PlasmaLean.Design.NearAxisQA PlasmaLean.Design.NearAxisQAAveraged Set Real

/-- **Averaged helical-momentum drift** along a passing 3.5 MeV alpha orbit of `reactorQA` on
`[0, t]` that has stayed in `ψ ≤ ψ_a`: `|P t − P 0| ≤ 2 (1935 + 218 + 93) q/Ω₀ + 11 q t`
(the drift bound inside `alpha_trapped_reactorQA_averaged_of_le`, extracted as a two-sided
estimate). -/
theorem averaged_drift {μ t : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ t)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (ht : 0 ≤ t) (hhist : ∀ s ∈ Icc 0 t, ψ s ≤ psiEdge) :
    |helicalMomentum reactorQA qα 0 1 ψ ρ t - helicalMomentum reactorQA qα 0 1 ψ ρ 0| ≤
      2 * ((1935 + 218 + 93) * cq) / Om0 + 11 * cq * t := by
  set σ := sgn0 ψ θ φ ρ with hσdef
  have hσ2 : σ ^ 2 = 1 := sgn0_sq
  set X := orbX σ μ ψ θ φ ρ with hX
  let a : ℕ → ℝ → ℝ := fun j r => if j % 2 = 0 then eval (amp j) (X r) else 0
  let b : ℕ → ℝ → ℝ := fun j r => if j % 2 = 1 then eval (amp j) (X r) else 0
  let A : ℕ → ℝ := fun j => ([1935, 218, 93, 11] : List ℝ).getD j 0 * cq
  have hH : ∀ s ∈ Icc 0 t, ∀ s' ∈ Icc 0 s, ψ s' ≤ psiEdge :=
    fun s hs s' hs' => hhist s' ⟨hs'.1, hs'.2.trans hs.2⟩
  have hd := osc_ibp_drift_iter (T := t) (Φ := fun r => 2 * σ * φ r) (Ω := Omf σ μ ψ θ φ ρ)
    (e := fun _ => 0) (η := 0) (Ω₀ := Om0) (by norm_num [Om0])
    (fun s hs => by
      obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs (hH s hs)
      refine ((h.dφ s hs).const_mul (2 * σ)).congr_deriv ?_
      simp only [Omf, orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt,
        along, reactorQA, field]
      field_simp)
    (fun s hs => by
      obtain ⟨⟨-, -, -, -, -, -, h5, -, -, -, h7, -⟩, -, -⟩ :=
        region_facts hμ h hE hpitch hs (hH s hs)
      simp only [Om0, Omf]
      gcongr)
    (fun s _ => by simp) ⟨ht, le_rfl⟩ 3 (helicalMomentum reactorQA qα 0 1 ψ ρ) a b A
    (fun s hs => by
      obtain ⟨-, hB, -⟩ := region_facts hμ h hE hpitch hs (hH s hs)
      refine (helicalMomentum_hasDerivAt_on mα_pos.ne' qα_ne G_ne 0 1 h hs).congr_deriv ?_
      simp only [a, b, Nat.zero_mod, ite_true, show ¬ (0 % 2 = 1) by norm_num, ite_false,
        zero_mul, add_zero]
      rw [hX, eval_amp0, orbX_sq5 hσ2, orbX_8]
      simp only [orbX, List.getD_cons_succ, List.getD_cons_zero, vel, parallelVelocity, Bt,
        along, symmetryDefect, reactorQA, field, nearAxisBφ, mα_eq, qα_eq, cm, cq, cmus, cvs,
        cb1]
      simp only [Bt, along] at hB
      rcases sgn0_cases (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) with h1 | h1
      · rw [show σ = 1 from hσdef.trans h1]; push_cast; field_simp; ring
      · rw [show σ = -1 from hσdef.trans h1]
        simp only [mul_neg, neg_mul, mul_one, sin_neg]
        push_cast; field_simp; ring)
    (fun j hj s hs => by
      obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs (hH s hs)
      have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
      interval_cases j
      · simpa [a, b] using hd
      · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
      · simpa [a, b] using hd)
    (fun j hj s hs => by
      obtain ⟨-, hB, hW⟩ := region_facts hμ h hE hpitch hs (hH s hs)
      have hd := amp_ratio_hasDerivAt h hs hσ2 hB hW j
      interval_cases j
      · simpa [a, b] using hasDerivAt_const s (0 : ℝ)
      · simpa [a, b] using hd
      · simpa [a, b] using hasDerivAt_const s (0 : ℝ))
    (fun j hj s hs => by
      obtain ⟨hreg, -, -⟩ := region_facts hμ h hE hpitch hs (hH s hs)
      interval_cases j
      · simpa [a, b, A] using global_bound glob_0 hreg
      · simpa [a, b, A] using global_bound glob_1 hreg
      · simpa [a, b, A] using global_bound glob_2 hreg
      · simpa [a, b, A] using amp3_bound hreg)
  refine hd.trans (le_of_eq ?_)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, A]
  norm_num
  ring

/-- Half-width (in `ψ`, T m²) of the two-sided band certified on `[0, T]`:
`D(T) = (|G| Δρ + (2 (1935 + 218 + 93) q/Ω₀ + 11 q T)/q)/ι₀`; `D(T) ≈ 2.593 + 26.07 T`. -/
@[expose] def Dpsi (T : ℝ) : ℝ :=
  ((581 / 10) * Δρv + (2 * ((1935 + 218 + 93) * cq) / Om0 + 11 * cq * T) / qα) / (211 / 500)

/-- **Two-sided band estimate.** A passing 3.5 MeV alpha orbit of `reactorQA` on `[0, t]` that
has stayed in `ψ ≤ ψ_a` satisfies `|ψ t − ψ 0| ≤ D(t)`. Unlike the trapping theorems, this bounds
`ψ` from **below** as well (it is what keeps the orbit off the axis). -/
theorem band_estimate {μ t : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ t)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (hpitch : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2)
    (ht : 0 ≤ t) (hhist : ∀ s ∈ Icc 0 t, ψ s ≤ psiEdge) :
    |ψ t - ψ 0| ≤ Dpsi t := by
  have hd := averaged_drift hμ h hE hpitch ht hhist
  have hρ := rho_dev hμ h hE hpitch ⟨ht, le_rfl⟩ hhist
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have e : 211 / 500 * (ψ t - ψ 0) =
      (581 / 10) * (ρ t - ρ 0) -
        (helicalMomentum reactorQA qα 0 1 ψ ρ t - helicalMomentum reactorQA qα 0 1 ψ ρ 0) / qα := by
    simp only [helicalMomentum, reactorQA, field]
    field_simp
    ring
  have h1 : 211 / 500 * |ψ t - ψ 0| ≤ (581 / 10) * Δρv +
      (2 * ((1935 + 218 + 93) * cq) / Om0 + 11 * cq * t) / qα := by
    rw [show 211 / 500 * |ψ t - ψ 0| = |211 / 500 * (ψ t - ψ 0)| by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 211 / 500)], e]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 581 / 10)]
      exact mul_le_mul_of_nonneg_left hρ (by norm_num)
    · rw [abs_div, abs_of_pos hq]
      exact div_le_div_of_nonneg_right hd hq.le
  unfold Dpsi
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- `D` is monotone in the horizon. -/
theorem Dpsi_mono {t T : ℝ} (htT : t ≤ T) : Dpsi t ≤ Dpsi T := by
  unfold Dpsi
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hc : (0 : ℝ) ≤ 11 * cq := by norm_num [cq]
  gcongr

/-- `D(T) ≥ 0` for `T ≥ 0`. -/
theorem Dpsi_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ Dpsi T := by
  refine le_trans ?_ (Dpsi_mono hT)
  norm_num [Dpsi, Δρv, Om0, cq, cm, qα]

/-! ## Compactness: the vector field is bounded on bands (periodicity in the angles) -/

/-- The near-axis QA vector field is `2π`-periodic in both Boozer angles. -/
theorem boozerVF_periodic (m q μ ψ θ φ ρ : ℝ) (n k : ℤ) :
    boozerVF reactorQA m q μ (ψ, θ - n * (2 * π), φ - k * (2 * π), ρ) =
      boozerVF reactorQA m q μ (ψ, θ, φ, ρ) := by
  have c1 : cos (θ - n * (2 * π)) = cos θ := cos_sub_int_mul_two_pi θ n
  have s1 : sin (θ - n * (2 * π)) = sin θ := sin_sub_int_mul_two_pi θ n
  have e2 : ∀ x : ℝ, ∀ j : ℤ, 2 * (x - j * (2 * π)) = 2 * x - ((2 * j : ℤ) : ℝ) * (2 * π) :=
    fun x j => by push_cast; ring
  have c2 : cos (2 * (θ - n * (2 * π))) = cos (2 * θ) := by
    rw [e2]; exact cos_sub_int_mul_two_pi _ _
  have s2 : sin (2 * (θ - n * (2 * π))) = sin (2 * θ) := by
    rw [e2]; exact sin_sub_int_mul_two_pi _ _
  have c3 : cos (2 * (φ - k * (2 * π))) = cos (2 * φ) := by
    rw [e2]; exact cos_sub_int_mul_two_pi _ _
  have s3 : sin (2 * (φ - k * (2 * π))) = sin (2 * φ) := by
    rw [e2]; exact sin_sub_int_mul_two_pi _ _
  simp only [boozerVF, reactorQA, field, nearAxisB, nearAxisBψ, nearAxisBθ, nearAxisBφ, c1, s1,
    c2, s2, c3, s3]

/-- **The vector field is bounded on every band** `a ≤ ψ ≤ b`, `|ρ| ≤ ρ_m` with `a > 0` (all
angles): by periodicity it suffices to bound it on a compact box in `{ψ > 0}`. -/
theorem reactorQA_VF_bounded (m q μ : ℝ) {a b ρm : ℝ} (ha : 0 < a) :
    ∃ M, ∀ s : ℝ × ℝ × ℝ × ℝ, a ≤ s.1 → s.1 ≤ b → |s.2.2.2| ≤ ρm →
      ‖boozerVF reactorQA m q μ s‖ ≤ M := by
  set C : Set (ℝ × ℝ × ℝ × ℝ) :=
    Icc a b ×ˢ (Icc 0 (2 * π) ×ˢ (Icc 0 (2 * π) ×ˢ Icc (-ρm) ρm)) with hCdef
  have hC : IsCompact C :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hCU : C ⊆ chartDomain := fun s hs => lt_of_lt_of_le ha hs.1.1
  have hcont : ContinuousOn (boozerVF reactorQA m q μ) C :=
    (NearAxisQAExistence.field_boozerVF_contDiffOn _ _ _ _ _ _ _ _ m q μ).continuousOn.mono hCU
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  refine ⟨M, fun s h1 h2 h3 => ?_⟩
  obtain ⟨ψ, θ, φ, ρ⟩ := s
  have hθ := toIcoMod_mem_Ico two_pi_pos 0 θ
  have hφ := toIcoMod_mem_Ico two_pi_pos 0 φ
  have e : boozerVF reactorQA m q μ (ψ, θ, φ, ρ) =
      boozerVF reactorQA m q μ (ψ, toIcoMod two_pi_pos 0 θ, toIcoMod two_pi_pos 0 φ, ρ) := by
    rw [toIcoMod, toIcoMod, zsmul_eq_mul, zsmul_eq_mul, boozerVF_periodic]
  rw [e]
  refine hM _ ⟨⟨h1, h2⟩, ⟨hθ.1, ?_⟩, ⟨hφ.1, ?_⟩, abs_le.mp h3⟩
  · have := hθ.2; rw [zero_add] at this; exact this.le
  · have := hφ.2; rw [zero_add] at this; exact this.le

/-! ## Initial data -/

/-- Guiding-centre energy `q²ρ²B²/(2m) + μB` of the state `s = (ψ, θ, φ, ρ)` (alpha,
`reactorQA`). -/
@[expose] def gcEnergy (μ : ℝ) (s : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  qα ^ 2 * s.2.2.2 ^ 2 * reactorQA.B s.1 s.2.1 s.2.2.1 ^ 2 / (2 * mα) +
    μ * reactorQA.B s.1 s.2.1 s.2.2.1

/-- Parallel velocity `q ρ B/m` of the state `s` (alpha, `reactorQA`). -/
@[expose] def gcVpar (s : ℝ × ℝ × ℝ × ℝ) : ℝ := qα * s.2.2.2 * reactorQA.B s.1 s.2.1 s.2.2.1 / mα

/-- Parallel-gyroradius bound from energy conservation: on `0 < ψ ≤ ψ_a`, energy `E_α` and
`μ ≥ 0` give `|ρ| ≤ 0.055 m`. -/
theorem abs_rho_le {μ ψ θ φ ρ : ℝ} (hμ : 0 ≤ μ) (hψ : 0 < ψ) (hψa : ψ ≤ psiEdge)
    (hE : qα ^ 2 * ρ ^ 2 * reactorQA.B ψ θ φ ^ 2 / (2 * mα) + μ * reactorQA.B ψ θ φ = Eα) :
    |ρ| ≤ 11 / 200 := by
  have hB := reactorQA_B_bounds (θ := θ) (φ := φ) hψ hψa
  have hm := mα_pos
  have hμB : 0 ≤ μ * reactorQA.B ψ θ φ := mul_nonneg hμ (by linarith [hB.1])
  have h1 : qα ^ 2 * ρ ^ 2 * reactorQA.B ψ θ φ ^ 2 ≤ 2 * mα * Eα := by
    have : qα ^ 2 * ρ ^ 2 * reactorQA.B ψ θ φ ^ 2 / (2 * mα) ≤ Eα := by linarith
    rwa [div_le_iff₀ (by positivity), mul_comm Eα] at this
  have hB2 : (4.93 : ℝ) ^ 2 ≤ reactorQA.B ψ θ φ ^ 2 := by nlinarith [hB.1]
  have h2 : qα ^ 2 * ρ ^ 2 * 4.93 ^ 2 ≤ 2 * mα * Eα := by
    have : 0 ≤ qα ^ 2 * ρ ^ 2 := by positivity
    nlinarith
  have h3 : ρ ^ 2 ≤ (11 / 200) ^ 2 := by
    have hn : 2 * mα * Eα < qα ^ 2 * 4.93 ^ 2 * (11 / 200) ^ 2 := by norm_num [mα, qα, Eα]
    have hq2 : 0 < qα ^ 2 * 4.93 ^ 2 := by norm_num [qα]
    by_contra hc
    push Not at hc
    nlinarith
  exact abs_le_of_sq_le_sq' h3 (by norm_num) |> abs_le.mpr

/-! ## From a forward band bound to existence on the horizon -/

/-- **Existence from a forward band bound.** Let an alpha birth state `s₀` (`μ ≥ 0`, energy
`E_α`) and `0 ≤ D' < ψ₀` with `ψ₀ + D' ≤ ψ_a` be such that every solution of the first-order
system from `s₀` on `[0, c]` (`c ≤ T`) stays in `|ψ − ψ₀| ≤ D'`. Then an orbit
`BoozerGCOrbitOn reactorQA … T` from `s₀` exists on all of `[0, T]` and stays in the band.
(Energy conservation bounds `ρ`, periodicity bounds the vector field, and
`boozerGCOrbitOn_exists_of_region` continues the local solution.) -/
theorem orbit_exists_of_forward_band {μ T D' : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hT : 0 ≤ T)
    (hμ : 0 ≤ μ) (hE : gcEnergy μ s₀ = Eα) (hD'0 : 0 ≤ D') (hlow : D' < s₀.1)
    (hup : s₀.1 + D' ≤ psiEdge)
    (key : ∀ c ∈ Icc 0 T, ∀ α : ℝ → ℝ × ℝ × ℝ × ℝ, α 0 = s₀ →
      (∀ t ∈ Icc 0 c, HasDerivAt α (boozerVF reactorQA mα qα μ (α t)) t) →
      ∀ t ∈ Icc 0 c, |(α t).1 - s₀.1| ≤ D') :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T ∧ ∀ t ∈ Icc 0 T, |ψ t - s₀.1| ≤ D' := by
  set ψ₀ := s₀.1 with hψ₀
  set R : Set (ℝ × ℝ × ℝ × ℝ) :=
    {s | ψ₀ - D' ≤ s.1} ∩ ({s | s.1 ≤ ψ₀ + D'} ∩ {s | |s.2.2.2| ≤ 11 / 200}) with hRdef
  have hRc : IsClosed R :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_const).inter
        (isClosed_le (by fun_prop) continuous_const))
  have hRU : R ⊆ chartDomain := fun s hs => by
    have := hs.1; change 0 < s.1; simp only [mem_ofPred_eq] at this; linarith
  obtain ⟨M, hM⟩ := reactorQA_VF_bounded mα qα μ (a := ψ₀ - D') (b := ψ₀ + D')
    (ρm := 11 / 200) (by linarith)
  obtain ⟨ψ, θ, φ, ρ, h0, h1, h2, h3, horb, hmem⟩ := boozerGCOrbitOn_exists_of_region hT
    (NearAxisQAExistence.field_boozerVF_contDiffOn _ _ _ _ _ _ _ _ mα qα μ)
    (by linarith : 0 < s₀.1) hRc hRU (fun s hs => hM s hs.1 hs.2.1 hs.2.2)
    (fun c hc α hα0 hα t ht => by
      have hb := key c hc α hα0 hα
      have horb : BoozerGCOrbitOn reactorQA mα qα μ (fun t => (α t).1) (fun t => (α t).2.1)
          (fun t => (α t).2.2.1) (fun t => (α t).2.2.2) c :=
        boozerGCOrbitOn_of_flow hα (fun s hs => by
          have := (abs_le.mp (hb s hs)).1; linarith)
      have hen := boozerEnergy_eq_on mα_pos.ne' qα_ne G_ne horb ht
      have hE0 : boozerEnergy reactorQA mα qα μ (fun t => (α t).1) (fun t => (α t).2.1)
          (fun t => (α t).2.2.1) (fun t => (α t).2.2.2) 0 = Eα := by
        change gcEnergy μ (α 0) = Eα; rw [hα0]; exact hE
      rw [hE0] at hen
      have hbt := abs_le.mp (hb t ht)
      refine ⟨by simp only [mem_ofPred_eq]; linarith, by simp only [mem_ofPred_eq]; linarith, ?_⟩
      exact abs_rho_le hμ (by linarith) (by linarith) hen)
  refine ⟨ψ, θ, φ, ρ, h0, h1, h2, h3, horb, fun t ht => ?_⟩
  have := hmem t ht
  simp only [hRdef, mem_inter_iff, mem_ofPred_eq] at this
  exact abs_le.mpr ⟨by linarith [this.1], by linarith [this.2.1]⟩

/-! ## Route (ii): existence on a prescribed horizon for births in a band -/

/-- **Existence on the full horizon `[0, T]` for alphas born in a band away from the axis.**
Let `T ≥ 0` and let the birth state `s₀ = (ψ₀, θ₀, φ₀, ρ₀)` of an alpha (`μ ≥ 0`, energy
`E_α = 3.5 MeV`, passing pitch `v_∥² ≥ 0.81 · 2E_α/m`) satisfy `D(T) < ψ₀` and
`ψ₀ + D(T) < ψ_a`. Then there is a guiding-centre orbit `BoozerGCOrbitOn reactorQA … T` on the
whole interval `[0, T]` starting at `s₀`, and it stays in the band `|ψ − ψ₀| ≤ D(T)`
(in particular off the axis and inside `ψ_a`). -/
theorem alpha_band_orbit_exists {μ T : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hT : 0 ≤ T) (hμ : 0 ≤ μ)
    (hE : gcEnergy μ s₀ = Eα) (hpitch : 81 / 100 * (2 * Eα / mα) ≤ gcVpar s₀ ^ 2)
    (hlow : Dpsi T < s₀.1) (hup : s₀.1 + Dpsi T < psiEdge) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T ∧ ∀ t ∈ Icc 0 T, |ψ t - s₀.1| ≤ Dpsi T := by
  set ψ₀ := s₀.1 with hψ₀
  set D' := Dpsi T with hD'
  have hD'0 : 0 ≤ D' := Dpsi_nonneg hT
  set δ := min (ψ₀ - D') (psiEdge - ψ₀ - D') / 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min (ψ₀ - D') (psiEdge - ψ₀ - D') := lt_min (by linarith) (by linarith)
    positivity
  have hδ1 : δ < ψ₀ - D' := by
    have := min_le_left (ψ₀ - D') (psiEdge - ψ₀ - D'); linarith
  have hδ2 : δ < psiEdge - ψ₀ - D' := by
    have := min_le_right (ψ₀ - D') (psiEdge - ψ₀ - D'); linarith
  refine orbit_exists_of_forward_band hT hμ hE hD'0 hlow hup.le (fun c hc α hα0 hα => ?_)
  refine boozer_bootstrap (D := D' + δ) hD'0 (by linarith) (by linarith) (by rw [hα0]) hα
    (fun t ht horb hhist => ?_)
  have hE' : boozerEnergy reactorQA mα qα μ (fun t => (α t).1) (fun t => (α t).2.1)
      (fun t => (α t).2.2.1) (fun t => (α t).2.2.2) 0 = Eα := by
    change gcEnergy μ (α 0) = Eα; rw [hα0]; exact hE
  have hp' : 81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα (fun t => (α t).1)
      (fun t => (α t).2.1) (fun t => (α t).2.2.1) (fun t => (α t).2.2.2) 0 ^ 2 := by
    change 81 / 100 * (2 * Eα / mα) ≤ gcVpar (α 0) ^ 2; rw [hα0]; exact hpitch
  have hb := band_estimate hμ horb hE' hp' ht.1 (fun s hs => by
    have := (abs_le.mp (hhist s hs)).2; linarith)
  simp only [hα0] at hb
  exact hb.trans (Dpsi_mono (ht.2.trans hc.2))

/-- Corollary in absolute terms: under the hypotheses of `alpha_band_orbit_exists`, with
`ψ_lo ≤ ψ₀ − D(T)` and `ψ₀ + D(T) ≤ ψ_hi`, the orbit exists on `[0, T]` and stays in
`[ψ_lo, ψ_hi]`. -/
theorem alpha_band_orbit_exists_of_le {μ T ψlo ψhi : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hT : 0 ≤ T)
    (hμ : 0 ≤ μ) (hE : gcEnergy μ s₀ = Eα) (hpitch : 81 / 100 * (2 * Eα / mα) ≤ gcVpar s₀ ^ 2)
    (hlo : 0 < ψlo) (hhi : ψhi < psiEdge) (h1 : ψlo ≤ s₀.1 - Dpsi T) (h2 : s₀.1 + Dpsi T ≤ ψhi) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T ∧ ∀ t ∈ Icc 0 T, ψlo ≤ ψ t ∧ ψ t ≤ ψhi := by
  obtain ⟨ψ, θ, φ, ρ, h0, h1', h2', h3, horb, hb⟩ :=
    alpha_band_orbit_exists hT hμ hE hpitch (by linarith) (by linarith)
  refine ⟨ψ, θ, φ, ρ, h0, h1', h2', h3, horb, fun t ht => ?_⟩
  have := abs_le.mp (hb t ht)
  constructor <;> linarith [this.1, this.2]

/-- `D(8 × 10⁻⁴ s) ≤ 2.65` T m². -/
theorem Dpsi_short : Dpsi 8e-4 ≤ 2.65 := by norm_num [Dpsi, Δρv, Om0, cq, cm, qα]

/-- `D(0.05 s) ≤ 3.9` T m². -/
theorem Dpsi_005 : Dpsi (5 / 100) ≤ 3.9 := by norm_num [Dpsi, Δρv, Om0, cq, cm, qα]

/-- **Full-horizon existence on the worst-case horizon `[0, 8 × 10⁻⁴ s]`** (the horizon of
`NearAxisQA.alpha_trapped_reactorQA`) for every 3.5 MeV passing alpha (`μ ≥ 0`,
`v_∥² ≥ 0.81 v²`) born at `2.75 ≤ ψ₀ ≤ 5.5` T m² (`0.98 m ≤ r₀ ≤ 1.39 m`, i.e.
`0.58 a ≲ r₀ ≲ 0.82 a`), any angles: the orbit exists on the whole interval and stays in
`0.1 ≤ ψ ≤ 8.2` T m². -/
theorem alpha_band_orbit_exists_short {μ : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hμ : 0 ≤ μ)
    (hE : gcEnergy μ s₀ = Eα) (hpitch : 81 / 100 * (2 * Eα / mα) ≤ gcVpar s₀ ^ 2)
    (h1 : 2.75 ≤ s₀.1) (h2 : s₀.1 ≤ 5.5) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ 8e-4 ∧
      ∀ t ∈ Icc 0 8e-4, 0.1 ≤ ψ t ∧ ψ t ≤ 8.2 :=
  alpha_band_orbit_exists_of_le (by norm_num) hμ hE hpitch (by norm_num)
    (by norm_num [psiEdge]) (by linarith [Dpsi_short]) (by linarith [Dpsi_short])

/-- **Full-horizon existence on `[0, 0.05 s]`** for every 3.5 MeV passing alpha (`μ ≥ 0`,
`v_∥² ≥ 0.81 v²`) born at `4 ≤ ψ₀ ≤ 4.3` T m² (`1.18 m ≤ r₀ ≤ 1.23 m ≈ 0.70–0.72 a`), any
angles: the orbit exists on the whole interval and stays in `0.1 ≤ ψ ≤ 8.2` T m². -/
theorem alpha_band_orbit_exists_005 {μ : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hμ : 0 ≤ μ)
    (hE : gcEnergy μ s₀ = Eα) (hpitch : 81 / 100 * (2 * Eα / mα) ≤ gcVpar s₀ ^ 2)
    (h1 : 4 ≤ s₀.1) (h2 : s₀.1 ≤ 4.3) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ (5 / 100) ∧
      ∀ t ∈ Icc 0 (5 / 100), 0.1 ≤ ψ t ∧ ψ t ≤ 8.2 :=
  alpha_band_orbit_exists_of_le (by norm_num) hμ hE hpitch (by norm_num)
    (by norm_num [psiEdge]) (by linarith [Dpsi_005]) (by linarith [Dpsi_005])

/-- Initial parallel gyroradius of a 3.5 MeV alpha with `μ = 0` born at `(ψ₀, 0, 0)`. -/
@[expose] def rho0 (ψ₀ : ℝ) : ℝ := Real.sqrt (2 * mα * Eα) / (qα * reactorQA.B ψ₀ 0 0)

/-- The birth state `(ψ₀, 0, 0, ρ₀(ψ₀))` with `μ = 0` has energy `E_α` and `v_∥² = 2E_α/m`
(so it satisfies the passing-pitch hypothesis) whenever `0 < ψ₀ ≤ ψ_a`. -/
theorem rho0_state {ψ₀ : ℝ} (h0 : 0 < ψ₀) (ha : ψ₀ ≤ psiEdge) :
    gcEnergy 0 (ψ₀, 0, 0, rho0 ψ₀) = Eα ∧
      81 / 100 * (2 * Eα / mα) ≤ gcVpar (ψ₀, 0, 0, rho0 ψ₀) ^ 2 := by
  have hB := (reactorQA_B_bounds (θ := 0) (φ := 0) h0 ha).1
  have hBpos : 0 < reactorQA.B ψ₀ 0 0 := by linarith
  have hq : 0 < qα := by norm_num [qα]
  have hm := mα_pos
  have hEpos : 0 < Eα := by norm_num [Eα]
  have hsq : Real.sqrt (2 * mα * Eα) ^ 2 = 2 * mα * Eα := Real.sq_sqrt (by positivity)
  have hv : gcVpar (ψ₀, 0, 0, rho0 ψ₀) ^ 2 = 2 * Eα / mα := by
    simp only [gcVpar, rho0]
    field_simp
    rw [hsq]
  refine ⟨?_, ?_⟩
  · simp only [gcEnergy, rho0]
    field_simp
    rw [hsq]; ring
  · rw [hv]
    have : 0 ≤ 2 * Eα / mα := by positivity
    linarith

/-- **Non-vacuity of the band class on the full horizon `[0, 0.05 s]`.** There is a constructed
orbit `BoozerGCOrbitOn reactorQA mα qα 0 … (0.05)` with energy exactly `E_α = 3.5 MeV`, pitch
`v_∥² = 2E_α/m`, born at `ψ₀ = 4` T m² (`r₀ ≈ 1.18 m`), which stays in `0.1 ≤ ψ ≤ 8.2` T m² on
the whole interval. -/
theorem alpha_band_nonvacuous_005 :
    ∃ (μ : ℝ) (ψ θ φ ρ : ℝ → ℝ), 0 ≤ μ ∧ BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ (5 / 100) ∧
      boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα ∧
      81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2 ∧
      ψ 0 = 4 ∧ ∀ t ∈ Icc 0 (5 / 100), 0.1 ≤ ψ t ∧ ψ t ≤ 8.2 := by
  obtain ⟨hE, hp⟩ := rho0_state (ψ₀ := 4) (by norm_num) (by norm_num [psiEdge])
  obtain ⟨ψ, θ, φ, ρ, h0, h1, h2, h3, horb, hb⟩ :=
    alpha_band_orbit_exists_005 le_rfl hE hp (by norm_num) (by norm_num)
  simp only at h0 h1 h2 h3
  refine ⟨0, ψ, θ, φ, ρ, le_rfl, horb, ?_, ?_, h0, hb⟩
  · change gcEnergy 0 (ψ 0, θ 0, φ 0, ρ 0) = Eα
    rw [h0, h1, h2, h3]; exact hE
  · change 81 / 100 * (2 * Eα / mα) ≤ gcVpar (ψ 0, θ 0, φ 0, ρ 0) ^ 2
    rw [h0, h1, h2, h3]; exact hp

/-! ## Route (i): an explicit horizon for every birth of the original class -/

/-- Constant for the radial drift speed: `(2E_α/(q B_min)) (|η| + 2|B₂c| a/B₀) ≤ 57000` m/s. -/
theorem radial_speed_numerics :
    2 * Eα / 4.93 / qα * (7 / 100 + 66 / 2000 / (57 / 10) * (17 / 10)) ≤ 57000 := by
  norm_num [Eα, qα]

/-- **Radial drift speed bound.** Along an alpha orbit of `reactorQA` (`μ ≥ 0`, energy `E_α`, any
pitch) on `[0, t]` that has stayed in `ψ ≤ ψ_a`, the near-axis radius `r = √(2ψ/B₀)` moves at
speed at most `57000` m/s: `|r(t) − r(0)| ≤ 57000 t`. (The `∇B` drift `ψ̇ ∝ ∂_θB = O(r)`, so
`ṙ = ψ̇/(B₀ r)` stays bounded up to the axis.) -/
theorem radius_lipschitz {μ t : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hμ : 0 ≤ μ)
    (h : BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ t)
    (hE : boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα)
    (ht : 0 ≤ t) (hhist : ∀ s ∈ Icc 0 t, ψ s ≤ psiEdge) :
    |radius (57 / 10) (ψ t) - radius (57 / 10) (ψ 0)| ≤ 57000 * t := by
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hm := mα_pos
  have hder : ∀ s ∈ Icc 0 t, ∃ d, HasDerivAt (fun r => radius (57 / 10) (ψ r)) d s ∧
      |d| ≤ 57000 := by
    intro s hs
    have hψs := h.pos s hs
    have hf : HasDerivAt (fun r => 2 * ψ r / (57 / 10))
        (2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * along reactorQA.B ψ θ φ s) *
          along reactorQA.Bθ ψ θ φ s / (mα * qα)) / (57 / 10)) s :=
      ((h.dψ s hs).const_mul 2).div_const _
    have hne : 2 * ψ s / (57 / 10) ≠ 0 := by positivity
    refine ⟨_, hf.sqrt hne, ?_⟩
    -- energy and the rate bound
    have hEs := boozerEnergy_eq_on hm.ne' qα_ne G_ne h hs
    rw [hE] at hEs
    have hB := reactorQA_B_bounds (θ := θ s) (φ := φ s) hψs (hhist s hs)
    obtain ⟨hX0, hX1⟩ := momentum_rate_le (q := qα) (ρ := ρ s) hm hμ
      (by norm_num : (0 : ℝ) < 4.93) hB.1
    have hEs' : qα ^ 2 * ρ s ^ 2 * reactorQA.B (ψ s) (θ s) (φ s) ^ 2 / (2 * mα) +
        μ * reactorQA.B (ψ s) (θ s) (φ s) = Eα := hEs
    rw [hEs'] at hX1
    have hr := radius_le_edge (hhist s hs)
    have hr2 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψs.le
    have hrpos : 0 < radius (57 / 10) (ψ s) := Real.sqrt_pos.mpr (by positivity)
    have hBθ : along reactorQA.Bθ ψ θ φ s = -(57 / 10 * (-7 / 100) * radius (57 / 10) (ψ s) *
        sin (θ s)) - 2 * ψ s / (57 / 10) * (2 * (33 / 2000) * sin (2 * θ s)) := rfl
    have hBv : along reactorQA.B ψ θ φ s = reactorQA.B (ψ s) (θ s) (φ s) := rfl
    rw [hBθ, hBv]
    change |2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * reactorQA.B (ψ s) (θ s) (φ s)) *
      (-(57 / 10 * (-7 / 100) * radius (57 / 10) (ψ s) * sin (θ s)) -
        2 * ψ s / (57 / 10) * (2 * (33 / 2000) * sin (2 * θ s))) / (mα * qα)) / (57 / 10) /
      (2 * radius (57 / 10) (ψ s))| ≤ 57000
    generalize radius (57 / 10) (ψ s) = r at hr hr2 hrpos ⊢
    generalize reactorQA.B (ψ s) (θ s) (φ s) = B at hX0 hX1 ⊢
    have hψr : ψ s = 57 / 10 * r ^ 2 / 2 := by field_simp at hr2 ⊢; linarith
    rw [hψr]
    set X := qα ^ 2 * ρ s ^ 2 * B / mα + μ with hX
    have e : 2 * (-(mα * μ + qα ^ 2 * ρ s ^ 2 * B) *
        (-(57 / 10 * (-7 / 100) * r * sin (θ s)) -
          2 * (57 / 10 * r ^ 2 / 2) / (57 / 10) * (2 * (33 / 2000) * sin (2 * θ s))) /
          (mα * qα)) / (57 / 10) / (2 * r) =
        -(X / qα) * (7 / 100 * sin (θ s) - 66 / 2000 / (57 / 10) * r * sin (2 * θ s)) := by
      rw [hX]; field_simp; ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg (div_nonneg hX0 hq.le)]
    have hs1 := abs_sin_le_one (θ s)
    have hs2 := abs_sin_le_one (2 * θ s)
    have htrig : |7 / 100 * sin (θ s) - 66 / 2000 / (57 / 10) * r * sin (2 * θ s)| ≤
        7 / 100 + 66 / 2000 / (57 / 10) * (17 / 10) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 100),
        abs_of_pos (by positivity : (0 : ℝ) < 66 / 2000 / (57 / 10) * r)]
      have h1 : 7 / 100 * |sin (θ s)| ≤ 7 / 100 := by nlinarith
      have h2 : 66 / 2000 / (57 / 10) * r * |sin (2 * θ s)| ≤
          66 / 2000 / (57 / 10) * (17 / 10) := by
        have : 66 / 2000 / (57 / 10) * r ≤ 66 / 2000 / (57 / 10) * (17 / 10) := by gcongr
        nlinarith [abs_nonneg (sin (2 * θ s))]
      linarith
    have hXq : X / qα ≤ 2 * Eα / 4.93 / qα := div_le_div_of_nonneg_right hX1 hq.le
    calc X / qα * |7 / 100 * sin (θ s) - 66 / 2000 / (57 / 10) * r * sin (2 * θ s)|
        ≤ 2 * Eα / 4.93 / qα * (7 / 100 + 66 / 2000 / (57 / 10) * (17 / 10)) :=
          mul_le_mul hXq htrig (abs_nonneg _) (by norm_num [Eα, qα])
      _ ≤ 57000 := radial_speed_numerics
  choose d hd hdb using hder
  let d' : ℝ → ℝ := fun s => if hs : s ∈ Icc 0 t then d s hs else 0
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r => radius (57 / 10) (ψ r))
    (f' := d') (C := 57000) (fun s hs => by
      simp only [d', hs, ↓reduceDIte]; exact (hd s hs).hasDerivWithinAt)
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      simp only [d', hs', ↓reduceDIte, Real.norm_eq_abs]; exact hdb s hs') t ⟨ht, le_rfl⟩
  simpa [Real.norm_eq_abs] using hmv

/-- **Explicit horizon for every birth of the original class (route (i)).** For every alpha birth
state `s₀` with `0 < ψ₀ ≤ ψ_start = B₀(a/4)²/2`, energy `E_α`, `μ ≥ 0` and **any pitch**, and every
`0 ≤ T ≤ r₀/285000` s (`r₀ = √(2ψ₀/B₀)`; e.g. `1.49 μs` for `r₀ = a/4`), an orbit
`BoozerGCOrbitOn reactorQA … T` from `s₀` exists on the whole interval `[0, T]` and stays in
`|ψ − ψ₀| ≤ (11/25) ψ₀`. The horizon is proportional to `r₀` and tends to `0` at the axis,
which is unavoidable in the `(ψ, θ)` chart. -/
theorem alpha_orbit_exists_explicit {μ T : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hμ : 0 ≤ μ)
    (hE : gcEnergy μ s₀ = Eα) (h0 : 0 < s₀.1) (hs : s₀.1 ≤ psiStart) (hT0 : 0 ≤ T)
    (hT : T ≤ radius (57 / 10) s₀.1 / 285000) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T ∧
      ∀ t ∈ Icc 0 T, |ψ t - s₀.1| ≤ 11 / 25 * s₀.1 := by
  set ψ₀ := s₀.1 with hψ₀
  have hedge : 3 / 2 * psiStart ≤ psiEdge := by norm_num [psiStart, psiEdge]
  refine orbit_exists_of_forward_band hT0 hμ hE (by positivity) (by linarith) (by linarith)
    (fun c hc α hα0 hα => ?_)
  refine boozer_bootstrap (D := ψ₀ / 2) (by positivity) (by linarith) (by linarith)
    (by rw [hα0]) hα (fun t ht horb hhist => ?_)
  have hE' : boozerEnergy reactorQA mα qα μ (fun t => (α t).1) (fun t => (α t).2.1)
      (fun t => (α t).2.2.1) (fun t => (α t).2.2.2) 0 = Eα := by
    change gcEnergy μ (α 0) = Eα; rw [hα0]; exact hE
  have hhist' : ∀ s ∈ Icc 0 t, (α s).1 ≤ psiEdge := fun s hs => by
    have := (abs_le.mp (hhist s hs)).2; linarith
  have hL := radius_lipschitz hμ horb hE' ht.1 hhist'
  simp only [hα0] at hL
  have hψt := horb.pos t ⟨ht.1, le_rfl⟩
  have hr0 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) h0.le
  have hrt := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψt.le
  have hr0p : 0 ≤ radius (57 / 10) ψ₀ := Real.sqrt_nonneg _
  have hrtp : 0 ≤ radius (57 / 10) (α t).1 := Real.sqrt_nonneg _
  have htT : 57000 * t ≤ radius (57 / 10) ψ₀ / 5 := by
    have := ht.2.trans hc.2
    have : 57000 * t ≤ 57000 * (radius (57 / 10) ψ₀ / 285000) := by nlinarith
    linarith
  have hd := (abs_le.mp (hL.trans htT))
  generalize radius (57 / 10) ψ₀ = r₀ at hr0 hr0p hd htT
  generalize radius (57 / 10) (α t).1 = r at hrt hrtp hd
  have e1 : (α t).1 = 57 / 10 * r ^ 2 / 2 := by field_simp at hrt ⊢; linarith
  have e0 : ψ₀ = 57 / 10 * r₀ ^ 2 / 2 := by field_simp at hr0 ⊢; linarith
  rw [e1, e0, abs_le]
  constructor <;> nlinarith [hd.1, hd.2]

/-- **The averaged theorem's hypothesis bundle is satisfiable from every birth state of the
class**, on the explicit horizon `r₀/285000` s: for every `s₀` with `0 < ψ₀ ≤ ψ_start`, energy
`E_α`, `μ ≥ 0` and passing pitch, there is an orbit on `[0, r₀/285000]` from `s₀`, and by
`alpha_trapped_reactorQA_averaged_of_le` it stays at `ψ ≤ 8.2`. -/
theorem alpha_trapped_reactorQA_averaged_explicit {μ : ℝ} {s₀ : ℝ × ℝ × ℝ × ℝ} (hμ : 0 ≤ μ)
    (hE : gcEnergy μ s₀ = Eα) (hpitch : 81 / 100 * (2 * Eα / mα) ≤ gcVpar s₀ ^ 2)
    (h0 : 0 < s₀.1) (hs : s₀.1 ≤ psiStart) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ (radius (57 / 10) s₀.1 / 285000) ∧
      ∀ t ∈ Icc 0 (radius (57 / 10) s₀.1 / 285000), ψ t ≤ 8.2 := by
  have hT0 : 0 ≤ radius (57 / 10) s₀.1 / 285000 := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  obtain ⟨ψ, θ, φ, ρ, h0', h1, h2, h3, horb, -⟩ :=
    alpha_orbit_exists_explicit hμ hE h0 hs hT0 le_rfl
  refine ⟨ψ, θ, φ, ρ, h0', h1, h2, h3, horb, ?_⟩
  have hTle : radius (57 / 10) s₀.1 / 285000 ≤ Tav := by
    have := radius_le_edge (hs.trans (by norm_num [psiStart, psiEdge]))
    rw [Tav]; rw [div_le_iff₀ (by norm_num)]; linarith
  refine alpha_trapped_reactorQA_averaged_of_le hTle hμ horb ?_ ?_ (by rw [h0']; exact hs)
  · change gcEnergy μ (ψ 0, θ 0, φ 0, ρ 0) = Eα
    rw [h0', h1, h2, h3]; exact hE
  · change 81 / 100 * (2 * Eα / mα) ≤ gcVpar (ψ 0, θ 0, φ 0, ρ 0) ^ 2
    rw [h0', h1, h2, h3]; exact hpitch

/-! ## Limits of the band method (sanity theorems) -/

/-- **The band method cannot reach the original birth class.** For every horizon `T ≥ 0`,
`D(T) > ψ_start = B₀(a/4)²/2`: already the orbit-width term `|G| Δρ/ι₀ ≈ 2.59` T m² exceeds the
birth flux of `alpha_trapped_reactorQA*`, so the hypothesis `D(T) < ψ₀` fails for every
`ψ₀ ≤ ψ_start`. -/
theorem Dpsi_gt_psiStart {T : ℝ} (hT : 0 ≤ T) : psiStart < Dpsi T :=
  lt_of_lt_of_le (by norm_num [Dpsi, Δρv, Om0, cq, cm, qα, psiStart]) (Dpsi_mono hT)

/-- **The band method cannot reach `0.06 s`, hence not `T_av = 0.19 s`.** For `T ≥ 0.06 s`,
`2 D(T) > ψ_a`, so no `ψ₀` satisfies both `D(T) < ψ₀` and `ψ₀ + D(T) < ψ_a`. (The exact limit
of the certified constants is `T ≈ 0.058 s`; at `T_av` the secular term `11 T/ι₀ ≈ 4.95` T m²
alone exceeds `ψ_a/2`.) -/
theorem band_empty_of_ge {T : ℝ} (hT : 6 / 100 ≤ T) : psiEdge < 2 * Dpsi T := by
  have := Dpsi_mono hT
  have h : psiEdge < 2 * Dpsi (6 / 100) := by norm_num [Dpsi, Δρv, Om0, cq, cm, qα, psiEdge]
  linarith

/-- In particular the band is empty at the averaged horizon `T_av = 0.19 s`. -/
theorem band_empty_Tav : psiEdge < 2 * Dpsi Tav := band_empty_of_ge (by norm_num [Tav])

end PlasmaLean.Design.NearAxisQAExistenceFull
