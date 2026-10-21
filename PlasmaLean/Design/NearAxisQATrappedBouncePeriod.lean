/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQATrappedTimeRows
public import PlasmaLean.Design.NearAxisQATrappedReanchor

/-!
# Validated bounce period and kick amplitude of trapped alphas in exact QA

Companion to `notes/theory/trapped-alpha-status.md` (§3 item 3). Model only: the exactly
quasi-axisymmetric member `exactQA` of the reactor near-axis family, vacuum Boozer guiding-centre
equations; orbits are supplied (their existence is `NearAxisQATrappedReference`).

Results:

* `exactQA_bounce_period`: for every orbit of the exact-QA start window (`Setup`), the bounce of
  `exactQA_bounce_precession` closes at a time `P ≤ 83 μs` (simulated `6.4–6.7 × 10⁻⁵ s`;
  previously proved `P ≤ 1.6 ms`), with precession `Δφ_b ∈ [0.7, 2.6]`, and the amplitude
  integral satisfies `∫₀ᴾ A (2ψ/B₀) dt ≤ 58` (`A = μ/q + qρ²B/m`; RK4: `38.8–46.5`).
* `reference_kick_tight`: the re-anchored reference data of `reference_kick_decomp` with the tight
  period: `|C / sin Δ|, |S / sin Δ| ≤ 2 ∫₀ᴾ |g| ≤ 4 |b₁| q · 58`. In flux units (divided by
  `q ι₀`) the amplitude constant is `M = 4 |b₁| · 58 / ι₀ ≤ 0.2364 T m²` for `reactorQA`
  (`tight_amplitude_le`), against `12.8 T m²` from the crude period.
* `reanchored_gap_forces_small_M`, `tight_amplitude_too_large`: **the tight amplitude does not
  fit the window.** The gap condition of `reactorQA_trapped_reanchored` needs `4M + R ≤ 0.52`,
  i.e. `M ≤ 0.13`. The certified `M ≤ 0.2364` does not meet it, and neither does the exact value
  of `2∫|g|/(qι₀)` (`0.158–0.189` by RK4). Improving the period bound further cannot help; what
  is needed is a bound on the *oscillatory* integrals `C, S` themselves (RK4: `|C/sin Δ| ≤ 0.023`).

**Method.** The generic legs `inner_leg_gen`, `outer_leg_gen` bound `∫ F` over one leg for any
continuous `F` with `F ≤ K_i · A|∂_θB|` on flank cells and `F ≤ K_b |θ̇|` at the bottom. This is
the decomposition of `inner_leg` / `outer_leg` with the integrand left free. The cell bounds come
from `NearAxisQATrappedTimeCells`, through the identity `A = 10⁶ · AmR x B_t` (`Afac_eq_AmR`,
energy conservation) and `|θ̇| ratR = Ω` at the bottom (`bottom_thetaDot`). They are applied with
`F = 1` (bounce time) and `F = A · 2ψ/B₀` (amplitude integral).
-/

public section
noncomputable section

namespace PlasmaLean.Design.NearAxisQATrappedResonance.Setup
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce
  PlasmaLean.Design.NearAxisQATrappedCells PlasmaLean.Design.NearAxisQATrappedPeriodic Real Set
variable {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
include S

/-- **The drift factor along the orbit is explicit**: `A = 10⁶ · AmR x B_t` at every orbit point
with leg coordinate `x` (`A · qB = 2E − μB` by energy conservation, `B = BsR x B_t`). -/
theorem Afac_eq_AmR {t : ℝ} (ht : t ∈ Icc 0 T) (inner : Bool) {x : ℝ}
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) :
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t = 10 ^ 6 * AmR x (Eα / μ) := by
  have hrel := S.rel ht inner hx hx0
  have hBs := BsR_eq hrel
  rw [hx] at hBs
  have hBeq : along exactQA.B ψ θ φ t = Bred (ψ t) (cos (θ t)) := by
    simp only [along]; exact exactQA_B_eq _ _ _
  have hEn := energy_along (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy ht
  have hμ := S.mu_pos
  have hB0 : 0 < along exactQA.B ψ θ φ t := by
    rw [hBeq]; have := hrel.B_pos; rwa [hx] at this
  unfold Afac AmR
  rw [hBs, ← hBeq]
  simp only [along] at hEn hB0 ⊢
  set B := exactQA.B (ψ t) (θ t) (φ t)
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have hE : (0 : ℝ) < Eα := by norm_num [Eα]
  have hEq : Eα = 1750000 * qα := by norm_num [Eα, qα]
  have e : qα ^ 2 * ρ t ^ 2 * B ^ 2 / mα = 2 * (Eα - μ * B) := by rw [← hEn]; field_simp; ring
  have lhs : μ / qα + qα * ρ t ^ 2 * B / mα = (2 * Eα - μ * B) / (qα * B) := by
    rw [eq_div_iff (by positivity)]
    have : (μ / qα + qα * ρ t ^ 2 * B / mα) * (qα * B) = μ * B + qα ^ 2 * ρ t ^ 2 * B ^ 2 / mα := by
      field_simp
    rw [this, e]; ring
  rw [lhs, hEq]
  field_simp
  ring

/-- **Generic inner leg.** On a stretch `[a, b]` with `ρ(a) = ρ(b) = 0`, `ρ < 0` in between,
`θ(a) > δ`, `θ(b) < −δ`: if a continuous integrand `F` satisfies `F ≤ K_i · A |∂_θB|` at flank
points whose leg coordinate lies in cell `i`, and `F ≤ K_b |θ̇|` at bottom points, then
`∫_a^b F ≤ 2 (1/40) Σ K_i + (6/5) K_b`. (The precession certificate `cert` supplies the
structure of the leg: monotone `θ` at the bottom and monotone `x` on the flanks.) -/
theorem inner_leg_gen {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds true (ψ 0) (Eα / μ) Mf Mb mb)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 T)) {K : ℕ → ℝ} {Kb : ℝ} (hK : ∀ i, 0 ≤ K i)
    (hflank : ∀ t ∈ Icc 0 T, ∀ x, psiR true (ψ 0) x = ψ t → 0 ≤ x → 3 / 5 ≤ |θ t| →
      ∀ i : ℕ, x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40) →
        F t ≤ K i * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          |along exactQA.Bθ ψ θ φ t|))
    (hbot : ∀ t ∈ Icc 0 T, ∀ x, psiR true (ψ 0) x = ψ t → 0 ≤ x → |θ t| ≤ 3 / 5 →
      F t ≤ Kb * |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t|)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hneg : ∀ t ∈ Ioo a b, ρ t < 0) (hθa : 3 / 5 < θ a) (hθb : θ b < -(3 / 5)) :
    ∫ t in a..b, F t ≤ 2 * (1 / 40 * ∑ i ∈ Finset.range 100, K i) + 6 / 5 * Kb := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hsub : Icc a b ⊆ Icc 0 T := fun t ht => hI t ht
  have hρle : ∀ t ∈ Icc a b, ρ t ≤ 0 := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hneg t ⟨h, h'⟩).le
  have hxψ : ∀ t ∈ Icc a b, psiR true (ψ 0) (ψ 0 - ψ t) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ 0 - ψ t := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρle t ht
    unfold kinv at h1; nlinarith
  have hxlt : ∀ t ∈ Icc a b, ψ 0 - ψ t ≤ (99 + 1) * (1 / 40) := by
    intro t ht; have := S.x_lt (hI t ht)
    rw [abs_sub_comm] at this; norm_num; linarith [le_abs_self (ψ 0 - ψ t)]
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono hsub
  have hFc := hF.mono hsub
  have hdc := S.cont_psiDot.mono hsub
  have htc := S.cont_thetaDot.mono hsub
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := θ) (c := 3 / 5) hab.le hθc hθa (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := θ) (c := -(3 / 5)) hs1.2 (hθc.mono
    (Icc_subset_Icc hs1.1.le le_rfl)) (by linarith) hθb.le
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  have hdown : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t < 0 := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    have := ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.1 rfl).1
    linarith
  have hlt1 : ∀ t ∈ Ioc s1 b, θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)) hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl))
      hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, hdown t ⟨hta, htb⟩ (by rw [hθt, abs_neg, abs_of_pos (by norm_num)]),
      S.hasDerivAt_theta (hI t ⟨hta.le, htb.le⟩)⟩
  -- piece 1: upper flank `[a, s1]`
  have hsa1 : Icc a s1 ⊆ Icc a b := Icc_subset_Icc le_rfl hs1.2
  have hθ1 : ∀ t ∈ Icc a s1, 3 / 5 ≤ θ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hθs1]
    · exact (hbef1 t ⟨ht.1, h⟩).le
  have hx1 : ∀ t ∈ Icc a s1, HasDerivAt (fun s => ψ 0 - ψ s)
      (-psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hsa1 ht))).const_sub (ψ 0)
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  have P1 := integral_le_cell_sum (Ω := F)
    (h := 1 / 40) (M := K) (n := 99) hs1.1.le (by norm_num) hx1
    (fun t ht => by
      rw [psiDot_eq, neg_neg]
      exact mul_nonneg (S.Afac_pos (hI t (hsa1 ht))).le
        (S.Bθ_pos (hI t (hsa1 ht)) (by linarith [hθ1 t ht])).le)
    (hFc.mono hsa1) (hdc.mono hsa1).neg (by simp [hψa]) (hxlt s1 ⟨hs1.1.le, hs1.2⟩) hK
    (fun t ht i hi => by
      have htI := hI t (hsa1 ht)
      have := hflank t htI _ (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_ge (hθ1 t ht)) i ((cell_iff i).mp hi)
      rw [psiDot_eq, neg_neg]
      rwa [abs_of_pos (S.Bθ_pos htI (by linarith [hθ1 t ht]))] at this)
  -- piece 2: bottom `[s1, s2]`
  have hs12 : Icc s1 s2 ⊆ Icc a b := Icc_subset_Icc hs1.1.le hs2.2
  have hbot' : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 ∧ t ∈ Ioo a b := by
    intro t ht
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, lt_of_lt_of_le hs1.1 ht.1, lt_of_le_of_lt ht.2 hs2b⟩
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h, hθs2]
      · exact (hbef2 t ⟨ht.1, h⟩).le
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hθs1]
      · exact (hlt1 t ⟨h, ht.2.trans hs2.2⟩).le
  have P2 := integral_le_mul_drop (Ω := F) (M := Kb) hs2.1.le
    (fun t ht => S.hasDerivAt_theta (hI t (hs12 ht))) (hFc.mono hs12) (htc.mono hs12)
    (fun t ht => by
      have h1 := hbot t (hI t (hs12 ht)) _ (hxψ t (hs12 ht)) (hx0 t (hs12 ht)) (hbot' t ht).1
      rwa [abs_of_neg (hdown t (hbot' t ht).2 (hbot' t ht).1)] at h1)
  rw [hθs1, hθs2] at P2
  -- piece 3: lower flank `[s2, b]`
  have hs2b' : Icc s2 b ⊆ Icc a b := Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl
  have hθ3 : ∀ t ∈ Icc s2 b, θ t ≤ -(3 / 5) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hθs2]
    · exact (hlt2 t ⟨h, ht.2⟩).le
  have hx3 : ∀ t ∈ Icc s2 b, HasDerivAt (fun s => ψ 0 - ψ s)
      (-psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hs2b' ht))).const_sub (ψ 0)
  have P3 := integral_le_cell_sum_rev (Ω := F)
    (h := 1 / 40) (M := K) (n := 99) hs2b.le (by norm_num) hx3
    (fun t ht => by
      rw [psiDot_eq, neg_neg]
      exact mul_nonpos_of_nonneg_of_nonpos (S.Afac_pos (hI t (hs2b' ht))).le
        (S.Bθ_neg (hI t (hs2b' ht)) (by linarith [hθ3 t ht])).le)
    (hFc.mono hs2b') (hdc.mono hs2b').neg (by simp [hψb]) (hxlt s2 (hs2b' ⟨le_rfl, hs2b.le⟩)) hK
    (fun t ht i hi => by
      have htI := hI t (hs2b' ht)
      have := hflank t htI _ (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_le (hθ3 t ht)) i ((cell_iff i).mp hi)
      rw [neg_neg, psiDot_eq, ← mul_neg]
      rwa [abs_of_neg (S.Bθ_neg htI (by linarith [hθ3 t ht]))] at this)
  -- assemble
  have hint : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable F MeasureTheory.volume u v := by
    intro u v hau huv hvb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hFc.mono (Icc_subset_Icc hau hvb)
  have hsplit : ∫ t in a..b, F t =
      (∫ t in a..s1, F t) + (∫ t in s1..s2, F t) + ∫ t in s2..b, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint a s1 le_rfl hs1.1.le hs1.2)
      (hint s1 s2 hs1.1.le hs2.1.le hs2.2),
      intervalIntegral.integral_add_adjacent_intervals (hint a s2 le_rfl (hs1.1.le.trans hs2.1.le)
        hs2.2) (hint s2 b (hs1.1.le.trans hs2.1.le) hs2b.le le_rfl)]
  rw [hsplit]
  have : (99 : ℕ) + 1 = 100 := rfl
  rw [this] at P1 P3
  linarith

/-- **Generic outer leg.** On a stretch `[a, b]` with `ρ(a) = ρ(b) = 0`, `ρ > 0` in between,
`θ(a) < −δ`, `θ(b) > δ`: under the same cell hypotheses as `inner_leg_gen` (for the outer leg
coordinate `x = ψ − ψ₀`), `∫_a^b F ≤ 2 (1/40) Σ K_i + (6/5) K_b`. -/
theorem outer_leg_gen {Mf : ℕ → ℝ} {Mb mb : ℝ} (cert : LegBounds false (ψ 0) (Eα / μ) Mf Mb mb)
    {F : ℝ → ℝ} (hF : ContinuousOn F (Icc 0 T)) {K : ℕ → ℝ} {Kb : ℝ} (hK : ∀ i, 0 ≤ K i)
    (hflank : ∀ t ∈ Icc 0 T, ∀ x, psiR false (ψ 0) x = ψ t → 0 ≤ x → 3 / 5 ≤ |θ t| →
      ∀ i : ℕ, x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40) →
        F t ≤ K i * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          |along exactQA.Bθ ψ θ φ t|))
    (hbot : ∀ t ∈ Icc 0 T, ∀ x, psiR false (ψ 0) x = ψ t → 0 ≤ x → |θ t| ≤ 3 / 5 →
      F t ≤ Kb * |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t|)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (hρa : ρ a = 0) (hρb : ρ b = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < ρ t) (hθa : θ a < -(3 / 5)) (hθb : 3 / 5 < θ b) :
    ∫ t in a..b, F t ≤ 2 * (1 / 40 * ∑ i ∈ Finset.range 100, K i) + 6 / 5 * Kb := by
  have hI : ∀ t ∈ Icc a b, t ∈ Icc 0 T := fun t ht => ⟨ha0.trans ht.1, ht.2.trans hbT⟩
  have hsub : Icc a b ⊆ Icc 0 T := fun t ht => hI t ht
  have hρge : ∀ t ∈ Icc a b, 0 ≤ ρ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hρa]
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h', hρb]
    · exact (hpos t ⟨h, h'⟩).le
  have hxψ : ∀ t ∈ Icc a b, psiR false (ψ 0) (ψ t - ψ 0) = ψ t := fun t _ => by simp [psiR]
  have hx0 : ∀ t ∈ Icc a b, 0 ≤ ψ t - ψ 0 := by
    intro t ht
    have h1 := S.mom (hI t ht); have h2 := hρge t ht
    unfold kinv at h1; nlinarith
  have hxlt : ∀ t ∈ Icc a b, ψ t - ψ 0 ≤ (99 + 1) * (1 / 40) := by
    intro t ht; have := S.x_lt (hI t ht)
    norm_num; linarith [le_abs_self (ψ t - ψ 0)]
  have hθc : ContinuousOn θ (Icc a b) := S.cont_theta.mono hsub
  have hFc := hF.mono hsub
  have hdc := S.cont_psiDot.mono hsub
  have htc := S.cont_thetaDot.mono hsub
  have hnθ : ∀ t ∈ Icc a b, HasDerivAt (fun s => -θ s)
      (-thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_theta (hI t ht)).neg
  obtain ⟨s1, hs1, hθs1, hbef1⟩ := first_hit (g := fun t => -θ t) (c := 3 / 5) hab.le hθc.neg
    (by linarith) (by linarith)
  obtain ⟨s2, hs2, hθs2, hbef2⟩ := first_hit (g := fun t => -θ t) (c := -(3 / 5)) hs1.2
    (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg (by linarith)
    (by linarith)
  have hs2b : s2 < b := lt_of_le_of_ne hs2.2 (fun h => by rw [h] at hθs2; linarith)
  have hup : ∀ t ∈ Ioo a b, |θ t| ≤ 3 / 5 → 0 < thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ)
      (ρ := ρ) t := by
    intro t ht hθt
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact ((S.bottom_bound cert (hI t htI) (hxψ t htI) (hx0 t htI) hθt).2.2 rfl).1
  have hlt1 : ∀ t ∈ Ioc s1 b, -θ t < 3 / 5 := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc hs1.1.le le_rfl)).neg hθs1.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le hs1.1 ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hlt2 : ∀ t ∈ Ioc s2 b, -θ t < -(3 / 5) := by
    refine lt_of_level_deriv_neg (f := fun t => -θ t)
      (hθc.mono (Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl)).neg hθs2.le ?_
    intro t ht hθt
    have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h] at hθt; linarith)
    have hta : a < t := lt_of_lt_of_le (hs1.1.trans hs2.1) ht.1
    exact ⟨_, by linarith [hup t ⟨hta, htb⟩ (by rw [abs_le]; constructor <;> linarith)],
      hnθ t ⟨hta.le, htb.le⟩⟩
  have hψa : ψ a = ψ 0 := by
    have := S.mom (hI a ⟨le_rfl, hab.le⟩); rw [hρa] at this; unfold kinv at this; linarith
  have hψb : ψ b = ψ 0 := by
    have := S.mom (hI b ⟨hab.le, le_rfl⟩); rw [hρb] at this; unfold kinv at this; linarith
  -- piece 1: lower flank `[a, s1]`
  have hsa1 : Icc a s1 ⊆ Icc a b := Icc_subset_Icc le_rfl hs1.2
  have hθ1 : ∀ t ∈ Icc a s1, θ t ≤ -(3 / 5) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]; linarith
    · linarith [hbef1 t ⟨ht.1, h⟩]
  have hx1 : ∀ t ∈ Icc a s1, HasDerivAt (fun s => ψ s - ψ 0)
      (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hsa1 ht))).sub_const (ψ 0)
  have P1 := integral_le_cell_sum (Ω := F)
    (h := 1 / 40) (M := K) (n := 99) hs1.1.le (by norm_num) hx1
    (fun t ht => by
      rw [psiDot_eq, ← mul_neg]
      exact mul_nonneg (S.Afac_pos (hI t (hsa1 ht))).le
        (neg_nonneg.mpr (S.Bθ_neg (hI t (hsa1 ht)) (by linarith [hθ1 t ht])).le))
    (hFc.mono hsa1) (hdc.mono hsa1) (by simp [hψa]) (hxlt s1 ⟨hs1.1.le, hs1.2⟩) hK
    (fun t ht i hi => by
      have htI := hI t (hsa1 ht)
      have := hflank t htI _ (hxψ t (hsa1 ht)) (hx0 t (hsa1 ht))
        (abs_ge_of_le (hθ1 t ht)) i ((cell_iff i).mp hi)
      rw [psiDot_eq, ← mul_neg]
      rwa [abs_of_neg (S.Bθ_neg htI (by linarith [hθ1 t ht]))] at this)
  -- piece 2: bottom `[s1, s2]`
  have hs12 : Icc s1 s2 ⊆ Icc a b := Icc_subset_Icc hs1.1.le hs2.2
  have hbot' : ∀ t ∈ Icc s1 s2, |θ t| ≤ 3 / 5 := by
    intro t ht
    refine abs_le.mpr ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; linarith
      · linarith [hlt1 t ⟨h, ht.2.trans hs2.2⟩]
    · rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]; linarith
      · linarith [hbef2 t ⟨ht.1, h⟩]
  have hin12 : ∀ t ∈ Icc s1 s2, t ∈ Ioo a b := fun t ht =>
    ⟨lt_of_lt_of_le hs1.1 ht.1, lt_of_le_of_lt ht.2 hs2b⟩
  have P2 := integral_le_mul_drop (Ω := F) (M := Kb) hs2.1.le (fun t ht => hnθ t (hs12 ht))
    (hFc.mono hs12) (htc.mono hs12).neg (fun t ht => by
      have h1 := hbot t (hI t (hs12 ht)) _ (hxψ t (hs12 ht)) (hx0 t (hs12 ht)) (hbot' t ht)
      rwa [abs_of_pos (hup t (hin12 t ht) (hbot' t ht)), ← neg_neg (thetaDot t)] at h1)
  rw [show -θ s1 - -θ s2 = 6 / 5 by linarith] at P2
  -- piece 3: upper flank `[s2, b]`
  have hs2b' : Icc s2 b ⊆ Icc a b := Icc_subset_Icc (hs1.1.le.trans hs2.1.le) le_rfl
  have hθ3 : ∀ t ∈ Icc s2 b, 3 / 5 ≤ θ t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]; linarith
    · linarith [hlt2 t ⟨h, ht.2⟩]
  have hx3 : ∀ t ∈ Icc s2 b, HasDerivAt (fun s => ψ s - ψ 0)
      (psiDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t) t :=
    fun t ht => (S.hasDerivAt_psi (hI t (hs2b' ht))).sub_const (ψ 0)
  have P3 := integral_le_cell_sum_rev (Ω := F)
    (h := 1 / 40) (M := K) (n := 99) hs2b.le (by norm_num) hx3
    (fun t ht => by
      rw [psiDot_eq, neg_nonpos]
      exact mul_nonneg (S.Afac_pos (hI t (hs2b' ht))).le
        (S.Bθ_pos (hI t (hs2b' ht)) (by linarith [hθ3 t ht])).le)
    (hFc.mono hs2b') (hdc.mono hs2b') (by simp [hψb]) (hxlt s2 (hs2b' ⟨le_rfl, hs2b.le⟩)) hK
    (fun t ht i hi => by
      have htI := hI t (hs2b' ht)
      have := hflank t htI _ (hxψ t (hs2b' ht)) (hx0 t (hs2b' ht))
        (abs_ge_of_ge (hθ3 t ht)) i ((cell_iff i).mp hi)
      rw [psiDot_eq, neg_neg]
      rwa [abs_of_pos (S.Bθ_pos htI (by linarith [hθ3 t ht]))] at this)
  -- assemble
  have hint : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b →
      IntervalIntegrable F MeasureTheory.volume u v := by
    intro u v hau huv hvb
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hFc.mono (Icc_subset_Icc hau hvb)
  have hsplit : ∫ t in a..b, F t =
      (∫ t in a..s1, F t) + (∫ t in s1..s2, F t) + ∫ t in s2..b, F t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint a s1 le_rfl hs1.1.le hs1.2)
      (hint s1 s2 hs1.1.le hs2.1.le hs2.2),
      intervalIntegral.integral_add_adjacent_intervals (hint a s2 le_rfl (hs1.1.le.trans hs2.1.le)
        hs2.2) (hint s2 b (hs1.1.le.trans hs2.1.le) hs2b.le le_rfl)]
  rw [hsplit]
  have : (99 : ℕ) + 1 = 100 := rfl
  rw [this] at P1 P3
  linarith

/-- **Bottom kinematics.** At a bottom point (`|θ| ≤ δ`) of the leg `inner`, `|θ̇| > 0` and
`Ω = |θ̇| · ratR` (`ratR = Ω/|θ̇|` is the bottom ratio of the precession cells), with
`Ω = A (−∂_ψB)` and `−∂_ψB = numR > 0`. -/
theorem bottom_thetaDot {inner : Bool} {Mf : ℕ → ℝ} {Mb mb : ℝ}
    (cert : LegBounds inner (ψ 0) (Eα / μ) Mf Mb mb) {t x : ℝ} (ht : t ∈ Icc 0 T)
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) (hθ : |θ t| ≤ 3 / 5) :
    0 < |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t| ∧
      Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t| *
          ratR inner (ψ 0) x (Eα / μ) (cos (θ t)) ∧
      Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * numR inner (ψ 0) x (cos (θ t)) ∧
      0 < numR inner (ψ 0) x (cos (θ t)) := by
  have hrel := S.rel ht inner hx hx0
  have hA := S.Afac_pos ht
  have hμ := S.mu_pos
  have hc : cos (3 / 5) ≤ cos (θ t) := by
    rw [← cos_abs (θ t)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_gt_three]) hθ
  have hxlt : x < 5 / 2 := by
    have := S.x_lt ht
    have e : |ψ t - ψ 0| = x := by
      cases inner <;> simp only [psiR, Bool.false_eq_true, ite_false, ite_true] at hx <;>
        rw [← hx] <;> simp [abs_of_nonneg hx0]
    linarith
  obtain ⟨-, hnr, hsign, -, -⟩ := cert.bottom x ⟨hx0, hxlt.le⟩ _ hrel hc
  have hnum := numR_eq hx (θ t) (φ t)
  have hBs := BsR_eq hrel
  rw [hx] at hBs
  have hBeq : along exactQA.B ψ θ φ t = Bred (ψ t) (cos (θ t)) := by
    simp only [along]; exact exactQA_B_eq _ _ _
  have hρ := S.mom ht
  have hEn := energy_along (by norm_num [mα]) (by norm_num [qα])
    (by rw [exactQA, qaField_G]; norm_num) S.orbit S.energy ht
  have hB0 : 0 < along exactQA.B ψ θ φ t := by
    have := hrel.B_pos; rw [hx] at this; rw [hBeq]; exact this
  have halg := bottom_alg (x := x) hμ hB0 hnr hEn
  have hRR : RR inner (ψ 0) x (Eα / μ) (cos (θ t)) =
      2 * lam * (Eα / μ * x) * (along exactQA.B ψ θ φ t * along exactQA.B ψ θ φ t ^ 2) *
        ((2 * (Eα / μ) - along exactQA.B ψ θ φ t) * numR inner (ψ 0) x (cos (θ t)))⁻¹ := by
    unfold RR; rw [hBs, ← hBeq]
  have hOm : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * numR inner (ψ 0) x (cos (θ t)) := by
    rw [Om_eq, hnum]; simp only [along]
  have hTD : thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      -(Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * numR inner (ψ 0) x (cos (θ t))) +
        qα * ρ t * along exactQA.B ψ θ φ t ^ 2 * kinv / mα := by
    unfold thetaDot Afac
    rw [hnum, show exactQA.ι (ψ t) = 211 / 500 from rfl, show exactQA.G = 581 / 10 from rfl]
    simp only [along]
    unfold kinv
    field_simp
    ring
  have hOmR : Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      RR inner (ψ 0) x (Eα / μ) (cos (θ t)) =
        qα * kinv ^ 2 * x * along exactQA.B ψ θ φ t ^ 2 / mα := by
    rw [hOm, hRR]; unfold Afac; exact halg
  have hOmpos : 0 < Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t := by
    rw [hOm]; exact mul_pos hA hnr
  refine ⟨?_, ?_, hOm, hnr⟩ <;> cases inner
  · simp only [Bool.false_eq_true, ite_false] at hsign
    have hρx : ρ t = kinv * x := by rw [hρ, ← hx]; simp [psiR]
    have hposeq : thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (RR false (ψ 0) x (Eα / μ) (cos (θ t)) - 1) := by
      rw [hTD, mul_sub, mul_one, hOmR, hOm, hρx]; ring
    rw [hposeq]; exact abs_pos.mpr (mul_pos hOmpos hsign).ne'
  · simp only [ite_true] at hsign
    have hρx : ρ t = -(kinv * x) := by rw [hρ, ← hx]; simp [psiR]
    have hneg : -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (1 + RR true (ψ 0) x (Eα / μ) (cos (θ t))) := by
      rw [hTD, mul_add, mul_one, hOmR, hOm, hρx]; ring
    rw [← abs_neg, hneg]; exact abs_pos.mpr (mul_pos hOmpos hsign).ne'
  · simp only [Bool.false_eq_true, ite_false] at hsign
    have hρx : ρ t = kinv * x := by rw [hρ, ← hx]; simp [psiR]
    have hposeq : thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (RR false (ψ 0) x (Eα / μ) (cos (θ t)) - 1) := by
      rw [hTD, mul_sub, mul_one, hOmR, hOm, hρx]; ring
    rw [hposeq, abs_of_pos (mul_pos hOmpos hsign)]
    simp only [ratR, Bool.false_eq_true, ite_false]
    rw [mul_assoc, mul_inv_cancel₀ hsign.ne', mul_one]
  · simp only [ite_true] at hsign
    have hρx : ρ t = -(kinv * x) := by rw [hρ, ← hx]; simp [psiR]
    have hneg : -thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
        Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
          (1 + RR true (ψ 0) x (Eα / μ) (cos (θ t))) := by
      rw [hTD, mul_add, mul_one, hOmR, hOm, hρx]; ring
    rw [← abs_neg, hneg, abs_of_pos (mul_pos hOmpos hsign)]
    simp only [ratR, ite_true]
    rw [mul_assoc, mul_inv_cancel₀ hsign.ne', mul_one]

/-- `x < 5/2` for a leg coordinate (from `|ρ| ≤ ρ_max`). -/
theorem leg_x_lt {t : ℝ} (ht : t ∈ Icc 0 T) {inner : Bool} {x : ℝ}
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) : x < 5 / 2 := by
  have := S.x_lt ht
  have e : |ψ t - ψ 0| = x := by
    cases inner <;> simp only [psiR, Bool.false_eq_true, ite_false, ite_true] at hx <;>
      rw [← hx] <;> simp [abs_of_nonneg hx0]
  linarith

/-- **Flank time bounds at a time `t`.** If `|θ t| ≥ δ` and the leg coordinate `x` is in cell
`i`: `1 ≤ (M_t i/10⁶) · A |∂_θB|` and `A · (2ψ/B₀) ≤ M_J i · A |∂_θB|`. -/
theorem flank_time_bound {inner : Bool} {Mt MJ : ℕ → ℝ} {Mbt MbJ : ℝ}
    (tc : TimeLegBounds inner (ψ 0) (Eα / μ) Mt MJ Mbt MbJ) {t x : ℝ} (ht : t ∈ Icc 0 T)
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) (hθ : 3 / 5 ≤ |θ t|) (i : ℕ)
    (hi : x ∈ Icc ((i : ℝ) / 40) (((i : ℝ) + 1) / 40)) :
    1 ≤ Mt i / 10 ^ 6 * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      |along exactQA.Bθ ψ θ φ t|) ∧
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) ≤
      MJ i * (Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        |along exactQA.Bθ ψ θ φ t|) := by
  have hrel := S.rel ht inner hx hx0
  have hA := S.Afac_pos ht
  have hc : cos (θ t) ≤ cos (3 / 5) := by
    rw [← cos_abs (θ t)]
    have := S.theta ht
    exact cos_le_cos_of_nonneg_of_le_pi (by norm_num)
      ((abs_lt.mpr ⟨this.1, this.2⟩).le.trans (by linarith [pi_pos])) hθ
  have hden := abs_Bθ_eq hrel hx (φ t)
  have hAe := S.Afac_eq_AmR ht inner hx hx0
  have hxlt := S.leg_x_lt ht hx hx0
  have h100 : i < 100 := by
    by_contra h
    push Not at h
    have : (100 : ℝ) ≤ i := by exact_mod_cast h
    have := hi.1
    rw [div_le_iff₀ (by norm_num)] at this
    linarith
  obtain ⟨h1, h2⟩ := tc.flank i h100 x hi _ hrel hc
  have hw : wR inner (ψ 0) x = 20 / 57 * ψ t := by unfold wR; rw [hx]
  simp only [along] at hden ⊢
  rw [hden]
  constructor
  · rw [hAe]
    calc (1 : ℝ) ≤
          Mt i * (AmR x (Eα / μ) * denR inner (ψ 0) x (cos (θ t)) (√(1 - cos (θ t) ^ 2))) := h1
      _ = _ := by ring
  · rw [← hw]
    calc Afac t * wR inner (ψ 0) x ≤
          Afac t * (MJ i * denR inner (ψ 0) x (cos (θ t)) (√(1 - cos (θ t) ^ 2))) :=
          mul_le_mul_of_nonneg_left h2 hA.le
      _ = _ := by ring

/-- **Bottom time bounds at a time `t`.** If `|θ t| ≤ δ`: `1 ≤ (M_bt/10⁶) |θ̇|` and
`A · (2ψ/B₀) ≤ M_bJ |θ̇|`. -/
theorem bottom_time_bound {inner : Bool} {Mf : ℕ → ℝ} {Mb mb : ℝ} {Mt MJ : ℕ → ℝ} {Mbt MbJ : ℝ}
    (cert : LegBounds inner (ψ 0) (Eα / μ) Mf Mb mb)
    (tc : TimeLegBounds inner (ψ 0) (Eα / μ) Mt MJ Mbt MbJ) {t x : ℝ} (ht : t ∈ Icc 0 T)
    (hx : psiR inner (ψ 0) x = ψ t) (hx0 : 0 ≤ x) (hθ : |θ t| ≤ 3 / 5) :
    1 ≤ Mbt / 10 ^ 6 * |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t| ∧
    Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t) ≤
      MbJ * |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t| := by
  have hrel := S.rel ht inner hx hx0
  have hA := S.Afac_pos ht
  have hc : cos (3 / 5) ≤ cos (θ t) := by
    rw [← cos_abs (θ t)]
    exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [pi_gt_three]) hθ
  have hxlt := S.leg_x_lt ht hx hx0
  obtain ⟨hTpos, hOm1, hOm2, hnr⟩ := S.bottom_thetaDot cert ht hx hx0 hθ
  obtain ⟨h1, h2⟩ := tc.bottom x ⟨hx0, hxlt.le⟩ _ hrel hc
  have hAe := S.Afac_eq_AmR ht inner hx hx0
  have hw : wR inner (ψ 0) x = 20 / 57 * ψ t := by unfold wR; rw [hx]
  set D := |thetaDot (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t|
  set r := ratR inner (ψ 0) x (Eα / μ) (cos (θ t))
  set n := numR inner (ψ 0) x (cos (θ t))
  set A := Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t
  have hDr : D * r = A * n := hOm1.symm.trans hOm2
  have hr : 0 < r := by
    have : 0 < D * r := by rw [hDr]; exact mul_pos hA hnr
    exact pos_of_mul_pos_right this hTpos.le
  rw [← hw]
  constructor
  · -- `r ≤ Mbt · AmR · n = (Mbt/10⁶) · A n = (Mbt/10⁶) D r`
    have : r ≤ Mbt / 10 ^ 6 * D * r := by
      calc r ≤ Mbt * (AmR x (Eα / μ) * n) := h1
        _ = Mbt / 10 ^ 6 * (A * n) := by rw [hAe]; ring
        _ = Mbt / 10 ^ 6 * D * r := by rw [← hDr]; ring
    have := le_of_mul_le_mul_right (a := r) (b := 1) (c := Mbt / 10 ^ 6 * D) (by linarith) hr
    exact this
  · -- `A w r ≤ MbJ A n = MbJ D r`
    have : A * wR inner (ψ 0) x * r ≤ MbJ * D * r := by
      calc A * wR inner (ψ 0) x * r = A * (wR inner (ψ 0) x * r) := by ring
        _ ≤ A * (MbJ * n) := mul_le_mul_of_nonneg_left h2 hA.le
        _ = MbJ * (A * n) := by ring
        _ = MbJ * D * r := by rw [← hDr]; ring
    exact le_of_mul_le_mul_right this hr

end PlasmaLean.Design.NearAxisQATrappedResonance.Setup

namespace PlasmaLean.Design.NearAxisQATrappedBouncePeriod
open PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQATrappedBounce PlasmaLean.Design.NearAxisQATrappedCells
  PlasmaLean.Design.NearAxisQATrappedResonance PlasmaLean.Design.NearAxisQATrappedPeriodic Real Set

/-! ## The validated bounce period -/

/-- **Bounce period and amplitude integral, given the cell certificates.** For an orbit in the
setting `Setup` with `T ≥ 1.6 ms`, if the precession bounds and the time bounds (targets `Pμ`
microseconds and `J`) hold on the window, the bounce of `exactQA_bounce_precession` closes at a
time `P ≤ Pμ · 10⁻⁶ s`, and `∫₀ᴾ A · (2ψ/B₀) dt ≤ J`. -/
theorem exactQA_bounce_period_of_cert {Pμ J : ℝ}
    (hcert : ∀ ψ₀ Bt : ℝ, ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8) → Bt ∈ Icc (27 / 5 : ℝ) (11 / 2) →
      PrecessionBounds ψ₀ Bt)
    (htc : ∀ ψ₀ Bt : ℝ, ψ₀ ∈ Icc (19 / 4 : ℝ) (47 / 8) → Bt ∈ Icc (27 / 5 : ℝ) (11 / 2) →
      TimeBounds Pμ J ψ₀ Bt)
    {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) (hT : 2 * Lhalf ≤ T) :
    ∃ P₁ P : ℝ, 0 < P₁ ∧ P₁ < P ∧ P ≤ 2 * Lhalf ∧ P ≤ Pμ / 10 ^ 6 ∧ ρ P₁ = 0 ∧ ρ P = 0 ∧
      (∀ t ∈ Ioo 0 P₁, ρ t < 0) ∧ (∀ t ∈ Ioo P₁ P, 0 < ρ t) ∧
      ψ P = ψ 0 ∧ θ P = θ 0 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) ∧
      ∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) ≤ J := by
  have hψ0 : ψ 0 ∈ Icc (19 / 4 : ℝ) (47 / 8) := ⟨by linarith [S.psi0.1], by linarith [S.psi0.2]⟩
  obtain ⟨Mfi, Mfo, Mbi, mbi, Mbo, mbo, ci, co, hup, hlow⟩ := hcert _ _ hψ0 S.Bt_mem
  obtain ⟨Mti, Mto, MJi, MJo, Mbti, Mbto, MbJi, MbJo, ti, tO, htime, hJ⟩ := htc _ _ hψ0 S.Bt_mem
  obtain ⟨z₁, z₂, hz₁, hz₁₂, hz₂, hρz₁, hρz₂, hneg, hpos, hθ0, hθz₁, hθz₂, hψz₂, hθz₂'⟩ :=
    S.bounce_closes ci hT
  have hz₂T : z₂ ≤ T := hz₂.trans hT
  -- precession (as in `exactQA_bounce_precession_of_cert`)
  have Pin := S.inner_leg ci le_rfl hz₁ (hz₁₂.le.trans hz₂T) S.rho0 hρz₁ hneg hθ0 hθz₁
  have Pout := S.outer_leg co hz₁.le hz₁₂ hz₂T hρz₁ hρz₂ hpos hθz₁ hθz₂
  have hΩc := S.cont_Om.mono (Icc_subset_Icc le_rfl hz₂T)
  have hint : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ z₂ →
      IntervalIntegrable (Setup.Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ))
        MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hΩc.mono (Icc_subset_Icc hu hv)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 z₁ le_rfl hz₁.le hz₁₂.le) (hint z₁ z₂ hz₁.le hz₁₂.le le_rfl)
  have hprec := precession_step (ι₀ := 211 / 500) (fun _ => rfl) S.orbit le_rfl
    (hz₁.le.trans hz₁₂.le) hz₂T (S.cont_Bψ.mono (Icc_subset_Icc le_rfl hz₂T))
  have hOm : ∫ t in (0 : ℝ)..z₂, Setup.Om (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t =
      -∫ t in (0 : ℝ)..z₂, poloidalDrift exactQA mα qα μ ψ θ φ ρ t := by
    unfold Setup.Om; rw [intervalIntegral.integral_neg]
  rw [hθz₂', sub_self, zero_sub, ← hOm, ← hsplit] at hprec
  -- bounce time: `F = 1`
  have h6 : (0 : ℝ) < 10 ^ 6 := by norm_num
  have T1 := S.inner_leg_gen ci (F := fun _ => (1 : ℝ)) continuousOn_const
    (K := fun i => Mti i / 10 ^ 6) (Kb := Mbti / 10 ^ 6)
    (fun i => div_nonneg (ti.Mt_nonneg i) h6.le)
    (fun t ht x hx hx0 hθ i hi => (S.flank_time_bound ti ht hx hx0 hθ i hi).1)
    (fun t ht x hx hx0 hθ => (S.bottom_time_bound ci ti ht hx hx0 hθ).1)
    le_rfl hz₁ (hz₁₂.le.trans hz₂T) S.rho0 hρz₁ hneg hθ0 hθz₁
  have T2 := S.outer_leg_gen co (F := fun _ => (1 : ℝ)) continuousOn_const
    (K := fun i => Mto i / 10 ^ 6) (Kb := Mbto / 10 ^ 6)
    (fun i => div_nonneg (tO.Mt_nonneg i) h6.le)
    (fun t ht x hx hx0 hθ i hi => (S.flank_time_bound tO ht hx hx0 hθ i hi).1)
    (fun t ht x hx hx0 hθ => (S.bottom_time_bound co tO ht hx hx0 hθ).1)
    hz₁.le hz₁₂ hz₂T hρz₁ hρz₂ hpos hθz₁ hθz₂
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero] at T1 T2
  rw [← Finset.sum_div] at T1 T2
  -- amplitude integral: `F = A · 2ψ/B₀`
  have hFc : ContinuousOn (fun t => Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
      (20 / 57 * ψ t)) (Icc 0 T) := S.cont_Afac.mul (continuousOn_const.mul S.cont_psi)
  have J1 := S.inner_leg_gen ci hFc (K := MJi) (Kb := MbJi) ti.MJ_nonneg
    (fun t ht x hx hx0 hθ i hi => (S.flank_time_bound ti ht hx hx0 hθ i hi).2)
    (fun t ht x hx hx0 hθ => (S.bottom_time_bound ci ti ht hx hx0 hθ).2)
    le_rfl hz₁ (hz₁₂.le.trans hz₂T) S.rho0 hρz₁ hneg hθ0 hθz₁
  have J2 := S.outer_leg_gen co hFc (K := MJo) (Kb := MbJo) tO.MJ_nonneg
    (fun t ht x hx hx0 hθ i hi => (S.flank_time_bound tO ht hx hx0 hθ i hi).2)
    (fun t ht x hx hx0 hθ => (S.bottom_time_bound co tO ht hx hx0 hθ).2)
    hz₁.le hz₁₂ hz₂T hρz₁ hρz₂ hpos hθz₁ hθz₂
  have hFi : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ z₂ →
      IntervalIntegrable (fun t => Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t)) MeasureTheory.volume u v := by
    intro u v hu huv hv
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le huv]; exact hFc.mono (Icc_subset_Icc hu (hv.trans hz₂T))
  have hJsplit := intervalIntegral.integral_add_adjacent_intervals
    (hFi 0 z₁ le_rfl hz₁.le hz₁₂.le) (hFi z₁ z₂ hz₁.le hz₁₂.le le_rfl)
  refine ⟨z₁, z₂, hz₁, hz₁₂, hz₂, ?_, hρz₁, hρz₂, hneg, hpos, hψz₂, hθz₂', ?_, ?_⟩
  · have : z₂ = z₁ + (z₂ - z₁) := by ring
    rw [this]
    have e : 2 * (1 / 40 * ((∑ i ∈ Finset.range 100, Mti i) / 10 ^ 6)) + 6 / 5 * (Mbti / 10 ^ 6) +
        (2 * (1 / 40 * ((∑ i ∈ Finset.range 100, Mto i) / 10 ^ 6)) + 6 / 5 * (Mbto / 10 ^ 6)) =
        (2 * (1 / 40) * (∑ i ∈ Finset.range 100, Mti i + ∑ i ∈ Finset.range 100, Mto i) +
          6 / 5 * (Mbti + Mbto)) / 10 ^ 6 := by ring
    have : (2 * (1 / 40) * (∑ i ∈ Finset.range 100, Mti i + ∑ i ∈ Finset.range 100, Mto i) +
          6 / 5 * (Mbti + Mbto)) / 10 ^ 6 ≤ Pμ / 10 ^ 6 :=
      div_le_div_of_nonneg_right htime h6.le
    linarith
  · constructor <;> nlinarith [Pin.1, Pout.1, Pin.2, Pout.2]
  · rw [← hJsplit]
    linarith

/-- **Validated bounce period (trapped 3.5 MeV alphas, exact QA, start window).** For an orbit
in the setting `Setup` (tip field `E/μ ∈ [5.4, 5.5] T`, start at an upper turning point with
`ψ(0) ∈ [4.75, 5.79] T m²`) on `[0, T]` with `T ≥ 1.6 ms`, the bounce closes at a time
`P ≤ 83 μs` (RK4: `6.4–6.7 × 10⁻⁵ s`): `ρ(P₁) = ρ(P) = 0`, the reduced state returns, the
precession per bounce is in `[0.7, 2.6]`, and the amplitude integral is `∫₀ᴾ A (2ψ/B₀) ≤ 58`
(RK4: `38.8–46.5`). -/
theorem exactQA_bounce_period {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P₁ P : ℝ, 0 < P₁ ∧ P₁ < P ∧ P ≤ 2 * Lhalf ∧ P ≤ 83 / 10 ^ 6 ∧ ρ P₁ = 0 ∧ ρ P = 0 ∧
      (∀ t ∈ Ioo 0 P₁, ρ t < 0) ∧ (∀ t ∈ Ioo P₁ P, 0 < ρ t) ∧
      ψ P = ψ 0 ∧ θ P = θ 0 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) ∧
      ∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) ≤ 58 :=
  exactQA_bounce_period_of_cert (fun _ _ => precession_cert) (fun _ _ => time_cert) S hT

/-! ## The kick amplitude with the tight period -/

/-- Along an orbit of the start window the reference amplitude is
`|g| = 2|b₁| q · A (2ψ/B₀)` (`q²ρ²B/m + μ = q A`). -/
theorem refAmp_abs (b₁ : ℝ) {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    |refAmp b₁ μ ψ θ ρ t| = 2 * |b₁| * qα *
      (Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t)) := by
  have hA := S.Afac_pos ht
  have hψ := S.psi_pos ht
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hm : (0 : ℝ) < mα := by norm_num [mα]
  have eB : along exactQA.B ψ θ φ t = Bf (ψ t) (θ t) := by
    simp only [along]; rw [exactQA_B_eq]; rfl
  have e : refAmp b₁ μ ψ θ ρ t = -(2 * b₁) *
      (qα * (Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t))) := by
    unfold refAmp Setup.Afac; rw [eB]; field_simp; ring
  rw [e, abs_mul, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) <
    qα * (Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t * (20 / 57 * ψ t)))]
  norm_num; ring

/-- **Kick decomposition over a given period** (the algebra of `reference_kick_decomp`, for any
`0 < P ≤ T` with `sin Δ ≠ 0`, `Δ = φ(P) − φ(0)`): the reference kick `∫₀ᴾ g sin 2φ` equals
`C sin 2φ(0) + S cos 2φ(0)` with `C = ∫₀ᴾ g cos 2(φ − φ(0))`, `S = ∫₀ᴾ g sin 2(φ − φ(0))`, and
`|C / sin Δ|, |S / sin Δ| ≤ 2 ∫₀ᴾ |g|` when `|sin Δ| ≥ 1/2`. -/
theorem kick_decomp_of_period (b₁ : ℝ) {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    {P : ℝ} (hP0 : 0 < P) (hPT : P ≤ T) (hsin : 1 / 2 ≤ |sin (φ P - φ 0)|) :
    (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t)) =
        (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) * sin (2 * φ 0) +
          (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) * cos (2 * φ 0) ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| := by
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
    intro f hf hfc
    rw [abs_div, div_le_iff₀ hs0]
    have h1 : |∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * f t| ≤
        ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| := by
      refine (intervalIntegral.abs_integral_le_integral_abs hP0.le).trans ?_
      apply intervalIntegral.integral_mono_on hP0.le
      · apply ContinuousOn.intervalIntegrable
        rw [hu]
        exact (hgc.mul hfc).abs
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

/-- **Reference kick data with the tight period.** For an exact-QA reference orbit of the start
window (`Setup`, `T ≥ 1.6 ms`) and any symmetry-breaking coefficient `b₁`, there is a bounce
period `0 < P ≤ 83 μs` with precession `Δ = φ(P) − φ(0) ∈ [0.7, 2.6]`, `|sin Δ| ≥ 1/2`, the kick
decomposition of `reference_kick_decomp`, and
`|C / sin Δ|, |S / sin Δ| ≤ 2 ∫₀ᴾ |g| ≤ 4 |b₁| q · 58`. -/
theorem reference_kick_tight (b₁ : ℝ) {μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ} (S : Setup μ T ψ θ φ ρ)
    (hT : 2 * Lhalf ≤ T) :
    ∃ P : ℝ, 0 < P ∧ P ≤ 83 / 10 ^ 6 ∧ φ P - φ 0 ∈ Icc (7 / 10 : ℝ) (13 / 5) ∧
      1 / 2 ≤ |sin (φ P - φ 0)| ∧
      (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * φ t)) =
        (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) * sin (2 * φ 0) +
          (∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) * cos (2 * φ 0) ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * cos (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        4 * |b₁| * qα * 58 ∧
      |(∫ t in (0 : ℝ)..P, refAmp b₁ μ ψ θ ρ t * sin (2 * (φ t - φ 0))) / sin (φ P - φ 0)| ≤
        4 * |b₁| * qα * 58 := by
  obtain ⟨P₁, P, hP₁, hP₁P, hPL, hP83, -, -, -, -, -, -, hφ, hJ⟩ := exactQA_bounce_period S hT
  have hP0 : 0 < P := hP₁.trans hP₁P
  have hPT : P ≤ T := hPL.trans hT
  have hsin := abs_sin_ge_half_of_mem hφ
  obtain ⟨hdec, hC, hS⟩ := kick_decomp_of_period b₁ S hP0 hPT hsin
  have hg : ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| = 2 * |b₁| * qα *
      ∫ t in (0 : ℝ)..P, Setup.Afac (μ := μ) (ψ := ψ) (θ := θ) (φ := φ) (ρ := ρ) t *
        (20 / 57 * ψ t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hP0.le] at ht
    exact refAmp_abs b₁ S ⟨ht.1, ht.2.trans hPT⟩
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  have hbound : 2 * ∫ t in (0 : ℝ)..P, |refAmp b₁ μ ψ θ ρ t| ≤ 4 * |b₁| * qα * 58 := by
    rw [hg]
    have : 0 ≤ 2 * |b₁| * qα := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hJ this]
  exact ⟨P, hP0, hP83, hφ, hsin, hdec, hC.trans hbound, hS.trans hbound⟩

/-! ## Does the tight amplitude fit the window? -/

/-- **The amplitude constant in flux units.** With `|b₁| ≤ 4.3 × 10⁻⁴` (`reactorQA`), the data
`d = (C, S)/(q ι₀ sin Δ)` of the re-anchored scheme satisfy
`|d| ≤ 4 |b₁| · 58 / ι₀ ≤ 0.2364 T m²` (from `reference_kick_tight`; the crude period gave
`12.8 T m²`). -/
theorem tight_amplitude_le {b₁ : ℝ} (hb : |b₁| ≤ 43 / 100000) :
    4 * |b₁| * qα * 58 / (qα * (211 / 500)) ≤ 2364 / 10000 := by
  have hq : (0 : ℝ) < qα := by norm_num [qα]
  rw [show 4 * |b₁| * qα * 58 / (qα * (211 / 500)) = 4 * |b₁| * 58 / (211 / 500) by
    field_simp]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith [abs_nonneg b₁]

/-- **What the re-anchored gap needs.** The gap condition of `reactorQA_trapped_reanchored`
(with nonnegative constants) forces `4M + R ≤ 0.52`, so `M ≤ 0.13 T m²`, whatever `N`, `R`, `e`,
`σ`, `γ` are: the start window has width `1.04`. -/
theorem reanchored_gap_forces_small_M {ψ₀ M R γ e σ : ℝ} {N : ℕ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hγ : 0 ≤ γ) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    (hgap : 2 * M + N * (R + γ + M * (e + σ)) + (2 * M + R) ≤
      min (ψ₀ - 475 / 100) (579 / 100 - ψ₀)) :
    4 * M + R ≤ 52 / 100 ∧ M ≤ 13 / 100 := by
  have hmin : min (ψ₀ - 475 / 100) (579 / 100 - ψ₀) ≤ 52 / 100 := by
    rcases le_total (ψ₀ - 475 / 100) (579 / 100 - ψ₀) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have : 0 ≤ (N : ℝ) * (R + γ + M * (e + σ)) := by positivity
  constructor <;> linarith

/-- **The tight amplitude is still too large for the window.** The certified constant `0.2364`
exceeds the `0.13` allowed by `reanchored_gap_forces_small_M`. So does `4 |b₁| J / ι₀` for every
`J ≥ 38` with `|b₁| = 4.3 × 10⁻⁴`, and the RK4 values of the amplitude integral are `J ≥ 38.8`
on the window. So no bound of the form `M = 2 ∫|g| / (q ι₀)` can close the re-anchored argument,
whatever the period bound: the oscillatory integrals `C, S` themselves must be bounded (RK4:
`|C / sin Δ| ≤ 0.023`). -/
theorem tight_amplitude_too_large :
    (13 / 100 : ℝ) < 2364 / 10000 ∧
      ∀ J : ℝ, 38 ≤ J → (13 / 100 : ℝ) < 4 * (43 / 100000) * J / (211 / 500) := by
  refine ⟨by norm_num, fun J hJ => ?_⟩
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith

/-! ## The shears `σ`, `γ`: what is proved -/

/-- **Crude precession shear.** For any two orbits of the start window (any two anchors), the
bounce precessions differ by at most `1.9`: both lie in the certified interval `[0.7, 2.6]`.
A sharper `σ` needs two-sided enclosures of `Δφ_b`. With the present cells the enclosure of
`Δφ_b` on a single index box (`9/1024` in `ψ₀`, `1/1280` in `B_t`) is still about `0.17–0.24` wide
(lower flank sums over the fully-flank cells, untrusted evaluation). The floor comes from the
single bottom ratio `[m_b, M_b]` per leg. -/
theorem precession_shear_crude {μ T μ' T' : ℝ} {ψ θ φ ρ ψ' θ' φ' ρ' : ℝ → ℝ}
    (S : Setup μ T ψ θ φ ρ) (S' : Setup μ' T' ψ' θ' φ' ρ') (hT : 2 * Lhalf ≤ T)
    (hT' : 2 * Lhalf ≤ T') :
    ∃ P P' : ℝ, 0 < P ∧ P ≤ 83 / 10 ^ 6 ∧ 0 < P' ∧ P' ≤ 83 / 10 ^ 6 ∧
      |(φ' P' - φ' 0) - (φ P - φ 0)| ≤ 19 / 10 := by
  obtain ⟨P₁, P, hP₁, hP₁P, -, hP, -, -, -, -, -, -, hφ, -⟩ := exactQA_bounce_period S hT
  obtain ⟨P₁', P', hP₁', hP₁P', -, hP', -, -, -, -, -, -, hφ', -⟩ := exactQA_bounce_period S' hT'
  refine ⟨P, P', hP₁.trans hP₁P, hP, hP₁'.trans hP₁P', hP', ?_⟩
  rw [abs_le]
  constructor <;> linarith [hφ.1, hφ.2, hφ'.1, hφ'.2]

/-- **Crude amplitude shear.** If `|dC k|, |dC (k+1)| ≤ M` then `|dC (k+1) − dC k| ≤ 2M`; with
the certified `M ≤ 0.2364` this gives `γ ≤ 0.4728`. -/
theorem amplitude_shear_crude {a b M : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ M) : |b - a| ≤ 2 * M := by
  have := abs_sub b a; linarith

/-- **With the certified constants the re-anchored gap cannot close**, for any number of
bounces `N`, any remainders `R, e ≥ 0`, any shears `σ, γ ≥ 0` and any start `ψ₀`: with
`M = 0.2364`, `4M > 0.52 ≥ min (ψ₀ − 4.75) (5.79 − ψ₀)`. -/
theorem certified_constants_fail {ψ₀ R γ e σ : ℝ} {N : ℕ} (hR : 0 ≤ R) (hγ : 0 ≤ γ)
    (he : 0 ≤ e) (hσ : 0 ≤ σ) :
    ¬ (2 * (2364 / 10000) + N * (R + γ + 2364 / 10000 * (e + σ)) + (2 * (2364 / 10000) + R) ≤
      min (ψ₀ - 475 / 100) (579 / 100 - ψ₀)) := by
  intro h
  have := (reanchored_gap_forces_small_M hR (by norm_num) hγ he hσ h).2
  norm_num at this

/-! ## Sanity checks -/

/-- Sanity (degenerate case): with no symmetry breaking (`b₁ = 0`) the reference amplitude
vanishes. -/
theorem refAmp_zero (μ : ℝ) (ψ θ ρ : ℝ → ℝ) (t : ℝ) : refAmp 0 μ ψ θ ρ t = 0 := by
  simp [refAmp]

/-- Sanity (special case): the certified period `83 μs` is below the old bound `2 L_half = 1.6 ms`
by a factor of more than `19`. -/
theorem period_improvement : (83 / 10 ^ 6 : ℝ) * 19 < 2 * Lhalf := by norm_num [Lhalf]

end PlasmaLean.Design.NearAxisQATrappedBouncePeriod
