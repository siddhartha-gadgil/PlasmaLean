/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Re-anchored bounce maps: discrete averaging with phase shear (rung M4)

Companion to `notes/theory/trapped-alpha-status.md` and
`notes/theory/near-qa-trapped-particles.md` (target T4, step 3). Pure real analysis on sequences;
no physics model is used here.

**Setting.** A trapped particle in a near-symmetric field is sampled at its upper turning
points `k = 0, 1, 2, …`: flux `y k`, toroidal angle `φ k`. At every tip a *fresh* reference orbit
of the exactly symmetric field is started at the current state (re-anchoring). The reference
supplies three numbers: the precession per bounce `Δ k` and the two harmonic coefficients
`C k, S k` of its `sin 2φ` kick, so that the reference kick is `C k sin 2φ k + S k cos 2φ k`.
The quantitative per-bounce hypotheses are:

* kick remainder: `|y (k+1) − y k − (C k sin 2φ k + S k cos 2φ k)| ≤ R`;
* phase-step remainder: `|2 φ (k+1) − 2 φ k − 2 Δ k| ≤ e`;
* phase shear: `|Δ (k+1) − Δ k| ≤ σ` (the precession changes because the anchor moved);
* amplitude shear: `C k = dC k · sin Δ k`, `S k = dS k · sin Δ k` with `|dC|, |dS| ≤ M` and
  `|dC (k+1) − dC k|, |dS (k+1) − dS k| ≤ γ` (non-resonance is encoded in `M`: if
  `|sin Δ k| ≥ s` and `|C k| ≤ A` one can take `dC k = C k / sin Δ k`, `M = A/s`).

Unlike a single global reference (`Kinetic.Boozer.bounce_drift_of_reference_le`), nothing has
to stay close to a fixed orbit for many bounces: every error is incurred over **one** bounce.

Results:

* `abs_sum_shear_le` (Abel summation with varying increments):
  `|Σ_{k ≤ n} c k sin (x k)| ≤ M + n (γ + M (e + σ))/2` when `c k = d k sin Δ k`, `|d k| ≤ M`,
  `|x (k+1) − x k − 2Δ k| ≤ e`, `|Δ (k+1) − Δ k| ≤ σ`, `|d (k+1) − d k| ≤ γ`;
  `abs_sum_shear_cos_le` is the cosine version. With `e = σ = γ = 0` this is the classical
  `|Σ sin(kα + β)| ≤ 1/|sin(α/2)|` bound (`abs_sum_shear_const`).
* `reanchored_drift_le`: `|y (n+1) − y 0| ≤ 2M + (n+1) R + n (γ + M (e + σ))`. The order-one
  kicks do not accumulate; the error per bounce is `R + γ + M (e + σ)`, the sum of the one-bounce
  remainder and the shear (the Chirikov/GWB-type) term.
* `reanchored_band`: a discrete first-exit argument. If the per-bounce hypotheses are only known
  while the anchors stay in a window `[lo, hi]` (the reference orbits are only controlled there),
  the gap `2M + N (R + γ + M (e + σ)) + D ≤ min (y 0 − lo) (hi − y 0)` (with `D` a one-step bound)
  keeps all anchors `y 0, …, y N` in the window.
* Sanity: `sin_mul_eq_half_sub` (the product identity), `abs_sum_shear_const` (constant data),
  `reanchored_drift_zero` (no kicks: no drift), `abs_sum_shear_resonant` (the bound is attained:
  amplitude shear `γ = 2` produces exactly the predicted linear growth `n + 1`).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic.BounceShear
open Real Finset Set

/-- Product identity: if `c = d sin Δ` then `c sin x = (d/2)(cos (x − Δ) − cos (x + Δ))`. -/
theorem sin_mul_eq_half_sub {c d Δ x : ℝ} (h : c = d * sin Δ) :
    c * sin x = d / 2 * (cos (x - Δ) - cos (x + Δ)) := by
  rw [h, cos_sub, cos_add]; ring

/-- Telescoping invariant for `abs_sum_shear_le`: after `j + 1` terms, the partial sum differs
from `(d 0/2) cos (x 0 − Δ 0) − (d j/2) cos (x j + Δ j)` by at most `j (γ + M (e + σ))/2`. -/
theorem abs_sum_shear_aux {c d Δ x : ℕ → ℝ} {M γ e σ : ℝ} (n : ℕ)
    (hcd : ∀ k ≤ n, c k = d k * sin (Δ k)) (hM : ∀ k ≤ n, |d k| ≤ M)
    (hx : ∀ k < n, |x (k + 1) - x k - 2 * Δ k| ≤ e) (hΔ : ∀ k < n, |Δ (k + 1) - Δ k| ≤ σ)
    (hd : ∀ k < n, |d (k + 1) - d k| ≤ γ) :
    ∀ j ≤ n, |(∑ k ∈ range (j + 1), c k * sin (x k)) - d 0 / 2 * cos (x 0 - Δ 0) +
      d j / 2 * cos (x j + Δ j)| ≤ j * (γ + M * (e + σ)) / 2 := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [sum_range_one, sin_mul_eq_half_sub (hcd 0 (Nat.zero_le _))]
    have e0 : d 0 / 2 * (cos (x 0 - Δ 0) - cos (x 0 + Δ 0)) - d 0 / 2 * cos (x 0 - Δ 0) +
        d 0 / 2 * cos (x 0 + Δ 0) = 0 := by ring
    simp [e0]
  | succ j ih =>
    intro hj
    have hjn : j < n := hj
    have ih' := ih hjn.le
    rw [sum_range_succ, sin_mul_eq_half_sub (hcd (j + 1) hj)]
    set u := cos (x (j + 1) - Δ (j + 1))
    set w := cos (x j + Δ j)
    have hu : |u| ≤ 1 := abs_cos_le_one _
    have huw : |u - w| ≤ e + σ := by
      refine (abs_cos_sub_cos_le _ _).trans ?_
      have e1 : x (j + 1) - Δ (j + 1) - (x j + Δ j) =
          (x (j + 1) - x j - 2 * Δ j) - (Δ (j + 1) - Δ j) := by ring
      rw [e1]
      exact (abs_sub _ _).trans (add_le_add (hx j hjn) (hΔ j hjn))
    have hT : |(d (j + 1) - d j) / 2 * u + d j / 2 * (u - w)| ≤ (γ + M * (e + σ)) / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_two]
      have h1 : |d (j + 1) - d j| / 2 * |u| ≤ γ / 2 := by
        have := hd j hjn
        have : |d (j + 1) - d j| * |u| ≤ γ * 1 :=
          mul_le_mul this hu (abs_nonneg _) ((abs_nonneg _).trans this)
        linarith
      have h2 : |d j| / 2 * |u - w| ≤ M * (e + σ) / 2 := by
        have hdj := hM j hjn.le
        have : |d j| * |u - w| ≤ M * (e + σ) :=
          mul_le_mul hdj huw (abs_nonneg _) ((abs_nonneg _).trans hdj)
        linarith
      linarith
    have e2 : (∑ k ∈ range (j + 1), c k * sin (x k)) +
          d (j + 1) / 2 * (cos (x (j + 1) - Δ (j + 1)) - cos (x (j + 1) + Δ (j + 1))) -
          d 0 / 2 * cos (x 0 - Δ 0) + d (j + 1) / 2 * cos (x (j + 1) + Δ (j + 1)) =
        ((∑ k ∈ range (j + 1), c k * sin (x k)) - d 0 / 2 * cos (x 0 - Δ 0) + d j / 2 * w) +
          ((d (j + 1) - d j) / 2 * u + d j / 2 * (u - w)) := by
      simp only [u, w]; ring
    rw [e2]
    refine (abs_add_le _ _).trans ?_
    push_cast
    linarith

/-- **Abel summation with phase and amplitude shear.** If `c k = d k sin Δ k` with `|d k| ≤ M`
(`k ≤ n`), the phase increments are `2 Δ k` up to `e`, and `Δ`, `d` change by at most `σ`, `γ`
per step, then `|Σ_{k ≤ n} c k sin (x k)| ≤ M + n (γ + M (e + σ))/2`. -/
theorem abs_sum_shear_le {c d Δ x : ℕ → ℝ} {M γ e σ : ℝ} (n : ℕ)
    (hcd : ∀ k ≤ n, c k = d k * sin (Δ k)) (hM : ∀ k ≤ n, |d k| ≤ M)
    (hx : ∀ k < n, |x (k + 1) - x k - 2 * Δ k| ≤ e) (hΔ : ∀ k < n, |Δ (k + 1) - Δ k| ≤ σ)
    (hd : ∀ k < n, |d (k + 1) - d k| ≤ γ) :
    |∑ k ∈ range (n + 1), c k * sin (x k)| ≤ M + n * (γ + M * (e + σ)) / 2 := by
  have hinv := abs_sum_shear_aux n hcd hM hx hΔ hd n le_rfl
  have h0 : |d 0 / 2 * cos (x 0 - Δ 0)| ≤ M / 2 := by
    rw [abs_mul, abs_div, abs_two]
    have := hM 0 (Nat.zero_le _)
    have : |d 0| * |cos (x 0 - Δ 0)| ≤ M * 1 :=
      mul_le_mul this (abs_cos_le_one _) (abs_nonneg _) ((abs_nonneg _).trans this)
    linarith
  have hn : |d n / 2 * cos (x n + Δ n)| ≤ M / 2 := by
    rw [abs_mul, abs_div, abs_two]
    have := hM n le_rfl
    have : |d n| * |cos (x n + Δ n)| ≤ M * 1 :=
      mul_le_mul this (abs_cos_le_one _) (abs_nonneg _) ((abs_nonneg _).trans this)
    linarith
  set S := ∑ k ∈ range (n + 1), c k * sin (x k)
  have e1 : S = (S - d 0 / 2 * cos (x 0 - Δ 0) + d n / 2 * cos (x n + Δ n)) +
      d 0 / 2 * cos (x 0 - Δ 0) - d n / 2 * cos (x n + Δ n) := by ring
  rw [e1]
  have h1 := abs_sub ((S - d 0 / 2 * cos (x 0 - Δ 0) + d n / 2 * cos (x n + Δ n)) +
    d 0 / 2 * cos (x 0 - Δ 0)) (d n / 2 * cos (x n + Δ n))
  have h2 := abs_add_le (S - d 0 / 2 * cos (x 0 - Δ 0) + d n / 2 * cos (x n + Δ n))
    (d 0 / 2 * cos (x 0 - Δ 0))
  linarith

/-- Cosine version of `abs_sum_shear_le` (shift the phases by `π/2`). -/
theorem abs_sum_shear_cos_le {c d Δ x : ℕ → ℝ} {M γ e σ : ℝ} (n : ℕ)
    (hcd : ∀ k ≤ n, c k = d k * sin (Δ k)) (hM : ∀ k ≤ n, |d k| ≤ M)
    (hx : ∀ k < n, |x (k + 1) - x k - 2 * Δ k| ≤ e) (hΔ : ∀ k < n, |Δ (k + 1) - Δ k| ≤ σ)
    (hd : ∀ k < n, |d (k + 1) - d k| ≤ γ) :
    |∑ k ∈ range (n + 1), c k * cos (x k)| ≤ M + n * (γ + M * (e + σ)) / 2 := by
  have := abs_sum_shear_le (x := fun k => x k + π / 2) n hcd hM
    (fun k hk => by have := hx k hk; ring_nf at this ⊢; exact this) hΔ hd
  simpa only [sin_add_pi_div_two] using this

/-- **Drift of a re-anchored bounce map.** With the per-bounce kick remainder `R`, phase-step
remainder `e`, shears `σ`, `γ` and amplitude bound `M` (module docstring),
`|y (n+1) − y 0| ≤ 2M + (n+1) R + n (γ + M (e + σ))`. -/
theorem reanchored_drift_le {y φ C S Δ dC dS : ℕ → ℝ} {R M γ e σ : ℝ} (n : ℕ)
    (hkick : ∀ k ≤ n, |y (k + 1) - y k - (C k * sin (2 * φ k) + S k * cos (2 * φ k))| ≤ R)
    (hC : ∀ k ≤ n, C k = dC k * sin (Δ k)) (hS : ∀ k ≤ n, S k = dS k * sin (Δ k))
    (hMC : ∀ k ≤ n, |dC k| ≤ M) (hMS : ∀ k ≤ n, |dS k| ≤ M)
    (hφ : ∀ k < n, |2 * φ (k + 1) - 2 * φ k - 2 * Δ k| ≤ e)
    (hΔ : ∀ k < n, |Δ (k + 1) - Δ k| ≤ σ)
    (hdC : ∀ k < n, |dC (k + 1) - dC k| ≤ γ) (hdS : ∀ k < n, |dS (k + 1) - dS k| ≤ γ) :
    |y (n + 1) - y 0| ≤ 2 * M + (n + 1) * R + n * (γ + M * (e + σ)) := by
  have hsin := abs_sum_shear_le (c := C) (x := fun k => 2 * φ k) n hC hMC hφ hΔ hdC
  have hcos := abs_sum_shear_cos_le (c := S) (x := fun k => 2 * φ k) n hS hMS hφ hΔ hdS
  have htel : y (n + 1) - y 0 = ∑ k ∈ range (n + 1), (y (k + 1) - y k) :=
    (sum_range_sub y (n + 1)).symm
  have hsplit : ∑ k ∈ range (n + 1), (y (k + 1) - y k) =
      (∑ k ∈ range (n + 1), (y (k + 1) - y k - (C k * sin (2 * φ k) + S k * cos (2 * φ k)))) +
        (∑ k ∈ range (n + 1), C k * sin (2 * φ k)) +
        ∑ k ∈ range (n + 1), S k * cos (2 * φ k) := by
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring
  have herr : |∑ k ∈ range (n + 1),
      (y (k + 1) - y k - (C k * sin (2 * φ k) + S k * cos (2 * φ k)))| ≤ (n + 1) * R := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have := sum_le_sum (s := range (n + 1)) (fun k hk => hkick k (Nat.lt_succ_iff.mp
      (mem_range.mp hk)))
    rw [sum_const, card_range, nsmul_eq_mul] at this
    push_cast at this
    linarith
  rw [htel, hsplit]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add_left (abs_add_le _ _) _).trans ?_
  linarith

/-- The drift bound at a general index `k ≤ N`, under the band hypotheses of
`reanchored_band` for the anchors `0, …, k`. -/
theorem reanchored_drift_at {y φ C S Δ dC dS : ℕ → ℝ} {R M γ e σ D lo hi : ℝ} {N : ℕ}
    (hstep : ∀ k < N, (∀ j ≤ k, y j ∈ Icc lo hi) →
      |y (k + 1) - y k - (C k * sin (2 * φ k) + S k * cos (2 * φ k))| ≤ R ∧
        C k = dC k * sin (Δ k) ∧ S k = dS k * sin (Δ k) ∧ |dC k| ≤ M ∧ |dS k| ≤ M ∧
        |y (k + 1) - y k| ≤ D)
    (hpair : ∀ k, k + 1 < N → (∀ j ≤ k + 1, y j ∈ Icc lo hi) →
      |2 * φ (k + 1) - 2 * φ k - 2 * Δ k| ≤ e ∧ |Δ (k + 1) - Δ k| ≤ σ ∧
        |dC (k + 1) - dC k| ≤ γ ∧ |dS (k + 1) - dS k| ≤ γ)
    (hM : 0 ≤ M) (hγ : 0 ≤ γ) (he : 0 ≤ e) (hσ : 0 ≤ σ)
    {k : ℕ} (hk : k ≤ N) (hin : ∀ j ≤ k, y j ∈ Icc lo hi) :
    |y k - y 0| ≤ 2 * M + k * (R + γ + M * (e + σ)) := by
  rcases k with _ | n
  · simp only [sub_self, abs_zero, CharP.cast_eq_zero, zero_mul, add_zero]; linarith
  · have hin' : ∀ j ≤ n, ∀ i ≤ j, y i ∈ Icc lo hi := fun j hj i hi => hin i (by omega)
    have hd := reanchored_drift_le (y := y) (φ := φ) (C := C) (S := S) (Δ := Δ) (dC := dC)
      (dS := dS) (R := R) (M := M) (γ := γ) (e := e) (σ := σ) n
      (fun j hj => (hstep j (by omega) (hin' j hj)).1)
      (fun j hj => (hstep j (by omega) (hin' j hj)).2.1)
      (fun j hj => (hstep j (by omega) (hin' j hj)).2.2.1)
      (fun j hj => (hstep j (by omega) (hin' j hj)).2.2.2.1)
      (fun j hj => (hstep j (by omega) (hin' j hj)).2.2.2.2.1)
      (fun j hj => (hpair j (by omega) (fun i hi => hin i (by omega))).1)
      (fun j hj => (hpair j (by omega) (fun i hi => hin i (by omega))).2.1)
      (fun j hj => (hpair j (by omega) (fun i hi => hin i (by omega))).2.2.1)
      (fun j hj => (hpair j (by omega) (fun i hi => hin i (by omega))).2.2.2)
    push_cast
    have : (n : ℝ) * (γ + M * (e + σ)) ≤ (n + 1) * (γ + M * (e + σ)) := by
      have : 0 ≤ γ + M * (e + σ) := by positivity
      nlinarith
    nlinarith

/-- **Re-anchored band (discrete first exit).** Suppose the per-bounce hypotheses at step `k`
hold whenever the anchors `y 0, …, y k` (resp. `y 0, …, y (k+1)` for the shear between `k` and
`k+1`) lie in `[lo, hi]`, and every step is at most `D`. If
`2M + N (R + γ + M (e + σ)) + D ≤ min (y 0 − lo) (hi − y 0)`, then all anchors `y 0, …, y N` stay
in `[lo, hi]`, and `|y k − y 0| ≤ 2M + k (R + γ + M (e + σ))` for `k ≤ N`. -/
theorem reanchored_band {y φ C S Δ dC dS : ℕ → ℝ} {R M γ e σ D lo hi : ℝ} (N : ℕ)
    (hstep : ∀ k < N, (∀ j ≤ k, y j ∈ Icc lo hi) →
      |y (k + 1) - y k - (C k * sin (2 * φ k) + S k * cos (2 * φ k))| ≤ R ∧
        C k = dC k * sin (Δ k) ∧ S k = dS k * sin (Δ k) ∧ |dC k| ≤ M ∧ |dS k| ≤ M ∧
        |y (k + 1) - y k| ≤ D)
    (hpair : ∀ k, k + 1 < N → (∀ j ≤ k + 1, y j ∈ Icc lo hi) →
      |2 * φ (k + 1) - 2 * φ k - 2 * Δ k| ≤ e ∧ |Δ (k + 1) - Δ k| ≤ σ ∧
        |dC (k + 1) - dC k| ≤ γ ∧ |dS (k + 1) - dS k| ≤ γ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hγ : 0 ≤ γ) (he : 0 ≤ e) (hσ : 0 ≤ σ) (hD : 0 ≤ D)
    (hgap : 2 * M + N * (R + γ + M * (e + σ)) + D ≤ min (y 0 - lo) (hi - y 0)) :
    ∀ k ≤ N, y k ∈ Icc lo hi ∧ |y k - y 0| ≤ 2 * M + k * (R + γ + M * (e + σ)) := by
  have hrate : 0 ≤ R + γ + M * (e + σ) := by positivity
  have hgap1 := (hgap.trans (min_le_left _ _))
  have hgap2 := (hgap.trans (min_le_right _ _))
  -- all anchors up to `k` lie in the window
  have hall : ∀ k ≤ N, ∀ j ≤ k, y j ∈ Icc lo hi := by
    intro k
    induction k with
    | zero =>
      intro _ j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have : 0 ≤ (N : ℝ) * (R + γ + M * (e + σ)) := by positivity
      exact ⟨by linarith, by linarith⟩
    | succ k ih =>
      intro hk j hj
      have hin := ih (by omega)
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · exact hin j (by omega)
      have hj' : j = k + 1 := by omega
      subst hj'
      have hdr := reanchored_drift_at hstep hpair hM hγ he hσ (by omega : k ≤ N) hin
      have hDk := (hstep k (by omega) hin).2.2.2.2.2
      have hkN : (k : ℝ) * (R + γ + M * (e + σ)) ≤ N * (R + γ + M * (e + σ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k ≤ N)) hrate
      have htot : |y (k + 1) - y 0| ≤ 2 * M + N * (R + γ + M * (e + σ)) + D := by
        have : |y (k + 1) - y 0| ≤ |y (k + 1) - y k| + |y k - y 0| := by
          have e1 : y (k + 1) - y 0 = (y (k + 1) - y k) + (y k - y 0) := by ring
          rw [e1]; exact abs_add_le _ _
        linarith
      have := abs_le.mp htot
      exact ⟨by linarith, by linarith⟩
  intro k hk
  exact ⟨hall k hk k le_rfl, reanchored_drift_at hstep hpair hM hγ he hσ hk (hall k hk)⟩

/-! ## Sanity checks -/

/-- Sanity (special case, no shear): for constant data `c k = sin Δ`, `d k = 1`, increments
exactly `2Δ`, the bound is the classical `|Σ_{k ≤ n} sin Δ · sin (2kΔ + β)| ≤ 1`. -/
theorem abs_sum_shear_const (Δ β : ℝ) (n : ℕ) :
    |∑ k ∈ range (n + 1), sin Δ * sin (2 * k * Δ + β)| ≤ 1 := by
  have := abs_sum_shear_le (c := fun _ => sin Δ) (d := fun _ => 1) (Δ := fun _ => Δ)
    (x := fun k => 2 * k * Δ + β) (M := 1) (γ := 0) (e := 0) (σ := 0) n
    (fun _ _ => by ring) (fun _ _ => by simp)
    (fun k _ => by push_cast; ring_nf; simp) (fun _ _ => by simp) (fun _ _ => by simp)
  simpa using this

/-- Sanity (degenerate case): with zero kicks and zero remainders there is no drift. -/
theorem reanchored_drift_zero (n : ℕ) (Δ φ : ℕ → ℝ) (hφ : ∀ k, φ (k + 1) = φ k + Δ k)
    (hΔ : ∀ k, Δ k = Δ 0) :
    |(fun _ : ℕ => (0 : ℝ)) (n + 1) - (fun _ : ℕ => (0 : ℝ)) 0| ≤
      2 * 0 + (n + 1) * 0 + n * (0 + 0 * (0 + 0)) := by
  have := reanchored_drift_le (y := fun _ => (0 : ℝ)) (φ := φ) (C := fun _ => 0)
    (S := fun _ => 0) (Δ := Δ) (dC := fun _ => 0) (dS := fun _ => 0) (R := 0) (M := 0) (γ := 0)
    (e := 0) (σ := 0) n (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun k _ => by rw [hφ k]; ring_nf; simp)
    (fun k _ => by rw [hΔ (k + 1), hΔ k]; simp) (fun _ _ => by simp) (fun _ _ => by simp)
  exact this

/-- Sanity (the bound of `abs_sum_shear_le` is attained): take `Δ k = π/2` (so `sin Δ = 1`),
phases `x k = kπ + π/2` (increments exactly `2Δ = π`) and alternating amplitudes
`c k = d k = (−1)^k`, i.e. `M = 1`, `γ = 2`, `e = σ = 0`. The bound is `1 + n` and the sum is
exactly `n + 1`: amplitude shear alone can produce linear growth. -/
theorem abs_sum_shear_resonant (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k * sin (k * π + π / 2) = n + 1 := by
  have h : ∀ k : ℕ, (-1 : ℝ) ^ k * sin (k * π + π / 2) = 1 := by
    intro k
    rw [sin_add_pi_div_two, cos_nat_mul_pi, ← pow_two, ← pow_mul, mul_comm k 2, pow_mul]
    simp
  simp only [h, sum_const, card_range, nsmul_eq_mul, mul_one]
  push_cast; ring

end PlasmaLean.Kinetic.BounceShear
