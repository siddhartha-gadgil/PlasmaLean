/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.ApproximateInvariant
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Oscillatory integration by parts for a scalar observable (Lemma A, M4/T8)

Source: `notes/theory/guiding-centre-averaging.md` §2.1 (Lemma A, proved informally there;
this file is the formal version). It is the elementary step at the heart of first-order
averaging (Sanders–Verhulst–Murdock Ch. 2, Arnold–Kozlov–Neishtadt Ch. 6), applied to a
supplied scalar observable along a supplied orbit, with explicit constants.

Setting on `[0,T]`: `P' = a sin Φ + b cos Φ + e`, `Φ' = Ω ≥ Ω₀ > 0`,
`(a/Ω)' = α`, `(b/Ω)' = β`, `|a| + |b| ≤ A`, `|α| + |β| ≤ A₁`, `|e| ≤ η`.

* `osc_ibp_remainder`: with `F = -(a/Ω) cos Φ + (b/Ω) sin Φ`, exactly
  `(P - F)' = α cos Φ - β sin Φ + e`;
* `osc_ibp_drift` (**Lemma A**): `|P t - P 0| ≤ 2A/Ω₀ + (A₁ + η) t`;
* `osc_ibp_drift_iter` (k-fold): for amplitude sequences with `(aⱼ/Ω)' = bⱼ₊₁`,
  `(bⱼ/Ω)' = -aⱼ₊₁` and `|aⱼ| + |bⱼ| ≤ Aⱼ`,
  `|P t - P 0| ≤ 2 (∑_{j<k} Aⱼ)/Ω₀ + (A_k + η) t`;
* sanity: a pure oscillation `A sin(Ω₀ t)/Ω₀` has no secular term (`osc_pure_bounded`),
  while constant forcing `P = η t` attains the secular term exactly and is unbounded
  (`osc_secular_needed`); the pure oscillation also reaches `A/Ω₀` at `t = π/(2Ω₀)`
  (`osc_oscillatory_needed`), so neither term in Lemma A can be dropped (the oscillatory
  constant `2A/Ω₀` is sharp up to the factor 2).

The note's statement is correct as written. The hypothesis `Ω ≥ Ω₀ > 0` is essential (a
phase whose frequency crosses zero, e.g. trapped particles, is excluded). The iteration in
the note, `(a, b) ↦ (-β, α)`, is encoded by the sequence convention above.
This is a scalar ODE-observable lemma; the amplitude bounds `Aⱼ` along actual orbits are
separate obligations (e.g. interval certificates).
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic

/-- The integration-by-parts corrector `F = -(a/Ω) cos Φ + (b/Ω) sin Φ`. -/
@[expose] def oscCorrector (a b Ω Φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -(a r / Ω r) * Real.cos (Φ r) + b r / Ω r * Real.sin (Φ r)

/-- The corrector is bounded by `(|a| + |b|)/Ω`. -/
theorem abs_oscCorrector_le {a b Ω Φ : ℝ → ℝ} {Ω₀ A r : ℝ} (hΩ₀ : 0 < Ω₀) (hΩ : Ω₀ ≤ Ω r)
    (hA : |a r| + |b r| ≤ A) : |oscCorrector a b Ω Φ r| ≤ A / Ω₀ := by
  have hpos : 0 < Ω r := lt_of_lt_of_le hΩ₀ hΩ
  unfold oscCorrector
  have h1 : |-(a r / Ω r) * Real.cos (Φ r)| ≤ |a r| / Ω r := by
    rw [abs_mul, abs_neg, abs_div, abs_of_pos hpos]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have h2 : |b r / Ω r * Real.sin (Φ r)| ≤ |b r| / Ω r := by
    rw [abs_mul, abs_div, abs_of_pos hpos]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  calc _ ≤ |a r| / Ω r + |b r| / Ω r := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (|a r| + |b r|) / Ω r := by ring
    _ ≤ A / Ω r := by gcongr
    _ ≤ A / Ω₀ := div_le_div_of_nonneg_left hA0 hΩ₀ hΩ

/-- **Exact remainder** of one integration by parts: `(P - F)' = α cos Φ - β sin Φ + e`.
The remainder has the same oscillatory form, with amplitudes `(a, b) ↦ (-β, α)`. -/
theorem osc_ibp_remainder {P Φ a b Ω e α β : ℝ → ℝ} {s : ℝ}
    (hP : HasDerivAt P (a s * Real.sin (Φ s) + b s * Real.cos (Φ s) + e s) s)
    (hΦ : HasDerivAt Φ (Ω s) s)
    (ha : HasDerivAt (fun r => a r / Ω r) (α s) s)
    (hb : HasDerivAt (fun r => b r / Ω r) (β s) s) (hΩ : Ω s ≠ 0) :
    HasDerivAt (fun r => P r - oscCorrector a b Ω Φ r)
      (α s * Real.cos (Φ s) - β s * Real.sin (Φ s) + e s) s := by
  have hc := hΦ.cos
  have hs := hΦ.sin
  have hF : HasDerivAt (oscCorrector a b Ω Φ)
      (-α s * Real.cos (Φ s) + -(a s / Ω s) * (-Real.sin (Φ s) * Ω s) +
        (β s * Real.sin (Φ s) + b s / Ω s * (Real.cos (Φ s) * Ω s))) s := by
    convert (ha.neg.mul hc).add (hb.mul hs) using 1
    funext r; simp [oscCorrector]
  convert hP.sub hF using 1
  field_simp
  ring

/-- Bound on the oscillatory remainder `|α cos Φ - β sin Φ + e| ≤ (|α| + |β|) + |e|`. -/
theorem abs_osc_remainder_le (α β e φ : ℝ) :
    |α * Real.cos φ - β * Real.sin φ + e| ≤ |α| + |β| + |e| := by
  have h1 : |α * Real.cos φ| ≤ |α| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |β * Real.sin φ| ≤ |β| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  calc _ ≤ |α * Real.cos φ - β * Real.sin φ| + |e| := abs_add_le _ _
    _ ≤ |α * Real.cos φ| + |β * Real.sin φ| + |e| := by gcongr; exact abs_sub _ _
    _ ≤ _ := by gcongr

/-- Generic step: if `P - F` drifts at most `R t` and `|F| ≤ c` at both ends, then
`|P t - P 0| ≤ 2c + R t`. -/
private theorem drift_of_corrector {P F : ℝ → ℝ} {c D : ℝ} {t : ℝ}
    (hD : |(P t - F t) - (P 0 - F 0)| ≤ D) (ht : |F t| ≤ c) (h0 : |F 0| ≤ c) :
    |P t - P 0| ≤ 2 * c + D := by
  have e : P t - P 0 = ((P t - F t) - (P 0 - F 0)) + F t - F 0 := by ring
  rw [e]
  calc _ ≤ |((P t - F t) - (P 0 - F 0)) + F t| + |F 0| := abs_sub _ _
    _ ≤ |(P t - F t) - (P 0 - F 0)| + |F t| + |F 0| := by gcongr; exact abs_add_le _ _
    _ ≤ D + c + c := by gcongr
    _ = _ := by ring

/-- **Lemma A (oscillatory integration by parts).** If on `[0,T]`
`P' = a sin Φ + b cos Φ + e`, `Φ' = Ω ≥ Ω₀ > 0`, `(a/Ω)' = α`, `(b/Ω)' = β`,
`|a| + |b| ≤ A`, `|α| + |β| ≤ A₁`, `|e| ≤ η`, then for `t ∈ [0,T]`
`|P t - P 0| ≤ 2A/Ω₀ + (A₁ + η) t`. -/
theorem osc_ibp_drift {P Φ a b Ω e α β : ℝ → ℝ} {T A A₁ η Ω₀ t : ℝ} (hΩ₀ : 0 < Ω₀)
    (hP : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt P (a s * Real.sin (Φ s) + b s * Real.cos (Φ s) + e s) s)
    (hΦ : ∀ s ∈ Set.Icc 0 T, HasDerivAt Φ (Ω s) s)
    (ha : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => a r / Ω r) (α s) s)
    (hb : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => b r / Ω r) (β s) s)
    (hΩ : ∀ s ∈ Set.Icc 0 T, Ω₀ ≤ Ω s) (hA : ∀ s ∈ Set.Icc 0 T, |a s| + |b s| ≤ A)
    (hA₁ : ∀ s ∈ Set.Icc 0 T, |α s| + |β s| ≤ A₁) (he : ∀ s ∈ Set.Icc 0 T, |e s| ≤ η)
    (ht : t ∈ Set.Icc 0 T) :
    |P t - P 0| ≤ 2 * A / Ω₀ + (A₁ + η) * t := by
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hD := invariant_drift (K := fun r => P r - oscCorrector a b Ω Φ r)
    (fun s hs => osc_ibp_remainder (hP s hs) (hΦ s hs) (ha s hs) (hb s hs)
      (lt_of_lt_of_le hΩ₀ (hΩ s hs)).ne')
    (fun s hs => (abs_osc_remainder_le _ _ _ _).trans (add_le_add (hA₁ s hs) (he s hs))) ht
  have := drift_of_corrector hD (abs_oscCorrector_le hΩ₀ (hΩ t ht) (hA t ht))
    (abs_oscCorrector_le hΩ₀ (hΩ 0 h0T) (hA 0 h0T))
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Iterated Lemma A (k-fold).** Amplitude sequences `a b : ℕ → ℝ → ℝ` with
`(aⱼ/Ω)' = bⱼ₊₁` and `(bⱼ/Ω)' = -aⱼ₊₁` (the note's map `(a, b) ↦ (-β, α)`), bounds
`|aⱼ| + |bⱼ| ≤ Aⱼ` for `j ≤ k`, and `P' = a₀ sin Φ + b₀ cos Φ + e`. Then
`|P t - P 0| ≤ 2 (∑_{j<k} Aⱼ)/Ω₀ + (A_k + η) t`: the secular rate is `A_k + η`. -/
theorem osc_ibp_drift_iter {Φ Ω e : ℝ → ℝ} {T η Ω₀ t : ℝ} (hΩ₀ : 0 < Ω₀)
    (hΦ : ∀ s ∈ Set.Icc 0 T, HasDerivAt Φ (Ω s) s)
    (hΩ : ∀ s ∈ Set.Icc 0 T, Ω₀ ≤ Ω s) (he : ∀ s ∈ Set.Icc 0 T, |e s| ≤ η)
    (ht : t ∈ Set.Icc 0 T) :
    ∀ (k : ℕ) (P : ℝ → ℝ) (a b : ℕ → ℝ → ℝ) (A : ℕ → ℝ),
      (∀ s ∈ Set.Icc 0 T,
        HasDerivAt P (a 0 s * Real.sin (Φ s) + b 0 s * Real.cos (Φ s) + e s) s) →
      (∀ j < k, ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => a j r / Ω r) (b (j + 1) s) s) →
      (∀ j < k, ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => b j r / Ω r) (-a (j + 1) s) s) →
      (∀ j ≤ k, ∀ s ∈ Set.Icc 0 T, |a j s| + |b j s| ≤ A j) →
      |P t - P 0| ≤ 2 * (∑ j ∈ Finset.range k, A j) / Ω₀ + (A k + η) * t := by
  intro k
  induction k with
  | zero =>
    intro P a b A hP _ _ hA
    have hD := invariant_drift hP (fun s hs => by
      have := abs_osc_remainder_le (b 0 s) (-a 0 s) (e s) (Φ s)
      rw [abs_neg] at this
      have hA0 := hA 0 le_rfl s hs
      calc _ = |b 0 s * Real.cos (Φ s) - -a 0 s * Real.sin (Φ s) + e s| := by ring_nf
        _ ≤ _ := this
        _ ≤ A 0 + η := by linarith [he s hs]) ht
    simpa using hD
  | succ k ih =>
    intro P a b A hP ha hb hA
    have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    set F := oscCorrector (a 0) (b 0) Ω Φ
    have hP' : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => P r - F r)
        (a 1 s * Real.sin (Φ s) + b 1 s * Real.cos (Φ s) + e s) s := by
      intro s hs
      have := osc_ibp_remainder (α := fun r => b 1 r) (β := fun r => -a 1 r) (hP s hs)
        (hΦ s hs) (ha 0 (by omega) s hs)
        (hb 0 (by omega) s hs) (lt_of_lt_of_le hΩ₀ (hΩ s hs)).ne'
      convert this using 1
      ring
    have hih := ih (fun r => P r - F r) (fun j => a (j + 1)) (fun j => b (j + 1))
      (fun j => A (j + 1)) hP' (fun j hj s hs => ha (j + 1) (by omega) s hs)
      (fun j hj s hs => hb (j + 1) (by omega) s hs)
      (fun j hj s hs => hA (j + 1) (by omega) s hs)
    have hc := drift_of_corrector hih
      (abs_oscCorrector_le hΩ₀ (hΩ t ht) (hA 0 (by omega) t ht))
      (abs_oscCorrector_le hΩ₀ (hΩ 0 h0T) (hA 0 (by omega) 0 h0T))
    rw [Finset.sum_range_succ']
    calc _ ≤ _ := hc
      _ = _ := by ring

/-! ## Sanity checks -/

/-- Sanity (`k = 1` is Lemma A): with `a₁ = -β`, `b₁ = α` the iterated bound specializes to
`2A₀/Ω₀ + (A₁ + η) t`. -/
theorem osc_ibp_drift_iter_one {P Φ Ω e : ℝ → ℝ} {a b : ℕ → ℝ → ℝ} {A : ℕ → ℝ}
    {T η Ω₀ t : ℝ} (hΩ₀ : 0 < Ω₀)
    (hP : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt P (a 0 s * Real.sin (Φ s) + b 0 s * Real.cos (Φ s) + e s) s)
    (hΦ : ∀ s ∈ Set.Icc 0 T, HasDerivAt Φ (Ω s) s)
    (ha : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => a 0 r / Ω r) (b 1 s) s)
    (hb : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun r => b 0 r / Ω r) (-a 1 s) s)
    (hΩ : ∀ s ∈ Set.Icc 0 T, Ω₀ ≤ Ω s) (he : ∀ s ∈ Set.Icc 0 T, |e s| ≤ η)
    (hA : ∀ j ≤ 1, ∀ s ∈ Set.Icc 0 T, |a j s| + |b j s| ≤ A j) (ht : t ∈ Set.Icc 0 T) :
    |P t - P 0| ≤ 2 * A 0 / Ω₀ + (A 1 + η) * t := by
  have := osc_ibp_drift_iter hΩ₀ hΦ hΩ he ht 1 P a b A hP
    (fun j hj => by obtain rfl : j = 0 := by omega
                    exact ha)
    (fun j hj => by obtain rfl : j = 0 := by omega
                    exact hb) hA
  simpa using this

/-- Sanity (pure oscillation): `P t = A sin(Ω₀ t)/Ω₀` with `P' = A cos(Ω₀ t)` (constant
amplitude and frequency, so `α = β = 0`, `e = 0`) satisfies Lemma A with **no secular term**:
`|P t - P 0| ≤ 2A/Ω₀` for every `t ≥ 0`. -/
theorem osc_pure_bounded {A Ω₀ t : ℝ} (hA : 0 ≤ A) (hΩ₀ : 0 < Ω₀) (ht : 0 ≤ t) :
    |A * Real.sin (Ω₀ * t) / Ω₀ - A * Real.sin (Ω₀ * 0) / Ω₀| ≤ 2 * A / Ω₀ := by
  have hΦ : ∀ s : ℝ, HasDerivAt (fun r => Ω₀ * r) Ω₀ s := fun s => by
    simpa using (hasDerivAt_id s).const_mul Ω₀
  have h := osc_ibp_drift (P := fun r => A * Real.sin (Ω₀ * r) / Ω₀) (Φ := fun r => Ω₀ * r)
    (a := fun _ => 0) (b := fun _ => A) (Ω := fun _ => Ω₀) (e := fun _ => 0)
    (α := fun _ => 0) (β := fun _ => 0) (T := t) (A := A) (A₁ := 0) (η := 0) (t := t) hΩ₀
    (fun s _ => by
      have := ((hΦ s).sin.const_mul A).div_const Ω₀
      convert this using 1
      field_simp
      ring)
    (fun s _ => hΦ s) (fun s _ => by simpa using hasDerivAt_const s (0 / Ω₀))
    (fun s _ => hasDerivAt_const s (A / Ω₀)) (fun _ _ => le_rfl)
    (fun _ _ => by simp [abs_of_nonneg hA]) (fun _ _ => by simp) (fun _ _ => by simp)
    ⟨ht, le_rfl⟩
  simpa using h

/-- Sanity (the oscillatory term is needed): the pure oscillation `A sin(Ω₀ t)/Ω₀`, which has
`a = 0`, `b = A`, `α = β = e = 0` (so `A₁ = η = 0`), reaches `|P t - P 0| = A/Ω₀` at
`t = π/(2Ω₀)`. Hence the constant term of Lemma A cannot be dropped, and `2A/Ω₀` is sharp up
to the factor 2. -/
theorem osc_oscillatory_needed {A Ω₀ : ℝ} (hA : 0 ≤ A) (hΩ₀ : 0 < Ω₀) :
    |A * Real.sin (Ω₀ * (Real.pi / (2 * Ω₀))) / Ω₀ - A * Real.sin (Ω₀ * 0) / Ω₀| = A / Ω₀ := by
  have : Ω₀ * (Real.pi / (2 * Ω₀)) = Real.pi / 2 := by field_simp
  rw [this, Real.sin_pi_div_two, mul_zero, Real.sin_zero]
  simp [abs_of_nonneg (div_nonneg hA hΩ₀.le)]

/-- Sanity (the secular term is needed): constant forcing `P t = η t` (`a = b = 0`,
`e = η`) attains the secular bound `η t` exactly, and is unbounded, so no bound of the form
`|P t - P 0| ≤ C` (oscillatory term alone) can hold. -/
theorem osc_secular_needed {η : ℝ} (hη : 0 < η) :
    (∀ t, 0 ≤ t → |η * t - η * 0| = η * t) ∧
      ¬ ∃ C : ℝ, ∀ t, 0 ≤ t → |η * t - η * 0| ≤ C := by
  refine ⟨fun t ht => by simp [abs_of_nonneg (mul_nonneg hη.le ht)], ?_⟩
  rintro ⟨C, hC⟩
  have h := hC ((|C| + 1) / η) (by positivity)
  rw [mul_zero, sub_zero, mul_div_cancel₀ _ hη.ne', abs_of_pos (by positivity)] at h
  linarith [le_abs_self C]

/-- Sanity (Lemma A applied to constant forcing): with `a = b = 0`, `e = η`, Lemma A gives
`|P t - P 0| ≤ η t`, which is attained by `osc_secular_needed`, so the bound is sharp in its
secular part. -/
theorem osc_constant_forcing {η Ω₀ t : ℝ} (hη : 0 ≤ η) (hΩ₀ : 0 < Ω₀) (ht : 0 ≤ t) :
    |η * t - η * 0| ≤ 2 * 0 / Ω₀ + (0 + η) * t := by
  have h := osc_ibp_drift (P := fun r => η * r) (Φ := fun r => Ω₀ * r)
    (a := fun _ => 0) (b := fun _ => 0) (Ω := fun _ => Ω₀) (e := fun _ => η)
    (α := fun _ => 0) (β := fun _ => 0) (T := t) (A := 0) (A₁ := 0) (η := η) (t := t) hΩ₀
    (fun s _ => by simpa using (hasDerivAt_id s).const_mul η)
    (fun s _ => by simpa using (hasDerivAt_id s).const_mul Ω₀)
    (fun s _ => by simpa using hasDerivAt_const s (0 / Ω₀))
    (fun s _ => by simpa using hasDerivAt_const s (0 / Ω₀)) (fun _ _ => le_rfl)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp [abs_of_nonneg hη])
    ⟨ht, le_rfl⟩
  simpa using h

end PlasmaLean.Kinetic
