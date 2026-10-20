/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQA
public import PlasmaLean.Theory.Kinetic.TrappedOrbits
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Trapped alphas in the reactor-scale near-axis QA model (rung M4)

Companion to `notes/theory/near-qa-trapped-particles.md` (targets T2 and the reactor form of the
discrete averaging statement). All statements are about the truncated near-axis **model**
`reactorQA` (`Design/NearAxisQA`) inside the vacuum Boozer guiding-centre model; the `O(r³)`
remainder of a real field is not bounded.

Results:

* `cos_two_well`: for `g(θ) = c + A cos θ + C cos 2θ` with `A < 0` and `4|C| < −A`, `g` is
  strictly increasing on `[0, π]` and strictly decreasing on `[π, 2π]`; `cos_two_well_minmax`:
  `θ = 0` is the unique minimiser and `θ = π` the unique maximiser on `[0, 2π)`.
  `cos_two_well_fails`: for `A = −1`, `C = 1` (`4|C| > −A`) monotonicity on `[0, π]` fails,
  so the condition is not vacuous.
* `reactorQA_single_well`: on every surface `0 < ψ ≤ ψ_a` (`0 < r ≤ a = 1.7 m`) and at every
  fixed `φ`, `θ ↦ B(ψ, θ, φ)` is strictly increasing on `[0, π]` and strictly decreasing on
  `[π, 2π]`: exactly one magnetic well (minimum at `θ = 0`) and one maximum (`θ = π`) per
  poloidal period. Condition used: `4 B₂c r² < B₀ |η| r`, i.e. `r < 6.04 m`.
  `reactorQA_single_well_minmax` gives the unique-extremum form.
* `lineB_single_well` / `reactorQA_single_well_fieldLine`: the same along every field line
  `φ = (θ − α)/ι₀`, ripple term `b₁ cos 2φ` included. There are critical points
  `θ₀ ≈ 0`, `θ₁ ≈ π`, `θ₂ ≈ 2π` (each within `1/20` rad) with `B` strictly increasing on
  `[θ₀, θ₁]` and strictly decreasing on `[θ₁, θ₂]`, for every `α`; so every poloidal turn has
  exactly one well (no ripple wells, obstruction O3 absent in the model). The minimum is shifted
  off `θ = 0` by the ripple, so the note's draft "strictly increasing on `[0, π]` along the line"
  is false in general. Margins used: `2|D|/ι < (−A − 4|C|)/40` and
  `4|C| + 4|D|/ι² < (19/20)(−A)` with `A = B₀ η r`, `C = B₂c r²`, `D = b₁ r²`.
* `reactorQA_Bφ_continuousOn`: `∂_φB` is continuous along any model orbit (integrability for
  the bounce identity).
* `reactorQA_bounce_step`: per-bounce identity `q ι₀ Δψ = ∫ (q²ρ²B/m + μ)(−2 b₁ r² sin 2φ) dt`
  between turning points.
* `reactorQA_bounce_drift_nonresonant`: **conditional** bounded secular drift over `N` bounces:
  if the per-bounce kicks are `A sin(kα + β)` up to `R` (assumed) and `sin(α/2) ≠ 0`
  (non-resonance, assumed), then `|ψ(τ N) − ψ(τ 0)| ≤ (|A|/|sin(α/2)| + N R)/(|q| ι₀)`.

**Scope.** The kick form, the non-resonance condition and the existence of turning points in the
drift theorem are hypotheses; deriving the kick form needs validated bounce integrals over the
exact-QA banana (target T4 of the note).
-/
public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQA
open PlasmaLean.Kinetic.Boozer Real

/-! ## Generic single-well lemma -/

/-- Derivative of `c + A cos θ + C cos 2θ`. -/
theorem hasDerivAt_cos_two (c A C θ : ℝ) :
    HasDerivAt (fun θ => c + A * cos θ + C * cos (2 * θ))
      (sin θ * (-A - 4 * C * cos θ)) θ := by
  have h := ((hasDerivAt_const θ c).add ((hasDerivAt_cos θ).const_mul A)).add
    ((((hasDerivAt_id θ).const_mul 2).cos).const_mul C)
  convert h using 1
  · funext x; simp only [Pi.add_apply, id]
  · simp only [id, sin_two_mul]; ring

/-- `−A − 4C cos θ > 0` when `4|C| < −A`. -/
theorem cos_two_factor_pos {A C : ℝ} (hC : 4 * |C| < -A) (θ : ℝ) : 0 < -A - 4 * C * cos θ := by
  have : C * cos θ ≤ |C| := by
    calc C * cos θ ≤ |C * cos θ| := le_abs_self _
      _ = |C| * |cos θ| := abs_mul _ _
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one θ) (abs_nonneg _)
      _ = |C| := mul_one _
  linarith

/-- **Generic single-well lemma.** If `4|C| < −A`, then `g(θ) = c + A cos θ + C cos 2θ` is
strictly increasing on `[0, π]` and strictly decreasing on `[π, 2π]`. -/
theorem cos_two_well {A C : ℝ} (hC : 4 * |C| < -A) (c : ℝ) :
    StrictMonoOn (fun θ => c + A * cos θ + C * cos (2 * θ)) (Set.Icc 0 π) ∧
      StrictAntiOn (fun θ => c + A * cos θ + C * cos (2 * θ)) (Set.Icc π (2 * π)) := by
  have hcont : Continuous (fun θ => c + A * cos θ + C * cos (2 * θ)) := by fun_prop
  constructor
  · refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cos_two c A C x).deriv]
    exact mul_pos (sin_pos_of_pos_of_lt_pi hx.1 hx.2) (cos_two_factor_pos hC x)
  · refine strictAntiOn_of_deriv_neg (convex_Icc π (2 * π)) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cos_two c A C x).deriv]
    have hs : sin x < 0 := by
      have e : sin x = sin (x - 2 * π) := by rw [sin_sub_two_pi]
      rw [e]
      exact sin_neg_of_neg_of_neg_pi_lt (by linarith [hx.2]) (by linarith [hx.1])
    exact mul_neg_of_neg_of_pos hs (cos_two_factor_pos hC x)

/-- **Unique minimum and maximum per period.** Under `4|C| < −A`, for
`g(θ) = c + A cos θ + C cos 2θ`: `g(0) < g(θ)` for `θ ∈ (0, 2π)` and `g(θ) < g(π)` for
`θ ∈ [0, 2π)`, `θ ≠ π`. With `2π`-periodicity this is one well and one maximum per period. -/
theorem cos_two_well_minmax {A C : ℝ} (hC : 4 * |C| < -A) (c : ℝ) :
    (∀ θ ∈ Set.Ioo 0 (2 * π),
        c + A * cos 0 + C * cos (2 * 0) < c + A * cos θ + C * cos (2 * θ)) ∧
      (∀ θ ∈ Set.Ico 0 (2 * π), θ ≠ π →
        c + A * cos θ + C * cos (2 * θ) < c + A * cos π + C * cos (2 * π)) := by
  obtain ⟨hmono, hanti⟩ := cos_two_well hC c
  have hπ := pi_pos
  have h2π : c + A * cos (2 * π) + C * cos (2 * (2 * π)) = c + A * cos 0 + C * cos (2 * 0) := by
    have : cos (2 * (2 * π)) = 1 := by
      rw [show 2 * (2 * π) = ((2 : ℕ) : ℝ) * (2 * π) by push_cast; ring, cos_nat_mul_two_pi]
    simp [this]
  constructor
  · intro θ hθ
    rcases le_or_gt θ π with h | h
    · exact hmono ⟨le_rfl, hπ.le⟩ ⟨hθ.1.le, h⟩ hθ.1
    · rw [← h2π]
      exact hanti ⟨h.le, hθ.2.le⟩ ⟨by linarith, le_rfl⟩ hθ.2
  · intro θ hθ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hmono ⟨hθ.1, h.le⟩ ⟨hπ.le, le_rfl⟩ h
    · exact hanti ⟨le_rfl, by linarith⟩ ⟨h.le, hθ.2.le⟩ h

/-- **The single-well condition is not vacuous.** For `A = −1`, `C = 1` (so `4|C| > −A`),
`θ ↦ −cos θ + cos 2θ` is not monotone on `[0, π]`: its value at `π/3` (`−1`) is below its value
at `0` (`0`), so `θ = 0` is not the minimum (a second well appears). -/
theorem cos_two_well_fails :
    ¬ StrictMonoOn (fun θ => 0 + (-1) * cos θ + 1 * cos (2 * θ)) (Set.Icc 0 π) := by
  intro h
  have hπ := pi_pos
  have := h ⟨le_rfl, hπ.le⟩ ⟨by positivity, by linarith⟩ (by positivity : (0 : ℝ) < π / 3)
  have e : cos (2 * (π / 3)) = -(1 / 2) := by
    rw [show 2 * (π / 3) = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  simp only [cos_zero, mul_zero, e, cos_pi_div_three] at this
  norm_num at this

/-! ## Single-well property of `reactorQA` -/

/-- `reactorQA.B` at fixed `(ψ, φ)` as a function of `θ` is `c + A cos θ + C cos 2θ` with
`A = B₀ η r` and `C = B₂c r²` (written with `r² = 2ψ/B₀`). -/
theorem reactorQA_B_theta (ψ φ : ℝ) :
    (fun θ => reactorQA.B ψ θ φ) = fun θ =>
      (57 / 10 + 2 * ψ / (57 / 10) * (-137 / 10000 + -43 / 100000 * cos (2 * φ))) +
        (57 / 10 * (-7 / 100) * radius (57 / 10) ψ) * cos θ +
        (2 * ψ / (57 / 10) * (33 / 2000)) * cos (2 * θ) := by
  funext θ
  simp only [reactorQA, field, nearAxisB]
  ring

/-- The single-well condition `4 |B₂c r²| < −B₀ η r` holds on `0 < ψ ≤ ψ_a`. -/
theorem reactorQA_well_condition {ψ : ℝ} (hψ0 : 0 < ψ) (hψ : ψ ≤ psiEdge) :
    4 * |2 * ψ / (57 / 10) * (33 / 2000)| < -(57 / 10 * (-7 / 100) * radius (57 / 10) ψ) := by
  have hr2 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψ0.le
  have hr := radius_le_edge hψ
  have hrpos : 0 < radius (57 / 10) ψ := sqrt_pos.mpr (by positivity)
  rw [abs_of_pos (by positivity), ← hr2]
  nlinarith

/-- **Single-well property of `reactorQA` at fixed `φ`** (target T2, fixed-`φ` form). On every
surface `0 < ψ ≤ ψ_a` (radius `0 < r ≤ 1.7 m`) and for every `φ`, `θ ↦ B(ψ, θ, φ)` is strictly
increasing on `[0, π]` and strictly decreasing on `[π, 2π]`. -/
theorem reactorQA_single_well {ψ φ : ℝ} (hψ0 : 0 < ψ) (hψ : ψ ≤ psiEdge) :
    StrictMonoOn (fun θ => reactorQA.B ψ θ φ) (Set.Icc 0 π) ∧
      StrictAntiOn (fun θ => reactorQA.B ψ θ φ) (Set.Icc π (2 * π)) := by
  rw [reactorQA_B_theta]
  exact cos_two_well (reactorQA_well_condition hψ0 hψ) _

/-- **One well and one maximum per poloidal period** for `reactorQA` at fixed `φ`, `0 < r ≤ a`:
the minimum over `[0, 2π)` is attained only at `θ = 0` and the maximum only at `θ = π`. -/
theorem reactorQA_single_well_minmax {ψ φ : ℝ} (hψ0 : 0 < ψ) (hψ : ψ ≤ psiEdge) :
    (∀ θ ∈ Set.Ioo 0 (2 * π), reactorQA.B ψ 0 φ < reactorQA.B ψ θ φ) ∧
      (∀ θ ∈ Set.Ico 0 (2 * π), θ ≠ π → reactorQA.B ψ θ φ < reactorQA.B ψ π φ) := by
  have h := cos_two_well_minmax (reactorQA_well_condition hψ0 hψ)
    (57 / 10 + 2 * ψ / (57 / 10) * (-137 / 10000 + -43 / 100000 * cos (2 * φ)))
  have e := congrFun (reactorQA_B_theta ψ φ)
  simp only [e]
  exact h

/-! ## Single well along field lines

Along the field line `θ = α + ι φ` the field strength is
`g(θ) = c + A cos θ + C cos 2θ + D cos(2(θ − α)/ι)`; the last (ripple) term is the
symmetry-breaking `b₁ cos 2φ`. It is not `2π`-periodic in `θ`, but shifting `θ` by `2πk` is the same
as replacing `α` by `α − 2πk`, so a statement for all `α` covers every poloidal turn. -/

/-- Field strength along a field line, in the abstract form
`c + A cos θ + C cos 2θ + D cos(2(θ − α)/ι)`. -/
@[expose] def lineB (c A C D ι α θ : ℝ) : ℝ :=
  c + A * cos θ + C * cos (2 * θ) + D * cos (2 * ((θ - α) / ι))

/-- `dg/dθ` along the field line. -/
@[expose] def lineB' (A C D ι α θ : ℝ) : ℝ :=
  -(A * sin θ) - 2 * C * sin (2 * θ) - 2 * D / ι * sin (2 * ((θ - α) / ι))

/-- `d²g/dθ²` along the field line. -/
@[expose] def lineB'' (A C D ι α θ : ℝ) : ℝ :=
  -(A * cos θ) - 4 * C * cos (2 * θ) - 4 * D / ι ^ 2 * cos (2 * ((θ - α) / ι))

/-- First derivative of `lineB`. -/
theorem hasDerivAt_lineB (c A C D ι α θ : ℝ) (hι : ι ≠ 0) :
    HasDerivAt (lineB c A C D ι α) (lineB' A C D ι α θ) θ := by
  have h := (((hasDerivAt_const θ c).add ((hasDerivAt_cos θ).const_mul A)).add
    ((((hasDerivAt_id θ).const_mul 2).cos).const_mul C)).add
    (((((hasDerivAt_id θ).sub_const α).div_const ι).const_mul 2).cos.const_mul D)
  convert h using 1
  · funext x; simp only [lineB, Pi.add_apply, id]
  · simp only [lineB', id]; field_simp; ring

/-- Second derivative of `lineB`. -/
theorem hasDerivAt_lineB' (A C D ι α θ : ℝ) (hι : ι ≠ 0) :
    HasDerivAt (lineB' A C D ι α) (lineB'' A C D ι α θ) θ := by
  have h := ((((hasDerivAt_sin θ).const_mul A).neg).sub
    ((((hasDerivAt_id θ).const_mul 2).sin).const_mul (2 * C))).sub
    (((((hasDerivAt_id θ).sub_const α).div_const ι).const_mul 2).sin.const_mul (2 * D / ι))
  convert h using 1
  · funext x; simp only [lineB', Pi.sub_apply, Pi.neg_apply, id]
  · simp only [lineB'', id]; field_simp; ring

/-- `lineB'` is continuous. -/
theorem continuous_lineB' (A C D ι α : ℝ) : Continuous (lineB' A C D ι α) := by
  unfold lineB'; fun_prop

/-- `|a sin x| ≤ |a|` and `|a cos x| ≤ |a|`. -/
theorem abs_mul_sin_cos_le (a x : ℝ) : |a * sin x| ≤ |a| ∧ |a * cos x| ≤ |a| := by
  rw [abs_mul, abs_mul]
  exact ⟨mul_le_of_le_one_right (abs_nonneg a) (abs_sin_le_one x),
    mul_le_of_le_one_right (abs_nonneg a) (abs_cos_le_one x)⟩

/-- Sign of `g'` where `sin θ ≥ 1/40`, under the first-derivative margin
`2|D|/ι < (−A − 4|C|)/40`. -/
theorem lineB'_pos {A C D ι α θ : ℝ} (hs : 2 * |D| / ι < (-A - 4 * |C|) / 40) (hι : 0 < ι)
    (hθ : 1 / 40 ≤ sin θ) : 0 < lineB' A C D ι α θ := by
  have hK : 0 ≤ 2 * |D| / ι := by positivity
  have h1 := abs_le.mp (abs_mul_sin_cos_le C θ).2
  have h2 := abs_le.mp (abs_mul_sin_cos_le (2 * D / ι) (2 * ((θ - α) / ι))).1
  have e2 : |2 * D / ι| = 2 * |D| / ι := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos hι]
  have e : lineB' A C D ι α θ = sin θ * (-A - 4 * (C * cos θ)) -
      2 * D / ι * sin (2 * ((θ - α) / ι)) := by
    simp only [lineB', sin_two_mul]; ring
  rw [e]
  nlinarith

/-- Sign of `g'` where `sin θ ≤ −1/40`. -/
theorem lineB'_neg {A C D ι α θ : ℝ} (hs : 2 * |D| / ι < (-A - 4 * |C|) / 40) (hι : 0 < ι)
    (hθ : sin θ ≤ -(1 / 40)) : lineB' A C D ι α θ < 0 := by
  have hK : 0 ≤ 2 * |D| / ι := by positivity
  have h1 := abs_le.mp (abs_mul_sin_cos_le C θ).2
  have h2 := abs_le.mp (abs_mul_sin_cos_le (2 * D / ι) (2 * ((θ - α) / ι))).1
  have e2 : |2 * D / ι| = 2 * |D| / ι := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos hι]
  have e : lineB' A C D ι α θ = sin θ * (-A - 4 * (C * cos θ)) -
      2 * D / ι * sin (2 * ((θ - α) / ι)) := by
    simp only [lineB', sin_two_mul]; ring
  rw [e]
  nlinarith

/-- Sign of `g''` where `cos θ ≥ 19/20`, under the second-derivative margin
`4|C| + 4|D|/ι² < (19/20)(−A)`. -/
theorem lineB''_pos {A C D ι α θ : ℝ} (hc : 4 * |C| + 4 * |D| / ι ^ 2 < 19 / 20 * -A)
    (hι : 0 < ι) (hθ : 19 / 20 ≤ cos θ) : 0 < lineB'' A C D ι α θ := by
  have hK : 0 ≤ 4 * |D| / ι ^ 2 := by positivity
  have hA : 0 < -A := by nlinarith [abs_nonneg C]
  have h1 := abs_le.mp (abs_mul_sin_cos_le C (2 * θ)).2
  have h2 := abs_le.mp (abs_mul_sin_cos_le (4 * D / ι ^ 2) (2 * ((θ - α) / ι))).2
  have e2 : |4 * D / ι ^ 2| = 4 * |D| / ι ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (pow_pos hι 2)]
  have e : lineB'' A C D ι α θ = -A * cos θ - 4 * (C * cos (2 * θ)) -
      4 * D / ι ^ 2 * cos (2 * ((θ - α) / ι)) := by
    simp only [lineB'']; ring
  rw [e]
  nlinarith

/-- Sign of `g''` where `cos θ ≤ −19/20`. -/
theorem lineB''_neg {A C D ι α θ : ℝ} (hc : 4 * |C| + 4 * |D| / ι ^ 2 < 19 / 20 * -A)
    (hι : 0 < ι) (hθ : cos θ ≤ -(19 / 20)) : lineB'' A C D ι α θ < 0 := by
  have hK : 0 ≤ 4 * |D| / ι ^ 2 := by positivity
  have hA : 0 < -A := by nlinarith [abs_nonneg C]
  have h1 := abs_le.mp (abs_mul_sin_cos_le C (2 * θ)).2
  have h2 := abs_le.mp (abs_mul_sin_cos_le (4 * D / ι ^ 2) (2 * ((θ - α) / ι))).2
  have e2 : |4 * D / ι ^ 2| = 4 * |D| / ι ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (pow_pos hι 2)]
  have e : lineB'' A C D ι α θ = -A * cos θ - 4 * (C * cos (2 * θ)) -
      4 * D / ι ^ 2 * cos (2 * ((θ - α) / ι)) := by
    simp only [lineB'']; ring
  rw [e]
  nlinarith

/-- `sin θ ≥ 1/40` on `[1/20, π − 1/20]` (Jordan's inequality and `π ≤ 4`). -/
theorem sin_ge_of_mem {θ : ℝ} (h : θ ∈ Set.Icc (1 / 20) (π - 1 / 20)) : 1 / 40 ≤ sin θ := by
  have hπ4 := pi_le_four
  have hπ3 := pi_gt_three
  have key : ∀ x, 1 / 20 ≤ x → x ≤ π / 2 → 1 / 40 ≤ sin x := fun x h1 h2 => by
    have := mul_le_sin (by linarith) h2
    have : 1 / 40 ≤ 2 / π * x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ pi_pos]; nlinarith
    linarith
  rcases le_total θ (π / 2) with h' | h'
  · exact key θ h.1 h'
  · rw [← sin_pi_sub]; exact key (π - θ) (by linarith [h.2]) (by linarith)

/-- `sin θ ≤ −1/40` on `[π + 1/20, 2π − 1/20]`. -/
theorem sin_le_of_mem {θ : ℝ} (h : θ ∈ Set.Icc (π + 1 / 20) (2 * π - 1 / 20)) :
    sin θ ≤ -(1 / 40) := by
  have := sin_ge_of_mem (θ := θ - π) ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [sin_sub_pi] at this
  linarith

/-- `cos θ ≥ 19/20` for `|θ − 2πk| ≤ 1/20`, `k ∈ {0, 1}`. -/
theorem cos_ge_of_near {θ : ℝ} (h : |θ| ≤ 1 / 20 ∨ |θ - 2 * π| ≤ 1 / 20) : 19 / 20 ≤ cos θ := by
  rcases h with h | h
  · have := abs_cos_sub_cos_le θ 0
    rw [cos_zero, sub_zero] at this
    linarith [(abs_le.mp this).1]
  · have := abs_cos_sub_cos_le (θ - 2 * π) 0
    rw [cos_zero, cos_sub_two_pi, sub_zero] at this
    linarith [(abs_le.mp this).1]

/-- `cos θ ≤ −19/20` for `|θ − π| ≤ 1/20`. -/
theorem cos_le_of_near {θ : ℝ} (h : |θ - π| ≤ 1 / 20) : cos θ ≤ -(19 / 20) := by
  have := abs_cos_sub_cos_le (θ - π) 0
  rw [cos_zero, cos_sub_pi, sub_zero] at this
  linarith [(abs_le.mp this).1]

/-- **Generic field-line single-well theorem.** Under the margins
`2|D|/ι < (−A − 4|C|)/40` and `4|C| + 4|D|/ι² < (19/20)(−A)`, for every field-line label `α`
there are critical points `θ₀ ∈ (−1/20, 1/20)`, `θ₁ ∈ (π − 1/20, π + 1/20)`,
`θ₂ ∈ (2π − 1/20, 2π + 1/20)` with `g` strictly increasing on `[θ₀, θ₁]` and strictly decreasing
on `[θ₁, θ₂]`: exactly one minimum (near `θ = 0`) and one maximum (near `θ = π`) per poloidal
turn, no ripple wells. -/
theorem lineB_single_well {c A C D ι : ℝ} (hι : 0 < ι)
    (hs : 2 * |D| / ι < (-A - 4 * |C|) / 40) (hc : 4 * |C| + 4 * |D| / ι ^ 2 < 19 / 20 * -A)
    (α : ℝ) :
    ∃ θ₀ ∈ Set.Ioo (-(1 / 20)) (1 / 20), ∃ θ₁ ∈ Set.Ioo (π - 1 / 20) (π + 1 / 20),
      ∃ θ₂ ∈ Set.Ioo (2 * π - 1 / 20) (2 * π + 1 / 20),
        StrictMonoOn (lineB c A C D ι α) (Set.Icc θ₀ θ₁) ∧
          StrictAntiOn (lineB c A C D ι α) (Set.Icc θ₁ θ₂) := by
  have hπ3 := pi_gt_three
  set g' := lineB' A C D ι α with hg'
  have hcont := continuous_lineB' A C D ι α
  have hsδ : 1 / 40 ≤ sin (1 / 20) := sin_ge_of_mem ⟨le_rfl, by linarith⟩
  -- monotonicity of `g'` in the three windows
  have w0 : StrictMonoOn g' (Set.Icc (-(1 / 20)) (1 / 20)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_lineB' A C D ι α x hι.ne').deriv]
    exact lineB''_pos hc hι (cos_ge_of_near (Or.inl (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)))
  have w1 : StrictAntiOn g' (Set.Icc (π - 1 / 20) (π + 1 / 20)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_lineB' A C D ι α x hι.ne').deriv]
    exact lineB''_neg hc hι (cos_le_of_near (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  have w2 : StrictMonoOn g' (Set.Icc (2 * π - 1 / 20) (2 * π + 1 / 20)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_lineB' A C D ι α x hι.ne').deriv]
    exact lineB''_pos hc hι
      (cos_ge_of_near (Or.inr (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)))
  -- endpoint signs
  have s1 : g' (-(1 / 20)) < 0 := lineB'_neg hs hι (by rw [sin_neg]; linarith)
  have s2 : 0 < g' (1 / 20) := lineB'_pos hs hι hsδ
  have s3 : 0 < g' (π - 1 / 20) := lineB'_pos hs hι (sin_ge_of_mem ⟨by linarith, le_rfl⟩)
  have s4 : g' (π + 1 / 20) < 0 := lineB'_neg hs hι (sin_le_of_mem ⟨le_rfl, by linarith⟩)
  have s5 : g' (2 * π - 1 / 20) < 0 := lineB'_neg hs hι (sin_le_of_mem ⟨by linarith, le_rfl⟩)
  have s6 : 0 < g' (2 * π + 1 / 20) := lineB'_pos hs hι (by
    rw [add_comm, sin_add_two_pi]; exact hsδ)
  -- critical points by the intermediate value theorem
  obtain ⟨θ₀, hθ₀, e₀⟩ := intermediate_value_Ioo (by norm_num) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g' (-(1 / 20))) (g' (1 / 20)) from ⟨s1, s2⟩)
  obtain ⟨θ₁, hθ₁, e₁⟩ := intermediate_value_Ioo' (by linarith) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g' (π + 1 / 20)) (g' (π - 1 / 20)) from ⟨s4, s3⟩)
  obtain ⟨θ₂, hθ₂, e₂⟩ := intermediate_value_Ioo (by linarith) hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Ioo (g' (2 * π - 1 / 20)) (g' (2 * π + 1 / 20)) from ⟨s5, s6⟩)
  have hgc : Continuous (lineB c A C D ι α) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_lineB c A C D ι α x hι.ne').continuousAt
  refine ⟨θ₀, hθ₀, θ₁, hθ₁, θ₂, hθ₂, ?_, ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hgc.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_lineB c A C D ι α x hι.ne').deriv]
    change 0 < g' x
    rcases lt_or_ge x (1 / 20) with h1 | h1
    · rw [← e₀]
      exact w0 ⟨hθ₀.1.le, hθ₀.2.le⟩ ⟨by linarith [hθ₀.1, hx.1], h1.le⟩ hx.1
    rcases le_or_gt x (π - 1 / 20) with h2 | h2
    · exact lineB'_pos hs hι (sin_ge_of_mem ⟨h1, h2⟩)
    · rw [← e₁]
      exact w1 ⟨h2.le, by linarith [hx.2, hθ₁.2]⟩ ⟨hθ₁.1.le, hθ₁.2.le⟩ hx.2
  · refine strictAntiOn_of_deriv_neg (convex_Icc _ _) hgc.continuousOn fun x hx => ?_
    rw [interior_Icc] at hx
    rw [(hasDerivAt_lineB c A C D ι α x hι.ne').deriv]
    change g' x < 0
    rcases lt_or_ge x (π + 1 / 20) with h1 | h1
    · rw [← e₁]
      exact w1 ⟨hθ₁.1.le, hθ₁.2.le⟩ ⟨by linarith [hθ₁.1, hx.1], h1.le⟩ hx.1
    rcases le_or_gt x (2 * π - 1 / 20) with h2 | h2
    · exact lineB'_neg hs hι (sin_le_of_mem ⟨h1, h2⟩)
    · rw [← e₂]
      exact w2 ⟨h2.le, by linarith [hx.2, hθ₂.2]⟩ ⟨hθ₂.1.le, hθ₂.2.le⟩ hx.2

/-- `reactorQA.B` along the field line `φ = (θ − α)/ι₀` in the form `lineB`, with
`A = B₀ η r`, `C = B₂c r²`, `D = b₁ r²` (`r² = 2ψ/B₀`). -/
theorem reactorQA_B_line (ψ α θ : ℝ) :
    reactorQA.B ψ θ ((θ - α) / (211 / 500)) =
      lineB (57 / 10 + 2 * ψ / (57 / 10) * (-137 / 10000))
        (57 / 10 * (-7 / 100) * radius (57 / 10) ψ) (2 * ψ / (57 / 10) * (33 / 2000))
        (2 * ψ / (57 / 10) * (-43 / 100000)) (211 / 500) α θ := by
  simp only [reactorQA, field, nearAxisB, lineB]
  ring

/-- **Single-well property of `reactorQA` along field lines** (target T2, field-line form).
For every surface `0 < ψ ≤ ψ_a` (`0 < r ≤ 1.7 m`) and every field-line label `α`, the field
strength `θ ↦ B(ψ, θ, (θ − α)/ι₀)` along the line has critical points
`θ₀ ∈ (−1/20, 1/20)`, `θ₁ ∈ (π − 1/20, π + 1/20)`, `θ₂ ∈ (2π − 1/20, 2π + 1/20)`, is strictly
increasing on `[θ₀, θ₁]` and strictly decreasing on `[θ₁, θ₂]`. Since the statement holds for all
`α` (and `θ ↦ θ + 2πk` amounts to `α ↦ α − 2πk`), every poloidal turn has exactly one magnetic
well and one maximum: no ripple wells, so obstruction O3 is absent in the model. -/
theorem reactorQA_single_well_fieldLine {ψ : ℝ} (hψ0 : 0 < ψ) (hψ : ψ ≤ psiEdge) (α : ℝ) :
    ∃ θ₀ ∈ Set.Ioo (-(1 / 20)) (1 / 20), ∃ θ₁ ∈ Set.Ioo (π - 1 / 20) (π + 1 / 20),
      ∃ θ₂ ∈ Set.Ioo (2 * π - 1 / 20) (2 * π + 1 / 20),
        StrictMonoOn (fun θ => reactorQA.B ψ θ ((θ - α) / (211 / 500))) (Set.Icc θ₀ θ₁) ∧
          StrictAntiOn (fun θ => reactorQA.B ψ θ ((θ - α) / (211 / 500))) (Set.Icc θ₁ θ₂) := by
  have hr2 := radius_sq (by norm_num : (0 : ℝ) < 57 / 10) hψ0.le
  have hr := radius_le_edge hψ
  have hrpos : 0 < radius (57 / 10) ψ := sqrt_pos.mpr (by positivity)
  have e : (fun θ => reactorQA.B ψ θ ((θ - α) / (211 / 500))) =
      lineB (57 / 10 + 2 * ψ / (57 / 10) * (-137 / 10000))
        (57 / 10 * (-7 / 100) * radius (57 / 10) ψ) (2 * ψ / (57 / 10) * (33 / 2000))
        (2 * ψ / (57 / 10) * (-43 / 100000)) (211 / 500) α := funext (reactorQA_B_line ψ α)
  rw [e]
  have hC : |2 * ψ / (57 / 10) * (33 / 2000)| = radius (57 / 10) ψ ^ 2 * (33 / 2000) := by
    rw [abs_of_pos (by positivity), hr2]
  have hD : |2 * ψ / (57 / 10) * (-43 / 100000)| = radius (57 / 10) ψ ^ 2 * (43 / 100000) := by
    rw [abs_of_neg (by nlinarith), hr2]; ring
  apply lineB_single_well (by norm_num)
  · rw [hC, hD]; nlinarith [mul_le_mul_of_nonneg_left hr hrpos.le]
  · rw [hC, hD]; norm_num; nlinarith [mul_le_mul_of_nonneg_left hr hrpos.le]

/-! ## Bounce steps in `reactorQA` -/

/-- `∂_φB` of `reactorQA` is continuous along any orbit of the model on `[0, T]`. -/
theorem reactorQA_Bφ_continuousOn {m q μ T : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    (h : BoozerGCOrbitOn reactorQA m q μ ψ θ φ ρ T) :
    ContinuousOn (along reactorQA.Bφ ψ θ φ) (Set.Icc 0 T) := by
  have hψ : ContinuousOn ψ (Set.Icc 0 T) :=
    fun s hs => (h.dψ s hs).continuousAt.continuousWithinAt
  have hφ : ContinuousOn φ (Set.Icc 0 T) :=
    fun s hs => (h.dφ s hs).continuousAt.continuousWithinAt
  change ContinuousOn (fun t => nearAxisBφ (57 / 10) (-43 / 100000) (ψ t) (φ t)) (Set.Icc 0 T)
  unfold nearAxisBφ
  exact ((((continuousOn_const.mul hψ).div_const _).mul
    (continuousOn_const.mul
      (Real.continuous_sin.comp_continuousOn (continuousOn_const.mul hφ))))).neg

/-- **Per-bounce identity in `reactorQA`.** Between turning points `t₀ ≤ t₁` (`v_∥ = 0`):
`q ι₀ (ψ(t₁) − ψ(t₀)) = ∫_{t₀}^{t₁} (q²ρ²B/m + μ) ∂_φB dt`, with
`∂_φB = −2 b₁ r² sin 2φ` (`nearAxis_symmetryDefect`) and `ι₀ = 211/500`. -/
theorem reactorQA_bounce_step {m q μ T t₀ t₁ : ℝ} {ψ θ φ ρ : ℝ → ℝ} (hm : m ≠ 0) (hq : q ≠ 0)
    (h : BoozerGCOrbitOn reactorQA m q μ ψ θ φ ρ T) (h0 : 0 ≤ t₀) (h01 : t₀ ≤ t₁)
    (h1T : t₁ ≤ T) (hB₀ : 0 < along reactorQA.B ψ θ φ t₀) (hB₁ : 0 < along reactorQA.B ψ θ φ t₁)
    (hv₀ : parallelVelocity reactorQA m q ψ θ φ ρ t₀ = 0)
    (hv₁ : parallelVelocity reactorQA m q ψ θ φ ρ t₁ = 0) :
    q * (211 / 500) * (ψ t₁ - ψ t₀) = ∫ t in t₀..t₁, qaKick reactorQA m q μ ψ θ φ ρ t := by
  have := bounce_psip_step hm hq (by norm_num [reactorQA, field]) h h0 h01 h1T
    ((reactorQA_Bφ_continuousOn h).mono (Set.Icc_subset_Icc h0 h1T)) hB₀ hB₁ hv₀ hv₁
  rw [← this]
  simp only [reactorQA, field]
  ring

/-- **Bounded secular drift of trapped alphas in `reactorQA` over `N` bounces
(conditional).** Let `τ 0 ≤ τ 1 ≤ … ≤ τ N ≤ T` be turning points of a model orbit on `[0, T]`
with `B > 0` there. **Assumed:** (i) the per-bounce kicks have the leading-order form
`|∫_{τ k}^{τ(k+1)} (q²ρ²B/m + μ) ∂_φB dt − A sin(kα + β)| ≤ R` (bounce average of the `b₁` term
over the exact-QA banana, toroidal phase advancing by `α` per bounce, remainder `R` absorbing
precession shear and finite-orbit-width corrections); (ii) non-resonance `sin(α/2) ≠ 0`.
Then `|ψ(τ N) − ψ(τ 0)| ≤ (|A|/|sin(α/2)| + N R)/(|q| ι₀)`: the order-`A` kicks do not
accumulate; only the remainder grows linearly in the number of bounces. -/
theorem reactorQA_bounce_drift_nonresonant {m q μ T A α β R : ℝ} {ψ θ φ ρ : ℝ → ℝ}
    {τ : ℕ → ℝ} {N : ℕ} (hm : m ≠ 0) (hq : q ≠ 0)
    (h : BoozerGCOrbitOn reactorQA m q μ ψ θ φ ρ T) (hτ : Monotone τ) (h0 : 0 ≤ τ 0)
    (hNT : τ N ≤ T) (hB : ∀ k ≤ N, 0 < along reactorQA.B ψ θ φ (τ k))
    (hv : ∀ k ≤ N, parallelVelocity reactorQA m q ψ θ φ ρ (τ k) = 0)
    (hα : sin (α / 2) ≠ 0)
    (hkick : ∀ k < N,
      |(∫ t in τ k..τ (k + 1), qaKick reactorQA m q μ ψ θ φ ρ t) - A * sin (k * α + β)| ≤ R) :
    |ψ (τ N) - ψ (τ 0)| ≤ (|A| / |sin (α / 2)| + N * R) / (|q| * (211 / 500)) := by
  have := bounce_drift_nonresonant hm hq (by norm_num [reactorQA, field]) h hτ h0 hNT
    (reactorQA_Bφ_continuousOn h) hB hv hα hkick
  have e : reactorQA.ψp (ψ (τ N)) - reactorQA.ψp (ψ (τ 0)) =
      211 / 500 * (ψ (τ N) - ψ (τ 0)) := by
    simp only [reactorQA, field]; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 211 / 500)] at this
  rw [le_div_iff₀ (by positivity)]
  linarith

end PlasmaLean.Design.NearAxisQA
