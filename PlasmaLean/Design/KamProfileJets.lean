/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorConfinedForever
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Real profile derivatives from a certified Fourier strip error

The toroidal Fourier variable is twice the geometric angle, up to a constant shift.
The Cauchy estimate is applied twice, each time spending half the strip. This controls the
first and second fundamental form inputs for both profiles of an exact KAM surface.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA WEll1Z2

/-- The two geometric angles in the doubly periodic surface chart. -/
inductive ProfileAngle where
  | poloidal
  | toroidal

namespace ProfileAngle

/-- Frequency factor relative to the stored Fourier angles. -/
def factor : ProfileAngle → ℝ
  | .poloidal => 1
  | .toroidal => 2

/-- Real partial derivative in a geometric angle. -/
def partialD : ProfileAngle → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  | .poloidal, f, θ, φ => deriv (fun u => f u φ) θ
  | .toroidal, f, θ, φ => deriv (f θ) φ

/-- Fourier derivative representing the selected geometric partial. -/
def symbol : ProfileAngle → FA → FA
  | .poloidal => dTh
  | .toroidal => dPh

/-- Fourier differentiation in either angle preserves real-strip analyticity. -/
theorem analytic (a : ProfileAngle) {x : FA} (hx : Ana x) : Ana (a.symbol x) := by
  cases a <;> apply hx.d

/-- A real physical-angle partial agrees pointwise with evaluation of its Fourier derivative. -/
theorem partial_Zof (a : ProfileAngle) {x : FA} (hx : Ana x) :
    a.partialD (Zof x) = Zof (a.symbol x) := by
  funext θ φ
  cases a
  · exact (hasDerivAt_Zof_θ hx θ φ).deriv
  · exact (hasDerivAt_Zof_φ hx θ φ).deriv

private theorem symbol_sub (a : ProfileAngle) {x y : FA} (hx : Ana x) (hy : Ana y) :
    a.symbol (x - y) = a.symbol x - a.symbol y := by
  cases a <;> apply dS_sub _ _ hx hy

private theorem half_step (a : ProfileAngle) {x : FA} {ρ r M : ℝ} (h : Bd r x M)
    (hρ : 0 < ρ) (hr : ρ / 2 ≤ r) :
    Bd (r - ρ / 2) (a.symbol x) (a.factor / ρ * M) := by
  have he : ρ ≤ Real.exp 1 * (ρ / 2) := by nlinarith [Real.exp_one_gt_two, hρ]
  have step (v w : ℂ) : Bd (r - ρ / 2) (dS v w x) (max ‖v‖ ‖w‖ / ρ * M) := by
    apply (h.dS (half_pos hρ) hr v w).le
    apply mul_le_mul_of_nonneg_right _ h.nonneg
    exact div_le_div_of_nonneg_left ((norm_nonneg v).trans (le_max_left _ _)) hρ he
  cases a
  · simpa [symbol, dTh, factor] using step 1 0
  · simpa [symbol, dPh, factor] using step 0 2

private theorem pointwise {x y : FA} {M : ℝ} (h : Bd 0 (x - y) M) (θ φ : ℝ) :
    |Zof x θ φ - Zof y θ φ| ≤ M := by
  simpa [Zof, eval_sub'] using (Complex.abs_re_le_norm (eval (x - y) θ (psi φ))).trans
    (norm_eval_le_of_Bd le_rfl h θ (psi φ))

/-- Uniform first derivative error in the selected geometric direction. -/
theorem first_error (a : ProfileAngle) {x y : FA} {ρ M : ℝ} (hρ : 0 < ρ)
    (h : Bd ρ (x - y) M) (hy : Ana y) (θ φ : ℝ) :
    |a.partialD (Zof x) θ φ - a.partialD (Zof y) θ φ| ≤ a.factor / ρ * M := by
  have hd : Ana (x - y) := ⟨ρ, M, hρ, h⟩
  have hx : Ana x := by simpa using hd.add hy
  rw [a.partial_Zof hx, a.partial_Zof hy]
  apply pointwise
  rw [← a.symbol_sub hx hy]
  exact (a.half_step h hρ (by linarith)).strip (by linarith)

/-- Uniform Hessian error including the mixed component, with a factor two for each
geometric toroidal derivative. -/
theorem second_error (a b : ProfileAngle) {x y : FA} {ρ M : ℝ} (hρ : 0 < ρ)
    (h : Bd ρ (x - y) M) (hy : Ana y) (θ φ : ℝ) :
    |b.partialD (a.partialD (Zof x)) θ φ - b.partialD (a.partialD (Zof y)) θ φ| ≤
      b.factor / ρ * (a.factor / ρ * M) := by
  have hd : Ana (x - y) := ⟨ρ, M, hρ, h⟩
  have hx : Ana x := by simpa using hd.add hy
  rw [a.partial_Zof hx, a.partial_Zof hy, b.partial_Zof (a.analytic hx),
    b.partial_Zof (a.analytic hy)]
  apply pointwise
  rw [← b.symbol_sub (a.analytic hx) (a.analytic hy), ← a.symbol_sub hx hy]
  have h₁ := a.half_step h hρ (by linarith)
  have h₂ := b.half_step h₁ hρ (by linarith)
  exact h₂.strip (by linarith)

end ProfileAngle
end PlasmaLean.Design.KamNewton
