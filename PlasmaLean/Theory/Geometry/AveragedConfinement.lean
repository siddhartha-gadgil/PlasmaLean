/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.PeriodicOrbitCorrector
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite-time confinement by a corrected periodic invariant

The first theorem constructs the derivative of the corrected label along the perturbed field.
The time estimates use only an orbit segment up to a proposed first hit. Uniform bounds can
therefore be taken on the closed band; no a priori confinement assumption is needed.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AveragedConfinement

open Set
open PlasmaLean.PeriodicOrbit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate a corrected scalar along the sum of a fast field and a perturbation.
The two first-order contributions cancel; no asymptotic remainder is discarded. -/
theorem corrected_hasDerivAt {ψ g : E → ℝ} {z : ℝ → E} {u ε : ℝ} {X Y : E}
    (hψ : DifferentiableAt ℝ ψ (z u)) (hg : DifferentiableAt ℝ g (z u))
    (hfast : fderiv ℝ ψ (z u) X = 0)
    (hcor : fderiv ℝ g (z u) X = -fderiv ℝ ψ (z u) Y)
    (hz : HasDerivAt z (X + ε • Y) u) :
    HasDerivAt (fun t ↦ ψ (z t) + ε * g (z t)) (ε ^ 2 * fderiv ℝ g (z u) Y) u := by
  apply ((hψ.hasFDerivAt.comp_hasDerivAt u hz).add
    ((hg.hasFDerivAt.comp_hasDerivAt u hz).const_mul ε)).congr_deriv
  simp only [map_add, map_smul, hfast, hcor, smul_eq_mul]
  ring

/-- For an actual normalized circle action, a zero fibre mean constructs the required
corrector. The hypotheses on the action and the perturbed orbit are local at the point. -/
theorem corrected_hasDerivAt_of_mean_zero (A : PhaseAction E) {ψ T f : E → ℝ}
    {z : ℝ → E} {u ε : ℝ} {X Y : E}
    (hT : 0 < T (z u)) (hinv : ∀ s, T (A.flow s (z u)) = T (z u))
    (hf : Continuous fun s ↦ f (A.flow s (z u)))
    (hmean : A.mean f (z u) = 0) (hval : f (z u) = fderiv ℝ ψ (z u) Y)
    (hψ : DifferentiableAt ℝ ψ (z u))
    (hg : DifferentiableAt ℝ (A.corrector T f) (z u))
    (hfast : fderiv ℝ ψ (z u) X = 0)
    (hflow : HasDerivAt (fun t ↦ A.flow (t / T (z u)) (z u)) X 0)
    (hz : HasDerivAt z (X + ε • Y) u) :
    HasDerivAt (fun t ↦ ψ (z t) + ε * A.corrector T f (z t))
      (ε ^ 2 * fderiv ℝ (A.corrector T f) (z u) Y) u := by
  apply corrected_hasDerivAt hψ hg hfast _ hz
  rw [A.fderiv_corrector_generator _ _ hT hinv hf hg hflow, hmean, hval, zero_sub]

/-- Integrated displacement estimate for the original label. The endpoint correction costs
at most twice its amplitude. All derivative bounds are restricted to the tested segment. -/
theorem displacement_le {ψ g k : ℝ → ℝ} {ε t G K : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun u ↦ ψ u + ε * g u)
      (ε ^ 2 * k s) (Icc 0 t) s)
    (hk : ∀ s ∈ Icc 0 t, |k s| ≤ K) (hg₀ : |g 0| ≤ G) (hgt : |g t| ≤ G) :
    |ψ t - ψ 0| ≤ 2 * |ε| * G + t * ε ^ 2 * K := by
  have hbound (s : ℝ) (hs : s ∈ Icc 0 t) : ‖ε ^ 2 * k s‖ ≤ ε ^ 2 * K := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hk s hs) (sq_nonneg ε)
  have hmv := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hbound (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at hmv
  have h₀ := mul_le_mul_of_nonneg_left hg₀ (abs_nonneg ε)
  have h₁ := mul_le_mul_of_nonneg_left hgt (abs_nonneg ε)
  have heq : ψ t - ψ 0 = ((ψ t + ε * g t - (ψ 0 + ε * g 0)) + ε * g 0) - ε * g t := by ring
  rw [heq]
  calc
    _ ≤ |ψ t + ε * g t - (ψ 0 + ε * g 0)| + |ε * g 0| + |ε * g t| :=
      (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by rw [abs_mul, abs_mul]; linarith only [h₀, h₁, hmv]

/-- A path starting with a margin δ can reach neither edge on this segment. Applying
this at a first hit requires estimates only through that hit, including its endpoint. -/
theorem no_boundary_hit {ψ g k : ℝ → ℝ} {ε t G K δ : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun u ↦ ψ u + ε * g u)
      (ε ^ 2 * k s) (Icc 0 t) s)
    (hk : ∀ s ∈ Icc 0 t, |k s| ≤ K) (hg₀ : |g 0| ≤ G) (hgt : |g t| ≤ G)
    (hstart : δ ≤ ψ 0 ∧ ψ 0 ≤ 1 - δ)
    (hbudget : 2 * |ε| * G + t * ε ^ 2 * K < δ) : ψ t ∈ Ioo 0 1 := by
  have h := abs_lt.mp ((displacement_le ht hd hk hg₀ hgt).trans_lt hbudget)
  constructor <;> linarith [hstart.1, hstart.2, h.1, h.2]

end PlasmaLean.AveragedConfinement
