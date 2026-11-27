/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.MovingFrameTrajectory

/-!
# Variation of the frame-reduced Jacobian quadratic form over a tube

The reduced Jacobian `M⁻¹(J M - M')` in a moving frame depends on the base point only
through the spatial Jacobian `J`. A bound on the derivative of `J` in frame directions
therefore controls, by the mean value theorem along a segment, how far the quadratic
form `⟪x, M⁻¹(J(z) M - M') x⟫` can move from its value at the centre of a convex tube.
For the plane the directional bound follows from bounds for the two basis directions.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Fields.FrameJacobianVariation

open Set
open scoped RealInnerProductSpace
open PlasmaLean.Fields.LogNormTrajectory

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The frame derivative cancels in the difference of two reduced Jacobians. -/
theorem jacobian_sub (J J₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) :
    MovingFrame.jacobian J M dM - MovingFrame.jacobian J₀ M dM =
      M.symm.toContinuousLinearMap.comp ((J - J₀).comp M.toContinuousLinearMap) := by
  ext x
  simp [MovingFrame.jacobian]

/-- Pointwise form of `jacobian_sub`. -/
theorem jacobian_sub_apply (J J₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) (x : E) :
    MovingFrame.jacobian J M dM x - MovingFrame.jacobian J₀ M dM x =
      M.symm ((J - J₀) (M x)) := by
  rw [← sub_apply, jacobian_sub]
  rfl

end Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The difference of the quadratic forms of two reduced Jacobians in a common frame. -/
theorem inner_jacobian_sub (J J₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) (x : E) :
    ⟪x, MovingFrame.jacobian J M dM x⟫ - ⟪x, MovingFrame.jacobian J₀ M dM x⟫ =
      ⟪x, M.symm ((J - J₀) (M x))⟫ := by
  rw [← inner_sub_right, jacobian_sub_apply]

/-- Mean value bound: a directional bound for the derivative of the spatial Jacobian on
a convex tube limits the change of the reduced quadratic form between two of its points
at frame displacement `v`. -/
theorem abs_quad_sub_le {T : Set E} {J : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
    {x z₀ v : E} {M : E ≃L[ℝ] E} {γ : ℝ} (dM : E →L[ℝ] E) (hT : Convex ℝ T)
    (hJ : ∀ ζ ∈ T, HasFDerivAt J (DJ ζ) ζ)
    (hD : ∀ ζ ∈ T, ∀ w : E, |⟪x, M.symm ((DJ ζ (M w)) (M x))⟫| ≤ γ * ‖w‖ * ‖x‖ ^ 2)
    (hz : z₀ ∈ T) (hv : z₀ + M v ∈ T) :
    |⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫ -
      ⟪x, MovingFrame.jacobian (J z₀) M dM x⟫| ≤ γ * ‖v‖ * ‖x‖ ^ 2 := by
  let c := fun t : ℝ => z₀ + t • M v
  have hd (t : ℝ) : HasDerivAt c (M v) t := by
    simpa [c] using ((hasDerivAt_id t).smul_const (M v)).const_add z₀
  have hc (t : ℝ) (ht : t ∈ Icc 0 1) : c t ∈ T := by
    have h := hT.add_smul_sub_mem hz hv ht
    simpa [c] using h
  let g := fun t : ℝ => ⟪x, M.symm (J (c t) (M x))⟫
  have hg (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt g ⟪x, M.symm ((DJ (c t) (M v)) (M x))⟫ t := by
    have h1 : HasDerivAt (fun t => J (c t)) (DJ (c t) (M v)) t :=
      (hJ _ (hc t ht)).comp_hasDerivAt t (hd t)
    have h2 : HasDerivAt (fun t => J (c t) (M x)) ((DJ (c t) (M v)) (M x)) t := by
      simpa using h1.clm_apply (hasDerivAt_const t (M x))
    have h3 := M.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h2
    simpa [g] using (hasDerivAt_const t x).inner ℝ h3
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope g
    (fun t => ⟪x, M.symm ((DJ (c t) (M v)) (M x))⟫) zero_lt_one
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hg t (Ioo_subset_Icc_self ht))
  have hb := hD _ (hc t (Ioo_subset_Icc_self ht)) v
  rw [he] at hb
  have hq : ⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫ -
      ⟪x, MovingFrame.jacobian (J z₀) M dM x⟫ = (g 1 - g 0) / (1 - 0) := by
    rw [inner_jacobian_sub]
    simp [g, c, inner_sub_right]
  rw [hq]
  exact hb

/-- A bound at the centre of the tube and the mean value bound give a bound for the
reduced quadratic form at every point of the tube within frame radius `ρ`. -/
theorem abs_quad_le_of_center {T : Set E} {J : E → E →L[ℝ] E}
    {DJ : E → E →L[ℝ] E →L[ℝ] E} {x z₀ v : E} {M : E ≃L[ℝ] E} {γ μ₀ ρ : ℝ}
    (dM : E →L[ℝ] E) (hT : Convex ℝ T) (hJ : ∀ ζ ∈ T, HasFDerivAt J (DJ ζ) ζ)
    (hD : ∀ ζ ∈ T, ∀ w : E, |⟪x, M.symm ((DJ ζ (M w)) (M x))⟫| ≤ γ * ‖w‖ * ‖x‖ ^ 2)
    (hz : z₀ ∈ T) (hv : z₀ + M v ∈ T) (hγ : 0 ≤ γ) (hρ : ‖v‖ ≤ ρ)
    (h₀ : |⟪x, MovingFrame.jacobian (J z₀) M dM x⟫| ≤ μ₀ * ‖x‖ ^ 2) :
    |⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫| ≤ (μ₀ + γ * ρ) * ‖x‖ ^ 2 := by
  have h := abs_quad_sub_le dM hT hJ hD hz hv
  have hm : γ * ‖v‖ * ‖x‖ ^ 2 ≤ γ * ρ * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ hγ) (sq_nonneg _)
  have ht := abs_sub_abs_le_abs_sub ⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫
    ⟪x, MovingFrame.jacobian (J z₀) M dM x⟫
  linarith

/-- Sanity check: where the spatial Jacobian has zero derivative on the tube, the reduced
quadratic form does not depend on the base point. -/
theorem quad_eq_of_fderiv_zero {T : Set E} {J : E → E →L[ℝ] E} {z₀ v : E}
    {M : E ≃L[ℝ] E} (dM : E →L[ℝ] E) (x : E) (hT : Convex ℝ T)
    (hJ : ∀ ζ ∈ T, HasFDerivAt J (0 : E →L[ℝ] E →L[ℝ] E) ζ)
    (hz : z₀ ∈ T) (hv : z₀ + M v ∈ T) :
    ⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫ =
      ⟪x, MovingFrame.jacobian (J z₀) M dM x⟫ := by
  have h := abs_quad_sub_le (x := x) (γ := 0) (DJ := fun _ => 0) dM hT hJ
    (fun ζ _ w => by simp) hz hv
  have h0 : |⟪x, MovingFrame.jacobian (J (z₀ + M v)) M dM x⟫ -
      ⟪x, MovingFrame.jacobian (J z₀) M dM x⟫| ≤ 0 := by simpa using h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

/-- Sanity check for a constant spatial Jacobian: the mean value bound holds with
coefficient zero. -/
theorem abs_quad_sub_le_const (J₀ : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E)
    (x z₀ v : E) :
    |⟪x, MovingFrame.jacobian ((fun _ : E => J₀) (z₀ + M v)) M dM x⟫ -
      ⟪x, MovingFrame.jacobian ((fun _ : E => J₀) z₀) M dM x⟫| ≤ 0 * ‖v‖ * ‖x‖ ^ 2 :=
  abs_quad_sub_le (T := univ) (J := fun _ : E => J₀) (DJ := fun _ => 0) (x := x) (γ := 0)
    (z₀ := z₀) (v := v) (M := M) dM convex_univ
    (fun ζ _ => hasFDerivAt_const J₀ ζ) (fun ζ _ w => by simp) (mem_univ _) (mem_univ _)

/-- In the plane, bounds for the two basis directions give the directional bound of
`abs_quad_sub_le` with the Euclidean combination of the two coefficients. -/
theorem directional_bound_of_basis {T : Set (EuclideanSpace ℝ (Fin 2))}
    {DJ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) →L[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)}
    {x : EuclideanSpace ℝ (Fin 2)}
    {M : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)} {g₀ g₁ : ℝ}
    (h₀ : ∀ ζ ∈ T, |⟪x, M.symm ((DJ ζ (M (EuclideanSpace.single 0 1))) (M x))⟫| ≤
      g₀ * ‖x‖ ^ 2)
    (h₁ : ∀ ζ ∈ T, |⟪x, M.symm ((DJ ζ (M (EuclideanSpace.single 1 1))) (M x))⟫| ≤
      g₁ * ‖x‖ ^ 2) :
    ∀ ζ ∈ T, ∀ w : EuclideanSpace ℝ (Fin 2),
      |⟪x, M.symm ((DJ ζ (M w)) (M x))⟫| ≤ Real.sqrt (g₀ ^ 2 + g₁ ^ 2) * ‖w‖ * ‖x‖ ^ 2 := by
  intro ζ hζ w
  have hw : w = w 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      w 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hlin : ⟪x, M.symm ((DJ ζ (M w)) (M x))⟫ =
      w 0 * ⟪x, M.symm ((DJ ζ (M (EuclideanSpace.single 0 1))) (M x))⟫ +
        w 1 * ⟪x, M.symm ((DJ ζ (M (EuclideanSpace.single 1 1))) (M x))⟫ := by
    conv_lhs => rw [hw]
    simp only [map_add, map_smul, add_apply,
      smul_apply, inner_add_right, inner_smul_right]
  have hn : ‖w‖ = Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  have hcs : |w 0| * g₀ + |w 1| * g₁ ≤ Real.sqrt (g₀ ^ 2 + g₁ ^ 2) * ‖w‖ := by
    rw [hn, ← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (|w 0| * g₁ - |w 1| * g₀), sq_abs (w 0), sq_abs (w 1)]
  have hx : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  rw [hlin]
  calc
    _ ≤ |w 0| * (g₀ * ‖x‖ ^ 2) + |w 1| * (g₁ * ‖x‖ ^ 2) := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (h₀ ζ hζ) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (h₁ ζ hζ) (abs_nonneg _))
    _ = (|w 0| * g₀ + |w 1| * g₁) * ‖x‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcs hx

end PlasmaLean.Fields.FrameJacobianVariation
