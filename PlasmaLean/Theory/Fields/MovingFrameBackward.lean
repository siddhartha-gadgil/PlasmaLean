/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.MovingFrameSlabs
public import PlasmaLean.Theory.Fields.BackwardDistance

/-!
# Backward existence and two-sided distance estimates in a moving frame

Reversing time turns a lower bound for the quadratic form of the frame Jacobian into
the upper bound used by the forward solver. Every point of the frame ellipsoid at the
end of a slab is therefore the endpoint of a solution on the whole slab, with the same
propagated radius. Two solutions that stay in the trial ellipsoid have frame separations
at the two ends of an interval that differ by at most the exponential factor given by a
two-sided bound for the same quadratic form.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Fields.TrajectorySlabs.MovingFrame

open Set Filter
open scoped Topology RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reversing the field and the frame velocity reverses the frame Jacobian. -/
theorem jacobian_neg (J : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) :
    LogNormTrajectory.MovingFrame.jacobian (-J) M (-dM) =
      -LogNormTrajectory.MovingFrame.jacobian J M dM := by
  ext v
  simp only [LogNormTrajectory.MovingFrame.jacobian, ContinuousLinearMap.comp_apply,
    sub_apply, neg_apply, ContinuousLinearEquiv.coe_coe,
    neg_sub_neg, map_sub, neg_sub]

/-- Derivative of a path traversed in the opposite direction on a closed interval. -/
theorem hasDerivWithinAt_reverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {f' : V} {a b t : ℝ} (h : HasDerivWithinAt f f' (Icc a b) (a + b - t)) :
    HasDerivWithinAt (fun u => f (a + b - u)) (-f') (Icc a b) t := by
  have hσ : HasDerivWithinAt (fun u : ℝ => a + b - u) (-1) (Icc a b) t :=
    ((hasDerivAt_id t).const_sub (a + b)).hasDerivWithinAt
  have maps : MapsTo (fun u : ℝ => a + b - u) (Icc a b) (Icc a b) := fun u hu =>
    ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  refine (h.scomp t hσ maps).congr_deriv ?_
  simp

/-- The inverse of a differentiable frame with continuous inverse is differentiable,
with derivative `-M⁻¹ M' M⁻¹`. -/
theorem hasDerivWithinAt_symm {M : ℝ → E ≃L[ℝ] E} {dM : E →L[ℝ] E} {s : Set ℝ} {τ : ℝ}
    (hM : HasDerivWithinAt (fun u => (M u).toContinuousLinearMap) dM s τ)
    (hc : ContinuousWithinAt (fun u => (M u).symm.toContinuousLinearMap) s τ) :
    HasDerivWithinAt (fun u => (M u).symm.toContinuousLinearMap)
      (-((M τ).symm.toContinuousLinearMap.comp
        (dM.comp (M τ).symm.toContinuousLinearMap))) s τ := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hM ⊢
  have hc' : Tendsto (fun u => (M u).symm.toContinuousLinearMap) (𝓝[s \ {τ}] τ)
      (𝓝 (M τ).symm.toContinuousLinearMap) := (hc.mono sdiff_subset).tendsto
  have key (u : ℝ) : slope (fun u => (M u).symm.toContinuousLinearMap) τ u =
      -((M u).symm.toContinuousLinearMap.comp
        ((slope (fun u => (M u).toContinuousLinearMap) τ u).comp
          (M τ).symm.toContinuousLinearMap)) := by
    ext v
    simp only [slope, vsub_eq_sub, smul_apply, sub_apply,
      neg_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      map_smul, map_sub, ContinuousLinearEquiv.symm_apply_apply,
      ContinuousLinearEquiv.apply_symm_apply, neg_sub, smul_sub]
  have inner := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).continuous.tendsto
    (dM, (M τ).symm.toContinuousLinearMap)
  have outer := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).continuous.tendsto
    ((M τ).symm.toContinuousLinearMap, dM.comp (M τ).symm.toContinuousLinearMap)
  have lim := (outer.comp (hc'.prodMk_nhds
    (inner.comp (hM.prodMk_nhds tendsto_const_nhds)))).neg
  exact lim.congr fun u => (key u).symm

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a longer interval with the same data the propagated radius is no smaller. -/
theorem propagated_mono_right {a t b r L ε : ℝ} (hat : a ≤ t) (htb : t ≤ b) (hr : 0 ≤ r)
    (hε : 0 ≤ ε) (hLen : max 0 L * (b - a) < 1) :
    propagated a t r L ε ≤ propagated a b r L ε := by
  have hm : 0 ≤ max 0 L := le_max_left _ _
  have num := mul_le_mul_of_nonneg_right (sub_le_sub_right htb a) hε
  have den := mul_le_mul_of_nonneg_left (sub_le_sub_right htb a) hm
  unfold propagated
  exact div_le_div₀ (add_nonneg hr (mul_nonneg (by linarith only [hat, htb]) hε))
    (by linarith only [num]) (by linarith only [hLen]) (by linarith only [den])

/-- Backward existence on one slab. A lower bound for the quadratic form of the frame
Jacobian on the trial ball gives, for every point of the ellipsoid at the end of the
slab, a solution on the whole slab ending there. It stays in the ellipsoid of the
propagated radius, in particular at the start. -/
theorem backward_step_of_defect [CompleteSpace E] {F : ℝ → E → E} {J : ℝ → E → E →L[ℝ] E}
    {p dp : ℝ → E} {M : ℝ → E ≃L[ℝ] E} {dM : ℝ → E →L[ℝ] E} {S : Set E}
    {a b r L ε T : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hLen : max 0 L * (b - a) < 1) (hTrial : propagated a b r L ε < T)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hTube : Metric.closedBall (0 : E) T ⊆ S)
    (hRet : ∃ P : E → E, LipschitzWith 1 P ∧ (∀ v, P v ∈ S) ∧ ∀ v ∈ S, P v = v)
    (hp : ∀ t ∈ Icc a b, HasDerivWithinAt p (dp t) (Icc a b) t)
    (hM : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => (M u).toContinuousLinearMap) (dM t) (Icc a b) t)
    (hcInv : ContinuousOn (fun t => (M t).symm.toContinuousLinearMap) (Icc a b))
    (hcdp : ContinuousOn dp (Icc a b)) (hcdM : ContinuousOn dM (Icc a b))
    (hF : ContinuousOn (fun q : ℝ × E => F q.1 (p q.1 + M q.1 q.2)) (Icc a b ×ˢ S))
    (hJ : ContinuousOn (fun q : ℝ × E => J q.1 (p q.1 + M q.1 q.2)) (Icc a b ×ˢ S))
    (hd : ∀ t ∈ Icc a b, ∀ v ∈ S, HasFDerivAt (F t) (J t (p t + M t v)) (p t + M t v))
    (quad : ∀ t ∈ Ioc a b, ∀ v ∈ Metric.closedBall (0 : E) T, ∀ d : E,
      -(L * ‖d‖ ^ 2) ≤
        ⟪d, LogNormTrajectory.MovingFrame.jacobian (J t (p t + M t v)) (M t) (dM t) d⟫)
    (hres : ∀ t ∈ Ioc a b, ‖(M t).symm (F t (p t) - dp t)‖ ≤ ε) :
    ∀ x ∈ ellipsoid (M b) (p b) r, ∃ v : ℝ → E, v b = x ∧
      v a ∈ ellipsoid (M a) (p a) (propagated a b r L ε) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt v (F t (v t)) (Icc a b) t ∧
        v t ∈ ellipsoid (M t) (p t) (propagated a b r L ε) := by
  have rev {u : ℝ} (hu : u ∈ Icc a b) : a + b - u ∈ Icc a b :=
    ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have rev' {u : ℝ} (hu : u ∈ Ico a b) : a + b - u ∈ Ioc a b :=
    ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have crev : ContinuousOn (fun u : ℝ => a + b - u) (Icc a b) :=
    (by fun_prop : Continuous fun u : ℝ => a + b - u).continuousOn
  have prev : ContinuousOn (fun q : ℝ × E => (a + b - q.1, q.2)) (Icc a b ×ˢ S) :=
    (by fun_prop : Continuous fun q : ℝ × E => (a + b - q.1, q.2)).continuousOn
  have pmaps : MapsTo (fun q : ℝ × E => (a + b - q.1, q.2)) (Icc a b ×ˢ S) (Icc a b ×ˢ S) :=
    fun q hq => ⟨rev hq.1, hq.2⟩
  have ea : a + b - a = b := by ring
  have eb : a + b - b = a := by ring
  have step := step_of_defect (F := fun u x => -F (a + b - u) x)
    (J := fun u x => -J (a + b - u) x) (p := fun u => p (a + b - u))
    (dp := fun u => -dp (a + b - u)) (M := fun u => M (a + b - u))
    (dM := fun u => -dM (a + b - u)) hab hr hε hLen hTrial hS hconv hTube hRet
    (fun t ht => hasDerivWithinAt_reverse (hp _ (rev ht)))
    (fun t ht => hasDerivWithinAt_reverse (f := fun u => (M u).toContinuousLinearMap)
      (hM _ (rev ht)))
    (hcInv.comp crev fun _ => rev) (hcdp.comp crev fun _ => rev).neg
    (hcdM.comp crev fun _ => rev).neg (hF.comp prev pmaps).neg (hJ.comp prev pmaps).neg
    (fun t ht v hv => (hd _ (rev ht) v hv).neg)
    (fun t ht v hv d => by
      rw [jacobian_neg, neg_apply, inner_neg_right]
      linarith only [quad _ (rev' ht) v hv d])
    (fun t ht => by
      rw [show ∀ x y : E, -x - -y = -(x - y) from fun x y => by abel, map_neg, norm_neg]
      exact hres _ (rev' ht))
  intro x hx
  obtain ⟨w, start, final, within⟩ := step.solve x (by rwa [ea])
  change w a = x at start
  change w b ∈ ellipsoid (M (a + b - b)) (p (a + b - b)) (propagated a b r L ε) at final
  rw [eb] at final
  refine ⟨fun t => w (a + b - t), by simpa only [eb] using start,
    by simpa only [ea] using final, fun t ht => ?_⟩
  obtain ⟨der, tube⟩ := within _ (rev ht)
  have back : a + b - (a + b - t) = t := by ring
  refine ⟨?_, ?_⟩
  · have h := hasDerivWithinAt_reverse (a := a) (b := b) (t := t) (f := w)
      (f' := -F t (w (a + b - t))) (by
        change HasDerivWithinAt w (-F (a + b - (a + b - t)) (w (a + b - t))) (Icc a b) _ at der
        rwa [back] at der)
    simpa only [neg_neg] using h
  · have h := tube.1
    change w (a + b - t) ∈ ellipsoid (M (a + b - (a + b - t))) (p (a + b - (a + b - t)))
      (propagated a b r L ε) at h
    rwa [back] at h

/-- Two-sided comparison of two solutions in the frame. If both stay in the trial
ellipsoid in the interior of the interval and the quadratic form of the frame Jacobian
lies between `-L‖d‖²` and `L‖d‖²` on the trial ball, the frame separations at the two
ends differ by at most the factor `exp (L (t - s))`. The coefficient may have either
sign. -/
theorem norm_symm_sub_le_exp_mul {F : ℝ → E → E} {J : ℝ → E → E →L[ℝ] E}
    {p : ℝ → E} {M : ℝ → E ≃L[ℝ] E} {dM : ℝ → E →L[ℝ] E} {x₁ x₂ : ℝ → E} {s t L T : ℝ}
    (hst : s ≤ t) (hcp : ContinuousOn p (Icc s t))
    (hM : ∀ τ ∈ Icc s t,
      HasDerivWithinAt (fun u => (M u).toContinuousLinearMap) (dM τ) (Icc s t) τ)
    (hcInv : ContinuousOn (fun τ => (M τ).symm.toContinuousLinearMap) (Icc s t))
    (hd : ∀ τ ∈ Ico s t, ∀ v ∈ Metric.closedBall (0 : E) T,
      HasFDerivAt (F τ) (J τ (p τ + M τ v)) (p τ + M τ v))
    (upper : ∀ τ ∈ Ico s t, ∀ v ∈ Metric.closedBall (0 : E) T, ∀ d : E,
      ⟪d, LogNormTrajectory.MovingFrame.jacobian (J τ (p τ + M τ v)) (M τ) (dM τ) d⟫ ≤
        L * ‖d‖ ^ 2)
    (lower : ∀ τ ∈ Ico s t, ∀ v ∈ Metric.closedBall (0 : E) T, ∀ d : E,
      -(L * ‖d‖ ^ 2) ≤
        ⟪d, LogNormTrajectory.MovingFrame.jacobian (J τ (p τ + M τ v)) (M τ) (dM τ) d⟫)
    (hx₁ : ∀ τ ∈ Icc s t, HasDerivWithinAt x₁ (F τ (x₁ τ)) (Icc s t) τ)
    (hx₂ : ∀ τ ∈ Icc s t, HasDerivWithinAt x₂ (F τ (x₂ τ)) (Icc s t) τ)
    (hm₁ : ∀ τ ∈ Ioo s t, x₁ τ ∈ ellipsoid (M τ) (p τ) T)
    (hm₂ : ∀ τ ∈ Ioo s t, x₂ τ ∈ ellipsoid (M τ) (p τ) T) :
    ‖(M s).symm (x₁ s - x₂ s)‖ ≤ Real.exp (L * (t - s)) * ‖(M t).symm (x₁ t - x₂ t)‖ ∧
    ‖(M t).symm (x₁ t - x₂ t)‖ ≤ Real.exp (L * (t - s)) * ‖(M s).symm (x₁ s - x₂ s)‖ := by
  let G := fun τ => LogNormTrajectory.MovingFrame.field (F τ) 0 0 (M τ) (dM τ)
  let B := fun τ => Metric.closedBall ((M τ).symm (p τ)) T
  have de {x : ℝ → E} (hx : ∀ τ ∈ Icc s t, HasDerivWithinAt x (F τ (x τ)) (Icc s t) τ)
      (τ : ℝ) (hτ : τ ∈ Icc s t) :
      HasDerivWithinAt (fun u => (M u).symm (x u)) (G τ ((M τ).symm (x τ))) (Icc s t) τ := by
    have h := (hasDerivWithinAt_symm (hM τ hτ) (hcInv τ hτ)).clm_apply (hx τ hτ)
    refine h.congr_deriv ?_
    simp only [G, LogNormTrajectory.MovingFrame.field, neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_add, sub_zero, map_sub]
    abel
  have mem {x : ℝ → E} (hx : ∀ τ ∈ Icc s t, HasDerivWithinAt x (F τ (x τ)) (Icc s t) τ)
      (hm : ∀ τ ∈ Ioo s t, x τ ∈ ellipsoid (M τ) (p τ) T) (τ : ℝ) (hτ : τ ∈ Ico s t) :
      (M τ).symm (x τ) ∈ B τ := by
    have hlt : s < t := hτ.1.trans_lt hτ.2
    have cx : ContinuousOn x (Icc s t) := fun u hu => (hx u hu).continuousWithinAt
    have cont : ContinuousOn (fun u => ‖(M u).symm (x u - p u)‖) (Icc s t) :=
      (hcInv.clm_apply (cx.sub hcp)).norm
    have hcl : τ ∈ closure (Ioo s t) := by
      rw [closure_Ioo hlt.ne]
      exact Ico_subset_Icc_self hτ
    have h := ContinuousWithinAt.closure_le hcl
      ((cont τ (Ico_subset_Icc_self hτ)).mono Ioo_subset_Icc_self)
      continuousWithinAt_const hm
    rw [Metric.mem_closedBall, dist_eq_norm, ← map_sub]
    exact h
  have hv (τ : ℝ) (z : E) (hz : z ∈ B τ) :
      z - (M τ).symm (p τ) ∈ Metric.closedBall (0 : E) T := by
    rw [mem_closedBall_zero_iff, ← dist_eq_norm]
    exact hz
  have dg (τ : ℝ) (hτ : τ ∈ Ico s t) (z : E) (hz : z ∈ B τ) :
      HasFDerivAt (G τ) (LogNormTrajectory.MovingFrame.jacobian
        (J τ (p τ + M τ (z - (M τ).symm (p τ)))) (M τ) (dM τ)) z := by
    have key : ∀ q, q = 0 + M τ z → ∀ J', HasFDerivAt (F τ) J' q →
        HasFDerivAt (G τ) (LogNormTrajectory.MovingFrame.jacobian J' (M τ) (dM τ)) z := by
      rintro _ rfl J' h
      exact LogNormTrajectory.MovingFrame.hasFDerivAt_field h
    exact key _ (by simp) _ (hd τ hτ _ (hv τ z hz))
  have hU (τ : ℝ) (hτ : τ ∈ Ico s t) : LogNormTrajectory.OneSidedOn (G τ) (B τ) L :=
    LogNormTrajectory.oneSidedOn_of_jacobian (convex_closedBall _ _) (dg τ hτ)
      fun z hz d => upper τ hτ _ (hv τ z hz) d
  have hLo (τ : ℝ) (hτ : τ ∈ Ico s t) : BackwardDistance.LowerOneSidedOn (G τ) (B τ) L :=
    BackwardDistance.lowerOneSidedOn_of_jacobian (convex_closedBall _ _) (dg τ hτ)
      fun z hz d => by simpa only [neg_mul] using lower τ hτ _ (hv τ z hz) d
  have cont {x : ℝ → E} (hx : ∀ τ ∈ Icc s t, HasDerivWithinAt x (F τ (x τ)) (Icc s t) τ) :
      ContinuousOn (fun u => (M u).symm (x u)) (Icc s t) :=
    fun τ hτ => (de hx τ hτ).continuousWithinAt
  have right {x : ℝ → E} (hx : ∀ τ ∈ Icc s t, HasDerivWithinAt x (F τ (x τ)) (Icc s t) τ)
      (τ : ℝ) (hτ : τ ∈ Ico s t) :
      HasDerivWithinAt (fun u => (M u).symm (x u)) (G τ ((M τ).symm (x τ))) (Ici τ) τ :=
    (de hx τ (Ico_subset_Icc_self hτ)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ)
  have diff (u : ℝ) : (M u).symm (x₁ u) - (M u).symm (x₂ u) = (M u).symm (x₁ u - x₂ u) :=
    (map_sub _ _ _).symm
  have back := BackwardDistance.norm_sub_le_exp_mul_of_lower (F := G) (s := B) hLo
    (cont hx₁) (cont hx₂) (right hx₁) (right hx₂) (mem hx₁ hm₁) (mem hx₂ hm₂) t
    (right_mem_Icc.mpr hst)
  have fwd := LogNormTrajectory.dist_le_of_residual (F := G) (s := B)
    (dy := fun τ => G τ ((M τ).symm (x₂ τ))) (ε := 0) (r := ‖(M s).symm (x₁ s - x₂ s)‖) hU
    (cont hx₁) (cont hx₂) (right hx₁) (right hx₂) (fun _ _ => by simp) (mem hx₁ hm₁)
    (mem hx₂ hm₂) (by rw [dist_eq_norm, diff]) t (right_mem_Icc.mpr hst)
  rw [gronwallBound_ε0, dist_eq_norm, mul_comm] at fwd
  simp only [diff] at back fwd
  exact ⟨back, fwd⟩

end Hilbert
end PlasmaLean.Fields.TrajectorySlabs.MovingFrame
