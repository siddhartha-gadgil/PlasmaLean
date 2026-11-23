/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.LogNormTrajectory

/-!
# A posteriori trajectory enclosures in a moving linear frame

On one time slab the physical point is `p(t) + M(t)v(t)`. The invertible frame changes
the defect to `M⁻¹(F(t,p)-p')` and the spatial Jacobian to `M⁻¹(JM-M')`. A signed
logarithmic-norm test on the latter gives a certified error in frame coordinates and
an enclosure in physical coordinates. The reference and frame may be chosen anew
at the next slab.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Fields.LogNormTrajectory.MovingFrame

open Set
open scoped RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The deviation velocity in the coordinates `x = p + M v`. -/
def field (F : E → E) (p dp : E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) (v : E) : E :=
  M.symm (F (p + M v) - dp - dM v)

/-- The conjugated spatial Jacobian includes the derivative of the frame. -/
def jacobian (J : E →L[ℝ] E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) : E →L[ℝ] E :=
  M.symm.toContinuousLinearMap.comp (J.comp M.toContinuousLinearMap - dM)

/-- At the origin of the frame the sole forcing is the transformed reference defect. -/
theorem field_zero (F : E → E) (p dp : E) (M : E ≃L[ℝ] E) (dM : E →L[ℝ] E) :
    field F p dp M dM 0 = M.symm (F p - dp) := by simp [field]

/-- Interpolating the two matrices on a slab gives the constant frame derivative used
by the enclosure. Invertibility throughout the slab is a separate condition. -/
theorem hasDerivAt_affine_frame (P Q : E →L[ℝ] E) (a b t : ℝ) :
    HasDerivAt (fun s => P + ((s - a) / (b - a)) • (Q - P)) ((b - a)⁻¹ • (Q - P)) t := by
  simpa using ((((hasDerivAt_id t).sub_const a).div_const (b - a)).smul_const (Q - P)).const_add P

/-- A spatial Jacobian at the physical point yields the frame Jacobian at the deviation. -/
theorem hasFDerivAt_field {F : E → E} {p dp v : E} {M : E ≃L[ℝ] E} {dM J : E →L[ℝ] E}
    (hd : HasFDerivAt F J (p + M v)) :
    HasFDerivAt (field F p dp M dM) (jacobian J M dM) v := by
  have h := ((hd.comp v (M.toContinuousLinearMap.hasFDerivAt.const_add p)).sub_const dp).sub
    dM.hasFDerivAt
  exact M.symm.toContinuousLinearMap.hasFDerivAt.comp v h

/-- Reconstruct a physical solution from the deviation equation. Derivatives are taken
within the slab so this applies at either endpoint of a piecewise differentiable frame. -/
theorem hasDerivWithinAt_reconstruct {F : ℝ → E → E} {p dp v : ℝ → E}
    {M : ℝ → E ≃L[ℝ] E} {dM : ℝ → E →L[ℝ] E} {s : Set ℝ} {t : ℝ}
    (hp : HasDerivWithinAt p (dp t) s t)
    (hM : HasDerivWithinAt (fun u => (M u).toContinuousLinearMap) (dM t) s t)
    (hv : HasDerivWithinAt v (field (F t) (p t) (dp t) (M t) (dM t) (v t)) s t) :
    HasDerivWithinAt (fun u => p u + M u (v u)) (F t (p t + M t (v t))) s t := by
  apply (hp.fun_add (hM.clm_apply hv)).congr_deriv
  change dp t + (dM t (v t) + M t ((M t).symm _)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  abel

/-- A jump of the polynomial reference at a common frame is measured after applying its
inverse. This is the incoming-radius update for adjacent slabs. -/
theorem radius_after_reference_jump (M : E ≃L[ℝ] E) (x old next : E) :
    ‖M.symm (x - next)‖ ≤ ‖M.symm (x - old)‖ + ‖M.symm (old - next)‖ := by
  calc
    _ = ‖M.symm (x - old) + M.symm (old - next)‖ := by
      rw [← map_add, sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _

/-- A variational frame removes the complete homogeneous linear drift. If the
reference is exact, the transformed error is constant even for an expanding field. -/
theorem homogeneous_linear_cancellation (J : E →L[ℝ] E) (p : E) (M : E ≃L[ℝ] E) :
    (∀ v, field J p (J p) M (J.comp M.toContinuousLinearMap) v = 0) ∧
      jacobian J M (J.comp M.toContinuousLinearMap) = 0 := by
  constructor
  · intro v
    simp [field, map_add]
  · simp [jacobian]

/-- The nonconstant shear `(x,y) ↦ (x,y+t*x)` exactly transports the errors of
`x'=0, y'=x`. Its frame velocity vanishes at every phase and for every deviation. -/
theorem exact_shear (t : ℝ) (p v : ℝ × ℝ) :
    let I := ContinuousLinearEquiv.refl ℝ ℝ
    let M := I.skewProd I (t • ContinuousLinearMap.id ℝ ℝ)
    let J := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
    field J p (J p) M J v = 0 ∧ jacobian J M J = 0 := by
  dsimp only
  let I := ContinuousLinearEquiv.refl ℝ ℝ
  let M := I.skewProd I (t • ContinuousLinearMap.id ℝ ℝ)
  let J := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have he : J.comp M.toContinuousLinearMap = J := by
    ext <;> simp [J, M, I, ContinuousLinearEquiv.skewProd_apply]
  have h := homogeneous_linear_cancellation J p M
  rw [he] at h
  exact ⟨h.1 v, h.2⟩

/-- In the shear fixture the proposed frame derivative is the derivative in operator
norm. Together with `exact_shear` this checks the time-dependent cancellation. -/
theorem hasDerivAt_shear_frame (t : ℝ) :
    let I := ContinuousLinearEquiv.refl ℝ ℝ
    let J := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
    HasDerivAt (fun s : ℝ => (I.skewProd I (s • ContinuousLinearMap.id ℝ ℝ)).toContinuousLinearMap)
      J t := by
  dsimp only
  let J := (0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let I := ContinuousLinearEquiv.refl ℝ ℝ
  have he (s : ℝ) : (I.skewProd I (s • ContinuousLinearMap.id ℝ ℝ)).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) + s • J := by
    ext <;> simp [I, J, ContinuousLinearEquiv.skewProd_apply]
  change HasDerivAt
    (fun s : ℝ => (I.skewProd I (s • ContinuousLinearMap.id ℝ ℝ)).toContinuousLinearMap) J t
  simp_rw [he]
  simpa using ((hasDerivAt_id t).smul_const J).const_add (ContinuousLinearMap.id ℝ (ℝ × ℝ))

end Normed

section Hilbert

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An invertible moving frame gives a full physical solution on the slab. The Jacobian
bound is tested on the frame trial ball. The data for ordinary local existence are needed
only on its containing compact convex box. Both the frame radius and the physical
radius, scaled by the operator norm of the instantaneous frame, hold at every time. -/
theorem exists_rational_step {F : ℝ → E → E} {J : ℝ → E → E →L[ℝ] E}
    {p dp : ℝ → E} {M : ℝ → E ≃L[ℝ] E} {dM : ℝ → E →L[ℝ] E} {S : Set E}
    {a b r L ε T : ℝ} {x₀ : E} (hab : a ≤ b) (hr : 0 ≤ r) (hε : 0 ≤ ε)
    (hLen : max 0 L * (b - a) < 1) (hs : (r + (b - a) * ε) / (1 - max 0 L * (b - a)) < T)
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
    (quad : ∀ t ∈ Ico a b, ∀ v ∈ Metric.closedBall (0 : E) T, ∀ d : E,
      ⟪d, jacobian (J t (p t + M t v)) (M t) (dM t) d⟫ ≤ L * ‖d‖ ^ 2)
    (hres : ∀ t ∈ Ico a b, ‖(M t).symm (F t (p t) - dp t)‖ ≤ ε)
    (ha : ‖(M a).symm (x₀ - p a)‖ ≤ r) :
    ∃ x : ℝ → E, x a = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (F t (x t)) (Icc a b) t ∧
      ‖(M t).symm (x t - p t)‖ ≤ (r + (b - a) * ε) / (1 - max 0 L * (b - a)) ∧
      dist (x t) (p t) ≤ ‖(M t).toContinuousLinearMap‖ *
        ((r + (b - a) * ε) / (1 - max 0 L * (b - a))) := by
  let G := fun t => field (F t) (p t) (dp t) (M t) (dM t)
  let D := fun t v => jacobian (J t (p t + M t v)) (M t) (dM t)
  have pull {V : Type u} [TopologicalSpace V] {f : ℝ → V} (hc : ContinuousOn f (Icc a b)) :
      ContinuousOn (fun q : ℝ × E => f q.1) (Icc a b ×ˢ S) :=
    hc.comp continuous_fst.continuousOn (fun _ h => h.1)
  have cm : ContinuousOn (fun t => (M t).toContinuousLinearMap) (Icc a b) := fun t ht =>
    (hM t ht).continuousWithinAt
  have cg : ContinuousOn (fun q : ℝ × E => G q.1 q.2) (Icc a b ×ˢ S) :=
    (pull hcInv).clm_apply
      ((hF.sub (pull hcdp)).sub ((pull hcdM).clm_apply continuous_snd.continuousOn))
  have cd : ContinuousOn (fun q : ℝ × E => D q.1 q.2) (Icc a b ×ˢ S) :=
    (pull hcInv).clm_comp ((hJ.clm_comp (pull cm)).sub (pull hcdM))
  have dg (t : ℝ) (ht : t ∈ Icc a b) (v : E) (hv : v ∈ S) :
      HasFDerivAt (G t) (D t v) v := hasFDerivAt_field (hd t ht v hv)
  obtain ⟨K, C, lip, tm, vel⟩ := picard_bounds_of_compact hS hconv cg cd
    fun t ht v hv => (dg t ht v hv).hasFDerivWithinAt
  have hL (t : ℝ) (ht : t ∈ Ico a b) : OneSidedOn (G t) (Metric.closedBall 0 T) L :=
    oneSidedOn_of_jacobian (convex_closedBall _ _)
      (fun v hv => dg t (Ico_subset_Icc_self ht) v (hTube hv)) (quad t ht)
  obtain ⟨v, hv₀, hv⟩ := exists_rational_step_of_retraction (F := G)
    (y := fun _ => 0) (dy := fun _ => 0) (x₀ := (M a).symm (x₀ - p a)) hab hr hε hLen hs
    hRet lip tm vel (fun _ _ => hTube) hL continuousOn_const
    (fun _ _ => (hasDerivAt_const _ _).hasDerivWithinAt)
    (fun t ht => by simpa [G, field_zero] using hres t ht) (by simpa using ha)
  refine ⟨fun t => p t + M t (v t), by simp [hv₀], ?_⟩
  intro t ht
  obtain ⟨hv', hvR⟩ := hv t ht
  rw [dist_zero_right] at hvR
  refine ⟨hasDerivWithinAt_reconstruct (hp t ht) (hM t ht) hv', by simpa using hvR, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left]
  exact ((M t).toContinuousLinearMap.le_opNorm (v t)).trans
    (mul_le_mul_of_nonneg_left hvR (norm_nonneg _))

end Hilbert

end PlasmaLean.Fields.LogNormTrajectory.MovingFrame
