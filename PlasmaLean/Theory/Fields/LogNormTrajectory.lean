/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Tactic

/-!
# Reference-trajectory enclosures from a one-sided Lipschitz bound

A bound on the quadratic form of the spatial Jacobian on each convex time slice
controls the amplification of trajectory errors in the real Hilbert norm. The
coefficient can be negative. A bounded reference residual contributes the
inhomogeneous term in Mathlib's scalar Grönwall estimate.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Fields.LogNormTrajectory

open Set Filter Real
open scoped Topology RealInnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Signed one-sided Lipschitz coefficient on a spatial slice. -/
def OneSidedOn (F : E → E) (s : Set E) (L : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ⟪x - y, F x - F y⟫ ≤ L * ‖x - y‖ ^ 2

/-- A pointwise upper bound for the Jacobian quadratic form gives the signed
one-sided Lipschitz inequality on the whole convex slice. -/
theorem oneSidedOn_of_jacobian {F : E → E} {J : E → E →L[ℝ] E} {s : Set E} {L : ℝ}
    (hs : Convex ℝ s) (hF : ∀ z ∈ s, HasFDerivAt F (J z) z)
    (hJ : ∀ z ∈ s, ∀ d : E, ⟪d, J z d⟫ ≤ L * ‖d‖ ^ 2) : OneSidedOn F s L := by
  intro x hx y hy
  let d := x - y
  let c := fun t : ℝ => y + t • d
  have hd (t : ℝ) : HasDerivAt c d t := by
    simpa [c] using ((hasDerivAt_id t).smul_const d).const_add y
  have hc (t : ℝ) (ht : t ∈ Icc 0 1) : c t ∈ s := hs.add_smul_sub_mem hy hx ht
  have hg (t : ℝ) (ht : t ∈ Icc 0 1) :
      HasDerivAt (fun t => ⟪d, F (c t)⟫) ⟪d, J (c t) d⟫ t := by
    simpa using (hasDerivAt_const t d).inner ℝ ((hF _ (hc t ht)).comp_hasDerivAt t (hd t))
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (fun t => ⟪d, F (c t)⟫)
    (fun t => ⟪d, J (c t) d⟫) zero_lt_one (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hg t (Ioo_subset_Icc_self ht))
  have hb := hJ _ (hc t (Ioo_subset_Icc_self ht)) d
  rw [he] at hb
  simpa [c, d, inner_sub_right] using hb

/-- A posteriori distance from an exact trajectory to a differentiable reference
path on a time-dependent tube. The coefficient L may have either sign or vanish. -/
theorem dist_le_of_residual {F : ℝ → E → E} {s : ℝ → Set E} {x y dy : ℝ → E}
    {a b r L ε : ℝ} (hL : ∀ t ∈ Ico a b, OneSidedOn (F t) (s t) L)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (dy t) (Ici t) t)
    (hres : ∀ t ∈ Ico a b, ‖F t (y t) - dy t‖ ≤ ε)
    (hxs : ∀ t ∈ Ico a b, x t ∈ s t) (hys : ∀ t ∈ Ico a b, y t ∈ s t)
    (ha : dist (x a) (y a) ≤ r) :
    ∀ t ∈ Icc a b, dist (x t) (y t) ≤ gronwallBound r L ε (t - a) := by
  let e := fun t => x t - y t
  let de := fun t => F t (x t) - dy t
  have hd (t : ℝ) (ht : t ∈ Ico a b) : HasDerivWithinAt e (de t) (Ici t) t :=
    (hxd t ht).sub (hyd t ht)
  have hb (t : ℝ) (ht : t ∈ Ico a b) :
      ⟪e t, de t⟫ ≤ L * ‖e t‖ ^ 2 + ‖e t‖ * ε := by
    have hc := hL t ht (x t) (hxs t ht) (y t) (hys t ht)
    have hcs := (real_inner_le_norm (e t) (F t (y t) - dy t)).trans
      (mul_le_mul_of_nonneg_left (hres t ht) (norm_nonneg _))
    rw [show de t = (F t (x t) - F t (y t)) + (F t (y t) - dy t) by unfold de; abel,
      inner_add_right]
    exact add_le_add hc hcs
  simp only [dist_eq_norm] at ha ⊢
  apply le_gronwallBound_of_liminf_deriv_right_le
    (f' := fun t => L * ‖e t‖ + ε) ((hx.sub hy).norm) _ ha (fun _ _ => le_rfl)
  intro t ht q hq
  by_cases h0 : e t = 0
  · have heq : x t = y t := sub_eq_zero.mp h0
    have hεq : ε < q := by simpa [h0] using hq
    have hq' : ‖de t‖ < q := by
      simpa [de, heq] using (hres t ht).trans_lt hεq
    exact (hd _ ht).liminf_right_slope_norm_le hq'
  · have hp : 0 < ‖e t‖ := norm_pos_iff.mpr h0
    have hsq := (hd _ ht).norm_sq.sqrt (by positivity)
    simp only [Real.sqrt_sq (norm_nonneg _)] at hsq
    have hd' : HasDerivWithinAt (fun t => ‖e t‖) (⟪e t, de t⟫ / ‖e t‖) (Ici t) t := by
      convert hsq using 1
      field_simp
    have hq' : ⟪e t, de t⟫ / ‖e t‖ < q := by
      apply lt_of_le_of_lt _ hq
      apply (div_le_iff₀ hp).mpr
      nlinarith only [hb t ht]
    simpa [slope_def_module] using hd'.liminf_right_slope_le hq'

/-- A rational upper bound for a step of length h when K ≥ 0 and Kh < 1. -/
theorem gronwallBound_le_rational {r K ε h : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hKh : K * h < 1) : gronwallBound r K ε h ≤ (r + h * ε) / (1 - K * h) := by
  rcases hK.eq_or_lt with he | hp
  · subst K
    simp [gronwallBound_K0, mul_comm]
  have hExp : exp (K * h) * (1 - K * h) ≤ 1 := by
    have hc := Real.add_one_le_exp (-(K * h))
    rw [Real.exp_neg] at hc
    calc
      exp (K * h) * (1 - K * h) ≤ exp (K * h) * (exp (K * h))⁻¹ := by gcongr; linarith only [hc]
      _ = 1 := mul_inv_cancel₀ (Real.exp_ne_zero _)
  apply (le_div_iff₀ (sub_pos.mpr hKh)).mpr
  rw [gronwallBound_of_K_ne_0 hp.ne']
  have h₁ := mul_le_mul_of_nonneg_left hExp hr
  have h₂ := mul_le_mul_of_nonneg_left hExp (div_nonneg hε hp.le)
  have he : ε / K * K = ε := div_mul_cancel₀ ε hp.ne'
  linear_combination h₁ + h₂ + h * he

/-- A strict trial radius removes the a priori assumption that the exact path
stays inside the tube. Only ODE information up to a possible first exit is used. -/
theorem le_of_prefix_bound {f : ℝ → ℝ} {a b R T : ℝ} (hc : ContinuousOn f (Icc a b))
    (hs : R < T) (hp : ∀ t ∈ Icc a b, (∀ u ∈ Ico a t, f u < T) → f t ≤ R) :
    ∀ t ∈ Icc a b, f t ≤ R := by
  have hwhole : ∀ t ∈ Icc a b, f t < T := by
    by_contra! hbad
    obtain ⟨t, ht, hft⟩ := hbad
    have hk := hc.upperSemicontinuousOn.isCompact_inter_preimage_Ici isCompact_Icc T
    obtain ⟨q, hq, hmin⟩ := hk.exists_isMinOn ⟨t, ht, hft⟩ continuousOn_id
    have hpre (u : ℝ) (hu : u ∈ Ico a q) : f u < T := by
      by_contra! hfu
      exact (not_le.mpr hu.2) (hmin (show u ∈ Icc a b ∩ f ⁻¹' Ici T from
        ⟨⟨hu.1, hu.2.le.trans hq.1.2⟩, hfu⟩))
    exact (not_le.mpr ((hp q hq.1 hpre).trans_lt hs)) hq.2
  exact fun t ht => hp t ht fun u hu => hwhole u ⟨hu.1, hu.2.le.trans ht.2⟩

/-- One numerical step with a uniform Euclidean residual bound and a signed
one-sided Lipschitz bound on the moving trial tube. The rational bound holds
throughout the step, including its endpoint. The path x need only satisfy the
equation while inside the trial tube. -/
theorem dist_le_rational_step {F : ℝ → E → E} {x y dy : ℝ → E} {a b r L ε T : ℝ}
    (hr : 0 ≤ r) (hε : 0 ≤ ε) (hLen : max 0 L * (b - a) < 1)
    (hs : (r + (b - a) * ε) / (1 - max 0 L * (b - a)) < T)
    (hL : ∀ t ∈ Ico a b, OneSidedOn (F t) (Metric.closedBall (y t) T) L)
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hxd : ∀ t ∈ Ico a b, dist (x t) (y t) < T →
      HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (dy t) (Ici t) t)
    (hres : ∀ t ∈ Ico a b, ‖F t (y t) - dy t‖ ≤ ε)
    (ha : dist (x a) (y a) ≤ r) :
    ∀ t ∈ Icc a b, dist (x t) (y t) ≤ (r + (b - a) * ε) / (1 - max 0 L * (b - a)) := by
  let K := max 0 L
  have hK : 0 ≤ K := le_max_left _ _
  have hc : ContinuousOn (fun t => dist (x t) (y t)) (Icc a b) := by
    simpa only [dist_eq_norm] using (hx.fun_sub hy).norm
  apply le_of_prefix_bound hc hs
  intro t ht hpre
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
  have hsub' : Ico a t ⊆ Ico a b := Ico_subset_Ico_right ht.2
  have hs' : 0 ≤ T := le_of_lt <| lt_of_le_of_lt (by
    exact div_nonneg (add_nonneg hr (mul_nonneg (sub_nonneg.mpr (ht.1.trans ht.2)) hε))
      (sub_pos.mpr hLen).le) hs
  have h := dist_le_of_residual (s := fun u => Metric.closedBall (y u) T) (L := K)
    (fun u hu x' hx' y' hy' => (hL u (hsub' hu) x' hx' y' hy').trans
      (mul_le_mul_of_nonneg_right (le_max_right 0 L) (sq_nonneg _)))
    (hx.mono hsub) (hy.mono hsub) (fun u hu => hxd u (hsub' hu) (hpre _ hu))
    (fun u hu => hyd u (hsub' hu)) (fun u hu => hres u (hsub' hu))
    (fun u hu => (hpre u hu).le) (fun u _ => Metric.mem_closedBall_self hs') ha
    t (Set.right_mem_Icc.mpr ht.1)
  exact (h.trans (gronwallBound_mono hr hε hK (sub_le_sub_right ht.2 a))).trans
    (gronwallBound_le_rational hr hK hε hLen)

/-- In two Cartesian coordinates, enclosure of the symmetric Jacobian diagonal
and off-diagonal row sum bounds its quadratic form in the Euclidean norm. -/
theorem quadraticForm_le_of_two_rows {J : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)}
    {a b c d L : ℝ} (hJ : ∀ w : EuclideanSpace ℝ (Fin 2),
      (J w) 0 = a * w 0 + b * w 1 ∧ (J w) 1 = c * w 0 + d * w 1)
    (hL : max a d + |(b + c) / 2| ≤ L) (w : EuclideanSpace ℝ (Fin 2)) :
    ⟪w, J w⟫ ≤ L * ‖w‖ ^ 2 := by
  let u := w 0
  let v := w 1
  let k := (b + c) / 2
  have hu := (le_max_left a d).trans (show max a d ≤ L - |k| by linarith only [hL])
  have hv := (le_max_right a d).trans (show max a d ≤ L - |k| by linarith only [hL])
  have hm : 2 * k * u * v ≤ |k| * (u ^ 2 + v ^ 2) := by
    rcases le_total 0 k with hp | hn
    · rw [abs_of_nonneg hp]; nlinarith only [mul_nonneg hp (sq_nonneg (u - v))]
    · rw [abs_of_nonpos hn]; nlinarith only [mul_nonneg (neg_nonneg.mpr hn) (sq_nonneg (u + v))]
  rw [PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [RCLike.inner_apply, conj_trivial, (hJ w).1, (hJ w).2]
  change (a * u + b * v) * u + (c * u + d * v) * v ≤ L * (u ^ 2 + v ^ 2)
  have he : 2 * k = b + c := by dsimp [k]; ring
  nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg u),
    mul_le_mul_of_nonneg_right hv (sq_nonneg v), hm, congrArg (fun q => q * u * v) he]

/-- A nonexpansive retraction onto any finite Cartesian box in the Euclidean norm. -/
theorem euclideanBox_retraction {ι : Type*} [Fintype ι] {lo hi : ι → ℝ} (hbox : lo ≤ hi) :
    let s := {x : EuclideanSpace ℝ ι | ∀ i, x i ∈ Icc (lo i) (hi i)}
    ∃ P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
      LipschitzWith 1 P ∧ (∀ x, P x ∈ s) ∧ ∀ x ∈ s, P x = x := by
  let P := fun x : EuclideanSpace ℝ ι => WithLp.toLp 2 (fun i => max (lo i) (min (x i) (hi i)))
  refine ⟨P, ?_, ?_, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have h := ((LipschitzWith.id.min_const (hi i)).const_max (lo i)).dist_le_mul (x i) (y i)
    have hab : |(P x) i - (P y) i| ≤ |x i - y i| := by simpa [P, Real.dist_eq] using h
    simpa only [sq_abs, PiLp.sub_apply] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hab
  · exact fun x i => ⟨le_max_left _ _, max_le (hbox i) (min_le_right _ _)⟩
  · intro x hx
    ext i
    exact (max_eq_right ((hx i).1.trans_eq (min_eq_left (hx i).2).symm)).trans
      (min_eq_left (hx i).2)

/-- Continuity of the field and spatial Jacobian on a compact space-time box
supplies the ordinary speed and Lipschitz bounds needed only for existence. -/
theorem picard_bounds_of_compact {F : ℝ → E → E} {J : ℝ → E → E →L[ℝ] E}
    {a b : ℝ} {S : Set E} (hS : IsCompact S) (hc : Convex ℝ S)
    (hF : ContinuousOn (fun p : ℝ × E => F p.1 p.2) (Icc a b ×ˢ S))
    (hJ : ContinuousOn (fun p : ℝ × E => J p.1 p.2) (Icc a b ×ˢ S))
    (hd : ∀ t ∈ Icc a b, ∀ x ∈ S, HasFDerivWithinAt (F t) (J t x) S x) :
    ∃ K M : ℝ≥0, (∀ t ∈ Icc a b, LipschitzOnWith K (F t) S) ∧
      (∀ x ∈ S, ContinuousOn (fun t => F t x) (Icc a b)) ∧
      (∀ t ∈ Icc a b, ∀ x ∈ S, ‖F t x‖ ≤ M) := by
  have hcomp := (isCompact_Icc (a := a) (b := b)).prod hS
  obtain ⟨k, hk⟩ := hcomp.exists_bound_of_continuousOn hJ
  obtain ⟨m, hm⟩ := hcomp.exists_bound_of_continuousOn hF
  refine ⟨⟨max k 0, le_max_right _ _⟩, ⟨max m 0, le_max_right _ _⟩, ?_, ?_, ?_⟩
  · intro t ht
    apply hc.lipschitzOnWith_of_nnNorm_hasFDerivWithin_le (hd t ht)
    intro x hx
    exact (hk (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · intro x hx
    exact hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, hx⟩)
  · exact fun t ht x hx => (hm (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)

/-- Existence through a validated step. The entire moving trial tube fits in
a fixed set with a nonexpansive retraction. On that set the field has a uniform
ordinary Lipschitz constant and speed bound and is time-continuous. These bounds
give existence by Picard–Lindelöf. The signed coefficient is required only on
the moving trial ball and determines the error radius. Cartesian enclosures
may use `euclideanBox_retraction`. -/
theorem exists_rational_step_of_retraction [CompleteSpace E] {F : ℝ → E → E}
    {y dy : ℝ → E} {a b r L ε T : ℝ} {x₀ : E} {S : Set E} {K M : ℝ≥0}
    (hab : a ≤ b) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hLen : max 0 L * (b - a) < 1)
    (hs : (r + (b - a) * ε) / (1 - max 0 L * (b - a)) < T)
    (hRet : ∃ P : E → E, LipschitzWith 1 P ∧ (∀ x, P x ∈ S) ∧ ∀ x ∈ S, P x = x)
    (hLip : ∀ t ∈ Icc a b, LipschitzOnWith K (F t) S)
    (hCont : ∀ x ∈ S, ContinuousOn (fun t => F t x) (Icc a b))
    (hVel : ∀ t ∈ Icc a b, ∀ x ∈ S, ‖F t x‖ ≤ M)
    (hTube : ∀ t ∈ Icc a b, Metric.closedBall (y t) T ⊆ S)
    (hL : ∀ t ∈ Ico a b, OneSidedOn (F t) (Metric.closedBall (y t) T) L)
    (hy : ContinuousOn y (Icc a b)) (hyd : ∀ t ∈ Ico a b, HasDerivWithinAt y (dy t) (Ici t) t)
    (hres : ∀ t ∈ Ico a b, ‖F t (y t) - dy t‖ ≤ ε) (ha : dist x₀ (y a) ≤ r) :
    ∃ x : ℝ → E, x a = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (F t (x t)) (Icc a b) t ∧
      dist (x t) (y t) ≤ (r + (b - a) * ε) / (1 - max 0 L * (b - a)) := by
  obtain ⟨P, hP, hPS, hfix⟩ := hRet
  let G := fun t x => F t (P x)
  have pl : IsPicardLindelof G (tmin := a) (tmax := b) ⟨a, left_mem_Icc.mpr hab⟩ x₀
      ⟨M * (b - a), mul_nonneg M.2 (sub_nonneg.mpr hab)⟩ 0 M K := by
    constructor
    · intro t ht
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      intro x _ y _
      exact ((hLip t ht).dist_le_mul _ (hPS _) _ (hPS _)).trans
        (mul_le_mul_of_nonneg_left (by simpa using hP.dist_le_mul x y) K.2)
    · exact fun x _ => hCont _ (hPS x)
    · exact fun t ht x _ => hVel t ht _ (hPS x)
    · change M * max (b - a) (a - a) ≤ M * (b - a) - 0
      simp [max_eq_left (sub_nonneg.mpr hab)]
  obtain ⟨x, h₀, hd⟩ := pl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hG (t : ℝ) (ht : t ∈ Icc a b) (hu : dist (x t) (y t) < T) :
      HasDerivWithinAt x (F t (x t)) (Icc a b) t := by
    have h := hd t ht
    change HasDerivWithinAt x (F t (P (x t))) (Icc a b) t at h
    rwa [hfix _ (hTube t ht hu.le)] at h
  have hdist := dist_le_rational_step hr hε hLen hs hL
    (fun t ht => (hd t ht).continuousWithinAt) hy
    (fun t ht h => (hG t (Ico_subset_Icc_self ht) h).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))) hyd hres
    (show dist (x a) (y a) ≤ r by simpa [h₀] using ha)
  exact ⟨x, h₀, fun t ht => ⟨hG t ht ((hdist t ht).trans_lt hs), hdist t ht⟩⟩

/-- Existence and uniform error control on a box moving with the reference path.
At time t the field and its spatial Jacobian need regularity only on y(t) + S,
where S is a fixed compact convex box of deviations. The signed one-sided
bound is needed only on the Euclidean trial ball inside that translated box. -/
theorem exists_rational_step_centered [CompleteSpace E] {F : ℝ → E → E}
    {J : ℝ → E → E →L[ℝ] E} {y dy : ℝ → E} {a b r L ε T : ℝ} {x₀ : E} {S : Set E}
    (hab : a ≤ b) (hr : 0 ≤ r) (hε : 0 ≤ ε) (hLen : max 0 L * (b - a) < 1)
    (hs : (r + (b - a) * ε) / (1 - max 0 L * (b - a)) < T)
    (hS : IsCompact S) (hconv : Convex ℝ S) (hTube : Metric.closedBall (0 : E) T ⊆ S)
    (hRet : ∃ P : E → E, LipschitzWith 1 P ∧ (∀ e, P e ∈ S) ∧ ∀ e ∈ S, P e = e)
    (hF : ContinuousOn (fun p : ℝ × E => F p.1 (y p.1 + p.2)) (Icc a b ×ˢ S))
    (hJ : ContinuousOn (fun p : ℝ × E => J p.1 (y p.1 + p.2)) (Icc a b ×ˢ S))
    (hd : ∀ t ∈ Icc a b, ∀ e ∈ S, HasFDerivAt (F t) (J t (y t + e)) (y t + e))
    (hL : ∀ t ∈ Ico a b, OneSidedOn (F t) (Metric.closedBall (y t) T) L)
    (hyd : ∀ t ∈ Icc a b, HasDerivWithinAt y (dy t) (Icc a b) t)
    (hdy : ContinuousOn dy (Icc a b)) (hres : ∀ t ∈ Ico a b, ‖F t (y t) - dy t‖ ≤ ε)
    (ha : dist x₀ (y a) ≤ r) :
    ∃ x : ℝ → E, x a = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (F t (x t)) (Icc a b) t ∧
      dist (x t) (y t) ≤ (r + (b - a) * ε) / (1 - max 0 L * (b - a)) := by
  let G := fun t e => F t (y t + e) - dy t
  have hcG : ContinuousOn (fun p : ℝ × E => G p.1 p.2) (Icc a b ×ˢ S) :=
    hF.fun_sub (hdy.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  have hdG (t : ℝ) (ht : t ∈ Icc a b) (e : E) (he : e ∈ S) :
      HasFDerivWithinAt (G t) (J t (y t + e)) S e := by
    have htrans := ((hd t ht e he).comp e ((hasFDerivAt_id e).const_add (y t))).sub_const (dy t)
    simpa [G, Function.comp_def] using htrans.hasFDerivWithinAt (s := S)
  obtain ⟨K, M, hLip, hCont, hVel⟩ := picard_bounds_of_compact hS hconv hcG hJ hdG
  have hLG (t : ℝ) (ht : t ∈ Ico a b) : OneSidedOn (G t) (Metric.closedBall 0 T) L := by
    intro e he f hf
    have htube (z : E) (hz : z ∈ Metric.closedBall 0 T) : y t + z ∈ Metric.closedBall (y t) T := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
    have h := hL t ht _ (htube e he) _ (htube f hf)
    simpa only [G, add_sub_add_left_eq_sub, sub_sub_sub_cancel_right] using h
  obtain ⟨e, he₀, he⟩ := exists_rational_step_of_retraction (F := G) (y := fun _ => 0)
    (dy := fun _ => 0) (x₀ := x₀ - y a) hab hr hε hLen hs hRet hLip hCont hVel
    (fun _ _ => hTube) hLG continuousOn_const (fun _ _ => (hasDerivAt_const _ _).hasDerivWithinAt)
    (fun t ht => by simpa [G] using hres t ht) (by simpa only [dist_eq_norm, sub_zero] using ha)
  refine ⟨fun t => y t + e t, by simp [he₀], ?_⟩
  intro t ht
  obtain ⟨heq, heR⟩ := he t ht
  refine ⟨?_, ?_⟩
  · simpa [G] using (hyd t ht).fun_add heq
  · simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using heR

end PlasmaLean.Fields.LogNormTrajectory
