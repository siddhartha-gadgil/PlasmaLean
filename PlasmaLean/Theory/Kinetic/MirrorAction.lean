/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Removing the square-root turning points of a regular mirror action

For a well with gap Q, roots a < b, and arclength density A, the one-way scaled
action is the integral of A√Q between the roots. A twice-divided difference gives
a continuous positive factor H such that Q(s)=(s−a)(b−s)H(s). The substitution
s=a+(b−a)sin²θ gives the fixed interval [0,π / 2]. Applications can absorb a
constant such as √2 into A.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Kinetic.MirrorAction

open Real Set MeasureTheory
open scoped Interval

/-- Continuous extension of Q(s)/((s−a)(b−s)) across the two simple roots. -/
def shape (Q : ℝ → ℝ) (a b s : ℝ) : ℝ := -dslope (dslope Q a) b s

private theorem first_at_right {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ha : Q a = 0) (hb : Q b = 0) : dslope Q a b = 0 := by
  rw [dslope_of_ne _ hab.ne', slope_def_field, ha, hb, sub_zero, zero_div]

/-- Exact factorization, including both turning points. -/
theorem factor {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ha : Q a = 0) (hb : Q b = 0) (s : ℝ) :
    Q s = (s - a) * (b - s) * shape Q a b s := by
  have h₁ := sub_smul_dslope_of_zero ha s
  have h₂ := sub_smul_dslope_of_zero (first_at_right hab ha hb) s
  rw [smul_eq_mul] at h₁ h₂
  unfold shape
  linear_combination -h₁ - (s - a)*h₂

/-- Continuity requires differentiability of Q at the roots and continuity elsewhere. -/
theorem shape_continuous {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hQ : Continuous Q) (ha : DifferentiableAt ℝ Q a) (hb : DifferentiableAt ℝ Q b) :
    Continuous (shape Q a b) := by
  have h₁ : Continuous (dslope Q a) :=
    continuousOn_univ.mp ((continuousOn_dslope Filter.univ_mem).mpr ⟨hQ.continuousOn, ha⟩)
  have h₂ := (differentiableAt_dslope_of_ne hab.ne').mpr hb
  exact (continuousOn_univ.mp ((continuousOn_dslope Filter.univ_mem).mpr
    ⟨h₁.continuousOn, h₂⟩)).neg

/-- The endpoint values of H are the signed slopes divided by the root separation. -/
theorem shape_ends {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b) (ha : Q a = 0) (hb : Q b = 0)
    (hd : DifferentiableAt ℝ Q b) :
    (b - a) * shape Q a b a = deriv Q a ∧ (b - a) * shape Q a b b = -deriv Q b := by
  have hf := first_at_right hab ha hb
  have hl := sub_smul_dslope_of_zero hf a
  simp only [smul_eq_mul, dslope_same] at hl
  have huw : DifferentiableAt ℝ (dslope Q a) b := (differentiableAt_dslope_of_ne hab.ne').2 hd
  have hprod := ((hasDerivAt_id b).sub_const a).mul huw.hasDerivAt
  have hfun : (fun x : ℝ => (x - a) * dslope Q a x) = Q :=
    funext fun x => sub_smul_dslope_of_zero ha x
  change HasDerivAt (fun x : ℝ => (x - a) * dslope Q a x)
    (1 * dslope Q a b + (b - a) * deriv (dslope Q a) b) b at hprod
  rw [hfun, hf, mul_zero, zero_add] at hprod
  unfold shape
  rw [dslope_same]
  constructor
  · linear_combination hl
  · rw [hprod.deriv]
    ring

/-- Two simple inward crossings and an accessible open well give a strictly positive
uniform lower bound on H, including both endpoints. -/
theorem exists_shape_lower {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hQ : Continuous Q)
    (ha : Q a = 0) (hb : Q b = 0) (hda : 0 < deriv Q a) (hdb : deriv Q b < 0)
    (hi : ∀ s ∈ Ioo a b, 0 < Q s) :
    ∃ c > 0, ∀ s ∈ Icc a b, c ≤ shape Q a b s := by
  have da := differentiableAt_of_deriv_ne_zero hda.ne'
  have db := differentiableAt_of_deriv_ne_zero hdb.ne
  obtain ⟨hl, hr⟩ := shape_ends hab ha hb db
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le)
    (shape_continuous hab hQ da db).continuousOn
  refine ⟨_, ?_, fun x hx => hmin hx⟩
  rcases hs.1.eq_or_lt with rfl | has
  · exact pos_of_mul_pos_right (hl ▸ hda) (sub_pos.mpr hab).le
  rcases hs.2.eq_or_lt with rfl | hsb
  · exact pos_of_mul_pos_right (hr ▸ neg_pos.mpr hdb) (sub_pos.mpr hab).le
  exact pos_of_mul_pos_right (factor hab ha hb s ▸ hi s ⟨has, hsb⟩)
    (mul_nonneg (sub_nonneg.mpr has.le) (sub_nonneg.mpr hsb.le))

/-- Quantitative certificate for a uniform lower bound m. In each endpoint collar
the gap grows at least linearly away from its root. In the core it exceeds a fixed
height. The constants can be shared across a family of wells. -/
theorem shape_ge_of_collars {Q : ℝ → ℝ} {a b m κ δ : ℝ} (hab : a < b) (hm : 0 ≤ m)
    (ha : Q a = 0) (hb : Q b = 0) (hd : DifferentiableAt ℝ Q b)
    (hda : κ ≤ deriv Q a) (hdb : κ ≤ -deriv Q b)
    (hL : m * (b - a) ≤ κ) (hδ : m * ((b - a) / 2) ^ 2 ≤ δ)
    (hcover : ∀ s ∈ Ioo a b, κ * (s - a) ≤ Q s ∨ κ * (b - s) ≤ Q s ∨ δ ≤ Q s)
    (s : ℝ) (hs : s ∈ Icc a b) : m ≤ shape Q a b s := by
  obtain ⟨hl, hr⟩ := shape_ends hab ha hb hd
  rcases hs.1.eq_or_lt with rfl | h₁
  · apply le_of_mul_le_mul_left _ (sub_pos.mpr hab)
    simpa only [hl, mul_comm m] using hL.trans hda
  rcases hs.2.eq_or_lt with rfl | h₂
  · apply le_of_mul_le_mul_left _ (sub_pos.mpr hab)
    simpa only [hr, mul_comm m] using hL.trans hdb
  have hp : 0 < (s - a) * (b - s) := mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂)
  apply le_of_mul_le_mul_left _ hp
  rw [← factor hab ha hb]
  rcases hcover s ⟨h₁, h₂⟩ with hl | hr | hc
  · have h := mul_le_mul_of_nonneg_left (show b - s ≤ b - a by linarith) hm
    nlinarith [mul_le_mul_of_nonneg_right (h.trans hL) (sub_nonneg.mpr h₁.le)]
  · have h := mul_le_mul_of_nonneg_left (show s - a ≤ b - a by linarith) hm
    nlinarith [mul_le_mul_of_nonneg_right (h.trans hL) (sub_nonneg.mpr h₂.le)]
  · have h : (s - a) * (b - s) ≤ ((b - a) / 2) ^ 2 := by nlinarith [sq_nonneg (2*s - a - b)]
    calc _ ≤ m * ((b - a) / 2) ^ 2 := by
           simpa only [mul_comm m] using mul_le_mul_of_nonneg_left h hm
         _ ≤ Q s := hδ.trans hc

/-- The fixed-angle parametrization of the well. -/
def chart (a b θ : ℝ) := a + (b - a) * sin θ ^ 2

/-- Half the Jacobian of the angle chart. -/
def halfSpeed (a b θ : ℝ) := (b - a) * sin θ * cos θ

private theorem chart_deriv (a b θ : ℝ) : HasDerivAt (chart a b) (2 * halfSpeed a b θ) θ := by
  have h := (((hasDerivAt_sin θ).pow 2).const_mul (b - a)).const_add a
  convert h using 1
  · rfl
  · simp [halfSpeed]
    ring

private theorem chart_mem {a b θ : ℝ} (hab : a ≤ b) : chart a b θ ∈ Icc a b := by
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg _))
  · unfold chart
    have hsin : sin θ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq θ, sq_nonneg (cos θ)]
    linarith [mul_le_mul_of_nonneg_left hsin (sub_nonneg.mpr hab)]

/-- The same positive denominator works uniformly on the fixed integration domain. -/
theorem exists_shape_chart_lower {Q : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hQ : Continuous Q)
    (ha : Q a = 0) (hb : Q b = 0) (hda : 0 < deriv Q a) (hdb : deriv Q b < 0)
    (hi : ∀ s ∈ Ioo a b, 0 < Q s) :
    ∃ c > 0, ∀ θ, c ≤ shape Q a b (chart a b θ) := by
  obtain ⟨c, hc, hmin⟩ := exists_shape_lower hab hQ ha hb hda hdb hi
  exact ⟨c, hc, fun _ => hmin _ (chart_mem hab.le)⟩

/-- The square root in the physical integrand is a smooth angular factor times √H.
In particular no division by the vanishing gap is required at either endpoint. -/
theorem sqrt_chart {Q : ℝ → ℝ} {a b θ : ℝ} (hab : a < b) (ha : Q a = 0) (hb : Q b = 0)
    (hθ : θ ∈ Icc 0 (π / 2)) :
    √(Q (chart a b θ)) = halfSpeed a b θ * √(shape Q a b (chart a b θ)) := by
  have hp : 0 ≤ halfSpeed a b θ := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hab.le)
      (sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos])))
    (cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2⟩)
  rw [factor hab ha hb]
  have hd : (chart a b θ - a) * (b - chart a b θ) = halfSpeed a b θ ^ 2 := by
    unfold chart halfSpeed
    linear_combination -(b - a) ^ 2 * sin θ ^ 2 * (sin_sq_add_cos_sq θ)
  rw [hd, sqrt_mul (sq_nonneg _), sqrt_sq hp]

/-- Exact transformation of the one-way physical action onto a fixed compact interval. -/
theorem action_eq_fixed {Q A : ℝ → ℝ} {a b : ℝ} (hab : a < b) (ha : Q a = 0) (hb : Q b = 0)
    (hc : Continuous (fun s => A s * √(Q s))) :
    (∫ s in a..b, A s * √(Q s)) =
      ∫ θ in 0..π / 2, 2 * halfSpeed a b θ ^ 2 * A (chart a b θ) *
        √(shape Q a b (chart a b θ)) := by
  have hd := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π / 2)
    (fun θ _ => chart_deriv a b θ) (by unfold halfSpeed; fun_prop) hc
  simp only [chart, sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    add_zero, sin_pi_div_two, one_pow, mul_one, add_sub_cancel] at hd
  rw [← hd]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le (by positivity)] at hθ
  change A (chart a b θ) * √(Q (chart a b θ)) * (2 * halfSpeed a b θ) = _
  rw [sqrt_chart hab ha hb hθ]
  ring

/-- In the interior the full physical derivative exists, and its transverse component
uses only partial derivatives at fixed physical position. -/
theorem density_partial {A Q : ℝ × ℝ → ℝ} {dA dQ : (ℝ × ℝ) →L[ℝ] ℝ} {u s : ℝ}
    (ha : HasFDerivAt A dA (u, s)) (hq : HasFDerivAt Q dQ (u, s)) (hp : 0 < Q (u, s)) :
    ∃ G : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (fun x => A x * √(Q x)) G (u, s) ∧
      G (1, 0) = dA (1, 0) * √(Q (u, s)) + A (u, s) * dQ (1, 0) / (2 * √(Q (u, s))) := by
  let W := fun x => A x * √(Q x)
  have hw : DifferentiableAt ℝ W (u, s) :=
    ha.differentiableAt.mul (hq.differentiableAt.sqrt hp.ne')
  refine ⟨_, hw.hasFDerivAt, ?_⟩
  have line : HasDerivAt (fun p => (p, s)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u s)
  have alg := (ha.comp_hasDerivAt u line).mul ((hq.comp_hasDerivAt u line).sqrt hp.ne')
  have g : HasDerivAt (fun t => W (t, s)) (fderiv ℝ W (u, s) (1, 0)) u :=
    (hw.hasFDerivAt.comp_hasDerivAt (f := fun p => (p, s)) (l := W) u line)
  have k : HasDerivAt (fun t => W (t, s))
      (dA (1, 0) * √(Q (u, s)) + A (u, s) * (dQ (1, 0) / (2 * √(Q (u, s))))) u := alg
  rw [g.unique k]
  ring

/-- Regularized pointwise transverse derivative. The variations dA, dQ are taken at
fixed physical position s. The resulting density extends to the two endpoint angles
whenever the factor H remains uniformly positive. -/
theorem transverse_density {Q : ℝ → ℝ} {a b θ A dA dQ : ℝ}
    (hab : a < b) (ha : Q a = 0) (hb : Q b = 0) (hθ : θ ∈ Ioo 0 (π / 2))
    (hH : 0 < shape Q a b (chart a b θ)) :
    (dA * √(Q (chart a b θ)) + A * dQ / (2 * √(Q (chart a b θ)))) * (2 * halfSpeed a b θ) =
      2 * halfSpeed a b θ ^ 2 * dA * √(shape Q a b (chart a b θ)) +
        A * dQ / √(shape Q a b (chart a b θ)) := by
  have hp : 0 < halfSpeed a b θ := mul_pos
    (mul_pos (sub_pos.mpr hab) (sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos])))
    (cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩)
  rw [sqrt_chart hab ha hb (Ioo_subset_Icc_self hθ)]
  field_simp [hp.ne', (sqrt_pos.mpr hH).ne']

/-- Transport identity for a density F evaluated along the moving well. At an interior
angle, differentiating the pulled-back density gives the physical partial at fixed s,
plus the angular derivative of the flux F·∂ₚs. Applications use F=A√Q. -/
theorem moving_chart_deriv {F : ℝ × ℝ → ℝ} {G : (ℝ × ℝ) →L[ℝ] ℝ} {a b : ℝ → ℝ}
    {u da db θ : ℝ} (ha : HasDerivAt a da u) (hb : HasDerivAt b db u)
    (hF : HasFDerivAt F G (u, chart (a u) (b u) θ)) :
    HasDerivAt (fun p => F (p, chart (a p) (b p) θ) * (2 * halfSpeed (a p) (b p) θ))
      (G (1, 0) * (2 * halfSpeed (a u) (b u) θ) +
        deriv (fun t => F (u, chart (a u) (b u) t) * chart da db t) θ) u := by
  have hx := ha.add ((hb.sub ha).mul_const (sin θ ^ 2))
  have hv := (((hb.sub ha).mul_const (sin θ)).mul_const (cos θ)).const_mul 2
  have hparam : HasDerivAt (fun p => (p, chart (a p) (b p) θ)) (1, chart da db θ) u :=
    (hasDerivAt_id u).prodMk hx
  have hangle : HasDerivAt (fun t => (u, chart (a u) (b u) t))
      (0, 2 * halfSpeed (a u) (b u) θ) θ :=
    (hasDerivAt_const θ u).prodMk (chart_deriv (a u) (b u) θ)
  have ht := hF.comp_hasDerivAt u hparam
  have hθ := hF.comp_hasDerivAt θ hangle
  have flux := hθ.mul (chart_deriv da db θ)
  change HasDerivAt (fun t => F (u, chart (a u) (b u) t) * chart da db t)
    (G (0, 2 * halfSpeed (a u) (b u) θ) * chart da db θ +
      F (u, chart (a u) (b u) θ) * (2 * halfSpeed da db θ)) θ at flux
  rw [flux.deriv]
  have g0 (x : ℝ) : G (0, x) = x * G (0, 1) := by
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext <;> simp
  have g1 (x : ℝ) : G (1, x) = G (1, 0) + x * G (0, 1) := by
    rw [← g0, ← map_add]
    congr 1
    ext <;> simp
  convert ht.mul hv using 1
  · rfl
  · simp only [Function.comp_apply, Pi.sub_apply]
    rw [g0 (2 * halfSpeed (a u) (b u) θ), g1 (chart da db θ)]
    unfold chart halfSpeed
    ring

/-- Cancellation of the endpoint-motion term in fixed coordinates. Here F is the
regularized density, D its parameter derivative and K the desired transverse density.
The transport flux P vanishes at both mirrors. The flux derivative is only used in the
open interval, so no derivative at a square-root endpoint is assumed. -/
theorem hasDerivAt_integral_of_transport {F D : ℝ → ℝ → ℝ} {P K : ℝ → ℝ}
    {u C l r : ℝ} {U : Set ℝ} (hU : U ∈ nhds u) (hlr : l ≤ r)
    (hf : ∀ x ∈ U, Continuous (F x)) (hd : Continuous (D u)) (hk : Continuous K)
    (hbound : ∀ x ∈ U, ∀ t ∈ Icc l r, |D x t| ≤ C)
    (hder : ∀ x ∈ U, ∀ t ∈ Icc l r, HasDerivAt (fun p => F p t) (D x t) x)
    (hP : ContinuousOn P (Icc l r)) (hends : P l = P r)
    (hflux : ∀ t ∈ Ioo l r, HasDerivAt P (D u t - K t) t) :
    HasDerivAt (fun x => ∫ t in l..r, F x t) (∫ t in l..r, K t) u := by
  have cover {t : ℝ} (h : t ∈ Set.uIoc l r) : t ∈ Icc l r := by
    rw [Set.uIoc_of_le hlr] at h
    exact ⟨h.1.le, h.2⟩
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun _ => C) (a := l) (b := r) hU
    (Filter.mem_of_superset hU fun x hx => (hf x hx).aestronglyMeasurable)
    ((hf u (mem_of_mem_nhds hU)).intervalIntegrable _ _) hd.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t ht x hx => hbound x hx t (cover ht))
    intervalIntegrable_const (Filter.Eventually.of_forall fun t ht x hx => hder x hx t (cover ht))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hP hflux
    ((hd.sub hk).intervalIntegrable _ _)
  rw [hends, sub_self, intervalIntegral.integral_sub (hd.intervalIntegrable _ _)
    (hk.intervalIntegrable _ _), sub_eq_zero] at he
  exact he ▸ hi.2

/-- Pullback of a physical one-way action density by its moving angle chart. -/
def pullback (W : ℝ × ℝ → ℝ) (a b : ℝ → ℝ) (p t : ℝ) : ℝ :=
  W (p, chart (a p) (b p) t) * (2 * halfSpeed (a p) (b p) t)

/-- Derivative of the physical action with moving zeros. W may have singular
physical derivatives at the turning points. Only the regularized pullback needs
a uniformly bounded parameter derivative D there. The interior fixed-position
partial times the chart Jacobian extends to K, which is the returned density. -/
theorem hasDerivAt_action {W : ℝ × ℝ → ℝ} {D : ℝ → ℝ → ℝ} {K a b : ℝ → ℝ}
    {u C da db : ℝ} {U : Set ℝ} (hU : U ∈ nhds u)
    (ha : HasDerivAt a da u) (hb : HasDerivAt b db u)
    (hW : ∀ p ∈ U, Continuous (fun s => W (p, s)))
    (hzero : W (u, a u) = 0 ∧ W (u, b u) = 0) (hd : Continuous (D u)) (hk : Continuous K)
    (hbound : ∀ p ∈ U, ∀ t ∈ Icc 0 (π / 2), |D p t| ≤ C)
    (hder : ∀ p ∈ U, ∀ t ∈ Icc 0 (π / 2),
      HasDerivAt (fun x => pullback W a b x t) (D p t) p)
    (hphys : ∀ t ∈ Ioo 0 (π / 2), ∃ G : (ℝ × ℝ) →L[ℝ] ℝ,
      HasFDerivAt W G (u, chart (a u) (b u) t) ∧
        K t = G (1, 0) * (2 * halfSpeed (a u) (b u) t)) :
    HasDerivAt (fun p => ∫ s in a p..b p, W (p, s)) (∫ t in 0..π / 2, K t) u := by
  have cc (x y : ℝ) : Continuous (chart x y) := by unfold chart; fun_prop
  have mu := mem_of_mem_nhds hU
  let P := fun t => W (u, chart (a u) (b u) t) * chart da db t
  have cp : Continuous P := ((hW u mu).comp (cc _ _)).mul (cc _ _)
  have pend : P 0 = P (π / 2) := by simp [P, chart, hzero]
  have deriv := hasDerivAt_integral_of_transport (P := P) (F := pullback W a b)
    hU (show (0 : ℝ) ≤ π / 2 by positivity) (fun p hp =>
      ((hW p hp).comp (cc _ _)).mul (by unfold halfSpeed; fun_prop))
    hd hk hbound hder cp.continuousOn pend (fun t ht => by
      obtain ⟨G, hG, hK⟩ := hphys t ht
      have hm := moving_chart_deriv ha hb hG
      change HasDerivAt (fun p => pullback W a b p t)
        (G (1, 0) * (2 * halfSpeed (a u) (b u) t) + _root_.deriv P t) u at hm
      have hsum := hm.unique (hder u mu t (Ioo_subset_Icc_self ht))
      have hv : HasDerivAt (fun x => (u, chart (a u) (b u) x))
          (0, 2 * halfSpeed (a u) (b u) t) t :=
        (hasDerivAt_const t u).prodMk (chart_deriv _ _ t)
      have hf := ((hG.comp_hasDerivAt t hv).mul (chart_deriv da db t)).differentiableAt
      change DifferentiableAt ℝ P t at hf
      have he : D u t - K t = _root_.deriv P t := by linarith [hsum, hK]
      rw [he]
      exact hf.hasDerivAt)
  apply deriv.congr_of_eventuallyEq
  filter_upwards [hU] with p hp
  have hc := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π / 2)
    (fun t _ => chart_deriv (a p) (b p) t) (by unfold halfSpeed; fun_prop) (hW p hp)
  simpa [pullback, Function.comp_def, chart] using hc.symm

/-- A quadratic mirror well has unit shape on the entire well, including both roots. -/
theorem quadratic_shape {a b : ℝ} (hab : a < b) (s : ℝ) (hs : s ∈ Icc a b) :
    shape (fun x => (x - a) * (b - x)) a b s = 1 := by
  let Q := fun x : ℝ => (x - a) * (b - x)
  have hQ (x : ℝ) : HasDerivAt Q ((b - x) - (x - a)) x := by
    convert ((hasDerivAt_id x).sub_const a).mul
      ((hasDerivAt_const x b).sub (hasDerivAt_id x)) using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq]
      ring
  have ha : Q a = 0 := by simp [Q]
  have hb : Q b = 0 := by simp [Q]
  obtain ⟨hl, hr⟩ := shape_ends hab ha hb (hQ b).differentiableAt
  change shape Q a b s = 1
  rcases hs.1.eq_or_lt with rfl | has
  · rw [(hQ a).deriv] at hl
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab.ne')
    linarith
  rcases hs.2.eq_or_lt with rfl | hsb
  · rw [(hQ s).deriv] at hr
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab.ne')
    linarith
  apply mul_left_cancel₀ (mul_ne_zero (sub_ne_zero.mpr has.ne') (sub_ne_zero.mpr hsb.ne'))
  rw [← factor hab ha hb, mul_one]

/-- Losing the slope at the left root really can destroy every positive lower bound:
Q(s)=s²(1−s) has an open accessible interval and a double left root. -/
theorem double_root_no_shape_lower :
    ¬ ∃ c > 0, ∀ s ∈ Icc (0 : ℝ) 1, c ≤ shape (fun x => x ^ 2 * (1 - x)) 0 1 s := by
  let Q := fun x : ℝ => x ^ 2 * (1 - x)
  have he := (shape_ends (Q := Q) (a := 0) (b := 1) (by norm_num) (by simp [Q]) (by simp [Q])
    (by unfold Q; fun_prop)).1
  have hd : deriv Q 0 = 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).pow 2).mul
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id (0 : ℝ)))
    change HasDerivAt Q _ 0 at h
    rw [h.deriv]
    norm_num
  rintro ⟨c, hc, hmin⟩
  have hl : c ≤ shape Q 0 1 0 := hmin 0 ⟨le_rfl, zero_le_one⟩
  rw [hd, sub_zero, one_mul] at he
  linarith

end PlasmaLean.Kinetic.MirrorAction
