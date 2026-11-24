/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionFlight
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Differentiating a clipped mirror action at a transverse level -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionFlight

open MeasureTheory Set Real Filter MirrorHeightAction MirrorActionEnvelope
open scoped Topology

/-- A fixed-base secant estimate for the clipped square root on the whole real line. -/
theorem sqrt_secant (p q : ℝ) : |√p - √q| * √|q| ≤ |p - q| := by
  rcases le_total 0 q with hq | hq
  · rw [abs_of_nonneg hq]
    rcases le_total 0 p with hp | hp
    · have eq : |√p - √q| * (√p + √q) = |p - q| := by
        rw [← abs_of_nonneg (add_nonneg (sqrt_nonneg p) (sqrt_nonneg q)), ← abs_mul]
        congr 1
        nlinarith [sq_sqrt hp, sq_sqrt hq]
      rw [← eq]
      exact mul_le_mul_of_nonneg_left (by linarith [sqrt_nonneg p]) (abs_nonneg _)
    · rw [sqrt_eq_zero_of_nonpos hp, zero_sub, abs_neg, abs_of_nonneg (sqrt_nonneg q),
        ← sq, sq_sqrt hq, abs_of_nonpos (by linarith : p - q ≤ 0)]
      linarith
  · rw [sqrt_eq_zero_of_nonpos hq, sub_zero, abs_of_nonneg (sqrt_nonneg p), abs_of_nonpos hq]
    rcases le_total 0 p with hp | hp
    · rw [abs_of_nonneg (by linarith : 0 ≤ p - q)]
      nlinarith [sq_nonneg (√p - √(-q)), sq_sqrt hp, sq_sqrt (neg_nonneg.mpr hq)]
    · simp [sqrt_eq_zero_of_nonpos hp]

private theorem bounded_slope (j h x : ℝ) (jx : j ≠ h) (hx : h ≠ x) :
    |(√(2 * (j - x)) - √(2 * (h - x))) / (j - h)| ≤ 2 / √|2 * (h - x)| := by
  have dj := abs_pos.mpr (sub_ne_zero.mpr jx)
  have dx := sqrt_pos.mpr (abs_pos.mpr (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
    (sub_ne_zero.mpr hx)))
  rw [abs_div, div_le_div_iff₀ dj dx]
  have b := sqrt_secant (2 * (j - x)) (2 * (h - x))
  rw [show 2 * (j - x) - 2 * (h - x) = 2 * (j - h) by ring] at b
  exact b.trans_eq ((abs_mul _ _).trans (by norm_num))

/-- A null level set and integrability of the two-sided inverse square-root gap suffice
at a specified height, without assuming continuity of the flight time in height. -/
theorem hasDerivAt_of_gap {f w : ℝ → ℝ} {a b h : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (level : ∀ᵐ t ∂volume.restrict (Ioc a b), h ≠ f t)
    (gap : IntegrableOn (fun t => |w t| * (2 / √|2 * (h - f t)|)) (Ioc a b)) :
    HasDerivAt (action f w a b) (oneWayBounceTime w f h a b) h := by
  let μ := volume.restrict (Ioc a b)
  let G (t k : ℝ) := w t * √(2 * (k - f t))
  let Q (k t : ℝ) := slope (G t) h k
  have ci (k : ℝ) : Integrable (fun t => G t k) μ :=
    ((cw.mul (continuous_sqrt.comp_continuousOn (continuousOn_const.mul
      (continuousOn_const.sub cf)))).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have ms (k : ℝ) : AEStronglyMeasurable (Q k) μ := by
    simp only [Q, slope_def_field, div_eq_mul_inv]
    exact (((ci k).sub (ci h)).mul_const _).aestronglyMeasurable
  have bound (k : ℝ) (hk : k ≠ h) : ∀ᵐ t ∂μ,
      ‖Q k t‖ ≤ |w t| * (2 / √|2 * (h - f t)|) := by
    filter_upwards [level] with t ht
    simpa only [Q, slope_def_field, G, ← mul_sub, mul_div_assoc, norm_eq_abs, abs_mul]
      using mul_le_mul_of_nonneg_left (bounded_slope k h (f t) hk ht) (abs_nonneg (w t))
  have lim : ∀ᵐ t ∂μ, Tendsto (fun k => Q k t) (𝓝[≠] h) (𝓝 (w t / √(2 * (h - f t)))) := by
    filter_upwards [level] with t ht
    have d := ((hasDerivAt_id h).sub_const (f t)).const_mul 2
    have root := hasDerivAt_sqrt (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (sub_ne_zero.mpr ht))
    have e := (root.comp h d).const_mul (w t)
    apply HasDerivAt.tendsto_slope
    apply e.congr_deriv
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  have bounds : ∀ᶠ k in 𝓝[≠] h, ∀ᵐ t ∂μ, ‖Q k t‖ ≤ |w t| * (2 / √|2 * (h - f t)|) := by
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact bound k hk
  have conv := tendsto_integral_filter_of_dominated_convergence
    (fun t => |w t| * (2 / √|2 * (h - f t)|)) (Eventually.of_forall ms)
    bounds gap lim
  apply hasDerivAt_iff_tendsto_slope.mpr
  have eq (k : ℝ) : slope (action f w a b) h k = ∫ t, Q k t ∂μ := by
    simp only [Q, slope_def_field, div_eq_mul_inv]
    rw [integral_mul_const, integral_sub (ci k) (ci h)]
    simp only [action, intervalIntegral.integral_of_le ab, μ, G]
  rw [show slope (action f w a b) h = fun k => ∫ t, Q k t ∂μ from funext eq]
  simpa only [μ, oneWayBounceTime, intervalIntegral.integral_of_le ab] using conv

private theorem distance_integrable (r a b : ℝ) :
    IntervalIntegrable (fun t => 1 / √|2 * (t - r)|) volume a b := by
  have pos := (scalar r a b).1
  have neg := (IntervalIntegrable.iff_comp_neg (by apply eNorm_ne_top)).mp
    ((scalar (-r) (-a) (-b)).1)
  simp only [neg_neg] at neg
  apply (pos.add neg).congr
  intro t _
  change 1 / √(2 * (t - r)) + 1 / √(2 * (-t - -r)) = 1 / √|2 * (t - r)|
  rw [show 2 * (-t - -r) = -(2 * (t - r)) by ring]
  rcases le_total 0 (2 * (t - r)) with ht | ht
  · simp [abs_of_nonneg ht, sqrt_eq_zero_of_nonpos (neg_nonpos.mpr ht)]
  · simp [abs_of_nonpos ht, sqrt_eq_zero_of_nonpos ht]

/-- A single simple level crossing on a compact interval gives a two-sided integrable
inverse square-root gap. This only uses differentiability at the root. -/
theorem gap_of_simple_root {f w : ℝ → ℝ} {a b h r v : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (hit : f r = h) (unique : ∀ t ∈ Icc a b, f t = h → t = r)
    (d : HasDerivAt f v r) (transverse : v ≠ 0) :
    IntervalIntegrable (fun t => |w t| * (2 / √|2 * (h - f t)|)) volume a b := by
  have factor (t : ℝ) : (t - r) * dslope f r t = f t - h := by
    simpa only [smul_eq_mul, hit] using sub_smul_dslope f r t
  have nonzero (t : ℝ) (ht : t ∈ Icc a b) : dslope f r t ≠ 0 := by
    rcases eq_or_ne t r with rfl | ne
    · simpa only [dslope_same, d.deriv] using transverse
    · intro hz
      exact ne (unique t ht (by linarith [show f t - h = 0 by rw [← factor, hz, mul_zero]]))
  have cd : ContinuousOn (dslope f r) (Icc a b) := by
    intro t ht
    rcases eq_or_ne t r with rfl | ne
    · exact (continuousAt_dslope_same.mpr d.differentiableAt).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne ne).mpr (cf t ht)
  have cc : ContinuousOn (fun t => |w t| * (2 / √|dslope f r t|)) (uIcc a b) := by
    rw [uIcc_of_le ab]
    exact cw.abs.mul (continuousOn_const.div (continuous_sqrt.comp_continuousOn cd.abs)
      (fun t ht => (sqrt_pos.mpr (abs_pos.mpr (nonzero t ht))).ne'))
  apply ((distance_integrable r a b).continuousOn_mul cc).congr
  intro t _
  change |w t| * (2 / √|dslope f r t|) * (1 / √|2 * (t - r)|) =
    |w t| * (2 / √|2 * (h - f t)|)
  have fac : |2 * (h - f t)| = |2 * (t - r)| * |dslope f r t| := by
    rw [← abs_mul, mul_assoc, factor, ← abs_neg (2 * (h - f t))]
    congr 1
    ring
  rw [fac, sqrt_mul (abs_nonneg _)]
  ring

/-- Two transverse first mirrors with forbidden outer caps give the exact derivative at
this height. Derivatives of either mirror's position are unnecessary. -/
theorem hasDerivAt_two_mirrors {f w : ℝ → ℝ} {a l c r b h vl vr : ℝ}
    (al : a ≤ l) (rb : r ≤ b) (well : LaunchWell f c h l r)
    (cf : ContinuousOn f (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (left : ∀ t ∈ Ico a l, h < f t) (right : ∀ t ∈ Ioc r b, h < f t)
    (dl : HasDerivAt f vl l) (nl : vl ≠ 0) (dr : HasDerivAt f vr r) (nr : vr ≠ 0) :
    HasDerivAt (action f w a b) (oneWayBounceTime w f h a b) h := by
  have ac := al.trans well.left_lt.le
  have cb := well.lt_right.le.trans rb
  have ul (t : ℝ) (ht : t ∈ Icc a c) (hit : f t = h) : t = l := by
    rcases lt_trichotomy t l with lt | eq | gt
    · exact False.elim ((left t ⟨ht.1, lt⟩).ne hit.symm)
    · exact eq
    · exact False.elim ((well.accessible t ⟨gt, ht.2.trans_lt well.lt_right⟩).ne hit)
  have ur (t : ℝ) (ht : t ∈ Icc c b) (hit : f t = h) : t = r := by
    rcases lt_trichotomy t r with lt | eq | gt
    · exact False.elim ((well.accessible t ⟨well.left_lt.trans_le ht.1, lt⟩).ne hit)
    · exact eq
    · exact False.elim ((right t ⟨gt, ht.2⟩).ne hit.symm)
  apply hasDerivAt_of_gap (ac.trans cb) cf cw
  · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne l),
      ae_restrict_of_ae (volume.ae_ne r)] with t ht n₁ n₂
    intro hit
    rcases le_total t c with tc | ct
    · exact n₁ (ul t ⟨ht.1.le, tc⟩ hit.symm)
    · exact n₂ (ur t ⟨ct, ht.2⟩ hit.symm)
  · have sl : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl cb
    have sr : Icc c b ⊆ Icc a b := Icc_subset_Icc ac le_rfl
    have p := gap_of_simple_root ac (cf.mono sl) (cw.mono sl) well.left_hit ul dl nl
    have q := gap_of_simple_root cb (cf.mono sr) (cw.mono sr) well.right_hit ur dr nr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (ac.trans cb)).mp (p.trans q)

/-- Removing forbidden end caps preserves the actual flight integral between the mirrors. -/
theorem time_eq_between {f w : ℝ → ℝ} {a l r b h : ℝ} (al : a ≤ l) (rb : r ≤ b)
    (it : IntervalIntegrable (fun t => w t / √(2 * (h - f t))) volume l r)
    (left : ∀ t ∈ Icc a l, h ≤ f t) (right : ∀ t ∈ Icc r b, h ≤ f t) :
    oneWayBounceTime w f h a b = oneWayBounceTime w f h l r := by
  let g := fun t => w t / √(2 * (h - f t))
  have cap {p q : ℝ} (pq : p ≤ q) (outer : ∀ t ∈ Icc p q, h ≤ f t) :
      IntervalIntegrable g volume p q ∧ (∫ t in p..q, g t) = 0 := by
    have vanish : EqOn (fun _ : ℝ => (0 : ℝ)) g (uIcc p q) := by
      rw [uIcc_of_le pq]
      intro t ht
      simp only [g, sqrt_eq_zero_of_nonpos (by linarith [outer t ht] : 2 * (h - f t) ≤ 0),
        div_zero]
    exact ⟨intervalIntegrable_const.congr (fun _ ht => vanish (uIoc_subset_uIcc ht)),
      by rw [← intervalIntegral.integral_congr vanish]; simp⟩
  obtain ⟨li, lz⟩ := cap al left
  obtain ⟨ri, rz⟩ := cap rb right
  have p := intervalIntegral.integral_add_adjacent_intervals li it
  have q := intervalIntegral.integral_add_adjacent_intervals (li.trans it) ri
  change (∫ t in a..b, g t) = ∫ t in l..r, g t
  rw [← q, rz, add_zero, ← p, lz, zero_add]

end PlasmaLean.Kinetic.MirrorActionFlight
