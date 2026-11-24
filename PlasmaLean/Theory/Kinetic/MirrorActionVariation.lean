/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorActionTransverse
public import PlasmaLean.Theory.Kinetic.MirrorActionComparison

/-! # First variation of the mirror action with respect to a field-line label -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionVariation
open Filter MeasureTheory Set Real MirrorActionFlight MirrorHeightAction
open scoped Topology

/-- Differentiate the clipped square root of a varying scalar profile under an integral.
Only the inverse square-root gap on the base profile enters the majorant. -/
theorem hasDerivAt_integral_sqrt {T : Type*} [MeasurableSpace T] {μ : Measure T}
    {P : ℝ → T → ℝ} {D C : T → ℝ} {p : ℝ}
    (integrable : ∀ᶠ s in 𝓝 p, Integrable (fun t => √(P s t)) μ)
    (regular : ∀ᵐ t ∂μ, P p t ≠ 0 ∧ HasDerivAt (fun s => P s t) (D t) p)
    (control : ∀ᶠ s in 𝓝[≠] p, ∀ᵐ t ∂μ, |P s t - P p t| ≤ C t * |s - p|)
    (gap : Integrable (fun t => C t / √|P p t|) μ) :
    HasDerivAt (fun s => ∫ t, √(P s t) ∂μ) (∫ t, D t / (2 * √(P p t)) ∂μ) p := by
  let Q (s : ℝ) (t : T) := slope (fun k => √(P k t)) p s
  have ip := integrable.self_of_nhds
  have ms : ∀ᶠ s in 𝓝[≠] p, AEStronglyMeasurable (Q s) μ := by
    filter_upwards [integrable.filter_mono nhdsWithin_le_nhds] with s hs
    simpa only [Q, slope_def_field, div_eq_mul_inv, Pi.sub_apply] using
      ((hs.sub ip).mul_const (s - p)⁻¹ |>.aestronglyMeasurable)
  have bounds : ∀ᶠ s in 𝓝[≠] p, ∀ᵐ t ∂μ, ‖Q s t‖ ≤ C t / √|P p t| := by
    filter_upwards [control, self_mem_nhdsWithin] with s hs ne
    filter_upwards [hs, regular] with t bound reg
    simp only [Q, slope_def_field, norm_eq_abs, abs_div]
    rw [
      div_le_div_iff₀ (abs_pos.mpr (sub_ne_zero.mpr ne)) (sqrt_pos.mpr (abs_pos.mpr reg.1))]
    exact (sqrt_secant _ _).trans bound
  have limits : ∀ᵐ t ∂μ, Tendsto (fun s => Q s t) (𝓝[≠] p) (𝓝 (D t / (2 * √(P p t)))) := by
    filter_upwards [regular] with t reg
    apply HasDerivAt.tendsto_slope
    simpa only [div_eq_mul_inv, one_mul, Function.comp_def, mul_comm] using
      (hasDerivAt_sqrt reg.1).comp p reg.2
  have conv := tendsto_integral_filter_of_dominated_convergence _ ms bounds gap limits
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply conv.congr'
  filter_upwards [integrable.filter_mono nhdsWithin_le_nhds] with s hs
  simp only [Q, slope_def_field, div_eq_mul_inv]
  rw [integral_mul_const, integral_sub hs ip]

private theorem gap_from_root {P C : ℝ → ℝ} {a b r v : ℝ} (ab : a ≤ b)
    (cf : ContinuousOn P (Icc a b)) (cc : ContinuousOn C (Icc a b))
    (nonneg : ∀ t ∈ Icc a b, 0 ≤ C t) (zero : P r = 0)
    (unique : ∀ t ∈ Icc a b, P t = 0 → t = r) (dv : HasDerivAt P v r) (nv : v ≠ 0) :
    IntervalIntegrable (fun t => C t / √|P t|) volume a b := by
  have given := gap_of_simple_root (f := fun t => -P t / 2) (w := fun t => C t / 2) (h := 0)
    ab (cf.neg.div_const 2) (cc.div_const 2) (by simp [zero])
    (fun t ht vanished => unique t ht (by linarith)) (dv.neg.div_const 2)
    (div_ne_zero (neg_ne_zero.mpr nv) (by norm_num))
  apply given.congr
  intro t ht
  have he := uIoc_subset_uIcc ht
  rw [uIcc_of_le ab] at he
  change |C t / 2| * (2 / √|2 * (0 - -P t / 2)|) = C t / √|P t|
  rw [abs_of_nonneg (div_nonneg (nonneg t he) (by norm_num : (0 : ℝ) ≤ 2)),
    show 2 * (0 - -P t / 2) = P t by ring]
  ring

/-- Two simple crossings of the base profile give both the null level set and the
integrable majorant required for differentiation, including the forbidden caps. -/
theorem transverse_window {P C : ℝ → ℝ} {a c b l r vl vr : ℝ} (ac : a ≤ c) (cb : c ≤ b)
    (cf : ContinuousOn P (Icc a b)) (cc : ContinuousOn C (Icc a b))
    (nonneg : ∀ t ∈ Icc a b, 0 ≤ C t) (left : P l = 0) (right : P r = 0)
    (ul : ∀ t ∈ Icc a c, P t = 0 → t = l) (ur : ∀ t ∈ Icc c b, P t = 0 → t = r)
    (dl : HasDerivAt P vl l) (nl : vl ≠ 0) (dr : HasDerivAt P vr r) (nr : vr ≠ 0) :
    (∀ᵐ t ∂volume.restrict (Ioc a b), P t ≠ 0) ∧
      IntegrableOn (fun t => C t / √|P t|) (Ioc a b) := by
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne l),
      ae_restrict_of_ae (volume.ae_ne r)] with t ht n₁ n₂
    intro hit
    rcases le_total t c with lo | hi
    · exact n₁ (ul t ⟨ht.1.le, lo⟩ hit)
    · exact n₂ (ur t ⟨hi, ht.2⟩ hit)
  · have sl : Icc a c ⊆ Icc a b := Icc_subset_Icc_right cb
    have sr : Icc c b ⊆ Icc a b := Icc_subset_Icc_left ac
    have pre := gap_from_root ac (cf.mono sl) (cc.mono sl) (fun t ht => nonneg t (sl ht))
      left ul dl nl
    have post := gap_from_root cb (cf.mono sr) (cc.mono sr) (fun t ht => nonneg t (sr ht))
      right ur dr nr
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (ac.trans cb)).mp (pre.trans post)

/-- The weighted gap incorporates the arclength change as well as the perturbation
of the field strength. Its square root agrees with the physical action density. -/
def weightedGap (f w : ℝ → ℝ → ℝ) (h s t : ℝ) := 2 * ((w s t) ^ 2 * (h - f s t))

/-- A fixed-height, fixed-window action derivative with respect to a parameter
of the traced curves. Both the field strength and the arclength weight may vary. -/
theorem hasDerivAt_action {f w : ℝ → ℝ → ℝ} {a b h p : ℝ} {D C : ℝ → ℝ} (ab : a ≤ b)
    (profiles : ∀ᶠ s in 𝓝 p, ContinuousOn (f s) (Icc a b) ∧ ContinuousOn (w s) (Icc a b) ∧
      ∀ t ∈ Icc a b, 0 ≤ w s t)
    (regular : ∀ᵐ t ∂volume.restrict (Ioc a b), weightedGap f w h p t ≠ 0 ∧
      HasDerivAt (fun s => weightedGap f w h s t) (D t) p)
    (control : ∀ᶠ s in 𝓝[≠] p, ∀ᵐ t ∂volume.restrict (Ioc a b),
      |weightedGap f w h s t - weightedGap f w h p t| ≤ C t * |s - p|)
    (gap : IntegrableOn (fun t => C t / √|weightedGap f w h p t|) (Ioc a b)) :
    HasDerivAt (fun s => action (f s) (w s) a b h)
      (∫ t in a..b, D t / (2 * √(weightedGap f w h p t))) p := by
  rw [intervalIntegral.integral_of_le ab]
  apply (hasDerivAt_integral_sqrt (P := weightedGap f w h) ?_ regular control gap)
    |>.congr_of_eventuallyEq
  · filter_upwards [profiles] with s hs
    rw [action, intervalIntegral.integral_of_le ab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact density_eq_sqrt_weighted_gap (hs.2.2 t (Ioc_subset_Icc_self ht)) _ _
  · filter_upwards [profiles] with s hs
    have cont : ContinuousOn (weightedGap f w h s) (Icc a b) :=
      (continuousOn_const (c := (2 : ℝ))).mul ((hs.2.1.pow 2).mul
        ((continuousOn_const (c := h)).sub hs.1))
    exact (continuous_sqrt.comp_continuousOn cont).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The two contributions to the field-line derivative are the change of arclength
and the change of field strength at fixed height. -/
def variation (h f w df dw : ℝ) := dw * √(2 * (h - f)) - w * df / √(2 * (h - f))

theorem weighted_derivative_eq {w : ℝ} (pos : 0 < w) (h f df dw : ℝ) :
    (2 * (2 * w * dw * (h - f) - w ^ 2 * df)) / (2 * √(2 * (w ^ 2 * (h - f)))) =
      variation h f w df dw := by
  rw [← density_eq_sqrt_weighted_gap pos.le, variation]
  by_cases active : 0 < 2 * (h - f)
  · have speed := sqrt_pos.mpr active
    field_simp [pos.ne', speed.ne']
    rw [sq_sqrt active.le]
    ring
  · simp [sqrt_eq_zero_of_nonpos (not_lt.mp active)]

/-- First variation in terms of the two observable derivatives. This includes moving
mirrors through the square-root clipping on a common fixed window. -/
theorem first_variation {f w : ℝ → ℝ → ℝ} {df dw C : ℝ → ℝ} {a b h p : ℝ} (ab : a ≤ b)
    (profiles : ∀ᶠ s in 𝓝 p, ContinuousOn (f s) (Icc a b) ∧ ContinuousOn (w s) (Icc a b) ∧
      ∀ t ∈ Icc a b, 0 ≤ w s t)
    (regular : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 < w p t ∧ h ≠ f p t ∧
      HasDerivAt (fun s => f s t) (df t) p ∧ HasDerivAt (fun s => w s t) (dw t) p)
    (control : ∀ᶠ s in 𝓝[≠] p, ∀ᵐ t ∂volume.restrict (Ioc a b),
      |weightedGap f w h s t - weightedGap f w h p t| ≤ C t * |s - p|)
    (gap : IntegrableOn (fun t => C t / √|weightedGap f w h p t|) (Ioc a b)) :
    HasDerivAt (fun s => action (f s) (w s) a b h)
      (∫ t in a..b, variation h (f p t) (w p t) (df t) (dw t)) p := by
  let D (t : ℝ) := 2 * (2 * w p t * dw t * (h - f p t) - (w p t) ^ 2 * df t)
  apply (hasDerivAt_action (D := D) ab profiles ?_ control gap).congr_deriv
  · rw [intervalIntegral.integral_of_le ab, intervalIntegral.integral_of_le ab]
    apply integral_congr_ae
    filter_upwards [regular] with t ht
    exact weighted_derivative_eq ht.1 _ _ _ _
  · filter_upwards [regular] with t ⟨pos, ne, hf, hw⟩
    refine ⟨mul_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero _ pos.ne') (sub_ne_zero.mpr ne)),
      ?_⟩
    have d := ((hw.pow 2).mul (hf.const_sub h)).const_mul 2
    apply d.congr_deriv
    dsimp [D]
    ring

/-- The sensitivity of action is bounded by the existing action and the flight time
when the relative change of arclength and the absolute change of strength are bounded. -/
theorem abs_variation_le {f w df dw : ℝ → ℝ} {a b h A B : ℝ} (ab : a ≤ b)
    (J : IntervalIntegrable (fun t => w t * √(2 * (h - f t))) volume a b)
    (T : IntervalIntegrable (fun t => w t / √(2 * (h - f t))) volume a b)
    (integrable : IntervalIntegrable (fun t => variation h (f t) (w t) (df t) (dw t)) volume a b)
    (control : ∀ t ∈ Ioo a b, 0 ≤ w t ∧ |dw t| ≤ A * w t ∧ |df t| ≤ B) :
    |∫ t in a..b, variation h (f t) (w t) (df t) (dw t)| ≤
      A * action f w a b h + B * MirrorActionEnvelope.oneWayBounceTime w f h a b := by
  let speed (t : ℝ) := √(2 * (h - f t))
  have bound (t : ℝ) (ht : t ∈ Ioo a b) :
      |variation h (f t) (w t) (df t) (dw t)| ≤ A * (w t * speed t) + B * (w t / speed t) := by
    obtain ⟨pos, arc, field⟩ := control t ht
    have v : 0 ≤ speed t := sqrt_nonneg _
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg pos, abs_of_nonneg v]
    calc
      _ ≤ A * w t * speed t + (w t * B) / speed t :=
        add_le_add (mul_le_mul_of_nonneg_right arc v)
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left field pos) v)
      _ = _ := by ring
  have mono := intervalIntegral.integral_mono_on_of_le_Ioo ab integrable.abs
    ((J.const_mul A).add (T.const_mul B)) bound
  apply (intervalIntegral.abs_integral_le_integral_abs ab).trans
  apply mono.trans_eq
  rw [intervalIntegral.integral_add (J.const_mul A) (T.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

end PlasmaLean.Kinetic.MirrorActionVariation
