/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorProfileStability

/-! # Action stability from regularity near the mirror height

On the deep part of a well the clipped parallel speed has a uniform
Lipschitz estimate. Only a collar of the mirror height needs control of the
arclength in field-strength bands. A flat or critical bottom is allowed.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorActionCollar
open MeasureTheory Real Set MirrorSublevelAction MirrorProfileStability

variable {X : Type*} [MeasurableSpace X]

/-- Away from the reference mirror height, rationalizing the two speeds gives a
linear perturbation estimate even when the perturbed speed is clipped. -/
theorem deep_speed_bound {b c h w δ : ℝ} (hw : 0 < w) (deep : b ≤ h - w)
    (near : |b - c| ≤ δ) :
    |√(2 * (h - b)) - √(2 * (h - c))| ≤ 2 * δ / √(2 * w) := by
  let r := √(2 * (h - b))
  let s := √(2 * (h - c))
  have rr : r ^ 2 = 2 * (h - b) := Real.sq_sqrt (by linarith)
  have ss : s ^ 2 = max (2 * (h - c)) 0 := Real.sq_sqrt'
  have rpos : √(2 * w) ≤ r := Real.sqrt_le_sqrt (by linarith)
  have diff : |r ^ 2 - s ^ 2| ≤ 2 * δ := by
    rw [rr, ss]
    rcases le_total 0 (2 * (h - c)) with hpos | hneg
    · rw [max_eq_left hpos]
      exact abs_le.mpr ⟨by linarith only [(abs_le.mp near).2],
        by linarith only [(abs_le.mp near).1]⟩
    · rw [max_eq_right hneg, sub_zero, abs_of_nonneg (by linarith)]
      linarith only [hneg, (abs_le.mp near).1]
  apply (le_div_iff₀ (Real.sqrt_pos.2 (by linarith))).mpr
  calc
    _ ≤ |r - s| * (r + s) := mul_le_mul_of_nonneg_left
      (by linarith only [rpos, Real.sqrt_nonneg (2 * (h - c))]) (abs_nonneg _)
    _ = |r ^ 2 - s ^ 2| := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (show 0 ≤ r + s from
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)), mul_comm]
    _ ≤ _ := diff

private theorem speed_integrable (μ : Measure X) [IsFiniteMeasure μ] {B : X → ℝ}
    (hB : AEMeasurable B μ) {base h : ℝ} (floorB : ∀ᵐ x ∂μ, base ≤ B x) :
    Integrable (fun x => √(2 * (h - B x))) μ := by
  apply Integrable.of_bound (by fun_prop) (√(2 * (h - base)))
  filter_upwards [floorB] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The near-height bands may be bounded on the whole reference well. On the
deeper region only its total arclength enters. The collar floor is h-w-δ for
both profiles, so the field-distribution hypothesis views only (h-w-2δ,h+δ]. -/
theorem action_of_collar (μ : Measure X) [IsFiniteMeasure μ] {B C : X → ℝ}
    (hB : Measurable B) (hC : AEMeasurable C μ) {base h w δ ε : ℝ}
    (hw : 0 < w) (hd : 0 ≤ δ) (floorB : ∀ᵐ x ∂μ, base ≤ B x)
    (floorC : ∀ᵐ x ∂μ, base ≤ C x) (near : ∀ᵐ x ∂μ, |B x - C x| ≤ δ)
    (bands : ∀ b ∈ Icc (h - w - δ) h,
      bandMass μ B (b - δ) b ≤ ε ∧ bandMass μ B b (b + δ) ≤ ε) :
    |action μ B h - action μ C h| ≤
      (2 * δ / √(2 * w)) * μ.real {x | B x ≤ h - w} + ε * √(2 * (w + δ)) := by
  let S : Set X := {x | B x ≤ h - w}
  have ms : MeasurableSet S := hB measurableSet_Iic
  have nearS : ∀ᵐ x ∂μ.restrict S, |B x - C x| ≤ δ := ae_restrict_of_ae near
  have nearT : ∀ᵐ x ∂μ.restrict Sᶜ, |B x - C x| ≤ δ := ae_restrict_of_ae near
  have iB := speed_integrable (h := h) μ hB.aemeasurable floorB
  have iC := speed_integrable (h := h) μ hC floorC
  have deep : |action (μ.restrict S) B h - action (μ.restrict S) C h| ≤
      (2 * δ / √(2 * w)) * μ.real S := by
    unfold action
    rw [← integral_sub iB.restrict iC.restrict, ← measureReal_restrict_apply_univ (μ := μ) S]
    apply (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le_const (μ := μ.restrict S) ?_)
    filter_upwards [ae_restrict_mem ms, nearS] with x xs xn
    simpa only [Real.norm_eq_abs] using deep_speed_bound hw xs xn
  have floors : ∀ᵐ x ∂μ.restrict Sᶜ, h - w - δ ≤ B x ∧ h - w - δ ≤ C x := by
    filter_upwards [ae_restrict_mem ms.compl, nearT] with x xt xn
    have above : h - w < B x := lt_of_not_ge xt
    exact ⟨by linarith, by linarith only [above, (abs_le.mp xn).2]⟩
  have small (a b : ℝ) : bandMass (μ.restrict Sᶜ) B a b ≤ bandMass μ B a b :=
    ENNReal.toReal_mono (measure_ne_top μ _) (Measure.restrict_le_self _)
  have collar := action_of_band_bounds (μ.restrict Sᶜ) hB.aemeasurable hC.restrict
    (floors.mono fun _ hx => hx.1) (floors.mono fun _ hx => hx.2) (by linarith : h - w - δ ≤ h)
    nearT (fun b hb => ⟨(small _ _).trans (bands b hb).1, (small _ _).trans (bands b hb).2⟩)
  have sumB : action (μ.restrict S) B h + action (μ.restrict Sᶜ) B h = action μ B h :=
    integral_add_compl ms iB
  have sumC : action (μ.restrict S) C h + action (μ.restrict Sᶜ) C h = action μ C h :=
    integral_add_compl ms iC
  rw [← sumB, ← sumC, add_sub_add_comm]
  exact (abs_add_le ..).trans (add_le_add deep
    (by simpa only [show h - (h - w - δ) = w + δ by ring] using collar))

/-- Finite regular branches need to cover only the strengths near the mirror.
The reference arclength below that collar can include arbitrary critical points. -/
theorem action_of_collar_branches {ι : Type*} [Fintype ι] {region : Set ℝ}
    (meas : MeasurableSet region) (finite : volume region ≠ ⊤)
    {B C : ℝ → ℝ} (hB : Measurable B) (hC : AEMeasurable C (volume.restrict region))
    {base h w δ : ℝ} (hw : 0 < w) (hd : 0 ≤ δ)
    (floorB : ∀ᵐ x ∂volume.restrict region, base ≤ B x)
    (floorC : ∀ᵐ x ∂volume.restrict region, base ≤ C x)
    (near : ∀ᵐ x ∂volume.restrict region, |B x - C x| ≤ δ)
    (D : ι → Set ℝ) (m : ι → ℝ) (positive : ∀ i, 0 < m i)
    (sep : ∀ i, SlopeSeparatedOn B (D i) (m i))
    (cover : ∀ x ∈ region, B x ∈ Ioc (h - w - 2 * δ) (h + δ) → ∃ i, x ∈ D i) :
    |action (volume.restrict region) B h - action (volume.restrict region) C h| ≤
      (2 * δ / √(2 * w)) * (volume.restrict region).real {x | B x ≤ h - w}
      + (δ * ∑ i, (m i)⁻¹) * √(2 * (w + δ)) := by
  let _ : IsFiniteMeasure (volume.restrict region) := isFiniteMeasure_restrict.mpr finite
  apply action_of_collar _ hB hC hw hd floorB floorC near
  intro b hb
  have band {u v : ℝ} (huv : u ≤ v) (low : h - w - 2 * δ ≤ u) (high : v ≤ h + δ) :
      bandMass (volume.restrict region) B u v ≤ (v - u) * ∑ i, (m i)⁻¹ :=
    bandMass_of_branches D m meas huv positive sep fun x hx hx' =>
      cover x hx ⟨low.trans_lt hx'.1, hx'.2.trans high⟩
  have lower := band (u := b - δ) (v := b) (by linarith) (by linarith [hb.1]) (by linarith [hb.2])
  have upper := band (u := b) (v := b + δ) (by linarith) (by linarith [hb.1]) (by linarith [hb.2])
  exact ⟨by simpa using lower, by simpa using upper⟩

end PlasmaLean.Kinetic.MirrorActionCollar
