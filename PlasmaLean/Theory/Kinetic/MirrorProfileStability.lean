/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorSublevelAction
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Stability under perturbing a mirror-well profile

The two comparisons at a fixed threshold use separate half-open field intervals
of width δ. A monotone arclength branch controls the mass in each interval by
its inverse slope. Neither smooth isolated turning points nor a density for the
distribution of field strength are needed for the inclusion inequalities.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorProfileStability
open MeasureTheory Real Set MirrorSublevelAction

variable {X : Type*} [MeasurableSpace X]

/-- Mass of a field-strength band open at its lower endpoint and closed at its upper one. -/
def bandMass (μ : Measure X) (B : X → ℝ) (a b : ℝ) : ℝ := μ.real (B ⁻¹' Ioc a b)

/-- An almost-everywhere uniform perturbation translates the two closed sublevel sets. -/
theorem sublevel_sandwich (μ : Measure X) [IsFiniteMeasure μ] {B C : X → ℝ} {δ : ℝ}
    (near : ∀ᵐ x ∂μ, |B x - C x| ≤ δ) (b : ℝ) :
    sublevelLength μ B (b - δ) ≤ sublevelLength μ C b ∧
      sublevelLength μ C b ≤ sublevelLength μ B (b + δ) := by
  constructor
  · apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [near] with x hx
    intro hb
    linarith only [hb, (abs_le.mp hx).1]
  · apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono_ae
    filter_upwards [near] with x hx
    intro hb
    linarith only [hb, (abs_le.mp hx).2]

/-- The single half-open band suffices for an increase in a closed sublevel length. -/
theorem sublevel_increment_le (μ : Measure X) [IsFiniteMeasure μ] (B : X → ℝ) (a b : ℝ) :
    sublevelLength μ B b ≤ sublevelLength μ B a + bandMass μ B a b := by
  have cover : {x | B x ≤ b} ⊆ {x | B x ≤ a} ∪ (B ⁻¹' Ioc a b) := by
    intro x hx
    by_cases h : B x ≤ a
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_not_ge h, hx⟩
  exact (measureReal_mono cover (measure_ne_top μ _)).trans (measureReal_union_le _ _)

/-- A perturbation costs the larger of two one-sided band masses, preserving all atoms. -/
theorem sublevel_difference_le (μ : Measure X) [IsFiniteMeasure μ] {B C : X → ℝ} {δ : ℝ}
    (near : ∀ᵐ x ∂μ, |B x - C x| ≤ δ) (b : ℝ) :
    |sublevelLength μ B b - sublevelLength μ C b| ≤
      max (bandMass μ B (b - δ) b) (bandMass μ B b (b + δ)) := by
  obtain ⟨low, high⟩ := sublevel_sandwich μ near b
  apply abs_le.mpr
  constructor
  · linarith only [high, sublevel_increment_le μ B b (b + δ),
      le_max_right (bandMass μ B (b - δ) b) (bandMass μ B b (b + δ))]
  · linarith only [low, sublevel_increment_le μ B (b - δ) b,
      le_max_left (bandMass μ B (b - δ) b) (bandMass μ B b (b + δ))]

/-- Field-band estimates on the reference profile alone control action perturbations. -/
theorem action_of_band_bounds (μ : Measure X) [IsFiniteMeasure μ] {B C : X → ℝ}
    (hB : AEMeasurable B μ) (hC : AEMeasurable C μ) {base h δ ε : ℝ}
    (floorB : ∀ᵐ x ∂μ, base ≤ B x) (floorC : ∀ᵐ x ∂μ, base ≤ C x) (hh : base ≤ h)
    (near : ∀ᵐ x ∂μ, |B x - C x| ≤ δ)
    (bands : ∀ b ∈ Icc base h, bandMass μ B (b - δ) b ≤ ε ∧ bandMass μ B b (b + δ) ≤ ε) :
    |action μ B h - action μ C h| ≤ ε * √(2 * (h - base)) := by
  apply action_difference_le μ μ hB hC floorB floorC hh
  intro b hb
  exact (sublevel_difference_le μ near b).trans (max_le (bands b hb).1 (bands b hb).2)

/-- An arbitrarily small constant perturbation can shift all mass across one threshold. -/
theorem flat_profile_jump (μ : Measure X) [IsProbabilityMeasure μ] {δ : ℝ} (hd : 0 < δ) :
    sublevelLength μ (fun _ => 0) 0 - sublevelLength μ (fun _ => δ) 0 = 1 := by
  simp [sublevelLength, not_le.mpr hd]

/-- Absolute secant separation. The coordinate may be arclength, angle, or another
one-dimensional parameter; the slope and displacement use the same coordinate. -/
def SlopeSeparatedOn (B : ℝ → ℝ) (D : Set ℝ) (m : ℝ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, m * |x - y| ≤ |B x - B y|

/-- A uniform signed derivative bound on a convex branch supplies secant separation
on its closure. A derivative estimate at just one contact does not appear here. -/
theorem separated_of_derivative {B : ℝ → ℝ} {D : Set ℝ} {m : ℝ}
    (domain : Convex ℝ D) (continuous : ContinuousOn B D)
    (diff : DifferentiableOn ℝ B (interior D))
    (slopes : (∀ x ∈ interior D, m ≤ deriv B x) ∨ (∀ x ∈ interior D, deriv B x ≤ -m)) :
    SlopeSeparatedOn B D m := by
  have ordered {x y : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≤ y) :
      m * (y - x) ≤ |B y - B x| := by
    rcases slopes with inc | dec
    · exact (domain.mul_sub_le_image_sub_of_le_deriv continuous diff inc x hx y hy hxy).trans
        (le_abs_self _)
    · have s := domain.image_sub_le_mul_sub_of_deriv_le continuous diff dec x hx y hy hxy
      linarith only [s, neg_le_abs (B y - B x)]
  intro x hx y hy
  rcases le_total y x with h | h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr h)] using ordered hy hx h
  · rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr h), abs_sub_comm (B x) (B y)]
    exact ordered hx hy h

/-- A fixed reference slope bounds the displacement of any actual perturbed root.
The perturbation itself only needs a value estimate at that root. -/
theorem root_displacement {B C : ℝ → ℝ} {D : Set ℝ} {m δ b c x y : ℝ} (hm : 0 < m)
    (sep : SlopeSeparatedOn B D m) (hx : x ∈ D) (hy : y ∈ D)
    (rootB : B x = b) (rootC : C y = c) (near : |B y - C y| ≤ δ) :
    |x - y| ≤ (|b - c| + δ) / m := by
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  have tail := abs_sub_le (B x) (C y) (B y)
  rw [abs_sub_comm (C y) (B y), rootB, rootC] at tail
  rw [rootC] at near
  exact (sep x hx y hy).trans (by simpa [rootB] using tail.trans (add_le_add_right near _))

/-- Surviving endpoint margins guarantee a perturbed root, and every such root
is localized by the reference slope. Only continuity is assumed of C. -/
theorem perturbed_roots {B C : ℝ → ℝ} {a b x h δ m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (sep : SlopeSeparatedOn B (Icc a b) m) (hx : x ∈ Icc a b) (root : B x = h)
    (cont : ContinuousOn C (Icc a b)) (near : ∀ t ∈ Icc a b, |B t - C t| ≤ δ)
    (margin : (B a + δ ≤ h ∧ h ≤ B b - δ) ∨ (B b + δ ≤ h ∧ h ≤ B a - δ)) :
    (∃ y ∈ Icc a b, C y = h) ∧ ∀ y ∈ Icc a b, C y = h → |x - y| ≤ δ / m := by
  have left := abs_le.mp (near a (left_mem_Icc.mpr hab))
  have right := abs_le.mp (near b (right_mem_Icc.mpr hab))
  constructor
  · rcases margin with ⟨lo, hi⟩ | ⟨lo, hi⟩
    · exact intermediate_value_Icc hab cont
        (show h ∈ Icc (C a) (C b) from ⟨by linarith, by linarith⟩)
    · exact intermediate_value_Icc' hab cont
        (show h ∈ Icc (C b) (C a) from ⟨by linarith, by linarith⟩)
  · intro y hy equal
    simpa using root_displacement hm sep hx hy root equal (near y hy)

/-- Convert an error in field strength to root motion when the certified slope
controls squared field strength in the chosen coordinate. -/
theorem squared_field_root_displacement {B C : ℝ → ℝ} {D : Set ℝ} {m δ h x y : ℝ}
    (hm : 0 < m) (sep : SlopeSeparatedOn (fun t => (B t) ^ 2) D m)
    (hx : x ∈ D) (hy : y ∈ D) (rootB : B x = h) (rootC : C y = h)
    (near : |B y - C y| ≤ δ) : |x - y| ≤ δ * (2 * |h| + δ) / m := by
  have adapt : |B y + C y| ≤ 2 * |h| + δ := by
    calc
      _ = |(B y - C y) + 2 * C y| := by congr 1; ring
      _ ≤ |B y - C y| + |2 * C y| := abs_add_le ..
      _ ≤ _ := by
        rw [abs_mul, rootC, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        linarith only [show |B y - h| ≤ δ by simpa only [rootC] using near]
  have sqerr : |(B y) ^ 2 - (C y) ^ 2| ≤ δ * (2 * |h| + δ) := by
    rw [sq_sub_sq, abs_mul, mul_comm |B y + C y| |B y - C y|]
    exact mul_le_mul near adapt (abs_nonneg _) ((abs_nonneg _).trans near)
  have motion := root_displacement (C := fun t => (C t) ^ 2) hm sep hx hy
    (show (B x) ^ 2 = h ^ 2 by rw [rootB]) (show (C y) ^ 2 = h ^ 2 by rw [rootC]) sqerr
  simpa using motion

/-- Sharp root displacement for an affine profile translated vertically by δ. -/
theorem affine_root_shift {m δ : ℝ} (hm : 0 < m) (hd : 0 ≤ δ) :
    m * (δ / m) - δ = 0 ∧ |(0 : ℝ) - δ / m| = δ / m := by
  constructor
  · field_simp; ring
  · simp [abs_of_nonneg (div_nonneg hd hm.le)]

/-- A single arclength branch spends at most (b-a)/m length in the field band (a,b].
Both ends may lie outside the branch's field range. -/
theorem branch_volume_le {B : ℝ → ℝ} {D : Set ℝ} {a b m : ℝ} (hm : 0 < m)
    (sep : SlopeSeparatedOn B D m) :
    volume (D ∩ B ⁻¹' Ioc a b) ≤ ENNReal.ofReal ((b - a) / m) := by
  apply (Real.volume_le_diam _).trans (Metric.ediam_le ?_)
  intro x hx y hy
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  apply (le_div_iff₀ hm).mpr
  rw [mul_comm]
  apply (sep x hx.1 y hy.1).trans
  rcases hx.2 with ⟨ax, xb⟩
  rcases hy.2 with ⟨ay, yb⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A finite cover only needs to include points whose field lies in the specified band.
Overlaps at branch boundaries are allowed. The coordinate carries Lebesgue arclength. -/
theorem bandMass_of_branches {ι : Type*} [Fintype ι] (D : ι → Set ℝ) (m : ι → ℝ)
    {region : Set ℝ} (meas : MeasurableSet region) {B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (positive : ∀ i, 0 < m i) (sep : ∀ i, SlopeSeparatedOn B (D i) (m i))
    (cover : ∀ x ∈ region, B x ∈ Ioc a b → ∃ i, x ∈ D i) :
    bandMass (volume.restrict region) B a b ≤ (b - a) * ∑ i, (m i)⁻¹ := by
  classical
  let pieces (i : ι) := D i ∩ B ⁻¹' Ioc a b
  have sub : (B ⁻¹' Ioc a b) ∩ region ⊆ ⋃ i, pieces i := by
    intro x hx
    obtain ⟨i, h⟩ := cover x hx.2 hx.1
    exact mem_iUnion.mpr ⟨i, h, hx.1⟩
  have bound := (measure_mono (μ := volume) sub).trans
    ((measure_iUnion_fintype_le volume pieces).trans
      (Finset.sum_le_sum (fun i _ => branch_volume_le (positive i) (sep i))))
  rw [bandMass, measureReal_restrict_apply' meas, measureReal_def]
  calc
    _ ≤ (∑ i, ENNReal.ofReal ((b - a) / m i)).toReal := ENNReal.toReal_mono
      (ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)).ne bound
    _ = ∑ i, (b - a) / m i := by
      rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
      exact Finset.sum_congr rfl fun i _ => ENNReal.toReal_ofReal
        (div_nonneg (sub_nonneg.mpr hab) (positive i).le)
    _ = _ := by simp [Finset.mul_sum, div_eq_mul_inv]

/-- Finite monotone arclength branches covering the probed strength window give
linear action stability. No slope estimate on the perturbed profile is required. -/
theorem action_of_branches {ι : Type*} [Fintype ι] {region : Set ℝ}
    (meas : MeasurableSet region) (finite : volume region ≠ ⊤)
    {B C : ℝ → ℝ} (hB : AEMeasurable B (volume.restrict region))
    (hC : AEMeasurable C (volume.restrict region)) {base h δ : ℝ} (hd : 0 ≤ δ) (hh : base ≤ h)
    (floorB : ∀ᵐ x ∂volume.restrict region, base ≤ B x)
    (floorC : ∀ᵐ x ∂volume.restrict region, base ≤ C x)
    (near : ∀ᵐ x ∂volume.restrict region, |B x - C x| ≤ δ)
    (D : ι → Set ℝ) (m : ι → ℝ) (positive : ∀ i, 0 < m i)
    (sep : ∀ i, SlopeSeparatedOn B (D i) (m i))
    (cover : ∀ x ∈ region, B x ∈ Ioc (base - δ) (h + δ) → ∃ i, x ∈ D i) :
    |action (volume.restrict region) B h - action (volume.restrict region) C h| ≤
      (δ * ∑ i, (m i)⁻¹) * √(2 * (h - base)) := by
  let _ : IsFiniteMeasure (volume.restrict region) := isFiniteMeasure_restrict.mpr finite
  apply action_of_band_bounds _ hB hC floorB floorC hh near
  intro b hb
  have localBand {x y : ℝ} (hxy : x ≤ y) (lower : base - δ ≤ x) (upper : y ≤ h + δ) :
      bandMass (volume.restrict region) B x y ≤ (y - x) * ∑ i, (m i)⁻¹ :=
    bandMass_of_branches D m meas hxy positive sep fun z hz hz' =>
      cover z hz ⟨lower.trans_lt hz'.1, hz'.2.trans upper⟩
  have lo := localBand (x := b - δ) (y := b) (by linarith) (by linarith [hb.1])
    (by linarith [hb.2])
  have hi := localBand (x := b) (y := b + δ) (by linarith) (by linarith [hb.1])
    (by linarith [hb.2])
  exact ⟨by simpa only [sub_sub_cancel] using lo, by simpa only [add_sub_cancel_left] using hi⟩

/-- Universal modulus of the clipped parallel speed, including thresholds with atoms. -/
theorem clipped_speed_perturbation {x y h δ : ℝ} (hd : 0 ≤ δ) (near : |x - y| ≤ δ) :
    |√(2 * (h - x)) - √(2 * (h - y))| ≤ √(2 * δ) := by
  let r := √(2 * (h - x))
  let s := √(2 * (h - y))
  have rr : r ^ 2 = max (2 * (h - x)) 0 := Real.sq_sqrt'
  have ss : s ^ 2 = max (2 * (h - y)) 0 := Real.sq_sqrt'
  have cap {a b : ℝ} (h : a ≤ b + 2 * δ) : max a 0 ≤ max b 0 + 2 * δ :=
    max_le (by linarith [le_max_left b 0]) (by linarith [le_max_right b 0])
  have rs : r ^ 2 ≤ s ^ 2 + 2 * δ := by
    rw [rr, ss]
    exact cap (by linarith only [(abs_le.mp near).1])
  have sr : s ^ 2 ≤ r ^ 2 + 2 * δ := by
    rw [rr, ss]
    exact cap (by linarith only [(abs_le.mp near).2])
  apply Real.le_sqrt_of_sq_le
  change |r - s| ^ 2 ≤ 2 * δ
  rw [sq_abs]
  rcases le_total r s with hr | hs
  · nlinarith only [sr, mul_nonneg (Real.sqrt_nonneg (2 * (h - x))) (sub_nonneg.mpr hr)]
  · nlinarith only [rs, mul_nonneg (Real.sqrt_nonneg (2 * (h - y))) (sub_nonneg.mpr hs)]

/-- A finite well with a lower field bound has a sharp square-root action modulus
even when its distribution of field strength is atomic. -/
theorem action_sqrt_bound (μ : Measure X) [IsFiniteMeasure μ] {B C : X → ℝ}
    (hB : AEMeasurable B μ) (hC : AEMeasurable C μ) {base h δ : ℝ} (hd : 0 ≤ δ)
    (floorB : ∀ᵐ x ∂μ, base ≤ B x) (floorC : ∀ᵐ x ∂μ, base ≤ C x)
    (near : ∀ᵐ x ∂μ, |B x - C x| ≤ δ) :
    |action μ B h - action μ C h| ≤ √(2 * δ) * μ.real univ := by
  have integr {F : X → ℝ} (hF : AEMeasurable F μ) (floorF : ∀ᵐ x ∂μ, base ≤ F x) :
      Integrable (fun x => √(2 * (h - F x))) μ := by
    apply Integrable.of_bound (by fun_prop) (√(2 * (h - base)))
    filter_upwards [floorF] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  unfold action
  rw [← integral_sub (integr hB floorB) (integr hC floorC)]
  apply (Real.norm_eq_abs _ ▸ norm_integral_le_of_norm_le_const (μ := μ) ?_)
  filter_upwards [near] with x hx
  simpa only [Real.norm_eq_abs] using clipped_speed_perturbation (h := h) hd hx

/-- A unit flat well shifted exactly onto the mirror height attains the square-root modulus. -/
theorem flat_action_attains (μ : Measure X) [IsProbabilityMeasure μ] {h δ : ℝ} :
    |action μ (fun _ => h - δ) h - action μ (fun _ => h) h| = √(2 * δ) := by
  simp [action, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- A label-Lipschitz field and a bounded reference band density control the action
derivative wherever that derivative exists, for the same arclength measure at all labels. -/
theorem label_derivative_le (μ : Measure X) [IsFiniteMeasure μ] (B : ℝ → X → ℝ)
    {α base h K L D : ℝ} (hL : 0 ≤ L) (hh : base ≤ h)
    (meas : ∀ β, AEMeasurable (B β) μ) (floor : ∀ β, ∀ᵐ x ∂μ, base ≤ B β x)
    (bands : ∀ a b : ℝ, a ≤ b → bandMass μ (B α) a b ≤ K * (b - a))
    (profiles : ∀ᶠ β in nhds α, ∀ᵐ x ∂μ, |B α x - B β x| ≤ L * |β - α|)
    (hd : HasDerivAt (fun β => action μ (B β) h) D α) :
    |D| ≤ (K * L) * √(2 * (h - base)) := by
  have hK : 0 ≤ K := (show 0 ≤ bandMass μ (B α) 0 1 from ENNReal.toReal_nonneg).trans
    (by simpa using bands 0 1 zero_le_one)
  apply abs_action_derivative_le (fun _ => μ) B hh (mul_nonneg hK hL) meas floor _ hd
  filter_upwards [profiles] with β near
  intro b _
  let δ := L * |β - α|
  have positive : 0 ≤ δ := mul_nonneg hL (abs_nonneg _)
  have above := bands b (b + δ) (by linarith)
  have below := bands (b - δ) b (by linarith)
  rw [add_sub_cancel_left] at above
  rw [sub_sub_cancel] at below
  rw [abs_sub_comm]
  exact (sublevel_difference_le μ near b).trans
    (by simpa only [δ, mul_assoc] using max_le below above)

end PlasmaLean.Kinetic.MirrorProfileStability
