/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorSublevelAction

/-!
# Finite sublevel-length certificates for the bounce action

On each parallel-speed interval the arclength profile is nonincreasing.
Endpoint length bounds suffice to enclose the action, even for wells with
plateaus. The largest speed step times the total drop bounds the gap between
the two exact endpoint sums.
-/

@[expose] public section
noncomputable section

open MeasureTheory Real Set
namespace PlasmaLean.Kinetic.MirrorSublevelAction

/-- Sum the widths of the first `n` speed panels times their supplied heights. -/
def panelSum (v height : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (v (i + 1) - v i) * height i

/-- Lower and upper rectangle sums for an antitone profile. The supplied node
heights may be certified inequalities rather than exact function values. -/
theorem integral_between_panel_sums {f : ℝ → ℝ} {v lo hi : ℕ → ℝ} {n : ℕ}
    (grid : Monotone v) (decreasing : AntitoneOn f (Icc (v 0) (v n)))
    (lo_ok : ∀ i < n, lo i ≤ f (v (i + 1))) (hi_ok : ∀ i < n, f (v i) ≤ hi i) :
    panelSum v lo n ≤ (∫ s in v 0..v n, f s) ∧
      (∫ s in v 0..v n, f s) ≤ panelSum v hi n := by
  have cell (i : ℕ) (h : i < n) :
      AntitoneOn f (Icc (v i) (v (i + 1))) :=
    decreasing.mono (Icc_subset_Icc (grid (Nat.zero_le i)) (grid h))
  have ordered (i : ℕ) : v i ≤ v (i + 1) := grid (Nat.le_succ i)
  have integ (i : ℕ) (h : i < n) : IntervalIntegrable f volume (v i) (v (i + 1)) :=
    (show AntitoneOn f (uIcc (v i) (v (i + 1))) by
      rw [uIcc_of_le (ordered i)]; exact cell i h).intervalIntegrable
  rw [← intervalIntegral.sum_integral_adjacent_intervals integ]
  constructor
  · apply Finset.sum_le_sum
    intro i hi'
    have hn := Finset.mem_range.mp hi'
    have bound := intervalIntegral.integral_mono_on (μ := volume) (ordered i)
      (intervalIntegrable_const (b := v (i + 1))) (integ i hn)
      (fun x hx => (lo_ok i hn).trans (cell i hn hx (right_mem_Icc.mpr (ordered i)) hx.2))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using bound
  · apply Finset.sum_le_sum
    intro i hi'
    have hn := Finset.mem_range.mp hi'
    have bound := intervalIntegral.integral_mono_on (μ := volume) (ordered i) (integ i hn)
      (intervalIntegrable_const (b := v (i + 1)))
      (fun x hx => (cell i hn (left_mem_Icc.mpr (ordered i)) hx hx.1).trans (hi_ok i hn))
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using bound

/-- Maximal width times total vertical drop bounds the exact endpoint-sum gap. -/
theorem panel_gap_le {v y : ℕ → ℝ} {n : ℕ} {mesh : ℝ}
    (width : ∀ i < n, v (i + 1) - v i ≤ mesh) (drop : ∀ i < n, y (i + 1) ≤ y i) :
    panelSum v y n - panelSum v (fun i => y (i + 1)) n ≤ mesh * (y 0 - y n) := by
  unfold panelSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n, mesh * (y i - y (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub]
      exact mul_le_mul_of_nonneg_right (width i (Finset.mem_range.mp hi))
        (sub_nonneg.mpr (drop i (Finset.mem_range.mp hi)))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Finset.sum_sub_distrib, sub_neg_eq_add, neg_sub] using
        congrArg Neg.neg (Finset.sum_range_sub y n)

/-- A common additive error in the panel heights accumulates over the exact
total width of the integration interval. -/
theorem panelSum_add_const (v y : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    panelSum v (fun i => y i + c) n = panelSum v y n + (v n - v 0) * c := by
  simp only [panelSum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_range_sub]

/-- Finite sublevel certificate in the existing one-passage action normalization.
Only the two endpoint inequalities per cell need field-line data. -/
theorem action_between_panel_sums {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {B : X → ℝ} (hB : AEMeasurable B μ) {base h : ℝ}
    (floorB : ∀ᵐ x ∂μ, base ≤ B x) {v lo hi : ℕ → ℝ} {n : ℕ}
    (grid : Monotone v) (start : v 0 = 0) (stop : v n = √(2 * (h - base)))
    (lo_ok : ∀ i < n, lo i ≤ sublevelLength μ B (h - (v (i + 1)) ^ 2 / 2))
    (hi_ok : ∀ i < n, sublevelLength μ B (h - (v i) ^ 2 / 2) ≤ hi i) :
    panelSum v lo n ≤ action μ B h ∧ action μ B h ≤ panelSum v hi n := by
  have anti := (antitone_sublevel_speed μ B h).mono
    (show Icc (v 0) (v n) ⊆ Ici 0 by rw [start]; exact Icc_subset_Ici_self)
  have bounds := integral_between_panel_sums grid anti lo_ok hi_ok
  rw [intervalIntegral.integral_of_le (grid (Nat.zero_le n)), start, stop] at bounds
  rwa [action_eq_integral_sublevel μ hB floorB]

/-- Discrepancies at finitely many thresholds suffice if a mesh error is
allowed. Only the reference well's total drop in sublevel length enters that
error. The field-line parameter spaces and arclength measures may differ. -/
theorem sampled_action_difference_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {B : X → ℝ} {C : Y → ℝ} (hB : AEMeasurable B μ) (hC : AEMeasurable C ν)
    {base h : ℝ} (floorB : ∀ᵐ x ∂μ, base ≤ B x) (floorC : ∀ᵐ x ∂ν, base ≤ C x)
    {v : ℕ → ℝ} {n : ℕ} {mesh ε : ℝ} (grid : Monotone v) (start : v 0 = 0)
    (stop : v n = √(2 * (h - base))) (width : ∀ i < n, v (i + 1) - v i ≤ mesh)
    (samples : ∀ i ≤ n, |sublevelLength μ B (h - (v i) ^ 2 / 2) -
      sublevelLength ν C (h - (v i) ^ 2 / 2)| ≤ ε) :
    |action μ B h - action ν C h| ≤ ε * v n + mesh *
      (sublevelLength ν C h - sublevelLength ν C (h - (v n) ^ 2 / 2)) := by
  let y := fun i => sublevelLength ν C (h - (v i) ^ 2 / 2)
  have ref := action_between_panel_sums ν hC floorC grid start stop
    (lo := fun i => y (i + 1)) (hi := y) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have cmp := action_between_panel_sums μ hB floorB grid start stop
    (lo := fun i => y (i + 1) + -ε) (hi := fun i => y i + ε)
    (fun i hi => by dsimp [y]; linarith [(abs_le.mp (samples (i + 1) hi)).1])
    (fun i hi => by dsimp [y]; linarith [(abs_le.mp (samples i hi.le)).2])
  have nonneg (i : ℕ) : v i ∈ Ici 0 := start ▸ grid (Nat.zero_le i)
  have gap := panel_gap_le (y := y) width (fun i _ =>
    antitone_sublevel_speed ν C h (nonneg i) (nonneg _) (grid (Nat.le_succ i)))
  have lo_shift := panelSum_add_const v (fun i => y (i + 1)) n (-ε)
  have hi_shift := panelSum_add_const v y n ε
  have y₀ : y 0 = sublevelLength ν C h := by simp [y, start]
  change |action μ B h - action ν C h| ≤ ε * v n + mesh * (_ - y n)
  rw [← y₀]
  rw [lo_shift, hi_shift, start, sub_zero] at cmp
  exact abs_le.mpr ⟨by linarith only [cmp.1, ref.2, gap], by linarith only [cmp.2, ref.1, gap]⟩

/-- On a unit-length well, the field strengths 3/2 and 7/8 have identical
sublevel lengths at 0 and 2. Their actions at height 2 differ by 1/2. -/
theorem two_thresholds_miss_action {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] :
    (∀ b ∈ ({0, 2} : Set ℝ), sublevelLength μ (fun _ => 3 / 2) b =
      sublevelLength μ (fun _ => 7 / 8) b) ∧
      action μ (fun _ => 3 / 2) 2 = 1 ∧ action μ (fun _ => 7 / 8) 2 = 3 / 2 := by
  constructor
  · intro b hb
    rcases hb with rfl | hb
    · norm_num [sublevelLength]
    · rw [mem_singleton_iff] at hb
      subst b
      norm_num [sublevelLength]
  · have root : √(2 * (2 - (7 / 8 : ℝ))) = 3 / 2 := by
      rw [show 2 * (2 - (7 / 8 : ℝ)) = (3 / 2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    simp only [action, integral_const, probReal_univ, smul_eq_mul, one_mul, root, and_true]
    norm_num

end PlasmaLean.Kinetic.MirrorSublevelAction
