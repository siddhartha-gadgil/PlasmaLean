/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorBounceTime
public import PlasmaLean.Theory.Kinetic.MirrorHeightBand
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Lower bounds on one-way flight time from speed, length and action -/

public section
noncomputable section
open Set MeasureTheory
namespace PlasmaLean.Kinetic.MirrorActionEnvelope

/-- A lower bound on arclength density and an upper bound on speed bound
the entire mirror-to-mirror time, including the two singular endpoints. -/
theorem LaunchWell.time_lower {f w : ℝ → ℝ} {c h l r m v : ℝ}
    (well : LaunchWell f c h l r) (hm : 0 ≤ m)
    (density : ∀ t ∈ Ioo l r, m ≤ w t)
    (speed : ∀ t ∈ Ioo l r, Real.sqrt (2 * (h - f t)) ≤ v)
    (finite : IntervalIntegrable (fun t => w t / Real.sqrt (2 * (h - f t))) volume l r) :
    (r - l) * (m / v) ≤ oneWayBounceTime w f h l r := by
  have pointwise (t : ℝ) (ht : t ∈ Ioo l r) :
      m / v ≤ w t / Real.sqrt (2 * (h - f t)) := by
    have pos := Real.sqrt_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2)
      (sub_pos.mpr (well.accessible t ht)))
    exact (div_le_div_of_nonneg_left hm pos (speed t ht)).trans
      (div_le_div_of_nonneg_right (density t ht) pos.le)
  simpa [oneWayBounceTime, mul_div_assoc] using intervalIntegral.integral_mono_on_of_le_Ioo
    (well.left_lt.trans well.lt_right).le intervalIntegrable_const finite pointwise

/-- The action and reciprocal-speed integral on any common passage bound its
arclength by Cauchy–Schwarz. The clock speed may tend to zero at either end. -/
theorem length_sq_le_action_mul_time {w v : ℝ → ℝ} {l r : ℝ} (order : l ≤ r)
    (density : ∀ t ∈ Ioo l r, 0 ≤ w t) (speed : ∀ t ∈ Ioo l r, 0 < v t)
    (lengthInt : IntervalIntegrable w volume l r)
    (actionInt : IntervalIntegrable (fun t => w t * v t) volume l r)
    (timeInt : IntervalIntegrable (fun t => w t / v t) volume l r)
    (positiveAction : 0 < ∫ t in l..r, w t * v t) :
    (∫ t in l..r, w t) ^ 2 ≤ (∫ t in l..r, w t * v t) * ∫ t in l..r, w t / v t := by
  let L := ∫ t in l..r, w t
  let J := ∫ t in l..r, w t * v t
  let T := ∫ t in l..r, w t / v t
  have bound (k : ℝ) : 2 * k * L - k ^ 2 * J ≤ T := by
    have cmp (t) (ht : t ∈ Ioo l r) :
        2 * k * w t - k ^ 2 * (w t * v t) ≤ w t / v t := by
      apply (le_div_iff₀ (speed t ht)).mpr
      nlinarith [mul_nonneg (density t ht) (sq_nonneg (1 - k * v t))]
    have integrated := intervalIntegral.integral_mono_on_of_le_Ioo order
      ((lengthInt.const_mul (2 * k)).sub (actionInt.const_mul (k ^ 2))) timeInt cmp
    rwa [intervalIntegral.integral_sub (lengthInt.const_mul _) (actionInt.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at integrated
  have Jpos : 0 < J := positiveAction
  have best := bound (L / J)
  have eq : 2 * (L / J) * L - (L / J) ^ 2 * J = L ^ 2 / J := by
    field_simp
    ring
  rw [eq] at best
  exact (div_le_iff₀ Jpos).mp best |>.trans_eq (mul_comm T J)

/-- A core speed estimate and an inverse-square-root estimate at the mirror
give a quantitative upper bound for the entire half-passage. -/
theorem half_time_upper {g : ℝ → ℝ} {a s r C D : ℝ} (as' : a ≤ s) (sr : s ≤ r)
    (finite : IntervalIntegrable g volume a r) (core : ∀ t ∈ Ioo a s, g t ≤ C)
    (collar : ∀ t ∈ Ioo s r, g t ≤ D / Real.sqrt (r - t)) :
    (∫ t in a..r, g t) ≤ (s - a) * C + 2 * D * Real.sqrt (r - s) := by
  have left := finite.mono_set (by rw [uIcc_of_le as', uIcc_of_le (as'.trans sr)]
                                   exact Icc_subset_Icc_right sr)
  have right := finite.mono_set (by rw [uIcc_of_le sr, uIcc_of_le (as'.trans sr)]
                                    exact Icc_subset_Icc_left as')
  let e := -(1 / 2 : ℝ)
  have major : IntervalIntegrable (fun t : ℝ => (r - t) ^ e) volume s r := by
    simpa [e] using (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r - s)
      (r := e) (by norm_num [e])).comp_sub_left r |>.symm
  have hcore := intervalIntegral.integral_mono_on_of_le_Ioo as' left intervalIntegrable_const core
  have bound (t : ℝ) (ht : t ∈ Ioo s r) : g t ≤ D * (r - t) ^ e := by
    rw [show e = -(1 / 2 : ℝ) from rfl, Real.rpow_neg (sub_nonneg.mpr ht.2.le),
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    exact collar t ht
  have hwing := intervalIntegral.integral_mono_on_of_le_Ioo sr right (major.const_mul D) bound
  have ip : (∫ t in s..r, (r - t) ^ e) = 2 * Real.sqrt (r - s) := by
    rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ e), sub_self,
      integral_rpow (Or.inl (by norm_num [e]))]
    norm_num [e, ← Real.sqrt_eq_rpow]
    ring
  rw [intervalIntegral.integral_const_mul, ip] at hwing
  rw [← intervalIntegral.integral_add_adjacent_intervals left right]
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hcore
  linarith

/-- Between the lower-height and upper-height mirrors the displacement estimate
for the inverse branch bounds the inverse speed by an inverse square root. -/
theorem branch_collar_time_bound {f : ℝ → ℝ} {a b L U k D : ℝ}
    (branch : MirrorHeightBand.Branch f a b L U k) {h : Icc L U} (lo : L ≤ U)
    (hk : 0 < k) (hL : 0 ≤ L) (hD : 0 ≤ D) (factor : (h : ℝ) ≤ k * D ^ 2)
    {t : ℝ} (ht : t ∈ Ioo (branch.time ⟨L, le_rfl, lo⟩) (branch.time h))
    (ha : 0 ≤ a) :
    (1 : ℝ) / Real.sqrt (2 * ((h : ℝ) - f t)) ≤ D / Real.sqrt (branch.time h - t) := by
  have low := branch.interior_time ⟨L, le_rfl, lo⟩
  have high := branch.interior_time h
  have fl := branch.after ⟨L, le_rfl, lo⟩ t ⟨ht.1, ht.2.le.trans high.2.le⟩
  have fh := branch.before h t ⟨ha.trans (low.1.trans ht.1).le, ht.2⟩
  let j : Icc L U := ⟨f t, fl.le, fh.le.trans h.2.2⟩
  have eq := branch.unique_time j t ⟨(low.1.trans ht.1).le, (ht.2.trans high.2).le⟩ rfl
  have sep := branch.displacement h j
  rw [← eq, abs_of_pos (sub_pos.mpr ht.2)] at sep
  change k * (branch.time h - t) ≤ |(h : ℝ) ^ 2 - (f t) ^ 2| at sep
  have fs : 0 ≤ f t := hL.trans fl.le
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ fs fh.le 2))] at sep
  have delta : branch.time h - t ≤ D ^ 2 * (2 * ((h : ℝ) - f t)) := by
    apply le_of_mul_le_mul_left _ hk
    nlinarith [mul_nonneg (sub_nonneg.mpr factor) (sub_nonneg.mpr fh.le), sq_nonneg (h - f t)]
  have gpos : 0 < 2 * ((h : ℝ) - f t) := by linarith
  have dt := sub_pos.mpr ht.2
  have sq := Real.sqrt_le_sqrt delta
  rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD] at sq
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr gpos) (Real.sqrt_pos.mpr dt)).mpr (by simpa using sq)

end PlasmaLean.Kinetic.MirrorActionEnvelope
