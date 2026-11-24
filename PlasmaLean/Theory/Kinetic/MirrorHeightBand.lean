/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorProfileStability
public import PlasmaLean.Theory.Fields.TrajectorySlabObservable

/-! # First transverse mirror times as a function of height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorHeightBand

open Set MirrorProfileStability

/-- A single inverse branch on the entire closed height interval. Each root is the
first one reached from zero, is unique on the closed outer interval, and has positive slope. -/
structure Branch (f : ℝ → ℝ) (a b L U k : ℝ) where
  time : Icc L U → ℝ
  interior_time : ∀ h : Icc L U, time h ∈ Ioo a b
  hit : ∀ h : Icc L U, f (time h) = h
  before : ∀ h : Icc L U, ∀ t ∈ Ico 0 (time h), f t < h
  after : ∀ h : Icc L U, ∀ t ∈ Ioc (time h) b, (h : ℝ) < f t
  unique_time : ∀ h : Icc L U, ∀ t ∈ Icc a b, f t = h → t = time h
  transverse : ∀ h : Icc L U, ∃ v > k / (2 * (h : ℝ)), HasDerivAt f v (time h)
  ordered : StrictMono time
  displacement : ∀ h j, k * |time h - time j| ≤ |(h : ℝ) ^ 2 - (j : ℝ) ^ 2|

/-- A positive squared-field derivative controls the entire branch, including heights
whose roots happen to lie at boundaries between two numerical certificates. -/
theorem exists_branch {f : ℝ → ℝ} {a b L U k : ℝ} (ha : 0 ≤ a) (ab : a < b)
    (hL : 0 < L) (hk : 0 < k) (nonneg : ∀ t, 0 ≤ f t) (cont : ContinuousOn f (Icc a b))
    (early : ∀ t ∈ Icc 0 a, f t < L)
    (last : ∃ q ∈ Ioo a b, f q = U)
    (slope : ∀ t ∈ Ioo a b, ∃ v > k, HasDerivAt (fun u => (f u) ^ 2) v t) :
    Nonempty (Branch f a b L U k) := by
  have cs : ContinuousOn (fun t => (f t) ^ 2) (Icc a b) := (continuous_pow 2).comp_continuousOn cont
  have incSq : StrictMonoOn (fun t => (f t) ^ 2) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) cs
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, lower, d⟩ := slope t ht
    rw [d.deriv]
    exact hk.trans lower
  have inc : StrictMonoOn f (Icc a b) := by
    intro t ht u hu tu
    have sq := incSq ht hu tu
    change (f t) ^ 2 < (f u) ^ 2 at sq
    by_contra! contra
    exact sq.not_ge (pow_le_pow_left₀ (nonneg u) contra 2)
  obtain ⟨q, hq, eq⟩ := last
  have high := inc (Ioo_subset_Icc_self hq) (right_mem_Icc.mpr ab.le) hq.2
  rw [eq] at high
  have roots (h : Icc L U) : ∃ t ∈ Ioo a b, f t = h ∧ ∀ u ∈ Ico 0 t, f u < h :=
    Fields.TrajectorySlabs.first_contact_in_bracket ha ab
      (fun u hu => (early u hu).trans_le h.2.1) cont (h.2.2.trans_lt high)
  choose time member hit before using roots
  have sep : SlopeSeparatedOn (fun t => (f t) ^ 2) (Icc a b) k := by
    apply separated_of_derivative (convex_Icc _ _) cs
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨v, _, d⟩ := slope x hx
      exact d.differentiableAt.differentiableWithinAt
    · left
      intro x hx
      rw [interior_Icc] at hx
      obtain ⟨v, hv, d⟩ := slope x hx
      rw [d.deriv]
      exact hv.le
  refine ⟨⟨time, member, hit, before, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h x hx
    rw [← hit h]
    exact inc (Ioo_subset_Icc_self (member h)) ⟨(member h).1.le.trans hx.1.le, hx.2⟩ hx.1
  · intro h x hx hx'
    exact inc.injOn hx (Ioo_subset_Icc_self (member h)) (hx'.trans (hit h).symm)
  · intro h
    obtain ⟨v, hv, d⟩ := slope _ (member h)
    have hp : 0 < (h : ℝ) := hL.trans_le h.2.1
    refine ⟨v / (2 * (h : ℝ)), div_lt_div_of_pos_right hv (by positivity), ?_⟩
    have ne : f (time h) ≠ 0 := (hit h).trans_ne hp.ne'
    simpa only [Real.sqrt_sq (nonneg _), hit, Real.sqrt_sq hp.le] using
      d.sqrt (pow_ne_zero 2 ne)
  · intro h j lt'
    apply (inc.lt_iff_lt (Ioo_subset_Icc_self (member h)) (Ioo_subset_Icc_self (member j))).mp
    simpa only [hit] using (show (h : ℝ) < (j : ℝ) from lt')
  · intro h j
    simpa only [hit] using sep _ (Ioo_subset_Icc_self (member h)) _ (Ioo_subset_Icc_self (member j))

/-- The first mirror time depends Lipschitz continuously on the physical field height.
The factor 2U converts the certified separation of squared strengths. -/
theorem Branch.time_lipschitz {f : ℝ → ℝ} {a b L U k : ℝ} (branch : Branch f a b L U k)
    (hL : 0 ≤ L) (hk : 0 < k) (h j : Icc L U) :
    |branch.time h - branch.time j| ≤ (2 * U / k) * |(h : ℝ) - (j : ℝ)| := by
  have sep := branch.displacement h j
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (hL.trans h.2.1) (hL.trans j.2.1))] at sep
  have sum : (h : ℝ) + (j : ℝ) ≤ 2 * U := by linarith [h.2.2, j.2.2]
  have sc := sep.trans (mul_le_mul_of_nonneg_right sum (abs_nonneg _))
  calc
    _ ≤ 2 * U * |(h : ℝ) - (j : ℝ)| / k := (le_div_iff₀ hk).mpr (by
      simpa only [mul_comm |branch.time h - branch.time j| k] using sc)
    _ = _ := by ring

/-- The inverse depends continuously on height up to and including both boundary heights. -/
theorem Branch.continuous_time {f : ℝ → ℝ} {a b L U k : ℝ} (branch : Branch f a b L U k)
    (hL : 0 ≤ L) (hk : 0 < k) : Continuous branch.time := by
  have lip : LipschitzWith (Real.toNNReal (2 * U / k)) branch.time := by
    apply LipschitzWith.of_dist_le_mul
    intro h j
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
    exact (branch.time_lipschitz hL hk h j).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _))
  exact lip.continuous

end PlasmaLean.Kinetic.MirrorHeightBand
