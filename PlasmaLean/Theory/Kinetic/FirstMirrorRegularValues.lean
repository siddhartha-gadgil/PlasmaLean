/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.TrajectorySlabObservable
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Topology.Order.Monotone

/-! # First mirror times for a profile with possible interior extrema -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.FirstMirror

open Set Filter MeasureTheory Topology

/-- Earliest contacts with the levels of a closed height band on one outward clock. -/
structure Family (f : ℝ → ℝ) (a b L U : ℝ) where
  time : Icc L U → ℝ
  interior_time : ∀ h, time h ∈ Ioo a b
  hit : ∀ h, f (time h) = h
  before : ∀ h, ∀ t ∈ Ico 0 (time h), f t < h

theorem exists_family {f : ℝ → ℝ} {a b L U : ℝ} (ha : 0 ≤ a) (ab : a < b)
    (early : ∀ t ∈ Icc 0 a, f t < L) (cont : ContinuousOn f (Icc a b)) (cap : U < f b) :
    Nonempty (Family f a b L U) := by
  have each (h : Icc L U) := Fields.TrajectorySlabs.first_contact_in_bracket ha ab
    (fun t ht => (early t ht).trans_le h.2.1) cont (h.2.2.trans_lt cap)
  choose time ht hit pre using each
  exact ⟨⟨time,ht,hit,pre⟩⟩

variable {f : ℝ → ℝ} {a b L U : ℝ}

theorem Family.strictMono (p : Family f a b L U) (ha : 0 ≤ a) : StrictMono p.time := by
  intro x y xy
  rcases lt_trichotomy (p.time x) (p.time y) with h | h | h
  · exact h
  · exact (xy.ne (Subtype.ext ((p.hit x).symm.trans ((congrArg f h).trans (p.hit y))))).elim
  · have low := p.before x _ ⟨ha.trans (p.interior_time y).1.le,h⟩
    rw [p.hit] at low
    exact (not_lt_of_ge xy.le low).elim

/-- Every compact interval strictly before a contact has a positive height gap. This
gives continuity from lower heights even at tangent first contacts. -/
theorem Family.continuous_from_below (p : Family f a b L U) (ha : 0 ≤ a)
    (cont : ContinuousOn f (Icc a b)) (h : Icc L U) : ContinuousWithinAt p.time (Iic h) h := by
  apply Metric.continuousWithinAt_iff.mpr
  intro ε pos
  let x := max a (p.time h - ε / 2)
  have ax : a ≤ x := le_max_left _ _
  have xt : x < p.time h := max_lt (p.interior_time h).1 (by linarith)
  obtain ⟨c,hc,highest⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ax)
    (cont.mono (Icc_subset_Icc_right (xt.trans (p.interior_time h).2).le))
  have gap := p.before h c ⟨ha.trans hc.1,hc.2.trans_lt xt⟩
  refine ⟨(h:ℝ)-f c,sub_pos.mpr gap,?_⟩
  intro j jh near
  have order : p.time j ≤ p.time h := (p.strictMono ha).monotone jh
  have above : f c < j := by
    change |(j:ℝ)-(h:ℝ)| < _ at near
    linarith [(abs_lt.mp near).1]
  have past : x < p.time j := by
    by_contra! le
    have q := (isMaxOn_iff.mp highest) (p.time j) ⟨(p.interior_time j).1.le,le⟩
    rw [p.hit] at q
    exact above.not_ge q
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr order)]
  have lower : p.time h - ε / 2 ≤ x := le_max_right _ _
  linarith

theorem Family.countable_exceptions (p : Family f a b L U) (ha : 0 ≤ a) :
    {h | ¬ ContinuousAt p.time h}.Countable := (p.strictMono ha).monotone.countable_not_continuousAt

/-- Sard's lemma in one dimension, restricted to the interior of the mirror bracket. -/
theorem critical_values_null {s : Set ℝ} (df : ∀ t ∈ s, DifferentiableAt ℝ f t) :
    volume (f '' {t ∈ s | deriv f t = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun _ => (0 : ℝ →L[ℝ] ℝ))
  · intro t ht
    have d := (df t ht.1).hasDerivAt
    rw [ht.2] at d
    simpa using d.hasFDerivAt.hasFDerivWithinAt
  · intro t _
    simp

/-- A noncritical first contact has positive derivative in the outward direction. -/
theorem Family.deriv_pos (p : Family f a b L U) (ha : 0 ≤ a) (h : Icc L U)
    (df : DifferentiableAt ℝ f (p.time h)) (reg : deriv f (p.time h) ≠ 0) :
    0 < deriv f (p.time h) := by
  by_contra! neg
  have limit := (hasDerivAt_iff_tendsto_slope_left_right.mp df.hasDerivAt).1
  have small := limit.eventually (eventually_lt_nhds (lt_of_le_of_ne neg reg))
  have interval : ∀ᶠ t in 𝓝[<] p.time h, t ∈ Ioo 0 (p.time h) :=
    Ioo_mem_nhdsLT (ha.trans_lt (p.interior_time h).1)
  obtain ⟨t,hs,ht⟩ := (small.and interval).exists
  have above := (slope_neg_iff_of_le (f := f) ht.2.le).mp (slope_comm f _ _ ▸ hs)
  rw [p.hit] at above
  exact above.not_gt (p.before h t ⟨ht.1.le,ht.2⟩)

/-- For almost every physical height in the band the earliest outward contact is simple.
The exceptional set is measured in height, with the underlying profile held fixed. -/
theorem Family.ae_transverse (p : Family f a b L U) (ha : 0 ≤ a)
    (df : ∀ t ∈ Ioo a b, f t ∈ Icc L U → DifferentiableAt ℝ f t) :
    ∀ᵐ H : ℝ, ∀ h : Icc L U, (h:ℝ) = H → 0 < deriv f (p.time h) := by
  let s := {t ∈ Ioo a b | f t ∈ Icc L U}
  have null := critical_values_null (s := s) (fun t ht => df t ht.1 ht.2)
  have regular : ∀ᵐ H : ℝ, H ∉ f '' {t ∈ s | deriv f t = 0} := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using null
  filter_upwards [regular] with H outside
  intro h hh
  have member : p.time h ∈ s := ⟨p.interior_time h,p.hit h ▸ h.2⟩
  apply p.deriv_pos ha h (df _ member.1 member.2)
  exact fun zero => outside ⟨p.time h,⟨member,zero⟩,(p.hit h).trans hh⟩

/-- The forward and backward first mirrors of the same birth are simple at almost every
height. Each clock may have its own bracket and earlier interior extrema. -/
theorem ae_two_sided {g : ℝ → ℝ} {c d : ℝ} (left : Family f a b L U)
    (right : Family g c d L U) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (df : ∀ t ∈ Ioo a b, f t ∈ Icc L U → DifferentiableAt ℝ f t)
    (dg : ∀ t ∈ Ioo c d, g t ∈ Icc L U → DifferentiableAt ℝ g t) :
    ∀ᵐ H : ℝ, ∀ h : Icc L U, (h:ℝ) = H →
      0 < deriv f (left.time h) ∧ 0 < deriv g (right.time h) := by
  filter_upwards [left.ae_transverse ha df,right.ae_transverse hc dg] with H l r
  exact fun h hh => ⟨l h hh,r h hh⟩

/-- A pair of vector fields along signed curves. The positive lower height ensures
differentiability of the norm at all relevant preimages, even if a field vanishes
elsewhere. The two earliest-contact functions are fixed before choosing the height. -/
theorem exists_ae_field_mirrors {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v w : ℝ → E) {c d : ℝ} (ha : 0 ≤ a) (ab : a < b) (hc : 0 ≤ c) (cd : c < d)
    (positive : 0 < L)
    (ev : ∀ t ∈ Icc 0 a, ‖v t‖ < L) (ew : ∀ t ∈ Icc 0 c, ‖w t‖ < L)
    (cv : ContinuousOn v (Icc a b)) (cw : ContinuousOn w (Icc c d))
    (dv : ∀ t ∈ Ioo a b, DifferentiableAt ℝ v t) (dw : ∀ t ∈ Ioo c d, DifferentiableAt ℝ w t)
    (capv : U < ‖v b‖) (capw : U < ‖w d‖) :
    ∃ p : Family (fun t => ‖v t‖) a b L U, ∃ q : Family (fun t => ‖w t‖) c d L U,
      ∀ᵐ H : ℝ, ∀ h : Icc L U, (h:ℝ) = H →
        0 < deriv (fun t => ‖v t‖) (p.time h) ∧ 0 < deriv (fun t => ‖w t‖) (q.time h) := by
  obtain ⟨p⟩ := exists_family ha ab ev cv.norm capv
  obtain ⟨q⟩ := exists_family hc cd ew cw.norm capw
  exact ⟨p,q,ae_two_sided p q ha hc
    (fun t ht h => (dv t ht).norm ℝ (norm_pos_iff.mp (positive.trans_le h.1)))
    (fun t ht h => (dw t ht).norm ℝ (norm_pos_iff.mp (positive.trans_le h.1)))⟩

/-- The one-dimensional area inequality bounds the height measure of every image
point with a small slope. It also holds for any subset, in outer measure. -/
theorem shallow_image_le (df : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t) (m : ℝ) :
    volume (f '' {t ∈ Ioo a b | |deriv f t| ≤ m}) ≤
      ENNReal.ofReal m * ENNReal.ofReal (b-a) := by
  let s := {t ∈ Ioo a b | |deriv f t| ≤ m}
  have ms : MeasurableSet s := measurableSet_Ioo.inter
    (measurableSet_le (continuous_abs.measurable.comp (measurable_deriv f)) measurable_const)
  have area : volume (f '' s) ≤ ∫⁻ t in s, ENNReal.ofReal |deriv f t| := by
    simpa only [ContinuousLinearMap.det_toSpanSingleton] using
      addHaar_image_le_lintegral_abs_det_fderiv volume ms
        (fun t ht => (df t ht.1).hasDerivAt.hasDerivWithinAt.hasFDerivWithinAt)
  calc
    volume (f '' s) ≤ ∫⁻ t in s, ENNReal.ofReal |deriv f t| := area
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal m := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem ms] with t ht
      exact ENNReal.ofReal_le_ofReal ht.2
    _ = ENNReal.ofReal m * volume s := by simp
    _ ≤ ENNReal.ofReal m * ENNReal.ofReal (b-a) := by
      rw [← Real.volume_Ioo]
      have sub : s ⊆ Ioo a b := fun _ ht => ht.1
      exact mul_le_mul_of_nonneg_left (measure_mono sub) zero_le

/-- Heights with a shallow earliest contact cost at most slope threshold times the
bracket length. The height set itself need not be proved measurable. -/
theorem Family.shallow_heights_le (p : Family f a b L U) (m : ℝ)
    (df : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t) :
    volume {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧ |deriv f (p.time h)| ≤ m} ≤
      ENNReal.ofReal m * ENNReal.ofReal (b-a) := by
  apply (measure_mono ?_).trans (shallow_image_le df m)
  rintro H ⟨h,rfl,hv⟩
  exact ⟨p.time h,⟨p.interior_time h,hv⟩,p.hit h⟩

/-- The union bound gives an explicit budget for heights with a shallow first contact
on either clock, without requiring any statistical independence of the two profiles. -/
theorem two_sided_shallow_heights_le {g : ℝ → ℝ} {c d : ℝ} (p : Family f a b L U)
    (q : Family g c d L U) (m : ℝ) (df : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (dg : ∀ t ∈ Ioo c d, DifferentiableAt ℝ g t) :
    volume {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧
      (|deriv f (p.time h)| ≤ m ∨ |deriv g (q.time h)| ≤ m)} ≤
      ENNReal.ofReal m * (ENNReal.ofReal (b-a) + ENNReal.ofReal (d-c)) := by
  let A := {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧ |deriv f (p.time h)| ≤ m}
  let B := {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧ |deriv g (q.time h)| ≤ m}
  rw [mul_add]
  refine (measure_mono (t := A ∪ B) ?_).trans ((measure_union_le _ _).trans
    (add_le_add (p.shallow_heights_le m df) (q.shallow_heights_le m dg)))
  rintro H ⟨h,eq,l | r⟩
  · exact Or.inl ⟨h,eq,l⟩
  · exact Or.inr ⟨h,eq,r⟩

/-- Positive slopes in both directions over a quantitative height measure. -/
theorem two_sided_good_heights {g : ℝ → ℝ} {c d : ℝ} (p : Family f a b L U)
    (q : Family g c d L U) (ha : 0 ≤ a) (hc : 0 ≤ c) (m : ℝ)
    (df : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t) (dg : ∀ t ∈ Ioo c d, DifferentiableAt ℝ g t) :
    ENNReal.ofReal (U-L) - ENNReal.ofReal m * (ENNReal.ofReal (b-a) + ENNReal.ofReal (d-c)) ≤
      volume {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧
        m < deriv f (p.time h) ∧ m < deriv g (q.time h)} := by
  let G := {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧ m < deriv f (p.time h) ∧ m < deriv g (q.time h)}
  let A := {H : ℝ | ∃ h : Icc L U, (h:ℝ) = H ∧
      (|deriv f (p.time h)| ≤ m ∨ |deriv g (q.time h)| ≤ m)}
  have cover : Icc L U ⊆ G ∪ A := by
    intro H hh
    let h : Icc L U := ⟨H,hh⟩
    have pos {F : ℝ → ℝ} {A B : ℝ} (r : Family F A B L U) (start : 0 ≤ A)
        (der : DifferentiableAt ℝ F (r.time h)) : 0 ≤ deriv F (r.time h) := by
      by_cases zero : deriv F (r.time h) = 0
      · exact zero.ge
      · exact (r.deriv_pos start h der zero).le
    by_cases l : m < deriv f (p.time h)
    · by_cases r : m < deriv g (q.time h)
      · exact Or.inl ⟨h,rfl,l,r⟩
      · refine Or.inr ⟨h,rfl,Or.inr ?_⟩
        rwa [abs_of_nonneg (pos q hc (dg _ (q.interior_time h))), ← not_lt]
    · refine Or.inr ⟨h,rfl,Or.inl ?_⟩
      rwa [abs_of_nonneg (pos p ha (df _ (p.interior_time h))), ← not_lt]
  apply tsub_le_iff_right.mpr
  rw [← Real.volume_Icc]
  exact (measure_mono cover).trans ((measure_union_le G A).trans
    (add_le_add le_rfl (two_sided_shallow_heights_le p q m df dg)))

end PlasmaLean.Kinetic.FirstMirror
