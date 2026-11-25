/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.FirstWellContinuation
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Continuous first-mirror positions and actions over a transverse family -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.FirstWellContinuation
open Set Topology Filter MirrorActionEnvelope MirrorHeightAction
variable {P : Type*} [TopologicalSpace P] {f w : P → ℝ → ℝ} {h : P → ℝ} {b : ℝ}

/-- Both mirror positions and the true first-well action are continuous over any parameter
space when the two first contacts are simple. Later extrema and contacts are unrestricted. -/
theorem CappedFamily.continuous_first_wells (fam : CappedFamily f w h b)
    (simple : ∀ p l r, LaunchWell (f p) 0 (h p) l r →
      deriv (f p) l ≠ 0 ∧ deriv (f p) r ≠ 0) :
    ∃ l r : P → ℝ, Continuous l ∧ Continuous r ∧
      (∀ p, LaunchWell (f p) 0 (h p) (l p) (r p)) ∧
      Continuous (fun p => action (f p) (w p) (l p) (r p) (h p)) := by
  have slice {g : P → ℝ → ℝ}
      (joint : ContinuousOn (fun q : P × ℝ => g q.1 q.2) (univ ×ˢ Icc (-b) b)) (p : P) :
      ContinuousOn (g p) (Icc (-b) b) :=
    joint.comp (continuous_const.prodMk continuous_id).continuousOn fun _ ht => ⟨mem_univ p, ht⟩
  have wells (p : P) := exists_launchWell (neg_lt_zero.mpr fam.duration) fam.duration
    (slice fam.field p) (fam.back p) (fam.birth p) (fam.forward p)
  choose l hl r hr well using wells
  have forward (p : P) : FirstContact (f p) (h p) b (r p) :=
    ⟨hr p, (well p).right_hit, fun t ht => (well p).accessible t
      ⟨(well p).left_lt.trans_le ht.1, ht.2⟩⟩
  have backward (p : P) : FirstContact (fun s => f p (-s)) (h p) b (-(l p)) := by
    refine ⟨⟨neg_pos.mpr (hl p).2, by linarith [(hl p).1]⟩, by simpa using (well p).left_hit, ?_⟩
    intro t ht
    exact (well p).accessible _ ⟨by linarith [ht.2], by linarith [ht.1, (hr p).1]⟩
  have signed {g : P → ℝ → ℝ}
      (joint : ContinuousOn (fun q : P × ℝ => g q.1 q.2) (univ ×ˢ Icc (-b) b)) :
      ContinuousOn (fun q : P × ℝ => g q.1 (-q.2)) (univ ×ˢ Icc 0 b) := by
    apply joint.comp (f := fun q : P × ℝ => (q.1, -q.2)) (by fun_prop)
    rintro ⟨p,t⟩ ⟨_, ht⟩
    exact ⟨mem_univ _, ⟨by linarith [ht.2], by linarith [ht.1, fam.duration]⟩⟩
  have sub : (univ : Set P) ×ˢ Icc 0 b ⊆ univ ×ˢ Icc (-b) b :=
    prod_mono_right (Icc_subset_Icc_left (neg_nonpos.mpr fam.duration.le))
  have cf (p : P) : CrossesOutward (f p) (h p) b (r p) := by
    by_contra blocked
    exact (simple p _ _ (well p)).2 ((forward p).localMax_of_not_crosses blocked).deriv_eq_zero
  have cb (p : P) : CrossesOutward (fun s => f p (-s)) (h p) b (-(l p)) := by
    by_contra blocked
    have zero := ((backward p).localMax_of_not_crosses blocked).deriv_eq_zero
    exact (simple p _ _ (well p)).1
      (by simpa only [deriv_comp_neg, neg_neg, neg_eq_zero] using zero)
  have cl : Continuous (fun p => -(l p)) := continuous_iff_continuousAt.mpr fun p =>
    continuousAt_time (signed fam.field) fam.height backward (cb p)
  have cr : Continuous r := continuous_iff_continuousAt.mpr fun p =>
    continuousAt_time (fam.field.mono sub) fam.height forward (cf p)
  refine ⟨l, r, by simpa only [Pi.neg_def, neg_neg] using cl.neg, cr, well, ?_⟩
  apply ((continuous_action (f := fun p t => f p (-t)) (w := fun p t => w p (-t))
    (signed fam.field) (signed fam.weight) fam.height backward cb).add
    (continuous_action (fam.field.mono sub) (fam.weight.mono sub) fam.height forward cf)).congr
  intro p
  have domain := Icc_subset_Icc (hl p).1.le (hr p).2.le
  exact action_split (well p).left_lt.le (well p).lt_right.le
    ((slice fam.field p).mono domain) ((slice fam.weight p).mono domain)

end PlasmaLean.Kinetic.FirstWellContinuation
