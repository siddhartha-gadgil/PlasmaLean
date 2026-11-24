/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorHeightBand
public import PlasmaLean.Theory.Kinetic.MirrorWellPersistence

/-! # Moving the birth point inside a two-sided transverse mirror bracket -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.MirrorHeightBand
open Set MirrorWellPersistence

/-- Every point between the two inner caps is strictly accessible. -/
theorem Branch.central_below {f : ℝ → ℝ} {a b L U k t : ℝ}
    (right : Branch f a b L U k) (left : Branch (fun s => f (-s)) a b L U k)
    (q : Icc L U) (ht : t ∈ Icc (-a) a) : f t < q := by
  rcases le_total 0 t with pos | neg
  · exact right.before q t ⟨pos, ht.2.trans_lt (right.interior_time q).1⟩
  · have h := left.before q (-t)
      ⟨neg_nonneg.mpr neg, lt_of_le_of_lt (by linarith [ht.1]) (left.interior_time q).1⟩
    simpa only [neg_neg] using h

/-- Oppositely oriented first-contact branches on a common profile give a transverse bracket
about every point in its central interval, at every height with a positive slope floor. -/
theorem Branch.bracket {f : ℝ → ℝ} {a b L U k c : ℝ}
    (right : Branch f a b L U k) (left : Branch (fun t => f (-t)) a b L U k)
    (q : Icc L U) (rate : 0 < k / (2 * (q : ℝ))) (central : |c| ≤ a) :
    Bracket f (-b) c b q := by
  have low {t : ℝ} (ht : t ∈ Icc (-a) a) := right.central_below left q ht
  obtain ⟨lo, hi⟩ := abs_le.mp central
  refine Bracket.of_signs (left.after q b ⟨(left.interior_time q).2,le_rfl⟩)
    (low ⟨lo,hi⟩) (right.after q b ⟨(right.interior_time q).2,le_rfl⟩) ?_ ?_
  · intro t ht hit
    by_cases mid : -a ≤ t
    · exact False.elim ((low ⟨mid,ht.2.trans hi⟩).ne hit)
    have atroot : -t = left.time q := left.unique_time q (-t)
      ⟨by linarith,by linarith [ht.1]⟩ (by simpa only [neg_neg])
    obtain ⟨v,hv,d⟩ := left.transverse q
    rw [← atroot] at d
    have reverse := d.comp t (hasDerivAt_id t).neg
    have orient : HasDerivAt f (-v) t := by
      simpa only [Function.comp_def,id_eq,neg_neg,mul_neg_one] using reverse
    rw [orient.deriv]
    exact neg_neg_of_pos (rate.trans hv)
  · intro t ht hit
    by_cases mid : t ≤ a
    · exact False.elim ((low ⟨lo.trans ht.1,mid⟩).ne hit)
    have atroot := right.unique_time q t ⟨le_of_not_ge mid,ht.2⟩ hit
    obtain ⟨v,hv,d⟩ := right.transverse q
    rw [atroot,d.deriv]
    exact rate.trans hv

end PlasmaLean.Kinetic.MirrorHeightBand
