/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AveragedConfinement
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Confinement from action bounds on two radial faces

At the inner face it suffices to bound the action from above at the largest
admissible mirror height. At the outer face it suffices to bound it from below
at the smallest height. Monotonicity in height on these two faces extends both
estimates to the window. A radial path whose action drift fits between the two
values stays inside, even when the action has several radial roots.
-/

@[expose] public section
namespace PlasmaLean.ActionFaceBarrier

open Set

/-- A continuous real coordinate leaving an open interval first hits an endpoint,
with its whole preceding segment in the closed interval. -/
theorem first_hit_of_departure {r : ℝ → ℝ} {lo hi t : ℝ} (hc : ContinuousOn r (Icc 0 t))
    (hstart : r 0 ∈ Ioo lo hi) {s : ℝ} (hs : s ∈ Icc 0 t) (hout : r s ∉ Ioo lo hi) :
    ∃ u ∈ Icc 0 t, (r u = lo ∨ r u = hi) ∧ ∀ v ∈ Icc 0 u, r v ∈ Icc lo hi := by
  have reach (v : ℝ) (hv : v ∈ Icc 0 t) (hout' : r v ∉ Ioo lo hi) :
      ∃ w ∈ Icc 0 v, r w = lo ∨ r w = hi := by
    have hcv := hc.mono (Icc_subset_Icc_right hv.2)
    by_cases hlow : r v ≤ lo
    · obtain ⟨w, hw, he⟩ := intermediate_value_Icc' hv.1 hcv
        (show lo ∈ Icc (r v) (r 0) from ⟨hlow, hstart.1.le⟩)
      exact ⟨w, hw, Or.inl he⟩
    · have hhigh : hi ≤ r v := le_of_not_gt fun h ↦ hout' ⟨lt_of_not_ge hlow, h⟩
      obtain ⟨w, hw, he⟩ := intermediate_value_Icc hv.1 hcv
        (show hi ∈ Icc (r 0) (r v) from ⟨hstart.2.le, hhigh⟩)
      exact ⟨w, hw, Or.inr he⟩
  let hits : Set ℝ := Icc 0 t ∩ r ⁻¹' ({lo, hi} : Set ℝ)
  have hclosed : IsClosed hits := hc.preimage_isClosed_of_isClosed isClosed_Icc
    (Set.toFinite _).isClosed
  have hcompact : IsCompact hits := isCompact_Icc.of_isClosed_subset hclosed inter_subset_left
  obtain ⟨w, hw, hwedge⟩ := reach s hs hout
  have embed {x : ℝ} (hx : x ∈ Icc 0 t) (he : r x = lo ∨ r x = hi) : x ∈ hits :=
    ⟨hx, by simpa using he⟩
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn
    ⟨w, embed (Icc_subset_Icc_right hs.2 hw) hwedge⟩ (continuousOn_id (s := hits))
  have huedge : r u = lo ∨ r u = hi := by simpa using hu.2
  refine ⟨u, hu.1, huedge, ?_⟩
  intro v hv
  rcases hv.2.eq_or_lt with rfl | hvu
  · rcases huedge with h | h <;> simp [h, (hstart.1.trans hstart.2).le]
  · apply Ioo_subset_Icc_self
    by_contra hn
    obtain ⟨x, hx, he⟩ := reach v (Icc_subset_Icc_right hu.1.2 hv) hn
    have hearly := hmin (embed (Icc_subset_Icc_right (hv.2.trans hu.1.2) hx) he)
    exact (not_le_of_gt (hx.2.trans_lt hvu)) hearly

variable {P : Type*} {J : P → ℝ → ℝ → ℝ} {lo hi low high innerMax outerMin : ℝ}

/-- Face estimates for an action as a function of phase, radius and height, in that order. -/
structure FaceBounds (J : P → ℝ → ℝ → ℝ) (lo hi low high innerMax outerMin : ℝ) : Prop where
  inner_mono : ∀ p, MonotoneOn (J p lo) (Icc low high)
  outer_mono : ∀ p, MonotoneOn (J p hi) (Icc low high)
  inner_le : ∀ p, J p lo high ≤ innerMax
  le_outer : ∀ p, outerMin ≤ J p hi low

/-- It suffices to control the orbit's height and action up through a possible first hit.
The phase type is arbitrary. The action may have critical points in the radial interior. -/
theorem FaceBounds.stays_inside (F : FaceBounds J lo hi low high innerMax outerMin)
    {r h : ℝ → ℝ} {phase : ℝ → P} {T budget : ℝ} (hc : ContinuousOn r (Icc 0 T))
    (hr : r 0 ∈ Ioo lo hi)
    (hinner : innerMax + budget < J (phase 0) (r 0) (h 0))
    (houter : J (phase 0) (r 0) (h 0) + budget < outerMin)
    (control : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, r s ∈ Icc lo hi) →
      h t ∈ Icc low high ∧ |J (phase t) (r t) (h t) - J (phase 0) (r 0) (h 0)| ≤ budget) :
    ∀ t ∈ Icc 0 T, r t ∈ Ioo lo hi := by
  intro t ht
  by_contra hout
  obtain ⟨u, hu, hedge, hband⟩ := first_hit_of_departure hc hr ht hout
  obtain ⟨hh, hd⟩ := control u hu hband
  have limits := abs_le.mp hd
  rcases hedge with hin | hex
  · have hle := (F.inner_mono (phase u) hh (right_mem_Icc.mpr (hh.1.trans hh.2)) hh.2).trans
      (F.inner_le _)
    rw [hin] at limits
    linarith only [limits.1, hle, hinner]
  · have hle := (F.le_outer (phase u)).trans
      (F.outer_mono _ (left_mem_Icc.mpr (hh.1.trans hh.2)) hh hh.1)
    rw [hex] at limits
    linarith only [limits.2, hle, houter]

/-- A corrected-action equation supplies the drift budget for the face test. The
correction and remainder are bounded only while the trajectory is in the strip. -/
theorem FaceBounds.stays_inside_of_corrected_action
    (F : FaceBounds J lo hi low high innerMax outerMin)
    {r h g k : ℝ → ℝ} {phase : ℝ → P} {T ε G K : ℝ} (hK : 0 ≤ K)
    (hc : ContinuousOn r (Icc 0 T)) (hr : r 0 ∈ Ioo lo hi)
    (height : ∀ s ∈ Icc 0 T, r s ∈ Icc lo hi → h s ∈ Icc low high)
    (hg : ∀ s ∈ Icc 0 T, r s ∈ Icc lo hi → |g s| ≤ G)
    (hk : ∀ s ∈ Icc 0 T, r s ∈ Icc lo hi → |k s| ≤ K)
    (hd : ∀ s ∈ Icc 0 T, r s ∈ Icc lo hi →
      HasDerivAt (fun v ↦ J (phase v) (r v) (h v) + ε * g v) (ε ^ 2 * k s) s)
    (hinner : innerMax + (2 * |ε| * G + T * ε ^ 2 * K) < J (phase 0) (r 0) (h 0))
    (houter : J (phase 0) (r 0) (h 0) + (2 * |ε| * G + T * ε ^ 2 * K) < outerMin) :
    ∀ t ∈ Icc 0 T, r t ∈ Ioo lo hi := by
  apply F.stays_inside hc hr hinner houter
  intro t ht hband
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  refine ⟨height _ ht (hband t (right_mem_Icc.mpr ht.1)), ?_⟩
  have drift := AveragedConfinement.displacement_le ht.1
    (fun s hs ↦ (hd s (sub hs) (hband s hs)).hasDerivWithinAt)
    (fun s hs ↦ hk s (sub hs) (hband s hs))
    (hg 0 ⟨le_rfl, ht.1.trans ht.2⟩ (Ioo_subset_Icc_self hr))
    (hg t ht (hband t (right_mem_Icc.mpr ht.1)))
  exact drift.trans (add_le_add_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 (sq_nonneg ε)) hK) _)

/-- A height window with a strict face gap and three different radial roots at zero height. -/
theorem three_root_face_bounds :
    let J := fun (_ : Unit) (r h : ℝ) ↦ h + (2*r-1)^3 - (2*r-1)/4
    FaceBounds J 0 1 (-1/8) (1/8) (-5/8) (5/8) ∧
      J () (1/4) 0 = 0 ∧ J () (1/2) 0 = 0 ∧ J () (3/4) 0 = 0 := by
  dsimp
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro _ a _ b _ hab
    linarith
  · intro _ a _ b _ hab
    linarith
  all_goals norm_num

end PlasmaLean.ActionFaceBarrier
