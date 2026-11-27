/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameHalfTube

/-!
# The closed core of the tube of a chain of position-frame slabs

The forward tube recorded by a chain of wide position-frame steps (gauge of slab `k` at most
the outgoing radius of its record) is a closed subset of the inner tube of
`PositionFrameTube`, and it contains every point of the tube whose backward solution starts
in the entry set of the chain.

* `frame_dist_chain_forward`, `eq_of_eq_forward`: frame distances and uniqueness away from the
  initial time, the counterparts of `frame_dist_chain` and `eq_of_eq`.
* `marginCheck`, `Margin`, `margin_of_check`: the outgoing radius of every record is at least
  its incoming radius and below the backward radius of its slab.
* `core`, `core_subset_inner`, `isClosed_core`: the closed core lies in the inner tube.
* `mem_core_of_label`: a solution in the outer tube that starts in the entry set of the chain
  lies in the core.
* `coreV`, `coreD`: the core doubled by a reflection about the initial time, with the
  intersection (`coreV`) or the union (`coreD`) of the two halves at the initial time.
  `coreV_subset` and `coreD_subset` place them in the doubled inner tube, `isClosed_coreD`
  shows that `coreD` is closed, and `coreV_eq_coreD` identifies the two when the core at the
  initial time is invariant under the reflection. `section_of_identity` gives the hypothesis
  of `coreD_subset` for the identity initial frame and a reflection fixing the initial point.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameTube

open Set PositionFrameSlabs PositionFrameBackward Filter Topology
open PlasmaLean.Fields

/-! ### Distances away from the initial time -/

section Forward

variable {domain : RegularityDomain} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
  {s₀ : State} {a : ℝ} {rows : List Step}

/-- Two solutions in the outer tube between two times of one slab: the frame distance at the
later time is at most `exp (max 0 μ / 64)` times the frame distance at the earlier time. -/
theorem slab_dist_forward (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {k : ℕ} (hk : k < rows.length) {t₀ t₁ : ℝ}
    (h₀ : time a k ≤ t₀) (h₀₁ : t₀ ≤ t₁) (h₁ : t₁ ≤ time a (k + 1)) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt u (F τ (u τ)) (Icc t₀ t₁) τ)
    (hv : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt v (F τ (v τ)) (Icc t₀ t₁) τ)
    (mu : ∀ τ ∈ Ioo t₀ t₁, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo t₀ t₁, v τ ∈ outer s₀ a rows τ) :
    ‖(frameAt s₀ a rows k t₁).symm (u t₁ - v t₁)‖ ≤
      Real.exp (max 0 ((rowAt rows k).mu : ℝ) / 64) *
        ‖(frameAt s₀ a rows k t₀).symm (u t₀ - v t₀)‖ := by
  have inside {z : ℝ → Plane} (mz : ∀ τ ∈ Ioo t₀ t₁, z τ ∈ outer s₀ a rows τ) :
      ∀ τ ∈ Ioo t₀ t₁, ‖(moving (stateAt s₀ rows k) (rowAt rows k) (time a k) τ).symm
        (z τ - reference (time a k) (rowAt rows k) τ)‖ ≤ (rowAt rows k).trial / (2 : ℝ) ^ 80 := by
    intro τ hτ
    obtain ⟨j, _, hj, hg⟩ := mz τ hτ
    obtain rfl := slab_unique ⟨h₀.trans_lt hτ.1, hτ.2.trans_le h₁⟩ hj
    exact hg
  have h₁' := h₁
  rw [time_succ] at h₁'
  refine ((frame_dist_le (geo.at hk) (fieldBounds_at bounds hk) (lower.at hk) h₀ h₀₁ h₁' hu hv
    (inside mu) (inside mv)).2).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)

private theorem chain_ge (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {i : ℕ} {s : ℝ} (hs : s ≤ time a (i + 1))
    (hs' : time a i ≤ s) {u v : ℝ → Plane} :
    ∀ k, i ≤ k → k < rows.length → ∀ t ∈ Icc (time a k) (time a (k + 1)), s ≤ t →
      (∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ) →
      (∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ) →
      (∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ) → (∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) →
      ‖(frameAt s₀ a rows k t).symm (u t - v t)‖ ≤
        Real.exp (∑ j ∈ Finset.Ico i (k + 1), max 0 ((rowAt rows j).mu : ℝ) / 64) *
          ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ := by
  intro k hik
  induction k, hik using Nat.le_induction with
  | base =>
    intro hk t ht hst hu hv mu mv
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    exact slab_dist_forward geo bounds lower hk hs' hst ht.2 hu hv mu mv
  | succ k hik ih =>
    intro hk t ht hst hu hv mu mv
    have hk' : k < rows.length := Nat.lt_of_succ_lt hk
    have hsn : s ≤ time a (k + 1) := hs.trans (time_le (Nat.succ_le_succ hik))
    have sub : Icc s (time a (k + 1)) ⊆ Icc s t := Icc_subset_Icc_right ht.1
    have sub' : Ioo s (time a (k + 1)) ⊆ Ioo s t := Ioo_subset_Ioo_right ht.1
    have first := ih hk' (time a (k + 1)) ⟨time_le (Nat.le_succ k), le_rfl⟩ hsn
      (fun τ hτ => (hu τ (sub hτ)).mono sub) (fun τ hτ => (hv τ (sub hτ)).mono sub)
      (fun τ hτ => mu τ (sub' hτ)) (fun τ hτ => mv τ (sub' hτ))
    rw [frameAt_node geo hk] at first
    have sub₂ : Icc (time a (k + 1)) t ⊆ Icc s t := Icc_subset_Icc_left hsn
    have sub₂' : Ioo (time a (k + 1)) t ⊆ Ioo s t := Ioo_subset_Ioo_left hsn
    have second := slab_dist_forward geo bounds lower hk le_rfl ht.1 ht.2
      (fun τ hτ => (hu τ (sub₂ hτ)).mono sub₂) (fun τ hτ => (hv τ (sub₂ hτ)).mono sub₂)
      (fun τ hτ => mu τ (sub₂' hτ)) (fun τ hτ => mv τ (sub₂' hτ))
    rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hik), Real.exp_add,
      mul_comm (Real.exp _) (Real.exp _), mul_assoc]
    exact second.trans (mul_le_mul_of_nonneg_left first (Real.exp_pos _).le)

/-- **Frame distances along the chain, forward.** Two solutions on `[s, t]` that lie in the
outer tube at the times strictly between `s` and `t`: their distance at `t`, in the frame of a
slab `k` containing `t`, is at most `exp E` times their distance at `s` in the frame of a slab
`i` containing `s`, where `E` bounds the sum of the growth exponents of all slabs. -/
theorem frame_dist_chain_forward (geo : Geo s₀ rows)
    (bounds : FieldBoundsOn F J s₀ a rows domain) (lower : LowerOn J s₀ a rows) {E : ℝ}
    (hE : ∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 ≤ E)
    {i k : ℕ} (hi : i < rows.length) (hk : k < rows.length) {s t : ℝ}
    (hs : s ∈ Icc (time a i) (time a (i + 1))) (ht : t ∈ Icc (time a k) (time a (k + 1)))
    (hst : s ≤ t) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (mu : ∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) :
    ‖(frameAt s₀ a rows k t).symm (u t - v t)‖ ≤
      Real.exp E * ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ := by
  have term (j : ℕ) : 0 ≤ max 0 ((rowAt rows j).mu : ℝ) / 64 :=
    div_nonneg (le_max_left _ _) (by norm_num)
  rcases le_or_gt i k with hik | hki
  · refine (chain_ge geo bounds lower hs.2 hs.1 k hik hk t ht hst hu hv mu mv).trans ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_trans ?_ hE)) (norm_nonneg _)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j _ _ => term j)
    exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hj).2.trans_le hk)
  · have h₁ : time a (k + 1) ≤ time a i := time_le hki
    have hts : t = s := le_antisymm (ht.2.trans (h₁.trans hs.1)) hst
    subst hts
    have hii : i ≤ k + 1 := time_le_iff.mp (hs.1.trans ht.2)
    obtain rfl : i = k + 1 := le_antisymm hii hki
    have ht' : t = time a (k + 1) := le_antisymm ht.2 hs.1
    have E0 : 0 ≤ E := (Finset.sum_nonneg fun j _ => term j).trans hE
    rw [ht', ← frameAt_node geo hi]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp E0)

/-- **Uniqueness away from the initial time.** Two solutions on `[s, t]` in the outer tube that
agree at `s` agree at `t`. -/
theorem eq_of_eq_forward (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows)
    {i k : ℕ} (hi : i < rows.length) (hk : k < rows.length) {s t : ℝ}
    (hs : s ∈ Icc (time a i) (time a (i + 1))) (ht : t ∈ Icc (time a k) (time a (k + 1)))
    (hst : s ≤ t) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (mu : ∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) (h : u s = v s) : u t = v t := by
  have chain := frame_dist_chain_forward geo bounds lower le_rfl hi hk hs ht hst hu hv mu mv
  rw [h, sub_self, map_zero, norm_zero, mul_zero] at chain
  have zero := norm_le_zero_iff.mp chain
  rw [EmbeddingLike.map_eq_zero_iff] at zero
  exact sub_eq_zero.mp zero

end Forward

/-! ### The margin check -/

/-- Margins of the recorded radii, with `β` in units of 2⁻⁸⁰ and one more entry than `rows`:
for the record `r` followed by the radius `b₁`, the incoming radius is at most the outgoing
radius, and the outgoing radius is below `b₁`. -/
def marginCheck : List Step → List ℕ → Bool
  | [], _ => true
  | r :: rs, _ :: b₁ :: bs =>
    Nat.ble r.incoming r.outgoing && Nat.blt r.outgoing b₁ && marginCheck rs (b₁ :: bs)
  | _ :: _, _ => false

/-- Margins of the recorded radii against the backward radii `β`. -/
structure Margin (rows : List Step) (β : ℕ → ℝ) : Prop where
  /-- the incoming radius of a record is at most its outgoing radius -/
  incoming : ∀ k < rows.length, (rowAt rows k).incoming ≤ (rowAt rows k).outgoing
  /-- the outgoing radius of a record is below the backward radius of its slab -/
  outgoing : ∀ k < rows.length, ((rowAt rows k).outgoing : ℝ) / 2 ^ 80 < β (k + 1)

/-- **Soundness of the margin check.** -/
theorem margin_of_check {rows : List Step} {bs : List ℕ} (h : marginCheck rows bs = true) :
    Margin rows (fun k => (bs.getD k 0 : ℝ) / 2 ^ 80) := by
  induction rows generalizing bs with
  | nil => constructor <;> exact fun k hk => absurd hk (Nat.not_lt_zero k)
  | cons r rs ih =>
    match bs, h with
    | b₀ :: b₁ :: bs, h =>
      simp only [marginCheck, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      obtain ⟨⟨inc, out⟩, tail⟩ := h
      have rest := ih tail
      constructor
      · rintro (_ | k) hk
        · exact inc
        · exact rest.incoming k (Nat.lt_of_succ_lt_succ hk)
      · rintro (_ | k) hk
        · change (r.outgoing : ℝ) / 2 ^ 80 < (b₁ : ℝ) / 2 ^ 80
          exact div_lt_div_of_pos_right (by exact_mod_cast out) (by positivity)
        · exact rest.outgoing k (Nat.lt_of_succ_lt_succ hk)

/-! ### The core -/

/-- The core of the tube: points within the outgoing radius of a closed slab containing the
time. -/
def core (s₀ : State) (a : ℝ) (rows : List Step) (t : ℝ) : Set Plane :=
  {x | ∃ k < rows.length, t ∈ Icc (time a k) (time a (k + 1)) ∧
    gauge s₀ a rows k (t, x) ≤ (rowAt rows k).outgoing / (2 : ℝ) ^ 80}

/-- The core lies over the closed time interval of the chain. -/
theorem core_time {s₀ : State} {a : ℝ} {rows : List Step} {t : ℝ} {x : Plane}
    (hx : x ∈ core s₀ a rows t) : t ∈ Icc a (time a rows.length) := by
  obtain ⟨k, hk, ht, _⟩ := hx
  have h₀ : time a 0 ≤ time a k := time_le (Nat.zero_le k)
  rw [time_zero] at h₀
  exact ⟨h₀.trans ht.1, ht.2.trans (time_le hk)⟩

/-- Every record of a chain of valid wide steps is valid from the state before its slab. -/
theorem valid_at {s₀ e : State} {rows : List Step}
    (h : PositionFrameWideChain.Steps s₀ rows e) {k : ℕ} (hk : k < rows.length) :
    PositionFrameWide.valid (stateAt s₀ rows k) (rowAt rows k) = true :=
  indexed (P := fun s r _ => PositionFrameWide.valid s r = true)
    (Q := fun s _ rows => PositionFrameWideChain.Steps s rows e)
    (fun _ _ _ _ h => h) rows s₀ 0 h k hk

/-- Passing from the point of the incoming state to the reference of a slab at its start
costs the recorded jump. -/
theorem start_shift_rev {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    (a : ℝ) (y : Plane) :
    ‖(moving s r a a).symm (y - reference a r a)‖ ≤
      ‖(frameEquiv s.frame s.frame 0).symm (y - point s.point)‖ + r.jumpBound / (2 : ℝ) ^ 80 := by
  have hj := norm_reference_jump h
  rw [frame_start h] at hj
  rw [moving_start h, reference_start]
  have split : (frameEquiv s.frame s.frame 0).symm (y - point (firstPoint r)) =
      (frameEquiv s.frame s.frame 0).symm (y - point s.point) +
        (frameEquiv s.frame s.frame 0).symm (point s.point - point (firstPoint r)) := by
    rw [← map_add]
    congr 1
    abel
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hj)

section Core

variable {domain : RegularityDomain} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
  {s₀ e : State} {a : ℝ} {rows : List Step} {β : ℕ → ℝ}

/-- At a node the gauge of the later slab exceeds the gauge of the earlier slab by at most
the jump of the later slab. -/
theorem gauge_node_ge (geo : Geo s₀ rows) {k : ℕ} (hk : k + 1 < rows.length) (x : Plane) :
    gauge s₀ a rows (k + 1) (time a (k + 1), x) ≤
      gauge s₀ a rows k (time a (k + 1), x) +
        (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := by
  rw [gauge_end geo (Nat.lt_of_succ_lt hk)]
  exact start_shift_rev (geo.at hk) (time a (k + 1)) x

/-- **The core lies in the inner tube** at the times before the end of the chain. -/
theorem core_subset_inner (steps : PositionFrameWideChain.Steps s₀ rows e)
    (margin : Margin rows β) {t : ℝ} (ht : t < time a rows.length) :
    core s₀ a rows t ⊆ inner s₀ a rows β t := by
  rintro x ⟨k, hk, hmem, hg⟩
  have geo := Geo.of_steps steps
  rcases hmem.2.lt_or_eq with hlt | heq
  · exact ⟨k, hk, ⟨hmem.1, hlt⟩, hg.trans_lt (margin.outgoing k hk)⟩
  · have hk1 : k + 1 < rows.length := by
      by_contra hcon
      have := time_le (a := a) (not_lt.mp hcon)
      linarith
    subst heq
    obtain ⟨inc, -⟩ :=
      PositionFrameWide.growth_sound (Bool.and_eq_true_iff.mp (valid_at steps hk1)).2
    have inc' : ((rowAt rows (k + 1)).incoming : ℝ) =
        (rowAt rows k).outgoing + (rowAt rows (k + 1)).jumpBound := by
      rw [inc, Nat.cast_add]
      rfl
    refine ⟨k + 1, hk1, ⟨le_rfl, ?_⟩, ?_⟩
    · rw [time_succ a (k + 1)]
      linarith
    · have node := gauge_node_ge (a := a) geo hk1 x
      have i2 : ((rowAt rows (k + 1)).incoming : ℝ) ≤ (rowAt rows (k + 1)).outgoing := by
        exact_mod_cast margin.incoming (k + 1) hk1
      calc gauge s₀ a rows (k + 1) (time a (k + 1), x)
          ≤ gauge s₀ a rows k (time a (k + 1), x) +
            (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := node
        _ ≤ (rowAt rows k).outgoing / (2 : ℝ) ^ 80 +
            (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := by linarith
        _ = (rowAt rows (k + 1)).incoming / (2 : ℝ) ^ 80 := by
          rw [inc']
          ring
        _ ≤ (rowAt rows (k + 1)).outgoing / (2 : ℝ) ^ 80 :=
          div_le_div_of_nonneg_right i2 (by positivity)
        _ < β (k + 1 + 1) := margin.outgoing (k + 1) hk1

/-- **The core is closed** as a subset of space-time. -/
theorem isClosed_coreTube (geo : Geo s₀ rows) :
    IsClosed {p : ℝ × Plane | p.2 ∈ core s₀ a rows p.1} := by
  have eq : {p : ℝ × Plane | p.2 ∈ core s₀ a rows p.1} =
      ⋃ k ∈ Finset.range rows.length, (Icc (time a k) (time a (k + 1)) ×ˢ univ) ∩
        gauge s₀ a rows k ⁻¹' Iic ((rowAt rows k).outgoing / (2 : ℝ) ^ 80) := by
    ext ⟨t, x⟩
    simp only [core, mem_ofPred_eq, mem_iUnion, Finset.mem_range, mem_inter_iff, mem_prod,
      mem_univ, and_true, mem_preimage, mem_Iic, exists_prop]
  rw [eq]
  exact isClosed_biUnion_finset fun k hk =>
    (continuousOn_gauge geo (Finset.mem_range.mp hk)).preimage_isClosed_of_isClosed
      (isClosed_Icc.prod isClosed_univ) isClosed_Iic

/-- The part of the core over a closed time interval is closed. -/
theorem isClosed_core (geo : Geo s₀ rows) (a' b' : ℝ) :
    IsClosed {p : ℝ × Plane | p.1 ∈ Icc a' b' ∧ p.2 ∈ core s₀ a rows p.1} :=
  (isClosed_Icc.preimage continuous_fst).inter (isClosed_coreTube geo)

/-- A curve in the recorded physical slabs has gauge at most the outgoing radius in every
slab. -/
theorem gauge_le_of_physicalSlabs {u : ℝ → Plane}
    (h : ∀ slab ∈ physicalSlabs s₀ a rows, ∀ t ∈ Icc slab.start slab.stop, u t ∈ slab.tube t)
    {k : ℕ} (hk : k < rows.length) {t : ℝ} (ht : t ∈ Icc (time a k) (time a (k + 1))) :
    gauge s₀ a rows k (t, u t) ≤ (rowAt rows k).outgoing / (2 : ℝ) ^ 80 := by
  rw [time_succ] at ht
  exact indexed (P := fun s r a => ∀ τ ∈ Icc a (a + 1 / 64),
      ‖(moving s r a τ).symm (u τ - reference a r τ)‖ ≤ r.outgoing / (2 : ℝ) ^ 80)
    (Q := fun s a rows => ∀ slab ∈ physicalSlabs s a rows,
      ∀ t ∈ Icc slab.start slab.stop, u t ∈ slab.tube t)
    (fun s a r _ h => ⟨fun τ hτ => (h (physicalSlab s r a) List.mem_cons_self τ hτ).1,
      fun slab hs => h slab (List.mem_cons_of_mem _ hs)⟩)
    rows s₀ a h k hk t ht

/-- **Points with label in the entry set lie in the core.** A solution on `[a, t]` in the
outer tube whose value at the initial time lies in the entry set of the chain lies in the
core at the time `t`. -/
theorem mem_core_of_label (steps : PositionFrameWideChain.Steps s₀ rows e)
    (bounds : FieldBoundsOn F J s₀ a rows domain) (lower : LowerOn J s₀ a rows)
    (hn : 0 < rows.length) {t : ℝ} (ht : t ∈ Icc a (time a rows.length)) {x : Plane}
    {v : ℝ → Plane} (hv : v t = x) (sol : FlowLabel.SolOn F (outer s₀ a rows) a t v)
    (start : v a ∈ stateSet s₀) : x ∈ core s₀ a rows t := by
  have geo := Geo.of_steps steps
  have len : a + (rows.length : ℝ) / 64 = time a rows.length := by
    simp only [time, PiecewiseTube.node]
    ring
  obtain ⟨u, u0, -, du, slabs⟩ := steps.trajectory bounds start
  rw [len] at du
  have gu : ∀ k < rows.length, ∀ τ ∈ Icc (time a k) (time a (k + 1)),
      gauge s₀ a rows k (τ, u τ) ≤ (rowAt rows k).outgoing / (2 : ℝ) ^ 80 :=
    fun k hk τ hτ => gauge_le_of_physicalSlabs slabs hk hτ
  have uo : ∀ τ ∈ Icc a (time a rows.length), u τ ∈ outer s₀ a rows τ := by
    intro τ hτ
    obtain ⟨k, hk, hmem⟩ := exists_slab_closed hn hτ
    obtain ⟨-, -, -, -, trial, -⟩ :=
      PositionFrameWide.growth_sound (Bool.and_eq_true_iff.mp (valid_at steps hk)).2
    exact ⟨k, hk, hmem, ((gu k hk τ hmem).trans_lt trial).le⟩
  obtain ⟨k, hk, hmem⟩ := exists_slab_closed hn ht
  have sol' : ∀ τ ∈ Icc a t,
      HasDerivWithinAt v (F τ (v τ)) (Icc a t) τ ∧ v τ ∈ outer s₀ a rows τ := by
    simpa only [FlowLabel.SolOn, uIcc_of_le ht.1] using sol
  have sub : Icc a t ⊆ Icc a (time a rows.length) := Icc_subset_Icc_right ht.2
  have start0 : a ∈ Icc (time a 0) (time a (0 + 1)) := by
    rw [time_succ, time_zero]
    exact ⟨le_rfl, by linarith⟩
  have eq := eq_of_eq_forward geo bounds lower hn hk start0 hmem ht.1
    (fun τ hτ => (du τ (sub hτ)).mono sub) (fun τ hτ => (sol' τ hτ).1)
    (fun τ hτ => uo τ (sub (Ioo_subset_Icc_self hτ)))
    (fun τ hτ => (sol' τ (Ioo_subset_Icc_self hτ)).2) u0
  rw [← hv, ← eq]
  exact ⟨k, hk, hmem, gu k hk t hmem⟩

end Core

/-! ### The doubled core -/

/-- The doubled inner tube is monotone in the tube. -/
theorem doubleV_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (σ : E ≃ₗᵢ[ℝ] E)
    {c b : ℝ} {V₁ V₂ : ℝ → Set E} (h : ∀ t ∈ Ico c b, V₁ t ⊆ V₂ t) {t : ℝ}
    (ht : t ∈ Ioo (2 * c - b) b) :
    FlowLabel.doubleV σ c V₁ t ⊆ FlowLabel.doubleV σ c V₂ t := by
  rcases lt_trichotomy c t with hct | heq | htc
  · rw [FlowLabel.doubleV_of_lt hct, FlowLabel.doubleV_of_lt hct]
    exact h t ⟨hct.le, ht.2⟩
  · rw [← heq, FlowLabel.doubleV_self, FlowLabel.doubleV_self]
    have hc := h c ⟨le_rfl, heq ▸ ht.2⟩
    exact inter_subset_inter hc (image_mono hc)
  · rw [FlowLabel.doubleV_of_gt htc, FlowLabel.doubleV_of_gt htc]
    exact image_mono (h _ ⟨by linarith, by linarith [ht.1]⟩)

/-- The core doubled by a reflection about the initial time, with the intersection of the two
halves at the initial time. -/
def coreV (refl : Plane ≃ₗᵢ[ℝ] Plane) (s₀ : State) (a : ℝ) (rows : List Step) (t : ℝ) :
    Set Plane :=
  FlowLabel.doubleV refl a (core s₀ a rows) t

/-- The core doubled by a reflection about the initial time, with the union of the two halves
at the initial time. -/
def coreD (refl : Plane ≃ₗᵢ[ℝ] Plane) (s₀ : State) (a : ℝ) (rows : List Step) (t : ℝ) :
    Set Plane :=
  FlowLabel.doubleW refl a (core s₀ a rows) t

/-- With the identity frame, the inverse frame map is the identity. -/
theorem frameEquiv_symm_identity {f : Frame} (h : f = ⟨2 ^ 40, 0, 0, 2 ^ 40⟩) (v : Plane) :
    (frameEquiv f f 0).symm v = v := by
  subst h
  have e : (frameEquiv ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ 0).symm v =
      backward ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ 0 v := by
    rw [← frameEquiv_backward (by norm_num [affineDet, entry])]
    rfl
  rw [e]
  ext i
  fin_cases i <;> norm_num [backward, affineDet, entry]

section Double

variable {s₀ e : State} {a : ℝ} {rows : List Step} {β : ℕ → ℝ}

/-- The doubled core with the intersection at the initial time lies in the doubled inner
tube. -/
theorem coreV_subset (steps : PositionFrameWideChain.Steps s₀ rows e) (margin : Margin rows β)
    (refl : Plane ≃ₗᵢ[ℝ] Plane) {t : ℝ}
    (ht : t ∈ Ioo (2 * a - time a rows.length) (time a rows.length)) :
    coreV refl s₀ a rows t ⊆ FlowLabel.doubleV refl a (inner s₀ a rows β) t :=
  doubleV_mono refl (fun _ ht => core_subset_inner steps margin ht.2) ht

/-- The two doubled cores agree when the core at the initial time is invariant under the
reflection. -/
theorem coreV_eq_coreD (refl : Plane ≃ₗᵢ[ℝ] Plane)
    (hsym : refl '' core s₀ a rows a = core s₀ a rows a) :
    coreV refl s₀ a rows = coreD refl s₀ a rows := by
  funext t
  rcases lt_trichotomy a t with hat | heq | hta
  · rw [coreV, coreD, FlowLabel.doubleV_of_lt hat, FlowLabel.doubleW_of_lt hat]
  · rw [coreV, coreD, ← heq, FlowLabel.doubleV_self, FlowLabel.doubleW_self, hsym, inter_self,
      union_self]
  · rw [coreV, coreD, FlowLabel.doubleV_of_gt hta, FlowLabel.doubleW_of_gt hta]

/-- **The doubled core lies in the doubled inner tube**, when the reflected core at the initial
time lies in the inner tube. -/
theorem coreD_subset (steps : PositionFrameWideChain.Steps s₀ rows e) (margin : Margin rows β)
    (refl : Plane ≃ₗᵢ[ℝ] Plane) (inv : ∀ x, refl (refl x) = x)
    (hsec : refl '' core s₀ a rows a ⊆ inner s₀ a rows β a) {t : ℝ}
    (ht : t ∈ Ioo (2 * a - time a rows.length) (time a rows.length)) :
    coreD refl s₀ a rows t ⊆ FlowLabel.doubleV refl a (inner s₀ a rows β) t := by
  rcases lt_trichotomy a t with hat | heq | hta
  · rw [coreD, FlowLabel.doubleW_of_lt hat, FlowLabel.doubleV_of_lt hat]
    exact core_subset_inner steps margin ht.2
  · have ha : a < time a rows.length := heq ▸ ht.2
    have sub := core_subset_inner (a := a) (t := a) steps margin ha
    rw [coreD, ← heq, FlowLabel.doubleW_self, FlowLabel.doubleV_self]
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact ⟨sub hx, (FlowLabel.mem_image_involution inv).mpr (hsec ⟨x, hx, rfl⟩)⟩
    · exact ⟨hsec ⟨y, hy, rfl⟩, mem_image_of_mem refl (sub hy)⟩
  · rw [coreD, FlowLabel.doubleW_of_gt hta, FlowLabel.doubleV_of_gt hta]
    exact image_mono (core_subset_inner steps margin (by linarith [ht.1]))

/-- **The doubled core is closed** as a subset of space-time. -/
theorem isClosed_coreD (geo : Geo s₀ rows) (refl : Plane ≃ₗᵢ[ℝ] Plane)
    (inv : ∀ x, refl (refl x) = x) :
    IsClosed {p : ℝ × Plane | p.2 ∈ coreD refl s₀ a rows p.1} := by
  have hH := isClosed_coreTube (a := a) geo
  have hΦ : Continuous fun q : ℝ × Plane => ((2 * a - q.1, refl q.2) : ℝ × Plane) :=
    (continuous_const.sub continuous_fst).prodMk (refl.continuous.comp continuous_snd)
  convert hH.union (hH.preimage hΦ) using 1
  ext ⟨t, x⟩
  simp only [coreD, mem_ofPred_eq, mem_union, mem_preimage]
  rcases lt_trichotomy a t with hat | heq | hta
  · rw [FlowLabel.doubleW_of_lt hat]
    refine ⟨Or.inl, ?_⟩
    rintro (h | h)
    · exact h
    · have := (core_time h).1
      linarith
  · rw [← heq, FlowLabel.doubleW_self, mem_union, FlowLabel.mem_image_involution inv,
      show 2 * a - a = a by ring]
  · rw [FlowLabel.doubleW_of_gt hta, FlowLabel.mem_image_involution inv]
    refine ⟨Or.inr, ?_⟩
    rintro (h | h)
    · have := (core_time h).1
      linarith
    · exact h

/-- The part of the doubled core over a closed time interval is closed. -/
theorem isClosed_coreD_window (geo : Geo s₀ rows) (refl : Plane ≃ₗᵢ[ℝ] Plane)
    (inv : ∀ x, refl (refl x) = x) (a' b' : ℝ) :
    IsClosed {p : ℝ × Plane | p.1 ∈ Icc a' b' ∧ p.2 ∈ coreD refl s₀ a rows p.1} :=
  (isClosed_Icc.preimage continuous_fst).inter (isClosed_coreD geo refl inv)

/-- With a core at the initial time that is invariant under the reflection, the doubled core
with the intersection at the initial time is closed over a closed time interval. -/
theorem isClosed_coreV_window (geo : Geo s₀ rows) (refl : Plane ≃ₗᵢ[ℝ] Plane)
    (inv : ∀ x, refl (refl x) = x) (hsym : refl '' core s₀ a rows a = core s₀ a rows a)
    (a' b' : ℝ) :
    IsClosed {p : ℝ × Plane | p.1 ∈ Icc a' b' ∧ p.2 ∈ coreV refl s₀ a rows p.1} := by
  rw [coreV_eq_coreD refl hsym]
  exact isClosed_coreD_window geo refl inv a' b'

/-- **The section hypothesis for the identity initial frame.** If the initial frame is the
identity, the reflection fixes the initial point, and the outgoing radius of the first record
with twice its jump is below the backward radius of the first slab, then the reflected core at
the initial time lies in the inner tube. -/
theorem section_of_identity (geo : Geo s₀ rows) (hn : 0 < rows.length)
    (hframe : s₀.frame = ⟨2 ^ 40, 0, 0, 2 ^ 40⟩) (refl : Plane ≃ₗᵢ[ℝ] Plane)
    (fix : refl (point s₀.point) = point s₀.point)
    (hβ : ((rowAt rows 0).outgoing + 2 * (rowAt rows 0).jumpBound : ℝ) / 2 ^ 80 < β 1) :
    refl '' core s₀ a rows a ⊆ inner s₀ a rows β a := by
  have frame : ∀ w : Plane, (frameAt s₀ a rows 0 a).symm w = w := by
    intro w
    have start := frameAt_start (a := a) geo hn
    rw [time_zero] at start
    rw [start]
    exact frameEquiv_symm_identity hframe w
  have g0 : ∀ y : Plane, gauge s₀ a rows 0 (a, y) = ‖y - reference a (rowAt rows 0) a‖ := by
    intro y
    change ‖(frameAt s₀ a rows 0 a).symm (y - reference (time a 0) (rowAt rows 0) a)‖ = _
    rw [frame, time_zero]
  have jump : ‖point s₀.point - reference a (rowAt rows 0) a‖ ≤
      (rowAt rows 0).jumpBound / (2 : ℝ) ^ 80 := by
    have hj := norm_reference_jump (geo.at hn)
    rw [frame_start (geo.at hn)] at hj
    change ‖(frameEquiv s₀.frame s₀.frame 0).symm
      (point s₀.point - point (firstPoint (rowAt rows 0)))‖ ≤ _ at hj
    rwa [frameEquiv_symm_identity hframe, ← reference_start a] at hj
  rintro _ ⟨y, ⟨k, hk, hmem, hg⟩, rfl⟩
  obtain rfl : k = 0 := by
    have h' : time a k ≤ time a 0 := by
      rw [time_zero]
      exact hmem.1
    exact Nat.le_zero.mp (time_le_iff.mp h')
  rw [g0] at hg
  refine ⟨0, hn, ?_, ?_⟩
  · rw [time_succ, time_zero]
    exact ⟨le_rfl, by linarith⟩
  · rw [g0]
    refine lt_of_le_of_lt ?_ hβ
    set q := reference a (rowAt rows 0) a
    set p := point s₀.point
    have split : refl y - q = refl (y - q) + (refl (q - p) - (q - p)) := by
      rw [map_sub, map_sub, fix]
      abel
    have n1 : ‖refl (y - q)‖ = ‖y - q‖ := refl.norm_map _
    have n2 : ‖refl (q - p) - (q - p)‖ ≤ ‖q - p‖ + ‖q - p‖ :=
      (norm_sub_le _ _).trans (by rw [refl.norm_map])
    have n3 : ‖q - p‖ = ‖p - q‖ := norm_sub_rev _ _
    rw [split]
    refine (norm_add_le _ _).trans ?_
    rw [add_div, mul_div_assoc]
    linarith

end Double

/-! ### Sanity: the stationary record -/

/-- The margin check accepts the stationary record with a positive radius at the end. -/
theorem marginCheck_stationary : marginCheck [stationary] [0, 1] = true := by
  with_unfolding_all rfl

/-- A radius at the end equal to the outgoing radius is rejected. -/
theorem marginCheck_reject : marginCheck [stationary] [0, 0] = false := by
  with_unfolding_all rfl

/-- A list of radii without an entry for the end of the last slab is rejected. -/
theorem marginCheck_short : marginCheck [stationary] [0] = false := by
  with_unfolding_all rfl

/-- The empty chain is accepted with any list of radii. -/
theorem marginCheck_nil (bs : List ℕ) : marginCheck [] bs = true := rfl

/-- The core of the empty chain is empty. -/
theorem core_nil (s₀ : State) (a t : ℝ) : core s₀ a [] t = ∅ := by
  ext x
  simp [core]

/-- The stationary record is a chain of valid wide steps. -/
theorem stationary_steps :
    PositionFrameWideChain.Steps (next stationary) [stationary] (next stationary) :=
  ⟨by with_unfolding_all rfl, rfl⟩

/-- Non-vacuity: for the stationary record with the zero field the hypotheses of
`mem_core_of_label` hold together, and every reference point of the slab lies in the core. -/
theorem stationary_mem_core (a : ℝ) {t : ℝ} (ht : t ∈ Icc a (a + 1 / 64)) :
    reference a stationary t ∈ core (next stationary) a [stationary] t := by
  have velocity (τ : ℝ) : referenceVelocity a stationary τ = 0 := by
    ext i
    fin_cases i <;> norm_num [referenceVelocity, polynomial, stationary,
      TrajectoryTaylorModel.ofDyadic, QPoly.scale, QPoly.deriv, QPoly.add, QPoly.eval,
      List.replicate_succ]
  have ht' : t ∈ Icc a (time a [stationary].length) := by
    change t ∈ Icc a (time a (0 + 1))
    rwa [time_succ, time_zero]
  have zero (τ : ℝ) : reference a stationary τ - reference (time a 0) (rowAt [stationary] 0) τ
      = 0 := by
    rw [time_zero]
    exact sub_self _
  refine mem_core_of_label (F := fun _ _ => 0) (J := fun _ _ => 0) stationary_steps
    (stationary_bounds a) (⟨lower_stationary a, trivial⟩ : LowerOn _ _ a [stationary])
    Nat.zero_lt_one ht' rfl ?_ ?_
  · intro τ hτ
    rw [uIcc_of_le ht.1] at hτ
    refine ⟨?_, 0, Nat.zero_lt_one, ?_, ?_⟩
    · have d := hasDerivAt_reference a stationary τ
      rw [velocity] at d
      exact d.hasDerivWithinAt
    · rw [time_succ, time_zero]
      exact ⟨hτ.1, hτ.2.trans ht.2⟩
    · change ‖(frameAt (next stationary) a [stationary] 0 τ).symm
        (reference a stationary τ - reference (time a 0) (rowAt [stationary] 0) τ)‖ ≤ _
      rw [zero, map_zero, norm_zero]
      positivity
  · change ‖(frameEquiv (next stationary).frame (next stationary).frame 0).symm
      (reference a stationary a - point (next stationary).point)‖ ≤ _
    have e : firstPoint stationary = (next stationary).point := by with_unfolding_all rfl
    rw [reference_start, e, sub_self, map_zero, norm_zero]
    positivity

/-- Non-vacuity: for the stationary record the doubled core lies in the doubled inner tube
with the radii of the accepted margin check, for the identity reflection. -/
theorem stationary_coreV_subset (a : ℝ) {t : ℝ} (ht : t ∈ Ioo (2 * a - time a 1) (time a 1)) :
    coreV (LinearIsometryEquiv.refl ℝ Plane) (next stationary) a [stationary] t ⊆
      FlowLabel.doubleV (LinearIsometryEquiv.refl ℝ Plane) a
        (inner (next stationary) a [stationary] fun k => (([0, 1] : List ℕ).getD k 0 : ℝ) / 2 ^ 80)
        t :=
  coreV_subset stationary_steps (margin_of_check marginCheck_stationary) _ ht

/-- Non-vacuity: the doubled core of the stationary record is closed. -/
theorem stationary_isClosed_coreD (a : ℝ) :
    IsClosed {p : ℝ × Plane |
      p.2 ∈ coreD (LinearIsometryEquiv.refl ℝ Plane) (next stationary) a [stationary] p.1} :=
  isClosed_coreD stationary_geo _ (fun _ => rfl)

end PlasmaLean.Certificates.PositionFrameTube
