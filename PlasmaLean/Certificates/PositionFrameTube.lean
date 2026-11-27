/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameBackward
public import PlasmaLean.Certificates.PositionFrameWideChain
public import PlasmaLean.Theory.Fields.FlowLabel
public import PlasmaLean.Theory.Fields.PiecewiseTube

/-!
# The tube of a chain of position-frame slabs: reachability, distances, openness

A chain of position-frame records with two-sided bounds on the frame Jacobian describes a
tube around the traced curve, slab by slab. Slab `k` occupies the times
`[time a k, time a (k+1)]` and measures the deviation from its reference in its own moving
frame (`gauge`). The outer tube consists of the points whose gauge is at most the trial radius
of their slab; the inner tube is given by a sequence of backward radii `β`.

* `reach`: from every point of the inner tube a solution runs back to the initial time
  inside the outer tube and lands in the frame ball of radius `β 0` around the initial point.
* `frame_dist_chain`, `dist_chain`, `eq_of_eq`: two solutions in the outer tube are no further
  apart at an earlier time than a fixed factor times their distance at a later time.
* `frame_inv_op_norm`: bound for the inverse frame matrix.
* `inner_relOpen`: the inner tube is open relative to the half-space of times not before the
  initial one.
* `stationary_reach`: the hypotheses hold together for the stationary record.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameTube

open Set PositionFrameSlabs PositionFrameBackward Filter Topology
open PlasmaLean.Fields

/-! ### Indexing the slabs -/

/-- Start time of slab `k`: the node `a + k / 64`. -/
def time (a : ℝ) (k : ℕ) : ℝ := PiecewiseTube.node a (1 / 64) k

theorem time_zero (a : ℝ) : time a 0 = a := PiecewiseTube.node_zero a _

theorem time_succ (a : ℝ) (k : ℕ) : time a (k + 1) = time a k + 1 / 64 :=
  PiecewiseTube.node_succ a _ k

/-- Shifting the initial time by one slab shifts the index. -/
theorem time_shift (a : ℝ) (k : ℕ) : time (a + 1 / 64) k = time a (k + 1) := by
  simp only [time, PiecewiseTube.node, Nat.cast_add, Nat.cast_one]
  ring

theorem time_le_iff {a : ℝ} {j k : ℕ} : time a j ≤ time a k ↔ j ≤ k := by
  have h : time a j ≤ time a k ↔ (j : ℝ) ≤ k := by
    simp only [time, PiecewiseTube.node]
    constructor <;> intro h <;> linarith
  rw [h, Nat.cast_le]

theorem time_le {a : ℝ} {j k : ℕ} (h : j ≤ k) : time a j ≤ time a k := time_le_iff.mpr h

/-- The record of slab `k` (the stationary record beyond the end of the list). -/
def rowAt (rows : List Step) (k : ℕ) : Step := rows.getD k stationary

/-- The state before slab `k`. -/
def stateAt (s₀ : State) (rows : List Step) : ℕ → State
  | 0 => s₀
  | k + 1 => next (rowAt rows k)

theorem rowAt_cons_succ (r : Step) (rs : List Step) (k : ℕ) :
    rowAt (r :: rs) (k + 1) = rowAt rs k := rfl

theorem stateAt_cons_succ (s₀ : State) (r : Step) (rs : List Step) (k : ℕ) :
    stateAt s₀ (r :: rs) (k + 1) = stateAt (next r) rs k := by
  cases k <;> rfl

/-- A property of consecutive records, given in recursive form over the list, holds for
every slab in indexed form. -/
theorem indexed {P : State → Step → ℝ → Prop} {Q : State → ℝ → List Step → Prop}
    (hQ : ∀ s a r rs, Q s a (r :: rs) → P s r a ∧ Q (next r) (a + 1 / 64) rs) :
    ∀ (rows : List Step) (s : State) (a : ℝ), Q s a rows → ∀ k < rows.length,
      P (stateAt s rows k) (rowAt rows k) (time a k)
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | r :: rs, s, a, h, 0, _ => by
    change P s r (time a 0)
    rw [time_zero]
    exact (hQ s a r rs h).1
  | r :: rs, s, a, h, k + 1, hk => by
    have tail := indexed hQ rs (next r) (a + 1 / 64) (hQ s a r rs h).2 k
      (Nat.lt_of_succ_lt_succ hk)
    rwa [stateAt_cons_succ, rowAt_cons_succ, ← time_shift]

/-! ### Hypotheses in list form -/

/-- Every record passes the geometric check from the state left by its predecessor. -/
def Geo : State → List Step → Prop
  | _, [] => True
  | s, r :: rs => geometry allLimits s r = true ∧ Geo (next r) rs

/-- A chain of valid wide steps passes the geometric checks. -/
theorem Geo.of_steps {s e : State} {rows : List Step}
    (h : PositionFrameWideChain.Steps s rows e) : Geo s rows := by
  induction rows generalizing s with
  | nil => trivial
  | cons r rs ih => exact ⟨(Bool.and_eq_true_iff.mp h.1).1, ih h.2⟩

/-- Geometric check of slab `k`. -/
theorem Geo.at {s₀ : State} {rows : List Step} (h : Geo s₀ rows) {k : ℕ}
    (hk : k < rows.length) :
    geometry allLimits (stateAt s₀ rows k) (rowAt rows k) = true :=
  indexed (P := fun s r _ => geometry allLimits s r = true) (Q := fun s _ rows => Geo s rows)
    (fun _ _ _ _ h => h) rows s₀ 0 h k hk

/-- Field bounds of slab `k`. -/
theorem fieldBounds_at {domain : RegularityDomain} {F : ℝ → Plane → Plane}
    {J : ℝ → Plane → Plane →L[ℝ] Plane} {s₀ : State} {a : ℝ} {rows : List Step}
    (h : FieldBoundsOn F J s₀ a rows domain) {k : ℕ} (hk : k < rows.length) :
    FieldBounds (stateAt s₀ rows k) (rowAt rows k) (time a k) F J domain :=
  indexed (P := fun s r a => FieldBounds s r a F J domain)
    (Q := fun s a rows => FieldBoundsOn F J s a rows domain) (fun _ _ _ _ h => h) rows s₀ a h k hk

/-- Lower bounds for the frame Jacobian on the consecutive records of one trajectory. -/
def LowerOn (J : ℝ → Plane → Plane →L[ℝ] Plane) (s : State) (a : ℝ) (rows : List Step) : Prop :=
  match rows with
  | [] => True
  | r :: rs => Lower s r a J ∧ LowerOn J (next r) (a + 1 / 64) rs

/-- Lower bound of slab `k`. -/
theorem LowerOn.at {J : ℝ → Plane → Plane →L[ℝ] Plane} {s₀ : State} {a : ℝ} {rows : List Step}
    (h : LowerOn J s₀ a rows) {k : ℕ} (hk : k < rows.length) :
    Lower (stateAt s₀ rows k) (rowAt rows k) (time a k) J :=
  indexed (P := fun s r a => Lower s r a J) (Q := fun s a rows => LowerOn J s a rows)
    (fun _ _ _ _ h => h) rows s₀ a h k hk

/-- The lower bounds of consecutive lists compose; the second list starts at the angle
and state where the first one ends. -/
theorem lowerOn_append {s m : State} {a b : ℝ} {l r : List Step}
    {J : ℝ → Plane → Plane →L[ℝ] Plane} (h : PositionFrameWideChain.Steps s l m)
    (b₁ : LowerOn J s a l) (hb : b = a + l.length / 64) (b₂ : LowerOn J m b r) :
    LowerOn J s a (l ++ r) := by
  induction l generalizing s a with
  | nil =>
    change s = m at h
    cases h
    have : b = a := by simpa using hb
    rw [← this]
    exact b₂
  | cons x xs ih =>
    refine ⟨b₁.1, ih (h := h.2) (b₁ := b₁.2) (hb := ?_)⟩
    rw [hb, List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- Backward radii: `β (k+1)` at the times of slab `k` propagates back to `σ k` at the start
of the slab, below the trial radius, and `σ k` with the reference jump is at most `β k`. -/
structure Radii (rows : List Step) (β σ : ℕ → ℝ) : Prop where
  /-- the radii are nonnegative -/
  nonneg : ∀ k < rows.length, 0 ≤ β (k + 1)
  /-- the recorded defects are nonnegative -/
  defect : ∀ k < rows.length, 0 ≤ ((rowAt rows k).defect : ℝ)
  /-- the growth over one slab is less than one -/
  rate : ∀ k < rows.length, max 0 ((rowAt rows k).mu : ℝ) / 64 < 1
  /-- the propagated radius is at most `σ k` -/
  back : ∀ k < rows.length, (β (k + 1) + (rowAt rows k).defect / 64) /
    (1 - max 0 ((rowAt rows k).mu : ℝ) / 64) ≤ σ k
  /-- `σ k` is below the trial radius -/
  trial : ∀ k < rows.length, σ k < (rowAt rows k).trial / (2 : ℝ) ^ 80
  /-- `σ k` with the reference jump is at most `β k` -/
  jump : ∀ k < rows.length, σ k + (rowAt rows k).jumpBound / (2 : ℝ) ^ 80 ≤ β k

/-- The radius after the backward step is not smaller than before it. -/
theorem Radii.le {rows : List Step} {β σ : ℕ → ℝ} (h : Radii rows β σ) {k : ℕ}
    (hk : k < rows.length) : β (k + 1) ≤ σ k := by
  have rate := h.rate k hk
  have pos : 0 < 1 - max 0 ((rowAt rows k).mu : ℝ) / 64 := by linarith
  have m0 : 0 ≤ max 0 ((rowAt rows k).mu : ℝ) / 64 := div_nonneg (le_max_left _ _) (by norm_num)
  refine le_trans ((le_div_iff₀ pos).mpr ?_) (h.back k hk)
  have := mul_nonneg (h.nonneg k hk) m0
  have := div_nonneg (h.defect k hk) (by norm_num : (0 : ℝ) ≤ 64)
  nlinarith

/-! ### Frames, gauges and tubes -/

/-- The moving frame of slab `k`. -/
def frameAt (s₀ : State) (a : ℝ) (rows : List Step) (k : ℕ) (t : ℝ) : Plane ≃L[ℝ] Plane :=
  moving (stateAt s₀ rows k) (rowAt rows k) (time a k) t

/-- Deviation of a space-time point from the reference of slab `k`, in the frame of that slab. -/
def gauge (s₀ : State) (a : ℝ) (rows : List Step) (k : ℕ) (p : ℝ × Plane) : ℝ :=
  ‖(frameAt s₀ a rows k p.1).symm (p.2 - reference (time a k) (rowAt rows k) p.1)‖

/-- The outer tube: points within the trial radius of a closed slab containing the time. -/
def outer (s₀ : State) (a : ℝ) (rows : List Step) (t : ℝ) : Set Plane :=
  {x | ∃ k < rows.length, t ∈ Icc (time a k) (time a (k + 1)) ∧
    gauge s₀ a rows k (t, x) ≤ (rowAt rows k).trial / (2 : ℝ) ^ 80}

/-- The inner tube: points strictly within the backward radius of their half-open slab. -/
def inner (s₀ : State) (a : ℝ) (rows : List Step) (β : ℕ → ℝ) (t : ℝ) : Set Plane :=
  {x | ∃ k < rows.length, t ∈ Ico (time a k) (time a (k + 1)) ∧
    gauge s₀ a rows k (t, x) < β (k + 1)}

/-- The inner tube as a subset of space-time. -/
def innerTube (s₀ : State) (a : ℝ) (rows : List Step) (β : ℕ → ℝ) : Set (ℝ × Plane) :=
  {p | p.1 ∈ Ico a (time a rows.length) ∧ p.2 ∈ inner s₀ a rows β p.1}

/-- The inner tube lies over the time interval of the chain. -/
theorem inner_time {s₀ : State} {a : ℝ} {rows : List Step} {β : ℕ → ℝ} {t : ℝ} {x : Plane}
    (hx : x ∈ inner s₀ a rows β t) : t ∈ Ico a (time a rows.length) := by
  obtain ⟨k, hk, ht, _⟩ := hx
  have h₀ : time a 0 ≤ time a k := time_le (Nat.zero_le k)
  rw [time_zero] at h₀
  exact ⟨h₀.trans ht.1, ht.2.trans_le (time_le hk)⟩

/-- The inner tube is the slab-wise region of the gauges with the radii `β (k+1)`. -/
theorem innerTube_eq_region (s₀ : State) (a : ℝ) (rows : List Step) (β : ℕ → ℝ) :
    innerTube s₀ a rows β =
      PiecewiseTube.region a (1 / 64) rows.length (gauge s₀ a rows) (fun k => β (k + 1)) := by
  ext p
  exact ⟨fun h => h.2, fun h => ⟨inner_time h, h⟩⟩

/-- A time in the interior of slab `i` lies in no other closed slab. -/
theorem slab_unique {a τ : ℝ} {i j : ℕ} (hi : τ ∈ Ioo (time a i) (time a (i + 1)))
    (hj : τ ∈ Icc (time a j) (time a (j + 1))) : j = i := by
  have h₁ : ¬ time a (i + 1) ≤ time a j := not_le.mpr (hi.2.trans_le' hj.1)
  have h₂ : ¬ time a (j + 1) ≤ time a i := not_le.mpr (hi.1.trans_le hj.2)
  rw [time_le_iff] at h₁ h₂
  omega

/-- At the start of a slab the moving frame is the frame of the incoming state. -/
theorem moving_start {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    (a : ℝ) : moving s r a a = frameEquiv s.frame s.frame 0 := by
  simpa [moving, coord] using frame_start h

/-- At the end of a slab the moving frame is the frame of the outgoing state. -/
theorem moving_end {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    (a : ℝ) : moving s r a (a + 1 / 64) = frameEquiv r.frame r.frame 0 := by
  have z : coord a (a + 1 / 64) = 1 := by unfold coord; ring
  simpa only [moving, z] using frame_end h

/-- Passing from the reference of a slab at its start to the point of the incoming state
costs the recorded jump. -/
theorem start_shift {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    (a : ℝ) (y : Plane) :
    ‖(frameEquiv s.frame s.frame 0).symm (y - point s.point)‖ ≤
      ‖(moving s r a a).symm (y - reference a r a)‖ + r.jumpBound / (2 : ℝ) ^ 80 := by
  have hj := norm_reference_jump h
  rw [frame_start h] at hj
  rw [moving_start h, reference_start]
  have split : (frameEquiv s.frame s.frame 0).symm (y - point s.point) =
      (frameEquiv s.frame s.frame 0).symm (y - point (firstPoint r)) -
        (frameEquiv s.frame s.frame 0).symm (point s.point - point (firstPoint r)) := by
    rw [← map_sub]
    congr 1
    abel
  rw [split]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hj)

section Chain

variable {domain : RegularityDomain} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
  {s₀ : State} {a : ℝ} {rows : List Step} {β σ : ℕ → ℝ}

/-- At the end of slab `k` its frame is the frame of the next state. -/
theorem frameAt_end (geo : Geo s₀ rows) {k : ℕ} (hk : k < rows.length) :
    frameAt s₀ a rows k (time a (k + 1)) =
      frameEquiv (stateAt s₀ rows (k + 1)).frame (stateAt s₀ rows (k + 1)).frame 0 := by
  rw [time_succ]
  exact moving_end (geo.at hk) _

/-- At the start of slab `k` its frame is the frame of the state before it. -/
theorem frameAt_start (geo : Geo s₀ rows) {k : ℕ} (hk : k < rows.length) :
    frameAt s₀ a rows k (time a k) =
      frameEquiv (stateAt s₀ rows k).frame (stateAt s₀ rows k).frame 0 :=
  moving_start (geo.at hk) _

/-- The frames of adjacent slabs agree at their common node. -/
theorem frameAt_node (geo : Geo s₀ rows) {k : ℕ} (hk : k + 1 < rows.length) :
    frameAt s₀ a rows k (time a (k + 1)) = frameAt s₀ a rows (k + 1) (time a (k + 1)) :=
  (frameAt_end geo (Nat.lt_of_succ_lt hk)).trans (frameAt_start geo hk).symm

/-- The gauge of slab `k` at its end measures the distance from the point of the next
state in the frame of that state. -/
theorem gauge_end (geo : Geo s₀ rows) {k : ℕ} (hk : k < rows.length) (x : Plane) :
    gauge s₀ a rows k (time a (k + 1), x) =
      ‖(frameEquiv (stateAt s₀ rows (k + 1)).frame (stateAt s₀ rows (k + 1)).frame 0).symm
        (x - point (stateAt s₀ rows (k + 1)).point)‖ := by
  have ref : reference (time a k) (rowAt rows k) (time a (k + 1)) =
      point (stateAt s₀ rows (k + 1)).point := by
    rw [time_succ]
    exact reference_end _ _
  change ‖(frameAt s₀ a rows k (time a (k + 1))).symm
    (x - reference (time a k) (rowAt rows k) (time a (k + 1)))‖ = _
  rw [frameAt_end geo hk, ref]

/-- The distance from the point of the state before slab `k`, in the frame of that state, is
at most the gauge of slab `k` at its start plus the recorded jump. -/
theorem state_dist_le (geo : Geo s₀ rows) {k : ℕ} (hk : k < rows.length) (x : Plane) :
    ‖(frameEquiv (stateAt s₀ rows k).frame (stateAt s₀ rows k).frame 0).symm
      (x - point (stateAt s₀ rows k).point)‖ ≤
      gauge s₀ a rows k (time a k, x) + (rowAt rows k).jumpBound / (2 : ℝ) ^ 80 :=
  start_shift (geo.at hk) (time a k) x

/-- At a node the gauge of the earlier slab exceeds the gauge of the later slab by at most
the jump of the later slab. -/
theorem gauge_node_le (geo : Geo s₀ rows) {k : ℕ} (hk : k + 1 < rows.length) (x : Plane) :
    gauge s₀ a rows k (time a (k + 1), x) ≤
      gauge s₀ a rows (k + 1) (time a (k + 1), x) +
        (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := by
  rw [gauge_end geo (Nat.lt_of_succ_lt hk)]
  exact state_dist_le geo hk x

/-- Each gauge is continuous on its closed slab. -/
theorem continuousOn_gauge (geo : Geo s₀ rows) {k : ℕ} (hk : k < rows.length) :
    ContinuousOn (gauge s₀ a rows k) (Icc (time a k) (time a (k + 1)) ×ˢ univ) := by
  have inv := continuousOn_frame_inverse (geo.at hk) (time a k)
  rw [← time_succ] at inv
  have c₁ : ContinuousOn (fun p : ℝ × Plane =>
      (frameEquiv (stateAt s₀ rows k).frame (rowAt rows k).frame
        (coord (time a k) p.1)).symm.toContinuousLinearMap)
      (Icc (time a k) (time a (k + 1)) ×ˢ univ) :=
    inv.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have cref : Continuous (reference (time a k) (rowAt rows k)) :=
    continuous_iff_continuousAt.mpr fun t => (hasDerivAt_reference _ _ t).continuousAt
  exact (c₁.clm_apply (continuous_snd.sub (cref.comp continuous_fst)).continuousOn).norm

/-! ### Backward reachability -/

private theorem glue {b c d : ℝ} {u v : ℝ → Plane}
    (hbc : b ≤ c) (hcd : c ≤ d) (join : u c = v c)
    (hu : ∀ t ∈ Icc b c, HasDerivWithinAt u (F t (u t)) (Icc b c) t)
    (hv : ∀ t ∈ Icc c d, HasDerivWithinAt v (F t (v t)) (Icc c d) t) :
    ∃ w : ℝ → Plane, EqOn w u (Icc b c) ∧ EqOn w v (Icc c d) ∧
      ∀ t ∈ Icc b d, HasDerivWithinAt w (F t (w t)) (Icc b d) t := by
  let w := fun t => if t ≤ c then u t else v t
  have left : EqOn w u (Icc b c) := fun _ ht => ite_eq_left ht.2
  have right : EqOn w v (Icc c d) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | h
    · simpa [w] using join
    · exact ite_eq_right h.not_ge
  refine ⟨w, left, right, fun t _ => ?_⟩
  have side {l r : ℝ} {z : ℝ → Plane} (he : EqOn w z (Icc l r))
      (hd : ∀ y ∈ Icc l r, HasDerivWithinAt z (F y (z y)) (Icc l r) y) :
      HasDerivWithinAt w (F t (w t)) (Icc l r) t := by
    by_cases hit : t ∈ Icc l r
    · rw [he hit]
      exact (hd t hit).congr_of_mem (fun _ h => he h) hit
    · exact HasFDerivWithinAt.of_notMem_closure (by rwa [isClosed_Icc.closure_eq])
  rw [← Icc_union_Icc_eq_Icc hbc hcd]
  exact (side left hu).union (side right hv)

/-- Backward step in slab `k`, in terms of the gauge. -/
theorem slab_back (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) (radii : Radii rows β σ) {k : ℕ} (hk : k < rows.length)
    {t : ℝ} (ht : t ∈ Icc (time a k) (time a (k + 1))) {x : Plane}
    (hx : gauge s₀ a rows k (t, x) ≤ β (k + 1)) :
    ∃ v : ℝ → Plane, v t = x ∧ ∀ τ ∈ Icc (time a k) t,
      HasDerivWithinAt v (F τ (v τ)) (Icc (time a k) t) τ ∧
      gauge s₀ a rows k (τ, v τ) ≤ σ k := by
  rw [time_succ] at ht
  exact backward_step (geo.at hk) (fieldBounds_at bounds hk) (lower.at hk) (radii.defect k hk)
    (radii.rate k hk) (radii.nonneg k hk) (radii.back k hk) (radii.trial k hk) ht hx

/-- Backward reachability from a closed slab: every point within gauge `β (k+1)` of slab `k`
is the value of a solution defined back to the initial time, which stays in the outer tube
and lands within `β 0` of the initial point in the initial frame. -/
theorem reach_closed (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) (radii : Radii rows β σ) :
    ∀ k < rows.length, ∀ t ∈ Icc (time a k) (time a (k + 1)), ∀ x : Plane,
      gauge s₀ a rows k (t, x) ≤ β (k + 1) →
      ∃ v : ℝ → Plane, v t = x ∧
        (∀ τ ∈ Icc a t, HasDerivWithinAt v (F τ (v τ)) (Icc a t) τ ∧ v τ ∈ outer s₀ a rows τ) ∧
        ‖(frameEquiv s₀.frame s₀.frame 0).symm (v a - point s₀.point)‖ ≤ β 0 := by
  intro k
  induction k with
  | zero =>
    intro hk t ht x hx
    obtain ⟨v, stop, sol⟩ := slab_back geo bounds lower radii hk ht hx
    have land := (state_dist_le (a := a) geo hk (v (time a 0))).trans
      ((add_le_add (sol (time a 0) ⟨le_rfl, ht.1⟩).2 le_rfl).trans (radii.jump 0 hk))
    have hz := time_zero a
    rw [hz] at sol land
    refine ⟨v, stop, fun τ hτ => ⟨(sol τ hτ).1, 0, hk, ⟨?_, hτ.2.trans ht.2⟩,
      ((sol τ hτ).2.trans_lt (radii.trial 0 hk)).le⟩, land⟩
    rw [hz]
    exact hτ.1
  | succ k ih =>
    intro hk t ht x hx
    have hk' : k < rows.length := Nat.lt_of_succ_lt hk
    obtain ⟨v₁, stop, sol⟩ := slab_back geo bounds lower radii hk ht hx
    have node : gauge s₀ a rows k (time a (k + 1), v₁ (time a (k + 1))) ≤ β (k + 1) :=
      (gauge_node_le geo hk _).trans
        ((add_le_add (sol _ ⟨le_rfl, ht.1⟩).2 le_rfl).trans (radii.jump (k + 1) hk))
    obtain ⟨u, join, before, land⟩ := ih hk' (time a (k + 1))
      ⟨time_le (Nat.le_succ k), le_rfl⟩ _ node
    have h₀ : a ≤ time a (k + 1) := by
      have := time_le (a := a) (Nat.zero_le (k + 1))
      rwa [time_zero] at this
    obtain ⟨w, left, right, global⟩ := glue h₀ ht.1 join (fun τ hτ => (before τ hτ).1)
      (fun τ hτ => (sol τ hτ).1)
    refine ⟨w, (right ⟨ht.1, le_rfl⟩).trans stop, fun τ hτ => ⟨global τ hτ, ?_⟩, ?_⟩
    · rcases le_total τ (time a (k + 1)) with h | h
      · rw [left ⟨hτ.1, h⟩]
        exact (before τ ⟨hτ.1, h⟩).2
      · rw [right ⟨h, hτ.2⟩]
        exact ⟨k + 1, hk, ⟨h, hτ.2.trans ht.2⟩,
          ((sol τ ⟨h, hτ.2⟩).2.trans_lt (radii.trial (k + 1) hk)).le⟩
    · rw [left ⟨le_rfl, h₀⟩]
      exact land

/-- **Backward reachability.** From every point of the inner tube a solution runs back to the
initial time `a` inside the outer tube, and its value at `a` lies within `β 0` of the initial
point `point s₀.point` in the initial frame `frameEquiv s₀.frame s₀.frame 0`. -/
theorem reach (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) (radii : Radii rows β σ) {t : ℝ} {x : Plane}
    (hx : x ∈ inner s₀ a rows β t) :
    ∃ v : ℝ → Plane, v t = x ∧ FlowLabel.SolOn F (outer s₀ a rows) a t v ∧
      ‖(frameEquiv s₀.frame s₀.frame 0).symm (v a - point s₀.point)‖ ≤ β 0 := by
  have ha := (inner_time hx).1
  obtain ⟨k, hk, ht, hg⟩ := hx
  obtain ⟨v, stop, sol, land⟩ := reach_closed geo bounds lower radii k hk t
    ⟨ht.1, ht.2.le⟩ x hg.le
  refine ⟨v, stop, ?_, land⟩
  intro τ hτ
  rw [uIcc_of_le ha] at hτ ⊢
  exact sol τ hτ

/-! ### Distances towards the initial time -/

/-- Two solutions in the outer tube between two times of one slab: the frame distance at the
earlier time is at most `exp (max 0 μ / 64)` times the frame distance at the later time. -/
theorem slab_dist (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {k : ℕ} (hk : k < rows.length) {t₀ t₁ : ℝ}
    (h₀ : time a k ≤ t₀) (h₀₁ : t₀ ≤ t₁) (h₁ : t₁ ≤ time a (k + 1)) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt u (F τ (u τ)) (Icc t₀ t₁) τ)
    (hv : ∀ τ ∈ Icc t₀ t₁, HasDerivWithinAt v (F τ (v τ)) (Icc t₀ t₁) τ)
    (mu : ∀ τ ∈ Ioo t₀ t₁, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo t₀ t₁, v τ ∈ outer s₀ a rows τ) :
    ‖(frameAt s₀ a rows k t₀).symm (u t₀ - v t₀)‖ ≤
      Real.exp (max 0 ((rowAt rows k).mu : ℝ) / 64) *
        ‖(frameAt s₀ a rows k t₁).symm (u t₁ - v t₁)‖ := by
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
    (inside mu) (inside mv)).1).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)

private theorem chain_le (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {i : ℕ} {s : ℝ} (hs : s ≤ time a (i + 1))
    (hs' : time a i ≤ s) {u v : ℝ → Plane} :
    ∀ k, i ≤ k → k < rows.length → ∀ t ∈ Icc (time a k) (time a (k + 1)), s ≤ t →
      (∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ) →
      (∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ) →
      (∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ) → (∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) →
      ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ ≤
        Real.exp (∑ j ∈ Finset.Ico i (k + 1), max 0 ((rowAt rows j).mu : ℝ) / 64) *
          ‖(frameAt s₀ a rows k t).symm (u t - v t)‖ := by
  intro k hik
  induction k, hik using Nat.le_induction with
  | base =>
    intro hk t ht hst hu hv mu mv
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    exact slab_dist geo bounds lower hk hs' hst ht.2 hu hv mu mv
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
    have second := slab_dist geo bounds lower hk le_rfl ht.1 ht.2
      (fun τ hτ => (hu τ (sub₂ hτ)).mono sub₂) (fun τ hτ => (hv τ (sub₂ hτ)).mono sub₂)
      (fun τ hτ => mu τ (sub₂' hτ)) (fun τ hτ => mv τ (sub₂' hτ))
    rw [Finset.sum_Ico_succ_top (Nat.le_succ_of_le hik), Real.exp_add, mul_assoc]
    exact first.trans (mul_le_mul_of_nonneg_left second (Real.exp_pos _).le)

/-- **Frame distances along the chain.** Two solutions on `[s, t]` that lie in the outer tube
at the times strictly between `s` and `t`: their distance at `s`, in the frame of a slab `i`
containing `s`, is at most `exp E` times their distance at `t` in the frame of a slab `k`
containing `t`, where `E` bounds the sum of the growth exponents of all slabs. -/
theorem frame_dist_chain (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {E : ℝ}
    (hE : ∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 ≤ E)
    {i k : ℕ} (hi : i < rows.length) (hk : k < rows.length) {s t : ℝ}
    (hs : s ∈ Icc (time a i) (time a (i + 1))) (ht : t ∈ Icc (time a k) (time a (k + 1)))
    (hst : s ≤ t) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (mu : ∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) :
    ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ ≤
      Real.exp E * ‖(frameAt s₀ a rows k t).symm (u t - v t)‖ := by
  have term (j : ℕ) : 0 ≤ max 0 ((rowAt rows j).mu : ℝ) / 64 :=
    div_nonneg (le_max_left _ _) (by norm_num)
  rcases le_or_gt i k with hik | hki
  · refine (chain_le geo bounds lower hs.2 hs.1 k hik hk t ht hst hu hv mu mv).trans ?_
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

/-- **Distances along the chain.** With bounds `A` for the frame at `s` and `Binv` for the
inverse frame at `t`, the Euclidean distance of the two solutions at `s` is at most
`A * exp E * Binv` times their distance at `t`. -/
theorem dist_chain (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) {E : ℝ}
    (hE : ∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 ≤ E)
    {i k : ℕ} (hi : i < rows.length) (hk : k < rows.length) {s t : ℝ}
    (hs : s ∈ Icc (time a i) (time a (i + 1))) (ht : t ∈ Icc (time a k) (time a (k + 1)))
    (hst : s ≤ t) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (mu : ∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) {A Binv : ℝ}
    (hA : ‖(frameAt s₀ a rows i s).toContinuousLinearMap‖ ≤ A)
    (hB : ‖(frameAt s₀ a rows k t).symm.toContinuousLinearMap‖ ≤ Binv) :
    ‖u s - v s‖ ≤ A * Real.exp E * Binv * ‖u t - v t‖ := by
  have A0 : 0 ≤ A := (norm_nonneg _).trans hA
  have chain := frame_dist_chain geo bounds lower hE hi hk hs ht hst hu hv mu mv
  have fwd : ‖u s - v s‖ ≤ A * ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ := by
    have h := ((frameAt s₀ a rows i s).toContinuousLinearMap.le_opNorm
      ((frameAt s₀ a rows i s).symm (u s - v s))).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
    simpa using h
  have back : ‖(frameAt s₀ a rows k t).symm (u t - v t)‖ ≤ Binv * ‖u t - v t‖ :=
    ((frameAt s₀ a rows k t).symm.toContinuousLinearMap.le_opNorm (u t - v t)).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  calc ‖u s - v s‖ ≤ A * ‖(frameAt s₀ a rows i s).symm (u s - v s)‖ := fwd
    _ ≤ A * (Real.exp E * (Binv * ‖u t - v t‖)) :=
      mul_le_mul_of_nonneg_left
        (chain.trans (mul_le_mul_of_nonneg_left back (Real.exp_pos _).le)) A0
    _ = A * Real.exp E * Binv * ‖u t - v t‖ := by ring

/-- **Uniqueness towards the initial time.** Two solutions on `[s, t]` in the outer tube that
agree at `t` agree at `s`. -/
theorem eq_of_eq (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows)
    {i k : ℕ} (hi : i < rows.length) (hk : k < rows.length) {s t : ℝ}
    (hs : s ∈ Icc (time a i) (time a (i + 1))) (ht : t ∈ Icc (time a k) (time a (k + 1)))
    (hst : s ≤ t) {u v : ℝ → Plane}
    (hu : ∀ τ ∈ Icc s t, HasDerivWithinAt u (F τ (u τ)) (Icc s t) τ)
    (hv : ∀ τ ∈ Icc s t, HasDerivWithinAt v (F τ (v τ)) (Icc s t) τ)
    (mu : ∀ τ ∈ Ioo s t, u τ ∈ outer s₀ a rows τ)
    (mv : ∀ τ ∈ Ioo s t, v τ ∈ outer s₀ a rows τ) (h : u t = v t) : u s = v s := by
  have chain := frame_dist_chain geo bounds lower le_rfl hi hk hs ht hst hu hv mu mv
  rw [h, sub_self, map_zero, norm_zero, mul_zero] at chain
  have zero := norm_le_zero_iff.mp chain
  rw [EmbeddingLike.map_eq_zero_iff] at zero
  exact sub_eq_zero.mp zero

/-! ### Relative openness of the inner tube -/

/-- **Relative openness.** The inner tube is a neighbourhood of each of its points within the
half-space of times not before the initial one. -/
theorem inner_relOpen (geo : Geo s₀ rows) (radii : Radii rows β σ) {p : ℝ × Plane}
    (hp : p ∈ innerTube s₀ a rows β) :
    innerTube s₀ a rows β ∈ 𝓝[{q : ℝ × Plane | a ≤ q.1}] p := by
  rw [innerTube_eq_region] at hp ⊢
  refine PiecewiseTube.region_mem_nhdsWithin (by norm_num)
    (fun k hk => continuousOn_gauge geo hk) (fun k hk x hx => ?_) hp
  calc gauge s₀ a rows k (time a (k + 1), x)
      ≤ gauge s₀ a rows (k + 1) (time a (k + 1), x) +
        (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := gauge_node_le geo hk x
    _ < β (k + 1 + 1) + (rowAt rows (k + 1)).jumpBound / (2 : ℝ) ^ 80 := by
      have hx' : gauge s₀ a rows (k + 1) (time a (k + 1), x) < β (k + 1 + 1) := hx
      linarith
    _ ≤ β (k + 1) := by
      have := radii.le hk
      have := radii.jump (k + 1) hk
      linarith

end Chain

/-! ### The inverse frame -/

private theorem adj_sq {A B C D K x y : ℝ}
    (h : ∀ x y : ℝ, (A * x + B * y) ^ 2 + (C * x + D * y) ^ 2 ≤ K * (x ^ 2 + y ^ 2)) :
    (D * x - B * y) ^ 2 + (A * y - C * x) ^ 2 ≤ K * (x ^ 2 + y ^ 2) := by
  have K0 : 0 ≤ K := by
    have := h 1 0
    nlinarith [sq_nonneg A, sq_nonneg C]
  obtain ⟨p, hp⟩ : ∃ p, p = D * x - B * y := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = A * y - C * x := ⟨_, rfl⟩
  rw [← hp, ← hq]
  obtain ⟨α, hα⟩ : ∃ α, α = A * q + B * (-p) := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = C * q + D * (-p) := ⟨_, rfl⟩
  have key := h q (-p)
  rw [← hα, ← hγ] at key
  have ident : p ^ 2 + q ^ 2 = y * α - x * γ := by
    have split : p ^ 2 + q ^ 2 = p * (D * x - B * y) + q * (A * y - C * x) := by
      rw [← hp, ← hq]
      ring
    rw [split, hα, hγ]
    ring
  have cauchy : (y * α - x * γ) ^ 2 ≤ (x ^ 2 + y ^ 2) * (α ^ 2 + γ ^ 2) := by
    nlinarith [sq_nonneg (x * α + y * γ)]
  have S0 : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  have N0 : 0 ≤ p ^ 2 + q ^ 2 := by positivity
  have prod : (p ^ 2 + q ^ 2) * (p ^ 2 + q ^ 2) ≤ K * (x ^ 2 + y ^ 2) * (p ^ 2 + q ^ 2) := by
    have h₂ := mul_le_mul_of_nonneg_left key S0
    have e : (-p) ^ 2 = p ^ 2 := by ring
    rw [e] at h₂
    nlinarith
  rcases N0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · exact le_of_mul_le_mul_right prod hpos

/-- **Inverse frame bound.** The inverse of the interpolated frame has operator norm at most
the recorded operator bound divided by the recorded lower bound for the determinant. -/
theorem frame_inv_op_norm {lim : Limits} {s : State} {r : Step} (h : geometry lim s r = true)
    {u : ℝ} (hu : |u| ≤ 1) :
    ‖(frameEquiv s.frame r.frame u).symm.toContinuousLinearMap‖ ≤ r.op / r.detLower := by
  obtain ⟨_, _, _, hlow, hdet, ho, _⟩ := geometry_sound h
  have dpos : (0 : ℝ) < r.detLower := by linarith
  have hd := hdet u hu
  rw [frameEquiv_backward (det_ne_zero h hu)]
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg ho dpos.le)
  intro v
  have adj : ‖matrix (entry s.frame.d r.frame.d u) (-entry s.frame.b r.frame.b u)
      (-entry s.frame.c r.frame.c u) (entry s.frame.a r.frame.a u) v‖ ≤ r.op * ‖v‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ho (norm_nonneg _))).mp ?_
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two, matrix_zero, matrix_one]
    have := adj_sq (x := v 0) (y := v 1) (fun x y => frame_norm_sq h hu x y)
    calc _ = (entry s.frame.d r.frame.d u * v 0 - entry s.frame.b r.frame.b u * v 1) ^ 2 +
          (entry s.frame.a r.frame.a u * v 1 - entry s.frame.c r.frame.c u * v 0) ^ 2 := by ring
      _ ≤ _ := this
  have inv : (affineDet s.frame r.frame u)⁻¹ ≤ (r.detLower : ℝ)⁻¹ := inv_anti₀ dpos hd
  have ipos : 0 ≤ (affineDet s.frame r.frame u)⁻¹ := inv_nonneg.mpr (dpos.le.trans hd)
  unfold backward
  rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ipos]
  calc (affineDet s.frame r.frame u)⁻¹ * _ ≤ (r.detLower : ℝ)⁻¹ * ((r.op : ℝ) * ‖v‖) :=
        mul_le_mul inv adj (norm_nonneg _) (inv_nonneg.mpr dpos.le)
    _ = r.op / r.detLower * ‖v‖ := by ring

/-- The inverse frame of slab `k` is bounded at every time of the slab. -/
theorem frameAt_inv_op_norm {s₀ : State} {a : ℝ} {rows : List Step} (geo : Geo s₀ rows) {k : ℕ}
    (hk : k < rows.length) {t : ℝ} (ht : t ∈ Icc (time a k) (time a (k + 1))) :
    ‖(frameAt s₀ a rows k t).symm.toContinuousLinearMap‖ ≤
      (rowAt rows k).op / (rowAt rows k).detLower := by
  rw [time_succ] at ht
  exact frame_inv_op_norm (geo.at hk) (abs_coord_le ht)

/-- The frame of slab `k` is bounded at every time of the slab. -/
theorem frameAt_op_norm {s₀ : State} {a : ℝ} {rows : List Step} (geo : Geo s₀ rows) {k : ℕ}
    (hk : k < rows.length) {t : ℝ} (ht : t ∈ Icc (time a k) (time a (k + 1))) :
    ‖(frameAt s₀ a rows k t).toContinuousLinearMap‖ ≤ (rowAt rows k).op := by
  rw [time_succ] at ht
  exact frame_op_norm (geo.at hk) (abs_coord_le ht)

/-! ### Sanity: the stationary record -/

/-- The stationary record passes the geometric check with the common limits. -/
theorem stationary_geo : Geo (next stationary) [stationary] :=
  ⟨by with_unfolding_all rfl, trivial⟩

/-- The stationary record with the zero field satisfies the field bounds. -/
theorem stationary_bounds (a : ℝ) :
    FieldBoundsOn (fun _ _ => 0) (fun _ _ => 0) (next stationary) a [stationary] := by
  have velocity (t : ℝ) : referenceVelocity a stationary t = 0 := by
    ext i
    fin_cases i <;> norm_num [referenceVelocity, polynomial, stationary,
      TrajectoryTaylorModel.ofDyadic, QPoly.scale, QPoly.deriv, QPoly.add, QPoly.eval,
      List.replicate_succ]
  have frame : frameVelocity (next stationary).frame stationary.frame = 0 := by
    simp [frameVelocity, next, forward, entry]
  refine ⟨⟨continuousOn_const, continuousOn_const, fun _ _ _ _ => hasFDerivAt_const _ _, ?_, ?_⟩,
    trivial⟩
  · intro t _ v _ w
    rw [frame]
    simp [Fields.LogNormTrajectory.MovingFrame.jacobian, stationary]
  · intro t _
    rw [velocity]
    simp [stationary]

/-- Constant radii `2⁻⁸¹` are backward radii for the stationary record. -/
theorem stationary_radii :
    Radii [stationary] (fun _ => 1 / (2 : ℝ) ^ 81) (fun _ => 1 / (2 : ℝ) ^ 81) := by
  have row : ∀ k < [stationary].length, rowAt [stationary] k = stationary := by
    intro k hk
    obtain rfl : k = 0 := Nat.lt_one_iff.mp hk
    rfl
  constructor
  all_goals
    intro k hk
    try rw [row k hk]
    norm_num [stationary]

/-- Non-vacuity: for the stationary record with the zero field the hypotheses of `reach`
hold together, and every reference point of the slab is reached. -/
theorem stationary_reach (a : ℝ) {t : ℝ} (ht : t ∈ Ico a (a + 1 / 64)) :
    ∃ v : ℝ → Plane, v t = reference a stationary t ∧
      FlowLabel.SolOn (fun _ _ => 0) (outer (next stationary) a [stationary]) a t v ∧
      ‖(frameEquiv (next stationary).frame (next stationary).frame 0).symm
        (v a - point (next stationary).point)‖ ≤ 1 / (2 : ℝ) ^ 81 := by
  refine reach (σ := fun _ => 1 / (2 : ℝ) ^ 81) stationary_geo (stationary_bounds a)
    (⟨lower_stationary a, trivial⟩ : LowerOn _ _ a [stationary]) stationary_radii ?_
  refine ⟨0, Nat.zero_lt_one, ?_, ?_⟩
  · rw [time_succ, time_zero]
    exact ht
  · change ‖(frameAt (next stationary) a [stationary] 0 t).symm
      (reference a stationary t - reference (time a 0) (rowAt [stationary] 0) t)‖ < _
    rw [time_zero]
    change ‖(frameAt (next stationary) a [stationary] 0 t).symm
      (reference a stationary t - reference a stationary t)‖ < _
    rw [sub_self, map_zero, norm_zero]
    positivity

end PlasmaLean.Certificates.PositionFrameTube
