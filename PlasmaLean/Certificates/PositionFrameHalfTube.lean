/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameTube
public import PlasmaLean.Theory.Fields.FlowLabelSymmetric

/-!
# The half tube of a chain of position-frame slabs

The chain facts of `PositionFrameTube` (backward reachability, distances towards the initial
time, uniqueness, relative openness) are assembled into a `FlowLabel.HalfTube` over the times
`[a, time a rows.length)`, for a field with a time-reversal symmetry about the initial time.

* `exists_slab`, `exists_slab_closed`: every time of the chain lies in a slab.
* `constCheck`, `const_of_check`: a computable check of the constants `E` (sum of the growth
  exponents) and `B` (bound for the inverse frames), with soundness.
* `halfTube`: the outer and inner tubes of the chain form a half tube with contraction factor
  `A * exp E * Binv`.
* `isOpen_region`: the region over the doubled inner tube is open.
* `frameAt_start_identity`: with the identity initial frame, `A = 1`.
* `stationary_halfTube`: the hypotheses hold together for the stationary record.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Certificates.PositionFrameTube

open Set PositionFrameSlabs PositionFrameBackward Filter Topology
open PlasmaLean.Fields

/-! ### Slabs containing a given time -/

/-- The initial time is before the end of a nonempty chain. -/
theorem lt_time (a : ℝ) {n : ℕ} (hn : 0 < n) : a < time a n := by
  have h := time_le (a := a) (Nat.succ_le_of_lt hn)
  rw [time_succ, time_zero] at h
  linarith

/-- Every time of the chain lies in a half-open slab. -/
theorem exists_slab {a t : ℝ} {n : ℕ} (ht : t ∈ Ico a (time a n)) :
    ∃ k < n, t ∈ Ico (time a k) (time a (k + 1)) := by
  induction n with
  | zero =>
    rw [time_zero] at ht
    exact absurd ht.2 (not_lt.mpr ht.1)
  | succ n ih =>
    rcases lt_or_ge t (time a n) with h | h
    · obtain ⟨k, hk, hmem⟩ := ih ⟨ht.1, h⟩
      exact ⟨k, Nat.lt_succ_of_lt hk, hmem⟩
    · exact ⟨n, Nat.lt_succ_self n, h, ht.2⟩

/-- Every time of a nonempty chain, the final time included, lies in a closed slab. -/
theorem exists_slab_closed {a t : ℝ} {n : ℕ} (hn : 0 < n) (ht : t ∈ Icc a (time a n)) :
    ∃ k < n, t ∈ Icc (time a k) (time a (k + 1)) := by
  rcases ht.2.lt_or_eq with h | h
  · obtain ⟨k, hk, hmem⟩ := exists_slab ⟨ht.1, h⟩
    exact ⟨k, hk, hmem.1, hmem.2.le⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact ⟨m, Nat.lt_succ_self m, h ▸ time_le (Nat.le_succ m), h.le⟩

/-! ### The constants -/

/-- Check of the constants of a chain: `E` bounds the sum of the growth exponents of the slabs,
and `B` bounds the recorded operator bound divided by the recorded lower determinant bound of
every record. -/
def constCheck (rows : List Step) (E B : ℚ) : Bool :=
  leQ ((rows.map fun r => max 0 r.mu / 64).sum) E &&
    rows.all fun r => ltQ 0 r.detLower && leQ r.op (B * r.detLower)

/-- The sum of the growth exponents over the slab indices is the sum over the list. -/
theorem sum_exponents (rows : List Step) :
    ∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 =
      (((rows.map fun r => max 0 r.mu / 64).sum : ℚ) : ℝ) := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [rowAt_cons_succ]
    rw [ih, List.map_cons, List.sum_cons]
    change _ + max 0 ((r.mu : ℚ) : ℝ) / 64 = _
    push_cast
    ring

/-- **Soundness of the check of the constants.** -/
theorem const_of_check {rows : List Step} {E B : ℚ} (h : constCheck rows E B = true) :
    (∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 ≤ E) ∧
    ∀ k < rows.length, ((rowAt rows k).op : ℝ) / (rowAt rows k).detLower ≤ B := by
  simp only [constCheck, Bool.and_eq_true, leQ_true, ltQ_true, List.all_eq_true] at h
  obtain ⟨sum, all⟩ := h
  refine ⟨?_, fun k hk => ?_⟩
  · rw [sum_exponents]
    exact_mod_cast sum
  · have mem : rowAt rows k ∈ rows := by
      have e : rowAt rows k = rows[k] := by
        simp [rowAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
      rw [e]
      exact List.getElem_mem hk
    obtain ⟨pos, le⟩ := all _ mem
    have pos' : (0 : ℝ) < (rowAt rows k).detLower := by exact_mod_cast pos
    rw [div_le_iff₀ pos']
    exact_mod_cast le

/-! ### The half tube -/

section Chain

variable {domain : RegularityDomain} {F : ℝ → Plane → Plane} {J : ℝ → Plane → Plane →L[ℝ] Plane}
  {s₀ : State} {a : ℝ} {rows : List Step} {β τ : ℕ → ℝ}

/-- **The half tube of a chain.** For a field with the time-reversal symmetry
`F (2 a - t) (refl x) = -refl (F t x)` and the speed bound `M` on the outer tube, the outer and
inner tubes of a nonempty chain form a half tube after the initial time `a`. The contraction
factor is `A * exp E * Binv`, where `A` bounds the initial frame, `E` the sum of the growth
exponents and `Binv` the inverse frames of all slabs. -/
theorem halfTube (geo : Geo s₀ rows) (bounds : FieldBoundsOn F J s₀ a rows domain)
    (lower : LowerOn J s₀ a rows) (radii : Radii rows β τ) (hn : 0 < rows.length)
    {A E Binv M : ℝ}
    (hE : ∑ j ∈ Finset.range rows.length, max 0 ((rowAt rows j).mu : ℝ) / 64 ≤ E)
    (hA : ‖(frameAt s₀ a rows 0 a).toContinuousLinearMap‖ ≤ A)
    (hB : ∀ k < rows.length, ((rowAt rows k).op : ℝ) / (rowAt rows k).detLower ≤ Binv)
    (hC : 1 ≤ A * Real.exp E * Binv) (hM : 0 ≤ M)
    (refl : Plane ≃ₗᵢ[ℝ] Plane) (inv : ∀ x, refl (refl x) = x)
    (speed : ∀ t x, x ∈ outer s₀ a rows t → ‖F t x‖ ≤ M)
    (symm : ∀ t x, x ∈ outer s₀ a rows t → F (2 * a - t) (refl x) = -refl (F t x)) :
    FlowLabel.HalfTube F refl a (time a rows.length) (outer s₀ a rows) (inner s₀ a rows β)
      (A * Real.exp E * Binv) M where
  lt := lt_time a hn
  one_le := hC
  speed_nonneg := hM
  involutive := inv
  reach := by
    intro t _ x hx
    obtain ⟨v, stop, sol, _⟩ := reach geo bounds lower radii hx
    exact ⟨v, stop, sol⟩
  contract := by
    intro t ht u v su sv
    obtain ⟨k, hk, hmem⟩ := exists_slab ht
    have hmem' : t ∈ Icc (time a k) (time a (k + 1)) := ⟨hmem.1, hmem.2.le⟩
    have start : a ∈ Icc (time a 0) (time a (0 + 1)) := by
      rw [time_succ, time_zero]
      exact ⟨le_rfl, by linarith⟩
    exact dist_chain geo bounds lower hE hn hk start hmem' ht.1 su.1 sv.1 su.2 sv.2 hA
      ((frameAt_inv_op_norm geo hk hmem').trans (hB k hk))
  unique := by
    intro t ht s hs u v su sv huv
    obtain ⟨k, hk, hmem⟩ := exists_slab ht
    obtain ⟨i, hi, smem⟩ := exists_slab (a := a) (n := rows.length) ⟨hs.1, hs.2.trans_lt ht.2⟩
    exact eq_of_eq geo bounds lower hi hk ⟨smem.1, smem.2.le⟩ ⟨hmem.1, hmem.2.le⟩ hs.2
      su.1 sv.1 su.2 sv.2 huv
  speed := fun t _ x hx => speed t x hx
  symm := fun t _ x hx => symm t x hx

/-- **Openness of the doubled inner region.** The region over the inner tube of a nonempty
chain, doubled by a reflection about the initial time, is open. -/
theorem isOpen_region (geo : Geo s₀ rows) (radii : Radii rows β τ)
    (refl : Plane ≃ₗᵢ[ℝ] Plane) (inv : ∀ x, refl (refl x) = x) (hn : 0 < rows.length) :
    IsOpen (FlowLabel.region (2 * a - time a rows.length) (time a rows.length)
      (FlowLabel.doubleV refl a (inner s₀ a rows β))) :=
  FlowLabel.isOpen_region_double refl inv (lt_time a hn)
    (fun _ hp => inner_relOpen (s₀ := s₀) (a := a) (rows := rows) (β := β) geo radii hp)

/-- With the identity initial frame, the frame of the first slab at the initial time has
operator norm at most one. -/
theorem frameAt_start_identity (geo : Geo s₀ rows) (hn : 0 < rows.length)
    (h : s₀.frame = ⟨2 ^ 40, 0, 0, 2 ^ 40⟩) :
    ‖(frameAt s₀ a rows 0 a).toContinuousLinearMap‖ ≤ 1 := by
  have start := frameAt_start (a := a) geo hn
  rw [time_zero] at start
  change frameAt s₀ a rows 0 a = frameEquiv s₀.frame s₀.frame 0 at start
  rw [start, h, frameEquiv_forward (by norm_num [affineDet, entry])]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have id : forward ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ ⟨2 ^ 40, 0, 0, 2 ^ 40⟩ 0 v = v := by
    ext i
    fin_cases i <;> norm_num [forward, entry]
  rw [id, one_mul]

end Chain

/-! ### Sanity: the stationary record -/

/-- The check of the constants accepts the stationary record with `E = 0` and `B = 1`. -/
theorem stationary_constCheck : constCheck [stationary] 0 1 = true := by
  with_unfolding_all rfl

/-- The check of the constants rejects a bound for the inverse frame that is too small. -/
theorem stationary_constCheck_reject : constCheck [stationary] 0 (1 / 2) = false := by
  with_unfolding_all rfl

/-- Non-vacuity: for the stationary record with the zero field and the identity reflection the
hypotheses of `halfTube` hold together. -/
theorem stationary_halfTube (a : ℝ) :
    FlowLabel.HalfTube (fun _ _ => (0 : Plane)) (LinearIsometryEquiv.refl ℝ Plane) a
      (time a 1) (outer (next stationary) a [stationary])
      (inner (next stationary) a [stationary] fun _ => 1 / (2 : ℝ) ^ 81)
      (1 * Real.exp 0 * 1) 0 := by
  obtain ⟨hE, hB⟩ := const_of_check stationary_constCheck
  refine halfTube (J := fun _ _ => 0) stationary_geo (stationary_bounds a)
    (⟨lower_stationary a, trivial⟩ : LowerOn _ _ a [stationary]) stationary_radii
    Nat.zero_lt_one (by simpa using hE)
    (frameAt_start_identity stationary_geo Nat.zero_lt_one rfl)
    (fun k hk => by simpa using hB k hk) (by simp) le_rfl
    (LinearIsometryEquiv.refl ℝ Plane) (fun _ => rfl) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp)

/-- Non-vacuity: the doubled inner region of the stationary record is open. -/
theorem stationary_isOpen_region (a : ℝ) :
    IsOpen (FlowLabel.region (2 * a - time a 1) (time a 1)
      (FlowLabel.doubleV (LinearIsometryEquiv.refl ℝ Plane) a
        (inner (next stationary) a [stationary] fun _ => 1 / (2 : ℝ) ^ 81))) :=
  isOpen_region stationary_geo stationary_radii _ (fun _ => rfl) Nat.zero_lt_one

end PlasmaLean.Certificates.PositionFrameTube
