/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Order.IntermediateValue

/-!
# A curve that solves an ODE wherever it stays in the regular region is the trapped solution

Let `V` be `C¹` on an open set `U` and `Y` a global solution of `γ' = V(γ)` with values in a
compact `K ⊆ U`. Let `X` be a continuous curve with `X 0 = Y 0` which solves the ODE on every
interval `[0, b]` (resp. `[a, 0]`) on which it stays in `U` — the typical situation of a physical
model whose equations reduce to `γ' = V(γ)` only where some regularity (`B ≠ 0`, a passing
condition, ...) holds along the whole time interval since `t = 0`. Then `X = Y` for all time
(`curve_eq_of_local`): a continuity ("real induction") argument with Grönwall uniqueness
(`ODE_solution_unique_of_mem_Icc_right`).

**Sanity.** `curve_eq_of_local_const`: the constant curve of the zero field.
-/

@[expose] public section

open Set Filter Topology

namespace PlasmaLean.Fields.Bootstrap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- The times `b` such that `X` stays in the closed set `K` on `[0, b]` form a closed set. -/
theorem isClosed_stay {X : ℝ → E} (hX : Continuous X) {K : Set E} (hK : IsClosed K)
    (h0 : X 0 ∈ K) : IsClosed {b : ℝ | ∀ u ∈ Icc 0 b, X u ∈ K} := by
  rw [← isOpen_compl_iff]
  have hO : IsOpen {u : ℝ | X u ∉ K} := hK.isOpen_compl.preimage hX
  have e : {b : ℝ | ∀ u ∈ Icc 0 b, X u ∈ K}ᶜ = ⋃ u ∈ {u : ℝ | 0 ≤ u ∧ X u ∉ K}, Ioi u := by
    ext b
    simp only [mem_compl_iff, Set.mem_ofPred_eq, not_forall, mem_Icc, exists_prop, mem_iUnion,
      mem_Ioi]
    constructor
    · rintro ⟨u, ⟨hu0, hub⟩, hu⟩
      have hu0' : 0 < u := lt_of_le_of_ne hu0 (fun h => hu (h ▸ h0))
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO u hu
      refine ⟨max 0 (u - ε / 2), ⟨le_max_left _ _, ?_⟩, ?_⟩
      · rcases le_total 0 (u - ε / 2) with h | h
        · rw [max_eq_right h]
          exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
        · rw [max_eq_left h]; exact fun h' => hu (by
            have : X 0 ∉ K := hball (by
              rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
            exact absurd h0 this)
      · exact lt_of_lt_of_le (max_lt (by linarith) (by linarith)) hub
    · rintro ⟨u, ⟨hu0, hu⟩, hub⟩
      exact ⟨u, ⟨hu0, hub.le⟩, hu⟩
  rw [e]
  exact isOpen_biUnion fun _ _ => isOpen_Ioi

/-- **Forward half**: `X = Y` on `[0, ∞)`. -/
theorem curve_eq_of_local_fwd {V : E → E} {U K : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    (hK : IsCompact K) (hKU : K ⊆ U) {X Y : ℝ → E} (hX : Continuous X)
    (hY : ∀ t, HasDerivAt Y (V (Y t)) t) (hYK : ∀ t, Y t ∈ K) (h0 : X 0 = Y 0)
    (hloc : ∀ b, 0 ≤ b → (∀ s ∈ Icc 0 b, X s ∈ U) → ∀ s ∈ Icc 0 b, HasDerivAt X (V (X s)) s) :
    ∀ t, 0 ≤ t → X t = Y t := by
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun t => (hY t).continuousAt
  -- uniqueness on an interval where `X` stays in `U`
  have huniq : ∀ b, 0 ≤ b → (∀ s ∈ Icc 0 b, X s ∈ U) → EqOn X Y (Icc 0 b) := by
    intro b hb hXU
    have hK' : IsCompact (K ∪ X '' Icc 0 b) := hK.union (isCompact_Icc.image hX)
    have hK'U : K ∪ X '' Icc 0 b ⊆ U := union_subset hKU (by
      rintro _ ⟨s, hs, rfl⟩; exact hXU s hs)
    obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK' (fun x hx => by
      obtain ⟨Kx, t, ht, hl⟩ := (hV.contDiffAt (hU.mem_nhds (hK'U hx))).exists_lipschitzOnWith
      exact ⟨Kx, t, mem_nhdsWithin_of_mem_nhds ht, hl⟩)
    have hd := hloc b hb hXU
    exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => V) (s := fun _ => K ∪ X '' Icc 0 b)
      (fun _ _ => hL) hX.continuousOn
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) hYc.continuousOn
      (fun t _ => (hY t).hasDerivWithinAt) (fun t _ => Or.inl (hYK t)) h0
  -- `X` stays in `K` on every `[0, T]`
  set S := {b : ℝ | ∀ u ∈ Icc 0 b, X u ∈ K}
  have hX0K : X 0 ∈ K := h0 ▸ hYK 0
  have hS : IsClosed S := isClosed_stay hX hK.isClosed hX0K
  have hstay : ∀ T, 0 ≤ T → T ∈ S := by
    intro T hT
    refine (hS.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin
      (by intro u hu; rw [le_antisymm hu.2 hu.1]; exact hX0K) (fun x hx => ?_) ⟨hT, le_rfl⟩
    obtain ⟨hxS, hx0, -⟩ := hx
    have hxU : X x ∈ U := hKU (hxS x ⟨hx0, le_rfl⟩)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hX) x hxU
    refine mem_of_superset (Ioo_mem_nhdsGT (show x < x + δ by linarith)) fun b hb => ?_
    have hXU : ∀ s ∈ Icc 0 b, X s ∈ U := by
      intro s hs
      rcases le_or_gt s x with h | h
      · exact hKU (hxS s ⟨hs.1, h⟩)
      · exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;>
          linarith [hs.2, hb.2])
    have heq := huniq b (by linarith [hb.1]) hXU
    intro u hu
    rw [heq hu]; exact hYK u
  intro t ht
  exact huniq t ht (fun s hs => hKU (hstay t ht s hs)) ⟨ht, le_rfl⟩

/-- **A curve that solves `γ' = V(γ)` wherever it has stayed in `U` since `t = 0` is the trapped
solution `Y`.** -/
theorem curve_eq_of_local {V : E → E} {U K : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U)
    (hK : IsCompact K) (hKU : K ⊆ U) {X Y : ℝ → E} (hX : Continuous X)
    (hY : ∀ t, HasDerivAt Y (V (Y t)) t) (hYK : ∀ t, Y t ∈ K) (h0 : X 0 = Y 0)
    (hfwd : ∀ b, 0 ≤ b → (∀ s ∈ Icc 0 b, X s ∈ U) → ∀ s ∈ Icc 0 b, HasDerivAt X (V (X s)) s)
    (hbwd : ∀ a, a ≤ 0 → (∀ s ∈ Icc a 0, X s ∈ U) → ∀ s ∈ Icc a 0, HasDerivAt X (V (X s)) s) :
    X = Y := by
  funext t
  rcases le_total 0 t with ht | ht
  · exact curve_eq_of_local_fwd hU hV hK hKU hX hY hYK h0 hfwd t ht
  · -- time reversal
    have hV' : ContDiffOn ℝ 1 (fun x => -V x) U := hV.neg
    have hY' : ∀ s, HasDerivAt (fun s => Y (-s)) (-V (Y (-s))) s := fun s => by
      have := (hY (-s)).scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have hloc' : ∀ b, 0 ≤ b → (∀ s ∈ Icc 0 b, X (-s) ∈ U) →
        ∀ s ∈ Icc 0 b, HasDerivAt (fun s => X (-s)) (-V (X (-s))) s := by
      intro b hb hU' s hs
      have hd := hbwd (-b) (by linarith) (fun r hr => by
        have := hU' (-r) ⟨by linarith [hr.2], by linarith [hr.1]⟩; simpa using this)
        (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have := hd.scomp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have h := curve_eq_of_local_fwd (V := fun x => -V x) hU hV' hK hKU
      (X := fun s => X (-s)) (Y := fun s => Y (-s)) (hX.comp continuous_neg) hY'
      (fun s => hYK (-s)) (by simpa using h0) hloc' (-t) (by linarith)
    simpa using h

/-- **Sanity** (degenerate case): for the zero field on `U = univ`, a curve with zero derivative
starting at `x₀` is the constant solution. -/
theorem curve_eq_of_local_const {X : ℝ → E} (x₀ : E) (hX : ∀ t, HasDerivAt X 0 t) (h0 : X 0 = x₀) :
    X = fun _ => x₀ :=
  curve_eq_of_local (V := fun _ => 0) (U := univ) (K := {x₀}) isOpen_univ contDiffOn_const
    isCompact_singleton (subset_univ _)
    (continuous_iff_continuousAt.2 fun t => (hX t).continuousAt)
    (fun t => hasDerivAt_const t x₀) (fun _ => rfl) h0 (fun _ _ _ s _ => hX s)
    (fun _ _ _ s _ => hX s)

end PlasmaLean.Fields.Bootstrap
