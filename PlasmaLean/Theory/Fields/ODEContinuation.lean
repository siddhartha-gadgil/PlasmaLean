/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FieldLineExistence

/-!
# Global existence from a priori bounds on every finite time interval

`ODEGlobal.exists_global` (in `Theory/Fields/FieldLineExistence`) needs a *single* compact set that
traps every local solution. Many systems only have bounds that grow with time: a charged particle
in a magnetic field keeps its speed, so after time `T` its position lies within distance `|v₀| T`
of the start, but no fixed compact set contains it for all time. This file proves the
corresponding continuation theorem.

**Hypothesis** (`APrioriBounded f U x₀`): for every horizon `T` there is a compact `K ⊆ U` such
that every solution of `α' = f(α)` on a symmetric interval `[-c, c]` with `0 ≤ c ≤ T` and
`α 0 = x₀` stays in `K` on `[-c, c]`.

**Theorem** (`exists_global_of_apriori`): if `f` is `C¹` on the open set `U ∋ x₀` and the
hypothesis holds, there is a global solution `γ : ℝ → E`, `γ 0 = x₀`, `γ' = f(γ)` at every time.

Proof: on the horizon `T` use the uniform Picard–Lindelöf time `ε` of `K_T`
(`uniform_local_existence`) and extend a solution on `[-S, S]` by steps `ε/2` at both ends
(`extend_right`, `extend_left`) until it covers `[-T, T]` (`extend_to_horizon`); then glue the
compatible solutions on `[-n, n]`, `n ∈ ℕ`, as in `exists_global`.

`apriori_of_locallyInvariant` recovers the fixed-compact-set case. Sanity:
`exists_global_of_apriori_zero` (the zero field).
-/

public section
noncomputable section

namespace PlasmaLean.Fields.ODEGlobal

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **A priori bounds on every finite horizon.** For every `T` there is a compact `K ⊆ U` that
contains every solution of `α' = f(α)` on `[-c, c]` (`0 ≤ c ≤ T`) starting at `x₀`. -/
@[expose] def APrioriBounded (f : E → E) (U : Set E) (x₀ : E) : Prop :=
  ∀ T : ℝ, ∃ K : Set E, IsCompact K ∧ K ⊆ U ∧ ∀ c ∈ Icc 0 T, ∀ α : ℝ → E, α 0 = x₀ →
    (∀ t ∈ Icc (-c) c, HasDerivAt α (f (α t)) t) → ∀ t ∈ Icc (-c) c, α t ∈ K

omit [ProperSpace E] in
/-- A set that is invariant for local solutions and contained in a compact `K ⊆ U` gives a priori
bounds (with the same `K` for every horizon) from each of its points. -/
theorem apriori_of_locallyInvariant {f : E → E} {U K Ω : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U) (hΩK : Ω ⊆ K) (hinv : LocallyInvariant f Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    APrioriBounded f U x₀ := fun _ =>
  ⟨K, hK, hKU, fun c hc α h0 hα t ht =>
    hΩK (hinv (-c) c α (by linarith [hc.1]) hc.1 (h0 ▸ hx₀) hα t ht)⟩

/-- **Extension to a horizon.** Under a priori bounds by `K ⊆ U` on `[-T, T]`, a solution on
`[-S, S]` (`0 ≤ S ≤ T`) starting at `x₀` extends to a solution on `[-T, T]` that agrees with it on
`[-S, S]`. -/
theorem extend_to_horizon {f : E → E} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) {x₀ : E} {T : ℝ}
    (hbd : ∀ c ∈ Icc 0 T, ∀ α : ℝ → E, α 0 = x₀ →
      (∀ t ∈ Icc (-c) c, HasDerivAt α (f (α t)) t) → ∀ t ∈ Icc (-c) c, α t ∈ K)
    {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) {α : ℝ → E} (hα0 : α 0 = x₀)
    (hα : ∀ t ∈ Icc (-S) S, HasDerivAt α (f (α t)) t) :
    ∃ β : ℝ → E, β 0 = x₀ ∧ (∀ t ∈ Icc (-T) T, HasDerivAt β (f (β t)) t) ∧
      ∀ t ∈ Icc (-S) S, β t = α t := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence hU hf hK hKU
  set h := ε / 2 with hh
  have hh0 : 0 < h := by positivity
  have key : ∀ k : ℕ, S + k * h ≤ T + h → ∃ β : ℝ → E, β 0 = x₀ ∧
      (∀ t ∈ Icc (-(S + k * h)) (S + k * h), HasDerivAt β (f (β t)) t) ∧
      ∀ t ∈ Icc (-S) S, β t = α t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨α, hα0, by simpa using hα, fun _ _ => rfl⟩
    | succ k ih =>
      intro hk
      push_cast at hk
      obtain ⟨β, hβ0, hβ, hβα⟩ := ih (by linarith)
      set c := S + k * h with hc
      have hc0 : 0 ≤ c := by positivity
      have hcT : c ≤ T := by linarith
      have hmemK := hbd c ⟨hc0, hcT⟩ β hβ0 hβ
      obtain ⟨β₁, hβ₁0, hβ₁⟩ := hloc _ (hmemK c ⟨by linarith, le_rfl⟩) c
      obtain ⟨β₂, hβ₂0, hβ₂⟩ := hloc _ (hmemK (-c) ⟨le_rfl, by linarith⟩) (-c)
      obtain ⟨γ₁, hγ₁, hγ₁e⟩ := extend_right hε hβ hβ₁0 hβ₁
      have hβ₂0' : β₂ (-c) = γ₁ (-c) := by rw [hγ₁e _ (by linarith), hβ₂0]
      obtain ⟨γ, hγ, hγe⟩ := extend_left hε hγ₁ hβ₂0' hβ₂
      refine ⟨γ, ?_, fun t ht => hγ t ?_, fun t ht => ?_⟩
      · rw [hγe 0 (by linarith), hγ₁e 0 hc0, hβ0]
      · push_cast at ht
        constructor <;> linarith [ht.1, ht.2]
      · have hcS : S ≤ c := by
          have : (0 : ℝ) ≤ k * h := by positivity
          linarith
        rw [hγe t (by linarith [ht.1]), hγ₁e t (by linarith [ht.2]), hβα t ht]
  set k := ⌈(T - S) / h⌉₊ with hk
  have h1 : (T - S) / h ≤ k := Nat.le_ceil _
  have h2 : (k : ℝ) < (T - S) / h + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hh0.le)
  have h1' : T - S ≤ k * h := by rwa [div_le_iff₀ hh0] at h1
  have h2' : k * h < T - S + h := by
    have := (lt_div_iff₀ hh0).mp (by linarith : (k : ℝ) - 1 < (T - S) / h)
    nlinarith
  obtain ⟨β, hβ0, hβ, hβα⟩ := key k (by linarith)
  exact ⟨β, hβ0, fun t ht => hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩, hβα⟩

/-- **Global existence from a priori bounds.** If `f` is `C¹` on the open set `U ∋ x₀` and the
solutions from `x₀` are a priori bounded on every finite horizon by compact subsets of `U`, then
there is a global solution `γ : ℝ → E` of `γ' = f(γ)` with `γ 0 = x₀`. -/
theorem exists_global_of_apriori {f : E → E} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {x₀ : E} (hx₀ : x₀ ∈ U) (hbd : APrioriBounded f U x₀) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  -- a local solution through `x₀`
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence hU hf isCompact_singleton
    (singleton_subset_iff.mpr hx₀)
  obtain ⟨β₀, hβ₀0, hβ₀⟩ := hloc x₀ rfl 0
  let P : ℕ → (ℝ → E) → Prop := fun n α =>
    α 0 = x₀ ∧ ∀ t ∈ Icc (-(n : ℝ)) n, HasDerivAt α (f (α t)) t
  have base : ∃ α, P 0 α := by
    refine ⟨β₀, hβ₀0, fun t ht => hβ₀ t ?_⟩
    simp only [CharP.cast_eq_zero, neg_zero, Icc_self, mem_singleton_iff] at ht
    subst ht; constructor <;> linarith
  have step : ∀ n (α : {α // P n α}), ∃ β : {β // P (n + 1) β},
      ∀ t ∈ Icc (-(n : ℝ)) n, β.1 t = α.1 t := by
    rintro n ⟨α, hα0, hα⟩
    obtain ⟨K, hK, hKU, hKb⟩ := hbd ((n : ℝ) + 1)
    obtain ⟨β, hβ0, hβ, hβα⟩ := extend_to_horizon hU hf hK hKU hKb (Nat.cast_nonneg n)
      (by linarith) hα0 hα
    exact ⟨⟨β, hβ0, fun t ht => hβ t (by push_cast at ht; exact ht)⟩, hβα⟩
  choose next hnext using step
  let seq : ∀ n : ℕ, {α // P n α} := fun n =>
    Nat.rec (motive := fun n => {α // P n α}) ⟨base.choose, base.choose_spec⟩
      (fun n α => next n α) n
  have hseq : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  have hagree : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Icc (-(n : ℝ)) n, (seq m).1 t = (seq n).1 t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _; rfl
    | succ m hnm ih =>
      intro t ht
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      rw [hseq, hnext m (seq m) t ⟨by linarith [ht.1], by linarith [ht.2]⟩, ih t ht]
  let N : ℝ → ℕ := fun t => ⌈|t|⌉₊ + 1
  have hN : ∀ t, |t| < N t := by
    intro t
    have := Nat.le_ceil |t|
    simp only [N]; push_cast; linarith
  let γ : ℝ → E := fun t => (seq (N t)).1 t
  have hγeq : ∀ n : ℕ, ∀ s ∈ Icc (-(n : ℝ)) n, γ s = (seq n).1 s := by
    intro n s hs
    rcases le_total (N s) n with hle | hle
    · have hs' := abs_lt.mp (hN s)
      exact (hagree (N s) n hle s ⟨by linarith, by linarith⟩).symm
    · exact hagree n (N s) hle s hs
  refine ⟨γ, (seq (N 0)).2.1, fun t => ?_⟩
  have ht := abs_lt.mp (hN t)
  have hmem : t ∈ Icc (-(N t : ℝ)) (N t) := ⟨ht.1.le, ht.2.le⟩
  rw [hγeq (N t) t hmem]
  refine ((seq (N t)).2.2 t hmem).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hγeq (N t) s ⟨hs.1.le, hs.2.le⟩

/-- Sanity check (degenerate case): for the zero field the a priori hypothesis holds with
`K = {x₀}`, and the continuation theorem returns a global solution. -/
theorem exists_global_of_apriori_zero (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ ((fun _ => (0 : E)) (γ t)) t := by
  refine exists_global_of_apriori isOpen_univ contDiffOn_const (mem_univ x₀) fun _ =>
    ⟨{x₀}, isCompact_singleton, subset_univ _, fun c hc α h0 hα t ht => ?_⟩
  have hcont : ContinuousOn α (Icc (-c) c) := fun u hu =>
    (hα u hu).continuousAt.continuousWithinAt
  have hcst := constant_of_has_deriv_right_zero hcont
    (fun u hu => (hα u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
  have h0' : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith [hc.1], hc.1⟩
  exact (hcst t ht).trans ((hcst 0 h0').symm.trans h0)

end PlasmaLean.Fields.ODEGlobal
