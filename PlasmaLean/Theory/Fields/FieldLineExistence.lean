/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.TorusTrapping
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Global existence and uniqueness of field lines trapped in a compact set

The all-time confinement theorems of `Theory/Fields/InvariantBarrier` and
`Theory/Fields/TorusTrapping` are statements about *given* two-sided field lines. This file
supplies the existence half, so that such statements are not vacuous.

**Generic ODE result** (`ODEGlobal.existsUnique_global`). Let `E` be a proper real normed space,
`f : E → E` a vector field that is `C¹` on an open set `U`, `K ⊆ U` compact and `Ω ⊆ K`. Suppose
`Ω` is *a priori invariant for local solutions*: every solution of `α' = f(α)` on a closed
interval `[a, b] ∋ 0` with `α 0 ∈ Ω` stays in `Ω` on `[a, b]`. Then for every `x₀ ∈ Ω` there is
exactly one global solution `γ : ℝ → E`, `γ 0 = x₀`, and it stays in `Ω` for all time.

The proof: compactness gives a uniform Picard–Lindelöf time `ε` for initial points in `K`
(`uniform_local_existence`); a solution on `[-T, T]` is extended to `[-T - ε/2, T + ε/2]` by gluing
local solutions at the endpoints (`extend_right`, `extend_left`; the extension agrees with the old
solution on `[-T, T]`); the resulting compatible sequence defines the global solution.
Uniqueness is Grönwall (`ODE_solution_unique_univ`) with the Lipschitz constant of `f` on `K`.

**Interval barriers** (`invariantBarrier_forward_Icc`, `invariantBarrier_Icc`,
`torus_trapping_Icc`): the first-exit barrier argument of `invariantBarrier_forward` and the torus
trapping theorem, for solutions defined only on a closed parameter interval `[a, b] ∋ 0`. These
are exactly the a priori invariance hypothesis of the generic result.

Sanity: `ODEGlobal.zero_field_global` (the zero field: the constant curve is the unique solution).
-/

public section
noncomputable section

namespace PlasmaLean.Fields

open Set Filter Topology Real Metric
open scoped NNReal

namespace ODEGlobal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Uniform local existence.** If `f` is `C¹` on an open set `U ⊇ K` with `K` compact, there is a
uniform time `ε > 0` such that from every point of `K`, at every initial time `t₀`, there is a
solution of `β' = f(β)` on `(t₀ - ε, t₀ + ε)`. -/
theorem uniform_local_existence {f : E → E} {U K : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ ε > 0, ∀ x ∈ K, ∀ t₀ : ℝ, ∃ β : ℝ → E, β t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt β (f (β t)) t := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ K) := hK.cthickening
  have hcd : ∀ x ∈ cthickening δ K, ContDiffAt ℝ 1 f x :=
    fun x hx => hf.contDiffAt (hU.mem_nhds (hδU hx))
  obtain ⟨Kl, hKl⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK' (fun x hx => by
    obtain ⟨Kx, t, ht, hl⟩ := (hcd x hx).exists_lipschitzOnWith
    exact ⟨Kx, t, mem_nhdsWithin_of_mem_nhds ht, hl⟩)
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn
    (fun x hx => (hcd x hx).continuousAt.continuousWithinAt)
  set M' := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  refine ⟨δ / (M' + 1), by positivity, fun x hx t₀ => ?_⟩
  set ε := δ / (M' + 1) with hεdef
  have hε : 0 < ε := by positivity
  have hball : closedBall x δ ⊆ cthickening δ K := closedBall_subset_cthickening hx δ
  have hpl : IsPicardLindelof (fun _ => f) (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by constructor <;> linarith⟩ x ⟨δ, hδ.le⟩ 0 ⟨M', hM'0⟩ Kl := by
    apply IsPicardLindelof.of_time_independent
    · intro y hy; exact (hM y (hball hy)).trans (le_max_left _ _)
    · exact hKl.mono hball
    · change (M' : ℝ) * max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) ≤ δ - 0
      rw [sub_zero, show t₀ + ε - t₀ = ε by ring, show t₀ - (t₀ - ε) = ε by ring, max_self, hεdef,
        mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
  obtain ⟨β, hβ0, hβ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, fun t ht => (hβ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩

omit [ProperSpace E] in
/-- **Extension to the right.** A solution on `[a, b]` whose endpoint value `α b` admits a local
solution on `(b - ε, b + ε)` extends to a solution on `[a, b + ε/2]` agreeing with `α` on
`(-∞, b]`. -/
theorem extend_right {f : E → E} {ε a b : ℝ} (hε : 0 < ε) {α β₁ : ℝ → E}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (f (α t)) t) (hβ0 : β₁ b = α b)
    (hβ : ∀ t ∈ Ioo (b - ε) (b + ε), HasDerivAt β₁ (f (β₁ t)) t) :
    ∃ γ : ℝ → E, (∀ t ∈ Icc a (b + ε / 2), HasDerivAt γ (f (γ t)) t) ∧ ∀ t ≤ b, γ t = α t := by
  classical
  set γ : ℝ → E := fun t => if t ≤ b then α t else β₁ t with hγdef
  have hl : ∀ t ≤ b, γ t = α t := fun t ht => by simp [hγdef, ht]
  have hr : ∀ t, b ≤ t → γ t = β₁ t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · subst h; simp [hγdef, hβ0]
    · simp [hγdef, not_le.mpr h]
  refine ⟨γ, fun t ht => ?_, hl⟩
  rcases lt_trichotomy t b with h | h | h
  · rw [hl t h.le]
    refine (hα t ⟨ht.1, h.le⟩).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    exact hl s hs.le
  · subst h
    rw [hl t le_rfl]
    have h1 : HasDerivWithinAt γ (f (α t)) (Iic t) t :=
      (hα t ⟨ht.1, le_rfl⟩).hasDerivWithinAt.congr (fun s hs => hl s hs) (hl t le_rfl)
    have h2 : HasDerivWithinAt γ (f (α t)) (Ici t) t := by
      have h3 := (hβ t ⟨by linarith, by linarith⟩).hasDerivWithinAt (s := Ici t)
      rw [hβ0] at h3
      exact h3.congr (fun s hs => hr s hs) (hr t le_rfl)
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [hr t h.le]
    refine (hβ t ⟨by linarith, by linarith [ht.2]⟩).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact hr s (le_of_lt hs)

omit [ProperSpace E] in
/-- **Extension to the left.** A solution on `[a, b]` whose initial value `α a` admits a local
solution on `(a - ε, a + ε)` extends to a solution on `[a - ε/2, b]` agreeing with `α` on
`[a, ∞)`. -/
theorem extend_left {f : E → E} {ε a b : ℝ} (hε : 0 < ε) {α β₁ : ℝ → E}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (f (α t)) t) (hβ0 : β₁ a = α a)
    (hβ : ∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt β₁ (f (β₁ t)) t) :
    ∃ γ : ℝ → E, (∀ t ∈ Icc (a - ε / 2) b, HasDerivAt γ (f (γ t)) t) ∧ ∀ t, a ≤ t → γ t = α t := by
  classical
  set γ : ℝ → E := fun t => if a ≤ t then α t else β₁ t with hγdef
  have hr : ∀ t, a ≤ t → γ t = α t := fun t ht => by simp [hγdef, ht]
  have hl : ∀ t ≤ a, γ t = β₁ t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · subst h; simp [hγdef, hβ0]
    · simp [hγdef, not_le.mpr h]
  refine ⟨γ, fun t ht => ?_, hr⟩
  rcases lt_trichotomy t a with h | h | h
  · rw [hl t h.le]
    refine (hβ t ⟨by linarith [ht.1], by linarith⟩).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    exact hl s hs.le
  · subst h
    rw [hr t le_rfl]
    have h2 : HasDerivWithinAt γ (f (α t)) (Ici t) t :=
      (hα t ⟨le_rfl, ht.2⟩).hasDerivWithinAt.congr (fun s hs => hr s hs) (hr t le_rfl)
    have h1 : HasDerivWithinAt γ (f (α t)) (Iic t) t := by
      have h3 := (hβ t ⟨by linarith, by linarith⟩).hasDerivWithinAt (s := Iic t)
      rw [hβ0] at h3
      exact h3.congr (fun s hs => hl s hs) (hl t le_rfl)
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [hr t h.le]
    refine (hα t ⟨h.le, ht.2⟩).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact hr s (le_of_lt hs)

/-- The a priori invariance hypothesis: every solution of `α' = f(α)` on a closed interval
`[a, b] ∋ 0` starting in `Ω` stays in `Ω` on `[a, b]`. -/
@[expose] def LocallyInvariant (f : E → E) (Ω : Set E) : Prop :=
  ∀ (a b : ℝ) (α : ℝ → E), a ≤ 0 → 0 ≤ b → α 0 ∈ Ω →
    (∀ t ∈ Icc a b, HasDerivAt α (f (α t)) t) → ∀ t ∈ Icc a b, α t ∈ Ω

/-- **Global existence.** Under the a priori invariance of `Ω ⊆ K ⊆ U` (`K` compact, `U` open,
`f` `C¹` on `U`), every `x₀ ∈ Ω` is the initial point of a global solution `γ : ℝ → E`. -/
theorem exists_global {f : E → E} {U K Ω : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hΩK : Ω ⊆ K) (hinv : LocallyInvariant f Ω)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence hU hf hK hKU
  set h := ε / 2 with hh
  have hh0 : 0 < h := by positivity
  let P : ℕ → (ℝ → E) → Prop := fun n α =>
    α 0 = x₀ ∧ ∀ t ∈ Icc (-(n * h)) (n * h), HasDerivAt α (f (α t)) t
  have base : ∃ α, P 0 α := by
    obtain ⟨β, hβ0, hβ⟩ := hloc x₀ (hΩK hx₀) 0
    refine ⟨β, hβ0, fun t ht => hβ t ?_⟩
    simp only [CharP.cast_eq_zero, zero_mul, neg_zero, Icc_self, mem_singleton_iff] at ht
    subst ht; constructor <;> linarith
  have step : ∀ n (α : {α // P n α}), ∃ β : {β // P (n + 1) β},
      ∀ t ∈ Icc (-(n * h)) (n * h), β.1 t = α.1 t := by
    rintro n ⟨α, hα0, hα⟩
    have hnh : (0 : ℝ) ≤ n * h := by positivity
    have hb : α (n * h) ∈ K := hΩK (hinv _ _ α (by linarith) hnh (hα0 ▸ hx₀) hα _ ⟨by linarith,
      le_rfl⟩)
    obtain ⟨β₁, hβ₁0, hβ₁⟩ := hloc _ hb (n * h)
    obtain ⟨γ₁, hγ₁, hγ₁e⟩ := extend_right hε hα hβ₁0 hβ₁
    have hγ₁0 : γ₁ 0 = x₀ := by rw [hγ₁e 0 hnh, hα0]
    have ha : γ₁ (-(n * h)) ∈ K := hΩK (hinv _ _ γ₁ (by linarith) (by linarith)
      (hγ₁0 ▸ hx₀) hγ₁ _ ⟨le_rfl, by linarith⟩)
    obtain ⟨β₂, hβ₂0, hβ₂⟩ := hloc _ ha (-(n * h))
    obtain ⟨γ, hγ, hγe⟩ := extend_left hε hγ₁ hβ₂0 hβ₂
    refine ⟨⟨γ, ?_, fun t ht => hγ t ?_⟩, fun t ht => ?_⟩
    · rw [hγe 0 (by linarith), hγ₁0]
    · push_cast at ht ⊢
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · simp only
      rw [hγe t ht.1, hγ₁e t ht.2]
  choose next hnext using step
  let seq : ∀ n : ℕ, {α // P n α} := fun n =>
    Nat.rec (motive := fun n => {α // P n α}) ⟨base.choose, base.choose_spec⟩
      (fun n α => next n α) n
  have hseq : ∀ n, seq (n + 1) = next n (seq n) := fun n => rfl
  have hmono : ∀ n m : ℕ, n ≤ m → (n : ℝ) * h ≤ m * h := fun n m hnm =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) hh0.le
  have hagree : ∀ n m : ℕ, n ≤ m → ∀ t ∈ Icc (-(n * h)) (n * h), (seq m).1 t = (seq n).1 t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => intro t _; rfl
    | succ m hnm ih =>
      intro t ht
      rw [hseq, hnext m (seq m) t ⟨by linarith [ht.1, hmono n m hnm], by
        linarith [ht.2, hmono n m hnm]⟩, ih t ht]
  let N : ℝ → ℕ := fun t => ⌈|t| / h⌉₊ + 1
  have hN : ∀ t, |t| < N t * h := by
    intro t
    have h1 : |t| / h ≤ ⌈|t| / h⌉₊ := Nat.le_ceil _
    have h2 : |t| ≤ ⌈|t| / h⌉₊ * h := by rwa [div_le_iff₀ hh0] at h1
    simp only [N]; push_cast; nlinarith
  let γ : ℝ → E := fun t => (seq (N t)).1 t
  have hγeq : ∀ n : ℕ, ∀ s ∈ Icc (-(n * h)) (n * h), γ s = (seq n).1 s := by
    intro n s hs
    rcases le_total (N s) n with hle | hle
    · have hs' := abs_lt.mp (hN s)
      exact (hagree (N s) n hle s ⟨by linarith, by linarith⟩).symm
    · exact hagree n (N s) hle s hs
  refine ⟨γ, (seq (N 0)).2.1, fun t => ?_⟩
  have ht := abs_lt.mp (hN t)
  have hmem : t ∈ Icc (-(N t * h)) (N t * h) := ⟨ht.1.le, ht.2.le⟩
  rw [hγeq (N t) t hmem]
  refine ((seq (N t)).2.2 t hmem).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact hγeq (N t) s ⟨hs.1.le, hs.2.le⟩

omit [ProperSpace E] in
/-- A global solution starting in a locally invariant set stays in it for all time. -/
theorem global_mem {f : E → E} {Ω : Set E} (hinv : LocallyInvariant f Ω) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (f (γ t)) t) (h0 : γ 0 ∈ Ω) (t : ℝ) : γ t ∈ Ω :=
  hinv (-|t|) |t| γ (by simp) (abs_nonneg t) h0 (fun s _ => hγ s) t
    ⟨neg_abs_le t, le_abs_self t⟩

omit [ProperSpace E] in
/-- **Uniqueness.** Two global solutions with the same initial point in a locally invariant set
`Ω ⊆ K ⊆ U` (`K` compact, `f` `C¹` on the open set `U`) coincide. -/
theorem unique_global {f : E → E} {U K Ω : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (hΩK : Ω ⊆ K) (hinv : LocallyInvariant f Ω)
    {γ₁ γ₂ : ℝ → E} (h₁ : ∀ t, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (f (γ₂ t)) t) (h0 : γ₁ 0 = γ₂ 0) (hΩ : γ₁ 0 ∈ Ω) : γ₁ = γ₂ := by
  obtain ⟨Kl, hKl⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK (fun x hx => by
    obtain ⟨Kx, t, ht, hl⟩ := (hf.contDiffAt (hU.mem_nhds (hKU hx))).exists_lipschitzOnWith
    exact ⟨Kx, t, mem_nhdsWithin_of_mem_nhds ht, hl⟩)
  exact ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => K) (t₀ := 0)
    (fun _ => hKl) (fun t => ⟨h₁ t, hΩK (global_mem hinv h₁ hΩ t)⟩)
    (fun t => ⟨h₂ t, hΩK (global_mem hinv h₂ (h0 ▸ hΩ) t)⟩) h0

/-- **Global existence and uniqueness of trapped solutions.** Let `f` be `C¹` on an open set `U`,
`K ⊆ U` compact and `Ω ⊆ K` invariant for local solutions on closed intervals. Then from every
`x₀ ∈ Ω` there is exactly one global solution `γ : ℝ → E` of `γ' = f(γ)` with `γ 0 = x₀`, and it
stays in `Ω` for all time. -/
theorem existsUnique_global {f : E → E} {U K Ω : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hK : IsCompact K) (hKU : K ⊆ U) (hΩK : Ω ⊆ K)
    (hinv : LocallyInvariant f Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    (∃! γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t) ∧
      ∀ γ : ℝ → E, γ 0 = x₀ → (∀ t, HasDerivAt γ (f (γ t)) t) → ∀ t, γ t ∈ Ω := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global hU hf hK hKU hΩK hinv hx₀
  refine ⟨⟨γ, ⟨hγ0, hγ⟩, fun γ' ⟨h0', h'⟩ => ?_⟩, fun γ' h0' h' t => ?_⟩
  · exact unique_global hU hf hK hKU hΩK hinv h' hγ (h0'.trans hγ0.symm) (h0' ▸ hx₀)
  · exact global_mem hinv h' (h0' ▸ hx₀) t

/-- Sanity check (degenerate case): for the zero field every set is locally invariant
(solutions are constant), and the constant curve is the unique global solution. -/
theorem zero_field_global (x₀ : E) :
    ∃! γ : ℝ → E, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ ((fun _ => (0 : E)) (γ t)) t := by
  have hinv : LocallyInvariant (fun _ => (0 : E)) {x₀} := by
    intro a b α ha hb h0 hα t ht
    have hcont : ContinuousOn α (Icc a b) := fun u hu =>
      (hα u hu).continuousAt.continuousWithinAt
    have hc := constant_of_has_deriv_right_zero hcont
      (fun u hu => (hα u (Ico_subset_Icc_self hu)).hasDerivWithinAt)
    have hc : ∀ s ∈ Icc a b, α s = α 0 := fun s hs =>
      (hc s hs).trans (hc 0 ⟨ha, hb⟩).symm
    exact (hc t ht).trans h0
  exact (existsUnique_global (U := univ) (K := {x₀}) isOpen_univ contDiffOn_const
    isCompact_singleton (subset_univ _) subset_rfl hinv rfl).1

end ODEGlobal

/-! ## Barriers for solutions on a closed parameter interval -/

/-- **Forward barrier on an interval** (first-exit argument). Under the hypotheses of
`invariantBarrier_forward`, a solution of `γ' = B(γ)` on `[0, T]` starting in `Ω` stays in `Ω`
on `[0, T]`. -/
theorem invariantBarrier_forward_Icc {B : Space → Space} {G : Space → ℝ} {L : ℝ}
    {Ω C : Set Space} (hΩ : IsOpen Ω) (hC : IsOpen C)
    (hfront : ∀ x ∈ frontier Ω, x ∈ C ∧ G x = 0) (hne : ∀ x ∈ Ω ∩ C, G x ≠ 0)
    (hgr : GronwallOn B G L C) {γ : ℝ → Space} {T : ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivAt γ (B (γ t)) t) (h0 : γ 0 ∈ Ω) :
    ∀ t ∈ Icc 0 T, γ t ∈ Ω := by
  by_contra hcon
  push Not at hcon
  have hγc : ContinuousOn γ (Icc 0 T) := fun u hu => (hγ u hu).continuousAt.continuousWithinAt
  set S := {t | t ∈ Icc 0 T ∧ γ t ∉ Ω} with hS
  have hSeq : S = Icc 0 T ∩ γ ⁻¹' Ωᶜ := rfl
  have hSc : IsClosed S := by
    rw [hSeq]; exact hγc.preimage_isClosed_of_isClosed isClosed_Icc hΩ.isClosed_compl
  obtain ⟨t₀, ht₀, hbad⟩ := hcon
  have hSne : S.Nonempty := ⟨t₀, ht₀, hbad⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf S
  have ht₁S : t₁ ∈ S := hSc.csInf_mem hSne hSb
  have ht₁pos : 0 < t₁ := by
    rcases ht₁S.1.1.eq_or_lt with h | h
    · exact absurd (h ▸ h0) ht₁S.2
    · exact h
  have hbefore : ∀ u ∈ Ico 0 t₁, γ u ∈ Ω := by
    intro u hu
    by_contra h
    exact absurd (csInf_le hSb ⟨⟨hu.1, hu.2.le.trans ht₁S.1.2⟩, h⟩) (not_le.mpr hu.2)
  have hlim : Tendsto γ (𝓝[<] t₁) (𝓝 (γ t₁)) :=
    (hγ t₁ ht₁S.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in 𝓝[<] t₁, γ u ∈ Ω := by
    filter_upwards [Ioo_mem_nhdsLT ht₁pos] with u hu
    exact hbefore u ⟨hu.1.le, hu.2⟩
  have hcl : γ t₁ ∈ closure Ω := mem_closure_of_tendsto hlim hev
  have hfr : γ t₁ ∈ frontier Ω := by
    rw [frontier, hΩ.interior_eq]; exact ⟨hcl, ht₁S.2⟩
  obtain ⟨hCt, hG0⟩ := hfront _ hfr
  have hnhds : γ ⁻¹' C ∈ 𝓝 t₁ := (hγ t₁ ht₁S.1).continuousAt.preimage_mem_nhds (hC.mem_nhds hCt)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  set a := max 0 (t₁ - η / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have hat : a < t₁ := max_lt ht₁pos (by linarith)
  have hinC : ∀ u ∈ Icc a t₁, γ u ∈ C := by
    intro u hu
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have : t₁ - η / 2 ≤ a := le_max_right _ _
    constructor <;> linarith [hu.1, hu.2]
  have hbd := (fieldLine_abs_bounds_Icc hgr hat.le
    (fun u hu => hγ u ⟨ha0.trans hu.1, hu.2.trans ht₁S.1.2⟩) hinC).1
  rw [hG0, abs_zero] at hbd
  have hGa : G (γ a) ≠ 0 := hne _ ⟨hbefore a ⟨ha0, hat⟩, hinC a ⟨le_rfl, hat.le⟩⟩
  have := mul_pos (abs_pos.mpr hGa) (exp_pos (-(L * (t₁ - a))))
  linarith

/-- **Two-sided barrier on an interval.** Under the hypotheses of `invariantBarrier_forward`, a
solution of `γ' = B(γ)` on `[a, b] ∋ 0` starting in `Ω` stays in `Ω` on `[a, b]` (backward by
time reversal). -/
theorem invariantBarrier_Icc {B : Space → Space} {G : Space → ℝ} {L : ℝ}
    {Ω C : Set Space} (hΩ : IsOpen Ω) (hC : IsOpen C)
    (hfront : ∀ x ∈ frontier Ω, x ∈ C ∧ G x = 0) (hne : ∀ x ∈ Ω ∩ C, G x ≠ 0)
    (hgr : GronwallOn B G L C) {γ : ℝ → Space} {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (B (γ t)) t) (h0 : γ 0 ∈ Ω) :
    ∀ t ∈ Icc a b, γ t ∈ Ω := by
  intro t ht
  rcases le_total 0 t with h | h
  · exact invariantBarrier_forward_Icc hΩ hC hfront hne hgr (T := b)
      (fun u hu => hγ u ⟨by linarith [hu.1], hu.2⟩) h0 t ⟨h, ht.2⟩
  · have hrev : ∀ s ∈ Icc 0 (-a), HasDerivAt (fun s => γ (-s)) (-B (γ (-s))) s := by
      intro s hs
      have := (hγ (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).scomp s
        (hasDerivAt_neg s)
      simp only [neg_one_smul] at this
      exact this
    have := invariantBarrier_forward_Icc hΩ hC hfront hne hgr.neg hrev (by simpa using h0) (-t)
      ⟨by linarith, by linarith [ht.1]⟩
    simpa using this

open TubeCoords in
/-- **Torus trapping on an interval.** Under the hypotheses of `torus_trapping_forward`, every
solution of `γ' = B(γ)` on a closed interval `[a, b] ∋ 0` starting inside the torus stays inside
on `[a, b]`. -/
theorem torus_trapping_Icc {c : TubeCoords} {ρ : ℝ → ℝ → ℝ} {B : Space → Space}
    {ρmin R₁ g₀ L : ℝ} (hρ : TorusProfile ρ) (hmin : 0 < ρmin) (hlo : ∀ a b, ρmin ≤ ρ a b)
    (hhi : ∀ a b, ρ a b ≤ R₁) (hclosed : IsClosed {x | x ∈ c.T ∧ c.r x ≤ R₁}) (hg₀ : 0 < g₀)
    (hinv : ∀ x ∈ c.T, 0 < c.r x → |c.G ρ x| < g₀ → |fderiv ℝ (c.G ρ) x (B x)| ≤ L * |c.G ρ x|)
    {γ : ℝ → Space} {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (B (γ t)) t) (h0 : γ 0 ∈ c.inside ρ) :
    ∀ t ∈ Icc a b, γ t ∈ c.inside ρ := by
  refine invariantBarrier_Icc (G := c.G ρ) (L := L) (C := c.collar ρ g₀)
    (isOpen_inside hρ hmin hlo) (isOpen_collar hρ g₀) (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) ha hb hγ h0
  · obtain ⟨hoff, heq⟩ := frontier_inside hρ hmin hlo hhi hclosed hx
    have hG0 : c.G ρ x = 0 := by simp only [G]; linarith
    exact ⟨⟨hoff, by simp [hG0, hg₀]⟩, hG0⟩
  · obtain ⟨⟨hT, h | h⟩, ⟨_, hr⟩, _⟩ := hx
    · exact absurd h (not_le.mpr hr)
    · simp only [G]; linarith
  · obtain ⟨hoff, hGx⟩ := hx
    refine ⟨differentiableAt_G hρ hoff, hinv x hoff.1 hoff.2 ?_⟩
    simp only [mem_preimage, mem_Ioo] at hGx
    exact abs_lt.mpr hGx

end PlasmaLean.Fields
