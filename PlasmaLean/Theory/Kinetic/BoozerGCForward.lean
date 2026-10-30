/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGCExistence
public import PlasmaLean.Theory.Kinetic.CanonicalMomentum

/-!
# Forward continuation of Boozer guiding-centre orbits (audit finding MA-M1)

`boozerGCOrbitOn_exists_of_apriori` (in `BoozerGCExistence`) needs an a priori bound on symmetric
time intervals `[-c, c]`. The trapping estimates of the near-axis files are *forward* estimates
(they are proved for orbits on `[0, t]`). This file gives the forward versions.

* `ODEGlobal.exists_forward_of_apriori`: a `C¹` field on an open `U` whose forward solutions
  from `x₀` on `[0, c]` (`c ≤ T`) stay in a fixed compact `K ⊆ U` has a solution on `[0, T]`
  (with derivatives at both endpoints);
* `boozerGCOrbitOn_exists_of_forward_apriori`: the Boozer version;
* **`boozerGCOrbitOn_exists_of_region`**: it suffices that forward solutions stay in a closed set
  `R ⊆ {ψ > 0}` on which the vector field is bounded (`‖f‖ ≤ M`); then they also stay within
  `M T` of `s₀`, and `R ∩ closedBall s₀ (M T)` is the compact set. The orbit stays in `R`;
* **`boozer_bootstrap`**: the continuity (bootstrap) argument that turns an estimate for genuine
  orbits (which stay off the axis by definition) into an a priori bound for arbitrary solutions
  of the first-order system: if every orbit on `[0, t]` that has stayed in the band
  `|ψ − ψ₀| ≤ D` (with `D < ψ₀`) satisfies `|ψ t − ψ₀| ≤ D' < D`, then every solution stays in
  `|ψ − ψ₀| ≤ D'`.

Sanity: `exists_forward_of_apriori_zero` (zero field).
-/

public section
noncomputable section

namespace PlasmaLean.Fields.ODEGlobal

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Forward continuation to a horizon.** If `f` is `C¹` on the open set `U ∋ x₀`, and every
solution of `α' = f(α)` on `[0, c]` (`0 ≤ c ≤ T`) with `α 0 = x₀` stays in a fixed compact
`K ⊆ U` on `[0, c]`, then there is a solution on `[0, T]` with `β 0 = x₀` (derivatives at every
`t ∈ [0, T]`, including the endpoints). -/
theorem exists_forward_of_apriori {f : E → E} {U K : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hK : IsCompact K) (hKU : K ⊆ U) {x₀ : E} (hx₀ : x₀ ∈ U)
    {T : ℝ} (hT : 0 ≤ T)
    (hbd : ∀ c ∈ Icc 0 T, ∀ α : ℝ → E, α 0 = x₀ →
      (∀ t ∈ Icc 0 c, HasDerivAt α (f (α t)) t) → ∀ t ∈ Icc 0 c, α t ∈ K) :
    ∃ β : ℝ → E, β 0 = x₀ ∧ ∀ t ∈ Icc 0 T, HasDerivAt β (f (β t)) t := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence hU hf (hK.union isCompact_singleton)
    (union_subset hKU (singleton_subset_iff.mpr hx₀))
  set h := ε / 2 with hh
  have hh0 : 0 < h := by positivity
  have key : ∀ k : ℕ, (k : ℝ) * h ≤ T + h → ∃ β : ℝ → E, β 0 = x₀ ∧
      ∀ t ∈ Icc 0 ((k : ℝ) * h), HasDerivAt β (f (β t)) t := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨β, hβ0, hβ⟩ := hloc x₀ (Or.inr rfl) 0
      refine ⟨β, hβ0, fun t ht => hβ t ?_⟩
      simp only [CharP.cast_eq_zero, zero_mul, Icc_self, mem_singleton_iff] at ht
      subst ht; constructor <;> linarith
    | succ k ih =>
      intro hk
      push_cast at hk
      obtain ⟨β, hβ0, hβ⟩ := ih (by linarith)
      set c := (k : ℝ) * h with hc
      have hc0 : 0 ≤ c := by positivity
      have hcT : c ≤ T := by linarith
      have hmem := hbd c ⟨hc0, hcT⟩ β hβ0 hβ c ⟨hc0, le_rfl⟩
      obtain ⟨β₁, hβ₁0, hβ₁⟩ := hloc _ (Or.inl hmem) c
      obtain ⟨γ, hγ, hγe⟩ := extend_right hε hβ hβ₁0 hβ₁
      refine ⟨γ, by rw [hγe 0 hc0, hβ0], fun t ht => hγ t ⟨ht.1, ?_⟩⟩
      have := ht.2
      push_cast at this
      linarith
  set k := ⌈T / h⌉₊ with hk
  have h1 : T / h ≤ k := Nat.le_ceil _
  have h1' : T ≤ k * h := by rwa [div_le_iff₀ hh0] at h1
  have h2' : (k : ℝ) * h ≤ T + h := by
    have := Nat.ceil_lt_add_one (div_nonneg hT hh0.le)
    rw [← hk] at this
    have h3 : (k : ℝ) - 1 < T / h := by linarith
    rw [lt_div_iff₀ hh0] at h3
    linarith
  obtain ⟨β, hβ0, hβ⟩ := key k h2'
  exact ⟨β, hβ0, fun t ht => hβ t ⟨ht.1, ht.2.trans h1'⟩⟩

omit [ProperSpace E] in
/-- Sanity check (degenerate case): for the zero field the constant curve is a forward
solution, and the forward a priori hypothesis holds with `K = {x₀}`. -/
theorem forward_apriori_zero (x₀ : E) (T : ℝ) :
    ∀ c ∈ Icc 0 T, ∀ α : ℝ → E, α 0 = x₀ →
      (∀ t ∈ Icc 0 c, HasDerivAt α ((fun _ => (0 : E)) (α t)) t) →
      ∀ t ∈ Icc 0 c, α t ∈ ({x₀} : Set E) := by
  intro c _ α h0 hα t ht
  have hc : ∀ s ∈ Icc 0 c, α s = α 0 := constant_of_has_deriv_right_zero
    (fun x hx => (hα x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hα x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
  simp [hc t ht, h0]

/-- Sanity check: the zero field has a forward solution on every horizon. -/
theorem exists_forward_of_apriori_zero (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ β : ℝ → E, β 0 = x₀ ∧ ∀ t ∈ Icc 0 T, HasDerivAt β ((fun _ => (0 : E)) (β t)) t :=
  exists_forward_of_apriori isOpen_univ contDiffOn_const isCompact_singleton (subset_univ _)
    (mem_univ x₀) hT (forward_apriori_zero x₀ T)

end PlasmaLean.Fields.ODEGlobal

namespace PlasmaLean.Kinetic.Boozer

open PlasmaLean.Fields.ODEGlobal Set Filter Topology

/-- **Existence on a prescribed horizon from a forward a priori bound.** If the vector field is
`C¹` on `{ψ > 0}` and every forward solution from `s₀` on `[0, c]` (`0 ≤ c ≤ T`) stays in a fixed
compact set `K ⊆ {ψ > 0}`, then there is an orbit `BoozerGCOrbitOn … T` starting at `s₀` that
stays in `K` on `[0, T]`. -/
theorem boozerGCOrbitOn_exists_of_forward_apriori {F : BoozerField} {m q μ T : ℝ} (hT : 0 ≤ T)
    (hF : ContDiffOn ℝ 1 (boozerVF F m q μ) chartDomain) {s₀ : ℝ × ℝ × ℝ × ℝ}
    (hs₀ : 0 < s₀.1) {K : Set (ℝ × ℝ × ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ chartDomain)
    (hbd : ∀ c ∈ Icc 0 T, ∀ α : ℝ → ℝ × ℝ × ℝ × ℝ, α 0 = s₀ →
      (∀ t ∈ Icc 0 c, HasDerivAt α (boozerVF F m q μ (α t)) t) → ∀ t ∈ Icc 0 c, α t ∈ K) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn F m q μ ψ θ φ ρ T ∧ ∀ t ∈ Icc 0 T, (ψ t, θ t, φ t, ρ t) ∈ K := by
  obtain ⟨β, hβ0, hβ⟩ := exists_forward_of_apriori isOpen_chartDomain hF hK hKU hs₀ hT hbd
  have hbK := hbd T ⟨hT, le_rfl⟩ β hβ0 hβ
  exact ⟨_, _, _, _, by rw [hβ0], by rw [hβ0], by rw [hβ0], by rw [hβ0],
    boozerGCOrbitOn_of_flow hβ (fun t ht => hKU (hbK t ht)), fun t ht => hbK t ht⟩

/-- **Existence from forward invariance of a region with bounded vector field.** Let `R` be a
closed subset of `{ψ > 0}` on which `‖boozerVF‖ ≤ M`. If every forward solution from `s₀` on
`[0, c]` (`0 ≤ c ≤ T`) stays in `R`, then there is an orbit `BoozerGCOrbitOn … T` starting at
`s₀` that stays in `R` on `[0, T]`. (The angles need not be bounded in `R`: solutions also stay
in the ball of radius `M T` around `s₀`, which supplies compactness.) -/
theorem boozerGCOrbitOn_exists_of_region {F : BoozerField} {m q μ T : ℝ} (hT : 0 ≤ T)
    (hF : ContDiffOn ℝ 1 (boozerVF F m q μ) chartDomain) {s₀ : ℝ × ℝ × ℝ × ℝ}
    (hs₀ : 0 < s₀.1) {R : Set (ℝ × ℝ × ℝ × ℝ)} (hRc : IsClosed R) (hRU : R ⊆ chartDomain)
    {M : ℝ} (hM : ∀ s ∈ R, ‖boozerVF F m q μ s‖ ≤ M)
    (hR : ∀ c ∈ Icc 0 T, ∀ α : ℝ → ℝ × ℝ × ℝ × ℝ, α 0 = s₀ →
      (∀ t ∈ Icc 0 c, HasDerivAt α (boozerVF F m q μ (α t)) t) → ∀ t ∈ Icc 0 c, α t ∈ R) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn F m q μ ψ θ φ ρ T ∧ ∀ t ∈ Icc 0 T, (ψ t, θ t, φ t, ρ t) ∈ R := by
  set K := R ∩ Metric.closedBall s₀ (M * T) with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_left hRc
  have hKU : K ⊆ chartDomain := fun s hs => hRU hs.1
  obtain ⟨ψ, θ, φ, ρ, h0, h1, h2, h3, horb, hmem⟩ :=
    boozerGCOrbitOn_exists_of_forward_apriori hT hF hs₀ hK hKU (fun c hc α hα0 hα t ht => by
      have hRα := hR c hc α hα0 hα
      refine ⟨hRα t ht, ?_⟩
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (hRα 0 ⟨le_rfl, ht.1.trans ht.2⟩))
      have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := α)
        (f' := fun s => boozerVF F m q μ (α s)) (C := M)
        (fun s hs => (hα s hs).hasDerivWithinAt)
        (fun s hs => hM _ (hRα s (Ico_subset_Icc_self hs))) t ht
      rw [Metric.mem_closedBall, dist_eq_norm, ← hα0]
      refine hmv.trans ?_
      have : t - 0 ≤ T := by linarith [ht.2, hc.2]
      exact mul_le_mul_of_nonneg_left this hM0)
  exact ⟨ψ, θ, φ, ρ, h0, h1, h2, h3, horb, fun t ht => (hmem t ht).1⟩

/-- **Bootstrap (continuity) argument.** Let `α` solve the first-order Boozer system on `[0, c]`
with `(α 0).1 = ψ₀`, and let `0 ≤ D' < D < ψ₀`. Suppose that for every `t ∈ [0, c]`, if the solution
has stayed in the band `|ψ − ψ₀| ≤ D` on `[0, t]` (so it is a genuine orbit
`BoozerGCOrbitOn … t`, off the axis), then `|ψ t − ψ₀| ≤ D'`. Then `|ψ t − ψ₀| ≤ D'` on all of
`[0, c]`. -/
theorem boozer_bootstrap {F : BoozerField} {m q μ c ψ₀ D D' : ℝ}
    {α : ℝ → ℝ × ℝ × ℝ × ℝ} (hD'0 : 0 ≤ D') (hDD : D' < D) (hDψ : D < ψ₀) (hα0 : (α 0).1 = ψ₀)
    (hα : ∀ t ∈ Icc 0 c, HasDerivAt α (boozerVF F m q μ (α t)) t)
    (step : ∀ t ∈ Icc 0 c,
      BoozerGCOrbitOn F m q μ (fun t => (α t).1) (fun t => (α t).2.1) (fun t => (α t).2.2.1)
        (fun t => (α t).2.2.2) t →
      (∀ s ∈ Icc 0 t, |(α s).1 - ψ₀| ≤ D) → |(α t).1 - ψ₀| ≤ D') :
    ∀ t ∈ Icc 0 c, |(α t).1 - ψ₀| ≤ D' := by
  rcases lt_or_ge c 0 with hc | hc
  · intro t ht; exact absurd (ht.1.trans ht.2) (not_le.mpr hc)
  set f : ℝ → ℝ := fun s => |(α (projIcc 0 c hc s)).1 - ψ₀| with hfdef
  have hαc : ContinuousOn α (Icc 0 c) := fun s hs => (hα s hs).continuousAt.continuousWithinAt
  have hfc : Continuous f :=
    continuous_abs.comp ((continuous_fst.comp (hαc.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) (fun s => Subtype.mem _))).sub
      continuous_const)
  have hfeq : ∀ s ∈ Icc 0 c, f s = |(α s).1 - ψ₀| := fun s hs => by
    simp only [hfdef, projIcc_of_mem hc hs]
  have hf0 : f 0 ≤ D' := by
    rw [hfeq 0 ⟨le_rfl, hc⟩, hα0, sub_self, abs_zero]; exact hD'0
  intro t₀ ht₀
  rw [← hfeq t₀ ht₀]
  refine trapped_until hfc hDD hf0 (fun t ht hhist' => ?_) t₀ ht₀
  have hsub : ∀ s ∈ Icc 0 t, s ∈ Icc 0 c := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  have hhist : ∀ s ∈ Icc 0 t, |(α s).1 - ψ₀| ≤ D := fun s hs => by
    rw [← hfeq s (hsub s hs)]; exact hhist' s hs
  rw [hfeq t ht]
  refine step t ht (boozerGCOrbitOn_of_flow (fun s hs => hα s (hsub s hs)) (fun s hs => ?_)) hhist
  have := (abs_le.mp (hhist s hs)).1
  linarith

end PlasmaLean.Kinetic.Boozer
