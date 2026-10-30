/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.BoozerGuidingCentre
public import PlasmaLean.Theory.Fields.ODEContinuation

/-!
# Existence of Boozer guiding-centre orbits (audit finding MA-M1)

`BoozerGCOrbitOn F m q μ ψ θ φ ρ T` (in `BoozerGuidingCentre`) is a property of a *supplied*
trajectory that stays off the magnetic axis (`ψ > 0`) on `[0, T]`. This file writes the model as
a first-order system `s' = boozerVF F m q μ s` on the state `s = (ψ, θ, φ, ρ) ∈ ℝ × ℝ × ℝ × ℝ` and
proves existence statements for it.

Results:

* `boozerGCOrbitOn_of_flow`, `boozerGCOrbit_of_flow`: solutions of the first-order system that
  stay in `ψ > 0` are `BoozerGCOrbitOn` (resp. `BoozerGCOrbit`) trajectories;
* **`boozerGCOrbitOn_exists_local`** (Picard–Lindelöf): if the vector field is `C¹` on the chart
  domain `{ψ > 0}`, then from every off-axis initial state `s₀` (`ψ₀ > 0`) there is an orbit on
  `[0, T]` for some `T > 0`;
* **`boozerGCOrbitOn_exists_of_apriori`** (continuation to a prescribed horizon): if moreover
  every solution from `s₀` on `[-c, c]`, `0 ≤ c ≤ T`, stays in a fixed compact subset of
  `{ψ > 0}`, then an orbit exists on the whole prescribed interval `[0, T]`;
* `boozerGCOrbit_exists_of_apriori`: with a priori bounds on every horizon, an orbit exists for
  all time.

What is **not** proved here: the a priori bound itself (that orbits from the hypothesis bundle of
the near-axis results stay at `ψ ≥ ψ_min > 0` up to the horizon). For passing alphas born near the
axis this is false in general (they may cross the axis), which is exactly why `BoozerGCOrbitOn`
carries `ψ > 0` as a hypothesis.
-/

public section
noncomputable section
namespace PlasmaLean.Kinetic.Boozer
open PlasmaLean.Fields.ODEGlobal Set Filter Topology

/-- The vacuum Boozer guiding-centre vector field on the state `(ψ, θ, φ, ρ)` (the right-hand
sides of `BoozerGCOrbit`). -/
@[expose] def boozerVF (F : BoozerField) (m q μ : ℝ) (s : ℝ × ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (-(m * μ + q ^ 2 * s.2.2.2 ^ 2 * F.B s.1 s.2.1 s.2.2.1) * F.Bθ s.1 s.2.1 s.2.2.1 / (m * q),
   (μ / q + q * s.2.2.2 ^ 2 * F.B s.1 s.2.1 s.2.2.1 / m) * F.Bψ s.1 s.2.1 s.2.2.1 +
      q * s.2.2.2 * F.B s.1 s.2.1 s.2.2.1 ^ 2 * F.ι s.1 / (F.G * m),
   q * s.2.2.2 * F.B s.1 s.2.1 s.2.2.1 ^ 2 / (F.G * m),
   -(m * μ + q ^ 2 * s.2.2.2 ^ 2 * F.B s.1 s.2.1 s.2.2.1) *
      (F.Bφ s.1 s.2.1 s.2.2.1 + F.ι s.1 * F.Bθ s.1 s.2.1 s.2.2.1) / (F.G * m * q))

/-- The chart domain `{ψ > 0}` of the state space. -/
@[expose] def chartDomain : Set (ℝ × ℝ × ℝ × ℝ) := {s | 0 < s.1}

/-- The chart domain is open. -/
theorem isOpen_chartDomain : IsOpen chartDomain := isOpen_lt continuous_const continuous_fst

/-- The four components of a solution of the first-order system satisfy the Boozer
guiding-centre equations at time `t`. -/
theorem boozer_components {F : BoozerField} {m q μ : ℝ} {γ : ℝ → ℝ × ℝ × ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ (boozerVF F m q μ (γ t)) t) :
    HasDerivAt (fun t => (γ t).1) (boozerVF F m q μ (γ t)).1 t ∧
    HasDerivAt (fun t => (γ t).2.1) (boozerVF F m q μ (γ t)).2.1 t ∧
    HasDerivAt (fun t => (γ t).2.2.1) (boozerVF F m q μ (γ t)).2.2.1 t ∧
    HasDerivAt (fun t => (γ t).2.2.2) (boozerVF F m q μ (γ t)).2.2.2 t := by
  have h1 := (hasFDerivAt_fst (p := γ t)).comp_hasDerivAt t h
  have h2 := (hasFDerivAt_snd (p := γ t)).comp_hasDerivAt t h
  have h21 := (hasFDerivAt_fst (p := (γ t).2)).comp_hasDerivAt t h2
  have h22 := (hasFDerivAt_snd (p := (γ t).2)).comp_hasDerivAt t h2
  have h221 := (hasFDerivAt_fst (p := (γ t).2.2)).comp_hasDerivAt t h22
  have h222 := (hasFDerivAt_snd (p := (γ t).2.2)).comp_hasDerivAt t h22
  exact ⟨h1, h21, h221, h222⟩

/-- A solution of the first-order system on `[0, T]` that stays in `ψ > 0` there is a
`BoozerGCOrbitOn` trajectory. -/
theorem boozerGCOrbitOn_of_flow {F : BoozerField} {m q μ T : ℝ} {γ : ℝ → ℝ × ℝ × ℝ × ℝ}
    (hγ : ∀ t ∈ Icc 0 T, HasDerivAt γ (boozerVF F m q μ (γ t)) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < (γ t).1) :
    BoozerGCOrbitOn F m q μ (fun t => (γ t).1) (fun t => (γ t).2.1) (fun t => (γ t).2.2.1)
      (fun t => (γ t).2.2.2) T where
  pos := hpos
  dψ t ht := (boozer_components (hγ t ht)).1
  dθ t ht := (boozer_components (hγ t ht)).2.1
  dφ t ht := (boozer_components (hγ t ht)).2.2.1
  dρ t ht := (boozer_components (hγ t ht)).2.2.2

/-- A global solution of the first-order system that stays in `ψ > 0` is a `BoozerGCOrbit`. -/
theorem boozerGCOrbit_of_flow {F : BoozerField} {m q μ : ℝ} {γ : ℝ → ℝ × ℝ × ℝ × ℝ}
    (hγ : ∀ t, HasDerivAt γ (boozerVF F m q μ (γ t)) t) (hpos : ∀ t, 0 < (γ t).1) :
    BoozerGCOrbit F m q μ (fun t => (γ t).1) (fun t => (γ t).2.1) (fun t => (γ t).2.2.1)
      (fun t => (γ t).2.2.2) where
  pos := hpos
  dψ t := (boozer_components (hγ t)).1
  dθ t := (boozer_components (hγ t)).2.1
  dφ t := (boozer_components (hγ t)).2.2.1
  dρ t := (boozer_components (hγ t)).2.2.2

/-- **Local existence of off-axis Boozer guiding-centre orbits** (Picard–Lindelöf). If the vector
field is `C¹` on the chart domain `{ψ > 0}`, then for every initial state `s₀ = (ψ₀, θ₀, φ₀, ρ₀)`
with `ψ₀ > 0` there are `T > 0` and an orbit `BoozerGCOrbitOn … T` starting at `s₀`. -/
theorem boozerGCOrbitOn_exists_local {F : BoozerField} {m q μ : ℝ}
    (hF : ContDiffOn ℝ 1 (boozerVF F m q μ) chartDomain) {s₀ : ℝ × ℝ × ℝ × ℝ}
    (hs₀ : 0 < s₀.1) :
    ∃ T > 0, ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧
      ρ 0 = s₀.2.2.2 ∧ BoozerGCOrbitOn F m q μ ψ θ φ ρ T := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence isOpen_chartDomain hF isCompact_singleton
    (singleton_subset_iff.mpr hs₀)
  obtain ⟨β, hβ0, hβ⟩ := hloc s₀ rfl 0
  have hd0 : HasDerivAt β (boozerVF F m q μ (β 0)) 0 := hβ 0 ⟨by linarith, by linarith⟩
  have hc : ContinuousAt (fun t => (β t).1) 0 :=
    continuous_fst.continuousAt.comp hd0.continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (β t).1 :=
    continuousAt_const.eventually_lt hc (by simpa [hβ0] using hs₀)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set T := min ε δ / 2 with hT
  have hT0 : 0 < T := by positivity
  have hTε : T < ε := by have := min_le_left ε δ; linarith
  have hTδ : T < δ := by have := min_le_right ε δ; linarith
  refine ⟨T, hT0, _, _, _, _, by rw [hβ0], by rw [hβ0], by rw [hβ0], by rw [hβ0],
    boozerGCOrbitOn_of_flow (fun t ht => hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (fun t ht => hball ?_)⟩
  rw [Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- **Existence on a prescribed horizon from an a priori bound.** If the vector field is `C¹` on
`{ψ > 0}` and every solution from `s₀` on `[-c, c]` (`0 ≤ c ≤ T`) stays in a fixed compact set
`K ⊆ {ψ > 0}`, then there is an orbit `BoozerGCOrbitOn … T` starting at `s₀` on the whole interval
`[0, T]`. -/
theorem boozerGCOrbitOn_exists_of_apriori {F : BoozerField} {m q μ T : ℝ} (hT : 0 ≤ T)
    (hF : ContDiffOn ℝ 1 (boozerVF F m q μ) chartDomain) {s₀ : ℝ × ℝ × ℝ × ℝ}
    (hs₀ : 0 < s₀.1) {K : Set (ℝ × ℝ × ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ chartDomain)
    (hbd : ∀ c ∈ Icc 0 T, ∀ α : ℝ → ℝ × ℝ × ℝ × ℝ, α 0 = s₀ →
      (∀ t ∈ Icc (-c) c, HasDerivAt α (boozerVF F m q μ (α t)) t) → ∀ t ∈ Icc (-c) c, α t ∈ K) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbitOn F m q μ ψ θ φ ρ T := by
  obtain ⟨ε, hε, hloc⟩ := uniform_local_existence isOpen_chartDomain hF isCompact_singleton
    (singleton_subset_iff.mpr hs₀)
  obtain ⟨β₀, hβ₀0, hβ₀⟩ := hloc s₀ rfl 0
  obtain ⟨β, hβ0, hβ, -⟩ := extend_to_horizon isOpen_chartDomain hF hK hKU hbd le_rfl hT hβ₀0
    (fun t ht => hβ₀ t (by
      have : t = 0 := by simp only [neg_zero, Icc_self, mem_singleton_iff] at ht; exact ht
      subst this; constructor <;> linarith))
  have hbK := hbd T ⟨hT, le_rfl⟩ β hβ0 hβ
  refine ⟨_, _, _, _, by rw [hβ0], by rw [hβ0], by rw [hβ0], by rw [hβ0],
    boozerGCOrbitOn_of_flow (fun t ht => hβ t ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => hKU (hbK t ⟨by linarith [ht.1], ht.2⟩))⟩

/-- **Global existence from a priori bounds.** If the vector field is `C¹` on `{ψ > 0}` and the
solutions from `s₀` are a priori bounded on every finite horizon by compact subsets of `{ψ > 0}`,
there is an orbit `BoozerGCOrbit` (all real times) starting at `s₀`. -/
theorem boozerGCOrbit_exists_of_apriori {F : BoozerField} {m q μ : ℝ}
    (hF : ContDiffOn ℝ 1 (boozerVF F m q μ) chartDomain) {s₀ : ℝ × ℝ × ℝ × ℝ}
    (hs₀ : 0 < s₀.1) (hbd : APrioriBounded (boozerVF F m q μ) chartDomain s₀) :
    ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧ ρ 0 = s₀.2.2.2 ∧
      BoozerGCOrbit F m q μ ψ θ φ ρ := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_of_apriori isOpen_chartDomain hF hs₀ hbd
  have hpos : ∀ t, 0 < (γ t).1 := fun t => by
    obtain ⟨K, -, hKU, hKb⟩ := hbd |t|
    exact hKU (hKb |t| ⟨abs_nonneg t, le_rfl⟩ γ hγ0 (fun s _ => hγ s) t
      ⟨neg_abs_le t, le_abs_self t⟩)
  exact ⟨_, _, _, _, by rw [hγ0], by rw [hγ0], by rw [hγ0], by rw [hγ0],
    boozerGCOrbit_of_flow hγ hpos⟩

end PlasmaLean.Kinetic.Boozer
