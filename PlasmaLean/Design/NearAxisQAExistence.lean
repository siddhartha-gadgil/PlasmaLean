/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.NearAxisQAAveraged
public import PlasmaLean.Theory.Kinetic.BoozerGCExistence

/-!
# Off-axis near-axis QA guiding-centre orbits exist locally (audit finding MA-M1)

The near-axis QA results (`NearAxisQA.alpha_trapped_reactorQA`,
`NearAxisQAAveraged.alpha_trapped_reactorQA_averaged*`) quantify over supplied
`BoozerGCOrbitOn reactorQA …` trajectories, which stay off the magnetic axis by definition. This
file proves that such trajectories exist.

Results:

* `field_boozerVF_contDiffOn`: for every near-axis model `NearAxisQA.field …` the Boozer
  guiding-centre vector field is `C¹` (indeed smooth) on the chart domain `ψ > 0`; the
  coefficients involve `r = √(2ψ/B₀)` and `1/r`, which are smooth for `ψ > 0`;
* **`nearAxis_orbit_exists_local`**, **`reactorQA_orbit_exists_local`**: from every initial state
  with `ψ₀ > 0` there is an orbit `BoozerGCOrbitOn … T` for some `T > 0`;
* **`alpha_trapped_reactorQA_averaged_nonvacuous`**: the full hypothesis bundle of
  `alpha_trapped_reactorQA_averaged_of_le` (energy `E_α = 3.5 MeV`, pitch `v_∥² ≥ 0.81 · 2E/m`,
  birth at `ψ₀ = psiStart`, orbit on `[0, T]`) is satisfied by a constructed orbit for some
  `0 < T ≤ 0.19 s`, and that orbit stays at `ψ ≤ 8.2` on `[0, T]`.

**Not proved** (recorded in `notes/theory/orbit-existence.md`): existence on the full horizon
`[0, 0.19 s]` (or `[0, 8 × 10⁻⁴ s]` of `alpha_trapped_reactorQA`). That needs an a priori lower
bound `ψ ≥ ψ_min > 0` along the orbit up to the horizon (`boozerGCOrbitOn_exists_of_apriori`
then applies); for passing alphas born at `ψ₀ ≤ psiStart` the orbit can reach the axis, so such
a bound cannot hold for the whole hypothesis class. The `T` obtained here is not quantified.
-/

public section
noncomputable section
namespace PlasmaLean.Design.NearAxisQAExistence
open PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer PlasmaLean.Design.NearAxisQA
  PlasmaLean.Design.NearAxisQAAveraged Set

/-- The Boozer guiding-centre vector field of every near-axis QA model is `C¹` on the chart domain
`ψ > 0`. -/
theorem field_boozerVF_contDiffOn (B₀ η b₀ b₁ B₂c ι₀ G : ℝ) (hB₀ : 0 < B₀) (m q μ : ℝ) :
    ContDiffOn ℝ 1 (boozerVF (field B₀ η b₀ b₁ B₂c ι₀ G hB₀) m q μ) chartDomain := by
  unfold boozerVF
  simp only [field, nearAxisB, nearAxisBψ, nearAxisBθ, nearAxisBφ, radius]
  fun_prop (disch := (intro x hx; have hx' : 0 < x.1 := hx; positivity))

/-- **Local existence for every near-axis QA model.** From every initial state with `ψ₀ > 0`
there is an orbit `BoozerGCOrbitOn (field …) m q μ … T` for some `T > 0`. -/
theorem nearAxis_orbit_exists_local (B₀ η b₀ b₁ B₂c ι₀ G : ℝ) (hB₀ : 0 < B₀) (m q μ : ℝ)
    {s₀ : ℝ × ℝ × ℝ × ℝ} (hs₀ : 0 < s₀.1) :
    ∃ T > 0, ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧
      ρ 0 = s₀.2.2.2 ∧ BoozerGCOrbitOn (field B₀ η b₀ b₁ B₂c ι₀ G hB₀) m q μ ψ θ φ ρ T :=
  boozerGCOrbitOn_exists_local (field_boozerVF_contDiffOn B₀ η b₀ b₁ B₂c ι₀ G hB₀ m q μ) hs₀

/-- **Local existence for the reactor QA model.** For every mass, charge and magnetic moment and
every initial state off the axis (`ψ₀ > 0`), there is an orbit `BoozerGCOrbitOn reactorQA … T`
for some `T > 0`. -/
theorem reactorQA_orbit_exists_local (m q μ : ℝ) {s₀ : ℝ × ℝ × ℝ × ℝ} (hs₀ : 0 < s₀.1) :
    ∃ T > 0, ∃ ψ θ φ ρ : ℝ → ℝ, ψ 0 = s₀.1 ∧ θ 0 = s₀.2.1 ∧ φ 0 = s₀.2.2.1 ∧
      ρ 0 = s₀.2.2.2 ∧ BoozerGCOrbitOn reactorQA m q μ ψ θ φ ρ T :=
  nearAxis_orbit_exists_local _ _ _ _ _ _ _ _ m q μ hs₀

/-- Initial parallel gyroradius of a 3.5 MeV alpha with `μ = 0` born at `(psiStart, 0, 0)`:
`ρ₀ = √(2 m E_α) / (q B)`. -/
@[expose] def alphaRho0 : ℝ := Real.sqrt (2 * mα * Eα) / (qα * reactorQA.B psiStart 0 0)

/-- **Non-vacuity of the averaged near-QA theorem on a short horizon.** There are `0 < T ≤ 0.19 s`
and a constructed orbit `BoozerGCOrbitOn reactorQA mα qα 0 … T` with energy exactly `E_α`
(3.5 MeV), pitch `v_∥² = 2E_α/m ≥ 0.81 · 2E_α/m`, born at `ψ₀ = psiStart`; by
`alpha_trapped_reactorQA_averaged_of_le` it stays at `ψ ≤ 8.2` on `[0, T]`. -/
theorem alpha_trapped_reactorQA_averaged_nonvacuous :
    ∃ T > 0, T ≤ Tav ∧ ∃ (μ : ℝ) (ψ θ φ ρ : ℝ → ℝ), 0 ≤ μ ∧
      BoozerGCOrbitOn reactorQA mα qα μ ψ θ φ ρ T ∧
      boozerEnergy reactorQA mα qα μ ψ θ φ ρ 0 = Eα ∧
      81 / 100 * (2 * Eα / mα) ≤ parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2 ∧
      ψ 0 ≤ psiStart ∧ ∀ t ∈ Icc 0 T, ψ t ≤ 8.2 := by
  have hps : 0 < psiStart := by norm_num [psiStart]
  obtain ⟨T, hT, ψ, θ, φ, ρ, hψ0, hθ0, hφ0, hρ0, h⟩ :=
    reactorQA_orbit_exists_local mα qα 0 (s₀ := (psiStart, 0, 0, alphaRho0)) hps
  simp only at hψ0 hθ0 hφ0 hρ0
  set T' := min T Tav with hT'
  have hT'0 : 0 < T' := lt_min hT (by norm_num [Tav])
  have h' := h.mono (min_le_left T Tav)
  have hB := (reactorQA_B_bounds (θ := 0) (φ := 0) hps (by norm_num [psiStart, psiEdge])).1
  have hBpos : 0 < reactorQA.B psiStart 0 0 := by linarith
  have hq : 0 < qα := by norm_num [qα]
  have hm := mα_pos
  have hEpos : 0 < Eα := by norm_num [Eα]
  have hsq : Real.sqrt (2 * mα * Eα) ^ 2 = 2 * mα * Eα := Real.sq_sqrt (by positivity)
  have hal : along reactorQA.B ψ θ φ 0 = reactorQA.B psiStart 0 0 := by
    simp only [along, hψ0, hθ0, hφ0]
  have hv2 : parallelVelocity reactorQA mα qα ψ θ φ ρ 0 ^ 2 = 2 * Eα / mα := by
    rw [parallelVelocity, hal, hρ0, alphaRho0]
    field_simp
    rw [hsq]
  have hE : boozerEnergy reactorQA mα qα 0 ψ θ φ ρ 0 = Eα := by
    rw [boozerEnergy_eq_parallel hm.ne', hv2]
    field_simp
    ring
  refine ⟨T', hT'0, min_le_right T Tav, 0, ψ, θ, φ, ρ, le_rfl, h', hE, ?_, hψ0.le, ?_⟩
  · rw [hv2]
    have : 0 ≤ 2 * Eα / mα := by positivity
    linarith
  · exact alpha_trapped_reactorQA_averaged_of_le (min_le_right T Tav) le_rfl h' hE
      (by rw [hv2]; have : 0 ≤ 2 * Eα / mα := by positivity
          linarith) hψ0.le

end PlasmaLean.Design.NearAxisQAExistence
