/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.VacuumTolerance
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A positive axial probe field is not confinement

For field-line parametrization γ'=B(γ), an axial component bounded below forces
escape from a bounded axial slab. The parameter is NOT particle time (in SI it has
units m/T). No trajectory existence is postulated or proved: the theorem bounds
the length of any supplied classical trajectory that remains in the probe ball.
It rules out misreading the nonvanishing-field certificate as all-time confinement.
-/
public section
noncomputable section
namespace PlasmaLean.Sanity
open Fields Design.VacuumPair

/-- A uniformly increasing scalar observable cannot remain in a bounded interval
longer than its width divided by the derivative lower bound. -/
theorem bounded_observable_duration {z dz : ℝ → ℝ} {T k r : ℝ} (hT : 0 ≤ T)
    (hd : ∀ s ∈ Set.Icc 0 T, HasDerivAt z (dz s) s)
    (hb : ∀ s ∈ Set.Icc 0 T, k ≤ dz s)
    (h0 : |z 0| ≤ r) (h1 : |z T| ≤ r) : k * T ≤ 2 * r := by
  have hc : ContinuousOn z (Set.Icc 0 T) := fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ z (interior (Set.Icc 0 T)) :=
    fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  have hder : ∀ s ∈ interior (Set.Icc 0 T), k ≤ deriv z s := by
    intro s hs
    rw [(hd s (interior_subset hs)).deriv]
    exact hb s (interior_subset hs)
  have h := (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv hc hdiff hder
    0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩ hT
  have hzero := (abs_le.mp h0).1
  have hlast := (abs_le.mp h1).2
  simp only [sub_zero] at h
  linarith

/-- Under the compiled tolerance budget, a field line staying in the 1 mm ball
must satisfy T μ₀ I ≤ 1/125. This is an upper residence-parameter bound, not a
physical particle residence time or an invariant surface certificate. -/
theorem probe_fieldLine_duration {μ₀ I J₁ J₂ T : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100)
    (γ : ℝ → Space) (hT : 0 ≤ T)
    (hγ : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt γ (manufacturedField μ₀ J₁ J₂ upper lower (γ s)) s)
    (stays : ∀ s ∈ Set.Icc 0 T, ‖γ s‖ ≤ 1 / 1000) : T * (μ₀ * I) ≤ 1 / 125 := by
  have hd : ∀ s ∈ Set.Icc 0 T, HasDerivAt (fun t => γ t 2)
      ((manufacturedField μ₀ J₁ J₂ upper lower (γ s)) 2) s := by
    intro s hs
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).hasFDerivAt.comp_hasDerivAt s (hγ s hs)
  have hz (s : ℝ) (hs : s ∈ Set.Icc 0 T) : |γ s 2| ≤ 1 / 1000 := by
    have hn : |γ s 2| ≤ ‖γ s‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (γ s) 2
    exact hn.trans (stays s hs)
  have h := bounded_observable_duration hT hd
    (fun s hs => (robust_probe_field hμ hI upper lower hu hl hJ₁ hJ₂ (γ s) (stays s hs)).1)
    (hz 0 ⟨le_rfl, hT⟩) (hz T ⟨hT, le_rfl⟩)
  nlinarith

/-- No global forward classical field line can stay in this probe ball forever
under the same positive-current tolerance assumptions. This rules out only this
ball as an all-time field-line trap, not other regions or particle dynamics. -/
theorem no_forever_probe_fieldLine {μ₀ I J₁ J₂ : ℝ} (hμ : 0 < μ₀) (hI : 0 < I)
    (upper lower : ℝ → Space) (hu : WithinTolerance upperCoil upper)
    (hl : WithinTolerance lowerCoil lower)
    (hJ₁ : |J₁ - I| ≤ I / 100) (hJ₂ : |J₂ - I| ≤ I / 100) :
    ¬ ∃ γ : ℝ → Space, (∀ s, 0 ≤ s →
      HasDerivAt γ (manufacturedField μ₀ J₁ J₂ upper lower (γ s)) s) ∧
      (∀ s, 0 ≤ s → ‖γ s‖ ≤ 1 / 1000) := by
  rintro ⟨γ, hd, hb⟩
  have hp : 0 < μ₀ * I := mul_pos hμ hI
  have h := probe_fieldLine_duration hμ hI upper lower hu hl hJ₁ hJ₂ γ
    (T := (μ₀ * I)⁻¹) (by positivity) (fun s hs => hd s hs.1) (fun s hs => hb s hs.1)
  rw [inv_mul_cancel₀ hp.ne'] at h
  norm_num at h

end PlasmaLean.Sanity
