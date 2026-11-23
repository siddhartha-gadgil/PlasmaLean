/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.IrrationalSection
public import PlasmaLean.Theory.Contract.SectionFlow
public import PlasmaLean.Theory.Contract.EmbeddedSurfaces

/-!
# Embedded invariant tori from winding and irrational transform

A turn in geometric toroidal angle propagates both coincidences and stationary tangents.
An irrational rotation propagates each to an entire poloidal section. Degree one of the
poloidal angle rules out a nontrivial period and a constant section.
-/

public section
noncomputable section

namespace PlasmaLean.Contract

open PlasmaLean.Fields PlasmaLean.Forms

variable {B : Space → Space} {R z Θ : ℝ → ℝ → ℝ} {ι : ℝ}

/-- A winding-one invariant torus with irrational transform and smooth profiles is embedded
if the magnetic field is locally C¹ at the image of the torus. -/
theorem FieldTorus.embeddedTorus_of_irrational (hT : FieldTorus B R z ι)
    {R₀ z₀ : ℝ → ℝ} (hP : PoloidalAngle R z R₀ z₀ Θ) (hι : Irrational ι)
    (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2))
    (hB : ∀ θ φ, ContDiffAt ℝ 1 B (cylPoint (R θ φ) φ (z θ φ))) : EmbeddedTorus R z := by
  obtain ⟨points, tangents⟩ := hT.section_return hR hz hB
  exact hT.embeddedTorus hR hz (hP.sections_injective_of_irrational_return hι hT points)
    (hP.sections_immersed_of_irrational_return hι hT hR hz tangents)

/-- A family with the current and transform bounds satisfies embedded C1 whenever every
transform is irrational, the profiles are C² and the field is locally C¹ on the images. -/
theorem CurrentFreeTransform.embedded_of_irrational {μ₀ Imax ιmin : ℝ} {S : Set SurfaceData}
    (h : CurrentFreeTransform μ₀ B S Imax ιmin)
    (hι : ∀ s ∈ S, Irrational s.iota)
    (hR : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.R p.1 p.2))
    (hz : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.z p.1 p.2))
    (hB : ∀ s ∈ S, ∀ θ φ, ContDiffAt ℝ 1 B (cylPoint (s.R θ φ) φ (s.z θ φ))) :
    EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin := by
  refine ⟨h, fun s hs => ?_⟩
  obtain ⟨hT, _, _, _, hP⟩ := h.torus s hs
  exact hT.embeddedTorus_of_irrational hP (hι s hs) (hR s hs) (hz s hs) (hB s hs)

end PlasmaLean.Contract
