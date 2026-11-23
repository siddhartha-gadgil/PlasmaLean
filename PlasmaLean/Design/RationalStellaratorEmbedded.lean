/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorContract
public import PlasmaLean.Theory.Contract.IrrationalTorus

/-!
# Embedded current-free transform on the rational stellarator

The surface is the exact KAM solution near rational stellarator torus A. Its zero-current
witness and its embeddedness refer to the same profiles.
-/

public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorContract

open Real Set PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Forms
open PlasmaLean.Design.RationalStellarator PlasmaLean.Design.KamTorusA

/-- The rotation number of the exact rational stellarator torus is irrational. -/
theorem iota_irrational : Irrational iota := by
  simpa [iota] using ((PlasmaLean.Theory.KAM.irrational_sqrt_five.natCast_add 75).div_natCast
    (show (562 : ℕ) ≠ 0 by norm_num))

/-- Every exact torus in this KAM certificate is embedded. -/
theorem ExactTorus.embedded {R z : ℝ → ℝ → ℝ} (h : ExactTorus R z) : EmbeddedTorus R z := by
  apply (ExactTorus.fieldTorus h).embeddedTorus_of_irrational
    (ExactTorus.poloidalAngle h) iota_irrational h.smooth_R h.smooth_z
  intro θ φ
  have hv := field_vacuum (1 / 4)
  have hp := cylPoint_mem_domain ((ExactTorus.fieldTorus h).R_pos θ φ) φ (z θ φ)
  exact (hv.contDiffOn.contDiffAt (hv.isOpen.mem_nhds hp)).of_le (by norm_num)

/-- Embedded C1 on the individual exact witness, with its original transform bound. -/
theorem ExactTorus.embeddedCurrentFreeTransform {R z : ℝ → ℝ → ℝ} (h : ExactTorus R z)
    {μ₀ : ℝ} (hμ : 0 < μ₀) :
    EmbeddedCurrentFreeTransform μ₀ (field (1 / 4)) {exactSurface R z} 0 iota := by
  refine ⟨ExactTorus.currentFreeTransform h hμ, ?_⟩
  rintro s rfl
  exact ExactTorus.embedded h

/-- The rational stellarator realizes embedded C1 with zero current and positive transform. -/
theorem rationalStellarator_embeddedCurrentFreeTransform {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData, EmbeddedCurrentFreeTransform μ₀ (field (1 / 4)) S 0 iota := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := KamNewton.torusA_exact
  have h := KamNewton.exactTorus hu hz hur hzr hR hZ hC
  exact ⟨_, ExactTorus.embeddedCurrentFreeTransform h hμ⟩

end PlasmaLean.Design.RationalStellaratorContract
