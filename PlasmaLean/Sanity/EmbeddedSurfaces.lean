/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.EmbeddedSurfaces
public import PlasmaLean.Sanity.FormFluxSurfaceEmbedded

/-!
# Sanity checks for the embeddedness clause of C1 (`Theory/Contract/EmbeddedSurfaces`)

* Accepted: a family consisting of circular tori satisfies `EmbeddedSurfaces`
  (`circ_embeddedSurfaces`).
* Rejected: a family containing the doubly covered torus does not (`dbl_not_embeddedSurfaces`),
  and no field satisfies clause C1 with embeddedness on such a family
  (`dbl_not_embeddedCurrentFreeTransform`); likewise for the torus collapsed to a circle
  (`circle_not_embeddedCurrentFreeTransform`).
* Degenerate: the empty family satisfies `EmbeddedSurfaces` but not the contract clause, which
  needs a surface (`empty_embeddedSurfaces`, `empty_not_embeddedCurrentFreeTransform`).

Not exhibited: an instance of `EmbeddedCurrentFreeTransform` with a non-zero rotational
transform. The library's C1 instances are KAM tori for which embeddedness is not yet proved
(plan question Q-36).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.EmbeddedSurfaces

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Forms
open PlasmaLean.Design.RationalStellaratorContract
open PlasmaLean.Sanity.FormFluxSurfaceEmbedded

/-- **Accepted**: circular tori with `0 < a < 1` form a family of embedded surfaces, for any
recorded transform and loop angle. -/
theorem circ_embeddedSurfaces {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (ι φ₀ : ℝ) :
    EmbeddedSurfaces {(⟨circR a, circZ a, ι, φ₀⟩ : SurfaceData)} := by
  intro s hs
  rw [Set.mem_singleton_iff.1 hs]
  exact circ_embeddedTorus ha ha1

/-- **Rejected**: a family containing the doubly covered torus is not a family of embedded
surfaces. -/
theorem dbl_not_embeddedSurfaces (a ι φ₀ : ℝ) :
    ¬ EmbeddedSurfaces {(⟨dblR a, dblZ a, ι, φ₀⟩ : SurfaceData)} :=
  fun h => dbl_not_embeddedTorus a (h _ rfl)

/-- **Rejected**: no field satisfies clause C1 with embeddedness on a family containing the
doubly covered torus. -/
theorem dbl_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (a ι φ₀ Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B {(⟨dblR a, dblZ a, ι, φ₀⟩ : SurfaceData)} Imax ιmin :=
  not_embeddedCurrentFreeTransform_of_not_embedded (s := ⟨dblR a, dblZ a, ι, φ₀⟩) rfl
    (dbl_not_embeddedTorus a)

/-- **Rejected**: no field satisfies clause C1 with embeddedness on a family containing the
torus collapsed to a circle. -/
theorem circle_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space)
    (ι φ₀ Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B {(⟨circR 0, circZ 0, ι, φ₀⟩ : SurfaceData)} Imax ιmin :=
  not_embeddedCurrentFreeTransform_of_not_embedded (s := ⟨circR 0, circZ 0, ι, φ₀⟩) rfl
    circle_not_embeddedTorus

/-- **Degenerate**: the empty family satisfies the embeddedness clause vacuously. -/
theorem empty_embeddedSurfaces : EmbeddedSurfaces ∅ := fun _ hs => absurd hs (Set.notMem_empty _)

/-- **Degenerate**: the empty family does not satisfy clause C1 with embeddedness, because
clause C1 needs at least one surface. -/
theorem empty_not_embeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (Imax ιmin : ℝ) :
    ¬ EmbeddedCurrentFreeTransform μ₀ B ∅ Imax ιmin :=
  fun h => Set.not_nonempty_empty h.nonempty

end PlasmaLean.Sanity.EmbeddedSurfaces
