/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormFluxSurfaceEmbedded

/-!
# Stellarator contract: the embeddedness clause of C1

Clause C1 (`Contract.CurrentFreeTransform`) describes each confining surface by a parametrised
torus `(θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ)` that is only continuous, and it does not say that the
surface is an embedded torus (audit item AF-1). A stellarator's flux surfaces are embedded tori:
that is what makes "inside the surface" meaningful. This file adds the missing clause.

* `EmbeddedSurfaces S`: every surface of the family is an `EmbeddedTorus` (`C²`, injective
  modulo the two periods, with injective differential; `Theory/Fields/FormFluxSurfaceEmbedded`).
* `EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin`: **clause C1 with embeddedness**,
  `CurrentFreeTransform` together with `EmbeddedSurfaces S`. This is the form of C1 that a
  stellarator candidate has to satisfy.
* Consequences for each surface: it is the image of a `C²` smooth embedding of the 2-torus, and
  a compact closed set (`EmbeddedCurrentFreeTransform.isSmoothEmbedding`, `isCompact_isClosed`).
* Proof obligations in usable form: `CurrentFreeTransform.embedded_of_sections` (for each
  surface: `C²` profiles, each cross-section `θ ↦ (R, z)` injective modulo `2π`, and
  `(∂_θ R, ∂_θ z) ≠ 0`), and `PoloidalAngle.sections_injective_of_strictMono` (a cross-section
  whose polar angle about the reference point is strictly increasing in `θ` is injective modulo
  `2π`, i.e. star-shaped sections are injective).

## Status and scope

* The clause is a separate predicate, and `CurrentFreeTransform` is unchanged, because none of
  the existing C1 instances (the rational stellarator and the Dommaschk candidates, whose tori
  come from a KAM argument) proves embeddedness yet. Proving `EmbeddedCurrentFreeTransform` for
  each of them is an open goal (plan question Q-36). Until then those instances establish C1
  without the embeddedness clause.
* `IotaOnTorus` already asks for a polar angle that winds once in `θ`, which excludes multiply
  covered sections; it does not exclude a section that crosses itself, nor a section that is
  not an immersed curve, and it asks only for continuity.
* Nothing here says that the surfaces of the family are nested or disjoint.
-/

@[expose] public section

namespace PlasmaLean.Contract

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Forms
open Real
open scoped Manifold

/-- The positivity of the period `2π`, needed for the circle `AddCircle (2π)`. -/
local instance factTwoPiPosC : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- **Embeddedness clause**: every surface of the family is an embedded torus. -/
def EmbeddedSurfaces (S : Set SurfaceData) : Prop := ∀ s ∈ S, EmbeddedTorus s.R s.z

/-- **Contract clause C1 with embeddedness**: clause C1 (`CurrentFreeTransform`) for a family of
surfaces each of which is an embedded torus. -/
structure EmbeddedCurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (S : Set SurfaceData)
    (Imax ιmin : ℝ) : Prop extends CurrentFreeTransform μ₀ B S Imax ιmin where
  /-- Each surface is an embedded torus. -/
  embedded : EmbeddedSurfaces S

variable {μ₀ : ℝ} {B : Space → Space} {S : Set SurfaceData} {Imax ιmin : ℝ}

/-- The embeddedness clause passes to a subfamily. -/
theorem EmbeddedSurfaces.mono {S' : Set SurfaceData} (h : EmbeddedSurfaces S) (hS : S' ⊆ S) :
    EmbeddedSurfaces S' := fun s hs => h s (hS hs)

/-- Clause C1 with embeddedness is monotone in the two allowances. -/
theorem EmbeddedCurrentFreeTransform.mono {Imax' ιmin' : ℝ}
    (h : EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin) (hI : Imax ≤ Imax') (hι : ιmin' ≤ ιmin)
    (hι' : 0 < ιmin') : EmbeddedCurrentFreeTransform μ₀ B S Imax' ιmin' :=
  { h.toCurrentFreeTransform.mono hI hι hι' with embedded := h.embedded }

/-- Each surface of clause C1 with embeddedness is the image of a `C²` smooth embedding of the
2-torus `AddCircle (2π) × AddCircle (2π)`. -/
theorem EmbeddedCurrentFreeTransform.isSmoothEmbedding
    (h : EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin) {s : SurfaceData} (hs : s ∈ S) :
    Manifold.IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2 (torusEmb s.R s.z) :=
  (h.embedded s hs).isSmoothEmbedding_torusEmb

/-- Each surface of clause C1 with embeddedness is a compact closed subset of space. -/
theorem EmbeddedCurrentFreeTransform.isCompact_isClosed
    (h : EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin) {s : SurfaceData} (hs : s ∈ S) :
    IsCompact (Set.range (torusMap s.R s.z)) ∧ IsClosed (Set.range (torusMap s.R s.z)) :=
  ⟨(h.embedded s hs).isCompact_isClosed_range.1, (h.embedded s hs).isCompact_isClosed_range.2.1⟩

/-- **The clause has content**: a family containing a surface that is not an embedded torus
does not satisfy clause C1 with embeddedness. -/
theorem not_embeddedCurrentFreeTransform_of_not_embedded {s : SurfaceData} (hs : s ∈ S)
    (hne : ¬ EmbeddedTorus s.R s.z) : ¬ EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin :=
  fun h => hne (h.embedded s hs)

/-- **Star-shaped sections are injective**: if the polar angle `Θ` of the cross-sections about
the reference curve is strictly increasing in `θ`, then each cross-section `θ ↦ (R, z)` is
injective modulo `2π`. -/
theorem PoloidalAngle.sections_injective_of_strictMono {R z : ℝ → ℝ → ℝ} {R₀ z₀ : ℝ → ℝ}
    {Θ : ℝ → ℝ → ℝ} (hΘ : PoloidalAngle R z R₀ z₀ Θ) (hmono : ∀ φ, StrictMono fun θ => Θ θ φ)
    (θ θ' φ : ℝ) (hR : R θ φ = R θ' φ) (hz : z θ φ = z θ' φ) :
    ∃ m : ℤ, θ' = θ + 2 * π * m := by
  obtain ⟨r, hr, h1, h2⟩ := hΘ.polar θ φ
  obtain ⟨r', hr', h1', h2'⟩ := hΘ.polar θ' φ
  have e1 : r * cos (Θ θ φ) = r' * cos (Θ θ' φ) := by rw [← h1, ← h1', hR]
  have e2 : r * sin (Θ θ φ) = r' * sin (Θ θ' φ) := by rw [← h2, ← h2', hz]
  have hsq : r ^ 2 = r' ^ 2 := by
    have a1 : r ^ 2 = (r * cos (Θ θ φ)) ^ 2 + (r * sin (Θ θ φ)) ^ 2 := by
      nlinarith [sin_sq_add_cos_sq (Θ θ φ)]
    have a2 : r' ^ 2 = (r' * cos (Θ θ' φ)) ^ 2 + (r' * sin (Θ θ' φ)) ^ 2 := by
      nlinarith [sin_sq_add_cos_sq (Θ θ' φ)]
    rw [a1, a2, e1, e2]
  have hrr : r = r' := by nlinarith
  subst hrr
  obtain ⟨m, hm⟩ := exists_int_of_cos_sin_eq (mul_left_cancel₀ hr.ne' e1)
    (mul_left_cancel₀ hr.ne' e2)
  have hw : ∀ k : ℤ, Θ (θ + 2 * π * k) φ = Θ θ φ + 2 * π * k := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have := hΘ.wind_θ (θ + 2 * π * n) φ
      push_cast at ih ⊢
      rw [show θ + 2 * π * ((n : ℝ) + 1) = θ + 2 * π * n + 2 * π by ring, this, ih]
      ring
    | pred n ih =>
      have := hΘ.wind_θ (θ + 2 * π * (-(n : ℝ) - 1)) φ
      push_cast at ih ⊢
      rw [show θ + 2 * π * (-(n : ℝ) - 1) + 2 * π = θ + 2 * π * -(n : ℝ) by ring, ih] at this
      linarith
  refine ⟨m, (hmono φ).injective ?_⟩
  rw [hw m, hm]

/-- **Proof obligation for the embeddedness clause, by sections**: clause C1 together with, for
each surface, `C²` profiles, cross-sections that are injective modulo `2π`, and a non-vanishing
tangent `(∂_θ R, ∂_θ z)`, gives clause C1 with embeddedness. -/
theorem CurrentFreeTransform.embedded_of_sections (hC : CurrentFreeTransform μ₀ B S Imax ιmin)
    (hR : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.R p.1 p.2))
    (hz : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.z p.1 p.2))
    (hinj : ∀ s ∈ S, ∀ θ θ' φ, s.R θ φ = s.R θ' φ → s.z θ φ = s.z θ' φ →
      ∃ m : ℤ, θ' = θ + 2 * π * m)
    (himm : ∀ s ∈ S, ∀ θ φ,
      ¬ (deriv (fun t => s.R t φ) θ = 0 ∧ deriv (fun t => s.z t φ) θ = 0)) :
    EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin :=
  { hC with
    embedded := fun s hs =>
      (hC.torus s hs).1.embeddedTorus (hR s hs) (hz s hs) (hinj s hs) (himm s hs) }

/-- **Proof obligation for the embeddedness clause, by a monotone polar angle**: clause C1
together with, for each surface, `C²` profiles, a poloidal angle that is strictly increasing in
`θ`, and a non-vanishing tangent `(∂_θ R, ∂_θ z)`, gives clause C1 with embeddedness. -/
theorem CurrentFreeTransform.embedded_of_strictMono (hC : CurrentFreeTransform μ₀ B S Imax ιmin)
    (hR : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.R p.1 p.2))
    (hz : ∀ s ∈ S, ContDiff ℝ 2 (fun p : ℝ × ℝ => s.z p.1 p.2))
    (hΘ : ∀ s ∈ S, ∃ R₀ z₀ : ℝ → ℝ, ∃ Θ : ℝ → ℝ → ℝ, PoloidalAngle s.R s.z R₀ z₀ Θ ∧
      ∀ φ, StrictMono fun θ => Θ θ φ)
    (himm : ∀ s ∈ S, ∀ θ φ,
      ¬ (deriv (fun t => s.R t φ) θ = 0 ∧ deriv (fun t => s.z t φ) θ = 0)) :
    EmbeddedCurrentFreeTransform μ₀ B S Imax ιmin :=
  hC.embedded_of_sections hR hz
    (fun s hs θ θ' φ h1 h2 => by
      obtain ⟨R₀, z₀, Θ, hP, hm⟩ := hΘ s hs
      exact hP.sections_injective_of_strictMono hm θ θ' φ h1 h2)
    himm

end PlasmaLean.Contract
