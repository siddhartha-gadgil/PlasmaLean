/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMCircle
public import PlasmaLean.Theory.Fields.FormCalculus
public import TauCeti.Analysis.Calculus.DifferentialForm.Integral
public import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Yang–Mills energy of the anti-self-dual lift: pointwise bound, minimality, local connection

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, paragraphs
"Integral periods and the holomorphic line bundle" (line 45: "Locally write `α = dΦ_i` and set
`A_i = a - Φ_i dt`. Then `dA_i = ℱ`.") and "A positive auxiliary energy and its exact scope"
(lines 54–59: "If `a₁` is a real one-form whose tangential trace on `∂M` vanishes, then
`d*ℱ = 0` and integration by parts give `∫_M |ℱ + da₁|² - ∫_M |ℱ|² = ∫_M |da₁|² ≥ 0`. Thus the
lift minimizes the Abelian Yang–Mills energy against these fixed-boundary connection
variations."). Assessment claim S-13 in `notes/theory/fusion-complex-geometry-assessment.md`.
This file continues `Theory/Fields/FormHYMLift`, `FormHYMStar` and `FormHYMCircle`.

TauCeti v4.36.0 has no construction of a line bundle from a closed 2-form, no first Chern
class and no Yang–Mills functional on connections. This file formalizes the parts of the claim
that do not need a bundle: an Abelian connection on a trivial bundle is a 1-form `A`, its
curvature is `dA`, and a variation of the connection is a 1-form `a`.

## Conventions

* Space `ℝ³ × ℝ` (`LiftSpace`), product Euclidean metric, orientation `dx₀ ∧ dx₁ ∧ dx₂ ∧ dτ`,
  star `liftStar`, inner product `liftInner` (the six coordinate 2-forms are orthonormal),
  wedge product TauCeti's `ContinuousAlternatingMap.wedge`.
* Integrals are Bochner integrals for Lebesgue measure `volume` on `ℝ³ × ℝ`, the product of
  the Lebesgue measures of `ℝ³` and `ℝ`. It is the Haar measure of the standard basis
  (`liftBasis_addHaar`), which is how TauCeti's integration theorem is applied.
* The energy density is `|F|² = liftInner F F`; the Yang–Mills density is `ymDensity F = ½|F|²`.

## What is proved

**A. Pointwise algebra** (no analysis).
* `liftInner` is a symmetric, positive definite bilinear form and the star is a self-adjoint
  isometry (`liftInner_comm`, `liftInner_add_left`, `liftInner_smul_left`,
  `liftInner_self_eq_zero`, `liftInner_liftStar_liftStar`, `liftInner_liftStar_right`).
* `sdPart F = (F + ⋆F)/2`, `asdPart F = (F - ⋆F)/2`; `|F|² = |F⁺|² + |F⁻|²`
  (`liftInner_self_eq_sdPart_add_asdPart`).
* `wedgeDensity F = ⟨F, ⋆F⟩` with `F ∧ F = wedgeDensity F · vol` (`wedge_self_apply`) and
  `wedgeDensity F = |F⁺|² - |F⁻|²` (`wedgeDensity_eq_sdPart_sub_asdPart`). The sign: with the
  convention `F ∧ ⋆G = ⟨F, G⟩ vol` of `wedge_liftStar_apply`, self-dual forms have
  `F ∧ F = +|F|² vol` and anti-self-dual forms `F ∧ F = -|F|² vol`.
* The Bogomolny identities `|F|² = -⟨F, ⋆F⟩ + 2|F⁺|² = ⟨F, ⋆F⟩ + 2|F⁻|²`, the bounds
  `|F|² ≥ -⟨F, ⋆F⟩` and `|F|² ≥ ⟨F, ⋆F⟩`, and the equality cases: equality in the first
  exactly for `⋆F = -F`, in the second exactly for `⋆F = F`
  (`liftInner_self_eq_neg_wedgeDensity_iff`, `liftInner_self_eq_wedgeDensity_iff`).

**C. Local connection.**
* `liftConnection A φ = π^*A - (π^*φ) dτ` and `extDeriv_liftConnection`:
  `d(π^*A - (π^*φ) dτ) = π^*(dA) - π^*(dφ) ∧ dτ`. The sign of the scalar term is `-`, as in the
  source.
* `VacuumForm.exists_liftConnection`: on an open star-convex region `Ω` the lift of a vacuum
  form is `d𝒜` for such a `τ`-independent `𝒜` on `Ω × ℝ`, with `A` and `φ` of class `C²`
  (TauCeti's Poincaré lemma, through `VacuumForm.exists_vectorPotential` and
  `VacuumForm.exists_scalarPotential`).

**B. Energy minimality.** Let `G` be a field of 2-forms that is `C¹` and co-closed,
`d(⋆G) = 0`, on an open set `U ⊆ ℝ³ × ℝ`, and `a` a `C¹` field of 1-forms on `ℝ³ × ℝ` whose
closed support is compact and contained in `U`.
* `integral_liftInner_extDeriv_eq_zero`: `∫ ⟨G, da⟩ = 0` (the cross term). Proof:
  `⟨G, da⟩ vol = ⋆G ∧ da = d(⋆G ∧ a)` (`extDeriv_starWedge_apply`, TauCeti's Leibniz rule) and
  `Module.Basis.integral_extDeriv_eq_zero`.
* `integral_energy_perturbation`: `∫ (|G + da|² - |G|²) = ∫ |da|²`;
  `integral_energy_perturbation_nonneg`: this is `≥ 0`;
  `integral_energy_perturbation_eq_zero_iff`: it is `0` exactly when `da = 0` everywhere.
* Closed anti-self-dual and closed self-dual fields are co-closed
  (`extDeriv_liftStar_eq_zero_of_antiSelfDual`, `extDeriv_liftStar_eq_zero_of_selfDual`).
* For the lift `ℱ = hymLift ω` of a vacuum form `ω` on an open `Ω` and `a` with compact support
  in `Ω × ℝ`: `VacuumForm.integral_energy_hymLift_perturbation` and its companions `_nonneg`,
  `_eq_zero_iff`, and `VacuumField.integral_ymDensity_hymLift_perturbation` in vector language.

**Integrability.** The energies `∫ |G|²` and `∫ |G + da|²` are not written separately: the lift
does not depend on `τ`, so it is not integrable over `ℝ³ × ℝ` unless it vanishes, and a Bochner
integral of a non-integrable function is `0` in Lean. The statements integrate the difference
`|G + da|² - |G|²`, which vanishes outside the support of `a`. Every integrand that occurs is
proved integrable (`integrable_liftInner_extDeriv`, `integrable_liftInner_extDeriv_self`,
`integrable_energy_perturbation`), so no statement here is true by a junk value.

## Relation to the source and what is not formalized

* The source perturbs on `M = Ω × S¹` by 1-forms with vanishing tangential trace on `∂M`. Here
  the perturbation has compact support in `Ω × ℝ`. This is a smaller class in two ways (support
  away from `∂Ω`, and compact in `τ` rather than periodic), and the identity is on the cover
  `Ω × ℝ`, not on the quotient. The periodic statement on `Ω × S¹` (integration over the circle
  factor, perturbations that are `τ`-periodic) is not proved in this file; it is in
  `Theory/Fields/FormHYMCircleEnergy` (for variations vanishing near `∂Ω`).
* "Minimises the Yang–Mills energy" is proved only in this sense: among connections `A + a`
  with `a` compactly supported, on the trivial bundle. No functional on a space of connections
  of a bundle is defined.
* The connection of part C is a connection on the TRIVIAL bundle over a star-convex region. On
  a region with non-trivial topology (a solid torus times the circle) the scalar potential is
  multivalued and the bundle of the source may be non-trivial. The line bundle, the unitary
  transition functions `exp(2πi n t)`, the Chern class `c₁ = [ℱ/2π]`, the integrality of the
  periods, the holomorphic structure and the comparison with the algebraic Picard group are NOT
  formalized.
* The integrated form of part A (`∫ |F|² ≥ |∫ F ∧ F|`, the topological lower bound) is not
  stated: on the non-compact `ℝ³ × ℝ` neither side is finite for the lift.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields Matrix Module
open scoped RealInnerProductSpace

/-! ## Algebra of the inner product of 2-forms -/

/-- The inner product of 2-forms on `ℝ³ × ℝ` is symmetric. -/
theorem liftInner_comm (F G : LiftForm 2) : liftInner F G = liftInner G F := by
  rw [liftInner_eq, liftInner_eq]
  ring

/-- The inner product is additive in its first argument. -/
theorem liftInner_add_left (F F' G : LiftForm 2) :
    liftInner (F + F') G = liftInner F G + liftInner F' G := by
  simp only [liftInner_eq, ContinuousAlternatingMap.add_apply]
  ring

/-- The inner product is homogeneous in its first argument. -/
theorem liftInner_smul_left (c : ℝ) (F G : LiftForm 2) :
    liftInner (c • F) G = c * liftInner F G := by
  simp only [liftInner_eq, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

/-- The inner product is additive in its second argument. -/
theorem liftInner_add_right (F G G' : LiftForm 2) :
    liftInner F (G + G') = liftInner F G + liftInner F G' := by
  rw [liftInner_comm, liftInner_add_left, liftInner_comm G, liftInner_comm G']

/-- The inner product is homogeneous in its second argument. -/
theorem liftInner_smul_right (c : ℝ) (F G : LiftForm 2) :
    liftInner F (c • G) = c * liftInner F G := by
  rw [liftInner_comm, liftInner_smul_left, liftInner_comm]

/-- The inner product with a negative in the first argument. -/
theorem liftInner_neg_left (F G : LiftForm 2) : liftInner (-F) G = -liftInner F G := by
  rw [← neg_one_smul ℝ F, liftInner_smul_left]
  ring

/-- The inner product with a negative in the second argument. -/
theorem liftInner_neg_right (F G : LiftForm 2) : liftInner F (-G) = -liftInner F G := by
  rw [liftInner_comm, liftInner_neg_left, liftInner_comm]

/-- The inner product with the zero form on the left. -/
@[simp] theorem liftInner_zero_left (G : LiftForm 2) : liftInner 0 G = 0 := by
  have h := liftInner_smul_left 0 0 G
  rwa [zero_smul, zero_mul] at h

/-- The inner product with the zero form on the right. -/
@[simp] theorem liftInner_zero_right (F : LiftForm 2) : liftInner F 0 = 0 := by
  rw [liftInner_comm, liftInner_zero_left]

/-- **The star is an isometry**: `⟨⋆F, ⋆G⟩ = ⟨F, G⟩`. -/
theorem liftInner_liftStar_liftStar (F G : LiftForm 2) :
    liftInner (liftStar F) (liftStar G) = liftInner F G := by
  obtain ⟨m0, m1, m2⟩ := liftStar_apply_mixed F
  obtain ⟨s0, s1, s2⟩ := liftStar_apply_spatial F
  obtain ⟨n0, n1, n2⟩ := liftStar_apply_mixed G
  obtain ⟨t0, t1, t2⟩ := liftStar_apply_spatial G
  rw [liftInner_eq, liftInner_eq, m0, m1, m2, s0, s1, s2, n0, n1, n2, t0, t1, t2]
  ring

/-- **The star is self-adjoint**: `⟨F, ⋆G⟩ = ⟨⋆F, G⟩`. -/
theorem liftInner_liftStar_right (F G : LiftForm 2) :
    liftInner F (liftStar G) = liftInner (liftStar F) G := by
  have h := liftInner_liftStar_liftStar (liftStar F) G
  rwa [liftStar_liftStar] at h

/-- The squared norm of a 2-form is non-negative. -/
theorem liftInner_self_nonneg (F : LiftForm 2) : 0 ≤ liftInner F F := by
  rw [liftInner_eq]
  have h1 := mul_self_nonneg (F ![(coordVec 1, 0), (coordVec 2, 0)])
  have h2 := mul_self_nonneg (F ![(coordVec 2, 0), (coordVec 0, 0)])
  have h3 := mul_self_nonneg (F ![(coordVec 0, 0), (coordVec 1, 0)])
  have h4 := mul_self_nonneg (F ![(coordVec 0, 0), (0, 1)])
  have h5 := mul_self_nonneg (F ![(coordVec 1, 0), (0, 1)])
  have h6 := mul_self_nonneg (F ![(coordVec 2, 0), (0, 1)])
  linarith

/-- **The inner product is positive definite**: `⟨F, F⟩ = 0` only for `F = 0`. -/
theorem liftInner_self_eq_zero {F : LiftForm 2} : liftInner F F = 0 ↔ F = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, liftInner_zero_left]⟩
  rw [liftInner_eq] at h
  have h1 := mul_self_nonneg (F ![(coordVec 1, 0), (coordVec 2, 0)])
  have h2 := mul_self_nonneg (F ![(coordVec 2, 0), (coordVec 0, 0)])
  have h3 := mul_self_nonneg (F ![(coordVec 0, 0), (coordVec 1, 0)])
  have h4 := mul_self_nonneg (F ![(coordVec 0, 0), (0, 1)])
  have h5 := mul_self_nonneg (F ![(coordVec 1, 0), (0, 1)])
  have h6 := mul_self_nonneg (F ![(coordVec 2, 0), (0, 1)])
  obtain ⟨k0, k1, k2⟩ := hodge_apply_coordVec (spatialPart F)
  rw [spatialPart_apply] at k0 k1 k2
  have hs : hodge (spatialPart F) = 0 := by
    apply form1_ext_coord
    · rw [k0]; exact mul_self_eq_zero.1 (by linarith)
    · rw [k1]; exact mul_self_eq_zero.1 (by linarith)
    · rw [k2]; exact mul_self_eq_zero.1 (by linarith)
  have hm : mixedPart F = 0 := by
    apply form1_ext_coord <;> rw [mixedPart_apply] <;> exact mul_self_eq_zero.1 (by linarith)
  have hs' : spatialPart F = 0 := hodge.injective (hs.trans (map_zero hodge).symm)
  rw [← ofParts_parts F, hs', hm]
  apply liftForm2_ext
  intro u v s t
  rw [ofParts_apply]
  simp

/-! ## Self-dual and anti-self-dual parts, and the Bogomolny identity -/

/-- **The self-dual part** `F⁺ = (F + ⋆F)/2` of a 2-form on `ℝ³ × ℝ`. -/
noncomputable def sdPart (F : LiftForm 2) : LiftForm 2 := (1 / 2 : ℝ) • (F + liftStar F)

/-- **The anti-self-dual part** `F⁻ = (F - ⋆F)/2` of a 2-form on `ℝ³ × ℝ`. -/
noncomputable def asdPart (F : LiftForm 2) : LiftForm 2 := (1 / 2 : ℝ) • (F - liftStar F)

/-- The self-dual part is self-dual. -/
theorem liftStar_sdPart (F : LiftForm 2) : liftStar (sdPart F) = sdPart F := by
  rw [sdPart, map_smul, map_add, liftStar_liftStar, add_comm]

/-- The anti-self-dual part is anti-self-dual. -/
theorem liftStar_asdPart (F : LiftForm 2) : liftStar (asdPart F) = -asdPart F := by
  rw [asdPart, map_smul, map_sub, liftStar_liftStar, ← smul_neg, neg_sub]

/-- The self-dual part lies in the `+1` eigenspace of the star. -/
theorem sdPart_mem_selfDualForms (F : LiftForm 2) : sdPart F ∈ selfDualForms :=
  mem_selfDualForms.2 (liftStar_sdPart F)

/-- The anti-self-dual part lies in the `-1` eigenspace of the star. -/
theorem asdPart_mem_antiSelfDualForms (F : LiftForm 2) : asdPart F ∈ antiSelfDualForms :=
  mem_antiSelfDualForms.2 (liftStar_asdPart F)

/-- **`F = F⁺ + F⁻`.** -/
theorem sdPart_add_asdPart (F : LiftForm 2) : sdPart F + asdPart F = F := by
  rw [sdPart, asdPart, ← smul_add, add_add_sub_cancel, ← two_smul ℝ F, smul_smul]
  norm_num

/-- **`⋆F = F⁺ - F⁻`.** -/
theorem sdPart_sub_asdPart (F : LiftForm 2) : sdPart F - asdPart F = liftStar F := by
  rw [sdPart, asdPart, ← smul_sub, add_sub_sub_cancel, ← two_smul ℝ (liftStar F), smul_smul]
  norm_num

/-- The self-dual part vanishes exactly for anti-self-dual forms. -/
theorem sdPart_eq_zero_iff (F : LiftForm 2) : sdPart F = 0 ↔ liftStar F = -F := by
  rw [sdPart, smul_eq_zero, add_eq_zero_iff_neg_eq, eq_comm (a := -F)]
  norm_num

/-- The anti-self-dual part vanishes exactly for self-dual forms. -/
theorem asdPart_eq_zero_iff (F : LiftForm 2) : asdPart F = 0 ↔ liftStar F = F := by
  rw [asdPart, smul_eq_zero, sub_eq_zero, eq_comm (a := F)]
  norm_num

/-- The self-dual part of the lift of the source vanishes. -/
theorem sdPart_hymLiftAt (b : Form 2) : sdPart (hymLiftAt b) = 0 :=
  (sdPart_eq_zero_iff _).2 (liftStar_hymLiftAt b)

/-- **Self-dual and anti-self-dual forms are orthogonal**, proved from the isometry property
of the star (an independent proof by components is `liftInner_eq_zero_of_liftStar` in
`Theory/Fields/FormHYMComplex`). -/
theorem liftInner_eq_zero_of_selfDual_antiSelfDual {F G : LiftForm 2} (hF : liftStar F = F)
    (hG : liftStar G = -G) : liftInner F G = 0 := by
  have h := liftInner_liftStar_liftStar F G
  rw [hF, hG, liftInner_neg_right] at h
  linarith

/-- `⟨F⁺, F⁻⟩ = 0`. -/
theorem liftInner_sdPart_asdPart (F : LiftForm 2) : liftInner (sdPart F) (asdPart F) = 0 :=
  liftInner_eq_zero_of_selfDual_antiSelfDual (liftStar_sdPart F) (liftStar_asdPart F)

/-- **The wedge density** of a 2-form: the number `q(F) = ⟨F, ⋆F⟩`, for which
`F ∧ F = q(F) vol` (`wedge_self_apply`). It is the density of the topological term
(`F ∧ F` is closed for closed `F`); its sign depends on the orientation. -/
noncomputable def wedgeDensity (F : LiftForm 2) : ℝ := liftInner F (liftStar F)

/-- **`F ∧ F = ⟨F, ⋆F⟩ vol`**, with TauCeti's wedge product. -/
theorem wedge_self_apply (F : LiftForm 2) (v : Fin (2 + 2) → LiftSpace) :
    (ContinuousAlternatingMap.wedge F F) v = wedgeDensity F * liftVol v := by
  have h := wedge_liftStar_apply F (liftStar F) v
  rwa [liftStar_liftStar] at h

/-- **Pythagoras for the star**: `|F|² = |F⁺|² + |F⁻|²`. -/
theorem liftInner_self_eq_sdPart_add_asdPart (F : LiftForm 2) :
    liftInner F F = liftInner (sdPart F) (sdPart F) + liftInner (asdPart F) (asdPart F) := by
  have h := liftInner_sdPart_asdPart F
  have h' : liftInner (asdPart F) (sdPart F) = 0 := by rw [liftInner_comm, h]
  conv_lhs => rw [← sdPart_add_asdPart F]
  rw [liftInner_add_left, liftInner_add_right, liftInner_add_right, h, h']
  ring

/-- **The wedge density is the difference of the two parts**: `⟨F, ⋆F⟩ = |F⁺|² - |F⁻|²`, so
`F ∧ F = (|F⁺|² - |F⁻|²) vol`. -/
theorem wedgeDensity_eq_sdPart_sub_asdPart (F : LiftForm 2) :
    wedgeDensity F = liftInner (sdPart F) (sdPart F) - liftInner (asdPart F) (asdPart F) := by
  have h := liftInner_sdPart_asdPart F
  have h' : liftInner (asdPart F) (sdPart F) = 0 := by rw [liftInner_comm, h]
  have e : wedgeDensity F = liftInner (sdPart F + asdPart F) (sdPart F - asdPart F) := by
    rw [sdPart_add_asdPart, sdPart_sub_asdPart, wedgeDensity]
  rw [e, sub_eq_add_neg, liftInner_add_left, liftInner_add_right, liftInner_add_right,
    liftInner_neg_right, liftInner_neg_right, h, h']
  ring

/-- **Bogomolny identity, anti-self-dual side**: `|F|² = -⟨F, ⋆F⟩ + 2 |F⁺|²`. -/
theorem liftInner_self_eq_neg_wedgeDensity_add (F : LiftForm 2) :
    liftInner F F = -wedgeDensity F + 2 * liftInner (sdPart F) (sdPart F) := by
  rw [liftInner_self_eq_sdPart_add_asdPart, wedgeDensity_eq_sdPart_sub_asdPart]
  ring

/-- **Bogomolny identity, self-dual side**: `|F|² = ⟨F, ⋆F⟩ + 2 |F⁻|²`. -/
theorem liftInner_self_eq_wedgeDensity_add (F : LiftForm 2) :
    liftInner F F = wedgeDensity F + 2 * liftInner (asdPart F) (asdPart F) := by
  rw [liftInner_self_eq_sdPart_add_asdPart, wedgeDensity_eq_sdPart_sub_asdPart]
  ring

/-- **Pointwise topological bound, anti-self-dual side**: `|F|² ≥ -⟨F, ⋆F⟩`, that is
`|F|² vol ≥ -F ∧ F`. -/
theorem neg_wedgeDensity_le_liftInner_self (F : LiftForm 2) :
    -wedgeDensity F ≤ liftInner F F := by
  have h := liftInner_self_nonneg (sdPart F)
  rw [liftInner_self_eq_neg_wedgeDensity_add]
  linarith

/-- **Equality in the bound holds exactly for anti-self-dual forms**:
`|F|² = -⟨F, ⋆F⟩ ↔ ⋆F = -F`. -/
theorem liftInner_self_eq_neg_wedgeDensity_iff (F : LiftForm 2) :
    liftInner F F = -wedgeDensity F ↔ liftStar F = -F := by
  rw [← sdPart_eq_zero_iff, ← liftInner_self_eq_zero (F := sdPart F),
    liftInner_self_eq_neg_wedgeDensity_add]
  constructor <;> intro h <;> linarith

/-- **Pointwise topological bound, self-dual side**: `|F|² ≥ ⟨F, ⋆F⟩`, that is
`|F|² vol ≥ F ∧ F`. -/
theorem wedgeDensity_le_liftInner_self (F : LiftForm 2) : wedgeDensity F ≤ liftInner F F := by
  have h := liftInner_self_nonneg (asdPart F)
  rw [liftInner_self_eq_wedgeDensity_add]
  linarith

/-- **Equality in the self-dual bound holds exactly for self-dual forms**:
`|F|² = ⟨F, ⋆F⟩ ↔ ⋆F = F`. -/
theorem liftInner_self_eq_wedgeDensity_iff (F : LiftForm 2) :
    liftInner F F = wedgeDensity F ↔ liftStar F = F := by
  rw [← asdPart_eq_zero_iff, ← liftInner_self_eq_zero (F := asdPart F),
    liftInner_self_eq_wedgeDensity_add]
  constructor <;> intro h <;> linarith

/-- Both bounds together: `|⟨F, ⋆F⟩| ≤ |F|²`. -/
theorem abs_wedgeDensity_le_liftInner_self (F : LiftForm 2) :
    |wedgeDensity F| ≤ liftInner F F :=
  abs_le.2 ⟨by linarith [neg_wedgeDensity_le_liftInner_self F], wedgeDensity_le_liftInner_self F⟩

/-- **The lift of the source attains the bound**: `|ℱ|² = -⟨ℱ, ⋆ℱ⟩`, so
`ℱ ∧ ℱ = -|ℱ|² vol = -2 |B|² vol`. -/
theorem wedgeDensity_hymLiftAt (b : Form 2) :
    wedgeDensity (hymLiftAt b) = -(2 * ‖flux.symm b‖ ^ 2) := by
  rw [← liftInner_hymLiftAt_self b,
    (liftInner_self_eq_neg_wedgeDensity_iff _).2 (liftStar_hymLiftAt b), neg_neg]

/-- The Yang–Mills density is non-negative. -/
theorem ymDensity_nonneg (F : LiftForm 2) : 0 ≤ ymDensity F := by
  have h := liftInner_self_nonneg F
  rw [ymDensity]
  linarith

/-- **The Yang–Mills density in terms of the two parts**:
`½ |F|² = -½ ⟨F, ⋆F⟩ + |F⁺|²`. -/
theorem ymDensity_eq_neg_wedgeDensity_add (F : LiftForm 2) :
    ymDensity F = -wedgeDensity F / 2 + liftInner (sdPart F) (sdPart F) := by
  rw [ymDensity, liftInner_self_eq_neg_wedgeDensity_add]
  ring

/-! ## The lift as the curvature of a connection on a trivial bundle -/

/-- **The connection 1-form** `𝒜 = π^*A - (π^*φ) dτ` on `ℝ³ × ℝ` built from a 1-form `A` on
`ℝ³` (the vector potential, `dA = ω`) and a function `φ` (the scalar potential, `dφ = ⋆ω`).
This is the source's local formula `A_i = a - Φ_i dt`. It does not depend on `τ`. -/
noncomputable def liftConnection (A : Space → Form 1) (φ : Space → ℝ) (p : LiftSpace) :
    LiftForm 1 :=
  (A p.1).compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ) - φ p.1 • dTau

/-- **Evaluation of the connection form**: `𝒜_{(x,τ)}(u, s) = A_x(u) - φ(x) s`. -/
theorem liftConnection_apply (A : Space → Form 1) (φ : Space → ℝ) (x u : Space) (τ s : ℝ) :
    liftConnection A φ (x, τ) ![(u, s)] = A x ![u] - φ x * s := by
  have e : ((Prod.fst : LiftSpace → Space) ∘ ![(u, s)]) = ![u] := by
    funext i; fin_cases i; rfl
  simp [liftConnection, ContinuousAlternatingMap.compContinuousLinearMap_apply, e]

/-- The connection form does not depend on the auxiliary coordinate, so it is invariant under
every translation `τ ↦ τ + ℓ`. -/
theorem liftConnection_tau_indep (A : Space → Form 1) (φ : Space → ℝ) (x : Space) (τ τ' : ℝ) :
    liftConnection A φ (x, τ) = liftConnection A φ (x, τ') := rfl

/-- **The curvature of the connection form**: `d𝒜 = π^*(dA) - π^*(dφ) ∧ dτ` at a point where
`A` and `φ` are differentiable. -/
theorem extDeriv_liftConnection {A : Space → Form 1} {φ : Space → ℝ} {x : Space}
    (hA : DifferentiableAt ℝ A x) (hφ : DifferentiableAt ℝ φ x) (τ : ℝ) :
    extDeriv (liftConnection A φ) (x, τ) = ofParts (extDeriv A x) (-formGrad φ x) := by
  let P : Form 1 →L[ℝ] LiftForm 1 :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ Space ℝ)
  have h1 : HasFDerivAt (fun p : LiftSpace => A p.1)
      (fderiv ℝ A x ∘L ContinuousLinearMap.fst ℝ Space ℝ) (x, τ) :=
    HasFDerivAt.comp (x, τ) (f := Prod.fst) (g := A) hA.hasFDerivAt hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : LiftSpace => φ p.1)
      (fderiv ℝ φ x ∘L ContinuousLinearMap.fst ℝ Space ℝ) (x, τ) :=
    HasFDerivAt.comp (x, τ) (f := Prod.fst) (g := φ) hφ.hasFDerivAt hasFDerivAt_fst
  have h3 : HasFDerivAt (liftConnection A φ)
      (P ∘L (fderiv ℝ A x ∘L ContinuousLinearMap.fst ℝ Space ℝ) -
        (fderiv ℝ φ x ∘L ContinuousLinearMap.fst ℝ Space ℝ).smulRight dTau) (x, τ) :=
    (P.hasFDerivAt.comp (x, τ) h1).sub (h2.smul_const dTau)
  apply liftForm2_ext
  intro u v s t
  have e1 (a : Space) (r : ℝ) :
      ((Prod.fst : LiftSpace → Space) ∘ (fun _ : Fin 1 => ((a, r) : LiftSpace))) =
        fun _ => a := rfl
  have c1 (a : Space) : (fun _ : Fin 1 => a) = ![a] := by
    funext i; fin_cases i; rfl
  rw [TauCeti.extDeriv_apply_pair, h3.fderiv, ofParts_apply, TauCeti.extDeriv_apply_pair]
  simp [P, ContinuousAlternatingMap.compContinuousLinearMap_apply, e1, c1]
  ring

/-- **The lift is the curvature of an explicit connection** wherever potentials exist: if
`dA = ω` and `dφ = ⋆ω` at `x`, with `A` and `φ` differentiable at `x`, then
`d(π^*A - (π^*φ) dτ) = ℱ` at `(x, τ)`. -/
theorem extDeriv_liftConnection_eq_hymLift {A : Space → Form 1} {φ : Space → ℝ}
    {w : Space → Form 2} {x : Space} (hA : DifferentiableAt ℝ A x)
    (hφ : DifferentiableAt ℝ φ x) (hdA : extDeriv A x = w x)
    (hdφ : formGrad φ x = hodge (w x)) (τ : ℝ) :
    extDeriv (liftConnection A φ) (x, τ) = hymLift w (x, τ) := by
  rw [extDeriv_liftConnection hA hφ, hdA, hdφ, hymLift, hymLiftAt_eq_ofParts]

/-- **Local connection for the lift of a vacuum field.** On an open star-convex region `Ω` a
vacuum form `ω` has a vector potential `A` and a scalar potential `φ`, both of class `C²` on
`Ω`, and the `τ`-independent 1-form `𝒜 = π^*A - (π^*φ) dτ` on `Ω × ℝ` satisfies `d𝒜 = ℱ`.

So on `Ω × ℝ`, and after the quotient by `τ ↦ τ + ℓ` on `Ω × S¹` (`𝒜` does not depend on `τ`),
the lift is the curvature of the connection `d - i𝒜` on the TRIVIAL line bundle. Nothing is
said here about a region that is not star-convex: on a solid torus the scalar potential is
multivalued, the local forms `𝒜` differ by multiples of `dτ`, and the bundle of the source may
be non-trivial. Cocycle data for the bundle and the integrality of the periods of `ℱ/2π` are
in `Theory/Fields/FormHYMBundle`. -/
theorem VacuumForm.exists_liftConnection {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ (A : Space → Form 1) (φ : Space → ℝ), ContDiffOn ℝ 2 A Ω ∧ ContDiffOn ℝ 2 φ Ω ∧
      ∀ x ∈ Ω, ∀ τ : ℝ, extDeriv (liftConnection A φ) (x, τ) = hymLift w (x, τ) := by
  obtain ⟨A, hA, -, hdA⟩ := h.exists_vectorPotential hs
  obtain ⟨φ, hφ, -, hdφ⟩ := h.exists_scalarPotential hs
  refine ⟨A, φ, hA, hφ, fun x hx τ => ?_⟩
  have hn := h.isOpen.mem_nhds hx
  exact extDeriv_liftConnection_eq_hymLift
    ((hA.contDiffAt hn).differentiableAt (by norm_num))
    ((hφ.contDiffAt hn).differentiableAt (by norm_num)) (hdA x hx) (hdφ x hx) τ

/-- **The lift of a vacuum field is exact on a star-convex region times the line**: there is a
1-form `𝒜` on `ℝ³ × ℝ` with `d𝒜 = ℱ` on `Ω × ℝ`. -/
theorem VacuumForm.exists_extDeriv_eq_hymLift {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ 𝒜 : LiftSpace → LiftForm 1,
      ∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv 𝒜 p = hymLift w p := by
  obtain ⟨A, φ, -, -, hd⟩ := h.exists_liftConnection hs
  exact ⟨liftConnection A φ, fun p hp => hd p.1 hp.1 p.2⟩

/-- Vector-language form of `VacuumForm.exists_liftConnection`: a vacuum field `B` on an open
star-convex region has potentials with `d(π^*A - (π^*φ) dτ) = ℱ`, where `ℱ` is the lift of the
flux form of `B`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.exists_liftConnection {Ω : Set Space}
    {B : Space → Space} (h : VacuumField Ω B) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ (A : Space → Form 1) (φ : Space → ℝ), ContDiffOn ℝ 2 A Ω ∧ ContDiffOn ℝ 2 φ Ω ∧
      ∀ x ∈ Ω, ∀ τ : ℝ,
        extDeriv (liftConnection A φ) (x, τ) = hymLift (fluxField B) (x, τ) :=
  (vacuumForm_flux_iff.2 h).exists_liftConnection hs

/-! ## The frame basis and Lebesgue measure on the lift space -/

/-- The standard basis `(e₀, e₁, e₂, e_τ)` of `ℝ³ × ℝ`. Integrals of top-degree forms are taken
on this basis; its Haar measure is Lebesgue measure (`liftBasis_addHaar`). -/
noncomputable def liftBasis : Basis (Fin 4) ℝ LiftSpace :=
  (stdBasis.toBasis.prod (Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv

/-- The vectors of the standard basis: `(e₀, 0)`, `(e₁, 0)`, `(e₂, 0)`, `(0, 1)`. -/
theorem liftBasis_apply :
    liftBasis 0 = (coordVec 0, 0) ∧ liftBasis 1 = (coordVec 1, 0) ∧
    liftBasis 2 = (coordVec 2, 0) ∧ liftBasis 3 = (0, 1) := by
  have h0 : finSumFinEquiv.symm (0 : Fin (3 + 1)) = Sum.inl 0 := rfl
  have h1 : finSumFinEquiv.symm (1 : Fin (3 + 1)) = Sum.inl 1 := rfl
  have h2 : finSumFinEquiv.symm (2 : Fin (3 + 1)) = Sum.inl 2 := rfl
  have h3 : finSumFinEquiv.symm (3 : Fin (3 + 1)) = Sum.inr 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [liftBasis, h0, h1, h2, h3, coordVec]

/-- **The Haar measure of the standard basis is Lebesgue measure** on `ℝ³ × ℝ` (the product of
the Lebesgue measures of `ℝ³` and `ℝ`). -/
theorem liftBasis_addHaar :
    liftBasis.addHaar = (MeasureTheory.volume : MeasureTheory.Measure LiftSpace) := by
  rw [liftBasis, Basis.addHaar_reindex, Basis.prod_addHaar, OrthonormalBasis.addHaar_eq_volume,
    Basis.addHaar_singleton, MeasureTheory.Measure.volume_eq_prod]

/-- The volume form is `1` on the standard basis. -/
theorem liftVol_liftBasis (h : 2 + 2 = 4) : liftVol (liftBasis ∘ Fin.cast h) = 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := liftBasis_apply
  have e : (liftBasis ∘ Fin.cast h : Fin (2 + 2) → LiftSpace) =
      ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)] := by
    funext i; fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  rw [e, liftVol_frame]

/-! ## The cross term: a co-closed form is orthogonal to compactly supported exact forms -/

/-- The star as a continuous linear map (the space of 2-forms is finite-dimensional). -/
noncomputable def liftStarCLM : LiftForm 2 →L[ℝ] LiftForm 2 :=
  haveI : FiniteDimensional ℝ (LiftForm 2) :=
    Module.finite_of_finrank_pos (by rw [finrank_liftForm2]; norm_num)
  LinearMap.toContinuousLinearMap liftStar.toLinearMap

/-- `liftStarCLM` is `liftStar`. -/
@[simp] theorem liftStarCLM_apply (F : LiftForm 2) : liftStarCLM F = liftStar F := rfl

/-- **`⋆F ∧ H = ⟨F, H⟩ vol`** for 2-forms on `ℝ³ × ℝ`. -/
theorem liftStar_wedge_apply (F H : LiftForm 2) (v : Fin (2 + 2) → LiftSpace) :
    (ContinuousAlternatingMap.wedge (liftStar F) H) v = liftInner F H * liftVol v := by
  have h := wedge_liftStar_apply (liftStar F) (liftStar H) v
  rwa [liftStar_liftStar, liftInner_liftStar_liftStar] at h

/-- The inner product of two continuous families of 2-forms is continuous. -/
theorem continuous_liftInner {X : Type*} [TopologicalSpace X] {F H : X → LiftForm 2}
    (hF : Continuous F) (hH : Continuous H) : Continuous fun x => liftInner (F x) (H x) := by
  simp only [liftInner_eq]
  fun_prop

section Energy

open MeasureTheory TauCeti

variable {G : LiftSpace → LiftForm 2} {a : LiftSpace → LiftForm 1} {U : Set LiftSpace}

/-- The 3-form `⋆G ∧ a` whose exterior derivative is the cross term. -/
noncomputable def starWedge (G : LiftSpace → LiftForm 2) (a : LiftSpace → LiftForm 1)
    (p : LiftSpace) : LiftSpace [⋀^Fin (2 + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.wedge (liftStar (G p)) (a p)

/-- `⋆G ∧ a` is of class `C¹` on the whole space when `a` is `C¹` and `G` is `C¹` on an open
set containing the closed support of `a`: away from that support the form vanishes
identically. -/
theorem contDiff_starWedge (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) (ha : ContDiff ℝ 1 a)
    (hsupp : tsupport a ⊆ U) : ContDiff ℝ 1 (starWedge G a) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ U
  · have h1 : ContDiffAt ℝ 1 (fun q => liftStar (G q)) p :=
      liftStarCLM.contDiff.contDiffAt.comp p (hG.contDiffAt (hU.mem_nhds hp))
    have h2 : ContDiffAt ℝ 1
        (fun q => ContinuousAlternatingMap.wedge (liftStar (G q)) (a q)) p := by
      simpa only [ContinuousAlternatingMap.wedge_def] using
        (contDiffAt_const (c := ContinuousLinearMap.mul ℝ ℝ)).pairedWedge h1 ha.contDiffAt
    exact h2
  · have h0 : a =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hp (hsupp h)
    have h1 : starWedge G a =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [h0] with q hq
      rw [starWedge, hq]
      exact ContinuousAlternatingMap.wedge_zero_right _
    exact contDiffAt_const.congr_of_eventuallyEq h1

/-- **Leibniz rule for the cross term**: if `G` is `C¹` and co-closed (`d(⋆G) = 0`) on an open
set `U` containing the closed support of `a`, then at every point of the space the top-degree
coefficient of `d(⋆G ∧ a)` on the standard basis is `⟨G, da⟩`. Outside `U` both sides vanish
because `a` vanishes identically near the point. -/
theorem extDeriv_starWedge_apply (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hsupp : tsupport a ⊆ U) (p : LiftSpace) :
    extDeriv (starWedge G a) p liftBasis = liftInner (G p) (extDeriv a p) := by
  by_cases hp : p ∈ U
  · have h1 : DifferentiableAt ℝ (fun q => liftStar (G q)) p :=
      liftStarCLM.differentiableAt.comp p
        ((hG.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero)
    have h2 : DifferentiableAt ℝ a p := ha.differentiable one_ne_zero p
    have h := extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ) h1 h2 liftBasis
    simp only [← ContinuousAlternatingMap.wedge_def] at h
    change extDeriv (fun q => ContinuousAlternatingMap.wedge (liftStar (G q)) (a q)) p liftBasis
      = _
    rw [h, hcc p hp, ContinuousAlternatingMap.wedge_zero_left, liftStar_wedge_apply,
      liftVol_liftBasis]
    simp
  · have h0 : a =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hp (hsupp h)
    have h1 : starWedge G a =ᶠ[nhds p] 0 := by
      filter_upwards [h0] with q hq
      rw [starWedge, hq]
      exact ContinuousAlternatingMap.wedge_zero_right _
    have h2 : extDeriv a p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hp (hsupp (tsupport_extDeriv_subset h))
    have h3 : extDeriv (starWedge G a) p = 0 :=
      image_eq_zero_of_notMem_tsupport fun h =>
        notMem_tsupport_iff_eventuallyEq.2 h1 (tsupport_extDeriv_subset h)
    rw [h3, h2, liftInner_zero_right]
    rfl

/-- **The cross term is integrable.** Under the hypotheses of
`integral_liftInner_extDeriv_eq_zero` the function `⟨G, da⟩` is integrable for Lebesgue
measure on `ℝ³ × ℝ`, although `G` is only defined with regularity on `U` and need not be
integrable: the function vanishes outside the compact support of `a`. -/
theorem integrable_liftInner_extDeriv (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    Integrable fun p => liftInner (G p) (extDeriv a p) := by
  have h := (liftBasis.integral_extDeriv_eq_zero (contDiff_starWedge hU hG ha hsupp)
    (hc.wedge_left (φ := fun q => liftStar (G q)))).1
  rw [liftBasis_addHaar] at h
  exact h.congr (Filter.Eventually.of_forall fun p =>
    extDeriv_starWedge_apply hU hG hcc ha hsupp p)

/-- **Orthogonality of a co-closed form to compactly supported exact forms.** Let `G` be a
field of 2-forms on `ℝ³ × ℝ` that is `C¹` and co-closed, `d(⋆G) = 0`, on an open set `U` (a
solution of the vacuum Maxwell equation in dimension four), and let `a` be a `C¹` field of
1-forms with compact support contained in `U`. Then `∫ ⟨G, da⟩ = 0`, for Lebesgue measure.

Proof: `⟨G, da⟩ vol = ⋆G ∧ da = d(⋆G ∧ a)`, and the integral of the exterior derivative of a
compactly supported `C¹` form vanishes (TauCeti's `Module.Basis.integral_extDeriv_eq_zero`).
The integrand is integrable (`integrable_liftInner_extDeriv`), so the value `0` is not a junk
value of the Bochner integral. -/
theorem integral_liftInner_extDeriv_eq_zero (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    ∫ p, liftInner (G p) (extDeriv a p) = 0 := by
  have h := (liftBasis.integral_extDeriv_eq_zero (contDiff_starWedge hU hG ha hsupp)
    (hc.wedge_left (φ := fun q => liftStar (G q)))).2
  rw [liftBasis_addHaar] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun p =>
    (extDeriv_starWedge_apply hU hG hcc ha hsupp p).symm)

/-- The energy density `|da|²` of a compactly supported `C¹` perturbation is integrable. -/
theorem integrable_liftInner_extDeriv_self (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    Integrable fun p => liftInner (extDeriv a p) (extDeriv a p) := by
  have hd : Continuous (extDeriv a) := (contDiff_extDeriv (r := 0) ha (by simp)).continuous
  refine (continuous_liftInner hd hd).integrable_of_hasCompactSupport ?_
  exact hc.extDeriv.mono fun p hp h => hp (by simp [h])

/-- **Pointwise expansion of the perturbed energy density**:
`|G + H|² - |G|² = |H|² + 2 ⟨G, H⟩`. -/
theorem liftInner_add_self_sub (F H : LiftForm 2) :
    liftInner (F + H) (F + H) - liftInner F F = liftInner H H + 2 * liftInner F H := by
  rw [liftInner_add_left, liftInner_add_right, liftInner_add_right, liftInner_comm H F]
  ring

/-- **The change of the energy density is integrable**: `|G + da|² - |G|²` is integrable for
Lebesgue measure, with no integrability hypothesis on `G` (it vanishes where `da = 0`). -/
theorem integrable_energy_perturbation (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    Integrable fun p => liftInner (G p + extDeriv a p) (G p + extDeriv a p) -
      liftInner (G p) (G p) := by
  refine ((integrable_liftInner_extDeriv_self ha hc).add
    ((integrable_liftInner_extDeriv hU hG hcc ha hc hsupp).const_mul 2)).congr
    (Filter.Eventually.of_forall fun p => ?_)
  exact (liftInner_add_self_sub (G p) (extDeriv a p)).symm

/-- **Energy identity for a compactly supported perturbation of the connection.** Let `G` be
a field of 2-forms on `ℝ³ × ℝ` that is `C¹` and co-closed (`d(⋆G) = 0`) on an open set `U`, and
let `a` be a `C¹` field of 1-forms with compact support contained in `U`. Then

`∫ (|G + da|² - |G|²) = ∫ |da|²`

for Lebesgue measure on `ℝ³ × ℝ`. The left integrand is the change of the Abelian Yang–Mills
energy density (times two) when the connection `A` with `dA = G` is replaced by `A + a`.

Integrability: both integrands are integrable (`integrable_energy_perturbation`,
`integrable_liftInner_extDeriv_self`), so this is an identity between genuine integrals. No
integrability of `G` is assumed or needed; a `τ`-independent `G` such as the lift is not
integrable over `ℝ³ × ℝ`, which is why the difference is integrated and the two energies are
not written separately. -/
theorem integral_energy_perturbation (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    ∫ p, (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) =
      ∫ p, liftInner (extDeriv a p) (extDeriv a p) := by
  have e : ∫ p, (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) =
      ∫ p, (liftInner (extDeriv a p) (extDeriv a p) + 2 * liftInner (G p) (extDeriv a p)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun p =>
      liftInner_add_self_sub (G p) (extDeriv a p))
  rw [e, integral_add (integrable_liftInner_extDeriv_self ha hc)
    ((integrable_liftInner_extDeriv hU hG hcc ha hc hsupp).const_mul 2), integral_const_mul,
    integral_liftInner_extDeriv_eq_zero hU hG hcc ha hc hsupp]
  ring

/-- **Minimality**: a compactly supported perturbation of the connection of a co-closed
curvature does not decrease the energy, `∫ (|G + da|² - |G|²) ≥ 0`. -/
theorem integral_energy_perturbation_nonneg (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    0 ≤ ∫ p, (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) := by
  rw [integral_energy_perturbation hU hG hcc ha hc hsupp]
  exact integral_nonneg fun p => liftInner_self_nonneg _

/-- **Strictness**: the energy is unchanged exactly when the perturbation does not change the
curvature, `∫ (|G + da|² - |G|²) = 0 ↔ da = 0` everywhere. -/
theorem integral_energy_perturbation_eq_zero_iff (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    ∫ p, (liftInner (G p + extDeriv a p) (G p + extDeriv a p) - liftInner (G p) (G p)) = 0 ↔
      ∀ p, extDeriv a p = 0 := by
  have hd : Continuous (extDeriv a) := (contDiff_extDeriv (r := 0) ha (by simp)).continuous
  rw [integral_energy_perturbation hU hG hcc ha hc hsupp,
    integral_eq_zero_iff_of_nonneg (fun p => liftInner_self_nonneg _)
      (integrable_liftInner_extDeriv_self ha hc)]
  have hz : Continuous (0 : LiftSpace → ℝ) := continuous_const
  rw [Continuous.ae_eq_iff_eq volume (continuous_liftInner hd hd) hz]
  constructor
  · intro h p
    exact liftInner_self_eq_zero.1 (congrFun h p)
  · intro h
    funext p
    rw [h p]
    exact liftInner_zero_left _

/-- The same identity for the Yang–Mills density `½ |F|²`:
`∫ (ym(G + da) - ym(G)) = ∫ ym(da)`. -/
theorem integral_ymDensity_perturbation (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (hcc : ∀ p ∈ U, extDeriv (fun q => liftStar (G q)) p = 0) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ U) :
    ∫ p, (ymDensity (G p + extDeriv a p) - ymDensity (G p)) =
      ∫ p, ymDensity (extDeriv a p) := by
  have e (p : LiftSpace) : ymDensity (G p + extDeriv a p) - ymDensity (G p) =
      (1 / 2 : ℝ) * (liftInner (G p + extDeriv a p) (G p + extDeriv a p) -
        liftInner (G p) (G p)) := by
    rw [ymDensity, ymDensity]; ring
  have e' (p : LiftSpace) : ymDensity (extDeriv a p) =
      (1 / 2 : ℝ) * liftInner (extDeriv a p) (extDeriv a p) := by
    rw [ymDensity]; ring
  simp only [e, e']
  rw [integral_const_mul, integral_const_mul,
    integral_energy_perturbation hU hG hcc ha hc hsupp]

/-! ## Closed self-dual and anti-self-dual forms are co-closed -/

/-- A closed anti-self-dual field of 2-forms is co-closed: if `⋆G = -G` everywhere and
`dG = 0` at `p`, then `d(⋆G) = 0` at `p`. -/
theorem extDeriv_liftStar_eq_zero_of_antiSelfDual (hasd : ∀ q, liftStar (G q) = -G q)
    {p : LiftSpace} (hcl : extDeriv G p = 0) : extDeriv (fun q => liftStar (G q)) p = 0 := by
  have e : (fun q => liftStar (G q)) = (-1 : ℝ) • G := by
    funext q
    rw [hasd q, Pi.smul_apply, neg_one_smul]
  rw [e, extDeriv_smul, hcl, smul_zero]

/-- A closed self-dual field of 2-forms is co-closed. -/
theorem extDeriv_liftStar_eq_zero_of_selfDual (hsd : ∀ q, liftStar (G q) = G q)
    {p : LiftSpace} (hcl : extDeriv G p = 0) : extDeriv (fun q => liftStar (G q)) p = 0 := by
  have e : (fun q => liftStar (G q)) = G := funext hsd
  rw [e, hcl]

/-- **Orthogonality for a closed anti-self-dual form**: `∫ ⟨G, da⟩ = 0` for `G` of class `C¹`,
closed on the open set `U` and anti-self-dual, and `a` of class `C¹` with compact support in
`U`. -/
theorem integral_liftInner_extDeriv_eq_zero_of_antiSelfDual (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (hasd : ∀ q, liftStar (G q) = -G q)
    (hcl : ∀ p ∈ U, extDeriv G p = 0) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ U) : ∫ p, liftInner (G p) (extDeriv a p) = 0 :=
  integral_liftInner_extDeriv_eq_zero hU hG
    (fun p hp => extDeriv_liftStar_eq_zero_of_antiSelfDual hasd (hcl p hp)) ha hc hsupp

/-- **Orthogonality for a closed self-dual form**: `∫ ⟨G, da⟩ = 0` for `G` of class `C¹`,
closed on the open set `U` and self-dual, and `a` of class `C¹` with compact support in
`U`. -/
theorem integral_liftInner_extDeriv_eq_zero_of_selfDual (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (hsd : ∀ q, liftStar (G q) = G q)
    (hcl : ∀ p ∈ U, extDeriv G p = 0) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ U) : ∫ p, liftInner (G p) (extDeriv a p) = 0 :=
  integral_liftInner_extDeriv_eq_zero hU hG
    (fun p hp => extDeriv_liftStar_eq_zero_of_selfDual hsd (hcl p hp)) ha hc hsupp

/-! ## The lift of a vacuum field minimises the Abelian Yang–Mills energy -/

/-- The lift of a vacuum form is of class `C¹` on `Ω × ℝ`. -/
theorem VacuumForm.contDiffOn_hymLift {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) : ContDiffOn ℝ 1 (hymLift w) (Ω ×ˢ (Set.univ : Set ℝ)) := by
  have h1 : ContDiffOn ℝ 1 (fun p : LiftSpace => w p.1) (Ω ×ˢ (Set.univ : Set ℝ)) :=
    (h.contDiffOn.of_le (by norm_num)).comp contDiff_fst.contDiffOn fun p hp => hp.1
  have e : hymLift w = hymLiftCLM ∘ fun p : LiftSpace => w p.1 := by
    funext p; simp [hymLift]
  rw [e]
  exact hymLiftCLM.contDiff.comp_contDiffOn h1

/-- The lift of a vacuum form is co-closed on `Ω × ℝ`: `d(⋆ℱ) = 0`. -/
theorem VacuumForm.extDeriv_liftStar_hymLift {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) :
    ∀ p ∈ Ω ×ˢ (Set.univ : Set ℝ), extDeriv (fun q => liftStar (hymLift w q)) p = 0 :=
  fun p hp => extDeriv_liftStar_eq_zero_of_antiSelfDual (liftStar_hymLift w) (h.hymLift_closed p hp)

/-- **The cross term vanishes for the lift of a vacuum field**: `∫ ⟨ℱ, da⟩ = 0` for every `C¹`
field of 1-forms `a` with compact support in `Ω × ℝ`. -/
theorem VacuumForm.integral_liftInner_hymLift_extDeriv {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    ∫ p, liftInner (hymLift w p) (extDeriv a p) = 0 :=
  integral_liftInner_extDeriv_eq_zero (h.isOpen.prod isOpen_univ) h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hc hsupp

/-- **Yang–Mills minimality of the lift, energy identity.** Let `ω` be a vacuum form on an
open region `Ω` of `ℝ³`, `ℱ = hymLift ω` its anti-self-dual lift on `Ω × ℝ`, and `a` a `C¹`
field of 1-forms on `ℝ³ × ℝ` with compact support contained in `Ω × ℝ`. Then

`∫ (|ℱ + da|² - |ℱ|²) = ∫ |da|²`

for Lebesgue measure on `ℝ³ × ℝ`. Both integrands are integrable (they vanish outside the
support of `a`); `ℱ` itself is not integrable in general and no such hypothesis is made. The
values of `ω` outside `Ω` do not matter. This is the source's identity
`∫_M |ℱ + da₁|² - ∫_M |ℱ|² = ∫_M |da₁|² ≥ 0`, for perturbations with compact support in
`Ω × ℝ` instead of perturbations of `Ω × S¹` with vanishing tangential trace on the boundary. -/
theorem VacuumForm.integral_energy_hymLift_perturbation {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    ∫ p, (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
        liftInner (hymLift w p) (hymLift w p)) =
      ∫ p, liftInner (extDeriv a p) (extDeriv a p) :=
  integral_energy_perturbation (h.isOpen.prod isOpen_univ) h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hc hsupp

/-- **Yang–Mills minimality of the lift.** For a vacuum form `ω` on `Ω` and a `C¹` field of
1-forms `a` with compact support in `Ω × ℝ`, the change of energy is non-negative:
`∫ (|ℱ + da|² - |ℱ|²) ≥ 0`. The integrand is integrable
(`VacuumForm.integrable_energy_hymLift_perturbation`). -/
theorem VacuumForm.integral_energy_hymLift_perturbation_nonneg {Ω : Set Space}
    {w : Space → Form 2} (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    0 ≤ ∫ p, (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
        liftInner (hymLift w p) (hymLift w p)) :=
  integral_energy_perturbation_nonneg (h.isOpen.prod isOpen_univ) h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hc hsupp

/-- The change of the energy density of the lift under a compactly supported perturbation is
integrable. -/
theorem VacuumForm.integrable_energy_hymLift_perturbation {Ω : Set Space}
    {w : Space → Form 2} (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    Integrable fun p => liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
        liftInner (hymLift w p) (hymLift w p) :=
  integrable_energy_perturbation (h.isOpen.prod isOpen_univ) h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hc hsupp

/-- **Strict minimality of the lift**: the energy is unchanged exactly when the perturbation
does not change the curvature, `∫ (|ℱ + da|² - |ℱ|²) = 0 ↔ da = 0` everywhere. -/
theorem VacuumForm.integral_energy_hymLift_perturbation_eq_zero_iff {Ω : Set Space}
    {w : Space → Form 2} (h : VacuumForm Ω w) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a)
    (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    ∫ p, (liftInner (hymLift w p + extDeriv a p) (hymLift w p + extDeriv a p) -
        liftInner (hymLift w p) (hymLift w p)) = 0 ↔ ∀ p, extDeriv a p = 0 :=
  integral_energy_perturbation_eq_zero_iff (h.isOpen.prod isOpen_univ) h.contDiffOn_hymLift
    h.extDeriv_liftStar_hymLift ha hc hsupp

/-- **Yang–Mills minimality of the lift, vector language**: for a vacuum field `B` on `Ω`, with
`ℱ` the lift of its flux form, and a `C¹` field of 1-forms `a` with compact support in
`Ω × ℝ`, `∫ (ym(ℱ + da) - ym(ℱ)) = ∫ ym(da)` and this is non-negative; here
`ym(F) = ½ |F|²` and `ym(ℱ) = |B|²` (`ymDensity_hymLiftAt_flux`). -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.integral_ymDensity_hymLift_perturbation
    {Ω : Set Space} {B : Space → Space} (h : VacuumField Ω B) (ha : ContDiff ℝ 1 a)
    (hc : HasCompactSupport a) (hsupp : tsupport a ⊆ Ω ×ˢ (Set.univ : Set ℝ)) :
    ∫ p, (ymDensity (hymLift (fluxField B) p + extDeriv a p) -
        ymDensity (hymLift (fluxField B) p)) = ∫ p, ymDensity (extDeriv a p) ∧
      0 ≤ ∫ p, ymDensity (extDeriv a p) := by
  have hv := vacuumForm_flux_iff.2 h
  refine ⟨integral_ymDensity_perturbation (hv.isOpen.prod isOpen_univ) hv.contDiffOn_hymLift
    hv.extDeriv_liftStar_hymLift ha hc hsupp, integral_nonneg fun p => ymDensity_nonneg _⟩

end Energy

end PlasmaLean.Forms
