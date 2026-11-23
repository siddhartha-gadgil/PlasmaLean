/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormFluxSurfacePeriods
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Flux surfaces as embedded tori, and the periods on the torus

The contract's invariant tori are parametrised maps `K (θ, φ) = cylPoint (R θ φ) φ (z θ φ)` on
the plane (`torusMap`), doubly `2π`-periodic. Nothing in `Contract.FieldTorus` or in
`PeriodicC2Torus` says that `K` is injective modulo the periods or an immersion (audit findings
AF-1 and AV-M9). This file defines the missing predicate and moves the statements of
`Theory/Fields/FormFluxSurfacePeriods` from the parameter plane to the torus
`AngleTorus = AddCircle (2π) × AddCircle (2π)`.

Definitions.
* `AngleTorus`, `torusProj : ℝ × ℝ → AngleTorus` (the quotient map), `torusLift f` (the descent
  of a function on the plane; it satisfies `torusLift f (torusProj p) = f p` when `f` is doubly
  `2π`-periodic, `torusLift_proj`).
* `PeriodicTorus R z`: `R`, `z` continuous and doubly `2π`-periodic (a `FieldTorus` and a
  `PeriodicC2Torus` are such).
* `torusEmb R z = torusLift (torusMap R z) : AngleTorus → Space`, the descended torus map.
* `InjectiveModPeriods R z`: `K p = K q` only if `q = p + (2π m, 2π n)` with integers `m`, `n`.
* `EmbeddedTorus R z`: `PeriodicC2Torus R z`, `InjectiveModPeriods R z`, and the differential
  `fderiv ℝ K p` is injective at every `p`.
* `torusFormT B R z = torusLift (torusForm B R z)`: the pull-back of `B♭` as a 1-form on the
  torus (the tangent space of `AngleTorus` at every point is `ℝ × ℝ`).

Results.
* Topology (continuity and periodicity only): `PeriodicTorus.continuous_torusEmb`,
  `range_torusEmb`, `isCompact_range_torusMap`, `injective_torusEmb_iff` (`torusEmb` is injective
  exactly when `K` is injective modulo the periods), `isClosedEmbedding_torusEmb`, and the
  homeomorphism `PeriodicTorus.homeomorph` of the 2-torus onto the surface `Set.range K`.
* Cylindrical criteria: `cylPoint_eq_iff_of_pos`; for `R > 0`, injectivity modulo the periods
  holds exactly when every section `θ ↦ (R θ φ, z θ φ)` is injective modulo `2π`
  (`PeriodicTorus.injectiveModPeriods_iff_sections`); for `R > 0` the differential of `K` is
  injective exactly when `(∂_θ R, ∂_θ z) ≠ 0` (`PeriodicC2Torus.injective_fderiv_torusMap_iff`).
  `EmbeddedTorus.of_sections` combines them. `torusMap_axis_dist`: a torus with `R > 0` does not
  meet the axis.
* Smoothness: `torusProj` is a local diffeomorphism with differential the identity;
  `contMDiff_torusLift`, `hasMFDerivAt_torusLift`; `EmbeddedTorus.isImmersion_torusEmb` and
  `EmbeddedTorus.isSmoothEmbedding_torusEmb`: for an embedded torus, `torusEmb` is a `C²`
  embedding of manifolds (Mathlib's `Manifold.IsSmoothEmbedding`: an immersion in the sense of
  slice charts that is a topological embedding).
* Periods on the torus: `PeriodicC2Torus.exists_potential_on_torus`: for a `C¹` curl-free field
  near the surface, `β - (P_θ/2π) dθ - (P_φ/2π) dφ` is the differential of a `C¹` function on
  the torus; `PeriodicC2Torus.periods_eq_of_potential_on_torus`: the two coefficients are
  forced. Neither uses embeddedness.
* Contract: `FieldTorus.periodicTorus`, `FieldTorus.isCompact_range_torusMap`,
  `FieldTorus.homeomorph`, `FieldTorus.axis_dist_pos`.

What is not proved. The class statement is not expressed in TauCeti's de Rham cohomology
(`TauCeti.deRhamCohomology`, `TauCeti.torusTimeForm`): that cohomology is built from `C^∞`
forms, whereas the pulled-back form of a `C²` surface and a `C¹` field is only continuous. The
statement here is the `C¹` one: existence and uniqueness of the decomposition
`β = a dθ + b dφ + dḡ` with `ḡ` a `C¹` function on the torus. The torus is the product
`AddCircle (2π) × AddCircle (2π)`, not TauCeti's `∀ i : Fin 2, AddCircle (2π)`. The image is
not shown to be an embedded submanifold in a sense other than "image of a smooth embedding".
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open Real
open scoped RealInnerProductSpace Manifold

/-- The period `2π` is positive (needed for the circle `AddCircle (2 * π)`). -/
local instance factTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ## The angle torus and the descent of periodic functions -/

/-- The **angle torus** `ℝ/2πℤ × ℝ/2πℤ` of the poloidal and toroidal parameters. -/
abbrev AngleTorus : Type := AddCircle (2 * π) × AddCircle (2 * π)

/-- The **quotient map** of the parameter plane onto the angle torus. -/
noncomputable def torusProj : ℝ × ℝ → AngleTorus :=
  Prod.map ((↑) : ℝ → AddCircle (2 * π)) ((↑) : ℝ → AddCircle (2 * π))

/-- The **descent** of a function on the parameter plane to the angle torus: its value at the
chosen representatives. For a doubly `2π`-periodic function it does not depend on the
representatives (`torusLift_proj`). -/
noncomputable def torusLift {α : Type*} (f : ℝ × ℝ → α) (x : AngleTorus) : α :=
  f (Quotient.out x.1, Quotient.out x.2)

/-- The quotient map sends `(θ, φ)` to the pair of classes. -/
theorem torusProj_apply (θ φ : ℝ) :
    torusProj (θ, φ) = ((θ : AddCircle (2 * π)), (φ : AddCircle (2 * π))) := rfl

/-- The quotient map onto the angle torus is surjective. -/
theorem torusProj_surjective : Function.Surjective torusProj :=
  Function.Surjective.prodMap QuotientAddGroup.mk_surjective QuotientAddGroup.mk_surjective

/-- Two reals have the same class in `ℝ/cℤ` exactly when they differ by an integer multiple of
`c`. -/
theorem addCircle_coe_eq_iff {c a b : ℝ} :
    (a : AddCircle c) = b ↔ ∃ m : ℤ, b = a + c * m := by
  rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul] at hm; linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [zsmul_eq_mul]; linarith⟩

/-- Two points of the plane have the same image in the angle torus exactly when they differ by
a period `(2π m, 2π n)`. -/
theorem torusProj_eq_iff {p q : ℝ × ℝ} :
    torusProj p = torusProj q ↔ ∃ m n : ℤ, q = p + (2 * π * m, 2 * π * n) := by
  rw [torusProj, Prod.map_apply', Prod.map_apply', Prod.mk.injEq, addCircle_coe_eq_iff,
    addCircle_coe_eq_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, n, hn⟩
    exact ⟨m, n, Prod.ext (by simpa using hm) (by simpa using hn)⟩
  · rintro ⟨m, n, h⟩
    exact ⟨⟨m, by simpa using congrArg Prod.fst h⟩, n, by simpa using congrArg Prod.snd h⟩

/-- The quotient map onto the angle torus is an open quotient map. -/
theorem isOpenQuotientMap_torusProj : IsOpenQuotientMap torusProj :=
  QuotientAddGroup.isOpenQuotientMap_mk.prodMap QuotientAddGroup.isOpenQuotientMap_mk

/-- A doubly `2π`-periodic function on the plane is invariant under all the translations
`(2π m, 2π n)` with integers `m`, `n`. -/
theorem periodic_add_int {α : Type*} {f : ℝ × ℝ → α} (hθ : ∀ p, f (p + (2 * π, 0)) = f p)
    (hφ : ∀ p, f (p + (0, 2 * π)) = f p) (p : ℝ × ℝ) (m n : ℤ) :
    f (p + (2 * π * m, 2 * π * n)) = f p := by
  have h1 : ∀ b, Function.Periodic (fun t => f (t, b)) (2 * π) := fun b t => by
    simpa using hθ (t, b)
  have h2 : ∀ a, Function.Periodic (fun t => f (a, t)) (2 * π) := fun a t => by
    simpa using hφ (a, t)
  have e1 := (h1 (p.2 + 2 * π * n)).int_mul m p.1
  have e2 := (h2 p.1).int_mul n p.2
  beta_reduce at e1 e2
  rw [show p + (2 * π * m, 2 * π * n) = (p.1 + m * (2 * π), p.2 + 2 * π * n) by
    ext <;> simp [mul_comm], e1, mul_comm (2 * π) (n : ℝ), e2]

/-- **The descent is well defined**: for a doubly `2π`-periodic `f`, the descended function
takes the value `f p` at the class of `p`. -/
theorem torusLift_proj {α : Type*} {f : ℝ × ℝ → α} (hθ : ∀ p, f (p + (2 * π, 0)) = f p)
    (hφ : ∀ p, f (p + (0, 2 * π)) = f p) (p : ℝ × ℝ) : torusLift f (torusProj p) = f p := by
  have h : torusProj p
      = torusProj (Quotient.out (torusProj p).1, Quotient.out (torusProj p).2) := by
    rw [torusProj_apply]
    exact Prod.ext (QuotientAddGroup.out_eq' _).symm (QuotientAddGroup.out_eq' _).symm
  obtain ⟨m, n, hmn⟩ := torusProj_eq_iff.1 h
  rw [torusLift, hmn, periodic_add_int hθ hφ]

/-- The descent composed with the quotient map is the original periodic function. -/
theorem torusLift_comp_proj {α : Type*} {f : ℝ × ℝ → α} (hθ : ∀ p, f (p + (2 * π, 0)) = f p)
    (hφ : ∀ p, f (p + (0, 2 * π)) = f p) : torusLift f ∘ torusProj = f :=
  funext (torusLift_proj hθ hφ)

/-- The descent of a continuous doubly periodic function is continuous on the torus. -/
theorem continuous_torusLift {α : Type*} [TopologicalSpace α] {f : ℝ × ℝ → α}
    (hθ : ∀ p, f (p + (2 * π, 0)) = f p) (hφ : ∀ p, f (p + (0, 2 * π)) = f p)
    (hf : Continuous f) : Continuous (torusLift f) := by
  rw [← isOpenQuotientMap_torusProj.continuous_comp_iff, torusLift_comp_proj hθ hφ]
  exact hf

/-- The range of the descent of a doubly periodic function is the range of the function. -/
theorem range_torusLift {α : Type*} {f : ℝ × ℝ → α} (hθ : ∀ p, f (p + (2 * π, 0)) = f p)
    (hφ : ∀ p, f (p + (0, 2 * π)) = f p) : Set.range (torusLift f) = Set.range f := by
  rw [← torusProj_surjective.range_comp, torusLift_comp_proj hθ hφ]

/-! ## Continuous doubly periodic tori and the descended torus map -/

/-- A **continuous doubly periodic torus**: `R` and `z` are continuous on the plane and
`2π`-periodic in both angles. No injectivity, no positivity of `R`. -/
structure PeriodicTorus (R z : ℝ → ℝ → ℝ) : Prop where
  /-- `R` is continuous. -/
  continuous_R : Continuous (fun p : ℝ × ℝ => R p.1 p.2)
  /-- `z` is continuous. -/
  continuous_z : Continuous (fun p : ℝ × ℝ => z p.1 p.2)
  /-- `R` is `2π`-periodic in `θ`. -/
  per_θ_R : ∀ θ φ, R (θ + 2 * π) φ = R θ φ
  /-- `z` is `2π`-periodic in `θ`. -/
  per_θ_z : ∀ θ φ, z (θ + 2 * π) φ = z θ φ
  /-- `R` is `2π`-periodic in `φ`. -/
  per_φ_R : ∀ θ φ, R θ (φ + 2 * π) = R θ φ
  /-- `z` is `2π`-periodic in `φ`. -/
  per_φ_z : ∀ θ φ, z θ (φ + 2 * π) = z θ φ

/-- A doubly periodic `C²` torus is a continuous doubly periodic torus. -/
theorem PeriodicC2Torus.periodicTorus {R z : ℝ → ℝ → ℝ} (h : PeriodicC2Torus R z) :
    PeriodicTorus R z :=
  ⟨h.contDiff_R.continuous, h.contDiff_z.continuous, h.per_θ_R, h.per_θ_z, h.per_φ_R,
    h.per_φ_z⟩

/-- A `FieldTorus` of the contract is a continuous doubly periodic torus. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.periodicTorus {B : Space → Space}
    {R z : ℝ → ℝ → ℝ} {ι : ℝ} (hT : FieldTorus B R z ι) : PeriodicTorus R z :=
  ⟨hT.continuous_R, hT.continuous_z, hT.per_θ_R, hT.per_θ_z, hT.per_φ_R, hT.per_φ_z⟩

/-- The **descended torus map** `AngleTorus → Space`, with
`torusEmb R z (↑θ, ↑φ) = torusMap R z (θ, φ)` for a doubly periodic torus
(`PeriodicTorus.torusEmb_proj`). -/
noncomputable def torusEmb (R z : ℝ → ℝ → ℝ) : AngleTorus → Space :=
  torusLift (torusMap R z)

/-- **Injectivity modulo the periods**: the torus map takes the same value at two parameters
only if they differ by a period `(2π m, 2π n)`. -/
def InjectiveModPeriods (R z : ℝ → ℝ → ℝ) : Prop :=
  ∀ p q : ℝ × ℝ, torusMap R z p = torusMap R z q →
    ∃ m n : ℤ, q = p + (2 * π * m, 2 * π * n)

section Topology

variable {R z : ℝ → ℝ → ℝ}

/-- The torus map of a continuous torus is continuous. -/
theorem PeriodicTorus.continuous_torusMap (h : PeriodicTorus R z) :
    Continuous (torusMap R z) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · exact (h.continuous_R.mul (continuous_cos.comp continuous_snd) :)
  · exact (h.continuous_R.mul (continuous_sin.comp continuous_snd) :)
  · exact h.continuous_z

/-- The torus map is `2π`-periodic in `θ`. -/
theorem PeriodicTorus.torusMap_add_θ (h : PeriodicTorus R z) (p : ℝ × ℝ) :
    torusMap R z (p + (2 * π, 0)) = torusMap R z p := by
  simp [torusMap, h.per_θ_R, h.per_θ_z]

/-- The torus map is `2π`-periodic in `φ`. -/
theorem PeriodicTorus.torusMap_add_φ (h : PeriodicTorus R z) (p : ℝ × ℝ) :
    torusMap R z (p + (0, 2 * π)) = torusMap R z p := by
  simp [torusMap, cylPoint, h.per_φ_R, h.per_φ_z]

/-- **The descended map lifts to the torus map**: `torusEmb R z (↑θ, ↑φ) = K (θ, φ)`. -/
theorem PeriodicTorus.torusEmb_proj (h : PeriodicTorus R z) (p : ℝ × ℝ) :
    torusEmb R z (torusProj p) = torusMap R z p :=
  torusLift_proj h.torusMap_add_θ h.torusMap_add_φ p

/-- The descended map at the classes of `θ` and `φ`. -/
theorem PeriodicTorus.torusEmb_coe (h : PeriodicTorus R z) (θ φ : ℝ) :
    torusEmb R z ((θ : AddCircle (2 * π)), (φ : AddCircle (2 * π))) = torusMap R z (θ, φ) :=
  h.torusEmb_proj (θ, φ)

/-- **The descended torus map is continuous.** -/
theorem PeriodicTorus.continuous_torusEmb (h : PeriodicTorus R z) :
    Continuous (torusEmb R z) :=
  continuous_torusLift h.torusMap_add_θ h.torusMap_add_φ h.continuous_torusMap

/-- **The surface is the image of the torus**: the range of the descended map is the range of
the torus map. -/
theorem PeriodicTorus.range_torusEmb (h : PeriodicTorus R z) :
    Set.range (torusEmb R z) = Set.range (torusMap R z) :=
  range_torusLift h.torusMap_add_θ h.torusMap_add_φ

/-- **The surface of a continuous doubly periodic torus is compact** (no injectivity needed). -/
theorem PeriodicTorus.isCompact_range_torusMap (h : PeriodicTorus R z) :
    IsCompact (Set.range (torusMap R z)) := by
  rw [← h.range_torusEmb]
  exact isCompact_range h.continuous_torusEmb

/-- **Injectivity on the torus is injectivity modulo the periods on the plane.** -/
theorem PeriodicTorus.injective_torusEmb_iff (h : PeriodicTorus R z) :
    Function.Injective (torusEmb R z) ↔ InjectiveModPeriods R z := by
  constructor
  · intro hinj p q hpq
    refine torusProj_eq_iff.1 (hinj ?_)
    rw [h.torusEmb_proj, h.torusEmb_proj, hpq]
  · intro hinj x y hxy
    obtain ⟨p, rfl⟩ := torusProj_surjective x
    obtain ⟨q, rfl⟩ := torusProj_surjective y
    rw [h.torusEmb_proj, h.torusEmb_proj] at hxy
    exact torusProj_eq_iff.2 (hinj p q hxy)

/-- **A torus that is injective modulo the periods is topologically embedded**: the descended
map is a closed embedding of the 2-torus in space. -/
theorem PeriodicTorus.isClosedEmbedding_torusEmb (h : PeriodicTorus R z)
    (hinj : InjectiveModPeriods R z) : Topology.IsClosedEmbedding (torusEmb R z) :=
  h.continuous_torusEmb.isClosedEmbedding (h.injective_torusEmb_iff.2 hinj)

/-- **The surface is homeomorphic to the 2-torus**: for a torus that is injective modulo the
periods, the homeomorphism of the angle torus onto the surface `Set.range (torusMap R z)`. -/
noncomputable def PeriodicTorus.homeomorph (h : PeriodicTorus R z)
    (hinj : InjectiveModPeriods R z) : AngleTorus ≃ₜ Set.range (torusMap R z) :=
  (h.isClosedEmbedding_torusEmb hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr h.range_torusEmb)

/-- The homeomorphism onto the surface is the descended torus map. -/
theorem PeriodicTorus.homeomorph_apply (h : PeriodicTorus R z)
    (hinj : InjectiveModPeriods R z) (x : AngleTorus) :
    (h.homeomorph hinj x : Space) = torusEmb R z x := rfl

end Topology

/-! ## Cylindrical criteria -/

/-- Two angles with the same cosine and sine differ by an integer multiple of `2π`. -/
theorem exists_int_of_cos_sin_eq {φ φ' : ℝ} (hc : cos φ = cos φ') (hs : sin φ = sin φ') :
    ∃ n : ℤ, φ' = φ + 2 * π * n := by
  have h1 : cos (φ' - φ) = 1 := by
    rw [cos_sub, ← hc, ← hs]
    nlinarith [sin_sq_add_cos_sq φ]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1
  exact ⟨n, by linarith⟩

/-- **Cylindrical points off the axis determine their coordinates**: for `R, R' > 0`,
`cylPoint R φ z = cylPoint R' φ' z'` exactly when `R = R'`, `z = z'` and `φ' - φ ∈ 2πℤ`. -/
theorem cylPoint_eq_iff_of_pos {R R' φ φ' z z' : ℝ} (hR : 0 < R) (hR' : 0 < R') :
    cylPoint R φ z = cylPoint R' φ' z' ↔ R = R' ∧ z = z' ∧ ∃ n : ℤ, φ' = φ + 2 * π * n := by
  constructor
  · intro h
    have h0 : R * cos φ = R' * cos φ' := by
      simpa [cylPoint] using congrArg (fun x : Space => x 0) h
    have h1 : R * sin φ = R' * sin φ' := by
      simpa [cylPoint] using congrArg (fun x : Space => x 1) h
    have h2 : z = z' := by simpa [cylPoint] using congrArg (fun x : Space => x 2) h
    have hsq : R ^ 2 = R' ^ 2 := by
      have e1 : R ^ 2 = (R * cos φ) ^ 2 + (R * sin φ) ^ 2 := by
        nlinarith [sin_sq_add_cos_sq φ]
      have e2 : R' ^ 2 = (R' * cos φ') ^ 2 + (R' * sin φ') ^ 2 := by
        nlinarith [sin_sq_add_cos_sq φ']
      rw [e1, e2, h0, h1]
    have hRR : R = R' := by nlinarith
    subst hRR
    exact ⟨rfl, h2, exists_int_of_cos_sin_eq (mul_left_cancel₀ hR.ne' h0)
      (mul_left_cancel₀ hR.ne' h1)⟩
  · rintro ⟨rfl, rfl, n, rfl⟩
    have hc : cos (φ + 2 * π * n) = cos φ := by
      rw [mul_comm]; exact Real.cos_add_int_mul_two_pi φ n
    have hs : sin (φ + 2 * π * n) = sin φ := by
      rw [mul_comm]; exact Real.sin_add_int_mul_two_pi φ n
    simp [cylPoint, hc, hs]

/-- **A torus with `R > 0` does not meet the axis**: the squared distance of `K (θ, φ)` from
the `z`-axis is `R²`. -/
theorem torusMap_axis_dist (R z : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    (torusMap R z p) 0 ^ 2 + (torusMap R z p) 1 ^ 2 = R p.1 p.2 ^ 2 := by
  simp only [torusMap, cylPoint]
  simp
  nlinarith [sin_sq_add_cos_sq p.2]

/-- The points of a torus with `R > 0` are off the axis: `x₀² + x₁² > 0` on the surface. -/
theorem torusMap_axis_dist_pos {R z : ℝ → ℝ → ℝ} (hR : ∀ θ φ, 0 < R θ φ) {x : Space}
    (hx : x ∈ Set.range (torusMap R z)) : 0 < x 0 ^ 2 + x 1 ^ 2 := by
  obtain ⟨p, rfl⟩ := hx
  rw [torusMap_axis_dist]
  exact pow_pos (hR p.1 p.2) 2

section Sections

variable {R z : ℝ → ℝ → ℝ}

/-- **Injectivity modulo the periods, by sections.** For a continuous doubly periodic torus
with `R > 0`, the torus map is injective modulo the periods exactly when every poloidal
section `θ ↦ (R θ φ, z θ φ)` is injective modulo `2π`. (The toroidal parameter is the
geometric toroidal angle, so points with different `φ` modulo `2π` are different.) -/
theorem PeriodicTorus.injectiveModPeriods_iff_sections (h : PeriodicTorus R z)
    (hR : ∀ θ φ, 0 < R θ φ) :
    InjectiveModPeriods R z ↔
      ∀ θ θ' φ, R θ φ = R θ' φ → z θ φ = z θ' φ → ∃ m : ℤ, θ' = θ + 2 * π * m := by
  constructor
  · intro hinj θ θ' φ h1 h2
    obtain ⟨m, n, hmn⟩ := hinj (θ, φ) (θ', φ) (by simp [torusMap, h1, h2])
    exact ⟨m, by simpa using congrArg Prod.fst hmn⟩
  · intro hsec p q hpq
    obtain ⟨hRR, hzz, n, hn⟩ := (cylPoint_eq_iff_of_pos (hR _ _) (hR _ _)).1 hpq
    have hRn : R q.1 q.2 = R q.1 p.2 := by
      rw [hn, mul_comm]
      exact (show Function.Periodic (R q.1) (2 * π) from fun t => h.per_φ_R q.1 t).int_mul n p.2
    have hzn : z q.1 q.2 = z q.1 p.2 := by
      rw [hn, mul_comm]
      exact (show Function.Periodic (z q.1) (2 * π) from fun t => h.per_φ_z q.1 t).int_mul n p.2
    obtain ⟨m, hm⟩ := hsec p.1 q.1 p.2 (hRR.trans hRn) (hzz.trans hzn)
    exact ⟨m, n, Prod.ext (by simpa using hm) (by simpa using hn)⟩

end Sections

/-! ## The immersion condition -/

section Immersion

variable {R z : ℝ → ℝ → ℝ}

/-- The differential of the torus map on `∂_θ`:
`∂_θ K = (∂_θ R cos φ, ∂_θ R sin φ, ∂_θ z)`. -/
theorem PeriodicC2Torus.fderiv_torusMap_θ (h : PeriodicC2Torus R z) (θ φ : ℝ) :
    fderiv ℝ (torusMap R z) (θ, φ) (1, 0) =
      WithLp.toLp 2 ![deriv (fun t => R t φ) θ * cos φ, deriv (fun t => R t φ) θ * sin φ,
        deriv (fun t => z t φ) θ] := by
  have hK : HasFDerivAt (torusMap R z) (fderiv ℝ (torusMap R z) (θ, φ)) (θ, φ) :=
    (h.contDiff_torusMap.differentiable (by norm_num) (θ, φ)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (t, φ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ φ)
  have hc : HasDerivAt (fun t => torusMap R z (t, φ))
      (fderiv ℝ (torusMap R z) (θ, φ) (1, 0)) θ :=
    HasFDerivAt.comp_hasDerivAt (l := torusMap R z) θ hK h1
  have hR : HasDerivAt (fun t => R t φ) (deriv (fun t => R t φ) θ) θ :=
    ((h.contDiff_R.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
      θ).hasDerivAt
  have hz : HasDerivAt (fun t => z t φ) (deriv (fun t => z t φ) θ) θ :=
    ((h.contDiff_z.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
      θ).hasDerivAt
  exact hc.unique (hasDerivAt_poloidalLoop hR hz)

/-- The differential of the torus map on `∂_φ`:
`∂_φ K = (∂_φ R cos φ - R sin φ, ∂_φ R sin φ + R cos φ, ∂_φ z)`. -/
theorem PeriodicC2Torus.fderiv_torusMap_φ (h : PeriodicC2Torus R z) (θ φ : ℝ) :
    fderiv ℝ (torusMap R z) (θ, φ) (0, 1) =
      WithLp.toLp 2 ![deriv (fun t => R θ t) φ * cos φ - R θ φ * sin φ,
        deriv (fun t => R θ t) φ * sin φ + R θ φ * cos φ, deriv (fun t => z θ t) φ] := by
  have hK : HasFDerivAt (torusMap R z) (fderiv ℝ (torusMap R z) (θ, φ)) (θ, φ) :=
    (h.contDiff_torusMap.differentiable (by norm_num) (θ, φ)).hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (θ, t)) ((0 : ℝ), (1 : ℝ)) φ :=
    (hasDerivAt_const φ θ).prodMk (hasDerivAt_id φ)
  have hc : HasDerivAt (fun t => torusMap R z (θ, t))
      (fderiv ℝ (torusMap R z) (θ, φ) (0, 1)) φ :=
    HasFDerivAt.comp_hasDerivAt (l := torusMap R z) φ hK h1
  have hR : HasDerivAt (fun t => R θ t) (deriv (fun t => R θ t) φ) φ :=
    ((h.contDiff_R.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
      φ).hasDerivAt
  have hz : HasDerivAt (fun t => z θ t) (deriv (fun t => z θ t) φ) φ :=
    ((h.contDiff_z.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
      φ).hasDerivAt
  have h3 := hasDerivAt_space3 (hR.mul (hasDerivAt_cos φ)) (hR.mul (hasDerivAt_sin φ)) hz
  rw [hc.unique h3]
  ext i
  fin_cases i <;> simp
  ring

/-- **The immersion condition in cylindrical form.** For a `C²` torus and a parameter with
`R > 0`, the differential of the torus map is injective (`∂_θ K` and `∂_φ K` are linearly
independent) exactly when `(∂_θ R, ∂_θ z) ≠ 0`. -/
theorem PeriodicC2Torus.injective_fderiv_torusMap_iff (h : PeriodicC2Torus R z) {θ φ : ℝ}
    (hR : 0 < R θ φ) :
    Function.Injective (fderiv ℝ (torusMap R z) (θ, φ)) ↔
      ¬ (deriv (fun t => R t φ) θ = 0 ∧ deriv (fun t => z t φ) θ = 0) := by
  set L := fderiv ℝ (torusMap R z) (θ, φ) with hL
  have hθ := h.fderiv_torusMap_θ θ φ
  have hφ := h.fderiv_torusMap_φ θ φ
  rw [← hL] at hθ hφ
  have hlin : ∀ a b : ℝ, L (a, b) = a • L (1, 0) + b • L (0, 1) := fun a b => by
    rw [← map_smul, ← map_smul, ← map_add]
    simp
  constructor
  · rintro hinj ⟨h1, h2⟩
    have h0 : L (1, 0) = L 0 := by
      rw [hθ, h1, h2, map_zero]
      ext i
      fin_cases i <;> simp
    have := congrArg Prod.fst (hinj h0)
    simp at this
  · intro hne
    refine (injective_iff_map_eq_zero L).2 fun v hv => ?_
    obtain ⟨a, b⟩ := v
    rw [hlin, hθ, hφ] at hv
    have e0 : a * (deriv (fun t => R t φ) θ * cos φ)
        + b * (deriv (fun t => R θ t) φ * cos φ - R θ φ * sin φ) = 0 := by
      simpa using congrArg (fun x : Space => x 0) hv
    have e1 : a * (deriv (fun t => R t φ) θ * sin φ)
        + b * (deriv (fun t => R θ t) φ * sin φ + R θ φ * cos φ) = 0 := by
      simpa using congrArg (fun x : Space => x 1) hv
    have e2 : a * deriv (fun t => z t φ) θ + b * deriv (fun t => z θ t) φ = 0 := by
      simpa using congrArg (fun x : Space => x 2) hv
    have hsc := sin_sq_add_cos_sq φ
    have hbR : b * R θ φ = 0 := by
      linear_combination cos φ * e1 - sin φ * e0 - b * R θ φ * hsc
    have hb : b = 0 := (mul_eq_zero.1 hbR).resolve_right hR.ne'
    subst hb
    simp only [zero_mul, add_zero] at e0 e1 e2
    have haR : a * deriv (fun t => R t φ) θ = 0 := by
      linear_combination cos φ * e0 + sin φ * e1 - a * deriv (fun t => R t φ) θ * hsc
    by_contra hv0
    have ha : a ≠ 0 := fun ha => hv0 (by rw [ha]; rfl)
    exact hne ⟨(mul_eq_zero.1 haR).resolve_left ha, (mul_eq_zero.1 e2).resolve_left ha⟩

end Immersion

/-! ## Embedded tori -/

/-- An **embedded torus**: a doubly periodic `C²` torus whose torus map is injective modulo
the periods and an immersion (its differential is injective at every parameter, i.e. `∂_θ K`
and `∂_φ K` are linearly independent). Then the descended map `torusEmb R z` is a `C²` embedding
of the 2-torus in space (`EmbeddedTorus.isSmoothEmbedding_torusEmb`). -/
structure EmbeddedTorus (R z : ℝ → ℝ → ℝ) : Prop extends PeriodicC2Torus R z where
  /-- The torus map is injective modulo the periods. -/
  injective : InjectiveModPeriods R z
  /-- The differential of the torus map is injective at every parameter. -/
  immersion : ∀ p, Function.Injective (fderiv ℝ (torusMap R z) p)

section Embedded

variable {R z : ℝ → ℝ → ℝ}

/-- **The usable criterion for cylindrical tori.** A doubly periodic `C²` torus with `R > 0`,
whose poloidal sections `θ ↦ (R θ φ, z θ φ)` are injective modulo `2π` and regular
(`(∂_θ R, ∂_θ z) ≠ 0`), is an embedded torus. -/
theorem EmbeddedTorus.of_sections (h : PeriodicC2Torus R z) (hR : ∀ θ φ, 0 < R θ φ)
    (hinj : ∀ θ θ' φ, R θ φ = R θ' φ → z θ φ = z θ' φ → ∃ m : ℤ, θ' = θ + 2 * π * m)
    (himm : ∀ θ φ, ¬ (deriv (fun t => R t φ) θ = 0 ∧ deriv (fun t => z t φ) θ = 0)) :
    EmbeddedTorus R z :=
  { h with
    injective := (h.periodicTorus.injectiveModPeriods_iff_sections hR).2 hinj
    immersion := fun p => (h.injective_fderiv_torusMap_iff (hR p.1 p.2)).2 (himm p.1 p.2) }

/-- An embedded torus is a continuous doubly periodic torus. -/
theorem EmbeddedTorus.periodicTorus (h : EmbeddedTorus R z) : PeriodicTorus R z :=
  h.toPeriodicC2Torus.periodicTorus

/-- The descended map of an embedded torus is injective. -/
theorem EmbeddedTorus.injective_torusEmb (h : EmbeddedTorus R z) :
    Function.Injective (torusEmb R z) :=
  h.periodicTorus.injective_torusEmb_iff.2 h.injective

/-- The descended map of an embedded torus is a closed topological embedding. -/
theorem EmbeddedTorus.isClosedEmbedding_torusEmb (h : EmbeddedTorus R z) :
    Topology.IsClosedEmbedding (torusEmb R z) :=
  h.periodicTorus.isClosedEmbedding_torusEmb h.injective

end Embedded

/-! ## Smoothness on the torus -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quotient map of the plane onto the angle torus is a local diffeomorphism, for every
differentiability order. -/
theorem isLocalDiffeomorph_torusProj (n : WithTop ℕ∞) :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) n torusProj := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (AddCircle.isLocalDiffeomorph_coe (2 * π) n).prodMap
    (AddCircle.isLocalDiffeomorph_coe (2 * π) n)

/-- The quotient map onto the angle torus has differential the identity of `ℝ × ℝ`, the
tangent spaces of the torus being read in its charts (local lifts). -/
theorem mfderiv_torusProj (p : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) torusProj p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  rw [torusProj, mfderiv_prodMap (AddCircle.hasMFDerivAt_coe (2 * π) p.1).mdifferentiableAt
    (AddCircle.hasMFDerivAt_coe (2 * π) p.2).mdifferentiableAt, AddCircle.mfderiv_coe,
    AddCircle.mfderiv_coe]
  refine ContinuousLinearMap.ext fun v => ?_
  exact Prod.ext (ContinuousLinearMap.id_apply (R₁ := ℝ) (v.1 : ℝ))
    (ContinuousLinearMap.id_apply (R₁ := ℝ) (v.2 : ℝ))

/-- The quotient map onto the angle torus is differentiable with differential the identity. -/
theorem hasMFDerivAt_torusProj (p : ℝ × ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) torusProj p
      (ContinuousLinearMap.id ℝ (ℝ × ℝ)) := by
  have hd := ((isLocalDiffeomorph_torusProj 1 p).mdifferentiableAt one_ne_zero).hasMFDerivAt
  rwa [mfderiv_torusProj] at hd

/-- **Descent of smoothness.** The descent of a doubly periodic `C^n` function on the plane is
a `C^n` function on the angle torus. -/
theorem contMDiff_torusLift {f : ℝ × ℝ → E} {n : WithTop ℕ∞}
    (hθ : ∀ p, f (p + (2 * π, 0)) = f p) (hφ : ∀ p, f (p + (0, 2 * π)) = f p)
    (hf : ContDiff ℝ n f) : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, E) n (torusLift f) := by
  rw [← (isLocalDiffeomorph_torusProj n).contMDiff_comp_iff torusProj_surjective le_rfl,
    torusLift_comp_proj hθ hφ]
  exact hf.contMDiff

/-- **Descent of the differential.** If a doubly periodic function on the plane has derivative
`L` at `p`, its descent has the differential `L` at the class of `p`. -/
theorem hasMFDerivAt_torusLift {f : ℝ × ℝ → E} (hθ : ∀ p, f (p + (2 * π, 0)) = f p)
    (hφ : ∀ p, f (p + (0, 2 * π)) = f p) {L : ℝ × ℝ →L[ℝ] E} {p : ℝ × ℝ}
    (hf : HasFDerivAt f L p) :
    HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, E) (torusLift f) (torusProj p) L := by
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (torusLift f ∘ torusProj) p L := by
    rw [torusLift_comp_proj hθ hφ]
    exact hf.hasMFDerivAt
  have hg : MDifferentiableAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, E) (torusLift f) (torusProj p) :=
    ((isLocalDiffeomorph_torusProj 1 p).mdifferentiableAt_comp_iff one_ne_zero).1
      hcomp.mdifferentiableAt
  have hc := mfderiv_comp p hg (hasMFDerivAt_torusProj p).mdifferentiableAt
  rw [hcomp.mfderiv, mfderiv_torusProj] at hc
  have hL : mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, E) (torusLift f) (torusProj p) = L := hc.symm
  rw [← hL]
  exact hg.hasMFDerivAt

/-- **The differential of a function on the torus is the derivative of its lift**: if `g` has
the differential `L` at the class of `p`, then `g ∘ torusProj` has the derivative `L` at `p`. -/
theorem hasFDerivAt_comp_torusProj {g : AngleTorus → E} {L : ℝ × ℝ →L[ℝ] E} {p : ℝ × ℝ}
    (hg : HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, E) g (torusProj p) L) :
    HasFDerivAt (g ∘ torusProj) L p :=
  (hg.comp p (hasMFDerivAt_torusProj p)).hasFDerivAt

/-- The quotient map is invariant under the poloidal period. -/
theorem torusProj_add_θ (p : ℝ × ℝ) : torusProj (p + (2 * π, 0)) = torusProj p :=
  (torusProj_eq_iff.2 ⟨1, 0, by simp⟩).symm

/-- The quotient map is invariant under the toroidal period. -/
theorem torusProj_add_φ (p : ℝ × ℝ) : torusProj (p + (0, 2 * π)) = torusProj p :=
  (torusProj_eq_iff.2 ⟨0, 1, by simp⟩).symm

variable {R z : ℝ → ℝ → ℝ}

/-- **The descended torus map of a `C²` torus is `C²`** as a map of manifolds. -/
theorem PeriodicC2Torus.contMDiff_torusEmb (h : PeriodicC2Torus R z) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2 (torusEmb R z) :=
  contMDiff_torusLift h.torusMap_add_θ h.torusMap_add_φ h.contDiff_torusMap

/-- **The differential of the descended torus map** at the class of `p` is the derivative of
the torus map at `p`. -/
theorem PeriodicC2Torus.mfderiv_torusEmb (h : PeriodicC2Torus R z) (p : ℝ × ℝ) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) (torusEmb R z) (torusProj p) =
      fderiv ℝ (torusMap R z) p :=
  (hasMFDerivAt_torusLift h.torusMap_add_θ h.torusMap_add_φ
    (h.contDiff_torusMap.differentiable (by norm_num) p).hasFDerivAt).mfderiv

/-- **The descended map of an embedded torus is a `C²` immersion** of the 2-torus in space, in
the sense of Mathlib (`Manifold.IsImmersion`, slice charts). -/
theorem EmbeddedTorus.isImmersion_torusEmb (h : EmbeddedTorus R z) :
    Manifold.IsImmersion (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2 (torusEmb R z) :=
  h.toPeriodicC2Torus.contMDiff_torusEmb.isImmersion_of_injective_mfderiv (by norm_num)
    fun x => by
      obtain ⟨p, rfl⟩ := torusProj_surjective x
      rw [h.toPeriodicC2Torus.mfderiv_torusEmb]
      exact h.immersion p

/-- **An embedded torus is a `C²` embedded torus**: the descended map is a `C²` embedding of
the manifold `AddCircle (2π) × AddCircle (2π)` in space (`Manifold.IsSmoothEmbedding`: an
immersion that is a topological embedding). -/
theorem EmbeddedTorus.isSmoothEmbedding_torusEmb (h : EmbeddedTorus R z) :
    Manifold.IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, Space) 2 (torusEmb R z) :=
  ⟨h.isImmersion_torusEmb, h.isClosedEmbedding_torusEmb.isEmbedding⟩

end Smooth

/-! ## The periods on the torus -/

section Periods

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {U : Set Space}

/-- The **pull-back of `B♭` as a 1-form on the angle torus**: the descent of `torusForm`. Its
value at a point is a linear form on `ℝ × ℝ`, the tangent space of the torus read in the angle
coordinates; `fst` is `dθ` and `snd` is `dφ`. -/
noncomputable def torusFormT (B : Space → Space) (R z : ℝ → ℝ → ℝ) :
    AngleTorus → (ℝ × ℝ →L[ℝ] ℝ) :=
  torusLift (torusForm B R z)

/-- The form on the torus at the class of `p` is the pulled-back form at `p`. -/
theorem PeriodicC2Torus.torusFormT_proj (h : PeriodicC2Torus R z) (B : Space → Space)
    (p : ℝ × ℝ) : torusFormT B R z (torusProj p) = torusForm B R z p :=
  torusLift_proj (h.torusForm_add_θ B) (h.torusForm_add_φ B) p

/-- The form on the torus is continuous when `B` is continuous at the points of the surface. -/
theorem PeriodicC2Torus.continuous_torusFormT (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p)) : Continuous (torusFormT B R z) :=
  continuous_torusLift (h.torusForm_add_θ B) (h.torusForm_add_φ B) (h.continuous_torusForm hBc)

/-- **The de Rham class of `B♭` on the flux surface, on the torus.** For a `C²` doubly periodic
torus and a field that is `C¹` and curl-free on an open set containing the surface, there is a
`C¹` function `g` on the angle torus with `β = (P_θ/2π) dθ + (P_φ/2π) dφ + dg`: the differential
of `g` at every point `x` is `torusFormT B R z x - (P_θ/2π) dθ - (P_φ/2π) dφ`. -/
theorem PeriodicC2Torus.exists_potential_on_torus (h : PeriodicC2Torus R z)
    (hUo : IsOpen U) (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0)
    (hU : ∀ p, torusMap R z p ∈ U) (θ₀ φ₀ : ℝ) :
    ∃ g : AngleTorus → ℝ, ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) 1 g ∧
      ∀ x, HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) g x (torusFormT B R z x
        - (poloidalPeriod B R z φ₀ / (2 * π)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (toroidalPeriod B R z θ₀ / (2 * π)) • ContinuousLinearMap.snd ℝ ℝ ℝ) := by
  obtain ⟨g, hgθ, hgφ, hg⟩ := h.exists_periodic_potential_of_curl_eq_zero hUo hB hcurl hU θ₀ φ₀
  have hBc := continuousAt_of_contDiffOn_torus hUo hB hU
  have hC1 : ContDiff ℝ 1 g := by
    refine contDiff_one_iff_fderiv.2 ⟨fun p => (hg p).differentiableAt, ?_⟩
    rw [show fderiv ℝ g = fun p => torusForm B R z p
        - (poloidalPeriod B R z φ₀ / (2 * π)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        - (toroidalPeriod B R z θ₀ / (2 * π)) • ContinuousLinearMap.snd ℝ ℝ ℝ from
      funext fun p => (hg p).fderiv]
    exact ((h.continuous_torusForm hBc).sub continuous_const).sub continuous_const
  refine ⟨torusLift g, contMDiff_torusLift hgθ hgφ hC1, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := torusProj_surjective x
  rw [h.torusFormT_proj]
  exact hasMFDerivAt_torusLift hgθ hgφ (hg p)

/-- **Uniqueness of the class on the torus.** If `β = a dθ + b dφ + dg` on the angle torus for
a differentiable function `g` on the torus, then the poloidal period is `2π a` (at every `φ`)
and the toroidal period is `2π b` (at every `θ`). In particular `a dθ + b dφ` is the
differential of a function on the torus only for `a = b = 0`. -/
theorem PeriodicC2Torus.periods_eq_of_potential_on_torus (h : PeriodicC2Torus R z)
    (hBc : ∀ p, ContinuousAt B (torusMap R z p)) {a b : ℝ} {g : AngleTorus → ℝ}
    (hg : ∀ x, HasMFDerivAt (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) g x (torusFormT B R z x
      - a • ContinuousLinearMap.fst ℝ ℝ ℝ - b • ContinuousLinearMap.snd ℝ ℝ ℝ)) (θ φ : ℝ) :
    poloidalPeriod B R z φ = 2 * π * a ∧ toroidalPeriod B R z θ = 2 * π * b := by
  refine h.periods_eq_of_periodic_potential hBc (g := g ∘ torusProj)
    (fun p => congrArg g (torusProj_add_θ p)) (fun p => congrArg g (torusProj_add_φ p))
    (fun p => ?_) θ φ
  have := hasFDerivAt_comp_torusProj (hg (torusProj p))
  rwa [h.torusFormT_proj] at this

end Periods

/-! ## Contract-facing corollaries -/

section Contract

variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- **The surface of a `FieldTorus` is compact.** -/
theorem _root_.PlasmaLean.Contract.FieldTorus.isCompact_range_torusMap
    (hT : FieldTorus B R z ι) : IsCompact (Set.range (torusMap R z)) :=
  hT.periodicTorus.isCompact_range_torusMap

/-- **The surface of a `FieldTorus` does not meet the axis**: `x₀² + x₁² > 0` on it. -/
theorem _root_.PlasmaLean.Contract.FieldTorus.axis_dist_pos (hT : FieldTorus B R z ι)
    {x : Space} (hx : x ∈ Set.range (torusMap R z)) : 0 < x 0 ^ 2 + x 1 ^ 2 :=
  torusMap_axis_dist_pos hT.R_pos hx

/-- **A `FieldTorus` that is injective modulo the periods is homeomorphic to the 2-torus**:
the homeomorphism of the angle torus onto the surface. By
`PeriodicTorus.injectiveModPeriods_iff_sections` the hypothesis says that the poloidal sections
are injective modulo `2π`. -/
noncomputable def _root_.PlasmaLean.Contract.FieldTorus.homeomorph (hT : FieldTorus B R z ι)
    (hinj : InjectiveModPeriods R z) : AngleTorus ≃ₜ Set.range (torusMap R z) :=
  hT.periodicTorus.homeomorph hinj

/-- **A `FieldTorus` with `C²` profiles and injective, regular poloidal sections is an
embedded torus.** -/
theorem _root_.PlasmaLean.Contract.FieldTorus.embeddedTorus (hT : FieldTorus B R z ι)
    (hR : ContDiff ℝ 2 (fun p : ℝ × ℝ => R p.1 p.2))
    (hz : ContDiff ℝ 2 (fun p : ℝ × ℝ => z p.1 p.2))
    (hinj : ∀ θ θ' φ, R θ φ = R θ' φ → z θ φ = z θ' φ → ∃ m : ℤ, θ' = θ + 2 * π * m)
    (himm : ∀ θ φ, ¬ (deriv (fun t => R t φ) θ = 0 ∧ deriv (fun t => z t φ) θ = 0)) :
    EmbeddedTorus R z :=
  EmbeddedTorus.of_sections (hT.periodicC2Torus hR hz) hT.R_pos hinj himm

/-- **The surface of an embedded torus is compact and closed**, and it is the image of the
`C²` embedding `torusEmb R z`. -/
theorem EmbeddedTorus.isCompact_isClosed_range (h : EmbeddedTorus R z) :
    IsCompact (Set.range (torusMap R z)) ∧ IsClosed (Set.range (torusMap R z)) ∧
      Set.range (torusEmb R z) = Set.range (torusMap R z) :=
  ⟨h.periodicTorus.isCompact_range_torusMap, h.periodicTorus.isCompact_range_torusMap.isClosed,
    h.periodicTorus.range_torusEmb⟩

end Contract

end PlasmaLean.Forms
