/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMEnergy
public import PlasmaLean.Theory.Fields.FormLoopCurrentInterval
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Topology.UnitInterval

/-!
# The anti-self-dual lift as the curvature of a `U(1)` connection: periods and cocycle data

Source: `sources/fusion_complex_geometry_reproducibility/continuation_geometry.tex`, paragraph
"Integral periods and the holomorphic line bundle" (lines 37–47): "Since `H²(Ω; ℝ) = 0`, the
only possible nonzero period of `ℱ` on `M` is `(1/2π) ∫_{γ × S¹_ℓ} ℱ = -Γℓ/2π`. For the
normalized seed, `Γ = 2π` and `ℓ = 1` make this period integral." and "Choose a global one-form
`a` on `Ω` with `da = β`. Locally write `α = dΦ_i` and set `A_i = a - Φ_i dt`. Then
`dA_i = ℱ`. A potential branch change by `2πn` changes `A_i` by `-2πn dt`, which has the unitary
transition `e^{2πint}` when `ℓ = 1`. With convention `∇ = d - iA`, the curvature is `-iℱ` and
`c₁ = [ℱ/(2π)]`." Assessment claim S-13 in `notes/theory/fusion-complex-geometry-assessment.md`.
This file continues `Theory/Fields/FormHYMEnergy` (the connection on the trivial bundle).

## Conventions

* The lift is `ℱ = π^*ω - π^*(⋆ω) ∧ dτ` (`hymLift`) on `ℝ³ × ℝ` (`LiftSpace`).
* **Orientation of the torus `γ × S¹`.** It is parametrised by `(s, τ) ↦ (γ s, τ)` and oriented
  by the ordered frame `(∂_s, ∂_τ)`: `torusPeriod F γ a b ℓ` is the iterated interval integral
  of `F((γ' s, 0), (0, 1))` over `s ∈ [a, b]`, `τ ∈ [0, ℓ]`. With this orientation the period
  of the lift is `-ℓ ∮_γ B · dl` (sign `-`, as in the source). The opposite orientation
  `(∂_τ, ∂_s)` gives `+`.
* `chernNumber F γ a b ℓ = torusPeriod F γ a b ℓ / 2π`: a real number.
* Connection convention `∇ = d - i𝒜ᵢ`; transition functions `gᵢⱼ` with values in Mathlib's
  `Circle`; compatibility `𝒜ᵢ - 𝒜ⱼ = dh` where locally `gᵢⱼ = exp(ih)` (`Circle.exp h`).

## What is proved

**1. Periods** (no hypothesis on the field or the curve unless stated).
* `torusPeriod_hymLift`, `torusPeriod_hymLift_fluxField`: `∫_{γ × [0, ℓ]} ℱ = -ℓ ∫_γ ⋆ω
  = -ℓ ∮_γ B · dl`. Both sides are the same interval integral, so the identity holds also
  when it is not integrable; `intervalIntegrable_circulation` gives integrability for a `C¹`
  curve and a continuous field.
* `torusPeriod_hymLift_eq_periodHom`: the period is `-ℓ` times TauCeti's de Rham period of
  `B♭` on the class of the loop (curl-free `C¹` field).
* `torusPeriod_hymLift_poloidal`, `chernNumber_hymLift_poloidal` (Ampère): over the poloidal
  loop of the contract the period is `-ℓ μ₀ I` and the Chern number `-ℓ μ₀ I / 2π`,
  `I = loopCurrent`.
* `VacuumField.torusPeriod_hymLift_eq_zero`: on a simply connected region all these periods
  vanish.
* `torusPeriod_hymLift_mem_iff`, `chernNumber_hymLift_mem_int_iff`: the period is in `2πℤ`
  (the Chern number is an integer) exactly when `ℓ ∮_γ B · dl ∈ 2πℤ`.

**2. Cocycle data.**
* `liftConnection_sub_eq_fderiv`: two local connections `π^*Aₖ - (π^*φₖ) dτ` whose vector
  potentials differ by `d lam` and scalar potentials by `c` differ by `d(lam - cτ)`;
  `circleExp_transPotential_periodic_iff`: `exp(i(lam - cτ))` is `ℓ`-periodic in `τ` exactly
  when `cℓ ∈ 2πℤ`.
* `LiftBundleData ι Ω F`: cocycle data of a `U(1)` line bundle with connection of curvature
  `F` over `Ω × ℝ` in cylinder charts `base i × ℝ`: local `C¹` connection forms with
  `d(conn i) = F`, circle-valued transition functions with the cocycle condition, and the
  compatibility above. `LiftBundleData.IsPeriodic L ℓ`: the data are invariant under
  `τ ↦ τ + ℓ`, that is, they are data on `Ω × S¹_ℓ` with charts `base i × S¹_ℓ`.
* `LiftBundleData.ofPotentials`: the source's construction. One vector potential and a family
  of local scalar potentials `φᵢ` give data with `gᵢⱼ = exp(i(φⱼ - φᵢ)τ)`;
  `ofPotentials_isPeriodic_iff`: they are `ℓ`-periodic exactly when every jump satisfies
  `(φⱼ - φᵢ)ℓ ∈ 2πℤ`.
* `VacuumForm.exists_liftBundleData`: on a star-convex region, one chart, transition function
  `1`, periodic for every `ℓ` (the trivial bundle; no quantisation).
* The wire field with two charts is the instance `Sanity.FormHYMBundle.wireBundle`.

**3. Integrality (Chern numbers).**
* `LiftBundleData.IsPeriodic.fibreIntegral_sub`: in two charts the integrals of the
  `dτ`-component of the connection over a circle fibre differ by an element of `2πℤ` (the
  winding number of the periodic transition function).
* `LiftBundleData.IsPeriodic.integral_rect`: Stokes' theorem over `γ([s₀, s₁]) × [0, ℓ]` in one
  chart.
* `LiftBundleData.IsPeriodic.torusPeriod_mem`, `chernNumber_mem_int`: **for every `ℓ`-periodic
  `LiftBundleData` with curvature `F` (any index type, any number of charts) and every closed
  `C¹` loop `γ` in `Ω`, `∫_{γ × [0, ℓ]} F ∈ 2πℤ`**: the Chern number over `γ × S¹_ℓ` is an
  integer.
* `LiftBundleData.not_isPeriodic_of_torusPeriod`, `IsPeriodic.circulation_mem`: the converse
  obstruction. If `ℓ ∮_γ B · dl ∉ 2πℤ` for one loop, no `ℓ`-periodic data with curvature the
  lift exist.

**Integrability.** In part 3 the inner integrals are integrals of continuous functions and the
outer integrand is proved interval integrable on every piece (`integral_rect`), so the
integrality theorem is not true by a junk value.

## What is not formalized

* `LiftBundleData` is cocycle data, not a Mathlib or TauCeti vector bundle: no total space, no
  `FiberBundle`/`VectorBundle` instance, no covariant derivative on sections. TauCeti v4.36.0
  and Mathlib have `VectorBundleCore` (topological cocycles) and TauCeti has Thom and Euler
  classes in singular cohomology (`Topology/VectorBundle/EulerClass`), but neither has
  connections on line bundles, a bundle built from a closed 2-form, Chern–Weil theory or a
  first Chern class; nothing of this was usable here.
* The first Chern class as a cohomology class `c₁ = [ℱ/2π] ∈ H²(M; ℤ)` is not constructed.
  "Chern number" means only the real number `torusPeriod / 2π` for the tori `γ × S¹_ℓ`; the
  integrality theorem is about these numbers. That these tori generate `H₂(Ω × S¹)` ("since
  `H²(Ω; ℝ) = 0`") is not formalized, and periods over closed surfaces in `Ω` are not treated.
* The charts are cylinders `V × ℝ` with `V ⊆ ℝ³` open, and the quotient `Ω × S¹_ℓ`
  (`Space × AddCircle ℓ` of `FormHYMCircle`) is not used: periodic data on the cover stand for
  data on the quotient. Charts of `Ω × S¹` that are not cylinders are not covered by the
  obstruction theorem.
* Sufficiency of the quantisation condition in general (existence of periodic data whenever
  all `ℓ ∮_γ B · dl ∈ 2πℤ`) is not proved; it is proved for data of the form `ofPotentials`
  (`ofPotentials_isPeriodic_iff`) and for the wire field (`wire_exists_periodic_iff`).
* The loops in part 3 are `C¹` on all of `ℝ`, not only on `[a, b]`, and not piecewise `C¹`.
* The holomorphic structure of the bundle, and the statement that it is not algebraic
  (the algebraic Picard group of `(ℂ^*)²` is zero), are not formalized.
-/

@[expose] public section

namespace PlasmaLean.Forms

open PlasmaLean.Vacuum PlasmaLean.Fields PlasmaLean.Contract
open TopologicalSpace Topology
open scoped RealInnerProductSpace

/-! ## Periods of a 2-form over the tori `γ × S¹` -/

/-- **The integral of a field of 2-forms over the torus `γ × [0, ℓ]`.** The torus is
parametrised by `(s, τ) ↦ (γ s, τ)`, `s ∈ [a, b]`, `τ ∈ [0, ℓ]`, and oriented by the ordered
frame `(∂_s, ∂_τ) = ((γ' s, 0), (0, 1))`: the loop direction first, the circle direction second.
The value is the iterated interval integral of `F_{(γ s, τ)}((γ' s, 0), (0, 1))`. -/
noncomputable def torusPeriod (F : LiftSpace → LiftForm 2) (γ : ℝ → Space) (a b ℓ : ℝ) : ℝ :=
  ∫ s in a..b, ∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)]

/-- **The Chern number over the torus `γ × S¹_ℓ`** of a field of 2-forms `F`: the period
divided by `2π` (the pairing of `[F/2π]` with the torus, orientation `(∂_s, ∂_τ)`). It is a real
number; whether it is an integer is a theorem or a hypothesis, never part of the definition. -/
noncomputable def chernNumber (F : LiftSpace → LiftForm 2) (γ : ℝ → Space) (a b ℓ : ℝ) : ℝ :=
  torusPeriod F γ a b ℓ / (2 * Real.pi)

/-- The integrand of the torus period of the lift: `ℱ((γ', 0), (0, 1)) = -(⋆ω)(γ')`. -/
theorem hymLift_torus_integrand (w : Space → Form 2) (x v : Space) (τ : ℝ) :
    hymLift w (x, τ) ![(v, 0), (0, 1)] = -hodge (w x) ![v] := by
  have h0 : hodge (w x) ![(0 : Space)] = 0 := by
    have := (hodge (w x)).map_coord_zero (m := ![(0 : Space)]) 0 rfl
    exact this
  have h1 : w x ![v, (0 : Space)] = 0 := by
    have := (w x).map_coord_zero (m := ![v, (0 : Space)]) 1 rfl
    exact this
  rw [hymLift_apply, h0, h1]
  ring

/-- **Period of the lift over `γ × S¹_ℓ`, form language**:
`∫_{γ × [0, ℓ]} ℱ = -ℓ ∫_γ ⋆ω`, with the orientation `(∂_s, ∂_τ)`. No hypothesis is needed: the
inner integral is the integral of a constant, so both sides are the same interval integral (in
particular they are junk values together). -/
theorem torusPeriod_hymLift (w : Space → Form 2) (γ : ℝ → Space) (a b ℓ : ℝ) :
    torusPeriod (hymLift w) γ a b ℓ = -(ℓ * ∫ s in a..b, hodge (w (γ s)) ![deriv γ s]) := by
  unfold torusPeriod
  simp only [hymLift_torus_integrand, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg]
  ring

/-- **Period of the lift over `γ × S¹_ℓ`, vector language**: for the lift of the flux form of
`B`, `∫_{γ × [0, ℓ]} ℱ = -ℓ ∮_γ B · dl`. The sign is `-` for the orientation `(∂_s, ∂_τ)`; it is
the source's `-Γℓ`. No hypothesis is needed. -/
theorem torusPeriod_hymLift_fluxField (B : Space → Space) (γ : ℝ → Space) (a b ℓ : ℝ) :
    torusPeriod (hymLift (fluxField B)) γ a b ℓ = -(ℓ * lineIntegral B γ a b) := by
  rw [torusPeriod_hymLift, lineIntegral]
  simp only [fluxField_apply, hodge_flux, flat_apply]
  rfl

/-- **The integrand of the circulation is integrable** for a `C¹` curve along which the field is
continuous. Under these hypotheses neither side of `torusPeriod_hymLift_fluxField` is a junk
value. -/
theorem intervalIntegrable_circulation {B : Space → Space} {γ : ℝ → Space}
    (hγ : ContDiff ℝ 1 γ) (hB : ∀ t, ContinuousAt B (γ t)) (a b : ℝ) :
    IntervalIntegrable (fun s => ⟪B (γ s), deriv γ s⟫) MeasureTheory.volume a b := by
  have hcont : Continuous fun t => ⟪B (γ t), deriv γ t⟫ :=
    continuous_iff_continuousAt.2 fun t =>
      ((hB t).comp hγ.continuous.continuousAt).inner
        (hγ.continuous_deriv le_rfl).continuousAt
  exact hcont.intervalIntegrable a b

/-- **Chern number of the lift over `γ × S¹_ℓ`**: `-ℓ ∮_γ B · dl / 2π`. -/
theorem chernNumber_hymLift_fluxField (B : Space → Space) (γ : ℝ → Space) (a b ℓ : ℝ) :
    chernNumber (hymLift (fluxField B)) γ a b ℓ = -(ℓ * lineIntegral B γ a b) / (2 * Real.pi) := by
  rw [chernNumber, torusPeriod_hymLift_fluxField]

/-- **The period of the lift is `-ℓ` times a de Rham period.** For a `C¹` curl-free field on an
open region `U` and a closed loop in `U` that is `C¹` on `[a, b]`, the period of the lift over
`γ × S¹_ℓ` is `-ℓ` times the period of `B♭` on the class of the loop. So it depends only on the
homotopy class of the loop in `U`. -/
theorem torusPeriod_hymLift_eq_periodHom {U : Opens Space} {B : Space → Space} {γ : ℝ → Space}
    {a b : ℝ} (hB : ContDiffOn ℝ 1 B U) (hcurl : ∀ x ∈ U, fieldCurl B x = 0) (hab : a < b)
    (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hclosed : γ a = γ b) (ℓ : ℝ) :
    torusPeriod (hymLift (fluxField B)) γ a b ℓ =
      -(ℓ * TauCeti.periodHom (onOpens U fun y => flat (B y)) (intervalCurve γ hab.le hU 0)
          (Additive.ofMul (.of (.mk (intervalPath hab.le hU hγ.continuousOn hclosed))))) := by
  rw [torusPeriod_hymLift_fluxField, lineIntegral_eq_periodHom hB hcurl hab hU hγ hclosed]

/-- **Ampère's law for the period.** Over the torus (poloidal loop of the contract) `× S¹_ℓ` the
period of the lift is `-ℓ μ₀ I`, where `I = loopCurrent μ₀ B R z φ₀` is the current linked by
the poloidal loop. Only `μ₀ ≠ 0` is used. -/
theorem torusPeriod_hymLift_poloidal {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (B : Space → Space)
    (R z : ℝ → ℝ → ℝ) (φ₀ ℓ : ℝ) :
    torusPeriod (hymLift (fluxField B)) (poloidalLoop R z φ₀) (-Real.pi) Real.pi ℓ =
      -(ℓ * μ₀ * loopCurrent μ₀ B R z φ₀) := by
  rw [torusPeriod_hymLift_fluxField, loopCurrent, poloidalCirculation]
  field_simp

/-- **Ampère's law for the Chern number**: over (poloidal loop) `× S¹_ℓ` the Chern number of the
lift is `-ℓ μ₀ I / 2π`. -/
theorem chernNumber_hymLift_poloidal {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (B : Space → Space)
    (R z : ℝ → ℝ → ℝ) (φ₀ ℓ : ℝ) :
    chernNumber (hymLift (fluxField B)) (poloidalLoop R z φ₀) (-Real.pi) Real.pi ℓ =
      -(ℓ * μ₀ * loopCurrent μ₀ B R z φ₀) / (2 * Real.pi) := by
  rw [chernNumber, torusPeriod_hymLift_poloidal hμ]

/-- **On a simply connected region all torus periods of the lift vanish.** For a vacuum field
on a simply connected open region `U` and a closed loop in `U` that is `C¹` on `[a, b]`, the
period of the lift over `γ × S¹_ℓ` is `0` for every `ℓ`. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.torusPeriod_hymLift_eq_zero {U : Opens Space}
    [SimplyConnectedSpace U] {B : Space → Space} (h : VacuumField U B) {γ : ℝ → Space}
    {a b : ℝ} (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) (hclosed : γ a = γ b) (ℓ : ℝ) :
    torusPeriod (hymLift (fluxField B)) γ a b ℓ = 0 := by
  rw [torusPeriod_hymLift_fluxField, h.lineIntegral_eq_zero_of_simplyConnected hab hU hγ hclosed,
    mul_zero, neg_zero]

/-- On a simply connected region the Chern numbers of the lift over the tori `γ × S¹_ℓ`
vanish. -/
theorem _root_.PlasmaLean.Vacuum.VacuumField.chernNumber_hymLift_eq_zero {U : Opens Space}
    [SimplyConnectedSpace U] {B : Space → Space} (h : VacuumField U B) {γ : ℝ → Space}
    {a b : ℝ} (hab : a < b) (hU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) (hclosed : γ a = γ b) (ℓ : ℝ) :
    chernNumber (hymLift (fluxField B)) γ a b ℓ = 0 := by
  rw [chernNumber, h.torusPeriod_hymLift_eq_zero hab hU hγ hclosed, zero_div]

/-- **The quantisation condition.** The period of the lift over `γ × S¹_ℓ` lies in `2πℤ`
exactly when `ℓ ∮_γ B · dl` does. -/
theorem torusPeriod_hymLift_mem_iff (B : Space → Space) (γ : ℝ → Space) (a b ℓ : ℝ) :
    (∃ n : ℤ, torusPeriod (hymLift (fluxField B)) γ a b ℓ = 2 * Real.pi * n) ↔
      ∃ n : ℤ, ℓ * lineIntegral B γ a b = 2 * Real.pi * n := by
  rw [torusPeriod_hymLift_fluxField]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by push_cast; linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨-n, by push_cast; linarith⟩

/-- A Chern number is an integer exactly when the period lies in `2πℤ`. -/
theorem chernNumber_mem_int_iff (F : LiftSpace → LiftForm 2) (γ : ℝ → Space) (a b ℓ : ℝ) :
    (∃ n : ℤ, chernNumber F γ a b ℓ = n) ↔ ∃ n : ℤ, torusPeriod F γ a b ℓ = 2 * Real.pi * n := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  unfold chernNumber
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [div_eq_iff hpi] at hn; linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [div_eq_iff hpi]; linarith⟩

/-- **Integrality of the Chern number of the lift**: it is an integer exactly when
`ℓ ∮_γ B · dl ∈ 2πℤ`. -/
theorem chernNumber_hymLift_mem_int_iff (B : Space → Space) (γ : ℝ → Space) (a b ℓ : ℝ) :
    (∃ n : ℤ, chernNumber (hymLift (fluxField B)) γ a b ℓ = n) ↔
      ∃ n : ℤ, ℓ * lineIntegral B γ a b = 2 * Real.pi * n := by
  rw [chernNumber_mem_int_iff, torusPeriod_hymLift_mem_iff]

/-! ## Local connections of the lift and their differences -/

/-- The difference of two local connection forms `π^*Aₖ - (π^*φₖ) dτ` on a vector `(u, s)`:
`(A₁ - A₂)(u) - (φ₁ - φ₂) s`. -/
theorem liftConnection_sub_apply (A₁ A₂ : Space → Form 1) (φ₁ φ₂ : Space → ℝ) (x u : Space)
    (τ s : ℝ) :
    (liftConnection A₁ φ₁ (x, τ) - liftConnection A₂ φ₂ (x, τ)) ![(u, s)] =
      (A₁ x - A₂ x) ![u] - (φ₁ x - φ₂ x) * s := by
  simp only [ContinuousAlternatingMap.sub_apply, liftConnection_apply]
  ring

/-- **The transition potential** `h(x, τ) = lam x - c τ` of two local connections whose vector
potentials differ by `d lam` and whose scalar potentials differ by the constant `c`. -/
def transPotential (lam : Space → ℝ) (c : ℝ) (p : LiftSpace) : ℝ := lam p.1 - c * p.2

/-- The derivative of the transition potential. -/
theorem hasFDerivAt_transPotential {lam : Space → ℝ} {x : Space}
    (hl : DifferentiableAt ℝ lam x) (c τ : ℝ) :
    HasFDerivAt (transPotential lam c)
      (fderiv ℝ lam x ∘L ContinuousLinearMap.fst ℝ Space ℝ -
        c • ContinuousLinearMap.snd ℝ Space ℝ) (x, τ) := by
  have h1 : HasFDerivAt (fun p : LiftSpace => lam p.1)
      (fderiv ℝ lam x ∘L ContinuousLinearMap.fst ℝ Space ℝ) (x, τ) :=
    HasFDerivAt.comp (x, τ) (f := Prod.fst) (g := lam) hl.hasFDerivAt hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : LiftSpace => c * p.2)
      (c • ContinuousLinearMap.snd ℝ Space ℝ) (x, τ) :=
    (hasFDerivAt_snd (p := ((x, τ) : LiftSpace))).const_mul c
  exact h1.sub h2

/-- **Two local connections of the lift differ by an exact form.** Let `𝒜ₖ = π^*Aₖ - (π^*φₖ) dτ`
(`k = 1, 2`). If at `x` the vector potentials differ by `d lam` and the scalar potentials by the
number `c`, then at `(x, τ)`, for every vector `v`,
`(𝒜₁ - 𝒜₂)(v) = d(lam - c τ)(v)`.
On a connected component of the overlap of two regions on which `φ₁ - φ₂` is the constant `c`
this is `𝒜₁ - 𝒜₂ = d(lam - c τ)`. -/
theorem liftConnection_sub_eq_fderiv {A₁ A₂ : Space → Form 1} {φ₁ φ₂ lam : Space → ℝ}
    {x : Space} {c : ℝ} (hl : DifferentiableAt ℝ lam x)
    (hA : formGrad lam x = A₁ x - A₂ x) (hφ : φ₁ x - φ₂ x = c) (τ : ℝ) (v : LiftSpace) :
    (liftConnection A₁ φ₁ (x, τ) - liftConnection A₂ φ₂ (x, τ)) ![v] =
      fderiv ℝ (transPotential lam c) (x, τ) v := by
  obtain ⟨u, s⟩ := v
  rw [(hasFDerivAt_transPotential hl c τ).fderiv, liftConnection_sub_apply, ← hA, hφ]
  simp

/-- **Periodicity of the transition function `exp(i(lam - c τ))`.** It is invariant under
`τ ↦ τ + ℓ`, that is, it is a function on the circle of length `ℓ`, exactly when
`c ℓ ∈ 2πℤ`. -/
theorem circleExp_transPotential_periodic_iff (lam : Space → ℝ) (c ℓ : ℝ) :
    (∀ (x : Space) (τ : ℝ), Circle.exp (transPotential lam c (x, τ + ℓ)) =
        Circle.exp (transPotential lam c (x, τ))) ↔ ∃ n : ℤ, c * ℓ = 2 * Real.pi * n := by
  simp only [transPotential, Circle.exp_eq_exp]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h 0 0
    exact ⟨-m, by push_cast; linarith⟩
  · rintro ⟨n, hn⟩ x τ
    exact ⟨-n, by push_cast; linarith⟩

/-- The local connection form is `C¹` on `V × ℝ` when the potentials are `C¹` on `V`. -/
theorem contDiffOn_liftConnection {A : Space → Form 1} {φ : Space → ℝ} {V : Set Space}
    (hA : ContDiffOn ℝ 1 A V) (hφ : ContDiffOn ℝ 1 φ V) :
    ContDiffOn ℝ 1 (liftConnection A φ) (V ×ˢ (Set.univ : Set ℝ)) := by
  let P : Form 1 →L[ℝ] LiftForm 1 :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.fst ℝ Space ℝ)
  have hfst : Set.MapsTo (Prod.fst : LiftSpace → Space) (V ×ˢ (Set.univ : Set ℝ)) V :=
    fun p hp => hp.1
  have h1 : ContDiffOn ℝ 1 (fun p : LiftSpace => P (A p.1)) (V ×ˢ (Set.univ : Set ℝ)) :=
    P.contDiff.comp_contDiffOn (hA.comp contDiff_fst.contDiffOn hfst)
  have h2 : ContDiffOn ℝ 1 (fun p : LiftSpace => φ p.1 • dTau) (V ×ˢ (Set.univ : Set ℝ)) :=
    (hφ.comp contDiff_fst.contDiffOn hfst).smul contDiffOn_const
  exact h1.sub h2

/-! ## Cocycle data of a `U(1)` line bundle with connection -/

/-- **Cocycle data of a `U(1)` line bundle with connection and curvature `F`** over `Ω × ℝ`, in
charts that are cylinders `V i × ℝ`.

* `base i` are open sets of `ℝ³` covering `Ω`; the charts are `base i × ℝ`.
* `conn i` is the local connection 1-form on `base i × ℝ`, of class `C¹`, with `d(conn i) = F`.
* `trans i j` is the transition function, with values in the unit circle of `ℂ`, and satisfies
  the cocycle condition on triple overlaps.
* Compatibility, written without logarithms: near every point of an overlap,
  `trans i j = exp(i h)` for a real function `h` with `dh = conn i - conn j` at the point. (This
  does not depend on the choice of `h`: it says `-i g⁻¹ dg = 𝒜ᵢ - 𝒜ⱼ` for `g = trans i j`.)

This is the classical description of a Hermitian line bundle with unitary connection
`∇ = d - i 𝒜ᵢ` in local trivialisations. It is data, not a Mathlib or TauCeti vector bundle: no
total space is built. -/
structure LiftBundleData (ι : Type*) (Ω : Set Space) (F : LiftSpace → LiftForm 2) where
  /-- The bases of the cylinder charts. -/
  base : ι → Set Space
  /-- The bases are open. -/
  isOpen_base : ∀ i, IsOpen (base i)
  /-- The bases cover the region. -/
  cover : Ω ⊆ ⋃ i, base i
  /-- The local connection 1-forms. -/
  conn : ι → LiftSpace → LiftForm 1
  /-- The local connection forms are `C¹` on their charts. -/
  contDiffOn_conn : ∀ i, ContDiffOn ℝ 1 (conn i) (base i ×ˢ (Set.univ : Set ℝ))
  /-- The curvature of every local connection form is `F`. -/
  curvature : ∀ i, ∀ x ∈ base i, ∀ τ : ℝ, extDeriv (conn i) (x, τ) = F (x, τ)
  /-- The transition functions, with values in the unit circle. -/
  trans : ι → ι → LiftSpace → Circle
  /-- The cocycle condition on triple overlaps. -/
  cocycle : ∀ i j k, ∀ x ∈ base i ∩ base j ∩ base k, ∀ τ : ℝ,
    trans i j (x, τ) * trans j k (x, τ) = trans i k (x, τ)
  /-- Compatibility of the connection forms with the transition functions. -/
  compat : ∀ i j, ∀ x ∈ base i ∩ base j, ∀ τ : ℝ, ∃ h : LiftSpace → ℝ,
    (∀ᶠ q in 𝓝 ((x, τ) : LiftSpace), trans i j q = Circle.exp (h q)) ∧
      DifferentiableAt ℝ h (x, τ) ∧
      ∀ v : LiftSpace, fderiv ℝ h (x, τ) v = (conn i (x, τ) - conn j (x, τ)) ![v]

namespace LiftBundleData

variable {ι : Type*} {Ω : Set Space} {F : LiftSpace → LiftForm 2}

/-- **The data are `ℓ`-periodic in `τ`**: the connection forms and the transition functions
are invariant under `τ ↦ τ + ℓ`. Periodic data on `Ω × ℝ` with cylinder charts are the same as
data on the quotient `Ω × S¹_ℓ` with charts `base i × S¹_ℓ`; the quotient itself is not formed
here. -/
structure IsPeriodic (L : LiftBundleData ι Ω F) (ℓ : ℝ) : Prop where
  /-- The connection forms are periodic. -/
  conn_periodic : ∀ i, ∀ x ∈ L.base i, ∀ τ : ℝ, L.conn i (x, τ + ℓ) = L.conn i (x, τ)
  /-- The transition functions are periodic. -/
  trans_periodic : ∀ i j, ∀ x ∈ L.base i ∩ L.base j, ∀ τ : ℝ,
    L.trans i j (x, τ + ℓ) = L.trans i j (x, τ)

/-- **Cocycle data of the lift from local scalar potentials.** Given one vector potential `A`
(`dA = ω`) on all the open sets `V i` and a scalar potential `φ i` (`dφᵢ = ⋆ω`) on each `V i`,
the local connections are `𝒜ᵢ = π^*A - (π^*φᵢ) dτ` and the transition functions are
`gᵢⱼ(x, τ) = exp(i (φⱼ(x) - φᵢ(x)) τ)`. On an overlap `φⱼ - φᵢ` is locally constant (both are
potentials of `⋆ω`), and `𝒜ᵢ - 𝒜ⱼ = (φⱼ - φᵢ) dτ = d((φⱼ - φᵢ) τ)`. This is the source's
construction (`A_i = a - Φ_i dt`). -/
noncomputable def ofPotentials {w : Space → Form 2} (V : ι → Set Space)
    (hV : ∀ i, IsOpen (V i)) (hcov : Ω ⊆ ⋃ i, V i) (A : Space → Form 1) (φ : ι → Space → ℝ)
    (hA : ∀ i, ContDiffOn ℝ 1 A (V i)) (hφ : ∀ i, ContDiffOn ℝ 1 (φ i) (V i))
    (hdA : ∀ i, ∀ x ∈ V i, extDeriv A x = w x)
    (hdφ : ∀ i, ∀ x ∈ V i, formGrad (φ i) x = hodge (w x)) :
    LiftBundleData ι Ω (hymLift w) where
  base := V
  isOpen_base := hV
  cover := hcov
  conn i := liftConnection A (φ i)
  contDiffOn_conn i := contDiffOn_liftConnection (hA i) (hφ i)
  curvature i x hx τ :=
    extDeriv_liftConnection_eq_hymLift
      (((hA i).contDiffAt ((hV i).mem_nhds hx)).differentiableAt (by norm_num))
      (((hφ i).contDiffAt ((hV i).mem_nhds hx)).differentiableAt (by norm_num))
      (hdA i x hx) (hdφ i x hx) τ
  trans i j p := Circle.exp ((φ j p.1 - φ i p.1) * p.2)
  cocycle i j k x _ τ := by
    rw [← Circle.exp_add]
    congr 1
    ring
  compat i j x hx τ := by
    have hi : DifferentiableAt ℝ (φ i) x :=
      ((hφ i).contDiffAt ((hV i).mem_nhds hx.1)).differentiableAt (by norm_num)
    have hj : DifferentiableAt ℝ (φ j) x :=
      ((hφ j).contDiffAt ((hV j).mem_nhds hx.2)).differentiableAt (by norm_num)
    have hfd : fderiv ℝ (φ j) x = fderiv ℝ (φ i) x := by
      ext u
      have h1 := congrArg (fun f : Form 1 => f ![u]) (hdφ i x hx.1)
      have h2 := congrArg (fun f : Form 1 => f ![u]) (hdφ j x hx.2)
      simp only [formGrad_apply] at h1 h2
      exact h2.trans h1.symm
    have h1 : HasFDerivAt (fun p : LiftSpace => φ j p.1 - φ i p.1)
        ((fderiv ℝ (φ j) x - fderiv ℝ (φ i) x) ∘L ContinuousLinearMap.fst ℝ Space ℝ) (x, τ) :=
      HasFDerivAt.comp (x, τ) (f := Prod.fst) (g := fun y => φ j y - φ i y)
        (hj.hasFDerivAt.sub hi.hasFDerivAt) hasFDerivAt_fst
    have h2 : HasFDerivAt (fun p : LiftSpace => (φ j p.1 - φ i p.1) * p.2)
        ((φ j x - φ i x) • ContinuousLinearMap.snd ℝ Space ℝ +
          τ • (fderiv ℝ (φ j) x - fderiv ℝ (φ i) x) ∘L ContinuousLinearMap.fst ℝ Space ℝ)
        (x, τ) :=
      h1.mul (hasFDerivAt_snd (p := ((x, τ) : LiftSpace)))
    refine ⟨fun p => (φ j p.1 - φ i p.1) * p.2, Filter.Eventually.of_forall fun q => rfl,
      h2.differentiableAt, fun v => ?_⟩
    obtain ⟨u, s⟩ := v
    rw [h2.fderiv, liftConnection_sub_apply, hfd]
    simp
    ring

/-- The cocycle data built from potentials are `ℓ`-periodic exactly when every jump of the
scalar potential satisfies `(φⱼ - φᵢ) ℓ ∈ 2πℤ` on the overlap `V i ∩ V j`. -/
theorem ofPotentials_isPeriodic_iff {w : Space → Form 2} (V : ι → Set Space)
    (hV : ∀ i, IsOpen (V i)) (hcov : Ω ⊆ ⋃ i, V i) (A : Space → Form 1) (φ : ι → Space → ℝ)
    (hA : ∀ i, ContDiffOn ℝ 1 A (V i)) (hφ : ∀ i, ContDiffOn ℝ 1 (φ i) (V i))
    (hdA : ∀ i, ∀ x ∈ V i, extDeriv A x = w x)
    (hdφ : ∀ i, ∀ x ∈ V i, formGrad (φ i) x = hodge (w x)) (ℓ : ℝ) :
    (ofPotentials (Ω := Ω) V hV hcov A φ hA hφ hdA hdφ).IsPeriodic ℓ ↔
      ∀ i j, ∀ x ∈ V i ∩ V j, ∃ n : ℤ, (φ j x - φ i x) * ℓ = 2 * Real.pi * n := by
  constructor
  · intro h i j x hx
    have h0 := h.trans_periodic i j x hx 0
    simp only [ofPotentials, Circle.exp_eq_exp] at h0
    obtain ⟨m, hm⟩ := h0
    exact ⟨m, by linarith⟩
  · intro h
    refine ⟨fun i x _ τ => rfl, fun i j x hx τ => ?_⟩
    obtain ⟨n, hn⟩ := h i j x hx
    simp only [ofPotentials, Circle.exp_eq_exp]
    exact ⟨n, by linarith⟩

end LiftBundleData

/-- **The trivial bundle on a star-convex region.** On an open star-convex region the lift of a
vacuum form is the curvature of one-chart cocycle data (transition function `1`), and these data
are `ℓ`-periodic for every `ℓ`: they descend to `Ω × S¹_ℓ` with no quantisation condition. -/
theorem VacuumForm.exists_liftBundleData {Ω : Set Space} {w : Space → Form 2}
    (h : VacuumForm Ω w) {x₀ : Space} (hs : StarConvex ℝ x₀ Ω) :
    ∃ L : LiftBundleData Unit Ω (hymLift w), (∀ x τ, L.trans () () (x, τ) = 1) ∧
      ∀ ℓ : ℝ, L.IsPeriodic ℓ := by
  obtain ⟨A, hA, -, hdA⟩ := h.exists_vectorPotential hs
  obtain ⟨φ, hφ, -, hdφ⟩ := h.exists_scalarPotential hs
  have hcov : Ω ⊆ ⋃ _ : Unit, Ω := fun x hx => Set.mem_iUnion.2 ⟨(), hx⟩
  refine ⟨LiftBundleData.ofPotentials (fun _ => Ω) (fun _ => h.isOpen) hcov A (fun _ => φ)
    (fun _ => hA.of_le (by norm_num)) (fun _ => hφ.of_le (by norm_num)) (fun _ => hdA)
    (fun _ => hdφ), fun x τ => ?_, fun ℓ => ?_⟩
  · simp [LiftBundleData.ofPotentials]
  · rw [LiftBundleData.ofPotentials_isPeriodic_iff]
    exact fun _ _ x _ => ⟨0, by simp⟩

/-! ## Integrality of the periods of periodic cocycle data -/

namespace LiftBundleData

variable {ι : Type*} {Ω : Set Space} {F : LiftSpace → LiftForm 2}

/-- The integral of the `dτ`-component of the local connection form `conn i` over the fibre
`{x} × [0, ℓ]`. For periodic data, `exp(i ·)` of it is the holonomy of the connection around
the circle fibre, computed in the chart `i`. -/
noncomputable def fibreIntegral (L : LiftBundleData ι Ω F) (i : ι) (ℓ : ℝ) (x : Space) : ℝ :=
  ∫ τ in (0 : ℝ)..ℓ, L.conn i (x, τ) ![(0, 1)]

/-- The local connection form is continuous along a fibre. -/
theorem continuous_conn_fibre (L : LiftBundleData ι Ω F) {i : ι} {x : Space}
    (hx : x ∈ L.base i) : Continuous fun τ : ℝ => L.conn i (x, τ) :=
  (L.contDiffOn_conn i).continuousOn.comp_continuous (by fun_prop) fun τ => ⟨hx, Set.mem_univ τ⟩

/-- The local connection form evaluated on a fixed vector is continuous along a fibre. -/
theorem continuous_conn_fibre_apply (L : LiftBundleData ι Ω F) {i : ι} {x : Space}
    (hx : x ∈ L.base i) (v : Fin 1 → LiftSpace) : Continuous fun τ : ℝ => L.conn i (x, τ) v :=
  (ContinuousAlternatingMap.apply ℝ LiftSpace ℝ v).continuous.comp (L.continuous_conn_fibre hx)

/-- **The fibre integrals in two charts differ by an element of `2πℤ`** for `ℓ`-periodic data:
the transition function is periodic, so its winding along the circle fibre is an integer. -/
theorem IsPeriodic.fibreIntegral_sub {L : LiftBundleData ι Ω F} {ℓ : ℝ} (hper : L.IsPeriodic ℓ)
    {i j : ι} {x : Space} (hx : x ∈ L.base i ∩ L.base j) :
    ∃ n : ℤ, L.fibreIntegral i ℓ x - L.fibreIntegral j ℓ x = 2 * Real.pi * n := by
  set u : ℝ → ℝ := fun τ => (L.conn i (x, τ) - L.conn j (x, τ)) ![(0, 1)] with hu_def
  have hu : Continuous u := by
    have := (L.continuous_conn_fibre_apply hx.1 ![(0, 1)]).sub
      (L.continuous_conn_fibre_apply hx.2 ![(0, 1)])
    exact this
  set H : ℝ → ℝ := fun τ => ∫ t in (0 : ℝ)..τ, u t with hH_def
  have hH : ∀ τ, HasDerivAt H (u τ) τ := fun τ => (hu.integral_hasStrictDerivAt 0 τ).hasDerivAt
  set k : ℝ → ℂ := fun τ => (L.trans i j (x, τ) : ℂ) * Complex.exp (-(H τ : ℂ) * Complex.I)
    with hk_def
  have hk : ∀ τ, HasDerivAt k 0 τ := by
    intro τ
    obtain ⟨h, hev, hd, hfd⟩ := L.compat i j x hx τ
    have hline : HasDerivAt (fun τ' : ℝ => ((x, τ') : LiftSpace)) ((0 : Space), (1 : ℝ)) τ :=
      (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
    have hm : HasDerivAt (fun τ' : ℝ => h (x, τ')) (u τ) τ := by
      have := hd.hasFDerivAt.comp_hasDerivAt τ hline
      rw [hfd] at this
      exact this
    have hev' : ∀ᶠ τ' in 𝓝 τ, k τ' =
        Complex.exp ((h (x, τ') : ℂ) * Complex.I) * Complex.exp (-(H τ' : ℂ) * Complex.I) := by
      have hc : Continuous fun τ' : ℝ => ((x, τ') : LiftSpace) := by fun_prop
      filter_upwards [hc.continuousAt.eventually hev] with τ' hτ'
      simp only [hk_def]
      rw [hτ', Circle.coe_exp]
    have h1 : HasDerivAt (fun τ' : ℝ => Complex.exp ((h (x, τ') : ℂ) * Complex.I))
        (Complex.exp ((h (x, τ) : ℂ) * Complex.I) * ((u τ : ℂ) * Complex.I)) τ :=
      (hm.ofReal_comp.mul_const Complex.I).cexp
    have h2 : HasDerivAt (fun τ' : ℝ => Complex.exp (-(H τ' : ℂ) * Complex.I))
        (Complex.exp (-(H τ : ℂ) * Complex.I) * (-(u τ : ℂ) * Complex.I)) τ :=
      (((hH τ).ofReal_comp.neg).mul_const Complex.I).cexp
    have h3 := h1.mul h2
    refine (h3.congr_of_eventuallyEq hev').congr_deriv ?_
    ring
  have hconst : k ℓ = k 0 :=
    is_const_of_deriv_eq_zero (fun τ => (hk τ).differentiableAt) (fun τ => (hk τ).deriv) ℓ 0
  have hH0 : H 0 = 0 := by simp [hH_def]
  have htr : L.trans i j (x, ℓ) = L.trans i j (x, 0) := by
    have := hper.trans_periodic i j x hx 0
    rwa [zero_add] at this
  have hexp : Circle.exp (-H ℓ) = 1 := by
    apply Circle.ext
    have hne : (L.trans i j (x, 0) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    simp only [hk_def, hH0, htr] at hconst
    rw [Circle.coe_exp, Circle.coe_one]
    have h4 : (L.trans i j (x, 0) : ℂ) * Complex.exp (-(H ℓ : ℂ) * Complex.I) =
        (L.trans i j (x, 0) : ℂ) * 1 := by
      rw [hconst]; simp
    have h5 := mul_left_cancel₀ hne h4
    rw [← h5]
    push_cast
    ring_nf
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.1 hexp
  refine ⟨-n, ?_⟩
  have hsub : L.fibreIntegral i ℓ x - L.fibreIntegral j ℓ x = H ℓ := by
    simp only [fibreIntegral, hH_def, hu_def, ContinuousAlternatingMap.sub_apply]
    rw [intervalIntegral.integral_sub
      ((L.continuous_conn_fibre_apply hx.1 _).intervalIntegrable _ _)
      ((L.continuous_conn_fibre_apply hx.2 _).intervalIntegrable _ _)]
  rw [hsub]
  push_cast
  linarith

/-- **Stokes' theorem on one chart.** For `ℓ`-periodic data and a `C¹` curve `γ` with
`γ([s₀, s₁])` in the base of the chart `i`, the integral of `F` over `γ([s₀, s₁]) × [0, ℓ]`
(orientation `(∂_s, ∂_τ)`) is the difference of the fibre integrals of `conn i` at the two ends;
the two edges `τ = 0` and `τ = ℓ` cancel by periodicity. The inner integral is an interval
integrable function of `s`, so the outer integral is not a junk value. -/
theorem IsPeriodic.integral_rect {L : LiftBundleData ι Ω F} {ℓ : ℝ} (hper : L.IsPeriodic ℓ)
    {γ : ℝ → Space} (hγ : ContDiff ℝ 1 γ) {i : ι} {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁)
    (hmem : ∀ s ∈ Set.Icc s₀ s₁, γ s ∈ L.base i) :
    IntervalIntegrable (fun s => ∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)])
        MeasureTheory.volume s₀ s₁ ∧
      ∫ s in s₀..s₁, ∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)] =
        L.fibreIntegral i ℓ (γ s₁) - L.fibreIntegral i ℓ (γ s₀) := by
  set S : Set ℝ := γ ⁻¹' L.base i with hS_def
  have hS : IsOpen S := (L.isOpen_base i).preimage hγ.continuous
  have hC : IsOpen (L.base i ×ˢ (Set.univ : Set ℝ)) := (L.isOpen_base i).prod isOpen_univ
  have hdiff : ∀ s ∈ S, ∀ τ : ℝ,
      HasFDerivAt (L.conn i) (fderiv ℝ (L.conn i) (γ s, τ)) (γ s, τ) := fun s hs τ =>
    (((L.contDiffOn_conn i).contDiffAt (hC.mem_nhds
      (show ((γ s, τ) : LiftSpace) ∈ L.base i ×ˢ (Set.univ : Set ℝ) from
        ⟨hs, Set.mem_univ τ⟩))).differentiableAt (by norm_num)).hasFDerivAt
  have hD : ContinuousOn (fderiv ℝ (L.conn i)) (L.base i ×ˢ (Set.univ : Set ℝ)) :=
    (L.contDiffOn_conn i).continuousOn_fderiv_of_isOpen hC le_rfl
  have c1 : (fun _ : Fin 1 => (((0 : Space), (1 : ℝ)) : LiftSpace)) = ![(0, 1)] := by
    funext j; fin_cases j; rfl
  have c2 (v : LiftSpace) : (fun _ : Fin 1 => v) = ![v] := by
    funext j; fin_cases j; rfl
  let T1 : ℝ → ℝ → ℝ := fun s τ =>
    fderiv ℝ (L.conn i) (γ s, τ) (deriv γ s, 0) (fun _ => ((0 : Space), (1 : ℝ)))
  let T2 : ℝ → ℝ → ℝ := fun s τ =>
    fderiv ℝ (L.conn i) (γ s, τ) ((0 : Space), (1 : ℝ)) (fun _ => (deriv γ s, (0 : ℝ)))
  have hΦ : Continuous fun q : ℝ × ℝ => ((γ q.1, q.2) : LiftSpace) :=
    (hγ.continuous.comp continuous_fst).prodMk continuous_snd
  have hΦmaps : Set.MapsTo (fun q : ℝ × ℝ => ((γ q.1, q.2) : LiftSpace))
      (S ×ˢ (Set.univ : Set ℝ)) (L.base i ×ˢ (Set.univ : Set ℝ)) :=
    fun q hq => ⟨hq.1, Set.mem_univ _⟩
  have hDΦ : ContinuousOn (fun q : ℝ × ℝ => fderiv ℝ (L.conn i) (γ q.1, q.2))
      (S ×ˢ (Set.univ : Set ℝ)) := hD.comp hΦ.continuousOn hΦmaps
  have hT1 : ContinuousOn (Function.uncurry T1) (S ×ˢ (Set.univ : Set ℝ)) := by
    have hv : Continuous fun q : ℝ × ℝ => ((deriv γ q.1, (0 : ℝ)) : LiftSpace) :=
      ((hγ.continuous_deriv le_rfl).comp continuous_fst).prodMk continuous_const
    have h1 := hDΦ.clm_apply hv.continuousOn
    exact (ContinuousAlternatingMap.apply ℝ LiftSpace ℝ
      (fun _ => ((0 : Space), (1 : ℝ)))).continuous.comp_continuousOn h1
  have hT1τ : ∀ s ∈ S, Continuous (T1 s) := fun s hs =>
    hT1.comp_continuous (f := fun τ : ℝ => (s, τ)) (by fun_prop) fun τ => ⟨hs, Set.mem_univ τ⟩
  have hT2τ : ∀ s ∈ S, Continuous (T2 s) := by
    intro s hs
    have h0 : Continuous fun τ : ℝ => fderiv ℝ (L.conn i) (γ s, τ) :=
      hD.comp_continuous (f := fun τ : ℝ => ((γ s, τ) : LiftSpace)) (by fun_prop)
        fun τ => (show ((γ s, τ) : LiftSpace) ∈ L.base i ×ˢ (Set.univ : Set ℝ) from
          ⟨hs, Set.mem_univ τ⟩)
    have h1 : Continuous fun τ : ℝ => fderiv ℝ (L.conn i) (γ s, τ) ((0 : Space), (1 : ℝ)) :=
      h0.clm_apply continuous_const
    exact (ContinuousAlternatingMap.apply ℝ LiftSpace ℝ
      (fun _ => (deriv γ s, (0 : ℝ)))).continuous.comp h1
  -- the `τ`-derivative term integrates to zero by periodicity
  have hT2int : ∀ s ∈ S, ∫ τ in (0 : ℝ)..ℓ, T2 s τ = 0 := by
    intro s hs
    have hg : ∀ τ : ℝ, HasDerivAt
        (fun τ' : ℝ => L.conn i (γ s, τ') (fun _ => (deriv γ s, (0 : ℝ)))) (T2 s τ) τ := by
      intro τ
      have hline : HasDerivAt (fun τ' : ℝ => ((γ s, τ') : LiftSpace))
          ((0 : Space), (1 : ℝ)) τ := (hasDerivAt_const τ (γ s)).prodMk (hasDerivAt_id τ)
      have h1 := (hdiff s hs τ).comp_hasDerivAt τ hline
      exact ((ContinuousAlternatingMap.apply ℝ LiftSpace ℝ
        (fun _ => (deriv γ s, (0 : ℝ)))).hasFDerivAt.comp_hasDerivAt τ h1)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hg τ)
      ((hT2τ s hs).intervalIntegrable _ _)]
    have := hper.conn_periodic i (γ s) hs 0
    rw [zero_add] at this
    rw [this, sub_self]
  -- the `s`-derivative term
  have hf : ∀ s ∈ S, ∀ τ : ℝ, HasDerivAt
      (fun s' : ℝ => L.conn i (γ s', τ) (fun _ => ((0 : Space), (1 : ℝ)))) (T1 s τ) s := by
    intro s hs τ
    have hcurve : HasDerivAt (fun s' : ℝ => ((γ s', τ) : LiftSpace)) (deriv γ s, (0 : ℝ)) s :=
      ((hγ.differentiable one_ne_zero) s).hasDerivAt.prodMk (hasDerivAt_const s τ)
    have h1 := (hdiff s hs τ).comp_hasDerivAt s hcurve
    exact ((ContinuousAlternatingMap.apply ℝ LiftSpace ℝ
      (fun _ => ((0 : Space), (1 : ℝ)))).hasFDerivAt.comp_hasDerivAt s h1)
  have hIcc : Set.Icc s₀ s₁ ⊆ S := hmem
  have hIJ : ∀ s ∈ Set.Icc s₀ s₁,
      (∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)]) = ∫ τ in (0 : ℝ)..ℓ, T1 s τ := by
    intro s hs
    have hpt : ∀ τ : ℝ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)] = T1 s τ - T2 s τ := fun τ => by
      rw [← L.curvature i _ (hmem s hs) τ, TauCeti.extDeriv_apply_pair]
    simp only [hpt]
    rw [intervalIntegral.integral_sub ((hT1τ s (hIcc hs)).intervalIntegrable _ _)
      ((hT2τ s (hIcc hs)).intervalIntegrable _ _), hT2int s (hIcc hs), sub_zero]
  have hJ : ContinuousOn (fun s => ∫ τ in (0 : ℝ)..ℓ, T1 s τ) S := by
    have h0 : ContDiffOn ℝ ((0 : ℕ∞) : WithTop ℕ∞) (Function.uncurry T1) (S ×ˢ Set.uIcc 0 ℓ) :=
      contDiffOn_zero.2 (hT1.mono (Set.prod_mono subset_rfl (Set.subset_univ _)))
    have h1 := h0.parametric_intervalIntegral (μ := MeasureTheory.volume) hS
    exact contDiffOn_zero.1 h1
  refine ⟨?_, ?_⟩
  · exact ((hJ.mono hIcc).congr hIJ).intervalIntegrable_of_Icc hs
  · have hu : Set.uIcc s₀ s₁ = Set.Icc s₀ s₁ := Set.uIcc_of_le hs
    rw [intervalIntegral.integral_congr (g := fun s => ∫ τ in (0 : ℝ)..ℓ, T1 s τ)
      (fun s hs' => hIJ s (hu ▸ hs'))]
    have hint : MeasureTheory.IntegrableOn (Function.uncurry T1)
        (Set.uIoc s₀ s₁ ×ˢ Set.uIoc 0 ℓ) := by
      have hK : IsCompact (Set.uIcc s₀ s₁ ×ˢ Set.uIcc 0 ℓ) := isCompact_uIcc.prod isCompact_uIcc
      have hcK : ContinuousOn (Function.uncurry T1) (Set.uIcc s₀ s₁ ×ˢ Set.uIcc 0 ℓ) :=
        hT1.mono (Set.prod_mono (hu ▸ hIcc) (Set.subset_univ _))
      exact (hcK.integrableOn_compact hK).mono_set
        (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap hint]
    have hinner : ∀ τ : ℝ, ∫ s in s₀..s₁, T1 s τ =
        L.conn i (γ s₁, τ) ![(0, 1)] - L.conn i (γ s₀, τ) ![(0, 1)] := by
      intro τ
      have hci : ContinuousOn (fun s => T1 s τ) (Set.uIcc s₀ s₁) :=
        hT1.comp (f := fun s : ℝ => (s, τ)) (by fun_prop)
          fun s hs' => ⟨hIcc (hu ▸ hs'), Set.mem_univ τ⟩
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs' => hf s (hIcc (hu ▸ hs')) τ) hci.intervalIntegrable, c1]
    simp only [hinner]
    rw [intervalIntegral.integral_sub
      ((L.continuous_conn_fibre_apply (hmem s₁ (Set.right_mem_Icc.2 hs)) _).intervalIntegrable
        _ _)
      ((L.continuous_conn_fibre_apply (hmem s₀ (Set.left_mem_Icc.2 hs)) _).intervalIntegrable
        _ _)]
    rfl

/-- **Integrality of the periods (the Chern numbers are integers).** Let `L` be `ℓ`-periodic
cocycle data over `Ω × ℝ` with curvature `F`, and `γ` a `C¹` curve with `γ([a, b]) ⊆ Ω` and
`γ a = γ b`. Then the integral of `F` over the torus `γ × [0, ℓ]` lies in `2πℤ`.

Proof: cut `[a, b]` into finitely many intervals, each mapped into the base of one chart
(Lebesgue number); on each piece Stokes' theorem gives the difference of the fibre integrals at
the two ends (`IsPeriodic.integral_rect`); at each cut point, and at the closing point, the
fibre integrals in two charts differ by an element of `2πℤ` (`IsPeriodic.fibreIntegral_sub`). -/
theorem IsPeriodic.torusPeriod_mem {L : LiftBundleData ι Ω F} {ℓ : ℝ} (hper : L.IsPeriodic ℓ)
    {γ : ℝ → Space} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hΩ : ∀ s ∈ Set.Icc a b, γ s ∈ Ω) (hclosed : γ a = γ b) :
    ∃ n : ℤ, torusPeriod F γ a b ℓ = 2 * Real.pi * n := by
  let c : ι → Set (Set.Icc a b) := fun i => {s | γ s ∈ L.base i}
  have hc₁ : ∀ i, IsOpen (c i) := fun i =>
    (L.isOpen_base i).preimage (hγ.continuous.comp continuous_subtype_val)
  have hc₂ : (Set.univ : Set (Set.Icc a b)) ⊆ ⋃ i, c i := fun s _ => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (L.cover (hΩ s s.2))
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, ⟨m, hm⟩, hsub⟩ := exists_monotone_Icc_subset_open_cover_Icc hab hc₁ hc₂
  choose idx hidx using hsub
  have hle : ∀ n, (t n : ℝ) ≤ t (n + 1) := fun n => hmono (Nat.le_succ n)
  have hmem : ∀ n, ∀ s ∈ Set.Icc (t n : ℝ) (t (n + 1)), γ s ∈ L.base (idx n) := by
    intro n s hs
    have hsab : s ∈ Set.Icc a b := ⟨(t n).2.1.trans hs.1, hs.2.trans (t (n + 1)).2.2⟩
    exact hidx n (show (⟨s, hsab⟩ : Set.Icc a b) ∈ Set.Icc (t n) (t (n + 1)) from ⟨hs.1, hs.2⟩)
  have key : ∀ n, IntervalIntegrable
      (fun s => ∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)])
        MeasureTheory.volume a (t n) ∧
      ∃ k : ℤ, ∫ s in a..(t n), ∫ τ in (0 : ℝ)..ℓ, F (γ s, τ) ![(deriv γ s, 0), (0, 1)] =
        L.fibreIntegral (idx n) ℓ (γ (t n)) - L.fibreIntegral (idx 0) ℓ (γ a) +
          2 * Real.pi * k := by
    intro n
    induction n with
    | zero =>
      rw [ht0]
      exact ⟨IntervalIntegrable.refl, 0, by simp⟩
    | succ n ih =>
      obtain ⟨hint, k, hk⟩ := ih
      obtain ⟨hint', hrect⟩ := hper.integral_rect hγ (i := idx n) (hle n) (hmem n)
      obtain ⟨k', hk'⟩ := hper.fibreIntegral_sub (i := idx n) (j := idx (n + 1))
        (x := γ (t (n + 1)))
        ⟨hmem n _ (Set.right_mem_Icc.2 (hle n)), hmem (n + 1) _ (Set.left_mem_Icc.2 (hle (n + 1)))⟩
      refine ⟨hint.trans hint', k + k', ?_⟩
      rw [← intervalIntegral.integral_add_adjacent_intervals hint hint', hk, hrect]
      push_cast
      linarith
  obtain ⟨-, k, hk⟩ := key m
  have hb : (t m : ℝ) = b := hm m le_rfl
  have ha0 : γ a ∈ L.base (idx 0) := by
    have := hmem 0 (t 0) (Set.left_mem_Icc.2 (hle 0))
    rwa [ht0] at this
  have hbm : γ a ∈ L.base (idx m) := by
    have := hmem m (t m) (Set.left_mem_Icc.2 (hle m))
    rwa [hb, ← hclosed] at this
  obtain ⟨k', hk'⟩ := hper.fibreIntegral_sub (i := idx m) (j := idx 0) (x := γ a) ⟨hbm, ha0⟩
  refine ⟨k + k', ?_⟩
  rw [hb, ← hclosed] at hk
  unfold torusPeriod
  rw [hk]
  push_cast
  linarith

/-- **Integrality of the Chern number**: for `ℓ`-periodic cocycle data with curvature `F` the
Chern number over every torus `γ × S¹_ℓ` (`γ` a closed `C¹` loop in `Ω`) is an integer. -/
theorem IsPeriodic.chernNumber_mem_int {L : LiftBundleData ι Ω F} {ℓ : ℝ}
    (hper : L.IsPeriodic ℓ) {γ : ℝ → Space} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hΩ : ∀ s ∈ Set.Icc a b, γ s ∈ Ω) (hclosed : γ a = γ b) :
    ∃ n : ℤ, chernNumber F γ a b ℓ = n :=
  (chernNumber_mem_int_iff F γ a b ℓ).2 (hper.torusPeriod_mem hγ hab hΩ hclosed)

/-- **The obstruction.** If the period of `F` over one torus `γ × [0, ℓ]` is not in `2πℤ`, then
no cocycle data with curvature `F` over `Ω × ℝ` (cylinder charts) are `ℓ`-periodic: `F` is not
the curvature of a `U(1)` connection given by such data on `Ω × S¹_ℓ`. -/
theorem not_isPeriodic_of_torusPeriod {ℓ : ℝ} {γ : ℝ → Space} (hγ : ContDiff ℝ 1 γ) {a b : ℝ}
    (hab : a ≤ b) (hΩ : ∀ s ∈ Set.Icc a b, γ s ∈ Ω) (hclosed : γ a = γ b)
    (hno : ¬ ∃ n : ℤ, torusPeriod F γ a b ℓ = 2 * Real.pi * n) (L : LiftBundleData ι Ω F) :
    ¬ L.IsPeriodic ℓ :=
  fun hper => hno (hper.torusPeriod_mem hγ hab hΩ hclosed)

/-- **Quantisation is necessary for the lift.** If cocycle data with curvature the lift of the
flux form of `B` are `ℓ`-periodic, then `ℓ ∮_γ B · dl ∈ 2πℤ` for every closed `C¹` loop `γ` in
`Ω`. -/
theorem IsPeriodic.circulation_mem {B : Space → Space}
    {L : LiftBundleData ι Ω (hymLift (fluxField B))} {ℓ : ℝ} (hper : L.IsPeriodic ℓ)
    {γ : ℝ → Space} (hγ : ContDiff ℝ 1 γ) {a b : ℝ} (hab : a ≤ b)
    (hΩ : ∀ s ∈ Set.Icc a b, γ s ∈ Ω) (hclosed : γ a = γ b) :
    ∃ n : ℤ, ℓ * lineIntegral B γ a b = 2 * Real.pi * n :=
  (torusPeriod_hymLift_mem_iff B γ a b ℓ).1 (hper.torusPeriod_mem hγ hab hΩ hclosed)

end LiftBundleData

end PlasmaLean.Forms
