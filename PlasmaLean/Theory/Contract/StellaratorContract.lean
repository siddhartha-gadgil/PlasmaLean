/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Vacuum
public import PlasmaLean.Theory.Fields.Maxwell
public import PlasmaLean.Theory.Kinetic.Omnigeneity
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Stellarator contract, clauses C1 and C2 (definitions and sanity triad; Q-21)

Normative specification: `notes/formalization/00-model-contracts.md`, section "Stellarator
contract: C1, C2 and C5"; plan question Q-21, goal G-11.

## C1: net toroidal current and rotational transform of the field

* `ampereCurrent μ₀ B x = (∇ × B)(x)/μ₀`: the Ampère current of the **same** field (not a
  separately supplied `J`).
* `cylPoint R φ z`: the point with cylindrical coordinates `(R, φ, z)`.
* `FieldTorus B R z ι`: a continuous torus `(θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ)` in cylindrical
  form (`φ` the geometric toroidal angle), `2π`-periodic in both angles, `R > 0`, on which the
  field-line flow is **conjugate to the linear flow with rotation number `ι`**: every line
  `t ↦ (θ + ι t, φ + t)` is mapped to a curve tangent to `B` (`flow`).
* `PoloidalAngle R z R₀ z₀ Θ`: the angle convention. `Θ` is a continuous polar angle of
  `(R − R₀, z − z₀)` about a fixed reference circle `R = R₀, z = z₀` that winds once in `θ` and
  not at all in `φ`. Without such a convention `ι` is defined only modulo integers
  (`θ ↦ θ + nφ` changes `ι` by `n`).
* `IotaOnTorus B R z ι`: `FieldTorus` plus a poloidal-angle convention. `IotaOnTorus.tendsto`:
  along every field line on the torus the poloidal angle advances at the asymptotic rate `ι`
  per toroidal radian (`(Θ − Θ₀)/φ → ι`), the physical definition of the rotational transform.
  `ι` is signed (its sign is the handedness of the field lines); C1 bounds `|ι|`.
* **Net toroidal current, intrinsically (Ampère's law)**: `lineIntegral B γ a b =
  ∫_a^b ⟪B(γ t), γ'(t)⟫ dt`; `poloidalLoop R z φ₀ θ = cylPoint (R θ φ₀) φ₀ (z θ φ₀)`, the
  poloidal loop of the torus itself at toroidal angle `φ₀`;
  `poloidalCirculation B R z φ₀ = ∮ B · dl` over `θ ∈ [-π, π]`; and
  `loopCurrent μ₀ B R z φ₀ = μ₀⁻¹ ∮ B · dl`. The loop is fixed by the surface data: there is no
  choice of spanning surface.
* `SurfaceData`, `CurrentFreeTransform μ₀ B S I_max ι_min` (clause C1): `μ₀ > 0` and a nonempty
  family `S` of surfaces, each a torus with transform `|ι| ≥ ι_min > 0` whose poloidal loop is
  `C¹`, along which `B` is continuous, and around which `|μ₀⁻¹ ∮ B · dl| ≤ I_max`, all for the
  same field `B`.

Section flux (auxiliary, **not** the C1 quantity):
* `netToroidalCurrent μ₀ B X ζ₀ k₀`: the flux `∫₀^{k₀} ∫_{-π}^{π} J · (∂_k X × ∂_χ X) dχ dk`
  of the Ampère current through the section `ζ = ζ₀`, `0 ≤ k ≤ k₀`, of a toroidal coordinate map
  `X : (k, χ, ζ) ↦ x`, oriented by `∂_k X × ∂_χ X` (the form of
  `LandremanFamily2FluxLabels.torCurrent`). `NetCurrentBound`, `CurrentFree` (`I_max = 0`) and
  `SectionSpans` (outer edge the loop, inner edge a point) are section-flux notions. Without
  regularity the section flux is not the circulation: a pinched section spanning the loop has
  flux `0` for every field (`Sanity/AuditRefreshContract`, audit finding AR-H1). For regular
  sections (`C²` map, `C¹` field, matched seams) Stokes' theorem identifies the two
  (`Theory/Contract/SectionStokes`, `netToroidalCurrent_eq_lineIntegral_div`).

Sanity triad (C1):
* witness lemma: `lineIntegral_eq_zero_of_potential` (FTC), `inner_toroidal_poloidalLoop` (a
  purely toroidal field is orthogonal to a loop of constant `φ`), and
  `poloidalCirculation_eq_zero_of_potential`: a field equal near the loop to a purely toroidal
  field plus the gradient of a single-valued `C¹` potential has zero circulation around every
  closed `C¹` poloidal loop; hence `currentFreeTransform_of_potential` (C1 with `I_max = 0`);
* degenerate: `poloidalCirculation_zero_field`, `netToroidalCurrent_zero_field`;
* **tokamak exclusion**: `iota_eq_zero_of_purelyToroidal`: for a purely toroidal field
  (`B_z = 0`, `B · (x, y, 0) = 0`; the vacuum axisymmetric field `B = (μ₀ I/2πR) e_φ` is one)
  every `IotaOnTorus` has `ι = 0`; hence `not_currentFreeTransform_of_purelyToroidal`: such a
  field fails C1 for every `I_max` and every `ι_min > 0`, although it carries no current;
* counterexamples: `netToroidalCurrent_rotation`/`rotation_not_currentFree` (section flux of the
  uniform-current field `B = e_z × x`); its loop circulation is `2π a²` around a circular loop of
  radius `a` (`Sanity/AuditRefreshContract`, `rotation_poloidalCirculation`), so it fails the C1
  current clause with `I_max = 0`; the toroidal counterexample is Landreman family 2
  (`Design/LandremanNetCurrent`, `family2_loopCurrent_eq`, `family2_not_currentFreeTransform`).

Witnesses and instances in `Design/RationalStellaratorContract` (the rational stellarator vacuum
field with the KAM torus A, and the circular torus of the field `∇φ` with `ι = 0`) and
`Design/DommaschkQA3` (zero circulation around every poloidal loop off the axis).

## C2: omnigeneity in the Boozer guiding-centre model

Model scope: the vacuum Boozer guiding-centre **model** of `Theory/Kinetic/BoozerGuidingCentre`
(supplied equations of motion and orbits, chart `ψ > 0`; `B` and `ι` are independent inputs, so
the model does not itself enforce Maxwell's equations). `OmnigenousOn` quantifies over every
species (`m > 0`, `q ≠ 0`), every `μ ≥ 0` and every energy, so it covers thermal ions and
electrons as well as alphas.

* `OmnigeneityContract F c κ_max` (clause C2): `0 < c`, `0 ≤ κ_max` and
  `ApproxOmnigenousOn F c κ_max` (per-bounce radial displacement `≤ κ_max (H/|q|) τ`);
  `κ_max = 0` is exact omnigeneity (`omnigeneityContract_zero_iff`).
* `BoozerAxisymmetric F`: `∂_φ B = 0` on the chart.

Sanity (C2):
* `omnigenousOn_of_axisymmetric`: axisymmetric with `ι ≥ ι_min > 0` ⇒ omnigenous (quasi-
  axisymmetry with helicity `(0, 1)`, `omnigenousOn_of_exactQS`);
* `omnigenousOn_of_axisymmetric_iota_zero`: axisymmetric with `ι = 0` on the region ⇒
  omnigenous (vacuously: `ρ̇ = 0`, so there are no trapped bounces); together with the tokamak
  exclusion this is the consistency check "an axisymmetric current-free field passes C2 and fails
  C1";
* degenerate: `constField_omnigeneityContract`; counterexample:
  `driftMirror_not_omnigeneityContract`.

**Not covered (open):** the effective ripple `ε_eff` (Nemov et al. 1999) and the link to `1/ν`
transport; the bounce-averaged drift as a function on velocity space; trapped-orbit existence for
a given field; the identification of the Boozer model with a Cartesian field; the theorem
"axisymmetric, current-free, nested surfaces ⇒ purely toroidal" (needs the maximum principle for
`Δ*ψ = 0`); section-independence of the section flux; Stokes' theorem for loops that do not bound a
coordinate section; reference curves that are not fixed circles.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Contract

open Real Set Filter Topology Matrix WithLp PlasmaLean.Fields PlasmaLean.Vacuum

/-! ## Section flux of the Ampère current (auxiliary; not the C1 quantity)

The C1 current is the loop circulation `loopCurrent` below. The section flux agrees with it only
for regular sections (`Theory/Contract/SectionStokes`). -/

/-- The coordinate point `(k, χ, ζ)` of a toroidal coordinate system, as an element of
`Space`. -/
@[expose] def coordPt (k χ ζ : ℝ) : Space := toLp 2 ![k, χ, ζ]

/-- The flux density `V · (a × b)` of a vector `V` through the oriented area element spanned by
`a` and `b`. -/
@[expose] def tripleFlux (V a b : Space) : ℝ := ofLp V ⬝ᵥ (ofLp a ⨯₃ ofLp b)

/-- The **Ampère current density of the field itself**, `J = (∇ × B)/μ₀`, from the actual
Fréchet derivative of `B`. -/
@[expose] def ampereCurrent (μ₀ : ℝ) (B : Space → Space) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ B x)

/-- **Section flux** of the Ampère current of `B` through the section `ζ = ζ₀`, `0 ≤ k ≤ k₀`,
`-π ≤ χ ≤ π` of the toroidal coordinate map `X : (k, χ, ζ) ↦ x`:
`I = ∫₀^{k₀} ∫_{-π}^{π} J · (∂_k X × ∂_χ X) dχ dk`, `J = (∇ × B)/μ₀` (units: A when `B` is in T,
lengths in m and `μ₀` in SI). This is the net toroidal current only for a regular section
spanning the poloidal loop (Stokes, `SectionStokes.netToroidalCurrent_eq_lineIntegral_div`);
clause C1 uses the loop circulation `loopCurrent` instead. -/
@[expose] def netToroidalCurrent (μ₀ : ℝ) (B X : Space → Space) (ζ₀ k₀ : ℝ) : ℝ :=
  ∫ k in (0 : ℝ)..k₀, ∫ χ in (-π)..π,
    tripleFlux (ampereCurrent μ₀ B (X (coordPt k χ ζ₀)))
      (fderiv ℝ X (coordPt k χ ζ₀) (basis 0)) (fderiv ℝ X (coordPt k χ ζ₀) (basis 1))

/-- **Section-flux bound**: `|I(k₀)| ≤ I_max` for the section flux through every section label
`k₀ ∈ K` (a section-flux notion, not clause C1). -/
@[expose] def NetCurrentBound (μ₀ : ℝ) (B X : Space → Space) (ζ₀ : ℝ) (K : Set ℝ)
    (Imax : ℝ) : Prop :=
  ∀ k₀ ∈ K, |netToroidalCurrent μ₀ B X ζ₀ k₀| ≤ Imax

/-- **Section-current-free** on the sections `K`: the section-flux bound with `I_max = 0` (a
section-flux notion, not clause C1). -/
@[expose] def CurrentFree (μ₀ : ℝ) (B X : Space → Space) (ζ₀ : ℝ) (K : Set ℝ) : Prop :=
  NetCurrentBound μ₀ B X ζ₀ K 0

/-- The section `ζ = ζ₀`, `0 ≤ k ≤ k₀` of `X` **spans the loop** `γ` in the weak sense: `k₀ ≥ 0`,
its outer edge `k = k₀` is `γ` and its inner edge `k = 0` is a single point. Nothing is required
of the seams `χ = ±π` or of the regularity of `X`, so this does not make the section flux equal
to the circulation of `γ` (`Sanity/AuditRefreshContract.pinch_spans`). -/
@[expose] def SectionSpans (X : Space → Space) (ζ₀ k₀ : ℝ) (γ : ℝ → Space) : Prop :=
  0 ≤ k₀ ∧ (∀ χ, X (coordPt k₀ χ ζ₀) = γ χ) ∧ ∀ χ χ', X (coordPt 0 χ ζ₀) = X (coordPt 0 χ' ζ₀)

section Current
variable {μ₀ : ℝ} {B X : Space → Space} {ζ₀ : ℝ} {K : Set ℝ}

/-- Section-current-free means zero section flux through every section of `K`. -/
theorem currentFree_iff :
    CurrentFree μ₀ B X ζ₀ K ↔ ∀ k₀ ∈ K, netToroidalCurrent μ₀ B X ζ₀ k₀ = 0 := by
  simp only [CurrentFree, NetCurrentBound, abs_nonpos_iff]

/-- The section-flux bound is monotone in `I_max`. -/
theorem NetCurrentBound.mono {Imax Imax' : ℝ} (h : NetCurrentBound μ₀ B X ζ₀ K Imax)
    (hI : Imax ≤ Imax') : NetCurrentBound μ₀ B X ζ₀ K Imax' :=
  fun k hk => (h k hk).trans hI

/-- A section-current-free field satisfies every nonnegative section-flux bound. -/
theorem CurrentFree.netCurrentBound {Imax : ℝ} (h : CurrentFree μ₀ B X ζ₀ K) (hI : 0 ≤ Imax) :
    NetCurrentBound μ₀ B X ζ₀ K Imax :=
  NetCurrentBound.mono h hI

/-- The kernel curl `curlOp` agrees with `Fields.curl`. -/
theorem curlOp_eq_fieldsCurl (L : Space →L[ℝ] Space) : curlOp L = curl L := by
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  apply space_ext <;> simp [curlOp, h0, h1, h2]

/-- In a vacuum region the Ampère current vanishes. -/
theorem ampereCurrent_eq_zero_of_vacuum {Ω : Set Space} (hB : VacuumField Ω B) {x : Space}
    (hx : x ∈ Ω) (μ₀ : ℝ) : ampereCurrent μ₀ B x = 0 := by
  have h := hB.curl_eq_zero x hx
  rw [fieldCurl, curlOp_eq_fieldsCurl] at h
  simp [ampereCurrent, h]

/-- An integral over a section whose integrand vanishes on the section is zero. -/
theorem netToroidalCurrent_eq_zero_of_eqOn {k₀ : ℝ} (hk₀ : 0 ≤ k₀)
    (h : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, ampereCurrent μ₀ B (X (coordPt k χ ζ₀)) = 0) :
    netToroidalCurrent μ₀ B X ζ₀ k₀ = 0 := by
  unfold netToroidalCurrent
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
  · simp
  intro k hk
  rw [uIcc_of_le hk₀] at hk
  simp only
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
  · simp
  intro χ hχ
  rw [uIcc_of_le (by linarith [pi_pos])] at hχ
  simp only [h k hk χ hχ, tripleFlux, ofLp_zero, zero_dotProduct]

/-- **Vacuum ⇒ zero section flux**: if `B` is a vacuum field on `Ω` and the section lies in `Ω`,
the flux of the Ampère current through it vanishes. -/
theorem netToroidalCurrent_eq_zero_of_vacuum {Ω : Set Space} (hB : VacuumField Ω B) {k₀ : ℝ}
    (hk₀ : 0 ≤ k₀) (hX : ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, X (coordPt k χ ζ₀) ∈ Ω) :
    netToroidalCurrent μ₀ B X ζ₀ k₀ = 0 :=
  netToroidalCurrent_eq_zero_of_eqOn hk₀ fun k hk χ hχ =>
    ampereCurrent_eq_zero_of_vacuum hB (hX k hk χ hχ) μ₀

/-- A vacuum field is section-current-free on every family of sections lying in its region. -/
theorem currentFree_of_vacuum {Ω : Set Space} (hB : VacuumField Ω B)
    (hX : ∀ k₀ ∈ K, 0 ≤ k₀ ∧ ∀ k ∈ Icc 0 k₀, ∀ χ ∈ Icc (-π) π, X (coordPt k χ ζ₀) ∈ Ω) :
    CurrentFree μ₀ B X ζ₀ K :=
  currentFree_iff.2 fun k₀ hk => netToroidalCurrent_eq_zero_of_vacuum hB (hX k₀ hk).1 (hX k₀ hk).2

end Current

/-- **Degenerate case**: the zero field has zero section flux through every section. -/
theorem netToroidalCurrent_zero_field (μ₀ : ℝ) (X : Space → Space) (ζ₀ k₀ : ℝ) :
    netToroidalCurrent μ₀ (fun _ => 0) X ζ₀ k₀ = 0 := by
  simp [netToroidalCurrent, ampereCurrent, tripleFlux, curl]

/-- **Counterexample (uniform current, section flux)**: the field `B = e_z × x = (-y, x, 0)` has
`μ₀ J = 2 e_z`, so its current through the slab section `{0 ≤ x ≤ k₀, -π ≤ y ≤ π, z = ζ₀}` of the
identity chart is `4π k₀/μ₀`. -/
theorem netToroidalCurrent_rotation (μ₀ ζ₀ k₀ : ℝ) :
    netToroidalCurrent μ₀ (crossBilinear (basis 2)) (fun x => x) ζ₀ k₀ = 4 * π * k₀ / μ₀ := by
  have hJ : ∀ x : Space, tripleFlux (ampereCurrent μ₀ (crossBilinear (basis 2)) x)
      (fderiv ℝ (fun x : Space => x) x (basis 0)) (fderiv ℝ (fun x : Space => x) x (basis 1)) =
      2 / μ₀ := by
    intro x
    rw [ampereCurrent, ContinuousLinearMap.fderiv, curl_rotation, fderiv_fun_id]
    simp [tripleFlux, cross_apply, dotProduct, basis]
    ring
  simp only [netToroidalCurrent, hJ, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The uniform-current field is not section-current-free on any family containing a section
`k₀ ≠ 0` of the identity chart (for `μ₀ ≠ 0`). -/
theorem rotation_not_currentFree {μ₀ ζ₀ : ℝ} (hμ : μ₀ ≠ 0) {K : Set ℝ} {k₀ : ℝ} (hk : k₀ ∈ K)
    (hk0 : k₀ ≠ 0) : ¬ CurrentFree μ₀ (crossBilinear (basis 2)) (fun x => x) ζ₀ K := by
  intro h
  have := currentFree_iff.1 h k₀ hk
  rw [netToroidalCurrent_rotation] at this
  have h4 : (4 * π) * k₀ = 0 := by
    rw [div_eq_zero_iff] at this
    exact this.resolve_right hμ
  rcases mul_eq_zero.1 h4 with h1 | h1
  · linarith [pi_pos]
  · exact hk0 h1

/-! ## Rotational transform on an invariant torus -/

/-- The point with cylindrical coordinates `(R, φ, z)`. -/
@[expose] def cylPoint (R φ z : ℝ) : Space := toLp 2 ![R * cos φ, R * sin φ, z]

/-- **Invariant torus with rotation number `ι`** (cylindrical form). The torus is
`(θ, φ) ↦ cylPoint (R θ φ) φ (z θ φ)`, with `φ` the geometric toroidal angle; it is continuous,
`2π`-periodic in `θ` and `φ`, has `R > 0`, and the field-line flow on it is conjugate to the
linear flow `(θ, φ) ↦ (θ + ι t, φ + t)`: every such line is mapped to a curve tangent to `B`
(velocity `c • B` for some scalar `c`; then `c ≠ 0`, since the curve has `φ̇ = 1`). -/
structure FieldTorus (B : Space → Space) (R z : ℝ → ℝ → ℝ) (ι : ℝ) : Prop where
  /-- `R` is continuous. -/
  continuous_R : Continuous (fun p : ℝ × ℝ => R p.1 p.2)
  /-- `z` is continuous. -/
  continuous_z : Continuous (fun p : ℝ × ℝ => z p.1 p.2)
  /-- The torus stays off the symmetry axis. -/
  R_pos : ∀ θ φ, 0 < R θ φ
  /-- `R` is `2π`-periodic in `θ`. -/
  per_θ_R : ∀ θ φ, R (θ + 2 * π) φ = R θ φ
  /-- `z` is `2π`-periodic in `θ`. -/
  per_θ_z : ∀ θ φ, z (θ + 2 * π) φ = z θ φ
  /-- `R` is `2π`-periodic in `φ`. -/
  per_φ_R : ∀ θ φ, R θ (φ + 2 * π) = R θ φ
  /-- `z` is `2π`-periodic in `φ`. -/
  per_φ_z : ∀ θ φ, z θ (φ + 2 * π) = z θ φ
  /-- The image of each line of slope `ι` is tangent to the field. -/
  flow : ∀ θ φ, ∃ c : ℝ,
    HasDerivAt (fun t => cylPoint (R (θ + t * ι) (φ + t)) (φ + t) (z (θ + t * ι) (φ + t)))
      (c • B (cylPoint (R θ φ) φ (z θ φ))) 0

/-- **Poloidal-angle convention**: `Θ` is a continuous polar angle of `(R − R₀, z − z₀)` about the
fixed reference circle `R = R₀, z = z₀`, winding once in `θ` and not at all in `φ`. -/
structure PoloidalAngle (R z : ℝ → ℝ → ℝ) (R₀ z₀ : ℝ) (Θ : ℝ → ℝ → ℝ) : Prop where
  /-- `Θ` is continuous. -/
  continuous : Continuous (fun p : ℝ × ℝ => Θ p.1 p.2)
  /-- `Θ` is a polar angle of `(R − R₀, z − z₀)` (the torus avoids the reference circle). -/
  polar : ∀ θ φ, ∃ r, 0 < r ∧ R θ φ - R₀ = r * cos (Θ θ φ) ∧ z θ φ - z₀ = r * sin (Θ θ φ)
  /-- One poloidal turn in `θ`. -/
  wind_θ : ∀ θ φ, Θ (θ + 2 * π) φ = Θ θ φ + 2 * π
  /-- No poloidal winding in `φ`. -/
  wind_φ : ∀ θ φ, Θ θ (φ + 2 * π) = Θ θ φ

/-- **Rotational transform `ι` of the field `B` on the torus `(R, z)`**: an invariant torus with
rotation number `ι` (`FieldTorus`) whose angle `θ` is poloidal in the sense of
`PoloidalAngle` about some fixed reference circle. -/
@[expose] def IotaOnTorus (B : Space → Space) (R z : ℝ → ℝ → ℝ) (ι : ℝ) : Prop :=
  FieldTorus B R z ι ∧ ∃ R₀ z₀ : ℝ, ∃ Θ : ℝ → ℝ → ℝ, PoloidalAngle R z R₀ z₀ Θ

/-- A continuous function on `ℝ²`, `2π`-periodic in both variables, is bounded. -/
theorem bound_of_doubly_periodic {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (h1 : ∀ a b, f (a + 2 * π, b) = f (a, b)) (h2 : ∀ a b, f (a, b + 2 * π) = f (a, b)) :
    ∃ C, ∀ p, |f p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc 0 (2 * π) ×ˢ Icc 0 (2 * π)) hf.continuousOn
  refine ⟨C, fun ⟨a, b⟩ => ?_⟩
  obtain ⟨a', ha', e1⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun a => f (a, b))
    (fun a => h1 a b) two_pi_pos a
  obtain ⟨b', hb', e2⟩ := Function.Periodic.exists_mem_Ico₀ (f := fun b => f (a', b))
    (fun b => h2 a' b) two_pi_pos b
  rw [e1, e2, ← Real.norm_eq_abs]
  exact hC _ ⟨Ico_subset_Icc_self ha', Ico_subset_Icc_self hb'⟩

section Torus
variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {ι : ℝ}

/-- `Θ − θ` is bounded for a poloidal angle. -/
theorem PoloidalAngle.exists_bound {R₀ z₀ : ℝ} {Θ : ℝ → ℝ → ℝ}
    (hΘ : PoloidalAngle R z R₀ z₀ Θ) : ∃ C, ∀ θ φ, |Θ θ φ - θ| ≤ C := by
  obtain ⟨C, hC⟩ := bound_of_doubly_periodic (f := fun p : ℝ × ℝ => Θ p.1 p.2 - p.1)
    (hΘ.continuous.sub continuous_fst) (fun a b => by simp only [hΘ.wind_θ]; ring)
    (fun a b => by simp only [hΘ.wind_φ])
  exact ⟨C, fun θ φ => hC (θ, φ)⟩

/-- **The poloidal angle advances at rate `ι`** along the line of slope `ι`:
`(Θ(θ₀ + s ι, s) − Θ(θ₀, 0))/s → ι` as `s → ∞`. -/
theorem PoloidalAngle.tendsto {R₀ z₀ : ℝ} {Θ : ℝ → ℝ → ℝ} (hΘ : PoloidalAngle R z R₀ z₀ Θ)
    (ι θ₀ : ℝ) :
    Tendsto (fun s => (Θ (θ₀ + s * ι) s - Θ θ₀ 0) / s) atTop (𝓝 ι) := by
  obtain ⟨C, hC⟩ := hΘ.exists_bound
  set b : ℝ → ℝ := fun s => Θ (θ₀ + s * ι) s - (θ₀ + s * ι) + θ₀ - Θ θ₀ 0 with hb
  have hbd : ∀ s, |b s| ≤ C + |θ₀ - Θ θ₀ 0| := fun s => by
    have := hC (θ₀ + s * ι) s
    calc |b s| = |(Θ (θ₀ + s * ι) s - (θ₀ + s * ι)) + (θ₀ - Θ θ₀ 0)| := by
          rw [hb]; ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by linarith)
  have h0 : Tendsto (fun s => b s / s) atTop (𝓝 0) := by
    have hlim : Tendsto (fun s : ℝ => (C + |θ₀ - Θ θ₀ 0|) / s) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with s hs
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hbd s) hs.le
  have h1 := h0.const_add ι
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  rw [hb]
  field_simp
  ring

/-- The tangency of `FieldTorus` at every point of a line of slope `ι`. -/
theorem FieldTorus.flow_at (hT : FieldTorus B R z ι) (θ₀ s : ℝ) : ∃ c : ℝ,
    HasDerivAt (fun t => cylPoint (R (θ₀ + t * ι) t) t (z (θ₀ + t * ι) t))
      (c • B (cylPoint (R (θ₀ + s * ι) s) s (z (θ₀ + s * ι) s))) s := by
  obtain ⟨c, hc⟩ := hT.flow (θ₀ + s * ι) s
  refine ⟨c, ?_⟩
  have h := HasDerivAt.comp_sub_const s s (by simpa using hc)
  convert h using 1
  funext t
  rw [show θ₀ + s * ι + (t - s) * ι = θ₀ + t * ι by ring, show s + (t - s) = t by ring]

/-- **The field line on the torus**: `IotaOnTorus` gives curves tangent to `B` along which the
poloidal angle advances at the asymptotic rate `ι` per toroidal radian; this identifies `ι` with
the physical rotational transform `lim ΔΘ/Δφ` along field lines. -/
theorem IotaOnTorus.tendsto (h : IotaOnTorus B R z ι) (θ₀ : ℝ) :
    (∀ s, ∃ c : ℝ,
      HasDerivAt (fun t => cylPoint (R (θ₀ + t * ι) t) t (z (θ₀ + t * ι) t))
        (c • B (cylPoint (R (θ₀ + s * ι) s) s (z (θ₀ + s * ι) s))) s) ∧
    ∃ R₀ z₀ : ℝ, ∃ Θ : ℝ → ℝ → ℝ, PoloidalAngle R z R₀ z₀ Θ ∧
      Tendsto (fun s => (Θ (θ₀ + s * ι) s - Θ θ₀ 0) / s) atTop (𝓝 ι) := by
  obtain ⟨hT, R₀, z₀, Θ, hΘ⟩ := h
  exact ⟨hT.flow_at θ₀, R₀, z₀, Θ, hΘ, hΘ.tendsto ι θ₀⟩

/-- A **purely toroidal** field: no vertical component and no component along the cylindrical
radius, `B_z = 0` and `x B_x + y B_y = 0` (`B = B_φ e_φ`). The vacuum axisymmetric field
`B = (μ₀ I/2πR) e_φ` is purely toroidal. -/
@[expose] def PurelyToroidal (B : Space → Space) : Prop :=
  ∀ x : Space, B x 2 = 0 ∧ x 0 * B x 0 + x 1 * B x 1 = 0

/-- Coordinates of a cylindrical point. -/
theorem cylPoint_coords (R φ z : ℝ) :
    cylPoint R φ z 0 = R * cos φ ∧ cylPoint R φ z 1 = R * sin φ ∧ cylPoint R φ z 2 = z := by
  simp [cylPoint]

/-- Derivative of a coordinate along a curve in space. -/
theorem hasDerivAt_coord {γ : ℝ → Space} {v : Space} {t : ℝ} (h : HasDerivAt γ v t)
    (i : Fin 3) : HasDerivAt (fun s => γ s i) (v i) t := by
  have := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t h
  simpa [Function.comp_def] using this

/-- In a purely toroidal field, `R` and `z` are constant along every line of slope `ι` on an
invariant torus (field lines are horizontal circles about the symmetry axis). -/
theorem FieldTorus.Rz_const_of_purelyToroidal (hT : FieldTorus B R z ι) (hB : PurelyToroidal B)
    (θ₀ s : ℝ) : R (θ₀ + s * ι) s = R θ₀ 0 ∧ z (θ₀ + s * ι) s = z θ₀ 0 := by
  set γ : ℝ → Space := fun t => cylPoint (R (θ₀ + t * ι) t) t (z (θ₀ + t * ι) t) with hγ
  have hd : ∀ t, ∃ c : ℝ, HasDerivAt γ (c • B (γ t)) t := hT.flow_at θ₀
  -- the vertical coordinate
  have hz : ∀ t, HasDerivAt (fun t => z (θ₀ + t * ι) t) 0 t := fun t => by
    obtain ⟨c, hc⟩ := hd t
    have h2 := hasDerivAt_coord hc 2
    simp only [hγ, (cylPoint_coords _ _ _).2.2, PiLp.smul_apply, smul_eq_mul,
      (hB _).1, mul_zero] at h2
    exact h2
  -- the squared radius
  have hR : ∀ t, HasDerivAt (fun t => R (θ₀ + t * ι) t ^ 2) 0 t := fun t => by
    obtain ⟨c, hc⟩ := hd t
    have h0 := hasDerivAt_coord hc 0
    have h1 := hasDerivAt_coord hc 1
    have hs := (h0.pow 2).add (h1.pow 2)
    have hfun : (fun s => γ s 0 ^ 2 + γ s 1 ^ 2) = fun t => R (θ₀ + t * ι) t ^ 2 := by
      funext s
      simp only [hγ, (cylPoint_coords _ _ _).1, (cylPoint_coords _ _ _).2.1]
      linear_combination R (θ₀ + s * ι) s ^ 2 * cos_sq_add_sin_sq s
    have hval : (↑(2 : ℕ) * γ t 0 ^ (2 - 1) * (c • B (γ t)) 0 +
        ↑(2 : ℕ) * γ t 1 ^ (2 - 1) * (c • B (γ t)) 1) = 0 := by
      simp only [PiLp.smul_apply, smul_eq_mul, Nat.cast_ofNat, pow_one,
        show (2 : ℕ) - 1 = 1 from rfl]
      linear_combination (2 * c) * (hB (γ t)).2
    rw [hval] at hs
    have hs' : HasDerivAt (fun s => γ s 0 ^ 2 + γ s 1 ^ 2) 0 t := hs
    rwa [hfun] at hs'
  have hzc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt)
    (fun t => (hz t).deriv) s 0
  have hRc := is_const_of_deriv_eq_zero (fun t => (hR t).differentiableAt)
    (fun t => (hR t).deriv) s 0
  simp only [zero_mul, add_zero] at hzc hRc
  refine ⟨?_, hzc⟩
  have h1 := hT.R_pos (θ₀ + s * ι) s
  have h2 := hT.R_pos θ₀ 0
  exact (pow_left_inj₀ h1.le h2.le two_ne_zero).1 hRc

/-- A continuous real function with `f 0 = 0` and `cos (f s) = 1` everywhere vanishes
identically (its values lie in `2πℤ`). -/
theorem eq_zero_of_cos_eq_one {f : ℝ → ℝ} (hf : Continuous f) (h0 : f 0 = 0)
    (h1 : ∀ s, cos (f s) = 1) (s : ℝ) : f s = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := (cos_eq_one_iff (f s)).1 (h1 s)
  have hivt := intermediate_value_uIcc (a := 0) (b := s) hf.continuousOn
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hn' : (n : ℝ) < 0 := by
      by_contra hc; have hc' := not_lt.1 hc; nlinarith [pi_pos]
    have hn1 : (n : ℝ) ≤ -1 := by
      have h1 : n < 0 := by exact_mod_cast hn'
      have h2 : n ≤ -1 := by omega
      exact_mod_cast h2
    have hmem : -π ∈ uIcc (f 0) (f s) := by
      rw [h0, mem_uIcc]; right; constructor <;> nlinarith [pi_pos]
    obtain ⟨t, -, ht⟩ := hivt hmem
    have := h1 t
    rw [ht, cos_neg, cos_pi] at this
    norm_num at this
  · have hn' : (0 : ℝ) < n := by
      by_contra hc; have hc' := not_lt.1 hc; nlinarith [pi_pos]
    have hn1 : (1 : ℝ) ≤ n := by
      have h1 : 0 < n := by exact_mod_cast hn'
      have h2 : 1 ≤ n := by omega
      exact_mod_cast h2
    have hmem : π ∈ uIcc (f 0) (f s) := by
      rw [h0, mem_uIcc]; left; constructor <;> nlinarith [pi_pos]
    obtain ⟨t, -, ht⟩ := hivt hmem
    have := h1 t
    rw [ht, cos_pi] at this
    norm_num at this

/-- **Tokamak exclusion (vacuum axisymmetric case).** In a purely toroidal field (in particular
the vacuum axisymmetric field `B = (μ₀ I/2πR) e_φ`) every invariant torus with a poloidal-angle
convention has rotational transform `ι = 0`. -/
theorem iota_eq_zero_of_purelyToroidal (hB : PurelyToroidal B) (h : IotaOnTorus B R z ι) :
    ι = 0 := by
  obtain ⟨hT, R₀, z₀, Θ, hΘ⟩ := h
  -- the poloidal angle is constant along the line of slope `ι` through `(0, 0)`
  have hconst : ∀ s, Θ (0 + s * ι) s - Θ 0 0 = 0 := by
    refine eq_zero_of_cos_eq_one (f := fun s => Θ (0 + s * ι) s - Θ 0 0) ?_ (by simp) ?_
    · exact (hΘ.continuous.comp ((continuous_const.add (continuous_id.mul continuous_const)).prodMk
        continuous_id)).sub continuous_const
    · intro s
      obtain ⟨hRs, hzs⟩ := hT.Rz_const_of_purelyToroidal hB 0 s
      obtain ⟨r, hr, hRr, hzr⟩ := hΘ.polar (0 + s * ι) s
      obtain ⟨r₀, hr₀, hRr₀, hzr₀⟩ := hΘ.polar 0 0
      rw [hRs] at hRr
      rw [hzs] at hzr
      have hrr : r = r₀ := by
        have e : r ^ 2 = r₀ ^ 2 := by
          have a := cos_sq_add_sin_sq (Θ (0 + s * ι) s)
          have b := cos_sq_add_sin_sq (Θ 0 0)
          have := congrArg (· ^ 2) (hRr.symm.trans hRr₀)
          have := congrArg (· ^ 2) (hzr.symm.trans hzr₀)
          nlinarith
        exact (pow_left_inj₀ hr.le hr₀.le two_ne_zero).1 e
      subst hrr
      have hc : cos (Θ (0 + s * ι) s) = cos (Θ 0 0) :=
        mul_left_cancel₀ hr.ne' (hRr.symm.trans hRr₀)
      have hs' : sin (Θ (0 + s * ι) s) = sin (Θ 0 0) :=
        mul_left_cancel₀ hr.ne' (hzr.symm.trans hzr₀)
      rw [cos_sub, hc, hs', ← sq, ← sq]
      exact cos_sq_add_sin_sq _
  have hlim := hΘ.tendsto ι 0
  have hz : (fun s => (Θ (0 + s * ι) s - Θ 0 0) / s) = fun _ => 0 := by
    funext s; rw [hconst s, zero_div]
  rw [hz] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end Torus

/-! ## The net toroidal current as a loop circulation (Ampère's law) -/

/-- The **line integral** `∫_a^b ⟪B(γ t), γ'(t)⟫ dt` of the field `B` along the curve `γ`. -/
@[expose] def lineIntegral (B : Space → Space) (γ : ℝ → Space) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ⟪B (γ t), deriv γ t⟫

/-- The **poloidal loop** `θ ↦ cylPoint (R θ φ₀) φ₀ (z θ φ₀)` of the torus `(R, z)` at the
toroidal angle `φ₀` (a loop of constant geometric toroidal angle on the torus itself). -/
@[expose] def poloidalLoop (R z : ℝ → ℝ → ℝ) (φ₀ θ : ℝ) : Space :=
  cylPoint (R θ φ₀) φ₀ (z θ φ₀)

/-- The **poloidal circulation** `∮ B · dl` of `B` around the poloidal loop of the torus
`(R, z)` at toroidal angle `φ₀`, over one period `θ ∈ [-π, π]`, oriented by increasing `θ`. -/
@[expose] def poloidalCirculation (B : Space → Space) (R z : ℝ → ℝ → ℝ) (φ₀ : ℝ) : ℝ :=
  lineIntegral B (poloidalLoop R z φ₀) (-π) π

/-- **Net toroidal current enclosed by the poloidal loop**, by Ampère's law:
`I = μ₀⁻¹ ∮ B · dl` (units: A when `B` is in T, lengths in m and `μ₀` in SI). It depends only on
the field and the surface data `(R, z, φ₀)`. -/
@[expose] def loopCurrent (μ₀ : ℝ) (B : Space → Space) (R z : ℝ → ℝ → ℝ) (φ₀ : ℝ) : ℝ :=
  poloidalCirculation B R z φ₀ / μ₀

section Loop
variable {B : Space → Space} {R z : ℝ → ℝ → ℝ} {φ₀ : ℝ}

/-- **Fundamental theorem of calculus for line integrals.** If, along a `C¹` curve `γ`, `B` is
continuous and has the same tangential component as `g`, and `g = ∇Φ` along `γ`, then
`∫_a^b B · dl = Φ(γ b) − Φ(γ a)`. -/
theorem lineIntegral_eq_sub_of_potential {g : Space → Space} {γ : ℝ → Space} {Φ : Space → ℝ}
    (a b : ℝ) (hγ : ContDiff ℝ 1 γ) (hB : ∀ t, ContinuousAt B (γ t))
    (hg : ∀ t, ⟪B (γ t), deriv γ t⟫ = ⟪g (γ t), deriv γ t⟫)
    (hΦ : ∀ t, HasFDerivAt Φ (innerSL ℝ (g (γ t))) (γ t)) :
    lineIntegral B γ a b = Φ (γ b) - Φ (γ a) := by
  have hd : ∀ t, HasDerivAt γ (deriv γ t) t := fun t =>
    ((hγ.differentiable one_ne_zero) t).hasDerivAt
  have hcont : Continuous fun t => ⟪B (γ t), deriv γ t⟫ :=
    continuous_iff_continuousAt.2 fun t =>
      ((hB t).comp hγ.continuous.continuousAt).inner
        (hγ.continuous_deriv le_rfl).continuousAt
  unfold lineIntegral
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => Φ (γ t))
    (fun t _ => ?_) (hcont.intervalIntegrable _ _)
  have h := (hΦ t).comp_hasDerivAt t (hd t)
  rw [hg t]
  simpa [Function.comp_def] using h

/-- A closed `C¹` curve along which `B` is tangentially a gradient has zero circulation. -/
theorem lineIntegral_eq_zero_of_potential {g : Space → Space} {γ : ℝ → Space} {Φ : Space → ℝ}
    {a b : ℝ} (hγ : ContDiff ℝ 1 γ) (hB : ∀ t, ContinuousAt B (γ t))
    (hg : ∀ t, ⟪B (γ t), deriv γ t⟫ = ⟪g (γ t), deriv γ t⟫)
    (hΦ : ∀ t, HasFDerivAt Φ (innerSL ℝ (g (γ t))) (γ t)) (hclosed : γ a = γ b) :
    lineIntegral B γ a b = 0 := by
  rw [lineIntegral_eq_sub_of_potential a b hγ hB hg hΦ, hclosed, sub_self]

/-- A curve in space is differentiable when its three coordinates are. -/
theorem hasDerivAt_space3 {f0 f1 f2 : ℝ → ℝ} {d0 d1 d2 t : ℝ} (h0 : HasDerivAt f0 d0 t)
    (h1 : HasDerivAt f1 d1 t) (h2 : HasDerivAt f2 d2 t) :
    HasDerivAt (fun s => (toLp 2 ![f0 s, f1 s, f2 s] : Space)) (toLp 2 ![d0, d1, d2]) t := by
  have h := ((h0.smul_const (basis 0)).add (h1.smul_const (basis 1))).add
    (h2.smul_const (basis 2))
  convert h using 1
  · funext s; ext k; fin_cases k <;> simp [basis]
  · ext k; fin_cases k <;> simp [basis]

/-- The velocity of the poloidal loop: `(R' cos φ₀, R' sin φ₀, z')`. -/
theorem hasDerivAt_poloidalLoop {θ R' z' : ℝ} (hR : HasDerivAt (fun t => R t φ₀) R' θ)
    (hz : HasDerivAt (fun t => z t φ₀) z' θ) :
    HasDerivAt (poloidalLoop R z φ₀) (toLp 2 ![R' * cos φ₀, R' * sin φ₀, z']) θ :=
  hasDerivAt_space3 (hR.mul_const _) (hR.mul_const _) hz

/-- The poloidal loop of a torus with `C¹` profiles `R(·, φ₀)`, `z(·, φ₀)` is `C¹`. -/
theorem contDiff_poloidalLoop (hR : ContDiff ℝ 1 fun t => R t φ₀)
    (hz : ContDiff ℝ 1 fun t => z t φ₀) : ContDiff ℝ 1 (poloidalLoop R z φ₀) := by
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · simpa [poloidalLoop, cylPoint] using hR.mul contDiff_const
  · simpa [poloidalLoop, cylPoint] using hR.mul contDiff_const
  · simpa [poloidalLoop, cylPoint] using hz

/-- **A purely toroidal field is orthogonal to a loop of constant toroidal angle**:
`⟪T(γ θ), γ'(θ)⟫ = 0` for the poloidal loop `γ` (with `R > 0`). -/
theorem inner_toroidal_poloidalLoop {T : Space → Space} (hT : PurelyToroidal T) {θ : ℝ}
    (hRpos : 0 < R θ φ₀) (hR : DifferentiableAt ℝ (fun t => R t φ₀) θ)
    (hz : DifferentiableAt ℝ (fun t => z t φ₀) θ) :
    ⟪T (poloidalLoop R z φ₀ θ), deriv (poloidalLoop R z φ₀) θ⟫ = 0 := by
  rw [(hasDerivAt_poloidalLoop hR.hasDerivAt hz.hasDerivAt).deriv]
  obtain ⟨h2, h01⟩ := hT (poloidalLoop R z φ₀ θ)
  set x := poloidalLoop R z φ₀ θ with hx
  have hx0 : x 0 = R θ φ₀ * cos φ₀ := by simp [hx, poloidalLoop, cylPoint]
  have hx1 : x 1 = R θ φ₀ * sin φ₀ := by simp [hx, poloidalLoop, cylPoint]
  rw [hx0, hx1] at h01
  have hc : cos φ₀ * T x 0 + sin φ₀ * T x 1 = 0 := by
    have : R θ φ₀ * (cos φ₀ * T x 0 + sin φ₀ * T x 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.1 this).resolve_left hRpos.ne'
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
  simp [h2]
  linear_combination deriv (fun t => R t φ₀) θ * hc

/-- **Witness lemma (C1 current clause).** If near the poloidal loop the field is
`B = T + ∇Φ` with `T` purely toroidal and `Φ` a single-valued `C¹` potential (`g = ∇Φ` along the
loop), the loop is closed (`R`, `z` take the same values at `θ = ±π`) and `C¹` with `R > 0`, and
`B` is continuous along it, then the circulation `∮ B · dl` vanishes. -/
theorem poloidalCirculation_eq_zero_of_potential {T g : Space → Space} {Φ : Space → ℝ}
    (hR : ContDiff ℝ 1 fun t => R t φ₀) (hz : ContDiff ℝ 1 fun t => z t φ₀)
    (hRpos : ∀ θ, 0 < R θ φ₀) (hRper : R π φ₀ = R (-π) φ₀) (hzper : z π φ₀ = z (-π) φ₀)
    (hB : ∀ θ, ContinuousAt B (poloidalLoop R z φ₀ θ))
    (hsplit : ∀ θ, B (poloidalLoop R z φ₀ θ) =
      T (poloidalLoop R z φ₀ θ) + g (poloidalLoop R z φ₀ θ))
    (hT : PurelyToroidal T)
    (hΦ : ∀ θ, HasFDerivAt Φ (innerSL ℝ (g (poloidalLoop R z φ₀ θ))) (poloidalLoop R z φ₀ θ)) :
    poloidalCirculation B R z φ₀ = 0 := by
  refine lineIntegral_eq_zero_of_potential (contDiff_poloidalLoop hR hz) hB (fun θ => ?_) hΦ ?_
  · rw [hsplit θ, inner_add_left,
      inner_toroidal_poloidalLoop hT (hRpos θ) ((hR.differentiable one_ne_zero) θ)
        ((hz.differentiable one_ne_zero) θ), zero_add]
  · simp [poloidalLoop, hRper, hzper]

/-- An invariant torus is closed in `θ`: `R`, `z` agree at `θ = ±π`. -/
theorem FieldTorus.closed {ι : ℝ} (h : FieldTorus B R z ι) (φ : ℝ) :
    R π φ = R (-π) φ ∧ z π φ = z (-π) φ := by
  have e : -π + 2 * π = π := by ring
  exact ⟨by rw [← h.per_θ_R (-π), e], by rw [← h.per_θ_z (-π), e]⟩

end Loop

/-- **Degenerate case**: the zero field has zero circulation around every loop. -/
theorem poloidalCirculation_zero_field (R z : ℝ → ℝ → ℝ) (φ₀ : ℝ) :
    poloidalCirculation (fun _ => 0) R z φ₀ = 0 := by
  simp [poloidalCirculation, lineIntegral]

/-! ## Clause C1 -/

/-- The data of one confining surface for clause C1: the torus `(R, z)` with its transform
`iota`, and the toroidal angle `φ₀` of the poloidal loop around which the net current is
measured. -/
structure SurfaceData where
  /-- Cylindrical radius of the torus. -/
  R : ℝ → ℝ → ℝ
  /-- Height of the torus. -/
  z : ℝ → ℝ → ℝ
  /-- Rotational transform on the torus. -/
  iota : ℝ
  /-- Toroidal angle of the poloidal loop. -/
  φ₀ : ℝ

/-- The poloidal loop of the surface. -/
@[expose] def SurfaceData.loop (s : SurfaceData) : ℝ → Space := poloidalLoop s.R s.z s.φ₀

/-- The net toroidal current enclosed by the poloidal loop of the surface,
`μ₀⁻¹ ∮ B · dl`. -/
@[expose] def SurfaceData.current (μ₀ : ℝ) (B : Space → Space) (s : SurfaceData) : ℝ :=
  loopCurrent μ₀ B s.R s.z s.φ₀

/-- **Contract clause C1 (current-free rotational transform)** for the field `B` (with
`μ₀ > 0`): a nonempty family `S` of confining surfaces, each an invariant torus with rotational
transform `|ι| ≥ ι_min > 0` (`IotaOnTorus`; either handedness), whose poloidal loop at `φ₀` is
`C¹` and carries `B` continuously, and around which the Ampère current
`I = μ₀⁻¹ ∮ B · dl` satisfies `|I| ≤ I_max`. -/
structure CurrentFreeTransform (μ₀ : ℝ) (B : Space → Space) (S : Set SurfaceData)
    (Imax ιmin : ℝ) : Prop where
  /-- The vacuum permeability is positive. -/
  mu0_pos : 0 < μ₀
  /-- There is at least one confining surface. -/
  nonempty : S.Nonempty
  /-- The transform bound is positive. -/
  iotaMin_pos : 0 < ιmin
  /-- Each surface is an invariant torus with its transform. -/
  torus : ∀ s ∈ S, IotaOnTorus B s.R s.z s.iota
  /-- The radial profile of each poloidal loop is `C¹`. -/
  loop_R : ∀ s ∈ S, ContDiff ℝ 1 fun θ => s.R θ s.φ₀
  /-- The vertical profile of each poloidal loop is `C¹`. -/
  loop_z : ∀ s ∈ S, ContDiff ℝ 1 fun θ => s.z θ s.φ₀
  /-- The field is continuous along each poloidal loop. -/
  field_continuous : ∀ s ∈ S, ∀ θ, ContinuousAt B (s.loop θ)
  /-- Net-current bound (Ampère's law around the poloidal loop). -/
  current_le : ∀ s ∈ S, |s.current μ₀ B| ≤ Imax
  /-- Transform bound (either handedness). -/
  iota_ge : ∀ s ∈ S, ιmin ≤ |s.iota|

section C1
variable {μ₀ : ℝ} {B : Space → Space} {S : Set SurfaceData} {Imax ιmin : ℝ}

/-- **Toroidal field plus gradient satisfies the current clause with `I_max = 0`**: if along every
poloidal loop of `S` the field is `B = T + ∇Φ` with `T` purely toroidal and `Φ` a single-valued
`C¹` potential, C1 reduces to the transform clause and the regularity of the loops. -/
theorem currentFreeTransform_of_potential {T g : Space → Space} {Φ : Space → ℝ} (hμ : 0 < μ₀)
    (hS : S.Nonempty) (hι : 0 < ιmin) (hTor : ∀ s ∈ S, IotaOnTorus B s.R s.z s.iota)
    (hR : ∀ s ∈ S, ContDiff ℝ 1 fun θ => s.R θ s.φ₀)
    (hz : ∀ s ∈ S, ContDiff ℝ 1 fun θ => s.z θ s.φ₀)
    (hB : ∀ s ∈ S, ∀ θ, ContinuousAt B (s.loop θ))
    (hsplit : ∀ s ∈ S, ∀ θ, B (s.loop θ) = T (s.loop θ) + g (s.loop θ))
    (hT : PurelyToroidal T) (hΦ : ∀ s ∈ S, ∀ θ, HasFDerivAt Φ (innerSL ℝ (g (s.loop θ))) (s.loop θ))
    (hge : ∀ s ∈ S, ιmin ≤ |s.iota|) : CurrentFreeTransform μ₀ B S 0 ιmin where
  mu0_pos := hμ
  nonempty := hS
  iotaMin_pos := hι
  torus := hTor
  loop_R := hR
  loop_z := hz
  field_continuous := hB
  current_le s hs := by
    have hcl := (hTor s hs).1.closed s.φ₀
    rw [SurfaceData.current, loopCurrent,
      poloidalCirculation_eq_zero_of_potential (hR s hs) (hz s hs)
        (fun θ => (hTor s hs).1.R_pos θ s.φ₀) hcl.1 hcl.2 (hB s hs) (hsplit s hs) hT (hΦ s hs),
      zero_div, abs_zero]
  iota_ge := hge

/-- **Tokamak exclusion at contract level**: a purely toroidal field (e.g. the vacuum
axisymmetric field) fails C1 for every `I_max` and every `ι_min`. -/
theorem not_currentFreeTransform_of_purelyToroidal (hB : PurelyToroidal B) :
    ¬ CurrentFreeTransform μ₀ B S Imax ιmin := by
  intro h
  obtain ⟨s, hs⟩ := h.nonempty
  have h0 := iota_eq_zero_of_purelyToroidal hB (h.torus s hs)
  have := h.iota_ge s hs
  rw [h0, abs_zero] at this
  linarith [h.iotaMin_pos]

/-- A surface whose poloidal loop encloses net current above `I_max` violates C1. -/
theorem not_currentFreeTransform_of_current {s : SurfaceData} (hs : s ∈ S)
    (hI : Imax < |s.current μ₀ B|) : ¬ CurrentFreeTransform μ₀ B S Imax ιmin :=
  fun h => absurd (h.current_le s hs) (not_le.2 hI)

/-- C1 is monotone: a larger current allowance and a smaller transform bound (still positive)
are weaker. -/
theorem CurrentFreeTransform.mono {Imax' ιmin' : ℝ} (h : CurrentFreeTransform μ₀ B S Imax ιmin)
    (hI : Imax ≤ Imax') (hι : ιmin' ≤ ιmin) (hι' : 0 < ιmin') :
    CurrentFreeTransform μ₀ B S Imax' ιmin' where
  mu0_pos := h.mu0_pos
  nonempty := h.nonempty
  iotaMin_pos := hι'
  torus := h.torus
  loop_R := h.loop_R
  loop_z := h.loop_z
  field_continuous := h.field_continuous
  current_le s hs := (h.current_le s hs).trans hI
  iota_ge s hs := hι.trans (h.iota_ge s hs)

end C1

/-! ## Clause C2 (Boozer guiding-centre model) -/

open PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer

/-- An **axisymmetric** Boozer field: `∂_φ B = 0` on the chart `ψ > 0`. -/
@[expose] def BoozerAxisymmetric (F : BoozerField) : Prop :=
  ∀ x θ φ, 0 < x → F.Bφ x θ φ = 0

/-- **Contract clause C2** on the region `0 < ψ ≤ c` in the vacuum Boozer guiding-centre model:
for every species, magnetic moment and energy, the radial displacement per trapped bounce is at
most `κ_max (H/|q|) τ` (`ApproxOmnigenousOn`); `κ_max = 0` is exact omnigeneity. -/
structure OmnigeneityContract (F : BoozerField) (c κmax : ℝ) : Prop where
  /-- The region is nonempty. -/
  region_pos : 0 < c
  /-- The drift constant is nonnegative. -/
  kappa_nonneg : 0 ≤ κmax
  /-- The bounded-drift clause. -/
  drift : ApproxOmnigenousOn F c κmax

section C2
variable {F : BoozerField}

/-- With `κ_max = 0`, C2 is exact omnigeneity (`OmnigenousOn`) on a nonempty region. -/
theorem omnigeneityContract_zero_iff {c : ℝ} :
    OmnigeneityContract F c 0 ↔ 0 < c ∧ OmnigenousOn F c := by
  rw [omnigenousOn_iff_approx_zero]
  exact ⟨fun h => ⟨h.region_pos, h.drift⟩, fun h => ⟨h.1, le_rfl, h.2⟩⟩

/-- **Axisymmetric ⇒ omnigenous** (Boozer model): an axisymmetric field with `ι ≥ ι_min > 0` on
`(0, c]` is omnigenous there (exact quasisymmetry with helicity `(0, 1)`; the twist comes from
`ι ≥ ι_min`). -/
theorem omnigenousOn_of_axisymmetric (hG : F.G ≠ 0) (hax : BoozerAxisymmetric F) {c ιmin : ℝ}
    (hι0 : 0 < ιmin) (hι : ∀ x ∈ Ioc 0 c, ιmin ≤ F.ι x) : OmnigenousOn F c :=
  omnigenousOn_of_exactQS (N := 0) (M := 1) hG
    (fun x θ φ hx _ => by simp [symmetryDefect, hax x θ φ hx])
    ((twistOn_qa_of_iota_ge hι).injOn hι0)

/-- **Axisymmetric with `ι = 0` ⇒ omnigenous, vacuously** (Boozer model): `ρ̇ ∝ ∂_φB + ι ∂_θB`
vanishes on the region, so `ρ` is constant along every orbit there and no trapped bounce exists.
With the tokamak exclusion this is the consistency check of the contract: an axisymmetric
current-free field passes C2 and fails C1. -/
theorem omnigenousOn_of_axisymmetric_iota_zero (hax : BoozerAxisymmetric F) {c : ℝ}
    (hι : ∀ x ∈ Ioc 0 c, F.ι x = 0) : OmnigenousOn F c := by
  intro m q μ ψ θ φ ρ τ _ _ _ hb
  exfalso
  obtain ⟨horb, ⟨hτ, hρ0, -, σ, hσ, -, hopp⟩, hreg⟩ := hb
  have hconst : ∀ t ∈ Icc 0 τ, ρ t = ρ 0 := by
    refine constant_of_has_deriv_right_zero (fun t ht => ?_) (fun t ht => ?_)
    · exact (horb.dρ t ht).continuousAt.continuousWithinAt
    · have ht' : t ∈ Icc 0 τ := Ico_subset_Icc_self ht
      have h := (horb.dρ t ht').hasDerivWithinAt (s := Ici t)
      have hpos := horb.pos t ht'
      rw [show along F.Bφ ψ θ φ t = 0 from hax _ _ _ hpos,
        hι (ψ t) ⟨hpos, hreg t ht'⟩] at h
      simpa using h
  have hs : σ / 2 ∈ Ioo 0 σ := ⟨by linarith [hσ.1], by linarith [hσ.1]⟩
  have ht : (σ + τ) / 2 ∈ Ioo σ τ := ⟨by linarith [hσ.2], by linarith [hσ.2]⟩
  have h := hopp _ hs _ ht
  rw [hconst _ ⟨hs.1.le, by linarith [hσ.2]⟩, hconst _ ⟨by linarith [hσ.1], ht.2.le⟩, hρ0,
    mul_zero] at h
  exact lt_irrefl _ h

/-- **Degenerate case**: a constant field strength satisfies C2 with `κ_max = 0`. -/
theorem constField_omnigeneityContract {B₀ ι₀ G c : ℝ} (hG : G ≠ 0) (hc : 0 < c) :
    OmnigeneityContract (constField B₀ ι₀ G) c 0 :=
  omnigeneityContract_zero_iff.2 ⟨hc, constField_omnigenousOn hG c⟩

/-- **Counterexample**: the drift-mirror field `B = 1 + φ² + k sin θ` (`0 < k ≤ 1/2`) fails C2
with `κ_max = 0` on every region `c ≥ 11`. -/
theorem driftMirror_not_omnigeneityContract {k c : ℝ} (hk0 : 0 < k) (hk : k ≤ 1 / 2)
    (hc : 11 ≤ c) : ¬ OmnigeneityContract (driftMirror k) c 0 :=
  fun h => driftMirror_not_omnigenous hk0 hk hc (omnigeneityContract_zero_iff.1 h).2

end C2

end PlasmaLean.Contract
