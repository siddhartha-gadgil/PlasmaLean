/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Kernel.Equilibrium
public import PlasmaLean.Theory.Fields.ClebschDivergence
public import PlasmaLean.Theory.Kinetic.CanonicalMomentum

/-!
# An exact Solov'ev toroidal equilibrium with finite pressure

With `R² = x₀² + x₁²`, `z = x₂` and a major-radius scale `L > 0`, the polynomial
`ψ̃ = R² z² / 2 + (R² - L²)² / 4` satisfies `Δ*ψ̃ = ψ̃_RR - ψ̃_R / R + ψ̃_zz = 3 R²`
(hand computation; the formal content is `force_balance` below), so it is a Solov'ev
solution of the Grad–Shafranov equation with constant `p'(ψ)` and
`F F' = 0`. With amplitude `A` (tesla) put `c = A / L²`, flux `Ψ = c ψ̃`, and
`∇φ = (-x₁, x₀, 0) / R²`. The magnetic field is
`B = ∇Ψ × ∇φ + F ∇φ = c (-x₀ z, -x₁ z, z² + R² - L²) + F (-x₁, x₀, 0) / R²`.

Off the vertical axis (`R ≠ 0`) we compute the actual Fréchet derivative of `B` and prove:

* `field_divergence_free`: `∇ · B = 0`;
* `field_curl`: `∇ × B = (3 c x₁, -3 c x₀, 0)`, so `μ₀ J` is a purely toroidal current;
* `force_balance`: the domain-kernel law `ForceBalance` holds, `J × B = ∇p`, with the
  actual gradient of `p = p₀ - (3 c² / μ₀) ψ̃`;
* `field_flux_tangent`, `current_flux_tangent`: `B · ∇ψ̃ = 0 = J · ∇ψ̃` (flux surfaces);
* `field_axisymmetric`: the canonical-momentum structure, hence `orbit_confined`:
  all-time full-orbit confinement in this exact finite-pressure equilibrium.

Realistic instance (`iter_like`): `L = 6 m`, `F = 30 T m` (5 T on axis), `A = 7/5 T`,
`p₀ = 3 A² / (16 μ₀)` so that `p ≥ 0` exactly on the region `ψ̃ ≤ L⁴/16`
(`4.24 m ≲ R ≲ 7.35 m`, `|z| ≤ 3 m`). Then `β_axis = 2 μ₀ p₀ / B_axis² = 147/5000 ≈ 2.9%`
exactly, independent of the value of `μ₀`. Deuterons up to 400 keV are confined for all
time by the canonical-momentum bound (`iter_like_deuteron_confined`); alpha particles up to
800 keV satisfy the same rigidity hypothesis (`alpha_rigidity`). 3.5 MeV alphas are NOT
covered by this crude bound.

Scope: this is an axisymmetric (tokamak) exact equilibrium, not a stellarator. It is a
genuine toroidal finite-pressure witness for the kernel law `ForceBalance`. The pressure
vanishes on the chosen boundary but the field does not match any coil set or vacuum
region, and no stability (MHD, kinetic) claim is made. Orbits are supplied, not
constructed; the model is non-relativistic and collisionless.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.Solovev
open PlasmaLean.Fields PlasmaLean.Kinetic WithLp

/-- Squared major radius. -/
@[expose] def R2 (x : Space) : ℝ := x 0 ^ 2 + x 1 ^ 2

/-- Solov'ev polynomial flux shape (units m⁴): `R² z²/2 + (R² - L²)²/4`. -/
@[expose] def psiT (L : ℝ) (x : Space) : ℝ := R2 x * x 2 ^ 2 / 2 + (R2 x - L ^ 2) ^ 2 / 4

/-- Explicit gradient of `psiT`. -/
@[expose] def psiTGrad (L : ℝ) (x : Space) : Space :=
  toLp 2 ![x 0 * (x 2 ^ 2 + R2 x - L ^ 2), x 1 * (x 2 ^ 2 + R2 x - L ^ 2), R2 x * x 2]

/-- Poloidal flux function `Ψ = (A / L²) ψ̃` (units T m²). -/
@[expose] def flux (A L : ℝ) (x : Space) : ℝ := A / L ^ 2 * psiT L x

/-- Gradient of the poloidal flux function. -/
@[expose] def fluxGrad (A L : ℝ) (x : Space) : Space := (A / L ^ 2) • psiTGrad L x

/-- Gradient of the toroidal angle, `(-x₁, x₀, 0) / R²` (zero on the vertical axis by
Lean's convention `0⁻¹ = 0`; only used off the axis). -/
@[expose] def phiGrad (x : Space) : Space := (R2 x)⁻¹ • toLp 2 ![-x 1, x 0, 0]

/-- Polynomial form of the poloidal field `∇Ψ × ∇φ`. -/
@[expose] def poloidal (A L : ℝ) (x : Space) : Space :=
  toLp 2 ![-(A / L ^ 2 * (x 0 * x 2)), -(A / L ^ 2 * (x 1 * x 2)),
    A / L ^ 2 * (x 2 ^ 2 + R2 x - L ^ 2)]

/-- The Solov'ev magnetic field `B = ∇Ψ × ∇φ + F ∇φ`. -/
@[expose] def field (A L F : ℝ) (x : Space) : Space := poloidal A L x + F • phiGrad x

/-- Pressure `p = p₀ - (3 c² / μ₀) ψ̃` with `c = A / L²`. -/
@[expose] def pressure (μ₀ p₀ A L : ℝ) (x : Space) : ℝ :=
  p₀ - 3 * (A / L ^ 2) ^ 2 / μ₀ * psiT L x

/-- Explicit pressure gradient. -/
@[expose] def pressureGrad (μ₀ A L : ℝ) (x : Space) : Space :=
  (-(3 * (A / L ^ 2) ^ 2 / μ₀)) • psiTGrad L x

/-- The poloidal part is exactly the Clebsch-type field `∇Ψ × ∇φ` off the axis. -/
theorem poloidal_eq_cross (A L : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    cross (fluxGrad A L x) (phiGrad x) = poloidal A L x := by
  apply space_ext
  all_goals simp [cross, crossProduct, fluxGrad, psiTGrad, phiGrad, poloidal]
  all_goals field_simp
  all_goals unfold R2; ring

/-- Coordinate functions are continuous linear, with themselves as derivative. -/
theorem coord_hasFDerivAt (i : Fin 3) (x : Space) :
    HasFDerivAt (fun y : Space => y i) (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt

/-- `psiT` has the explicit gradient as its Fréchet derivative. -/
theorem psiT_hasFDerivAt (L : ℝ) (x : Space) :
    HasFDerivAt (psiT L) (innerSL ℝ (psiTGrad L x)) x := by
  have hR := ((coord_hasFDerivAt 0 x).pow 2).add ((coord_hasFDerivAt 1 x).pow 2)
  have h := ((hR.mul ((coord_hasFDerivAt 2 x).pow 2)).const_mul (1 / 2)).add
    (((hR.sub_const (L ^ 2)).pow 2).const_mul (1 / 4))
  convert h using 1
  · funext y; simp [psiT, R2]; ring
  · ext v
    simp [psiTGrad, R2, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
      dotProduct]
    ring

/-- The poloidal flux has gradient `fluxGrad`. -/
theorem flux_hasFDerivAt (A L : ℝ) (x : Space) :
    HasFDerivAt (flux A L) (innerSL ℝ (fluxGrad A L x)) x := by
  refine ((psiT_hasFDerivAt L x).const_mul (A / L ^ 2)).congr_fderiv ?_
  ext v
  simp [fluxGrad, psiTGrad, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
    dotProduct]

/-- The pressure has the explicit gradient as its Fréchet derivative. -/
theorem pressure_hasFDerivAt (μ₀ p₀ A L : ℝ) (x : Space) :
    HasFDerivAt (pressure μ₀ p₀ A L) (innerSL ℝ (pressureGrad μ₀ A L x)) x := by
  refine (((psiT_hasFDerivAt L x).const_mul (3 * (A / L ^ 2) ^ 2 / μ₀)).const_sub
    p₀).congr_fderiv ?_
  ext v
  simp [pressureGrad, psiTGrad, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three,
    dotProduct]

/-! ## Derivative of the field off the axis -/

/-- Explicit Jacobian `jac k i = ∂ᵢ Bₖ` off the axis, with `c = A / L²`. -/
@[expose] def jac (A L F : ℝ) (x : Space) : Fin 3 → Fin 3 → ℝ :=
  let c := A / L ^ 2
  ![![-(c * x 2) + 2 * F * x 0 * x 1 / R2 x ^ 2, -(F * (x 0 ^ 2 - x 1 ^ 2) / R2 x ^ 2),
      -(c * x 0)],
    ![F * (x 1 ^ 2 - x 0 ^ 2) / R2 x ^ 2, -(c * x 2) - 2 * F * x 0 * x 1 / R2 x ^ 2,
      -(c * x 1)],
    ![2 * c * x 0, 2 * c * x 1, 2 * c * x 2]]

/-- Row `k` of the Jacobian as a continuous linear functional. -/
@[expose] def row (A L F : ℝ) (x : Space) (k : Fin 3) : Space →L[ℝ] ℝ :=
  ∑ i, jac A L F x k i • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i

/-- The derivative operator assembled from the Jacobian rows. -/
@[expose] def fieldDeriv (A L F : ℝ) (x : Space) : Space →L[ℝ] Space :=
  ∑ k, (row A L F x k).smulRight (basis k)

/-- Entries of the assembled derivative are the Jacobian entries. -/
theorem fieldDeriv_apply (A L F : ℝ) (x : Space) (i k : Fin 3) :
    fieldDeriv A L F x (basis i) k = jac A L F x k i := by
  rw [fieldDeriv, coords_apply]
  fin_cases i <;> simp [row, Fin.sum_univ_three, basis]

/-- Coordinates of the field as explicit expressions. -/
theorem field_coords (A L F : ℝ) :
    (fun y => field A L F y 0) = (fun y => -(A / L ^ 2 * (y 0 * y 2)) - F * y 1 / R2 y) ∧
    (fun y => field A L F y 1) = (fun y => -(A / L ^ 2 * (y 1 * y 2)) + F * y 0 / R2 y) ∧
    (fun y => field A L F y 2) = (fun y => A / L ^ 2 * (y 2 ^ 2 + R2 y - L ^ 2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> funext y <;>
    simp [field, poloidal, phiGrad] <;> ring

/-- Off the vertical axis the Solov'ev field has the explicit Jacobian as its actual
Fréchet derivative. -/
theorem field_hasFDerivAt (A L F : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    HasFDerivAt (field A L F) (fieldDeriv A L F x) x := by
  have h0 := coord_hasFDerivAt 0 x
  have h1 := coord_hasFDerivAt 1 x
  have h2 := coord_hasFDerivAt 2 x
  have hR : HasFDerivAt R2 ((2 * x 0) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0 +
      (2 * x 1) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1) x := by
    have := (h0.pow 2).add (h1.pow 2)
    convert this using 1
    · funext y; simp [R2]
    · ext v; simp
  have hinv : HasFDerivAt (fun y => (R2 y)⁻¹) (-(R2 x ^ 2)⁻¹ •
      ((2 * x 0) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0 +
      (2 * x 1) • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1)) x := by
    refine ((hasDerivAt_inv hx).hasFDerivAt.comp x hR).congr_fderiv ?_
    ext v
    simp
    ring
  obtain ⟨e0, e1, e2⟩ := field_coords A L F
  have k0 : HasFDerivAt (fun y => field A L F y 0) (row A L F x 0) x := by
    rw [e0]
    have := ((h0.mul h2).const_mul (A / L ^ 2)).neg.sub ((h1.mul hinv).const_mul F)
    convert this using 1
    · funext y; simp [div_eq_mul_inv]; ring
    · ext v
      simp [row, jac, Fin.sum_univ_three]
      field_simp
      unfold R2
      ring
  have k1 : HasFDerivAt (fun y => field A L F y 1) (row A L F x 1) x := by
    rw [e1]
    have := ((h1.mul h2).const_mul (A / L ^ 2)).neg.add ((h0.mul hinv).const_mul F)
    convert this using 1
    · funext y; simp [div_eq_mul_inv]; ring
    · ext v
      simp [row, jac, Fin.sum_univ_three]
      field_simp
      unfold R2
      ring
  have k2 : HasFDerivAt (fun y => field A L F y 2) (row A L F x 2) x := by
    rw [e2]
    have := (((h2.pow 2).add hR).sub_const (L ^ 2)).const_mul (A / L ^ 2)
    convert this using 1
    ext v
    simp [row, jac, Fin.sum_univ_three]
    ring
  apply hasFDerivAt_of_coords
  intro k
  fin_cases k
  · exact k0
  · exact k1
  · exact k2

/-- `∇ · B = 0` off the vertical axis. -/
theorem field_divergence_free (A L F : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    divergence (fderiv ℝ (field A L F) x) = 0 := by
  rw [(field_hasFDerivAt A L F hx).fderiv, divergence_apply, fieldDeriv_apply,
    fieldDeriv_apply, fieldDeriv_apply]
  simp [jac]
  ring

/-- `∇ × B = (3 c x₁, -3 c x₀, 0)` off the vertical axis: a purely toroidal current,
independent of the toroidal field constant `F`. -/
theorem field_curl (A L F : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    curl (fderiv ℝ (field A L F) x) =
      toLp 2 ![3 * (A / L ^ 2) * x 1, -(3 * (A / L ^ 2) * x 0), 0] := by
  rw [(field_hasFDerivAt A L F hx).fderiv]
  obtain ⟨c0, c1, c2⟩ := curl_coords (fieldDeriv A L F x)
  apply space_ext
  · rw [c0, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring
  · rw [c1, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring
  · rw [c2, fieldDeriv_apply, fieldDeriv_apply]; simp [jac]; ring

/-- Current density from Ampère's law, `J = (∇ × B) / μ₀`. -/
@[expose] def current (μ₀ A L F : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (field A L F) x)

/-- Force balance `J × B = ∇p` (the domain-kernel law) at every point off the vertical
axis, with `J` the actual Ampère current and `∇p` the actual pressure gradient. -/
theorem force_balance (μ₀ A L F : ℝ) (hμ : μ₀ ≠ 0) {x : Space} (hx : R2 x ≠ 0) :
    ForceBalance (ofLp (field A L F x)) (ofLp (current μ₀ A L F x))
      (ofLp (pressureGrad μ₀ A L x)) := by
  refine ⟨?_⟩
  rw [current, field_curl A L F hx]
  ext i
  fin_cases i
  all_goals simp [cross_apply, field, poloidal, phiGrad, pressureGrad, psiTGrad]
  all_goals field_simp
  all_goals unfold R2; ring

/-- Consequence via the kernel: the pressure gradient is tangent to the field. -/
theorem field_pressure_tangent (μ₀ A L F : ℝ) (hμ : μ₀ ≠ 0) {x : Space}
    (hx : R2 x ≠ 0) :
    ofLp (field A L F x) ⬝ᵥ ofLp (pressureGrad μ₀ A L x) = 0 := by
  have := force_balance μ₀ A L F hμ hx
  exact field_tangency _ (ofLp (current μ₀ A L F x)) _

/-- Flux surfaces: `B · ∇ψ̃ = 0` everywhere (including the axis convention). -/
theorem field_flux_tangent (A L F : ℝ) (x : Space) :
    ⟪psiTGrad L x, field A L F x⟫ = 0 := by
  simp [psiTGrad, field, poloidal, phiGrad, R2, EuclideanSpace.inner_eq_star_dotProduct,
    Fin.sum_univ_three, dotProduct]
  ring

/-- The current lies in flux surfaces: `J · ∇ψ̃ = 0` off the axis. -/
theorem current_flux_tangent (μ₀ A L F : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    ⟪psiTGrad L x, current μ₀ A L F x⟫ = 0 := by
  rw [current, field_curl A L F hx]
  simp [psiTGrad, EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
  ring

/-- `ψ̃` is an exact global first integral of the field lines. -/
theorem psiT_firstIntegral (A L F : ℝ) : FirstIntegralOn (field A L F) (psiT L) Set.univ := by
  intro x _
  refine ⟨(psiT_hasFDerivAt L x).differentiableAt, ?_⟩
  rw [(psiT_hasFDerivAt L x).fderiv]
  simpa using field_flux_tangent A L F x

/-- Sanity: with zero amplitude the pressure is constant and the current vanishes. -/
theorem current_zero_amplitude (μ₀ L F : ℝ) {x : Space} (hx : R2 x ≠ 0) :
    current μ₀ 0 L F x = 0 := by
  rw [current, field_curl 0 L F hx]
  ext i; fin_cases i <;> simp

/-! ## Canonical momentum and all-time orbit confinement -/

/-- The Solov'ev field has the axisymmetric canonical-momentum structure with flux
gradient `fluxGrad` (the toroidal part exerts no vertical torque). -/
theorem field_axisymmetric (A L F : ℝ) : AxisymmetricFlux (field A L F) (fluxGrad A L) := by
  intro x v
  simp [angularZ, field, poloidal, phiGrad, fluxGrad, psiTGrad, cross, crossProduct, R2,
    EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_three, dotProduct]
  ring

/-- Points with `ψ̃ ≤ L⁴/16` satisfy `L²/2 ≤ R² ≤ 3L²/2` and `z² ≤ L²/4`. -/
theorem region_bounds {L : ℝ} (hL : 0 < L) (x : Space) (hx : psiT L x ≤ L ^ 4 / 16) :
    L ^ 2 / 2 ≤ R2 x ∧ R2 x ≤ 3 * L ^ 2 / 2 ∧ x 2 ^ 2 ≤ L ^ 2 / 4 := by
  unfold psiT at hx
  have hR : 0 ≤ R2 x := by unfold R2; positivity
  have hz := sq_nonneg (x 2)
  have hL2 : 0 < L ^ 2 := by positivity
  have hsq : (R2 x - L ^ 2) ^ 2 ≤ (L ^ 2 / 2) ^ 2 := by nlinarith [mul_nonneg hR hz]
  have habs := abs_le_of_sq_le_sq' hsq (by positivity)
  have hlo : L ^ 2 / 2 ≤ R2 x := by linarith [habs.1]
  have hhi : R2 x ≤ 3 * L ^ 2 / 2 := by linarith [habs.2]
  refine ⟨hlo, hhi, ?_⟩
  have : R2 x * x 2 ^ 2 ≤ L ^ 4 / 8 := by nlinarith [sq_nonneg (R2 x - L ^ 2)]
  have h4 : L ^ 2 / 2 * x 2 ^ 2 ≤ L ^ 4 / 8 := le_trans (by nlinarith) this
  nlinarith

/-- Points with `ψ̃ ≤ L⁴/16` have norm at most `4L/3`. -/
theorem region_norm {L : ℝ} (hL : 0 < L) (x : Space) (hx : psiT L x ≤ L ^ 4 / 16) :
    ‖x‖ ≤ 4 * L / 3 := by
  obtain ⟨-, hhi, hz⟩ := region_bounds hL x hx
  have hn := EuclideanSpace.norm_sq_eq x
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
  have : ‖x‖ ^ 2 ≤ (4 * L / 3) ^ 2 := by rw [hn]; unfold R2 at hhi; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this

/-- The pressure with `p₀ = 3 A² / (16 μ₀)` is nonnegative on the region and equals
`p₀` on the magnetic axis. -/
theorem pressure_nonneg {μ₀ A L : ℝ} (hμ : 0 < μ₀) (hL : 0 < L) {x : Space}
    (hx : psiT L x ≤ L ^ 4 / 16) : 0 ≤ pressure μ₀ (3 * A ^ 2 / (16 * μ₀)) A L x := by
  unfold pressure
  have hL4 : (A / L ^ 2) ^ 2 * L ^ 4 = A ^ 2 := by field_simp
  have : 3 * (A / L ^ 2) ^ 2 / μ₀ * psiT L x ≤ 3 * (A / L ^ 2) ^ 2 / μ₀ * (L ^ 4 / 16) :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  have e : 3 * (A / L ^ 2) ^ 2 / μ₀ * (L ^ 4 / 16) = 3 * A ^ 2 / (16 * μ₀) := by
    rw [← hL4]; field_simp
  linarith

/-- Magnetic axis `(L, 0, 0)`: `ψ̃ = 0`, poloidal field zero, `|B| = F / L`. -/
theorem axis_values (A L F : ℝ) (hL : 0 < L) :
    psiT L (toLp 2 ![L, 0, 0]) = 0 ∧
    field A L F (toLp 2 ![L, 0, 0]) = toLp 2 ![0, F / L, 0] := by
  constructor
  · simp [psiT, R2]
  · apply space_ext
    all_goals simp [field, poloidal, phiGrad, R2]
    all_goals field_simp

/-- All-time full-orbit confinement in the exact Solov'ev equilibrium: with rigidity
`|m| ‖v‖ / |q| ≤ A L / 64`, initial `ψ̃ ≤ L⁴/64` and `‖x 0‖ ≤ 4L/3`, the orbit satisfies
`ψ̃ ≤ 11 L⁴/192` and `R² ≥ L²/2` for every real time. -/
theorem orbit_confined {A L F m q : ℝ} (hA : 0 < A) (hL : 0 < L) (hm : m ≠ 0) (hq : q ≠ 0)
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) (field A L F) x v)
    (hrig : |m| * ‖v 0‖ ≤ |q| * (A * L / 64)) (hψ0 : psiT L (x 0) ≤ L ^ 4 / 64)
    (hx0 : ‖x 0‖ ≤ 4 * L / 3) (t : ℝ) :
    psiT L (x t) ≤ 11 * L ^ 4 / 192 ∧ L ^ 2 / 2 ≤ R2 (x t) := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hc : 0 < A / L ^ 2 := by positivity
  have hk : |m| * ‖v 0‖ / |q| ≤ A * L / 64 := by
    rw [div_le_iff₀ hqpos]; linarith
  have hgap : flux A L (x 0) + |m| * ‖v 0‖ / |q| * (4 * L / 3 + ‖x 0‖) ≤
      A / L ^ 2 * (11 * L ^ 4 / 192) := by
    have h1 : |m| * ‖v 0‖ / |q| * (4 * L / 3 + ‖x 0‖) ≤ A * L / 64 * (8 * L / 3) :=
      mul_le_mul hk (by linarith) (by positivity) (by positivity)
    have h2 : flux A L (x 0) ≤ A / L ^ 2 * (L ^ 4 / 64) :=
      mul_le_mul_of_nonneg_left hψ0 hc.le
    have e1 : A / L ^ 2 * (L ^ 4 / 64) = A * L ^ 2 / 64 := by field_simp
    have e2 : A / L ^ 2 * (11 * L ^ 4 / 192) = 11 * (A * L ^ 2) / 192 := by field_simp
    rw [e2]; rw [e1] at h2; nlinarith
  have hreg : ∀ y, flux A L y ≤ A / L ^ 2 * (L ^ 4 / 16) → ‖y‖ ≤ 4 * L / 3 := fun y hy =>
    region_norm hL y (le_of_mul_le_mul_left hy hc)
  have hlt : A / L ^ 2 * (11 * L ^ 4 / 192) < A / L ^ 2 * (L ^ 4 / 16) :=
    mul_lt_mul_of_pos_left (by nlinarith [pow_pos hL 4]) hc
  have hp := orbit_trapped hm hq h (flux_hasFDerivAt A L) (field_axisymmetric A L F) hlt
    (by positivity) hreg hgap t
  have hψ : psiT L (x t) ≤ 11 * L ^ 4 / 192 := le_of_mul_le_mul_left hp hc
  exact ⟨hψ, (region_bounds hL _ (hψ.trans (by nlinarith [pow_pos hL 4]))).1⟩

/-! ## A realistic reactor-scale instance

`L = 6 m`, `F = 30 T m`, `A = 7/5 T`, `p₀ = 3 A² / (16 μ₀)`. -/

/-- On-axis toroidal field is exactly 5 T. -/
theorem iter_like_axis_field :
    field (7 / 5) 6 30 (toLp 2 ![6, 0, 0]) = toLp 2 ![0, 5, 0] := by
  rw [(axis_values (7 / 5) 6 30 (by norm_num)).2]; norm_num

/-- On-axis beta `2 μ₀ p₀ / B_axis²` equals `147/5000 ≈ 2.94%`, for every `μ₀ > 0`. -/
theorem iter_like_beta (μ₀ : ℝ) (hμ : 0 < μ₀) :
    2 * μ₀ * (3 * (7 / 5 : ℝ) ^ 2 / (16 * μ₀)) / 5 ^ 2 = 147 / 5000 := by
  field_simp; norm_num

/-- With `μ₀ ∈ [1.2566e-6, 1.2567e-6]` (bracketing 4π × 10⁻⁷), the axis pressure lies
between 292,000 and 292,600 Pa. -/
theorem iter_like_pressure (μ₀ : ℝ) (h1 : 1.2566e-6 ≤ μ₀) (h2 : μ₀ ≤ 1.2567e-6) :
    292000 ≤ 3 * (7 / 5 : ℝ) ^ 2 / (16 * μ₀) ∧ 3 * (7 / 5 : ℝ) ^ 2 / (16 * μ₀) ≤ 292600 := by
  have hμ : 0 < μ₀ := lt_of_lt_of_le (by norm_num) h1
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- Deuterons of kinetic energy at most 400 keV satisfy the rigidity condition
`m ‖v‖ ≤ q A L / 64` (with `m = 3.3436e-27 kg`, `q = 1.6022e-19 C`, `m‖v‖² ≤ 2K`). -/
theorem deuteron_rigidity (s : ℝ)
    (hK : 3.3436e-27 * s ^ 2 ≤ 2 * (400e3 * 1.6022e-19)) :
    |(3.3436e-27 : ℝ)| * s ≤ |(1.6022e-19 : ℝ)| * (7 / 5 * 6 / 64) := by
  rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
  nlinarith [sq_nonneg (3.3436e-27 * s - 1.6022e-19 * (7 / 5 * 6 / 64))]

/-- Alpha particles of kinetic energy at most 800 keV satisfy the rigidity condition
(`m = 6.6447e-27 kg`, `q = 2 × 1.6022e-19 C`). -/
theorem alpha_rigidity (s : ℝ)
    (hK : 6.6447e-27 * s ^ 2 ≤ 2 * (800e3 * 1.6022e-19)) :
    |(6.6447e-27 : ℝ)| * s ≤ |(2 * 1.6022e-19 : ℝ)| * (7 / 5 * 6 / 64) := by
  rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
  nlinarith [sq_nonneg (6.6447e-27 * s - 2 * 1.6022e-19 * (7 / 5 * 6 / 64))]

/-- All-time confinement of every deuteron up to 400 keV that starts with `ψ̃ ≤ 6⁴/64`
(i.e. `ψ̃ ≤ 81/4 m⁴`) and `‖x‖ ≤ 8 m` in the reactor-scale Solov'ev equilibrium. -/
theorem iter_like_deuteron_confined {x v : ℝ → Space}
    (h : LorentzOrbit 3.3436e-27 1.6022e-19 (fun _ => 0) (field (7 / 5) 6 30) x v)
    (hK : 3.3436e-27 * ‖v 0‖ ^ 2 ≤ 2 * (400e3 * 1.6022e-19))
    (hψ0 : psiT 6 (x 0) ≤ 6 ^ 4 / 64) (hx0 : ‖x 0‖ ≤ 4 * 6 / 3) (t : ℝ) :
    psiT 6 (x t) ≤ 11 * 6 ^ 4 / 192 ∧ 6 ^ 2 / 2 ≤ R2 (x t) :=
  orbit_confined (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    (deuteron_rigidity _ hK) hψ0 hx0 t

end PlasmaLean.Design.Solovev
