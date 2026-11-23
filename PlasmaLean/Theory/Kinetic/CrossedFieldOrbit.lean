/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MagneticHamiltonConverse
public import PlasmaLean.Theory.Kinetic.LorentzExistence
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.ODE.ExistUnique

/-!
# The E × B drift orbit; existence and uniqueness of Hamiltonian integral curves

Part A is an explicit orbit in crossed uniform fields `E = E₀ e_x`, `B = B₀ e_z`.

* `driftVelocity E₀ B₀ = −(E₀ / B₀) e_y`; `driftVelocity_eq_cross`: it is `(E × B) / B₀²`.
* `crossedVelocity`, `crossedPosition`: a gyration with frequency `Ω = q B₀ / m`
  (`gyroFrequency`) about a guiding centre that drifts with `driftVelocity`, plus uniform motion
  along `e_z`. The parameters `a`, `b` are the components of the gyration velocity at time `0`,
  `w` is the parallel velocity and `X` the guiding centre at time `0`.
* `crossedField_orbit`: for `m, q, B₀ ≠ 0` this is a `LorentzOrbit`.
  `crossedField_orbit_exists`: every initial position and velocity is attained.
* `crossedVelocity_periodic`, `crossedPosition_period`: the velocity has period `2π / Ω` and
  over one period the position advances by `(2π / Ω) (v_d + w e_z)`; so the velocity averaged
  over a period is the drift velocity plus the parallel velocity.
  `crossedPosition_gyroradius`: the distance from the drifting guiding centre is constant.
* `crossedField_hamilton`, `crossedField_energy`: the canonical lift is an integral curve of the
  Hamiltonian vector field of `emHamiltonian` for every differentiable gauge `A` with
  `∇ × A = B₀ e_z` and every potential of `E₀ e_x`; the energy is constant.

Part B is about integral curves of the Hamiltonian vector field of `emHamiltonian m q A Φ`,
written in the closed form `emHamiltonField m q A E` of `hamiltonianVectorField_emHamiltonian`.

* `contDiff_emHamiltonField`: the field is `C¹` when `A` is `C²` and `E` is `C¹`.
* `emHamilton_exists_local` (Picard–Lindelöf), `emHamilton_eqOn_Ioo`, `emHamilton_unique`:
  local existence through every point, and uniqueness on an open interval and for all times.
* `LorentzOrbitOn m q E B x v s`: the Lorentz equations at the times of a set `s`
  (`lorentzOrbitOn_univ`: for `s = univ` it is `LorentzOrbit`). The all-time statements
  `lorentzOrbit_emHamilton` and `lorentzOrbit_of_emHamilton` of
  `Theory/Kinetic/MagneticHamiltonConverse` are the case `s = Set.univ` of
  `lorentzOrbitOn_emHamilton` and `lorentzOrbitOn_of_emHamilton` through `lorentzOrbitOn_univ`
  (they are proved separately there, by the same argument).
  `lorentzOrbitOn_iff_emHamilton`: the interval form of `lorentzOrbit_iff_emHamilton`.
  `lorentzOrbitOn_exists_local`, `lorentzOrbitOn_unique`, `lorentzOrbit_unique`: local existence
  and uniqueness of Lorentz orbits for `B = ∇ × A`, `E = −∇Φ`, `A` of class `C²`, `E` of class
  `C¹`, `m ≠ 0`.
* Uniqueness without potentials: `lorentzEMField m q E B` is the first-order field
  `(x, v) ↦ (v, (q/m) (E x + v × B x))` on `Space × Space`; it is `C¹` when `E` and `B` are
  (`contDiff_lorentzEMField`), and a Lorentz orbit is an integral curve of it for `m ≠ 0`
  (`LorentzOrbitOn.hasDerivAt_lorentzEMField`). Hence `lorentzOrbitOn_unique_of_contDiff`,
  `lorentzOrbit_unique_of_contDiff`: two Lorentz orbits in `C¹` fields `E`, `B` with the same
  position and velocity at one time coincide. No vector or scalar potential is assumed, so
  this applies to fields that have none (`E` need not be a gradient, and `B` need not even be
  divergence free). `lorentzOrbit_existsUnique_of_contDiff`: with `lorentzOrbit_exists`, for
  `E = 0` and every `C¹` magnetic field there is exactly one Lorentz orbit for all times from
  every initial position and velocity.
* `exists_global_of_linear_growth`: a `C¹` vector field with `‖f z‖ ≤ K ‖z‖ + C` has global
  integral curves (Grönwall bound and the continuation theorem of
  `Theory/Fields/ODEContinuation`).
  `emHamilton_exists_global`: for a continuous linear `A` and a `C¹` field `E = −∇Φ` with
  `‖E y‖ ≤ a + b ‖y‖`, integral curves exist for all times, with no hypothesis on `m`.
  `lorentzOrbit_existsUnique_linearGauge`: hence a unique Lorentz orbit for all times from
  every initial position and velocity. `lorentzOrbit_existsUnique_uniform`: the case of
  arbitrary uniform `E` and `B`, in the symmetric gauge `A = (B × y) / 2` (`symmetricGauge`).

Comparison with `Theory/Kinetic/LorentzExistence`: `lorentzOrbit_exists` there has no electric
field, allows every `C¹` magnetic field and does not state uniqueness; uniqueness for it is
`lorentzOrbit_existsUnique_of_contDiff` here. The global result
`lorentzOrbit_existsUnique_linearGauge` allows an electric field of linear growth, but the
magnetic field is uniform (the curl of a linear vector potential). Neither existence result
contains the other. Uniqueness alone holds for all `C¹` fields `E`, `B`
(`lorentzOrbit_unique_of_contDiff`), with no potentials. Mathematically this contains
`lorentzOrbit_unique`, since `∇ × A` is `C¹` for `A` of class `C²`; that implication is not
formalized here and the two theorems are proved independently (one through the Hamiltonian
field on `Space × Space*`, the other through the first-order field on `Space × Space`).

Limit of the statements: every theorem of Part B stated through the Hamiltonian assumes a
vector potential `A` differentiable (`C²` for existence and uniqueness) on ALL of space with
`B = ∇ × A` everywhere, and `E = −∇Φ` on all of space. This excludes the vacuum field `∇φ` of
a straight wire or a toroidal coil (no global potential regular on the axis) and any field
defined only on a toroidal region; versions on an open set containing the orbit are not
stated. The potential-free uniqueness theorems also assume fields `C¹` on all of space.

Not proved here: global existence for a general `C²` vector potential with an electric field
(it is in `Theory/Kinetic/LorentzGlobalExistence`, for a field of linear growth or a potential
energy bounded below); maximal intervals of existence; dependence of the orbit on its initial
data; time-dependent fields.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Fields.ODEGlobal PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti InnerProductSpace Set WithLp
open scoped RealInnerProductSpace

/-! ## Part A: the E × B drift orbit -/

/-- The gyrofrequency `Ω = q B₀ / m`. -/
noncomputable def gyroFrequency (m q B₀ : ℝ) : ℝ := q * B₀ / m

/-- The gyrofrequency is nonzero when mass, charge and field strength are. -/
theorem gyroFrequency_ne_zero {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) :
    gyroFrequency m q B₀ ≠ 0 :=
  div_ne_zero (mul_ne_zero hq hB) hm

/-- The E × B drift velocity for `E = E₀ e_x`, `B = B₀ e_z`: `−(E₀ / B₀) e_y`. -/
noncomputable def driftVelocity (E₀ B₀ : ℝ) : Space := -(E₀ / B₀) • coordVec 1

/-- The drift velocity is `(E × B) / |B|²`. -/
theorem driftVelocity_eq_cross (E₀ : ℝ) {B₀ : ℝ} (hB : B₀ ≠ 0) :
    driftVelocity E₀ B₀ =
      (1 / B₀ ^ 2) • cross (E₀ • coordVec 0 : Space) (B₀ • coordVec 2) := by
  ext i
  fin_cases i <;> simp [driftVelocity, cross, cross_apply]
  field_simp

/-- Velocity of the drift orbit: a gyration `(a cos Ωt + b sin Ωt, −a sin Ωt + b cos Ωt)` about
the drift velocity `−(E₀ / B₀) e_y`, and the parallel velocity `w`. -/
noncomputable def crossedVelocity (m q E₀ B₀ a b w : ℝ) (t : ℝ) : Space :=
  toLp 2 ![a * Real.cos (gyroFrequency m q B₀ * t) + b * Real.sin (gyroFrequency m q B₀ * t),
    -a * Real.sin (gyroFrequency m q B₀ * t) + b * Real.cos (gyroFrequency m q B₀ * t) -
      E₀ / B₀, w]

/-- Position of the drift orbit: a gyration about the guiding centre
`X − (E₀ / B₀) t e_y + w t e_z`. -/
noncomputable def crossedPosition (m q E₀ B₀ : ℝ) (X : Space) (a b w : ℝ) (t : ℝ) : Space :=
  X + toLp 2 ![(a * Real.sin (gyroFrequency m q B₀ * t) -
        b * Real.cos (gyroFrequency m q B₀ * t)) / gyroFrequency m q B₀,
    (a * Real.cos (gyroFrequency m q B₀ * t) +
        b * Real.sin (gyroFrequency m q B₀ * t)) / gyroFrequency m q B₀ - E₀ / B₀ * t,
    w * t]

/-- **The E × B drift orbit.** For `m, q, B₀ ≠ 0`, in the uniform fields `E = E₀ e_x` and
`B = B₀ e_z`, the gyration about a guiding centre drifting with `−(E₀ / B₀) e_y` solves
`x' = v`, `m v' = q (E + v × B)`. -/
theorem crossedField_orbit {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ)
    (X : Space) (a b w : ℝ) :
    LorentzOrbit m q (fun _ => E₀ • coordVec 0) (fun _ => B₀ • coordVec 2)
      (crossedPosition m q E₀ B₀ X a b w) (crossedVelocity m q E₀ B₀ a b w) := by
  have hΩ := gyroFrequency_ne_zero hm hq hB
  have hΩdef : gyroFrequency m q B₀ = q * B₀ / m := rfl
  set Ω := gyroFrequency m q B₀ with hΩset
  have hs (t : ℝ) : HasDerivAt (fun s => Real.sin (Ω * s)) (Real.cos (Ω * t) * Ω) t := by
    simpa using ((hasDerivAt_id' t).const_mul Ω).sin
  have hc (t : ℝ) : HasDerivAt (fun s => Real.cos (Ω * s)) (-Real.sin (Ω * t) * Ω) t := by
    simpa using ((hasDerivAt_id' t).const_mul Ω).cos
  constructor
  · intro t
    have h0 : HasDerivAt (fun s => (a * Real.sin (Ω * s) - b * Real.cos (Ω * s)) / Ω)
        (a * Real.cos (Ω * t) + b * Real.sin (Ω * t)) t := by
      have h := (((hs t).const_mul a).sub ((hc t).const_mul b)).div_const Ω
      refine h.congr_deriv ?_
      field_simp
      ring
    have h1 : HasDerivAt
        (fun s => (a * Real.cos (Ω * s) + b * Real.sin (Ω * s)) / Ω - E₀ / B₀ * s)
        (-a * Real.sin (Ω * t) + b * Real.cos (Ω * t) - E₀ / B₀) t := by
      have h := ((((hc t).const_mul a).add ((hs t).const_mul b)).div_const Ω).sub
        ((hasDerivAt_id' t).const_mul (E₀ / B₀))
      refine h.congr_deriv ?_
      field_simp
    have h2 : HasDerivAt (fun s => w * s) w t := by
      simpa using (hasDerivAt_id' t).const_mul w
    have hcoord : HasDerivAt (fun s => ![(a * Real.sin (Ω * s) - b * Real.cos (Ω * s)) / Ω,
        (a * Real.cos (Ω * s) + b * Real.sin (Ω * s)) / Ω - E₀ / B₀ * s, w * s])
        ![a * Real.cos (Ω * t) + b * Real.sin (Ω * t),
          -a * Real.sin (Ω * t) + b * Real.cos (Ω * t) - E₀ / B₀, w] t := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      exacts [h0, h1, h2]
    exact (hasDerivAt_toLp hcoord).const_add X
  · intro t
    refine ⟨toLp 2 ![Ω * (-a * Real.sin (Ω * t) + b * Real.cos (Ω * t)),
      -Ω * (a * Real.cos (Ω * t) + b * Real.sin (Ω * t)), 0], ?_, ?_⟩
    · have h0 : HasDerivAt (fun s => a * Real.cos (Ω * s) + b * Real.sin (Ω * s))
          (Ω * (-a * Real.sin (Ω * t) + b * Real.cos (Ω * t))) t := by
        refine (((hc t).const_mul a).add ((hs t).const_mul b)).congr_deriv ?_
        ring
      have h1 : HasDerivAt
          (fun s => -a * Real.sin (Ω * s) + b * Real.cos (Ω * s) - E₀ / B₀)
          (-Ω * (a * Real.cos (Ω * t) + b * Real.sin (Ω * t))) t := by
        refine ((((hs t).const_mul (-a)).add ((hc t).const_mul b)).sub_const
          (E₀ / B₀)).congr_deriv ?_
        ring
      apply hasDerivAt_toLp
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      exacts [h0, h1, hasDerivAt_const t w]
    · ext i
      fin_cases i <;>
        simp [crossedVelocity, cross, cross_apply, ← hΩset, hΩdef] <;>
        field_simp <;> ring

/-- The initial velocity of the drift orbit is `(a, b − E₀ / B₀, w)`. -/
theorem crossedVelocity_zero (m q E₀ B₀ a b w : ℝ) :
    crossedVelocity m q E₀ B₀ a b w 0 = toLp 2 ![a, b - E₀ / B₀, w] := by
  simp [crossedVelocity]

/-- The initial position of the drift orbit is `X + (−b / Ω, a / Ω, 0)`. -/
theorem crossedPosition_zero (m q E₀ B₀ : ℝ) (X : Space) (a b w : ℝ) :
    crossedPosition m q E₀ B₀ X a b w 0 =
      X + toLp 2 ![-b / gyroFrequency m q B₀, a / gyroFrequency m q B₀, 0] := by
  simp [crossedPosition]

/-- **Every initial condition is attained.** For `m, q, B₀ ≠ 0`, in the crossed uniform fields
`E₀ e_x`, `B₀ e_z` there is a Lorentz orbit, for all times, with any prescribed initial
position and velocity; it is one of the explicit drift orbits. -/
theorem crossedField_orbit_exists {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0)
    (E₀ : ℝ) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space,
      LorentzOrbit m q (fun _ => E₀ • coordVec 0) (fun _ => B₀ • coordVec 2) x v ∧
        x 0 = x₀ ∧ v 0 = v₀ := by
  have hΩ := gyroFrequency_ne_zero hm hq hB
  refine ⟨_, _, crossedField_orbit hm hq hB E₀
    (x₀ - toLp 2 ![-(v₀ 1 + E₀ / B₀) / gyroFrequency m q B₀, v₀ 0 / gyroFrequency m q B₀, 0])
    (v₀ 0) (v₀ 1 + E₀ / B₀) (v₀ 2), ?_, ?_⟩
  · rw [crossedPosition_zero, sub_add_cancel]
  · rw [crossedVelocity_zero]
    ext i
    fin_cases i <;> simp

/-- The velocity relative to the drift is a rotation of `(a, b)`: its perpendicular speed is
constant. -/
theorem crossedVelocity_gyration_speed (m q E₀ B₀ a b w t : ℝ) :
    (crossedVelocity m q E₀ B₀ a b w t 0 - driftVelocity E₀ B₀ 0) ^ 2 +
        (crossedVelocity m q E₀ B₀ a b w t 1 - driftVelocity E₀ B₀ 1) ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [crossedVelocity, driftVelocity]
  simp only [PiLp.smul_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, smul_eq_mul]
  simp
  nlinarith [Real.sin_sq_add_cos_sq (gyroFrequency m q B₀ * t)]

/-- **The velocity is periodic** with the gyro-period `2π / Ω`. -/
theorem crossedVelocity_periodic {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0)
    (E₀ a b w t : ℝ) :
    crossedVelocity m q E₀ B₀ a b w (t + 2 * Real.pi / gyroFrequency m q B₀) =
      crossedVelocity m q E₀ B₀ a b w t := by
  have hΩ := gyroFrequency_ne_zero hm hq hB
  have e : gyroFrequency m q B₀ * (t + 2 * Real.pi / gyroFrequency m q B₀) =
      gyroFrequency m q B₀ * t + 2 * Real.pi := by
    field_simp
  simp only [crossedVelocity, e, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- **Displacement over one gyro-period.** The position advances by
`(2π / Ω) (v_d + w e_z)`: the mean velocity over a period is the drift velocity plus the
parallel velocity. -/
theorem crossedPosition_period {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0)
    (E₀ : ℝ) (X : Space) (a b w t : ℝ) :
    crossedPosition m q E₀ B₀ X a b w (t + 2 * Real.pi / gyroFrequency m q B₀) =
      crossedPosition m q E₀ B₀ X a b w t +
        (2 * Real.pi / gyroFrequency m q B₀) • (driftVelocity E₀ B₀ + w • coordVec 2) := by
  have hΩ := gyroFrequency_ne_zero hm hq hB
  have e : gyroFrequency m q B₀ * (t + 2 * Real.pi / gyroFrequency m q B₀) =
      gyroFrequency m q B₀ * t + 2 * Real.pi := by
    field_simp
  simp only [crossedPosition, e, Real.cos_add_two_pi, Real.sin_add_two_pi, driftVelocity]
  ext i
  fin_cases i <;> simp <;> ring

/-- The distance of the drift orbit from its drifting guiding centre is the constant
`√(a² + b²) / |Ω|`. -/
theorem crossedPosition_gyroradius {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0)
    (E₀ : ℝ) (X : Space) (a b w t : ℝ) :
    (crossedPosition m q E₀ B₀ X a b w t 0 - X 0) ^ 2 +
        (crossedPosition m q E₀ B₀ X a b w t 1 - (X 1 - E₀ / B₀ * t)) ^ 2 =
      (a ^ 2 + b ^ 2) / gyroFrequency m q B₀ ^ 2 := by
  have hΩ := gyroFrequency_ne_zero hm hq hB
  simp only [crossedPosition, PiLp.add_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_left]
  have h := Real.sin_sq_add_cos_sq (gyroFrequency m q B₀ * t)
  have e : a ^ 2 + b ^ 2 =
      (a * Real.sin (gyroFrequency m q B₀ * t) - b * Real.cos (gyroFrequency m q B₀ * t)) ^ 2 +
        (a * Real.cos (gyroFrequency m q B₀ * t) +
          b * Real.sin (gyroFrequency m q B₀ * t)) ^ 2 := by
    linear_combination (-(a ^ 2 + b ^ 2)) * h
  rw [e]
  field_simp
  ring

/-- **Hamilton's equations along the drift orbit.** For every differentiable vector potential
`A` with `∇ × A = B₀ e_z` and every potential `Φ` of `E₀ e_x`, the canonical lift of the drift
orbit is an integral curve of the Hamiltonian vector field of `emHamiltonian m q A Φ`. -/
theorem crossedField_hamilton {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ)
    {A : Space → Space} {Φ : Space → ℝ} (hA : Differentiable ℝ A)
    (hcurl : ∀ y, fieldCurl A y = B₀ • coordVec 2)
    (hΦ : IsPotential Φ (fun _ => E₀ • coordVec 0)) (X : Space) (a b w t : ℝ) :
    HasDerivAt (canonicalCurve m q A (crossedPosition m q E₀ B₀ X a b w)
        (crossedVelocity m q E₀ B₀ a b w))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ)
        (canonicalCurve m q A (crossedPosition m q E₀ B₀ X a b w)
          (crossedVelocity m q E₀ B₀ a b w) t)) t :=
  lorentzOrbit_emHamilton hm (crossedField_orbit hm hq hB E₀ X a b w) hA
    (fun y => (hcurl y).symm) hΦ t

/-- **Energy along the drift orbit.** For every potential `Φ` of `E₀ e_x` the energy
`(m/2)‖v‖² + q Φ(x)` is constant. -/
theorem crossedField_energy {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ)
    {Φ : Space → ℝ} (hΦ : IsPotential Φ (fun _ => E₀ • coordVec 0)) (X : Space)
    (a b w s t : ℝ) :
    orbitEnergy m q Φ (crossedPosition m q E₀ B₀ X a b w) (crossedVelocity m q E₀ B₀ a b w) s =
      orbitEnergy m q Φ (crossedPosition m q E₀ B₀ X a b w)
        (crossedVelocity m q E₀ B₀ a b w) t :=
  energy_conserved (crossedField_orbit hm hq hB E₀ X a b w) hΦ s t

/-! ## Part B: existence and uniqueness of integral curves -/

/-- The Hamiltonian vector field of `emHamiltonian` in closed form: at `z = (x, p)` it is
`(v, q (DA)ᵀ v + q E(x)♭)` with `v = (p♯ − q A(x)) / m`. -/
noncomputable def emHamiltonField (m q : ℝ) (A E : Space → Space) (z : PhaseSpace) :
    PhaseSpace :=
  (kineticVelocity m q A z,
    q • (innerSL ℝ (kineticVelocity m q A z)).comp (fderiv ℝ A z.1) + q • innerSL ℝ (E z.1))

/-- For `A` differentiable and `E = −∇Φ`, the Hamiltonian vector field of
`emHamiltonian m q A Φ` is `emHamiltonField m q A E`. -/
theorem hamiltonianVectorField_emHamiltonian_eq (m q : ℝ) {A E : Space → Space}
    {Φ : Space → ℝ} (hA : Differentiable ℝ A) (hΦ : IsPotential Φ E) :
    (strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) = emHamiltonField m q A E :=
  funext fun z => hamiltonianVectorField_emHamiltonian m q hΦ (hA z.1)

/-- The velocity `(p♯ − q A(x)) / m` is a `C¹` function on phase space when `A` is `C¹`. -/
theorem contDiff_kineticVelocity (m q : ℝ) {A : Space → Space} (hA : ContDiff ℝ 1 A) :
    ContDiff ℝ 1 (kineticVelocity m q A) := by
  have h1 : ContDiff ℝ 1 (fun z : PhaseSpace => (toDual ℝ Space).symm z.2) := by
    have h := (toDualSymmL (F := Space)).contDiff (n := 1).comp
      (contDiff_snd (𝕜 := ℝ) (E := Space) (F := StrongDual ℝ Space))
    simpa only [Function.comp_def, toDualSymmL_apply] using h
  have h2 : ContDiff ℝ 1 (fun z : PhaseSpace => A z.1) := hA.comp contDiff_fst
  exact (h1.sub (h2.const_smul q)).const_smul m⁻¹

/-- **Regularity of the Hamiltonian vector field.** If `A` is `C²` and `E` is `C¹`, the closed
form `emHamiltonField m q A E` is `C¹` on phase space. No hypothesis on `m`. -/
theorem contDiff_emHamiltonField (m q : ℝ) {A E : Space → Space} (hA : ContDiff ℝ 2 A)
    (hE : ContDiff ℝ 1 E) : ContDiff ℝ 1 (emHamiltonField m q A E) := by
  have hkv := contDiff_kineticVelocity m q (hA.of_le (by norm_num))
  have hD : ContDiff ℝ 1 (fun z : PhaseSpace => fderiv ℝ A z.1) :=
    (hA.fderiv_right (m := 1) (by norm_num)).comp contDiff_fst
  have hin : ContDiff ℝ 1 (fun z : PhaseSpace => innerSL ℝ (kineticVelocity m q A z)) :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).contDiff.comp hkv
  have hEz : ContDiff ℝ 1 (fun z : PhaseSpace => innerSL ℝ (E z.1)) :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).contDiff.comp (hE.comp contDiff_fst)
  exact hkv.prodMk (((hin.clm_comp hD).const_smul q).add (hEz.const_smul q))

/-- **Uniqueness of integral curves on an open interval.** Two integral curves of a `C¹` vector
field on `(a, b)` that agree at one time of `(a, b)` agree on `(a, b)`. -/
theorem integralCurve_eqOn_Ioo {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → F} (hf : ContDiff ℝ 1 f) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) {γ₁ γ₂ : ℝ → F}
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt γ₁ (f (γ₁ t)) t)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt γ₂ (f (γ₂ t)) t) (h0 : γ₁ t₀ = γ₂ t₀) :
    EqOn γ₁ γ₂ (Ioo a b) := by
  intro t ht
  have hmin : a < min t t₀ := lt_min ht.1 ht₀.1
  have hmax : max t t₀ < b := max_lt ht.2 ht₀.2
  have hsub : Icc ((a + min t t₀) / 2) ((max t t₀ + b) / 2) ⊆ Ioo a b := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  set c := (a + min t t₀) / 2 with hc
  set d := (max t t₀ + b) / 2 with hd
  have hK : IsCompact (γ₁ '' Icc c d ∪ γ₂ '' Icc c d) :=
    (isCompact_Icc.image_of_continuousOn fun s hs =>
      (h₁ s (hsub hs)).continuousAt.continuousWithinAt).union
    (isCompact_Icc.image_of_continuousOn fun s hs =>
      (h₂ s (hsub hs)).continuousAt.continuousWithinAt)
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
    hf.locallyLipschitz.locallyLipschitzOn
  have hmem (r : ℝ) (hr : r ∈ Ioo c d) : r ∈ Icc c d := Ioo_subset_Icc_self hr
  exact ODE_solution_unique_of_mem_Ioo (v := fun _ => f)
    (s := fun _ => γ₁ '' Icc c d ∪ γ₂ '' Icc c d) (t₀ := t₀) (fun _ _ => hL)
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
    (fun r hr => ⟨h₁ r (hsub (hmem r hr)), Or.inl ⟨r, hmem r hr, rfl⟩⟩)
    (fun r hr => ⟨h₂ r (hsub (hmem r hr)), Or.inr ⟨r, hmem r hr, rfl⟩⟩) h0
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩

/-- **Local existence of integral curves** (Picard–Lindelöf). Let `A` be `C²` and `E = −∇Φ` be
`C¹`. Through every point `z₀` of phase space, at every initial time `t₀`, there is an integral
curve of the Hamiltonian vector field of `emHamiltonian m q A Φ` on an open interval about
`t₀`. No hypothesis on `m`: for `m = 0` Lean's division makes the kinetic term `0`, so the
statement is then about `H = qΦ`. -/
theorem emHamilton_exists_local (m q : ℝ) {A E : Space → Space} {Φ : Space → ℝ}
    (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) (z₀ : PhaseSpace)
    (t₀ : ℝ) :
    ∃ ε > 0, ∃ z : ℝ → PhaseSpace, z t₀ = z₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt z ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z t)) t := by
  rw [hamiltonianVectorField_emHamiltonian_eq m q (hA.differentiable (by norm_num)) hΦ]
  obtain ⟨z, hz0, ε, hε, hz⟩ := (contDiff_emHamiltonField m q hA
    hE).contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
      (x₀ := z₀) t₀
  exact ⟨ε, hε, z, hz0, hz⟩

/-- **Uniqueness of integral curves on an interval.** Let `A` be `C²` and `E = −∇Φ` be `C¹`.
Two integral curves of the Hamiltonian vector field of `emHamiltonian m q A Φ` on `(a, b)` that
agree at one time of `(a, b)` agree on `(a, b)`. -/
theorem emHamilton_eqOn_Ioo (m q : ℝ) {A E : Space → Space} {Φ : Space → ℝ}
    (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) {z₁ z₂ : ℝ → PhaseSpace}
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt z₁
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z₁ t)) t)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt z₂
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z₂ t)) t)
    (h0 : z₁ t₀ = z₂ t₀) : EqOn z₁ z₂ (Ioo a b) := by
  rw [hamiltonianVectorField_emHamiltonian_eq m q (hA.differentiable (by norm_num)) hΦ]
    at h₁ h₂
  exact integralCurve_eqOn_Ioo (contDiff_emHamiltonField m q hA hE) ht₀ h₁ h₂ h0

/-- **Uniqueness of integral curves for all times.** Let `A` be `C²` and `E = −∇Φ` be `C¹`. Two
integral curves of the Hamiltonian vector field of `emHamiltonian m q A Φ`, defined for all
times, that agree at one time are equal. -/
theorem emHamilton_unique (m q : ℝ) {A E : Space → Space} {Φ : Space → ℝ}
    (hA : ContDiff ℝ 2 A) (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E)
    {z₁ z₂ : ℝ → PhaseSpace}
    (h₁ : ∀ t, HasDerivAt z₁
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z₁ t)) t)
    (h₂ : ∀ t, HasDerivAt z₂
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z₂ t)) t)
    {t₀ : ℝ} (h0 : z₁ t₀ = z₂ t₀) : z₁ = z₂ := by
  funext t
  exact emHamilton_eqOn_Ioo m q hA hE hΦ (a := min t t₀ - 1) (b := max t t₀ + 1)
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
    (fun s _ => h₁ s) (fun s _ => h₂ s) h0
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩

/-! ### Lorentz orbits on a set of times -/

/-- The Newton–Lorentz equations `x' = v`, `m v' = q (E + v × B)` at the times of a set `s`
(two-sided derivatives; `s` is an open interval in the applications). -/
structure LorentzOrbitOn (m q : ℝ) (E B : Space → Space) (x v : ℝ → Space) (s : Set ℝ) :
    Prop where
  /-- The velocity is the derivative of the position. -/
  position : ∀ t ∈ s, HasDerivAt x (v t) t
  /-- Newton's law with the Lorentz force. -/
  newton : ∀ t ∈ s, ∃ a, HasDerivAt v a t ∧ m • a = q • (E (x t) + cross (v t) (B (x t)))

/-- On the set of all times, `LorentzOrbitOn` is `LorentzOrbit`. -/
theorem lorentzOrbitOn_univ {m q : ℝ} {E B : Space → Space} {x v : ℝ → Space} :
    LorentzOrbitOn m q E B x v univ ↔ LorentzOrbit m q E B x v :=
  ⟨fun h => ⟨fun t => h.position t (mem_univ t), fun t => h.newton t (mem_univ t)⟩,
    fun h => ⟨fun t _ => h.position t, fun t _ => h.newton t⟩⟩

/-- An orbit on a set of times is an orbit on every subset. -/
theorem LorentzOrbitOn.mono {m q : ℝ} {E B : Space → Space} {x v : ℝ → Space} {s s' : Set ℝ}
    (h : LorentzOrbitOn m q E B x v s) (hs : s' ⊆ s) : LorentzOrbitOn m q E B x v s' :=
  ⟨fun t ht => h.position t (hs ht), fun t ht => h.newton t (hs ht)⟩

/-- A Lorentz orbit for all times is an orbit on every set of times. -/
theorem LorentzOrbit.on {m q : ℝ} {E B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q E B x v) (s : Set ℝ) : LorentzOrbitOn m q E B x v s :=
  (lorentzOrbitOn_univ.mpr h).mono (subset_univ s)

/-- **Hamilton's equations on a set of times** (forward). Let `m ≠ 0`, `A` be differentiable,
`B = ∇ × A` and `E = −∇Φ`. At every time of `s`, the canonical lift of a Lorentz orbit on `s`
has the Hamiltonian vector field of `emHamiltonian m q A Φ` as its derivative. -/
theorem lorentzOrbitOn_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} {x v : ℝ → Space} {s : Set ℝ} (h : LorentzOrbitOn m q E B x v s)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y) (hΦ : IsPotential Φ E)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (canonicalCurve m q A x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (canonicalCurve m q A x v t)) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t ht
  have hx := h.position t ht
  have hv' : HasDerivAt (fun s => innerSL ℝ (v s)) (innerSL ℝ a) t :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t ha
  have hA' : HasDerivAt (fun s => innerSL ℝ (A (x s)))
      (innerSL ℝ (fderiv ℝ A (x t) (v t))) t :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      ((hA (x t)).hasFDerivAt.comp_hasDerivAt t hx)
  have hγ : HasDerivAt (canonicalCurve m q A x v)
      (v t, m • innerSL ℝ a + q • innerSL ℝ (fderiv ℝ A (x t) (v t))) t :=
    hx.prodMk ((hv'.const_smul m).add (hA'.const_smul q))
  refine hγ.congr_deriv ?_
  have hAt : DifferentiableAt ℝ A (canonicalCurve m q A x v t).1 := hA (x t)
  rw [hamiltonianVectorField_emHamiltonian m q hΦ hAt, kineticVelocity_canonicalCurve hm]
  refine Prod.ext rfl ?_
  change _ = q • (innerSL ℝ (v t)).comp (fderiv ℝ A (x t)) + q • innerSL ℝ (E (x t))
  ext w
  have hid := inner_cross_curlOp (fderiv ℝ A (x t)) (v t) w
  have hma : m * ⟪a, w⟫ =
      q * (⟪E (x t), w⟫ + ⟪cross (v t) (curlOp (fderiv ℝ A (x t))), w⟫) := by
    have := congrArg (fun y : Space => ⟪y, w⟫) hlaw
    simpa [inner_smul_left, inner_add_left, mul_add, hcurl, fieldCurl] using this
  simp only [_root_.add_apply, _root_.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [hma, hid, real_inner_comm (fderiv ℝ A (x t) w) (v t)]
  ring

/-- **Hamilton's equations on a set of times** (converse). Let `m ≠ 0`, `A` be differentiable,
`B = ∇ × A` and `E = −∇Φ`. If `z` has the Hamiltonian vector field of `emHamiltonian m q A Φ`
as its derivative at every time of `s`, its position and velocity are a Lorentz orbit on `s`. -/
theorem lorentzOrbitOn_of_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} {z : ℝ → PhaseSpace} {s : Set ℝ} (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (hΦ : IsPotential Φ E)
    (hz : ∀ t ∈ s, HasDerivAt z
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z t)) t) :
    LorentzOrbitOn m q E B (fun t => (z t).1) (fun t => kineticVelocity m q A (z t)) s := by
  have hz' (t : ℝ) (ht : t ∈ s) :=
    hamiltonianVectorField_emHamiltonian m q hΦ (hA (z t).1) ▸ hz t ht
  have hx (t : ℝ) (ht : t ∈ s) : HasDerivAt (fun s => (z s).1) (kineticVelocity m q A (z t)) t :=
    (ContinuousLinearMap.fst ℝ Space (StrongDual ℝ Space)).hasFDerivAt.comp_hasDerivAt t
      (hz' t ht)
  refine ⟨hx, fun t ht => ?_⟩
  set P : StrongDual ℝ Space := q • (innerSL ℝ (kineticVelocity m q A (z t))).comp
    (fderiv ℝ A (z t).1) + q • innerSL ℝ (E (z t).1) with hP
  have hp : HasDerivAt (fun s => (z s).2) P t :=
    (ContinuousLinearMap.snd ℝ Space (StrongDual ℝ Space)).hasFDerivAt.comp_hasDerivAt t
      (hz' t ht)
  have hp' : HasDerivAt (fun s => (toDual ℝ Space).symm (z s).2)
      ((toDual ℝ Space).symm P) t := by
    have h := (toDualSymmL (F := Space)).hasFDerivAt.comp_hasDerivAt t hp
    simp only [Function.comp_def, toDualSymmL_apply] at h
    exact h
  have hAx : HasDerivAt (fun s => A (z s).1)
      (fderiv ℝ A (z t).1 (kineticVelocity m q A (z t))) t :=
    (hA (z t).1).hasFDerivAt.comp_hasDerivAt t (hx t ht)
  refine ⟨_, (hp'.sub (hAx.const_smul q)).const_smul m⁻¹, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hm, one_smul]
  refine ext_inner_right ℝ fun w => ?_
  have hid := inner_cross_curlOp (fderiv ℝ A (z t).1) (kineticVelocity m q A (z t)) w
  rw [hcurl, fieldCurl, inner_sub_left, toDual_symm_apply, inner_smul_left, inner_smul_left,
    inner_add_left, hid, hP]
  simp only [_root_.add_apply, _root_.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, RCLike.conj_to_real]
  rw [real_inner_comm (fderiv ℝ A (z t).1 w)]
  ring

/-- **Lorentz orbits and integral curves correspond on a set of times.** For `m ≠ 0`, `A`
differentiable, `B = ∇ × A` and `E = −∇Φ`: `(x, v)` is a Lorentz orbit on `s` if and only if
its canonical lift satisfies Hamilton's equations for `emHamiltonian m q A Φ` at every time of
`s`. For `s = univ` this is `lorentzOrbit_iff_emHamilton`. -/
theorem lorentzOrbitOn_iff_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hΦ : IsPotential Φ E) (x v : ℝ → Space) (s : Set ℝ) :
    LorentzOrbitOn m q E B x v s ↔
      ∀ t ∈ s, HasDerivAt (canonicalCurve m q A x v)
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (canonicalCurve m q A x v t)) t := by
  refine ⟨fun h t ht => lorentzOrbitOn_emHamilton hm h hA hcurl hΦ ht, fun h => ?_⟩
  have key := lorentzOrbitOn_of_emHamilton hm hA hcurl hΦ h
  have hv : (fun t => kineticVelocity m q A (canonicalCurve m q A x v t)) = v :=
    funext fun t => kineticVelocity_canonicalCurve hm q A x v t
  rw [hv] at key
  exact key

/-- **Local existence of Lorentz orbits.** Let `m ≠ 0`, `A` be `C²`, `B = ∇ × A`, and
`E = −∇Φ` be `C¹`. For every initial time `t₀`, position `x₀` and velocity `v₀` there is a
Lorentz orbit on an open interval about `t₀` with `x t₀ = x₀` and `v t₀ = v₀`. -/
theorem lorentzOrbitOn_exists_local {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) (x₀ v₀ : Space) (t₀ : ℝ) :
    ∃ ε > 0, ∃ x v : ℝ → Space,
      LorentzOrbitOn m q E B x v (Ioo (t₀ - ε) (t₀ + ε)) ∧ x t₀ = x₀ ∧ v t₀ = v₀ := by
  obtain ⟨ε, hε, z, hz0, hz⟩ := emHamilton_exists_local m q hA hE hΦ
    (canonicalCurve m q A (fun _ => x₀) (fun _ => v₀) t₀) t₀
  refine ⟨ε, hε, _, _,
    lorentzOrbitOn_of_emHamilton hm (hA.differentiable (by norm_num)) hcurl hΦ hz, ?_, ?_⟩
  · rw [hz0]
    rfl
  · rw [hz0]
    exact kineticVelocity_canonicalCurve hm q A _ _ t₀

/-- **Uniqueness of Lorentz orbits on an interval.** Let `m ≠ 0`, `A` be `C²`, `B = ∇ × A`, and
`E = −∇Φ` be `C¹`. Two Lorentz orbits on `(a, b)` with the same position and velocity at one
time of `(a, b)` have the same position and velocity on `(a, b)`. -/
theorem lorentzOrbitOn_unique {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {x₁ v₁ x₂ v₂ : ℝ → Space} (h₁ : LorentzOrbitOn m q E B x₁ v₁ (Ioo a b))
    (h₂ : LorentzOrbitOn m q E B x₂ v₂ (Ioo a b)) (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀)
    {t : ℝ} (ht : t ∈ Ioo a b) : x₁ t = x₂ t ∧ v₁ t = v₂ t := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have h0 : canonicalCurve m q A x₁ v₁ t₀ = canonicalCurve m q A x₂ v₂ t₀ := by
    simp only [canonicalCurve, canonicalCovector, hx, hv]
  have key := emHamilton_eqOn_Ioo m q hA hE hΦ ht₀
    (fun r hr => lorentzOrbitOn_emHamilton hm h₁ hAd hcurl hΦ hr)
    (fun r hr => lorentzOrbitOn_emHamilton hm h₂ hAd hcurl hΦ hr) h0 ht
  refine ⟨congrArg Prod.fst key, ?_⟩
  rw [← kineticVelocity_canonicalCurve hm q A x₁ v₁ t, key,
    kineticVelocity_canonicalCurve hm q A x₂ v₂ t]

/-- **Uniqueness of Lorentz orbits for all times.** Let `m ≠ 0`, `A` be `C²`, `B = ∇ × A`, and
`E = −∇Φ` be `C¹`. Two Lorentz orbits with the same position and velocity at one time are
equal. -/
theorem lorentzOrbit_unique {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : ContDiff ℝ 2 A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbit m q E B x₁ v₁) (h₂ : LorentzOrbit m q E B x₂ v₂) {t₀ : ℝ}
    (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀) : x₁ = x₂ ∧ v₁ = v₂ := by
  have key (t : ℝ) : x₁ t = x₂ t ∧ v₁ t = v₂ t :=
    lorentzOrbitOn_unique hm hA hcurl hE hΦ (a := min t t₀ - 1) (b := max t t₀ + 1)
      ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩ (h₁.on _) (h₂.on _)
      hx hv ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
  exact ⟨funext fun t => (key t).1, funext fun t => (key t).2⟩

/-! ### Uniqueness of Lorentz orbits without potentials -/

/-- The Newton–Lorentz vector field with an electric field, on `Space × Space`:
`(x, v) ↦ (v, (q/m) (E x + v × B x))`. For `E = 0` it is `lorentzField m q B`
(`lorentzEMField_zero`). -/
noncomputable def lorentzEMField (m q : ℝ) (E B : Space → Space) (y : Space × Space) :
    Space × Space :=
  (y.2, (q / m) • (E y.1 + cross y.2 (B y.1)))

/-- With no electric field, `lorentzEMField` is `lorentzField` of
`Theory/Kinetic/LorentzExistence`. -/
theorem lorentzEMField_zero (m q : ℝ) (B : Space → Space) :
    lorentzEMField m q (fun _ => 0) B = lorentzField m q B := by
  funext y
  simp [lorentzEMField, lorentzField]

/-- The Newton–Lorentz vector field is `C¹` when `E` and `B` are. No hypothesis on `m`. -/
theorem contDiff_lorentzEMField (m q : ℝ) {E B : Space → Space} (hE : ContDiff ℝ 1 E)
    (hB : ContDiff ℝ 1 B) : ContDiff ℝ 1 (lorentzEMField m q E B) := by
  have hpair : ContDiff ℝ 1 (fun y : Space × Space => (y.2, B y.1)) :=
    contDiff_snd.prodMk (hB.comp contDiff_fst)
  have hcr : ContDiff ℝ 1 (fun y : Space × Space => cross y.2 (B y.1)) :=
    contDiff_cross.comp hpair
  exact contDiff_snd.prodMk (((hE.comp contDiff_fst).add hcr).const_smul (q / m))

/-- For `m ≠ 0`, a Lorentz orbit on a set of times is, at each of these times, an integral
curve `t ↦ (x t, v t)` of `lorentzEMField`. No hypothesis on the fields. -/
theorem LorentzOrbitOn.hasDerivAt_lorentzEMField {m q : ℝ} (hm : m ≠ 0)
    {E B : Space → Space} {x v : ℝ → Space} {s : Set ℝ} (h : LorentzOrbitOn m q E B x v s)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun r => (x r, v r)) (lorentzEMField m q E B (x t, v t)) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t ht
  have hacc : a = (q / m) • (E (x t) + cross (v t) (B (x t))) := by
    rw [div_eq_inv_mul, ← smul_smul, ← hlaw, smul_smul, inv_mul_cancel₀ hm, one_smul]
  exact (h.position t ht).prodMk (hacc ▸ ha)

/-- **Uniqueness of Lorentz orbits on an interval, without potentials.** Let `m ≠ 0` and let
`E` and `B` be `C¹` on all of space. Two Lorentz orbits on `(a, b)` with the same position and
velocity at one time of `(a, b)` have the same position and velocity on `(a, b)`. No vector or
scalar potential is assumed. -/
theorem lorentzOrbitOn_unique_of_contDiff {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {x₁ v₁ x₂ v₂ : ℝ → Space} (h₁ : LorentzOrbitOn m q E B x₁ v₁ (Ioo a b))
    (h₂ : LorentzOrbitOn m q E B x₂ v₂ (Ioo a b)) (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀)
    {t : ℝ} (ht : t ∈ Ioo a b) : x₁ t = x₂ t ∧ v₁ t = v₂ t := by
  have key := integralCurve_eqOn_Ioo (contDiff_lorentzEMField m q hE hB) ht₀
    (γ₁ := fun r => (x₁ r, v₁ r)) (γ₂ := fun r => (x₂ r, v₂ r))
    (fun r hr => h₁.hasDerivAt_lorentzEMField hm hr)
    (fun r hr => h₂.hasDerivAt_lorentzEMField hm hr) (Prod.ext hx hv) ht
  exact ⟨congrArg Prod.fst key, congrArg Prod.snd key⟩

/-- **Uniqueness of Lorentz orbits for all times, without potentials.** Let `m ≠ 0` and let `E`
and `B` be `C¹` on all of space. Two Lorentz orbits with the same position and velocity at one
time are equal. No vector or scalar potential is assumed: `E` need not be a gradient and `B`
need not be a curl. -/
theorem lorentzOrbit_unique_of_contDiff {m q : ℝ} (hm : m ≠ 0) {E B : Space → Space}
    (hE : ContDiff ℝ 1 E) (hB : ContDiff ℝ 1 B) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbit m q E B x₁ v₁) (h₂ : LorentzOrbit m q E B x₂ v₂) {t₀ : ℝ}
    (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀) : x₁ = x₂ ∧ v₁ = v₂ := by
  have key (t : ℝ) : x₁ t = x₂ t ∧ v₁ t = v₂ t :=
    lorentzOrbitOn_unique_of_contDiff hm hE hB (a := min t t₀ - 1) (b := max t t₀ + 1)
      ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩ (h₁.on _) (h₂.on _)
      hx hv ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
  exact ⟨funext fun t => (key t).1, funext fun t => (key t).2⟩

/-- **Global existence and uniqueness of Lorentz orbits in a `C¹` magnetic field.** If `B` is
`C¹` on all of space and `m ≠ 0`, then for every initial position `x₀` and velocity `v₀` there
is a Lorentz orbit (no electric field) for all times with `x 0 = x₀`, `v 0 = v₀`
(`lorentzOrbit_exists`), and every Lorentz orbit with these initial data equals it. No vector
potential is assumed. -/
theorem lorentzOrbit_existsUnique_of_contDiff {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    (hB : ContDiff ℝ 1 B) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q (fun _ => 0) B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨x, v, horb, hx0, hv0⟩ := lorentzOrbit_exists (q := q) hm hB x₀ v₀
  exact ⟨x, v, horb, hx0, hv0, fun x' v' h' hx' hv' =>
    lorentzOrbit_unique_of_contDiff hm contDiff_const hB h' horb (t₀ := 0)
      (hx'.trans hx0.symm) (hv'.trans hv0.symm)⟩

/-! ### Global existence for fields of linear growth -/

/-- **Global existence for a vector field of linear growth.** A `C¹` vector field `f` with
`‖f z‖ ≤ K ‖z‖ + C` has an integral curve for all times through every point: the Grönwall
bound gives the a priori bounds needed by `exists_global_of_apriori`. -/
theorem exists_global_of_linear_growth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [ProperSpace F] {f : F → F} (hf : ContDiff ℝ 1 f) {K C : ℝ}
    (hgrow : ∀ z, ‖f z‖ ≤ K * ‖z‖ + C) (x₀ : F) :
    ∃ γ : ℝ → F, γ 0 = x₀ ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  refine exists_global_of_apriori isOpen_univ hf.contDiffOn (mem_univ x₀) fun T => ?_
  have hgrow' : ∀ z, ‖f z‖ ≤ |K| * ‖z‖ + |C| := fun z =>
    (hgrow z).trans (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg z))
      (le_abs_self C))
  have hmono := gronwallBound_mono (norm_nonneg x₀) (abs_nonneg C) (abs_nonneg K)
  refine ⟨Metric.closedBall 0 (gronwallBound ‖x₀‖ |K| |C| T), isCompact_closedBall _ _,
    subset_univ _, fun c hc α h0 hα t ht => ?_⟩
  rw [mem_closedBall_zero_iff]
  have hfw : ∀ (β : ℝ → F) (g : F → F), (∀ z, ‖g z‖ ≤ |K| * ‖z‖ + |C|) → β 0 = x₀ →
      (∀ s ∈ Icc 0 c, HasDerivAt β (g (β s)) s) →
      ∀ s ∈ Icc 0 c, ‖β s‖ ≤ gronwallBound ‖x₀‖ |K| |C| T := by
    intro β g hg hβ0 hβ s hs
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := β) (f' := fun u => g (β u))
      (δ := ‖x₀‖) (K := |K|) (ε := |C|) (a := 0) (b := c)
      (fun u hu => (hβ u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hβ u (Ico_subset_Icc_self hu)).hasDerivWithinAt) (by rw [hβ0])
      (fun u _ => hg _) s hs
    rw [sub_zero] at h
    exact h.trans (hmono (hs.2.trans hc.2))
  rcases le_total 0 t with h | h
  · exact hfw α f hgrow' h0 (fun s hs => hα s ⟨by linarith [hs.1, hc.1], hs.2⟩) t ⟨h, ht.2⟩
  · have hrev : ∀ s ∈ Icc 0 c, HasDerivAt (fun u => α (-u)) (-f (α (-s))) s := by
      intro s hs
      have h1 := (hα (-s) ⟨by linarith [hs.2], by linarith [hs.1, hc.1]⟩).scomp s
        (hasDerivAt_neg s)
      simpa [Function.comp_def] using h1
    have h2 := hfw (fun u => α (-u)) (fun z => -f z)
      (fun z => by rw [norm_neg]; exact hgrow' z) (by simpa using h0) hrev (-t)
      ⟨by linarith, by linarith [ht.1]⟩
    simpa using h2

/-- **Global existence of integral curves in a linear gauge.** Let the vector potential be a
continuous linear map `L` (a uniform magnetic field) and let `E = −∇Φ` be `C¹` with
`‖E y‖ ≤ a + b ‖y‖` (for example uniform or linear). Then through every point of phase space
there is an integral curve of the Hamiltonian vector field of `emHamiltonian m q L Φ` for all
times. No hypothesis on `m`: for `m = 0` Lean's division makes the kinetic term `0`, so the
statement is then about `H = qΦ`. -/
theorem emHamilton_exists_global (m q : ℝ) (L : Space →L[ℝ] Space) {E : Space → Space}
    {Φ : Space → ℝ} (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) {a b : ℝ}
    (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧ ∀ t, HasDerivAt z
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q L Φ) (z t)) t := by
  rw [hamiltonianVectorField_emHamiltonian_eq m q L.differentiable hΦ]
  let kvL : PhaseSpace →L[ℝ] Space :=
    m⁻¹ • ((toDualSymmL (F := Space)).comp (ContinuousLinearMap.snd ℝ Space (StrongDual ℝ Space))
      - q • L.comp (ContinuousLinearMap.fst ℝ Space (StrongDual ℝ Space)))
  have hkv : ∀ z, kineticVelocity m q L z = kvL z := fun z => by
    simp [kvL, kineticVelocity, toDualSymmL_apply]
  let Λ₂ : PhaseSpace →L[ℝ] StrongDual ℝ Space :=
    q • ((ContinuousLinearMap.compL ℝ Space Space ℝ).flip L).comp
      ((innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).comp kvL)
  have hdecomp : ∀ z, emHamiltonField m q L E z =
      (kvL.prod Λ₂) z + (0, q • innerSL ℝ (E z.1)) := fun z => by
    refine Prod.ext ?_ ?_
    · simp [emHamiltonField, hkv]
    · simp [emHamiltonField, hkv, Λ₂, L.fderiv]
  refine exists_global_of_linear_growth
    (contDiff_emHamiltonField m q (L.contDiff (n := 2)) hE)
    (K := ‖kvL.prod Λ₂‖ + |q| * |b|) (C := |q| * |a|) (fun z => ?_) z₀
  rw [hdecomp]
  have h1 : ‖(kvL.prod Λ₂) z‖ ≤ ‖kvL.prod Λ₂‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖((0 : Space), q • innerSL ℝ (E z.1))‖ ≤ |q| * (|a| + |b| * ‖z‖) := by
    rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), norm_smul, Real.norm_eq_abs,
      innerSL_apply_norm]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg q)
    calc ‖E z.1‖ ≤ a + b * ‖z.1‖ := hgrow _
      _ ≤ |a| + |b| * ‖z‖ := add_le_add (le_abs_self a)
          (mul_le_mul (le_abs_self b) (norm_fst_le z) (norm_nonneg _) (abs_nonneg b))
  calc ‖(kvL.prod Λ₂) z + (0, q • innerSL ℝ (E z.1))‖
      ≤ ‖(kvL.prod Λ₂) z‖ + ‖((0 : Space), q • innerSL ℝ (E z.1))‖ := norm_add_le _ _
    _ ≤ ‖kvL.prod Λ₂‖ * ‖z‖ + |q| * (|a| + |b| * ‖z‖) := add_le_add h1 h2
    _ = (‖kvL.prod Λ₂‖ + |q| * |b|) * ‖z‖ + |q| * |a| := by ring

/-- **Global existence and uniqueness of Lorentz orbits in a uniform magnetic field with an
electric field of linear growth.** Let `m ≠ 0`, `B = ∇ × L` for a continuous linear vector
potential `L`, and `E = −∇Φ` be `C¹` with `‖E y‖ ≤ a + b ‖y‖`. For every initial position `x₀`
and velocity `v₀` there is a Lorentz orbit for all times with `x 0 = x₀`, `v 0 = v₀`, and every
Lorentz orbit with these initial data equals it. -/
theorem lorentzOrbit_existsUnique_linearGauge {m q : ℝ} (hm : m ≠ 0) (L : Space →L[ℝ] Space)
    {E B : Space → Space} {Φ : Space → ℝ} (hcurl : ∀ y, B y = fieldCurl L y)
    (hE : ContDiff ℝ 1 E) (hΦ : IsPotential Φ E) {a b : ℝ}
    (hgrow : ∀ y, ‖E y‖ ≤ a + b * ‖y‖) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q E B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q E B x' v' → x' 0 = x₀ → v' 0 = v₀ →
        x' = x ∧ v' = v := by
  obtain ⟨z, hz0, hz⟩ := emHamilton_exists_global m q L hE hΦ hgrow
    (canonicalCurve m q L (fun _ => x₀) (fun _ => v₀) 0)
  have horb := lorentzOrbit_of_emHamilton hm L.differentiable hcurl hΦ hz
  have hx0 : (z 0).1 = x₀ := by
    rw [hz0]
    rfl
  have hv0 : kineticVelocity m q L (z 0) = v₀ := by
    rw [hz0]
    exact kineticVelocity_canonicalCurve hm q L _ _ 0
  exact ⟨_, _, horb, hx0, hv0, fun x' v' h' hx' hv' =>
    lorentzOrbit_unique hm (L.contDiff (n := 2)) hcurl hE hΦ h' horb (t₀ := 0)
      (hx'.trans hx0.symm) (hv'.trans hv0.symm)⟩

/-- The symmetric gauge `A(y) = (B × y) / 2` of a uniform magnetic field `B`, as a continuous
linear map. -/
noncomputable def symmetricGauge (Bv : Space) : Space →L[ℝ] Space :=
  (1 / 2 : ℝ) • crossBilinear Bv

/-- `∇ × ((B × y) / 2) = B`. -/
theorem fieldCurl_symmetricGauge (Bv y : Space) : fieldCurl (symmetricGauge Bv) y = Bv := by
  rw [fieldCurl, (symmetricGauge Bv).fderiv]
  ext i
  fin_cases i <;>
    simp [curlOp, symmetricGauge, crossBilinear_apply, cross, cross_apply] <;> ring

/-- **Uniform fields.** For `m ≠ 0` and arbitrary uniform fields `E` and `B` (not necessarily
perpendicular), there is exactly one Lorentz orbit for all times from every initial position
and velocity. For `E = E₀ e_x`, `B = B₀ e_z` it is the explicit orbit of `crossedField_orbit`
(when `q, B₀ ≠ 0`). -/
theorem lorentzOrbit_existsUnique_uniform {m : ℝ} (hm : m ≠ 0) (q : ℝ) (Ev Bv x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => Ev) (fun _ => Bv) x v ∧ x 0 = x₀ ∧
      v 0 = v₀ ∧ ∀ x' v' : ℝ → Space, LorentzOrbit m q (fun _ => Ev) (fun _ => Bv) x' v' →
        x' 0 = x₀ → v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_linearGauge hm (symmetricGauge Bv) (Φ := fun y => -⟪Ev, y⟫)
    (fun y => (fieldCurl_symmetricGauge Bv y).symm) contDiff_const
    (fun _ => (-(innerSL ℝ Ev)).hasFDerivAt) (a := ‖Ev‖) (b := 0) (fun _ => by simp) x₀ v₀

/-- **The drift orbit is the only orbit with its initial data.** For `m, q, B₀ ≠ 0`, every
Lorentz orbit in the crossed fields `E₀ e_x`, `B₀ e_z` that starts with the position and
velocity of a drift orbit is that drift orbit. -/
theorem crossedField_orbit_unique {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0)
    (E₀ : ℝ) (X : Space) (a b w : ℝ) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => E₀ • coordVec 0) (fun _ => B₀ • coordVec 2) x v)
    (hx : x 0 = crossedPosition m q E₀ B₀ X a b w 0)
    (hv : v 0 = crossedVelocity m q E₀ B₀ a b w 0) :
    x = crossedPosition m q E₀ B₀ X a b w ∧ v = crossedVelocity m q E₀ B₀ a b w :=
  lorentzOrbit_unique hm ((symmetricGauge (B₀ • coordVec 2)).contDiff (n := 2))
    (Φ := fun y => -⟪(E₀ • coordVec 0 : Space), y⟫)
    (fun y => (fieldCurl_symmetricGauge (B₀ • coordVec 2) y).symm) contDiff_const
    (fun _ => (-(innerSL ℝ (E₀ • coordVec 0 : Space))).hasFDerivAt) h
    (crossedField_orbit hm hq hB E₀ X a b w) hx hv

end PlasmaLean.Kinetic
