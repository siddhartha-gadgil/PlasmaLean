/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CrossedFieldOrbit
public import PlasmaLean.Sanity.MagneticHamiltonConverse

/-!
# Sanity checks for `Theory/Kinetic/CrossedFieldOrbit`

The crossed uniform fields are `E₀ e_x` (`uniformE E₀`, potential `uniformPotential E₀`) and
`B₀ e_z` (Landau gauge `landau B₀`).

* Accepted: `unit_drift_orbit`: the drift orbit with `m = q = E₀ = B₀ = 1`, gyration velocity
  `(1, 0)` and guiding centre at the origin is a Lorentz orbit. Spot values:
  `unit_velocity_zero` (`v(0) = (1, −1, 0)`), `unit_velocity_pi` (`v(π) = (−1, −1, 0)`),
  `unit_position_pi` (`x(π) = (0, −1 − π, 0)`), `unit_position_period` (over the period `2π`
  the position moves by `−2π e_y`).
* Accepted: `crossedPosition_zero_radius`, `crossedVelocity_zero_radius`: with zero gyration
  velocity and zero parallel velocity the drift orbit is the straight line
  `X + t v_d`, `v = v_d`. `drift_line_orbit`: that line is a Lorentz orbit for `B₀ ≠ 0`, with no
  hypothesis on `m` or `q`.
* Accepted: `drift_orbit_hamilton`: `crossed_fields_hamilton` of
  `Sanity/MagneticHamiltonConverse` applied to the explicit orbit, so that theorem has an
  instance with `B₀ ≠ 0`. `drift_orbit_hamiltonian_conserved`, `drift_orbit_energy`: the
  Hamiltonian and the energy `(m/2)‖v‖² − q E₀ x` are constant along it.
* Rejected: `opposite_drift_not_orbit`: for `q ≠ 0`, `E₀ ≠ 0`, `B₀ ≠ 0` the uniform motion with
  the opposite velocity `+(E₀ / B₀) e_y` is not a Lorentz orbit; this fixes the sign of the
  drift. `opposite_drift_orbit_zero_field` shows the rejection is due to `E₀ ≠ 0`.
* Uniqueness: `uniform_orbits_coincide`: two Lorentz orbits in the crossed fields with the same
  initial position and velocity coincide (in the Landau gauge). `drift_orbits_differ`: orbits
  with different initial velocities differ, so the hypothesis on the initial data is used.
* Regression (audit AV-M4), uniqueness without potentials: `shear_orbit_existsUnique`: in the
  sheared field `B = x e_z`, which is not uniform, there is exactly one Lorentz orbit for all
  times from every initial position and velocity (`lorentzOrbit_existsUnique_of_contDiff`).
  `rotational_E_orbits_coincide`: uniqueness in the electric field `E = x e_y`, whose curl is
  `e_z ≠ 0` (`rotational_E_curl_ne_zero`), so that it is not a gradient (this last step is
  not formalized here) and `lorentzOrbit_unique`, which needs `E = −∇Φ`, does not apply.
-/

@[expose] public section

namespace PlasmaLean.Sanity.CrossedFieldOrbit

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum
open PlasmaLean.Sanity.NoetherLagrangian PlasmaLean.Sanity.MagneticHamiltonConverse TauCeti
open WithLp
open scoped RealInnerProductSpace

/-- **Accepted fixture**: the drift orbit with `m = q = E₀ = B₀ = 1`, gyration velocity
`(1, 0)`, no parallel velocity and guiding centre at the origin. -/
theorem unit_drift_orbit :
    LorentzOrbit 1 1 (uniformE 1) (fun _ => (1 : ℝ) • coordVec 2)
      (crossedPosition 1 1 1 1 0 1 0 0) (crossedVelocity 1 1 1 1 1 0 0) :=
  crossedField_orbit one_ne_zero one_ne_zero one_ne_zero 1 0 1 0 0

/-- Spot value: the initial velocity of the unit drift orbit is `(1, −1, 0)`. -/
theorem unit_velocity_zero : crossedVelocity 1 1 1 1 1 0 0 0 = toLp 2 ![1, -1, 0] := by
  rw [crossedVelocity_zero]
  norm_num

/-- Spot value: half a gyro-period later the velocity is `(−1, −1, 0)`; the gyration has
reversed and the drift `−e_y` is unchanged. -/
theorem unit_velocity_pi : crossedVelocity 1 1 1 1 1 0 0 Real.pi = toLp 2 ![-1, -1, 0] := by
  simp [crossedVelocity, gyroFrequency]

/-- Spot value: the position of the unit drift orbit at time `π` is `(0, −1 − π, 0)`. -/
theorem unit_position_pi :
    crossedPosition 1 1 1 1 0 1 0 0 Real.pi = toLp 2 ![0, -1 - Real.pi, 0] := by
  simp [crossedPosition, gyroFrequency]

/-- Spot value: over the gyro-period `2π` the unit drift orbit moves by `−2π e_y`. -/
theorem unit_position_period (t : ℝ) :
    crossedPosition 1 1 1 1 0 1 0 0 (t + 2 * Real.pi) =
      crossedPosition 1 1 1 1 0 1 0 0 t + (2 * Real.pi) • driftVelocity 1 1 := by
  have h := crossedPosition_period (m := 1) (q := 1) (B₀ := 1) one_ne_zero one_ne_zero
    one_ne_zero 1 0 1 0 0 t
  simpa [gyroFrequency] using h

/-- With zero gyration velocity and zero parallel velocity the position is the straight line
`X + t v_d`. -/
theorem crossedPosition_zero_radius (m q E₀ B₀ : ℝ) (X : Space) (t : ℝ) :
    crossedPosition m q E₀ B₀ X 0 0 0 t = X + t • driftVelocity E₀ B₀ := by
  ext i
  fin_cases i <;> simp [crossedPosition, driftVelocity]
  ring

/-- With zero gyration velocity and zero parallel velocity the velocity is the drift
velocity. -/
theorem crossedVelocity_zero_radius (m q E₀ B₀ t : ℝ) :
    crossedVelocity m q E₀ B₀ 0 0 0 t = driftVelocity E₀ B₀ := by
  ext i
  fin_cases i <;> simp [crossedVelocity, driftVelocity]

/-- **Accepted fixture**: uniform motion with the drift velocity `−(E₀ / B₀) e_y` is a Lorentz
orbit in the crossed fields, for `B₀ ≠ 0` and every mass and charge: the electric force and
the magnetic force cancel. -/
theorem drift_line_orbit (m q E₀ : ℝ) {B₀ : ℝ} (hB : B₀ ≠ 0) (X : Space) :
    LorentzOrbit m q (uniformE E₀) (fun _ => B₀ • coordVec 2)
      (fun t => X + t • driftVelocity E₀ B₀) (fun _ => driftVelocity E₀ B₀) := by
  constructor
  · intro t
    simpa using ((hasDerivAt_id t).smul_const (driftVelocity E₀ B₀)).const_add X
  · intro t
    refine ⟨0, hasDerivAt_const t _, ?_⟩
    have hc : uniformE E₀ (X + t • driftVelocity E₀ B₀) +
        cross (driftVelocity E₀ B₀) (B₀ • coordVec 2) = 0 := by
      ext i
      fin_cases i <;> simp [uniformE, driftVelocity, cross, cross_apply]
      field_simp
      ring
    rw [hc, smul_zero, smul_zero]

/-- **Rejected**: for `q ≠ 0`, `E₀ ≠ 0`, `B₀ ≠ 0`, uniform motion with the opposite velocity
`+(E₀ / B₀) e_y` is not a Lorentz orbit: the two forces add instead of cancelling. This checks
the sign of the drift. -/
theorem opposite_drift_not_orbit (m : ℝ) {q E₀ B₀ : ℝ} (hq : q ≠ 0) (hE : E₀ ≠ 0)
    (hB : B₀ ≠ 0) (X : Space) :
    ¬ LorentzOrbit m q (uniformE E₀) (fun _ => B₀ • coordVec 2)
      (fun t => X + t • (-driftVelocity E₀ B₀)) (fun _ => -driftVelocity E₀ B₀) := by
  intro h
  obtain ⟨a, ha, hlaw⟩ := h.newton 0
  have ha0 : a = 0 := ha.unique (hasDerivAt_const 0 _)
  rw [ha0, smul_zero] at hlaw
  have h0 := congrArg (fun y : Space => y 0) hlaw
  have h1 : q * E₀ + q * (B₀ * (E₀ / B₀)) = 0 := by
    simpa [uniformE, driftVelocity, cross, cross_apply] using h0.symm
  have e : B₀ * (E₀ / B₀) = E₀ := by field_simp
  rw [e] at h1
  exact mul_ne_zero hq hE (by linarith)

/-- **Content check**: without an electric field the particle at rest is an orbit, and the
"opposite drift" is the same motion; the rejection above is due to `E₀ ≠ 0`. -/
theorem opposite_drift_orbit_zero_field (m q : ℝ) {B₀ : ℝ} (hB : B₀ ≠ 0) (X : Space) :
    LorentzOrbit m q (uniformE 0) (fun _ => B₀ • coordVec 2)
      (fun t => X + t • (-driftVelocity 0 B₀)) (fun _ => -driftVelocity 0 B₀) := by
  have h := drift_line_orbit m q 0 hB X
  have e : driftVelocity 0 B₀ = 0 := by simp [driftVelocity]
  rw [e] at h ⊢
  simpa using h

/-- **Accepted fixture**: `crossed_fields_hamilton` has an instance with `B₀ ≠ 0`. In the Landau
gauge with the potential `−E₀ x`, the canonical lift of the explicit drift orbit is an integral
curve of the Hamiltonian vector field. -/
theorem drift_orbit_hamilton {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ)
    (X : Space) (a b w t : ℝ) :
    HasDerivAt (canonicalCurve m q (landau B₀) (crossedPosition m q E₀ B₀ X a b w)
        (crossedVelocity m q E₀ B₀ a b w))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q (landau B₀) (uniformPotential E₀))
        (canonicalCurve m q (landau B₀) (crossedPosition m q E₀ B₀ X a b w)
          (crossedVelocity m q E₀ B₀ a b w) t)) t :=
  crossed_fields_hamilton hm (crossedField_orbit hm hq hB E₀ X a b w) t

/-- **Accepted fixture**: the Hamiltonian is constant along the lift of the drift orbit. -/
theorem drift_orbit_hamiltonian_conserved {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0)
    (hB : B₀ ≠ 0) (E₀ : ℝ) (X : Space) (a b w s t : ℝ) :
    emHamiltonian m q (landau B₀) (uniformPotential E₀)
        (canonicalCurve m q (landau B₀) (crossedPosition m q E₀ B₀ X a b w)
          (crossedVelocity m q E₀ B₀ a b w) s) =
      emHamiltonian m q (landau B₀) (uniformPotential E₀)
        (canonicalCurve m q (landau B₀) (crossedPosition m q E₀ B₀ X a b w)
          (crossedVelocity m q E₀ B₀ a b w) t) :=
  emHamiltonian_conserved m q (landau B₀).differentiable (isPotential_uniform E₀)
    (drift_orbit_hamilton hm hq hB E₀ X a b w) s t

/-- **Accepted fixture**: the energy `(m/2)‖v‖² − q E₀ x` is constant along the drift orbit:
the kinetic energy oscillates as the particle moves along `E`. -/
theorem drift_orbit_energy {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) (E₀ : ℝ)
    (X : Space) (a b w s t : ℝ) :
    m / 2 * ‖crossedVelocity m q E₀ B₀ a b w s‖ ^ 2 -
        q * (E₀ * crossedPosition m q E₀ B₀ X a b w s 0) =
      m / 2 * ‖crossedVelocity m q E₀ B₀ a b w t‖ ^ 2 -
        q * (E₀ * crossedPosition m q E₀ B₀ X a b w t 0) := by
  have h := crossedField_energy hm hq hB E₀ (isPotential_uniform E₀) X a b w s t
  simp only [orbitEnergy, uniformPotential_apply] at h
  linarith

/-- **Uniqueness check**: two Lorentz orbits in the crossed uniform fields with the same
initial position and velocity coincide (`lorentzOrbit_unique` in the Landau gauge). -/
theorem uniform_orbits_coincide {m : ℝ} (hm : m ≠ 0) (q E₀ B₀ : ℝ) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbit m q (uniformE E₀) (fun _ => B₀ • coordVec 2) x₁ v₁)
    (h₂ : LorentzOrbit m q (uniformE E₀) (fun _ => B₀ • coordVec 2) x₂ v₂)
    (hx : x₁ 0 = x₂ 0) (hv : v₁ 0 = v₂ 0) : x₁ = x₂ ∧ v₁ = v₂ :=
  lorentzOrbit_unique hm ((landau B₀).contDiff (n := 2)) (fun y => (curl_landau B₀ y).symm)
    contDiff_const (isPotential_uniform E₀) h₁ h₂ hx hv

/-- **Content check**: the hypothesis on the initial velocity is used. The unit drift orbit and
the uniform drift from the same initial position are two different Lorentz orbits. -/
theorem drift_orbits_differ :
    LorentzOrbit 1 1 (uniformE 1) (fun _ => (1 : ℝ) • coordVec 2)
        (crossedPosition 1 1 1 1 0 1 0 0) (crossedVelocity 1 1 1 1 1 0 0) ∧
      LorentzOrbit 1 1 (uniformE 1) (fun _ => (1 : ℝ) • coordVec 2)
        (fun t => crossedPosition 1 1 1 1 0 1 0 0 0 + t • driftVelocity 1 1)
        (fun _ => driftVelocity 1 1) ∧
      crossedVelocity 1 1 1 1 1 0 0 ≠ fun _ => driftVelocity 1 1 := by
  refine ⟨unit_drift_orbit, drift_line_orbit 1 1 1 one_ne_zero _, fun h => ?_⟩
  have h0 := congrArg (fun f : ℝ → Space => f 0 0) h
  simp [crossedVelocity, driftVelocity] at h0

/-- Regression (audit AV-M4): in the sheared field `B = x e_z` (not uniform, no electric
field) there is exactly one Lorentz orbit for all times from every initial position and
velocity. No vector potential enters the statement or the proof. -/
theorem shear_orbit_existsUnique {m : ℝ} (hm : m ≠ 0) (q : ℝ) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) (fun y => y 0 • coordVec 2) x v ∧
      x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q (fun _ => 0) (fun y => y 0 • coordVec 2) x' v' →
        x' 0 = x₀ → v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_contDiff hm
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff.smul contDiff_const) x₀ v₀

/-- The electric field `E = x e_y` (the linear map `landau 1`) has curl `e_z ≠ 0`. -/
theorem rotational_E_curl_ne_zero (y : Space) : fieldCurl (landau 1) y ≠ 0 := by
  rw [curl_landau, one_smul]
  intro h
  have h2 := congrArg (fun z : Space => z 2) h
  simp at h2

/-- Regression (audit AV-M4): uniqueness of Lorentz orbits in the electric field `E = x e_y`,
which is not curl free, and an arbitrary `C¹` magnetic field. `lorentzOrbit_unique` needs a
scalar and a vector potential; `lorentzOrbit_unique_of_contDiff` needs neither. -/
theorem rotational_E_orbits_coincide {m : ℝ} (hm : m ≠ 0) (q : ℝ) {B : Space → Space}
    (hB : ContDiff ℝ 1 B) {x₁ v₁ x₂ v₂ : ℝ → Space}
    (h₁ : LorentzOrbit m q (landau 1) B x₁ v₁) (h₂ : LorentzOrbit m q (landau 1) B x₂ v₂)
    {t₀ : ℝ} (hx : x₁ t₀ = x₂ t₀) (hv : v₁ t₀ = v₂ t₀) : x₁ = x₂ ∧ v₁ = v₂ :=
  lorentzOrbit_unique_of_contDiff hm (landau 1).contDiff hB h₁ h₂ hx hv

end PlasmaLean.Sanity.CrossedFieldOrbit
