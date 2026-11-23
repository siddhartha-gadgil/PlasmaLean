/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MagneticHamiltonConverse
public import PlasmaLean.Sanity.NoetherLagrangian

/-!
# Sanity checks for `Theory/Kinetic/MagneticHamiltonConverse`

The uniform electric field `E₀ e_x` (`uniformE E₀`) with potential `Φ = −E₀ x`
(`uniformPotential E₀`, `isPotential_uniform`).

* Accepted: `accel_orbit`: with no magnetic field the uniformly accelerated trajectory
  `x = X + t u + (q E₀ / 2m) t² e_x` is a Lorentz orbit, so the hypotheses of the theory are
  satisfiable with a nonzero electric field. `accel_hamilton`: its canonical lift (vector
  potential zero) is an integral curve of the Hamiltonian vector field of `emHamiltonian`.
  `accel_recovered`: the converse, applied to that integral curve, returns the same position
  and velocity. `accel_energy`: the Hamiltonian on the lift is constant in time.
* Accepted: `crossed_fields_hamilton`: every Lorentz orbit in the crossed uniform fields
  `E₀ e_x`, `B₀ e_z` lifts, in the Landau gauge, to an integral curve.
* Rejected: `free_line_not_hamilton`: for `q ≠ 0`, `E₀ ≠ 0` (and `m ≠ 0`) the lift of the free
  straight line `x = X + t u` is not an integral curve, so Hamilton's equation for
  `emHamiltonian` sees the electric field. `free_line_hamilton_zero_charge`: for `q = 0` the
  same line is an integral curve, so the rejection is due to the electric force.
-/

@[expose] public section

namespace PlasmaLean.Sanity.MagneticHamiltonConverse

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum
open PlasmaLean.Sanity.NoetherLagrangian TauCeti
open scoped RealInnerProductSpace

/-- The uniform electric field `E₀ e_x`. -/
noncomputable def uniformE (E₀ : ℝ) : Space → Space := fun _ => E₀ • coordVec 0

/-- The potential `Φ = −E₀ x` of the uniform electric field. -/
noncomputable def uniformPotential (E₀ : ℝ) : Space → ℝ := fun y => -⟪E₀ • coordVec 0, y⟫

/-- The potential in coordinates: `Φ(y) = −E₀ y₀`. -/
theorem uniformPotential_apply (E₀ : ℝ) (y : Space) : uniformPotential E₀ y = -(E₀ * y 0) := by
  simp [uniformPotential, inner_smul_left, coordVec, EuclideanSpace.inner_single_left]

/-- `E₀ e_x = −∇(−E₀ x)`. -/
theorem isPotential_uniform (E₀ : ℝ) : IsPotential (uniformPotential E₀) (uniformE E₀) :=
  fun _ => (-(innerSL ℝ (E₀ • coordVec 0))).hasFDerivAt

/-- The zero vector potential has zero curl. -/
theorem fieldCurl_zero (y : Space) : (0 : Space) = fieldCurl (fun _ => (0 : Space)) y := by
  ext i
  fin_cases i <;> simp [fieldCurl, curlOp]

/-- Position of a uniformly accelerated particle: `X + t u + (q E₀ / 2m) t² e_x`. -/
noncomputable def accelPosition (m q E₀ : ℝ) (X u : Space) (t : ℝ) : Space :=
  X + t • u + (q * E₀ / (2 * m) * t ^ 2) • coordVec 0

/-- Velocity of a uniformly accelerated particle: `u + (q E₀ / m) t e_x`. -/
noncomputable def accelVelocity (m q E₀ : ℝ) (u : Space) (t : ℝ) : Space :=
  u + (q * E₀ / m * t) • coordVec 0

/-- **Accepted fixture**: in the uniform electric field with no magnetic field, the uniformly
accelerated trajectory is a Lorentz orbit (for `m ≠ 0`). -/
theorem accel_orbit {m : ℝ} (hm : m ≠ 0) (q E₀ : ℝ) (X u : Space) :
    LorentzOrbit m q (uniformE E₀) (fun _ => 0) (accelPosition m q E₀ X u)
      (accelVelocity m q E₀ u) := by
  constructor
  · intro t
    have h1 : HasDerivAt (fun s : ℝ => s • u) u t := by
      simpa using (hasDerivAt_id t).smul_const u
    have h2 : HasDerivAt (fun s : ℝ => (q * E₀ / (2 * m) * s ^ 2) • coordVec 0)
        ((q * E₀ / m * t) • (coordVec 0 : Space)) t := by
      have h := (((hasDerivAt_pow 2 t).const_mul (q * E₀ / (2 * m))).smul_const
        (coordVec 0 : Space))
      refine h.congr_deriv ?_
      congr 1
      field_simp
      ring
    exact ((h1.const_add X).add h2)
  · intro t
    refine ⟨(q * E₀ / m) • coordVec 0, ?_, ?_⟩
    · have h := ((hasDerivAt_id t).const_mul (q * E₀ / m)).smul_const (coordVec 0 : Space)
      exact (h.const_add u).congr_deriv (by rw [mul_one])
    · have hc : cross (accelVelocity m q E₀ u t) (0 : Space) = 0 := by
        ext i
        fin_cases i <;> simp [cross, cross_apply]
      rw [hc, add_zero, uniformE, smul_smul, smul_smul]
      congr 1
      field_simp

/-- **Accepted fixture**: the canonical lift of the uniformly accelerated orbit is an integral
curve of the Hamiltonian vector field of `emHamiltonian` (zero vector potential). -/
theorem accel_hamilton {m : ℝ} (hm : m ≠ 0) (q E₀ : ℝ) (X u : Space) (t : ℝ) :
    HasDerivAt (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
        (accelVelocity m q E₀ u))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q (fun _ => 0) (uniformPotential E₀))
        (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
          (accelVelocity m q E₀ u) t)) t :=
  lorentzOrbit_emHamilton hm (accel_orbit hm q E₀ X u) (differentiable_const 0) fieldCurl_zero
    (isPotential_uniform E₀) t

/-- **Accepted fixture**: the converse theorem, applied to the integral curve of
`accel_hamilton`, returns a Lorentz orbit whose position and velocity are the uniformly
accelerated ones. -/
theorem accel_recovered {m : ℝ} (hm : m ≠ 0) (q E₀ : ℝ) (X u : Space) :
    LorentzOrbit m q (uniformE E₀) (fun _ => 0)
        (fun t => (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
          (accelVelocity m q E₀ u) t).1)
        (fun t => kineticVelocity m q (fun _ => 0)
          (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
            (accelVelocity m q E₀ u) t)) ∧
      (∀ t, (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
          (accelVelocity m q E₀ u) t).1 = accelPosition m q E₀ X u t) ∧
      ∀ t, kineticVelocity m q (fun _ => 0)
          (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
            (accelVelocity m q E₀ u) t) = accelVelocity m q E₀ u t :=
  ⟨lorentzOrbit_of_emHamilton hm (differentiable_const 0) fieldCurl_zero
      (isPotential_uniform E₀) (accel_hamilton hm q E₀ X u),
    fun _ => rfl, fun t => kineticVelocity_canonicalCurve hm q _ _ _ t⟩

/-- **Accepted fixture**: the Hamiltonian on the lift of the uniformly accelerated orbit does
not depend on time. -/
theorem accel_energy {m : ℝ} (hm : m ≠ 0) (q E₀ : ℝ) (X u : Space) (s t : ℝ) :
    emHamiltonian m q (fun _ => 0) (uniformPotential E₀)
        (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
          (accelVelocity m q E₀ u) s) =
      emHamiltonian m q (fun _ => 0) (uniformPotential E₀)
        (canonicalCurve m q (fun _ => 0) (accelPosition m q E₀ X u)
          (accelVelocity m q E₀ u) t) :=
  emHamiltonian_conserved m q (differentiable_const 0) (isPotential_uniform E₀)
    (accel_hamilton hm q E₀ X u) s t

/-- **Accepted fixture**: every Lorentz orbit in the crossed uniform fields `E₀ e_x` and
`B₀ e_z` lifts, in the Landau gauge, to an integral curve of the Hamiltonian vector field. -/
theorem crossed_fields_hamilton {m q E₀ B₀ : ℝ} (hm : m ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (uniformE E₀) (fun _ => B₀ • coordVec 2) x v) (t : ℝ) :
    HasDerivAt (canonicalCurve m q (landau B₀) x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q (landau B₀) (uniformPotential E₀))
        (canonicalCurve m q (landau B₀) x v t)) t :=
  lorentzOrbit_emHamilton hm h (landau B₀).differentiable (fun y => (curl_landau B₀ y).symm)
    (isPotential_uniform E₀) t

/-- **Rejected**: for `q ≠ 0` and `E₀ ≠ 0` the canonical lift of the free straight line
`x = X + t u`, `v = u` is not an integral curve of the Hamiltonian vector field of
`emHamiltonian` in the uniform electric field. -/
theorem free_line_not_hamilton {m q E₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hE : E₀ ≠ 0)
    (X u : Space) :
    ¬ ∀ t, HasDerivAt (canonicalCurve m q (fun _ => 0) (fun t => X + t • u) (fun _ => u))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q (fun _ => 0) (uniformPotential E₀))
        (canonicalCurve m q (fun _ => 0) (fun t => X + t • u) (fun _ => u) t)) t := by
  intro h
  have horb := (lorentzOrbit_iff_emHamilton (B := fun _ => 0) hm (differentiable_const 0)
    fieldCurl_zero (isPotential_uniform E₀) _ _).mpr h
  obtain ⟨a, ha, hlaw⟩ := horb.newton 0
  have ha0 : a = 0 := ha.unique (hasDerivAt_const 0 u)
  have hc : cross u (0 : Space) = 0 := by
    ext i
    fin_cases i <;> simp [cross, cross_apply]
  rw [ha0, smul_zero, hc, add_zero, uniformE, smul_smul] at hlaw
  have h0 := congrArg (fun y : Space => y 0) hlaw
  have h1 : q * E₀ = 0 := by simpa [coordVec] using h0.symm
  exact mul_ne_zero hq hE h1

/-- **Content check**: for zero charge the free straight line is an integral curve, in the
same electric field; the rejection above is due to the electric force. -/
theorem free_line_hamilton_zero_charge {m : ℝ} (hm : m ≠ 0) (E₀ : ℝ) (X u : Space) (t : ℝ) :
    HasDerivAt (canonicalCurve m 0 (fun _ => 0) (fun t => X + t • u) (fun _ => u))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m 0 (fun _ => 0) (uniformPotential E₀))
        (canonicalCurve m 0 (fun _ => 0) (fun t => X + t • u) (fun _ => u) t)) t := by
  refine lorentzOrbit_emHamilton (E := uniformE E₀) (B := fun _ => 0) hm ?_
    (differentiable_const 0) fieldCurl_zero (isPotential_uniform E₀) t
  constructor
  · intro s
    simpa using ((hasDerivAt_id s).smul_const u).const_add X
  · intro s
    exact ⟨0, hasDerivAt_const s u, by simp⟩

end PlasmaLean.Sanity.MagneticHamiltonConverse
