/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MagneticSymplectic
public import PlasmaLean.Sanity.NoetherLagrangian

/-!
# Sanity checks for `Theory/Kinetic/MagneticSymplectic`

The uniform field `B₀ e_z` in the Landau gauge `A = B₀ x e_y` (`landau B₀`).

* Accepted: `extDeriv_potentialForm_landau`: `d(q A♭) = q B₀ • flux e_z`, and
  `landau_magneticForm`: the kinetic momentum map pulls the canonical form back to
  `Ω + q B₀ dx ∧ dy`.
* Accepted: `landau_hamilton`: every Lorentz orbit in the uniform field gives an integral
  curve of the Hamiltonian vector field of `magneticHamiltonian`; `helix_hamilton` applies it
  to the explicit helix of `Theory/Kinetic/FullOrbit`, so the hypothesis is satisfiable, and
  `helix_energy` evaluates the Hamiltonian there as `(m/2)(u² + w²)`.
* Content checks: `magneticForm_zero_charge`: for `q = 0` the magnetic term vanishes and the
  canonical form is preserved; `landau_not_symplectic`: for `q ≠ 0` and `B₀ ≠ 0` the kinetic
  momentum map does not preserve the canonical form, so the magnetic term cannot be dropped.
-/

@[expose] public section

namespace PlasmaLean.Sanity.MagneticSymplectic

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open PlasmaLean.Sanity.NoetherLagrangian TauCeti
open scoped RealInnerProductSpace

/-- The flux form of `e_z` is `dx ∧ dy`. -/
theorem flux_coordVec_two (a b : Space) :
    flux (coordVec 2) ![a, b] = a 0 * b 1 - a 1 * b 0 := by
  rw [flux_apply, volForm_vec]
  simp

/-- **Accepted fixture**: in the Landau gauge, `d(q A♭) = q B₀ • flux e_z`. -/
theorem extDeriv_potentialForm_landau (q B₀ : ℝ) (y : Space) :
    extDeriv (potentialForm q (landau B₀)) y = (q * B₀) • flux (coordVec 2) := by
  rw [extDeriv_potentialForm, curl_landau, map_smul, smul_smul]

/-- **Accepted fixture**: for the uniform field the kinetic momentum map pulls the canonical
form back to `Ω + q B₀ dx ∧ dy`. -/
theorem landau_magneticForm (q B₀ : ℝ) (z v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap q (landau B₀)) z v)
        (fderiv ℝ (kineticMomentumMap q (landau B₀)) z w) =
      strongDualCotangentSymplecticForm v w +
        q * B₀ * (v.1 0 * w.1 1 - v.1 1 * w.1 0) := by
  rw [canonicalForm_fderiv_kineticMomentumMap_flux q (landau B₀).differentiableAt,
    curl_landau, map_smul, ContinuousAlternatingMap.smul_apply, flux_coordVec_two, smul_eq_mul]
  ring

/-- **Content check**: with zero charge the magnetic term vanishes, for every vector
potential: the derivative of the kinetic momentum map preserves the canonical form. -/
theorem magneticForm_zero_charge {A : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap 0 A) z v)
        (fderiv ℝ (kineticMomentumMap 0 A) z w) =
      strongDualCotangentSymplecticForm v w := by
  rw [canonicalForm_fderiv_kineticMomentumMap_flux 0 hA]
  simp

/-- **Content check**: for `q ≠ 0` and `B₀ ≠ 0` the kinetic momentum map of the Landau gauge
does not preserve the canonical form at any point: the magnetic term is not zero. -/
theorem landau_not_symplectic {q B₀ : ℝ} (hq : q ≠ 0) (hB : B₀ ≠ 0) (z : PhaseSpace) :
    ¬ ∀ v w : PhaseSpace,
      strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap q (landau B₀)) z v)
          (fderiv ℝ (kineticMomentumMap q (landau B₀)) z w) =
        strongDualCotangentSymplecticForm v w := by
  intro h
  have h1 := h (coordVec 0, 0) (coordVec 1, 0)
  rw [landau_magneticForm] at h1
  have h2 : q * B₀ = 0 := by simpa using h1
  exact mul_ne_zero hq hB h2

/-- **Accepted fixture**: every Lorentz orbit in the uniform field `B₀ e_z` gives an integral
curve of the Hamiltonian vector field of the Landau-gauge Hamiltonian. -/
theorem landau_hamilton {m q B₀ : ℝ} (hm : m ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (fun _ => B₀ • coordVec 2) x v) (t : ℝ) :
    HasDerivAt (canonicalCurve m q (landau B₀) x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (magneticHamiltonian m q (landau B₀)) (canonicalCurve m q (landau B₀) x v t)) t :=
  lorentzOrbit_hamilton hm h (landau B₀).differentiable (fun y => (curl_landau B₀ y).symm) t

/-- The uniform field of `Theory/Kinetic/FullOrbit` is `B₀ e_z`. -/
theorem uniformField_eq (B₀ : ℝ) : uniformField B₀ = fun _ => B₀ • coordVec 2 := by
  funext y
  ext i
  fin_cases i <;> simp [uniformField]

/-- **Accepted fixture**: the explicit helix satisfies Hamilton's equations, so the hypotheses
of `lorentzOrbit_hamilton` are satisfiable. -/
theorem helix_hamilton {m q B₀ : ℝ} (hm : m ≠ 0) (hω : q * B₀ / m ≠ 0) (X : Space) (u w t : ℝ) :
    HasDerivAt (canonicalCurve m q (landau B₀) (helixPosition X u w (q * B₀ / m))
        (helixVelocity u w (q * B₀ / m)))
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (magneticHamiltonian m q (landau B₀))
        (canonicalCurve m q (landau B₀) (helixPosition X u w (q * B₀ / m))
          (helixVelocity u w (q * B₀ / m)) t)) t := by
  have h := helix_orbit hm hω X u w
  rw [uniformField_eq] at h
  exact landau_hamilton hm h t

/-- **Accepted fixture**: on the helix the Hamiltonian is the kinetic energy
`(m/2)(u² + w²)`. -/
theorem helix_energy {m : ℝ} (hm : m ≠ 0) (q B₀ : ℝ) (X : Space) (u w ω' t : ℝ) :
    magneticHamiltonian m q (landau B₀)
        (canonicalCurve m q (landau B₀) (helixPosition X u w ω') (helixVelocity u w ω') t) =
      m / 2 * (u ^ 2 + w ^ 2) := by
  rw [magneticHamiltonian_canonicalCurve hm, helix_speed]

end PlasmaLean.Sanity.MagneticSymplectic
