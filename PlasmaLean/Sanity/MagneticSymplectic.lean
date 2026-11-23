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
  `landau_magneticForm`: the kinetic momentum map `Ψ` (canonical to kinetic momenta) satisfies
  `Ψ^*Ω = Ω + q B₀ dx ∧ dy`. This is a form on the space of canonical momenta; it is not the
  magnetic symplectic form, which is `Ω − q B₀ dx ∧ dy` on the space of kinetic momenta.
* Regression (audit AV-H1), the sign of the magnetic form: `landau_inverse_magneticForm` (the
  inverse map pulls `Ω` back to `Ω − q B₀ dx ∧ dy`), `landau_magneticForm_symplectic` (`Ψ`
  pulls `Ω − q B₀ dx ∧ dy` back to `Ω`), `uniform_magneticForm_lorentzForceField` (accepted:
  with `− q` the free Hamiltonian generates the Lorentz force in the uniform field),
  `uniform_plus_sign_fails` (rejected: with `+ q` it does not, for `m, q, B₀ ≠ 0`), and
  `helix_kineticCurve` (the explicit helix is an integral curve of the Lorentz-force field).
* Accepted: `landau_hamilton`: every Lorentz orbit in the uniform field gives an integral
  curve of the Hamiltonian vector field of `magneticHamiltonian`; `helix_hamilton` applies it
  to the explicit helix of `Theory/Kinetic/FullOrbit`, so the hypothesis is satisfiable, and
  `helix_energy` evaluates the Hamiltonian there as `(m/2)(u² + w²)`.
* Content checks: `magneticForm_zero_charge`: for `q = 0` the magnetic term vanishes and the
  canonical form is preserved; `landau_not_symplectic`: for `q ≠ 0` and `B₀ ≠ 0` the kinetic
  momentum map does not preserve the canonical form, so the magnetic term cannot be dropped.
  This check does not see the sign of the magnetic term; `uniform_plus_sign_fails` does.
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

/-- **Accepted fixture**: for the uniform field the kinetic momentum map `Ψ`, from canonical
to kinetic momenta, satisfies `Ω(DΨ v, DΨ w) = Ω(v, w) + q B₀ (dx ∧ dy)(v, w)`, that is
`Ψ^*Ω = Ω + q B₀ dx ∧ dy`. This is not the magnetic symplectic form: that form is
`Ω − q B₀ dx ∧ dy` on the space of kinetic momenta (`landau_magneticForm_symplectic`,
`uniform_magneticForm_lorentzForceField`). -/
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
does not preserve the canonical form at any point: the magnetic term is not zero. This check
cannot detect the sign of the magnetic term (it holds equally with `−q` in place of `q`); the
sign is tested by `uniform_magneticForm_lorentzForceField` and `uniform_plus_sign_fails`. -/
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

/-! ### Regression (audit AV-H1): the sign and direction of the magnetic form -/

/-- Regression (audit AV-H1): the inverse map `(x, π) ↦ (x, π + q A(x)♭)`, from kinetic to
canonical momenta, pulls the canonical form back to `Ω − q B₀ dx ∧ dy` in the uniform field:
the minus sign of the magnetic form. -/
theorem landau_inverse_magneticForm (q B₀ : ℝ) (z v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap (-q) (landau B₀)) z v)
        (fderiv ℝ (kineticMomentumMap (-q) (landau B₀)) z w) =
      strongDualCotangentSymplecticForm v w -
        q * B₀ * (v.1 0 * w.1 1 - v.1 1 * w.1 0) := by
  rw [canonicalForm_fderiv_kineticMomentumMap_neg_flux q (landau B₀).differentiableAt,
    curl_landau, map_smul, ContinuousAlternatingMap.smul_apply, flux_coordVec_two, smul_eq_mul]
  ring

/-- Regression (audit AV-H1): the kinetic momentum map of the Landau gauge pulls the magnetic
form `Ω − q π^*ω_B` of the uniform field back to the canonical form. -/
theorem landau_magneticForm_symplectic (q B₀ : ℝ) (z v w : PhaseSpace) :
    magneticForm q (fun _ => B₀ • coordVec 2) (kineticMomentumMap q (landau B₀) z)
        (fderiv ℝ (kineticMomentumMap q (landau B₀)) z v)
        (fderiv ℝ (kineticMomentumMap q (landau B₀)) z w) =
      strongDualCotangentSymplecticForm v w :=
  magneticForm_fderiv_kineticMomentumMap q (landau B₀).differentiableAt
    (curl_landau B₀ z.1).symm v w

/-- Regression (audit AV-H1), accepted: in the uniform field `B₀ e_z`, with the form
`Ω − q B₀ dx ∧ dy`, the Lorentz-force field `X = (π♯/m, (q/m) (π♯ × B)♭)` satisfies
`ι_X Ω_mag = dH` for the free Hamiltonian `H = ‖π‖² / (2m)`. -/
theorem uniform_magneticForm_lorentzForceField (m q B₀ : ℝ) (z w : PhaseSpace) :
    strongDualCotangentSymplecticForm
          (lorentzForceField m q (fun _ => B₀ • coordVec 2) z) w -
        q * B₀ * ((lorentzForceField m q (fun _ => B₀ • coordVec 2) z).1 0 * w.1 1 -
          (lorentzForceField m q (fun _ => B₀ • coordVec 2) z).1 1 * w.1 0) =
      fderiv ℝ (freeParticleHamiltonian m) z w := by
  rw [← magneticForm_lorentzForceField m q (fun _ => B₀ • coordVec 2) z w, magneticForm,
    map_smul, ContinuousAlternatingMap.smul_apply, flux_coordVec_two, smul_eq_mul]
  ring

/-- Regression (audit AV-H1), rejected: with `+ q` in place of `− q` in the magnetic form the
same identity fails in the uniform field `B₀ e_z` when `m, q, B₀ ≠ 0`. It fails at the
kinetic momentum `π = e_x♭` (any position) on the tangent vector `w = (e_y, 0)`: the left-hand
side exceeds the right-hand side by `2 q B₀ / m`. So the form `Ω + q π^*ω_B` is not the
magnetic symplectic form in the convention `ι_X Ω = dH`. -/
theorem uniform_plus_sign_fails {m q B₀ : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) (hB : B₀ ≠ 0) :
    ¬ ∀ z w : PhaseSpace,
      strongDualCotangentSymplecticForm
            (lorentzForceField m q (fun _ => B₀ • coordVec 2) z) w +
          q * B₀ * ((lorentzForceField m q (fun _ => B₀ • coordVec 2) z).1 0 * w.1 1 -
            (lorentzForceField m q (fun _ => B₀ • coordVec 2) z).1 1 * w.1 0) =
        fderiv ℝ (freeParticleHamiltonian m) z w := by
  intro h
  have h1 := h (0, innerSL ℝ (coordVec 0)) (coordVec 1, 0)
  have h2 := uniform_magneticForm_lorentzForceField m q B₀ (0, innerSL ℝ (coordVec 0))
    (coordVec 1, 0)
  have h3 : q * B₀ * ((lorentzForceField m q (fun _ => B₀ • coordVec 2)
        (0, innerSL ℝ (coordVec 0))).1 0 * (coordVec 1 : Space) 1 -
      (lorentzForceField m q (fun _ => B₀ • coordVec 2)
        (0, innerSL ℝ (coordVec 0))).1 1 * (coordVec 1 : Space) 0) = 0 := by
    linarith
  have h4 : q * B₀ * m⁻¹ = 0 := by
    simpa [lorentzForceField, toDual_symm_innerSL] using h3
  exact mul_ne_zero (mul_ne_zero hq hB) (inv_ne_zero hm) h4

/-- Regression (audit AV-H1): the explicit helix of `Theory/Kinetic/FullOrbit`, with its
kinetic momentum, is an integral curve of the Lorentz-force field of the uniform field; so the
field that `uniform_magneticForm_lorentzForceField` identifies as Hamiltonian for
`Ω − q π^*ω_B` has the gyrating orbits as integral curves. -/
theorem helix_kineticCurve {m q B₀ : ℝ} (hm : m ≠ 0) (hω : q * B₀ / m ≠ 0) (X : Space)
    (u w t : ℝ) :
    HasDerivAt (kineticCurve m (helixPosition X u w (q * B₀ / m))
        (helixVelocity u w (q * B₀ / m)))
      (lorentzForceField m q (uniformField B₀)
        (kineticCurve m (helixPosition X u w (q * B₀ / m))
          (helixVelocity u w (q * B₀ / m)) t)) t :=
  lorentzOrbit_kineticCurve hm (helix_orbit hm hω X u w) t

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
