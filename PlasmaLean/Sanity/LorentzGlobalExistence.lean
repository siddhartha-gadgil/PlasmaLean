/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.LorentzGlobalExistence

/-!
# Sanity checks for `Theory/Kinetic/LorentzGlobalExistence`

Fields used: the confining potential `harmonicPotential y = ‖y‖² / 2` with
`harmonicField y = −y`; the sheared magnetic field `shearField y = y₀ e_z` with vector potential
`shearGauge y = (y₀² / 2) e_y`; the quartic potential `quarticPotential σ y = σ y₀⁴ / 4` with
`quarticField σ y = −σ y₀³ e_x`.

* Accepted (linear growth): `harmonic_shear_orbit_existsUnique`: for `m ≠ 0` and every `q`
  there is exactly one Lorentz orbit for all times in `E = −y`, `B = y₀ e_z` from every initial
  position and velocity. Neither earlier global theorem applies: the electric field is not
  zero (`lorentzOrbit_exists`), and the magnetic field is not uniform
  (`shearField_not_uniform`), whereas `lorentzOrbit_existsUnique_linearGauge` needs
  `B = ∇ × L` with `L` linear, which is uniform.
* Accepted (energy bound): `harmonic_shear_orbit_existsUnique_of_energy`: the same conclusion
  for `0 < m`, `0 ≤ q` from the potential bounded below. `quartic_orbit_existsUnique`: for
  `0 < m`, `0 ≤ q σ` and ANY `C¹` magnetic field, a unique global orbit in the quartic well;
  for `σ ≠ 0` this electric field is not of linear growth (`quarticField_not_linear_growth`),
  so here only the energy theorem applies.
* The two hypotheses are independent: `harmonic_not_bounded_below`: for `q < 0` the potential
  energy `q ‖y‖² / 2` is not bounded below, so for `0 < m` the energy theorem does not apply
  to the field `E = −y`, while the linear-growth theorem does.
* Accepted (Hamiltonian): `fieldCurl_shearGauge`: `∇ × shearGauge = shearField`.
  `harmonic_shear_hamilton_existsUnique`: for `m ≠ 0`, a unique integral curve for all times of
  the Hamiltonian vector field of `emHamiltonian m q shearGauge harmonicPotential` through
  every point of phase space. `shearGauge` is quadratic, so `emHamilton_exists_global` (linear
  vector potential) does not apply.
* Rejected (hypotheses fail): the repulsive quartic field `E = y₀³ e_x`
  (`quarticField_neg_one`), potential `−y₀⁴ / 4`. For `q σ < 0` the potential energy is not
  bounded below (`quartic_not_bounded_below`), and for `σ ≠ 0` the field is not of linear growth
  (`quarticField_not_linear_growth`), so neither theorem applies. With `B = 0`, `m = q = 1`
  the equation of motion is `x'' = x³`, whose solutions with large initial data blow up in
  finite time; that blow-up is NOT proved here. What is proved is only that this field
  violates each hypothesis.
-/

@[expose] public section

namespace PlasmaLean.Sanity.LorentzGlobalExistence

open PlasmaLean PlasmaLean.Kinetic PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti WithLp
open scoped RealInnerProductSpace

/-- The confining potential `‖y‖² / 2`. -/
noncomputable def harmonicPotential (y : Space) : ℝ := ‖y‖ ^ 2 / 2

/-- The electric field `−y` of the confining potential. -/
def harmonicField (y : Space) : Space := -y

/-- The sheared magnetic field `y₀ e_z`. -/
noncomputable def shearField (y : Space) : Space := y 0 • coordVec 2

/-- A vector potential `(y₀² / 2) e_y` of the sheared field. -/
noncomputable def shearGauge (y : Space) : Space := (y 0 ^ 2 / 2) • coordVec 1

/-- The quartic potential `σ y₀⁴ / 4` (a well for `σ > 0`, a hill for `σ < 0`). -/
noncomputable def quarticPotential (σ : ℝ) (y : Space) : ℝ := σ * y 0 ^ 4 / 4

/-- The electric field `−σ y₀³ e_x` of the quartic potential. -/
noncomputable def quarticField (σ : ℝ) (y : Space) : Space := (-(σ * y 0 ^ 3)) • coordVec 0

/-- The Cartesian unit vector `e_x` has norm `1`. -/
theorem norm_coordVec_zero : ‖(coordVec 0 : Space)‖ = 1 := by
  simp [coordVec]

/-- The first coordinate, as a continuous linear map, has itself as derivative. -/
theorem hasFDerivAt_coord_zero (y : Space) :
    HasFDerivAt (fun z : Space => z 0) (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0) y :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).hasFDerivAt

/-- `−y = −∇(‖y‖² / 2)`. -/
theorem isPotential_harmonic : IsPotential harmonicPotential harmonicField := by
  intro y
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext z
    simp only [harmonicPotential]
    ring
  · ext w
    simp [harmonicField]

/-- `−σ y₀³ e_x = −∇(σ y₀⁴ / 4)`. -/
theorem isPotential_quartic (σ : ℝ) : IsPotential (quarticPotential σ) (quarticField σ) := by
  intro y
  have h := ((hasFDerivAt_coord_zero y).pow 4).const_mul (σ / 4)
  convert h using 1
  · funext z
    simp only [quarticPotential]
    ring
  · ext w
    simp [quarticField, inner_coords3]
    ring

/-- The field `−y` is `C¹` (it is linear). -/
theorem contDiff_harmonicField : ContDiff ℝ 1 harmonicField :=
  contDiff_id.neg

/-- The sheared field is `C¹`. -/
theorem contDiff_shearField : ContDiff ℝ 1 shearField :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff.smul contDiff_const

/-- The quadratic vector potential is `C²`. -/
theorem contDiff_shearGauge : ContDiff ℝ 2 shearGauge :=
  (((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff.pow 2).div_const 2).smul
    contDiff_const

/-- The quartic field is `C¹`. -/
theorem contDiff_quarticField (σ : ℝ) : ContDiff ℝ 1 (quarticField σ) :=
  ((contDiff_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff.pow 3)).neg).smul
    contDiff_const

/-- The electric field `−y` has linear growth: `‖−y‖ ≤ 0 + 1 ‖y‖`. -/
theorem harmonicField_linear_growth (y : Space) : ‖harmonicField y‖ ≤ 0 + 1 * ‖y‖ := by
  simp [harmonicField]

/-- The sheared field is not uniform: it vanishes at the origin and not at `e_x`. -/
theorem shearField_not_uniform (Bv : Space) : shearField ≠ fun _ => Bv := by
  intro h
  have h0 := congrArg (fun z : Space => z 2) (congrFun h 0)
  have h1 := congrArg (fun z : Space => z 2) (congrFun h (coordVec 0))
  simp only [shearField] at h0 h1
  rw [← h0] at h1
  simp at h1

/-- **Accepted fixture** (linear growth): in the non-uniform fields `E = −y`, `B = y₀ e_z`, for
`m ≠ 0` and every charge, there is exactly one Lorentz orbit for all times from every initial
position and velocity. -/
theorem harmonic_shear_orbit_existsUnique {m : ℝ} (hm : m ≠ 0) (q : ℝ) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q harmonicField shearField x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q harmonicField shearField x' v' → x' 0 = x₀ →
        v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_linear_growth hm contDiff_harmonicField contDiff_shearField
    harmonicField_linear_growth x₀ v₀

/-- **Accepted fixture** (energy bound): the same conclusion for `0 < m`, `0 ≤ q`, from the
potential energy `q ‖y‖² / 2 ≥ 0`. -/
theorem harmonic_shear_orbit_existsUnique_of_energy {m q : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q harmonicField shearField x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q harmonicField shearField x' v' → x' 0 = x₀ →
        v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_potential_bounded_below hm contDiff_harmonicField
    contDiff_shearField isPotential_harmonic (c := 0)
    (fun y => mul_nonneg hq (by unfold harmonicPotential; positivity)) x₀ v₀

/-- **Accepted fixture** (energy bound, no linear growth): in the quartic well
`Φ = σ y₀⁴ / 4` with `0 ≤ q σ`, `0 < m`, and ANY `C¹` magnetic field, there is exactly one
Lorentz orbit for all times from every initial position and velocity. -/
theorem quartic_orbit_existsUnique {m q σ : ℝ} (hm : 0 < m) (hqσ : 0 ≤ q * σ)
    {B : Space → Space} (hB : ContDiff ℝ 1 B) (x₀ v₀ : Space) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (quarticField σ) B x v ∧ x 0 = x₀ ∧ v 0 = v₀ ∧
      ∀ x' v' : ℝ → Space, LorentzOrbit m q (quarticField σ) B x' v' → x' 0 = x₀ →
        v' 0 = v₀ → x' = x ∧ v' = v :=
  lorentzOrbit_existsUnique_of_potential_bounded_below hm (contDiff_quarticField σ) hB
    (isPotential_quartic σ) (c := 0)
    (fun y => by
      have h4 : 0 ≤ y 0 ^ 4 := by positivity
      have : q * quarticPotential σ y = q * σ * (y 0 ^ 4 / 4) := by
        simp only [quarticPotential]
        ring
      rw [this]
      positivity) x₀ v₀

/-- **Hypothesis check**: for `σ ≠ 0` the quartic field is not of linear growth, for any
constants `a`, `b`. -/
theorem quarticField_not_linear_growth {σ : ℝ} (hσ : σ ≠ 0) (a b : ℝ) :
    ¬ ∀ y, ‖quarticField σ y‖ ≤ a + b * ‖y‖ := by
  intro h
  have hτ : 0 < |σ| := abs_pos.mpr hσ
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + (|a| + |b|) / |σ| := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    rw [hs]
    have : 0 ≤ (|a| + |b|) / |σ| := by positivity
    linarith
  have hab : |a| + |b| = |σ| * (s - 1) := by
    rw [hs]
    field_simp
    ring
  have hy := h (s • coordVec 0)
  have hn : ‖(s • coordVec 0 : Space)‖ = s := by
    rw [norm_smul, norm_coordVec_zero, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hE : ‖quarticField σ (s • coordVec 0)‖ = |σ| * s ^ 3 := by
    have h0 : (s • coordVec 0 : Space) 0 = s := by simp
    rw [quarticField, norm_smul, norm_coordVec_zero, mul_one, h0, Real.norm_eq_abs, abs_neg,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 3)]
  rw [hn, hE] at hy
  have h1 : a + b * s ≤ (|a| + |b|) * s := by
    nlinarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  rw [hab] at h1
  have h2 : s ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s]
  nlinarith [mul_pos hτ (by linarith : (0 : ℝ) < s)]

/-- **Hypothesis check**: for `q σ < 0` the potential energy `q σ y₀⁴ / 4` is not bounded
below. -/
theorem quartic_not_bounded_below {q σ : ℝ} (hqσ : q * σ < 0) :
    ¬ ∃ c : ℝ, ∀ y, c ≤ q * quarticPotential σ y := by
  rintro ⟨c, h⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + 4 * |c| / (-(q * σ)) := ⟨_, rfl⟩
  have hκ : 0 < -(q * σ) := by linarith
  have hs1 : 1 ≤ s := by
    rw [hs]
    have : 0 ≤ 4 * |c| / (-(q * σ)) := by positivity
    linarith
  have hq0 : q ≠ 0 := fun h0 => by simp [h0] at hqσ
  have hσ0 : σ ≠ 0 := fun h0 => by simp [h0] at hqσ
  have hc : 4 * |c| = -(q * σ) * (s - 1) := by
    rw [hs]
    field_simp
    ring
  have hy := h (s • coordVec 0)
  have h0 : (s • coordVec 0 : Space) 0 = s := by simp
  rw [quarticPotential, h0] at hy
  have h4 : s ≤ s ^ 4 := le_self_pow₀ hs1 (by norm_num)
  have hκs : -(q * σ) * s ≤ -(q * σ) * s ^ 4 := mul_le_mul_of_nonneg_left h4 hκ.le
  nlinarith [neg_abs_le c]

/-- **Independence of the two hypotheses**: for `q < 0` the potential energy `q ‖y‖² / 2` of
the field `E = −y` is not bounded below, although `E` has linear growth. -/
theorem harmonic_not_bounded_below {q : ℝ} (hq : q < 0) :
    ¬ ∃ c : ℝ, ∀ y, c ≤ q * harmonicPotential y := by
  rintro ⟨c, h⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 + 2 * |c| / (-q) := ⟨_, rfl⟩
  have hκ : 0 < -q := by linarith
  have hs1 : 1 ≤ s := by
    rw [hs]
    have : 0 ≤ 2 * |c| / (-q) := by positivity
    linarith
  have hq0 : q ≠ 0 := hq.ne
  have hc : 2 * |c| = -q * (s - 1) := by
    rw [hs]
    field_simp
    ring
  have hy := h (s • coordVec 0)
  have hn : ‖(s • coordVec 0 : Space)‖ = s := by
    rw [norm_smul, norm_coordVec_zero, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [harmonicPotential, hn] at hy
  have h2 : s ≤ s ^ 2 := by nlinarith
  have hκs : -q * s ≤ -q * s ^ 2 := mul_le_mul_of_nonneg_left h2 hκ.le
  nlinarith [neg_abs_le c]

/-- The repulsive quartic field (`σ = −1`) is `E = y₀³ e_x`. -/
theorem quarticField_neg_one (y : Space) : quarticField (-1) y = y 0 ^ 3 • coordVec 0 := by
  simp [quarticField]

/-- **Rejected fixture**: for `0 < q` the field `E = y₀³ e_x` satisfies neither hypothesis of
the global existence theorems: its potential energy is not bounded below and it is not of
linear growth. (Finite-time blow-up of its orbits is not proved.) -/
theorem repulsive_quartic_rejected {q : ℝ} (hq : 0 < q) (a b : ℝ) :
    (¬ ∃ c : ℝ, ∀ y, c ≤ q * quarticPotential (-1) y) ∧
      ¬ ∀ y, ‖quarticField (-1) y‖ ≤ a + b * ‖y‖ :=
  ⟨quartic_not_bounded_below (by linarith),
    quarticField_not_linear_growth (by norm_num) a b⟩

/-- `∇ × ((y₀² / 2) e_y) = y₀ e_z`. -/
theorem fieldCurl_shearGauge (y : Space) : fieldCurl shearGauge y = shearField y := by
  have h : HasFDerivAt shearGauge
      ((y 0 • EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).smulRight (coordVec 1)) y := by
    have h1 := (((hasFDerivAt_coord_zero y).pow 2).const_mul (1 / 2 : ℝ)).smul_const
      (coordVec 1 : Space)
    convert h1 using 1
    · funext z
      simp only [shearGauge]
      congr 1
      ring
    · ext w i
      simp
      split_ifs <;> ring
  rw [fieldCurl, h.fderiv]
  ext i
  fin_cases i <;> simp [curlOp, shearField]

/-- **Accepted fixture** (Hamiltonian formulation): for `m ≠ 0`, through every point of phase
space there is exactly one integral curve for all times of the Hamiltonian vector field of
`emHamiltonian m q shearGauge harmonicPotential`. The vector potential is quadratic. -/
theorem harmonic_shear_hamilton_existsUnique {m : ℝ} (hm : m ≠ 0) (q : ℝ) (z₀ : PhaseSpace) :
    ∃ z : ℝ → PhaseSpace, z 0 = z₀ ∧
      (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q shearGauge harmonicPotential) (z t)) t) ∧
      ∀ z' : ℝ → PhaseSpace, z' 0 = z₀ →
        (∀ t, HasDerivAt z'
          ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
            (emHamiltonian m q shearGauge harmonicPotential) (z' t)) t) → z' = z :=
  emHamilton_existsUnique_of_linear_growth hm contDiff_shearGauge contDiff_harmonicField
    isPotential_harmonic harmonicField_linear_growth z₀

end PlasmaLean.Sanity.LorentzGlobalExistence
