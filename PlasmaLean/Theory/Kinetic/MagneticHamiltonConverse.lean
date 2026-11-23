/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MagneticSymplectic

/-!
# Hamilton's equations and the Lorentz equations are equivalent

`Theory/Kinetic/MagneticSymplectic` proves that a Lorentz orbit with no electric field, lifted
with its canonical momentum, is an integral curve of the Hamiltonian vector field of
`magneticHamiltonian`. This file adds an electrostatic field and proves the converse.

* `emHamiltonian m q A Φ`: `H(x, p) = ‖p♯ − q A(x)‖² / (2m) + q Φ(x)`; for `Φ = 0` it is
  `magneticHamiltonian` (`emHamiltonian_zero`).
* `kineticVelocity m q A z`: the velocity `(p♯ − q A(x)) / m` of a phase-space point.
* `hamiltonianVectorField_emHamiltonian`: Hamilton's equations in closed form. Where `A` is
  differentiable and `E = −∇Φ` (`IsPotential Φ E`), the Hamiltonian vector field of `H` at
  `z = (x, p)` is `(v, q (DA)ᵀ v + q E(x)♭)` with `v = kineticVelocity m q A z`; no hypothesis
  on `m`.
* `lorentzOrbit_emHamilton` (forward): for `m ≠ 0`, `A` differentiable, `B = ∇ × A` and
  `E = −∇Φ`, the canonical lift of a Lorentz orbit is an integral curve of the Hamiltonian
  vector field. `lorentzOrbit_hamilton_of_emHamilton` recovers `lorentzOrbit_hamilton` from it
  at `Φ = 0`.
* `lorentzOrbit_of_emHamilton` (converse): under the same hypotheses on the fields, every
  integral curve `z` of the Hamiltonian vector field gives a Lorentz orbit with position
  `(z t).1` and velocity `kineticVelocity m q A (z t)`, and `z` is the canonical lift of that
  orbit (`canonicalCurve_of_emHamilton`). Only differentiability of `A` is used: the velocity
  is differentiable because `p` and `x` are, and `A` is differentiable along `x`.
* `lorentzOrbit_iff_emHamilton`, `emHamilton_iff_exists_lorentzOrbit`: the two equivalences.
* `emHamiltonian_canonicalCurve`: on the canonical lift, `H` is `orbitEnergy`, that is
  `(m/2)‖v‖² + q Φ(x)`. `emHamiltonian_conserved`: `H` is constant along integral curves, from
  TauCeti's `apply_eq_of_hasDerivWithinAt_hamiltonianVectorField`.
  `orbitEnergy_conserved_of_emHamilton`: so the energy of the orbit read off from an integral
  curve is constant. For Lorentz orbits themselves, conservation of `orbitEnergy` is
  `energy_conserved` of `Theory/Kinetic/FullOrbit`, which needs neither a vector potential nor
  `m ≠ 0`; it is not restated here.

Not proved here: time-dependent potentials. Existence and uniqueness of integral curves, and
curves defined only on an interval of times (`LorentzOrbitOn`), are in
`Theory/Kinetic/CrossedFieldOrbit`.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti InnerProductSpace
open scoped RealInnerProductSpace

/-- The Hamiltonian of a particle of mass `m` and charge `q` in the vector potential `A` and
the scalar potential `Φ`: `H(x, p) = ‖p♯ − q A(x)‖² / (2m) + q Φ(x)`. -/
noncomputable def emHamiltonian (m q : ℝ) (A : Space → Space) (Φ : Space → ℝ)
    (z : PhaseSpace) : ℝ :=
  magneticHamiltonian m q A z + q * Φ z.1

/-- With zero scalar potential the Hamiltonian is `magneticHamiltonian`. -/
theorem emHamiltonian_zero (m q : ℝ) (A : Space → Space) :
    emHamiltonian m q A (fun _ => 0) = magneticHamiltonian m q A := by
  funext z
  simp [emHamiltonian]

/-- The velocity of a phase-space point: `v = (p♯ − q A(x)) / m`. -/
noncomputable def kineticVelocity (m q : ℝ) (A : Space → Space) (z : PhaseSpace) : Space :=
  m⁻¹ • ((toDual ℝ Space).symm z.2 - q • A z.1)

/-- On the canonical lift of a trajectory the velocity is the velocity of the trajectory
(for `m ≠ 0`). -/
theorem kineticVelocity_canonicalCurve {m : ℝ} (hm : m ≠ 0) (q : ℝ) (A : Space → Space)
    (x v : ℝ → Space) (t : ℝ) :
    kineticVelocity m q A (canonicalCurve m q A x v t) = v t := by
  change m⁻¹ • ((toDual ℝ Space).symm (canonicalCovector m q A x v t) - q • A (x t)) = v t
  rw [toDual_symm_canonicalCovector_sub, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- The magnetic Hamiltonian is differentiable at every point over which `A` is. -/
theorem differentiableAt_magneticHamiltonian (m q : ℝ) {A : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) : DifferentiableAt ℝ (magneticHamiltonian m q A) z :=
  ((hasFDerivAt_freeParticleHamiltonian m (kineticMomentumMap q A z)).comp z
    (hasFDerivAt_cotangentFiberTranslate
      (differentiableAt_potentialForm q hA)).differentiableAt.hasFDerivAt).differentiableAt

/-- The potential energy `z ↦ q Φ(x)` on phase space has derivative `(δx, δp) ↦ −q⟪E, δx⟫`
when `E = −∇Φ`. -/
theorem hasFDerivAt_potentialEnergy (q : ℝ) {Φ : Space → ℝ} {E : Space → Space}
    (hΦ : IsPotential Φ E) (z : PhaseSpace) :
    HasFDerivAt (fun z : PhaseSpace => q * Φ z.1)
      (q • (-(innerSL ℝ (E z.1))).comp (ContinuousLinearMap.fst ℝ Space (StrongDual ℝ Space)))
      z :=
  ((hΦ z.1).comp z (ContinuousLinearMap.fst ℝ Space (StrongDual ℝ Space)).hasFDerivAt).const_mul
    q

/-- The Hamiltonian is differentiable at every point over which `A` is, when `E = −∇Φ`. -/
theorem differentiableAt_emHamiltonian (m q : ℝ) {A : Space → Space} {Φ : Space → ℝ}
    {E : Space → Space} (hΦ : IsPotential Φ E) {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) : DifferentiableAt ℝ (emHamiltonian m q A Φ) z :=
  (differentiableAt_magneticHamiltonian m q hA).add
    (hasFDerivAt_potentialEnergy q hΦ z).differentiableAt

/-- **The derivative of the Hamiltonian.** With `v = (p♯ − q A(x)) / m`,
`dH(δx, δp) = δp(v) − q⟪DA δx, v⟫ − q⟪E, δx⟫`. -/
theorem fderiv_emHamiltonian_apply (m q : ℝ) {A : Space → Space} {Φ : Space → ℝ}
    {E : Space → Space} (hΦ : IsPotential Φ E) {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (w : PhaseSpace) :
    fderiv ℝ (emHamiltonian m q A Φ) z w =
      w.2 (kineticVelocity m q A z) - q * ⟪fderiv ℝ A z.1 w.1, kineticVelocity m q A z⟫ -
        q * ⟪E z.1, w.1⟫ := by
  have h := (differentiableAt_magneticHamiltonian m q hA).hasFDerivAt.add
    (hasFDerivAt_potentialEnergy q hΦ z)
  have e : fderiv ℝ (emHamiltonian m q A Φ) z = _ := h.fderiv
  rw [e, _root_.add_apply, fderiv_magneticHamiltonian_apply m q hA]
  simp only [kineticVelocity, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', _root_.neg_apply, innerSL_apply_apply, smul_eq_mul, map_smul,
    inner_smul_right]
  ring

/-- **Hamilton's equations in closed form.** Where `A` is differentiable and `E = −∇Φ`, the
Hamiltonian vector field of `emHamiltonian` at `z = (x, p)` is `x' = v`,
`p' = q (DA)ᵀ v + q E(x)♭`, with `v = (p♯ − q A(x)) / m`. No hypothesis on `m`. -/
theorem hamiltonianVectorField_emHamiltonian (m q : ℝ) {A : Space → Space} {Φ : Space → ℝ}
    {E : Space → Space} (hΦ : IsPotential Φ E) {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) :
    (strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) z =
      (kineticVelocity m q A z,
        q • (innerSL ℝ (kineticVelocity m q A z)).comp (fderiv ℝ A z.1) +
          q • innerSL ℝ (E z.1)) := by
  symm
  rw [SymplecticForm.eq_hamiltonianVectorField_iff]
  intro w
  rw [fderiv_emHamiltonian_apply m q hΦ hA]
  simp only [strongDualCotangentSymplecticForm_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm (fderiv ℝ A z.1 w.1)]
  ring

/-- **Hamilton's equations for a Lorentz orbit with an electric field.** Let `m ≠ 0`, `A` be
differentiable, `B = ∇ × A` and `E = −∇Φ`. Along a Lorentz orbit `x' = v`,
`m v' = q (E + v × B)`, the curve `t ↦ (x t, m (v t)♭ + q A(x t)♭)` is an integral curve of
the Hamiltonian vector field of `emHamiltonian m q A Φ` for the canonical symplectic form. -/
theorem lorentzOrbit_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} {x v : ℝ → Space} (h : LorentzOrbit m q E B x v)
    (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y) (hΦ : IsPotential Φ E)
    (t : ℝ) :
    HasDerivAt (canonicalCurve m q A x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (canonicalCurve m q A x v t)) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t
  have hx := h.position t
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

/-- `lorentzOrbit_hamilton` is the case `Φ = 0` of `lorentzOrbit_emHamilton`. -/
theorem lorentzOrbit_hamilton_of_emHamilton {m q : ℝ} (hm : m ≠ 0) {A B : Space → Space}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (t : ℝ) :
    HasDerivAt (canonicalCurve m q A x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (magneticHamiltonian m q A) (canonicalCurve m q A x v t)) t := by
  have key := lorentzOrbit_emHamilton hm h hA hcurl (constant_potential 0) t
  rwa [emHamiltonian_zero] at key

/-- **Converse: integral curves are Lorentz orbits.** Let `m ≠ 0`, `A` be differentiable,
`B = ∇ × A` and `E = −∇Φ`. If `z` is an integral curve of the Hamiltonian vector field of
`emHamiltonian m q A Φ`, then its position `x t = (z t).1` and its velocity
`v t = (p♯ − q A(x)) / m` satisfy `x' = v` and `m v' = q (E + v × B)`. -/
theorem lorentzOrbit_of_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} {z : ℝ → PhaseSpace} (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (hΦ : IsPotential Φ E)
    (hz : ∀ t, HasDerivAt z
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z t)) t) :
    LorentzOrbit m q E B (fun t => (z t).1) (fun t => kineticVelocity m q A (z t)) := by
  have hz' (t : ℝ) := hamiltonianVectorField_emHamiltonian m q hΦ (hA (z t).1) ▸ hz t
  have hx (t : ℝ) : HasDerivAt (fun s => (z s).1) (kineticVelocity m q A (z t)) t :=
    (ContinuousLinearMap.fst ℝ Space (StrongDual ℝ Space)).hasFDerivAt.comp_hasDerivAt t (hz' t)
  refine ⟨hx, fun t => ?_⟩
  set P : StrongDual ℝ Space := q • (innerSL ℝ (kineticVelocity m q A (z t))).comp
    (fderiv ℝ A (z t).1) + q • innerSL ℝ (E (z t).1) with hP
  have hp : HasDerivAt (fun s => (z s).2) P t :=
    (ContinuousLinearMap.snd ℝ Space (StrongDual ℝ Space)).hasFDerivAt.comp_hasDerivAt t (hz' t)
  have hp' : HasDerivAt (fun s => (toDual ℝ Space).symm (z s).2)
      ((toDual ℝ Space).symm P) t := by
    have h := (toDualSymmL (F := Space)).hasFDerivAt.comp_hasDerivAt t hp
    simp only [Function.comp_def, toDualSymmL_apply] at h
    exact h
  have hAx : HasDerivAt (fun s => A (z s).1)
      (fderiv ℝ A (z t).1 (kineticVelocity m q A (z t))) t :=
    (hA (z t).1).hasFDerivAt.comp_hasDerivAt t (hx t)
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

/-- Every phase-space curve is the canonical lift of its own position and velocity (for
`m ≠ 0`): `p = m v♭ + q A(x)♭` with `v = (p♯ − q A(x)) / m`. -/
theorem canonicalCurve_kineticVelocity {m : ℝ} (hm : m ≠ 0) (q : ℝ) (A : Space → Space)
    (z : ℝ → PhaseSpace) :
    canonicalCurve m q A (fun t => (z t).1) (fun t => kineticVelocity m q A (z t)) = z := by
  funext t
  refine Prod.ext rfl ?_
  change m • innerSL ℝ (kineticVelocity m q A (z t)) + q • innerSL ℝ (A (z t).1) = (z t).2
  ext w
  simp only [kineticVelocity, _root_.add_apply, _root_.smul_apply, innerSL_apply_apply,
    smul_eq_mul, inner_smul_left, inner_sub_left, toDual_symm_apply, RCLike.conj_to_real]
  field_simp
  ring

/-- **Lorentz orbits and integral curves correspond.** For `m ≠ 0`, `A` differentiable,
`B = ∇ × A` and `E = −∇Φ`: `(x, v)` is a Lorentz orbit if and only if its canonical lift is an
integral curve of the Hamiltonian vector field of `emHamiltonian m q A Φ`. -/
theorem lorentzOrbit_iff_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hΦ : IsPotential Φ E) (x v : ℝ → Space) :
    LorentzOrbit m q E B x v ↔
      ∀ t, HasDerivAt (canonicalCurve m q A x v)
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (canonicalCurve m q A x v t)) t := by
  refine ⟨fun h t => lorentzOrbit_emHamilton hm h hA hcurl hΦ t, fun h => ?_⟩
  have key := lorentzOrbit_of_emHamilton hm hA hcurl hΦ h
  have hv : (fun t => kineticVelocity m q A (canonicalCurve m q A x v t)) = v :=
    funext fun t => kineticVelocity_canonicalCurve hm q A x v t
  rw [hv] at key
  exact key

/-- **Hamilton's equations are the Lorentz equations.** For `m ≠ 0`, `A` differentiable,
`B = ∇ × A` and `E = −∇Φ`: a phase-space curve is an integral curve of the Hamiltonian vector
field of `emHamiltonian m q A Φ` if and only if it is the canonical lift of a Lorentz orbit. -/
theorem emHamilton_iff_exists_lorentzOrbit {m q : ℝ} (hm : m ≠ 0) {A E B : Space → Space}
    {Φ : Space → ℝ} (hA : Differentiable ℝ A) (hcurl : ∀ y, B y = fieldCurl A y)
    (hΦ : IsPotential Φ E) (z : ℝ → PhaseSpace) :
    (∀ t, HasDerivAt z
        ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
          (emHamiltonian m q A Φ) (z t)) t) ↔
      ∃ x v, LorentzOrbit m q E B x v ∧ z = canonicalCurve m q A x v := by
  constructor
  · intro hz
    exact ⟨_, _, lorentzOrbit_of_emHamilton hm hA hcurl hΦ hz,
      (canonicalCurve_kineticVelocity hm q A z).symm⟩
  · rintro ⟨x, v, h, rfl⟩ t
    exact lorentzOrbit_emHamilton hm h hA hcurl hΦ t

/-- On the canonical lift the Hamiltonian is the orbit energy `(m/2)‖v‖² + q Φ(x)` of
`Theory/Kinetic/FullOrbit` (for `m ≠ 0`). -/
theorem emHamiltonian_canonicalCurve {m : ℝ} (hm : m ≠ 0) (q : ℝ) (A : Space → Space)
    (Φ : Space → ℝ) (x v : ℝ → Space) (t : ℝ) :
    emHamiltonian m q A Φ (canonicalCurve m q A x v t) = orbitEnergy m q Φ x v t := by
  rw [emHamiltonian, magneticHamiltonian_canonicalCurve hm]
  rfl

/-- **Conservation of the Hamiltonian.** For `A` differentiable and `E = −∇Φ`, the Hamiltonian
is constant along every integral curve of its Hamiltonian vector field
(`TauCeti.SymplecticForm.apply_eq_of_hasDerivWithinAt_hamiltonianVectorField`). No hypothesis
on `m` and none relating `B` to `A`. -/
theorem emHamiltonian_conserved (m q : ℝ) {A E : Space → Space} {Φ : Space → ℝ}
    {z : ℝ → PhaseSpace} (hA : Differentiable ℝ A) (hΦ : IsPotential Φ E)
    (hz : ∀ t, HasDerivAt z
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z t)) t) (s t : ℝ) :
    emHamiltonian m q A Φ (z s) = emHamiltonian m q A Φ (z t) :=
  SymplecticForm.apply_eq_of_hasDerivWithinAt_hamiltonianVectorField _ isPreconnected_univ
    (fun r _ => (hz r).hasDerivWithinAt)
    (fun r _ => differentiableAt_emHamiltonian m q hΦ (hA (z r).1)) (Set.mem_univ t)
    (Set.mem_univ s)

/-- **Energy along integral curves.** For `m ≠ 0`, `A` differentiable and `E = −∇Φ`, the
energy `(m/2)‖v‖² + q Φ(x)` of the position and velocity read off from an integral curve of
the Hamiltonian vector field is constant. Together with `lorentzOrbit_of_emHamilton` this
agrees with `energy_conserved` of `Theory/Kinetic/FullOrbit`, which proves the same
conservation directly for every Lorentz orbit. -/
theorem orbitEnergy_conserved_of_emHamilton {m q : ℝ} (hm : m ≠ 0) {A E : Space → Space}
    {Φ : Space → ℝ} {z : ℝ → PhaseSpace} (hA : Differentiable ℝ A) (hΦ : IsPotential Φ E)
    (hz : ∀ t, HasDerivAt z
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (emHamiltonian m q A Φ) (z t)) t) (s t : ℝ) :
    orbitEnergy m q Φ (fun r => (z r).1) (fun r => kineticVelocity m q A (z r)) s =
      orbitEnergy m q Φ (fun r => (z r).1) (fun r => kineticVelocity m q A (z r)) t := by
  have key := emHamiltonian_conserved m q hA hΦ hz s t
  rw [← emHamiltonian_canonicalCurve hm q A, ← emHamiltonian_canonicalCurve hm q A,
    canonicalCurve_kineticVelocity hm]
  exact key

end PlasmaLean.Kinetic
