/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.NoetherLagrangian
public import TauCeti.Geometry.Symplectic.Cotangent.Fiberwise
public import TauCeti.Geometry.Symplectic.Hamiltonian.FreeParticle
public import TauCeti.Analysis.Calculus.DifferentialForm.Basic

/-!
# Charged-particle orbits and the magnetic symplectic form

The phase space of a particle in `Space` is the linear cotangent space `Space × Space*`, with
TauCeti's canonical symplectic form `Ω((δx, δp), (δx', δp')) = δp'(δx) − δp(δx')`
(`TauCeti.strongDualCotangentSymplecticForm`). For a vector potential `A` and charge `q` this
file instantiates TauCeti's magnetic translation with the one-form `q A♭` and connects it to
Lorentz orbits.

* `potentialForm q A`: the one-form `q A♭`. `extDeriv_potentialForm`: its exterior derivative
  is `q • flux (∇ × A)`, the magnetic flux form times the charge, with no differentiability
  hypothesis.
* `kineticMomentumMap q A`: the map `(x, p) ↦ (x, p − q A(x)♭)` from canonical to kinetic
  momentum (`TauCeti.cotangentFiberTranslate`). It is a bijection
  (`kineticMomentumMap_bijective`) with inverse `kineticMomentumMap (-q) A`
  (`kineticMomentumMap_neg_comp`). Where `A` is differentiable, with `B = ∇ × A`, the identity
  proved is `Ω(DΨ v, DΨ w) = Ω(v, w) + q ω_B(δx_v, δx_w)`, that is `Ψ^*Ω = Ω + q π^*ω_B`
  (`canonicalForm_fderiv_kineticMomentumMap`, `canonicalForm_fderiv_kineticMomentumMap_flux`).
* **Sign and direction of the magnetic symplectic form.** In the convention above
  (`ι_X Ω = dH`) the magnetic symplectic form on the space of positions and KINETIC momenta is
  `magneticForm q B = Ω − q π^*ω_B`, with a minus sign. The sign is fixed by
  `magneticForm_lorentzForceField`: with this form the free Hamiltonian `‖π‖² / (2m)` has
  Hamiltonian vector field `lorentzForceField`, `x' = π♯/m`, `π' = (q/m) (π♯ × B)♭`, and
  Lorentz orbits are its integral curves (`lorentzOrbit_kineticCurve`). The map `Ψ` goes from
  (canonical momenta, `Ω`) to (kinetic momenta, `Ω − q π^*ω_B`) and is symplectic between
  these (`magneticForm_fderiv_kineticMomentumMap`); its inverse pulls `Ω` back to
  `Ω − q π^*ω_B` (`canonicalForm_fderiv_kineticMomentumMap_neg_flux`). The form
  `Ω + q π^*ω_B` of the first identity is a form on the space of canonical momenta, the
  pull-back of the canonical form of the kinetic space; it is not the magnetic form.
* `magneticHamiltonian m q A`: the free-particle kinetic energy of TauCeti composed with the
  kinetic momentum map, `H(x, p) = ‖p♯ − q A(x)‖² / (2m)` (`magneticHamiltonian_eq`), with
  derivative `fderiv_magneticHamiltonian_apply`.
* `lorentzOrbit_hamilton`: along a Lorentz orbit with `E = 0`, `B = ∇ × A` and `m ≠ 0`, the
  curve `t ↦ (x t, m (v t)♭ + q A(x t)♭)` is an integral curve of the Hamiltonian vector field
  of `H` for the canonical form (`TauCeti.SymplecticForm.hamiltonianVectorField`, convention
  `ι_X Ω = dH`). `magneticHamiltonian_canonicalCurve`: on that curve `H = (m/2)‖v‖²`.

Limit of the statements: every theorem that relates `B` to `A` assumes a vector potential `A`
differentiable on ALL of space with `B = ∇ × A` everywhere (or at the point considered, for the
pointwise statements). This excludes the vacuum field `∇φ` of a straight wire or of a toroidal
coil (it has no global potential regular on the axis) and any field defined only on a toroidal
region. Versions on an open set containing the orbit are not stated. Only `magneticForm`,
`lorentzForceField`, `magneticForm_lorentzForceField` and `lorentzOrbit_kineticCurve` use the
field `B` alone, with no potential and no regularity.

Not proved here: the kinetic momentum map is not bundled as a symplectomorphism (the statements
are pointwise, as in TauCeti), and closedness and nondegeneracy of `magneticForm` are not
stated; no time-dependent potential is treated. The converse (integral curves of the
Hamiltonian field are Lorentz orbits) and an electric field are in
`Theory/Kinetic/MagneticHamiltonConverse`.
-/

@[expose] public section

namespace PlasmaLean.Kinetic

open PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Forms
open TauCeti InnerProductSpace ContinuousAlternatingMap
open scoped RealInnerProductSpace

/-- The phase space of a particle: positions and covectors (canonical momenta). -/
abbrev PhaseSpace : Type := Space × StrongDual ℝ Space

/-- The one-form `q A♭` of a vector potential `A`, for a particle of charge `q`. -/
noncomputable def potentialForm (q : ℝ) (A : Space → Space) : Space → Form 1 :=
  fun y => q • flat (A y)

/-- `q A♭` on a tangent vector is `q⟪A, w⟫`. -/
theorem potentialForm_apply (q : ℝ) (A : Space → Space) (y : Space) (w : Fin 1 → Space) :
    potentialForm q A y w = q * ⟪A y, w 0⟫ := by
  simp [potentialForm]

/-- The derivative of `q A♭` is `δ ↦ q (DA δ)♭`. -/
theorem hasFDerivAt_potentialForm (q : ℝ) {A : Space → Space} {y : Space}
    (hA : DifferentiableAt ℝ A y) :
    HasFDerivAt (potentialForm q A)
      (q • (flat.toContinuousLinearEquiv : Space →L[ℝ] Form 1).comp (fderiv ℝ A y)) y :=
  ((flat.toContinuousLinearEquiv : Space →L[ℝ] Form 1).hasFDerivAt.comp y
    hA.hasFDerivAt).const_smul q

/-- `q A♭` is differentiable wherever `A` is. -/
theorem differentiableAt_potentialForm (q : ℝ) {A : Space → Space} {y : Space}
    (hA : DifferentiableAt ℝ A y) : DifferentiableAt ℝ (potentialForm q A) y :=
  (hasFDerivAt_potentialForm q hA).differentiableAt

/-- **The magnetic term**: `d(q A♭) = q • flux (∇ × A)`, the flux form of the magnetic field
`B = ∇ × A` times the charge. It holds at every point with no differentiability hypothesis
(both sides use the Fréchet derivative, which is zero where `A` is not differentiable). -/
theorem extDeriv_potentialForm (q : ℝ) (A : Space → Space) (y : Space) :
    extDeriv (potentialForm q A) y = q • flux (fieldCurl A y) := by
  have h : potentialForm q A = q • fun z => flat (A z) := rfl
  rw [h, extDeriv_smul_field, extDeriv_flat]

/-- The map from canonical to kinetic momentum, `(x, p) ↦ (x, p − q A(x)♭)`: TauCeti's magnetic
translation of the cotangent space by the one-form `q A♭`. -/
noncomputable def kineticMomentumMap (q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    PhaseSpace :=
  cotangentFiberTranslate (potentialForm q A) z

/-- The kinetic momentum map keeps the position. -/
@[simp] theorem kineticMomentumMap_fst (q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    (kineticMomentumMap q A z).1 = z.1 :=
  cotangentFiberTranslate_fst _ z

/-- The kinetic momentum map subtracts `q A(x)♭` from the momentum. -/
theorem kineticMomentumMap_snd (q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    (kineticMomentumMap q A z).2 = z.2 - q • innerSL ℝ (A z.1) := by
  ext w
  simp [kineticMomentumMap, cotangentFiberTranslate_snd_apply, potentialForm_apply]

/-- The kinetic momentum map is a bijection of phase space, for every `A`; its inverse adds
`q A(x)♭` back. -/
theorem kineticMomentumMap_bijective (q : ℝ) (A : Space → Space) :
    Function.Bijective (kineticMomentumMap q A) :=
  ⟨(leftInverse_cotangentFiberTranslate_neg (potentialForm q A)).injective,
    (rightInverse_cotangentFiberTranslate_neg (potentialForm q A)).surjective⟩

/-- **Pull-back of the canonical form by the kinetic momentum map.** At a point `z = (x, p)`
where the vector potential `A` is differentiable, the derivative of
`Ψ : (x, p) ↦ (x, p − q A(x)♭)` satisfies, on tangent vectors `v`, `w`,
`Ω(DΨ v, DΨ w) = Ω(v, w) + d(q A♭)_x(δx_v, δx_w)`, that is `Ψ^*Ω = Ω + π^*d(q A♭)`. This is
`TauCeti.strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate` for `σ = q A♭`.
The right-hand side is a form on the space of canonical momenta. It is not the magnetic
symplectic form, which lives on the space of kinetic momenta and is `Ω − q π^*ω_B`
(`magneticForm`, `magneticForm_fderiv_kineticMomentumMap`). -/
theorem canonicalForm_fderiv_kineticMomentumMap (q : ℝ) {A : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap q A) z v)
        (fderiv ℝ (kineticMomentumMap q A) z w) =
      strongDualCotangentSymplecticForm v w + extDeriv (potentialForm q A) z.1 ![v.1, w.1] :=
  strongDualCotangentSymplecticForm_fderiv_cotangentFiberTranslate
    (differentiableAt_potentialForm q hA) v w

/-- **`Ψ^*Ω = Ω + q π^*ω_B`.** In kernel language the pulled-back form of
`canonicalForm_fderiv_kineticMomentumMap` is the canonical form plus the charge times the
flux form of `B = ∇ × A` on the position components:
`Ω(DΨ v, DΨ w) = Ω(v, w) + q ω_B(δx_v, δx_w)`, for `Ψ` from canonical to kinetic momenta.
Convention: `Ω((δx, δp), (δx', δp')) = δp'(δx) − δp(δx')`, `ι_X Ω = dH`, and
`ω_B(a, b) = ⟪B, a × b⟫`. In this convention the magnetic symplectic form on the kinetic
space is `Ω − q π^*ω_B` (`magneticForm`), with the opposite sign; the present identity says
that `Ψ` pulls it back to `Ω` (`magneticForm_fderiv_kineticMomentumMap`). -/
theorem canonicalForm_fderiv_kineticMomentumMap_flux (q : ℝ) {A : Space → Space}
    {z : PhaseSpace} (hA : DifferentiableAt ℝ A z.1) (v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap q A) z v)
        (fderiv ℝ (kineticMomentumMap q A) z w) =
      strongDualCotangentSymplecticForm v w + q * flux (fieldCurl A z.1) ![v.1, w.1] := by
  rw [canonicalForm_fderiv_kineticMomentumMap q hA, extDeriv_potentialForm]
  simp

/-- The derivative of the kinetic momentum map: `DΨ (δx, δp) = (δx, δp − q (DA δx)♭)`. -/
theorem fderiv_kineticMomentumMap (q : ℝ) {A : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (w : PhaseSpace) :
    fderiv ℝ (kineticMomentumMap q A) z w =
      (w.1, w.2 - q • innerSL ℝ (fderiv ℝ A z.1 w.1)) := by
  have h := fderiv_cotangentFiberTranslate (differentiableAt_potentialForm q hA) w
  rw [(hasFDerivAt_potentialForm q hA).fderiv] at h
  change fderiv ℝ (cotangentFiberTranslate (potentialForm q A)) z w = _
  rw [h]
  refine Prod.ext rfl ?_
  ext u
  simp

/-- The kinetic momentum map with charge `−q` is the inverse of the one with charge `q`:
`(x, π) ↦ (x, π + q A(x)♭)` from kinetic to canonical momenta. No hypothesis on `A`. -/
theorem kineticMomentumMap_neg_comp (q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    kineticMomentumMap (-q) A (kineticMomentumMap q A z) = z ∧
      kineticMomentumMap q A (kineticMomentumMap (-q) A z) = z := by
  refine ⟨Prod.ext (by simp) ?_, Prod.ext (by simp) ?_⟩
  · rw [kineticMomentumMap_snd, kineticMomentumMap_snd, kineticMomentumMap_fst]
    simp
  · rw [kineticMomentumMap_snd, kineticMomentumMap_snd, kineticMomentumMap_fst]
    simp

/-- **Pull-back of the canonical form by the inverse map.** The map
`Ψ⁻¹ = kineticMomentumMap (-q) A : (x, π) ↦ (x, π + q A(x)♭)` from kinetic to canonical
momenta satisfies `Ω(DΨ⁻¹ v, DΨ⁻¹ w) = Ω(v, w) − q ω_B(δx_v, δx_w)` with `B = ∇ × A`: the
canonical form, expressed in position and kinetic momentum, is `Ω − q π^*ω_B`. -/
theorem canonicalForm_fderiv_kineticMomentumMap_neg_flux (q : ℝ) {A : Space → Space}
    {z : PhaseSpace} (hA : DifferentiableAt ℝ A z.1) (v w : PhaseSpace) :
    strongDualCotangentSymplecticForm (fderiv ℝ (kineticMomentumMap (-q) A) z v)
        (fderiv ℝ (kineticMomentumMap (-q) A) z w) =
      strongDualCotangentSymplecticForm v w - q * flux (fieldCurl A z.1) ![v.1, w.1] := by
  rw [canonicalForm_fderiv_kineticMomentumMap_flux (-q) hA]
  ring

/-- **The magnetic symplectic form** on the space of positions and kinetic momenta, at the
point `z = (x, π)`: `Ω(v, w) − q ω_B(δx_v, δx_w)` with `ω_B = flux (B x)`, that is
`Ω − q π^*ω_B`. Convention: `Ω((δx, δp), (δx', δp')) = δp'(δx) − δp(δx')` and
`ι_X Ω = dH` (TauCeti), `ω_B(a, b) = ⟪B, a × b⟫`. The minus sign is forced by
`magneticForm_lorentzForceField`. It is defined for every field `B`; no potential is used. -/
noncomputable def magneticForm (q : ℝ) (B : Space → Space) (z v w : PhaseSpace) : ℝ :=
  strongDualCotangentSymplecticForm v w - q * flux (B z.1) ![v.1, w.1]

/-- The Lorentz-force vector field on the space of positions and kinetic momenta:
at `(x, π)` it is `x' = π♯ / m`, `π' = (q/m) (π♯ × B(x))♭`, that is `π' = q v × B` with
`v = π♯ / m`. -/
noncomputable def lorentzForceField (m q : ℝ) (B : Space → Space) (z : PhaseSpace) :
    PhaseSpace :=
  (m⁻¹ • (toDual ℝ Space).symm z.2,
    (q / m) • innerSL ℝ (cross ((toDual ℝ Space).symm z.2) (B z.1)))

/-- **The sign of the magnetic form.** With `magneticForm q B = Ω − q π^*ω_B`, the Lorentz-force
field `X = (π♯/m, (q/m) (π♯ × B)♭)` satisfies `ι_X Ω_mag = dH` for the free Hamiltonian
`H(x, π) = ‖π‖² / (2m)`: the free Hamiltonian with the magnetic form generates
`m v' = q v × B`. No hypothesis on `B`, and none on `m` (for `m = 0` Lean's division makes
both sides `0`). With `+ q` in place of `− q` the identity fails
(`Sanity.MagneticSymplectic.uniform_plus_sign_fails`). -/
theorem magneticForm_lorentzForceField (m q : ℝ) (B : Space → Space) (z w : PhaseSpace) :
    magneticForm q B z (lorentzForceField m q B z) w =
      fderiv ℝ (freeParticleHamiltonian m) z w := by
  rw [(hasFDerivAt_freeParticleHamiltonian m z).fderiv]
  obtain ⟨c0, c1, c2⟩ := cross_coords ((toDual ℝ Space).symm z.2) (B z.1)
  simp only [magneticForm, lorentzForceField, strongDualCotangentSymplecticForm_apply,
    flux_apply, volForm_vec, _root_.smul_apply, innerSL_apply_apply, inner_coords3, c0, c1, c2,
    PiLp.smul_apply, smul_eq_mul, map_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.apply_apply]
  ring

/-- **The kinetic momentum map is symplectic from `Ω` to the magnetic form.** Where `A` is
differentiable and `B = ∇ × A`, the map `Ψ : (x, p) ↦ (x, p − q A(x)♭)` pulls
`magneticForm q B = Ω − q π^*ω_B` back to the canonical form:
`Ω_mag(DΨ v, DΨ w) = Ω(v, w)`. -/
theorem magneticForm_fderiv_kineticMomentumMap (q : ℝ) {A B : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (hcurl : B z.1 = fieldCurl A z.1) (v w : PhaseSpace) :
    magneticForm q B (kineticMomentumMap q A z) (fderiv ℝ (kineticMomentumMap q A) z v)
        (fderiv ℝ (kineticMomentumMap q A) z w) =
      strongDualCotangentSymplecticForm v w := by
  rw [magneticForm, canonicalForm_fderiv_kineticMomentumMap_flux q hA, kineticMomentumMap_fst,
    hcurl, fderiv_kineticMomentumMap q hA, fderiv_kineticMomentumMap q hA]
  ring

/-- The phase-space curve `t ↦ (x t, m (v t)♭)` of a trajectory, with the kinetic momentum. -/
noncomputable def kineticCurve (m : ℝ) (x v : ℝ → Space) (t : ℝ) : PhaseSpace :=
  (x t, m • innerSL ℝ (v t))

/-- **Lorentz orbits are integral curves of the Lorentz-force field.** For `m ≠ 0`, along a
Lorentz orbit `x' = v`, `m v' = q v × B` (no electric field), the curve
`t ↦ (x t, m (v t)♭)` of positions and kinetic momenta has derivative `lorentzForceField`.
By `magneticForm_lorentzForceField` that field is the Hamiltonian vector field of the free
Hamiltonian for `magneticForm q B = Ω − q π^*ω_B`. No potential and no regularity of `B`. -/
theorem lorentzOrbit_kineticCurve {m q : ℝ} (hm : m ≠ 0) {B : Space → Space}
    {x v : ℝ → Space} (h : LorentzOrbit m q (fun _ => 0) B x v) (t : ℝ) :
    HasDerivAt (kineticCurve m x v) (lorentzForceField m q B (kineticCurve m x v t)) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t
  have hv' : HasDerivAt (fun s => innerSL ℝ (v s)) (innerSL ℝ a) t :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t ha
  have hγ : HasDerivAt (kineticCurve m x v) (v t, m • innerSL ℝ a) t :=
    (h.position t).prodMk (hv'.const_smul m)
  refine hγ.congr_deriv ?_
  have hu : (toDual ℝ Space).symm (m • innerSL ℝ (v t)) = m • v t := by
    rw [map_smul, toDual_symm_innerSL]
  have hc : cross (m • v t) (B (x t)) = m • cross (v t) (B (x t)) :=
    crossBilinear.map_smul₂ m (v t) (B (x t))
  rw [zero_add] at hlaw
  refine Prod.ext ?_ ?_
  · change v t = m⁻¹ • (toDual ℝ Space).symm (m • innerSL ℝ (v t))
    rw [hu, smul_smul, inv_mul_cancel₀ hm, one_smul]
  · change m • innerSL ℝ a
      = (q / m) • innerSL ℝ (cross ((toDual ℝ Space).symm (m • innerSL ℝ (v t))) (B (x t)))
    rw [hu, ← map_smul, hlaw, hc, map_smul, map_smul, smul_smul, div_mul_cancel₀ q hm]

/-- The Hamiltonian of a particle of mass `m` and charge `q` in the vector potential `A`: the
free-particle kinetic energy of TauCeti evaluated on the kinetic momentum,
`H(x, p) = ‖p − q A(x)♭‖² / (2m)`. -/
noncomputable def magneticHamiltonian (m q : ℝ) (A : Space → Space) (z : PhaseSpace) : ℝ :=
  freeParticleHamiltonian m (kineticMomentumMap q A z)

/-- The Riesz representative of `a♭` is `a`. -/
theorem toDual_symm_innerSL (a : Space) : (toDual ℝ Space).symm (innerSL ℝ a) = a := by
  have h : innerSL ℝ a = toDual ℝ Space a := by
    ext w
    simp
  rw [h, LinearIsometryEquiv.symm_apply_apply]

/-- The kinetic momentum as a vector: `(p − q A(x)♭)♯ = p♯ − q A(x)`. -/
theorem toDual_symm_kineticMomentumMap (q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    (toDual ℝ Space).symm (kineticMomentumMap q A z).2 =
      (toDual ℝ Space).symm z.2 - q • A z.1 := by
  rw [kineticMomentumMap_snd, map_sub, map_smul, toDual_symm_innerSL]

/-- `H(x, p) = ‖p♯ − q A(x)‖² / (2m)`, with `p♯` the vector representing the covector `p`. -/
theorem magneticHamiltonian_eq (m q : ℝ) (A : Space → Space) (z : PhaseSpace) :
    magneticHamiltonian m q A z = ‖(toDual ℝ Space).symm z.2 - q • A z.1‖ ^ 2 / (2 * m) := by
  rw [magneticHamiltonian, freeParticleHamiltonian_apply, ← toDual_symm_kineticMomentumMap,
    LinearIsometryEquiv.norm_map]

/-- **The derivative of the Hamiltonian.** With `u = p♯ − q A(x)` the kinetic momentum vector,
`dH(δx, δp) = (δp(u) − q⟪DA δx, u⟫) / m`: that is `∂_p H = u / m` and
`∂_x H = −(q/m) (DA)ᵀ u`. -/
theorem fderiv_magneticHamiltonian_apply (m q : ℝ) {A : Space → Space} {z : PhaseSpace}
    (hA : DifferentiableAt ℝ A z.1) (w : PhaseSpace) :
    fderiv ℝ (magneticHamiltonian m q A) z w =
      m⁻¹ * (w.2 ((toDual ℝ Space).symm z.2 - q • A z.1) -
        q * ⟪fderiv ℝ A z.1 w.1, (toDual ℝ Space).symm z.2 - q • A z.1⟫) := by
  have hΨ : HasFDerivAt (kineticMomentumMap q A) (fderiv ℝ (kineticMomentumMap q A) z) z :=
    (hasFDerivAt_cotangentFiberTranslate
      (differentiableAt_potentialForm q hA)).differentiableAt.hasFDerivAt
  have h := (hasFDerivAt_freeParticleHamiltonian m (kineticMomentumMap q A z)).comp z hΨ
  have e : fderiv ℝ (magneticHamiltonian m q A) z = _ := h.fderiv
  rw [e]
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.apply_apply, smul_eq_mul,
    fderiv_kineticMomentumMap q hA, toDual_symm_kineticMomentumMap, _root_.sub_apply,
    innerSL_apply_apply]

/-- The canonical momentum `p = m v♭ + q A(x)♭` along a trajectory, as a covector. -/
noncomputable def canonicalCovector (m q : ℝ) (A : Space → Space) (x v : ℝ → Space) (t : ℝ) :
    StrongDual ℝ Space :=
  m • innerSL ℝ (v t) + q • innerSL ℝ (A (x t))

/-- The phase-space curve `t ↦ (x t, m (v t)♭ + q A(x t)♭)` of a trajectory. -/
noncomputable def canonicalCurve (m q : ℝ) (A : Space → Space) (x v : ℝ → Space) (t : ℝ) :
    PhaseSpace :=
  (x t, canonicalCovector m q A x v t)

/-- On the canonical curve the kinetic momentum vector is `m v`. -/
theorem toDual_symm_canonicalCovector_sub (m q : ℝ) (A : Space → Space) (x v : ℝ → Space)
    (t : ℝ) :
    (toDual ℝ Space).symm (canonicalCovector m q A x v t) - q • A (x t) = m • v t := by
  rw [canonicalCovector, map_add, map_smul, map_smul, toDual_symm_innerSL,
    toDual_symm_innerSL, add_sub_cancel_right]

/-- On the canonical curve the Hamiltonian is the kinetic energy `(m/2)‖v‖²` (for `m ≠ 0`). -/
theorem magneticHamiltonian_canonicalCurve {m : ℝ} (hm : m ≠ 0) (q : ℝ) (A : Space → Space)
    (x v : ℝ → Space) (t : ℝ) :
    magneticHamiltonian m q A (canonicalCurve m q A x v t) = m / 2 * ‖v t‖ ^ 2 := by
  rw [magneticHamiltonian_eq]
  change ‖(toDual ℝ Space).symm (canonicalCovector m q A x v t) - q • A (x t)‖ ^ 2 / (2 * m)
    = _
  rw [toDual_symm_canonicalCovector_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- **Hamilton's equations for a Lorentz orbit.** Let `B = ∇ × A` with `A` differentiable and
`m ≠ 0`. Along a Lorentz orbit `x' = v`, `m v' = q v × B` (no electric field), the phase-space
curve `t ↦ (x t, p t)` with canonical momentum `p = m v♭ + q A(x)♭` is an integral curve of the
Hamiltonian vector field of `H(x, p) = ‖p♯ − q A(x)‖² / (2m)` for the canonical symplectic
form of `Space × Space*` (TauCeti's `hamiltonianVectorField`, with `ι_X Ω = dH`). -/
theorem lorentzOrbit_hamilton {m q : ℝ} (hm : m ≠ 0) {A B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (hA : Differentiable ℝ A)
    (hcurl : ∀ y, B y = fieldCurl A y) (t : ℝ) :
    HasDerivAt (canonicalCurve m q A x v)
      ((strongDualCotangentSymplecticForm (V := Space)).hamiltonianVectorField
        (magneticHamiltonian m q A) (canonicalCurve m q A x v t)) t := by
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
  rw [SymplecticForm.eq_hamiltonianVectorField_iff]
  intro w
  have hAt : DifferentiableAt ℝ A (canonicalCurve m q A x v t).1 := hA (x t)
  rw [fderiv_magneticHamiltonian_apply m q hAt]
  change _ = m⁻¹ * (w.2 ((toDual ℝ Space).symm (canonicalCovector m q A x v t) - q • A (x t)) -
    q * ⟪fderiv ℝ A (x t) w.1,
      (toDual ℝ Space).symm (canonicalCovector m q A x v t) - q • A (x t)⟫)
  rw [toDual_symm_canonicalCovector_sub]
  have hid := inner_cross_curlOp (fderiv ℝ A (x t)) (v t) w.1
  have hma : m * ⟪a, w.1⟫ = q * ⟪cross (v t) (curlOp (fderiv ℝ A (x t))), w.1⟫ := by
    have := congrArg (fun y : Space => ⟪y, w.1⟫) hlaw
    simpa [inner_smul_left, hcurl, fieldCurl] using this
  simp only [strongDualCotangentSymplecticForm_apply, _root_.add_apply, _root_.smul_apply,
    innerSL_apply_apply, smul_eq_mul, map_smul, inner_smul_right]
  rw [hma, hid]
  field_simp
  ring

end PlasmaLean.Kinetic
