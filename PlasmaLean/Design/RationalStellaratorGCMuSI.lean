/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCConfined

/-!
# Scaling of `μ > 0` Littlejohn orbits between SI and model units

For the rational stellarator field in SI units `fieldSI B₀ R₀ x = B₀ · field (1/4) (x/R₀)`, a
Littlejohn orbit `(X, v_∥)` with mass `m`, charge `q`, magnetic moment `μ` corresponds to the model
orbit `(X/R₀, v_∥/R₀)` with mass `m/B₀`, the same charge and magnetic moment `μ/R₀²`
(`littlejohnSI_iff`), and the Hamiltonian scales by `B₀R₀²` (`hamiltonian_fieldSI`). The
ingredients: `gradAbsB_fieldSI` (`∇|B_SI|(x) = (B₀/R₀) ∇|B|(x/R₀)`) and `Bstar_fieldSI`.

**Sanity.** `littlejohnSI_iff_one`: for `B₀ = R₀ = 1` the correspondence is the identity.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Real Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator
  PlasmaLean.Kinetic.GCLittlejohn WithLp

/-- **`∇|B_SI|(x) = (B₀/R₀) ∇|B|(x/R₀)`.** -/
theorem gradAbsB_fieldSI {B₀ : ℝ} (hB₀ : 0 < B₀) (R₀ : ℝ) (x : Space) :
    gradAbsB (fieldSI B₀ R₀) x = (B₀ * R₀⁻¹) • gradAbsB (field (1 / 4)) (R₀⁻¹ • x) := by
  have e : (fun y => ‖fieldSI B₀ R₀ y‖) =
      B₀ • ((fun y => ‖field (1 / 4) y‖) <| R₀⁻¹ • ·) := by
    funext y
    simp [fieldSI, norm_smul, abs_of_pos hB₀]
  have hf := fderiv_comp_smul (𝕜 := ℝ) (f := fun y : Space => ‖field (1 / 4) y‖) (x := x) R₀⁻¹
  rw [gradAbsB, e, gradient, fderiv_const_smul_field, Pi.smul_apply]
  erw [hf]
  rw [smul_smul, map_smul, gradAbsB, gradient]

/-- **`B*_SI(x) = B₀ B*(x/R₀)`** with mass `m/B₀` and parallel velocity `v/R₀`. -/
theorem Bstar_fieldSI {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m q v : ℝ) (x : Space) :
    Bstar m q (fieldSI B₀ R₀) v x = B₀ • Bstar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x) := by
  rw [Bstar_eq_modField, Bstar_eq_modField, fieldSI_modField hB₀ hR₀]
  congr 2
  field_simp

/-- `B*_∥` in SI units against model units. -/
theorem BstarPar_fieldSI' {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m q v : ℝ) (x : Space) :
    BstarPar m q (fieldSI B₀ R₀) v x =
      B₀ * BstarPar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x) := by
  rw [BstarPar_fieldSI hB₀ hR₀, BstarPar_field]

/-- **The Hamiltonian scales by `B₀R₀²`.** -/
theorem hamiltonian_fieldSI {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m μ v : ℝ) (x : Space) :
    hamiltonian m μ (fieldSI B₀ R₀) x v =
      B₀ * R₀ ^ 2 * hamiltonian (m / B₀) (μ / R₀ ^ 2) (field (1 / 4)) (R₀⁻¹ • x) (v / R₀) := by
  simp only [hamiltonian, fieldSI, norm_smul, Real.norm_eq_abs, abs_of_pos hB₀]
  field_simp

/-- The velocity of an SI orbit, rescaled, in model form. -/
theorem velSI_eq {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m q μ v : ℝ) (x : Space) :
    R₀⁻¹ • ((BstarPar m q (fieldSI B₀ R₀) v x)⁻¹ • (v • Bstar m q (fieldSI B₀ R₀) v x +
      (μ / q) • cross (bhat (fieldSI B₀ R₀) x) (gradAbsB (fieldSI B₀ R₀) x))) =
    (BstarPar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x))⁻¹ •
      ((v / R₀) • Bstar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x) +
        (μ / R₀ ^ 2 / q) • cross (bhat (field (1 / 4)) (R₀⁻¹ • x))
          (gradAbsB (field (1 / 4)) (R₀⁻¹ • x))) := by
  rw [BstarPar_fieldSI' hB₀ hR₀, Bstar_fieldSI hB₀ hR₀, bhat_fieldSI hB₀,
    gradAbsB_fieldSI hB₀]
  beta_reduce
  rw [cross_smul_right, mul_inv, smul_add, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
    smul_smul, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2
  · field_simp
  · field_simp

/-- The parallel acceleration of an SI orbit, rescaled, in model form. -/
theorem accSI_eq {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) (m q μ v : ℝ) (x : Space) :
    R₀⁻¹ * (-(μ / m) * (BstarPar m q (fieldSI B₀ R₀) v x)⁻¹ *
      ⟪Bstar m q (fieldSI B₀ R₀) v x, gradAbsB (fieldSI B₀ R₀) x⟫) =
    -(μ / R₀ ^ 2 / (m / B₀)) * (BstarPar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x))⁻¹ *
      ⟪Bstar (m / B₀) q (field (1 / 4)) (v / R₀) (R₀⁻¹ • x),
        gradAbsB (field (1 / 4)) (R₀⁻¹ • x)⟫ := by
  rw [BstarPar_fieldSI' hB₀ hR₀, Bstar_fieldSI hB₀ hR₀, gradAbsB_fieldSI hB₀, inner_smul_left,
    inner_smul_right, mul_inv]
  simp only [RCLike.conj_to_real]
  have hB : B₀ ≠ 0 := hB₀.ne'
  have hR : R₀ ≠ 0 := hR₀.ne'
  rcases eq_or_ne m 0 with hm | hm
  · subst hm; simp
  field_simp

/-- **SI orbits are rescaled model orbits**: `(X, v)` is a Littlejohn orbit in `fieldSI B₀ R₀`
with `(m, q, μ)` iff `(X/R₀, v/R₀)` is one in `field (1/4)` with `(m/B₀, q, μ/R₀²)`. -/
theorem littlejohnSI_iff {B₀ R₀ : ℝ} (hB₀ : 0 < B₀) (hR₀ : 0 < R₀) {m q μ : ℝ} {X : ℝ → Space}
    {v : ℝ → ℝ} :
    LittlejohnOrbit m q μ (fieldSI B₀ R₀) X v ↔
      LittlejohnOrbit (m / B₀) q (μ / R₀ ^ 2) (field (1 / 4)) (fun t => R₀⁻¹ • X t)
        (fun t => v t / R₀) := by
  have hR : R₀ ≠ 0 := hR₀.ne'
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have := (h.hX t).const_smul R₀⁻¹
      rwa [velSI_eq hB₀ hR₀] at this
    · have := (h.hv t).div_const R₀
      rw [div_eq_inv_mul _ R₀, accSI_eq hB₀ hR₀] at this
      exact this
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · have h1 := (h.hX t).const_smul R₀
      have e : (R₀ • fun s => R₀⁻¹ • X s) = X := by
        funext s; rw [Pi.smul_apply, smul_smul, mul_inv_cancel₀ hR, one_smul]
      rw [e, ← velSI_eq hB₀ hR₀, smul_smul, mul_inv_cancel₀ hR, one_smul] at h1
      exact h1
    · have h1 := (h.hv t).const_mul R₀
      have e : (fun s => R₀ * (v s / R₀)) = v := by funext s; field_simp
      rw [e, ← accSI_eq hB₀ hR₀, ← mul_assoc, mul_inv_cancel₀ hR, one_mul] at h1
      exact h1

/-- **Sanity**: for `B₀ = R₀ = 1` the SI field is the model field and the correspondence is the
identity. -/
theorem littlejohnSI_iff_one {m q μ : ℝ} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q μ (fieldSI 1 1) X v) :
    LittlejohnOrbit m q μ (field (1 / 4)) X v := by
  have := (littlejohnSI_iff one_pos one_pos).1 h
  simpa using this

end PlasmaLean.Design.RationalStellaratorGC
