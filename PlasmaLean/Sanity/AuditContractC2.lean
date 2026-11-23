/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.BoozerModel

/-!
# Audit (23 November 2026): regressions for clause C2 and the per-torus QA defect

Findings AV-M7, AV-M8 and AV-L1 of the audit of 23 November 2026.

**AV-M8: a Boozer chart does not pin the poloidal angle.** `Contract.BoozerChart` has no
poloidal-angle convention. If `x` is a chart of `B` onto `Ω` for the model `F`, then for every
integer `k` the relabelled map `x'(ψ, θ, φ) = x(ψ, θ − kφ, φ)` is a chart of the **same** field
onto the **same** region for the model `relabelField F k`, whose rotational transform is
`F.ι + k` (`relabelChart`, `BoozerModelOf.relabel`). So the `ι` of a Boozer model of a field is
defined only modulo integers, and the hypotheses `ιmin ≤ F.ι` of the bridge theorems
`omnigeneityContract_of_qa` and `omnigeneityContract_of_defect_le` depend on the chart. Concrete
fixture: the field `∇φ`, whose rotational transform in the sense of clause C1 is `0` on every
torus (`Contract.iota_eq_zero_of_purelyToroidal`), has a Boozer model with `ι = 1`
(`toroidal_boozerModelOf_iota_one`), and its relabelled surfaces are `FieldTorus`es with rotation
number `1` (`torChart_relabel_fieldTorus`; they have no `PoloidalAngle`).

**AV-M7: C2 for a field has no non-vacuous witness.** The only accepted instance of
`Contract.OmnigeneityContract` is the field `∇φ` with `ι = 0`, where no trapped bounce exists. A
trapped bounce is constructed only at model level, for the drift-mirror model, which is not the
Boozer model of any field in the library (`exists_trappedBounce_driftMirror`).

**AV-L1: `TorusQADefectLe` has no regularity clause.** It is built from `deriv` and a division,
so it holds with bound `0` for a constant map `K` (`torusQADefectLe_const`) and for the zero
field (`torusQADefectLe_zero_field`). The predicate alone is not a quasisymmetry statement.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Sanity.AuditContractC2

open Real Set PlasmaLean.Fields PlasmaLean.Contract PlasmaLean.Kinetic PlasmaLean.Kinetic.Boozer
  PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Design.RationalStellarator (toroidal)

/-! ## AV-M8: relabelling the poloidal angle of a Boozer chart -/

/-- The shear `(ψ, θ, φ) ↦ (ψ, θ − kφ, φ)` of the chart domain, as a continuous linear map. -/
@[expose] def shear (k : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) -
        k • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))))

/-- Evaluation of the shear. -/
theorem shear_apply (k : ℝ) (p : ℝ × ℝ × ℝ) : shear k p = (p.1, p.2.1 - k * p.2.2, p.2.2) := by
  simp [shear]

/-- The shear is the derivative of the relabelling map. -/
theorem hasFDerivAt_shear (k : ℝ) (p : ℝ × ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ × ℝ => ((q.1, q.2.1 - k * q.2.2, q.2.2) : ℝ × ℝ × ℝ)) (shear k)
      p := by
  have h := (shear k).hasFDerivAt (x := p)
  rwa [show (⇑(shear k) : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) = fun q => (q.1, q.2.1 - k * q.2.2, q.2.2) from
    funext (shear_apply k)] at h

/-- The **relabelled Boozer model**: the model `F` written in the poloidal angle
`θ' = θ + kφ`. Its field strength is `F.B(ψ, θ' − kφ, φ)`, its rotational transform is
`F.ι + k` and its poloidal flux function is `F.ψp + kψ`; `G` is unchanged. -/
@[expose] def relabelField (F : BoozerField) (k : ℝ) : BoozerField where
  B ψ θ φ := F.B ψ (θ - k * φ) φ
  Bψ ψ θ φ := F.Bψ ψ (θ - k * φ) φ
  Bθ ψ θ φ := F.Bθ ψ (θ - k * φ) φ
  Bφ ψ θ φ := F.Bφ ψ (θ - k * φ) φ - k * F.Bθ ψ (θ - k * φ) φ
  ψp x := F.ψp x + k * x
  ι x := F.ι x + k
  G := F.G
  hasFDerivAt_B p hp := by
    have h := (F.hasFDerivAt_B (p.1, p.2.1 - k * p.2.2, p.2.2) hp).comp p (hasFDerivAt_shear k p)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    simp only [gradCLM_apply, ContinuousLinearMap.comp_apply, shear_apply]
    ring
  hasDerivAt_ψp x hx := by
    have h := (F.hasDerivAt_ψp x hx).add ((hasDerivAt_id' x).const_mul k)
    rw [mul_one] at h
    exact h

/-- The relabelled model has rotational transform `F.ι + k`. -/
theorem relabelField_iota (F : BoozerField) (k x : ℝ) : (relabelField F k).ι x = F.ι x + k :=
  rfl

section Relabel

variable {B : Space → Space} {Ω : Set Space} {c : ℝ} {F : BoozerField}

/-- A chart is periodic in `θ` with every integer multiple of `2π`. -/
theorem chart_sub_int_mul (X : BoozerChart B Ω c F) (k : ℤ) (ψ θ φ : ℝ) :
    X.x (ψ, θ - k * (2 * π), φ) = X.x (ψ, θ, φ) := by
  have hper : Function.Periodic (fun t => X.x (ψ, t, φ)) (2 * π) := fun t => X.per_θ ψ t φ
  exact (hper.int_mul k).sub_eq θ

/-- The derivative of the relabelled chart map. -/
theorem fderiv_relabel (X : BoozerChart B Ω c F) (k : ℝ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    fderiv ℝ (fun q : ℝ × ℝ × ℝ => X.x (q.1, q.2.1 - k * q.2.2, q.2.2)) p =
      (fderiv ℝ X.x (p.1, p.2.1 - k * p.2.2, p.2.2)).comp (shear k) :=
  ((X.differentiableAt (p := (p.1, p.2.1 - k * p.2.2, p.2.2)) hp).hasFDerivAt.comp p
    (hasFDerivAt_shear k p)).fderiv

/-- `e_ψ` of the relabelled chart map. -/
theorem chartPsi_relabel (X : BoozerChart B Ω c F) (k : ℝ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    chartPsi (fun q : ℝ × ℝ × ℝ => X.x (q.1, q.2.1 - k * q.2.2, q.2.2)) p =
      chartPsi X.x (p.1, p.2.1 - k * p.2.2, p.2.2) := by
  rw [chartPsi, fderiv_relabel X k hp, ContinuousLinearMap.comp_apply, shear_apply]
  simp [chartPsi]

/-- `e_θ` of the relabelled chart map. -/
theorem chartTheta_relabel (X : BoozerChart B Ω c F) (k : ℝ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    chartTheta (fun q : ℝ × ℝ × ℝ => X.x (q.1, q.2.1 - k * q.2.2, q.2.2)) p =
      chartTheta X.x (p.1, p.2.1 - k * p.2.2, p.2.2) := by
  rw [chartTheta, fderiv_relabel X k hp, ContinuousLinearMap.comp_apply, shear_apply]
  simp [chartTheta]

/-- `e_φ` of the relabelled chart map: `e_φ − k e_θ`. -/
theorem chartPhi_relabel (X : BoozerChart B Ω c F) (k : ℝ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    chartPhi (fun q : ℝ × ℝ × ℝ => X.x (q.1, q.2.1 - k * q.2.2, q.2.2)) p =
      chartPhi X.x (p.1, p.2.1 - k * p.2.2, p.2.2) -
        k • chartTheta X.x (p.1, p.2.1 - k * p.2.2, p.2.2) := by
  rw [chartPhi, fderiv_relabel X k hp, ContinuousLinearMap.comp_apply, shear_apply,
    clm_apply_triple]
  simp only [chartPhi, chartTheta, zero_smul, zero_add, mul_one, zero_sub, one_smul, neg_smul]
  abel

/-- The Jacobian of the relabelled chart map is the Jacobian of the chart. -/
theorem chartJac_relabel (X : BoozerChart B Ω c F) (k : ℝ) {p : ℝ × ℝ × ℝ}
    (hp : p ∈ chartRegion c) :
    chartJac (fun q : ℝ × ℝ × ℝ => X.x (q.1, q.2.1 - k * q.2.2, q.2.2)) p =
      chartJac X.x (p.1, p.2.1 - k * p.2.2, p.2.2) := by
  rw [chartJac, chartPsi_relabel X k hp, chartTheta_relabel X k hp, chartPhi_relabel X k hp,
    chartJac, tripleFlux_cycle, tripleFlux_cycle, sub_eq_neg_add, ← neg_smul,
    tripleFlux_smul_add_left, tripleFlux_self_right, mul_zero, zero_add, ← tripleFlux_cycle,
    ← tripleFlux_cycle]

/-- **Regression (audit AV-M8): a Boozer chart does not pin the poloidal angle.** If `X` is a
Boozer chart of the field `B` onto `Ω` for the model `F`, then for every integer `k` the map
`(ψ, θ, φ) ↦ X.x (ψ, θ − kφ, φ)` is a Boozer chart of the same field onto the same region for the
relabelled model `relabelField F k`, whose rotational transform is `F.ι + k`. -/
@[expose] def relabelChart (X : BoozerChart B Ω c F) (k : ℤ) :
    BoozerChart B Ω c (relabelField F k) where
  x q := X.x (q.1, q.2.1 - k * q.2.2, q.2.2)
  contDiffAt p hp :=
    (X.contDiffAt (p.1, p.2.1 - k * p.2.2, p.2.2) hp).comp p
      (show ContDiffAt ℝ 1 (fun q : ℝ × ℝ × ℝ => ((q.1, q.2.1 - k * q.2.2, q.2.2) : ℝ × ℝ × ℝ)) p
        by fun_prop)
  per_θ ψ θ φ := by
    have h := X.per_θ ψ (θ - k * φ) φ
    rwa [show θ - k * φ + 2 * π = θ + 2 * π - k * φ by ring] at h
  per_φ ψ θ φ := by
    have h := chart_sub_int_mul X k ψ (θ - k * φ) (φ + 2 * π)
    rw [show θ - k * φ - k * (2 * π) = θ - k * (φ + 2 * π) by ring] at h
    exact h.trans (X.per_φ ψ (θ - k * φ) φ)
  inj p hp p' hp' h := by
    obtain ⟨h1, ⟨m, hm⟩, ⟨n, hn⟩⟩ := X.inj (p.1, p.2.1 - k * p.2.2, p.2.2) hp
      (p'.1, p'.2.1 - k * p'.2.2, p'.2.2) hp' h
    simp only at h1 hm hn
    refine ⟨h1, ⟨m + k * n, ?_⟩, ⟨n, hn⟩⟩
    push_cast
    linear_combination hm + (k : ℝ) * hn
  image := by
    refine Eq.trans ?_ X.image
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, p.2.1 - k * p.2.2, p.2.2), hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1, p.2.1 + k * p.2.2, p.2.2), hp, by simp⟩
  jac_ne p hp := by
    rw [chartJac_relabel X k hp]
    exact X.jac_ne _ hp
  contra p hp := by
    rw [chartJac_relabel X k hp, chartTheta_relabel X k hp, chartPhi_relabel X k hp,
      X.contra (p.1, p.2.1 - k * p.2.2, p.2.2) hp, relabelField_iota]
    module
  cov_psi p hp := by
    rw [chartPsi_relabel X k hp]
    exact X.cov_psi (p.1, p.2.1 - k * p.2.2, p.2.2) hp
  cov_theta p hp := by
    rw [chartTheta_relabel X k hp]
    exact X.cov_theta (p.1, p.2.1 - k * p.2.2, p.2.2) hp
  cov_phi p hp := by
    rw [chartPhi_relabel X k hp, inner_sub_right, inner_smul_right,
      X.cov_phi (p.1, p.2.1 - k * p.2.2, p.2.2) hp, X.cov_theta (p.1, p.2.1 - k * p.2.2, p.2.2) hp,
      mul_zero, sub_zero]
    rfl
  modB p hp := X.modB (p.1, p.2.1 - k * p.2.2, p.2.2) hp

/-- **Regression (audit AV-M8): the rotational transform of a Boozer model of a field is defined
only modulo integers.** If `F` is a Boozer model of `B` on `Ω`, so is `relabelField F k` for
every integer `k`, with rotational transform `F.ι + k`. -/
theorem _root_.PlasmaLean.Contract.BoozerModelOf.relabel (h : BoozerModelOf B Ω c F) (k : ℤ) :
    BoozerModelOf B Ω c (relabelField F k) :=
  let ⟨X⟩ := h
  ⟨relabelChart X k⟩

end Relabel

/-- **Regression (audit AV-M8): the field `∇φ` has a Boozer model with `ι = 1`** on
`torRegion R₀ c`, although its rotational transform in the sense of clause C1 is `0` on every
torus (`Contract.iota_eq_zero_of_purelyToroidal`) and its model `torModel R₀` has `ι = 0`. The
transform `F.ι` of clause C2 is therefore not tied to the transform `SurfaceData.iota` of clause
C1. -/
theorem toroidal_boozerModelOf_iota_one {R₀ : ℝ} (hR₀ : 0 < R₀) (c : ℝ) :
    ∃ F : BoozerField, BoozerModelOf toroidal (torRegion R₀ c) c F ∧ (∀ x, F.ι x = 1) ∧
      ∀ x, (torModel R₀).ι x = 0 :=
  ⟨relabelField (torModel R₀) (1 : ℤ), (toroidal_boozerModelOf hR₀ c).relabel 1,
    fun x => by simp [relabelField, torModel], fun _ => rfl⟩

/-- **Regression (audit AV-M8): the relabelled surfaces of the chart of `∇φ` are `FieldTorus`es
with rotation number `1`.** The parametrisation `θ ↦ θ − φ` winds once around the cross-section
per toroidal turn, so `FieldTorus` alone does not fix the rotational transform; the
poloidal-angle convention of `IotaOnTorus` does. -/
theorem torChart_relabel_fieldTorus {R₀ : ℝ} (hR₀ : 0 < R₀) {ψ : ℝ} (hψ : 0 < ψ) :
    FieldTorus toroidal (fun θ φ => torR R₀ ψ (θ - φ)) (fun θ φ => torZ ψ (θ - φ)) 1 where
  continuous_R := by unfold torR; fun_prop
  continuous_z := by unfold torZ; fun_prop
  R_pos _ _ := torR_pos hR₀ _ _
  per_θ_R θ φ := by
    simp only [torR]
    rw [show θ + 2 * π - φ = θ - φ + 2 * π by ring, cos_add_two_pi]
  per_θ_z θ φ := by
    simp only [torZ]
    rw [show θ + 2 * π - φ = θ - φ + 2 * π by ring, sin_add_two_pi]
  per_φ_R θ φ := by
    simp only [torR]
    rw [show θ - (φ + 2 * π) = θ - φ - 2 * π by ring, cos_sub_two_pi]
  per_φ_z θ φ := by
    simp only [torZ]
    rw [show θ - (φ + 2 * π) = θ - φ - 2 * π by ring, sin_sub_two_pi]
  flow θ φ := by
    obtain ⟨c, hc⟩ := (torChart_fieldTorus hR₀ hψ).flow (θ - φ) φ
    refine ⟨c, ?_⟩
    simp only [mul_zero, add_zero] at hc
    simp only [mul_one, add_sub_add_right_eq_sub]
    exact hc

/-! ## AV-M7: the only constructed trapped bounce is at model level -/

/-- **Regression (audit AV-M7): a trapped bounce exists at model level only.** The drift-mirror
model `driftMirror k` (`0 ≤ k ≤ 1/2`) has an explicit trapped bounce in the region `ψ ≤ 11`
(`Kinetic.Boozer.dm_trappedBounce`), with radial displacement `−2πk` per bounce. This model is
not shown to be the Boozer model of any field: no `BoozerChart` is constructed for it, and the
only field with a constructed chart (`∇φ`, `torBoozerChart`) has no trapped bounce. Clause C2 for
a field (`Contract.OmnigeneityContract`) therefore has no non-vacuous witness in the library. -/
theorem exists_trappedBounce_driftMirror {k : ℝ} (hk0 : 0 ≤ k) (hk : k ≤ 1 / 2) :
    ∃ (m q μ c τ : ℝ) (ψ θ φ ρ : ℝ → ℝ), 0 < m ∧ q ≠ 0 ∧ 0 ≤ μ ∧
      TrappedBounce (driftMirror k) m q μ c ψ θ φ ρ τ ∧ ψ τ - ψ 0 = -(2 * π * k) :=
  ⟨1, 1, 3 / 2, 11, π, dmψ k, dmθ, dmφ, dmρ, one_pos, one_ne_zero, by norm_num,
    dm_trappedBounce hk0 hk, dm_displacement k⟩

/-! ## AV-L1: `TorusQADefectLe` without regularity -/

/-- **Regression (audit AV-L1): a constant map satisfies `TorusQADefectLe` with bound `0`**, for
every field and every `ι`. The map `K = const` is not a torus, so the predicate alone is not a
quasisymmetry statement: consumers must add `FieldTorus`, differentiability of `|B| ∘ K` and
`J > 0`. -/
theorem torusQADefectLe_const (B : Space → Space) (ι : ℝ) (x₀ : Space) :
    TorusQADefectLe B ι (fun _ _ => x₀) 0 := fun θ φ => by
  simp [torusQADefect, boozerDeriv, thetaDeriv, lineDeriv, modB]

/-- **Regression (audit AV-L1): the zero field satisfies `TorusQADefectLe` with bound `0`** on
every map `K`, for every `ι` (here `|B| ∘ K = 0` and the Boozer Jacobian `J = B · 𝓛K` is `0`, so
the defect is a division by zero). The predicate alone is not a quasisymmetry statement. -/
theorem torusQADefectLe_zero_field (ι : ℝ) (K : ℝ → ℝ → Space) :
    TorusQADefectLe (fun _ => 0) ι K 0 := fun θ φ => by
  simp [torusQADefect, boozerDeriv, thetaDeriv, lineDeriv, modB]

end PlasmaLean.Sanity.AuditContractC2
