/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamANest
public import PlasmaLean.Design.DommaschkKamAConsts
public import PlasmaLean.Design.DommaschkKamCContract

/-!
# Clause C1 for the Dommaschk target from the exact torus A (nested certified region)

**On-demand module** (imports the on-demand `Design/DommaschkKamAConsts`,
`Design/DommaschkKamANest`, `Design/DommaschkKamCContract`). Build:
`lake build PlasmaLean.Design.DommaschkKamAContract`.

The torus-A analogue of `Design/DommaschkKamCContract`: an exact analytic real invariant torus of
the flow form of `dkFieldTC` with rotational transform `ι_A = −(19 + √5)/89` that is
`10⁻¹²`-close to the data torus A (`ExactTorusA`, the conclusion of `dk_exact_of_res` of
`Design/DommaschkKamAConsts`) is a `FieldTorus` of `DommaschkQA2R.field candidate`
(`ExactTorusA.fieldTorus`, the proof of `ExactTorusC.fieldTorus` with the torus-A constants).

**The common reference curve.** The poloidal angle is measured about the explicit curve
`R̄(φ) = R₀ + rU(2φ)`, `z̄(φ) = rZ(2φ)` (`Rref`, `Zref`): the `θ`-average of the low-resolution
surrogate of torus C (`Design/DommaschkKamANest`), the same curve for tori C and A. For torus A
the `ℓ¹` radial criterion of `Design/DommaschkKamCRadial` fails (float: tail `0.0322 > c₀ = 0.0310`
about its own average), so the radial condition `(R − R̄) cos θ + (z − z̄) sin θ > 0` comes from the
squared approximate inverse of the nesting chain (`radA_pos`, `radC_pos`), transferred to the
exact tori by `osc_close` (`μ`-closeness plus the tail certificates). `poloidalAngle_ref` turns it
into a `PoloidalAngle` (`Θ = angF θ (R − R̄) (z − z̄)`, `Θref`), for any analytic real torus.

**Results.**
* `ExactTorusA.iotaOnTorus : IotaOnTorus (field candidate) R z ι_A`, and
  `ExactTorusC.iotaOnTorusRef`: the exact torus C about the same reference curve;
* `dommaschkA_C1_of_exact`: C1 with `I_max = 0`, `ι_min = 0.2386` on `{surfaceA u z}`.
  **Note:** `|ι_A| = 0.238608 < 0.24`, so `ι_min = 6/25` is out of reach for torus A
  (`not_C1_iotaMin_A`); `0.2386` is the largest four-digit admissible value (`iotaA_ge`);
* `dommaschkA_C1`, `dommaschkA_iotaOnTorus`: conditional only on the initial residual bounds
  (`Design/DommaschkKamAFinal` removes them).

**Sanity.** `iotaA_ge`, `iotaA_lt` (concrete), `Rref_per` (periodicity), the rejected fixture
`not_C1_iotaMin_A`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Design.DommaschkKamC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Design.KamTorusA (psi angF angF_polar hasDerivAt_line hasDerivAt_toLp3
  cos_two_mul_eq sin_two_mul_eq)

/-! ## The common reference curve and the poloidal angle -/

/-- The common reference radius `R̄(φ) = R₀ + rU(2φ)` (the `θ`-average of the C surrogate). -/
def Rref (φ : ℝ) : ℝ := DommaschkKam.dkR0 + (eval rU 0 (2 * φ)).re

/-- The common reference height `z̄(φ) = rZ(2φ)`. -/
def Zref (φ : ℝ) : ℝ := (eval rZ 0 (2 * φ)).re

/-- The poloidal angle about the common reference curve. -/
def Θref (u z : FA) (θ φ : ℝ) : ℝ := angF θ (RofC u θ φ - Rref φ) (Zof z θ φ - Zref φ)

/-- `rU`, `rZ` are analytic. -/
theorem ana_rU : Ana rU := ana_thProj (DommaschkKamC.ana_xA 4)

/-- `rZ` is analytic. -/
theorem ana_rZ : Ana rZ := ana_thProj (DommaschkKamC.ana_xA 5)

/-- The reference radius is continuous. -/
theorem continuous_Rref : Continuous Rref :=
  continuous_const.add (Complex.continuous_re.comp
    ((continuous_evalP ana_rU).comp (continuous_const.prodMk (continuous_const.mul continuous_id))))

/-- The reference height is continuous. -/
theorem continuous_Zref : Continuous Zref :=
  Complex.continuous_re.comp
    ((continuous_evalP ana_rZ).comp (continuous_const.prodMk (continuous_const.mul continuous_id)))

/-- `2(φ + 2π) = 2φ + 2π + 2π`. -/
theorem two_mul_add (φ : ℝ) : 2 * (φ + 2 * Real.pi) = 2 * φ + 2 * Real.pi + 2 * Real.pi := by ring

/-- **Sanity**: the reference radius is `2π`-periodic. -/
theorem Rref_per (φ : ℝ) : Rref (φ + 2 * Real.pi) = Rref φ := by
  simp only [Rref, two_mul_add, eval_periodic_ψ]

/-- The reference height is `2π`-periodic. -/
theorem Zref_per (φ : ℝ) : Zref (φ + 2 * Real.pi) = Zref φ := by
  simp only [Zref, two_mul_add, eval_periodic_ψ]

/-- **Poloidal angle about the common reference curve** for any analytic torus satisfying the
radial condition. -/
theorem poloidalAngle_ref {u z : FA} (hu : Ana u) (hz : Ana z)
    (hrad : ∀ θ φ, 0 < (RofC u θ φ - Rref φ) * Real.cos θ + (Zof z θ φ - Zref φ) * Real.sin θ) :
    PoloidalAngle (RofC u) (Zof z) Rref Zref (Θref u z) where
  continuous_R₀ := continuous_Rref
  continuous_z₀ := continuous_Zref
  per_R₀ := Rref_per
  per_z₀ := Zref_per
  continuous := by
    have hR : Continuous fun p : ℝ × ℝ => RofC u p.1 p.2 := (contDiff_RofC hu).continuous
    have hZ : Continuous fun p : ℝ × ℝ => Zof z p.1 p.2 := (contDiff_Zof hz).continuous
    have hR0 : Continuous fun p : ℝ × ℝ => Rref p.2 := continuous_Rref.comp continuous_snd
    have hZ0 : Continuous fun p : ℝ × ℝ => Zref p.2 := continuous_Zref.comp continuous_snd
    have hnum : Continuous fun p : ℝ × ℝ =>
        (Zof z p.1 p.2 - Zref p.2) * Real.cos p.1 - (RofC u p.1 p.2 - Rref p.2) * Real.sin p.1 := by
      fun_prop
    have hden : Continuous fun p : ℝ × ℝ =>
        (RofC u p.1 p.2 - Rref p.2) * Real.cos p.1 + (Zof z p.1 p.2 - Zref p.2) * Real.sin p.1 := by
      fun_prop
    exact continuous_fst.add (Real.continuous_arctan.comp
      (hnum.div hden fun p => (hrad p.1 p.2).ne'))
  polar θ φ := by
    have hr := hrad θ φ
    set a := RofC u θ φ - Rref φ
    set b := Zof z θ φ - Zref φ
    have hab : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ), Real.sin_sq_add_cos_sq θ]
    exact ⟨√(a ^ 2 + b ^ 2), Real.sqrt_pos.mpr hab, (angF_polar hr).1, (angF_polar hr).2⟩
  wind_θ θ φ := by
    simp only [Θref, angF, RofC, Zof, eval_periodic_θ, Real.cos_add_two_pi, Real.sin_add_two_pi]
    ring
  wind_φ θ φ := by
    simp only [Θref, RofC, Zof, psi_add_two_pi, eval_periodic_ψ, Rref_per, Zref_per]

/-- The Lean-angle torus at `ψ(φ)` is the oracle-frame torus at `2φ`. -/
theorem eval_psi_rot (x : FA) (θ φ : ℝ) : eval x θ (psi φ) = eval (rotψi x) θ (2 * φ) := by
  conv_lhs => rw [← rotψ_rotψi x]
  rw [eval_rotψ]
  congr 1
  simp only [psi]; ring

/-- `rotψi` preserves reality. -/
theorem isReal_rotψi' {x : FA} (h : IsReal x) : IsReal (rotψi x) :=
  isReal_rotψ (isReal_rotψ (isReal_rotψ h))

/-- **Oracle-frame closeness**: a torus `μ`-close (strip `9/1400`) to `rotψ x₀` is, after
`rotψi`, within `μ + t` (`ℓ¹`) of any `s` with `‖x₀ − s‖₀ ≤ t`. -/
theorem osc_close {u x0 s : FA} {μ t : ℝ} (hc : Bd (9 / 1400) (u - rotψ x0) μ)
    (ht : Bd 0 (x0 - s) t) : Bd 0 (rotψi u - s) (μ + t) := by
  have h1 := Bd_rotψi (hc.strip (by norm_num : (0 : ℝ) ≤ 9 / 1400))
  rw [rotψi_sub, rotψi_rotψ] at h1
  have := h1.add ht
  rwa [show rotψi u - x0 + (x0 - s) = rotψi u - s by ring] at this

/-- The radial function of a torus in contract coordinates is the oracle-frame one. -/
theorem rad_contract (u z : FA) (θ φ : ℝ) :
    (RofC u θ φ - Rref φ) * Real.cos θ + (Zof z θ φ - Zref φ) * Real.sin θ =
      ((eval (rotψi u) θ (2 * φ)).re - (eval rU 0 (2 * φ)).re) * Real.cos θ +
        ((eval (rotψi z) θ (2 * φ)).re - (eval rZ 0 (2 * φ)).re) * Real.sin θ := by
  simp only [RofC, Rref, Zof, Zref, eval_psi_rot]; ring

/-! ## The exact torus A -/

/-- **The exact torus A** (the conclusion of `dk_exact_of_res` of `Design/DommaschkKamAConsts`):
a real analytic torus solving the flow form of `dkFieldTC` exactly with rotational transform
`ι_A`, `10⁻¹²`-close to the data torus A on the strip `9/1400`. -/
structure ExactTorusA (u z : FA) : Prop where
  /-- `u` is analytic. -/
  ana_u : Ana u
  /-- `z` is analytic. -/
  ana_z : Ana z
  /-- `u` is real. -/
  real_u : IsReal u
  /-- `z` is real. -/
  real_z : IsReal z
  /-- Exact invariance, `R`-component. -/
  resR : dkFieldTC.resR DommaschkKamDio.dkIotaA u z = 0
  /-- Exact invariance, `z`-component. -/
  resZ : dkFieldTC.resZ DommaschkKamDio.dkIotaA u z = 0
  /-- Closeness to the data torus A. -/
  close : Close (9 / 1400) DommaschkKamDio.dkIotaA u z u₀A z₀A (muq : ℝ)

namespace ExactTorusA

variable {u z : FA} (h : ExactTorusA u z)
include h

/-- The admissibility bounds hold at the exact torus (`dk_hadmC`, strip `9/1400`). -/
theorem adm : dkFieldTC.AdmBoundsG cDK DommaschkKamDio.dkIotaA (9 / 1400) u z :=
  dk_hadmC _ u z (by norm_num [cDK]) (by norm_num [cDK]) h.ana_u h.ana_z h.close

/-- `|R − R₀| ≤ 0.1586`. -/
theorem abs_Zof_u (θ φ : ℝ) : |Zof u θ φ| ≤ 31703 / 200000 := by
  have h1 := norm_eval_le_of_Bd (by norm_num) h.adm.hu θ (psi φ)
  have h2 := Complex.abs_re_le_norm (eval u θ (psi φ))
  have e : cDK.au = ((auC : ℚ) : ℝ) := rfl
  rw [e, auC] at h1
  unfold Zof
  push_cast at h1
  linarith

/-- The torus stays off the axis: `R ≥ 29/32 − 0.1586 > 0`. -/
theorem R_pos (θ φ : ℝ) : 0 < RofC u θ φ := by
  have := (abs_le.mp (h.abs_Zof_u θ φ)).1
  unfold RofC DommaschkKam.dkR0
  linarith

/-- The variables of the field polynomials at a point of the torus are `ptC R φ z`. -/
theorem eval_xB_pt (θ φ : ℝ) :
    (fun j => eval (xB u z j) θ (psi φ)) = DommaschkKam.ptC (RofC u θ φ) φ (Zof z θ φ) := by
  funext j
  fin_cases j
  · change eval u θ (psi φ) = (((RofC u θ φ - DommaschkKam.dkR0 : ℝ)) : ℂ)
    rw [RofC, add_sub_cancel_left, Zof, ← eval_ofReal_re h.real_u]
  · change eval z θ (psi φ) = ((Zof z θ φ : ℝ) : ℂ)
    rw [Zof, ← eval_ofReal_re h.real_z]
  · change eval cS θ (psi φ) = ((Real.cos (2 * φ) : ℝ) : ℂ)
    rw [eval_cS, cos_two_mul_eq]; push_cast; ring
  · change eval sS θ (psi φ) = ((Real.sin (2 * φ) : ℝ) : ℂ)
    rw [eval_sS, sin_two_mul_eq]
  · change eval 0 θ (psi φ) = 0; simp
  · change eval 0 θ (psi φ) = 0; simp

/-- `D(K) = R⁷ B_φ` on the torus. -/
theorem eval_Dof (θ φ : ℝ) : eval (dkFieldTC.Dof u z) θ (psi φ) =
    ((RofC u θ φ ^ 7 * DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) : ℝ) : ℂ) := by
  rw [FlowFieldG.Dof, eval_polyExpr, h.eval_xB_pt]
  exact DommaschkKam.Dp_ident (h.R_pos θ φ) φ _

/-- **`B_φ ≠ 0` on the torus** (`D` is a unit of the strip algebra). -/
theorem Bphi_ne (θ φ : ℝ) : DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) ≠ 0 := by
  obtain ⟨b, hb⟩ := h.adm.frame.unit_D.exists_right_inv
  have h1 := congrArg (fun x => eval x θ (psi φ)) hb
  simp only [WEll1Z2.eval_mul, eval_one] at h1
  rw [h.eval_Dof] at h1
  intro h0
  rw [h0, mul_zero, Complex.ofReal_zero, zero_mul] at h1
  exact zero_ne_one h1

/-- **Exact invariance, `R`-component, pointwise**: `R⁷B_φ (∂_φR + ι ∂_θR) = R⁸B_R`. -/
theorem inv_R (θ φ : ℝ) :
    RofC u θ φ ^ 7 * DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) *
        (deriv (fun φ' => RofC u θ φ') φ +
          DommaschkKamDio.dkIotaA * deriv (fun θ' => RofC u θ' φ) θ) =
      RofC u θ φ ^ 8 * DommaschkKam.cylBR (RofC u θ φ) φ (Zof z θ φ) := by
  have h0 := congrArg (fun x => eval x θ (psi φ)) h.resR
  simp only [eval_zero'] at h0
  rw [FlowFieldG.resR_eq, eval_sub', WEll1Z2.eval_mul, h.eval_Dof,
    eval_Lt_real h.ana_u h.real_u, eval_polyExpr, h.eval_xB_pt,
    show dkFieldTC.nRp = DommaschkKam.nRp from rfl, DommaschkKam.nRp_ident (h.R_pos θ φ)] at h0
  rw [(hasDerivAt_RofC_φ h.ana_u θ φ).deriv, (hasDerivAt_RofC_θ h.ana_u θ φ).deriv]
  exact_mod_cast sub_eq_zero.mp h0

/-- **Exact invariance, `z`-component, pointwise**: `R⁷B_φ (∂_φz + ι ∂_θz) = R⁸B_z`. -/
theorem inv_Z (θ φ : ℝ) :
    RofC u θ φ ^ 7 * DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) *
        (deriv (fun φ' => Zof z θ φ') φ +
          DommaschkKamDio.dkIotaA * deriv (fun θ' => Zof z θ' φ) θ) =
      RofC u θ φ ^ 8 * DommaschkKam.cylBz (RofC u θ φ) φ (Zof z θ φ) := by
  have h0 := congrArg (fun x => eval x θ (psi φ)) h.resZ
  simp only [eval_zero'] at h0
  rw [FlowFieldG.resZ_eq, eval_sub', WEll1Z2.eval_mul, h.eval_Dof,
    eval_Lt_real h.ana_z h.real_z, eval_polyExpr, h.eval_xB_pt,
    show dkFieldTC.nZp = DommaschkKam.nZp from rfl, DommaschkKam.nZp_ident (h.R_pos θ φ)] at h0
  rw [(hasDerivAt_Zof_φ h.ana_z θ φ).deriv, (hasDerivAt_Zof_θ h.ana_z θ φ).deriv]
  exact_mod_cast sub_eq_zero.mp h0

/-- **The exact torus is a `FieldTorus` of `field candidate` with rotation number `ι_A`**. -/
theorem fieldTorus :
    FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z)
      DommaschkKamDio.dkIotaA where
  continuous_R := (contDiff_RofC h.ana_u).continuous
  continuous_z := (contDiff_Zof h.ana_z).continuous
  R_pos := h.R_pos
  per_θ_R θ φ := by simp only [RofC, Zof, eval_periodic_θ]
  per_θ_z θ φ := by simp only [Zof, eval_periodic_θ]
  per_φ_R θ φ := by simp only [RofC, Zof, psi_add_two_pi, eval_periodic_ψ]
  per_φ_z θ φ := by simp only [Zof, psi_add_two_pi, eval_periodic_ψ]
  flow θ φ := by
    set ι := DommaschkKamDio.dkIotaA
    have hdR : Differentiable ℝ (fun p : ℝ × ℝ => RofC u p.1 p.2) :=
      (contDiff_RofC h.ana_u).differentiable (by norm_num)
    have hdZ : Differentiable ℝ (fun p : ℝ × ℝ => Zof z p.1 p.2) :=
      (contDiff_Zof h.ana_z).differentiable (by norm_num)
    have hLR := hasDerivAt_line hdR θ φ ι 1
    have hLZ := hasDerivAt_line hdZ θ φ ι 1
    simp only [mul_one, one_mul] at hLR hLZ
    have hφ : HasDerivAt (fun t : ℝ => φ + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add φ
    have hd := hasDerivAt_toLp3 (hLR.mul hφ.cos) (hLR.mul hφ.sin) hLZ
    have hR := h.R_pos θ φ
    have hB := h.Bphi_ne θ φ
    have hIR := h.inv_R θ φ
    have hIZ := h.inv_Z θ φ
    set R := RofC u θ φ
    set Bp := DommaschkKam.cylBphi R φ (Zof z θ φ) with hBp
    set BR := DommaschkKam.cylBR R φ (Zof z θ φ) with hBR
    set BZ := DommaschkKam.cylBz R φ (Zof z θ φ) with hBZ
    set La := ι * deriv (fun θ' => RofC u θ' φ) θ + deriv (fun φ' => RofC u θ φ') φ with hLa
    set Lb := ι * deriv (fun θ' => Zof z θ' φ) θ + deriv (fun φ' => Zof z θ φ') φ with hLb
    have hR7 : R ^ 7 ≠ 0 := pow_ne_zero _ hR.ne'
    have eLa : La * Bp = R * BR := by
      apply mul_left_cancel₀ hR7
      rw [hLa]; linear_combination hIR
    have eLb : Lb * Bp = R * BZ := by
      apply mul_left_cancel₀ hR7
      rw [hLb]; linear_combination hIZ
    set F := DommaschkQA2R.field DommaschkQA2R.candidate (cylPoint R φ (Zof z θ φ)) with hF
    have hB0 : F 0 = Real.cos φ * BR - Real.sin φ * Bp := by
      simp only [hBR, hBp, DommaschkKam.cylBR, DommaschkKam.cylBphi, hF]
      linear_combination (-(F 0)) * Real.sin_sq_add_cos_sq φ
    have hB1 : F 1 = Real.sin φ * BR + Real.cos φ * Bp := by
      simp only [hBR, hBp, DommaschkKam.cylBR, DommaschkKam.cylBphi, hF]
      linear_combination (-(F 1)) * Real.sin_sq_add_cos_sq φ
    have hB2 : F 2 = BZ := by simp only [hBZ, DommaschkKam.cylBz, hF]
    refine ⟨R / Bp, hd.congr_deriv ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul, hB0]
      simp
      field_simp
      linear_combination (Real.cos φ) * eLa
    · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul, hB1]
      simp
      field_simp
      linear_combination (Real.sin φ) * eLa
    · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.smul_apply, smul_eq_mul, hB2]
      simp
      field_simp
      linear_combination eLb

/-- The oracle-frame torus is within `10⁻¹⁰` of the A surrogate (`U`). -/
theorem osc_U : Bd 0 (rotψi u - xA 4) (1 / 10 ^ 10) := by
  have hq : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num
  have ht := Bd_tg_U hq
  rw [← Uo_sub_xA] at ht
  exact (osc_close h.close.du ht).le (by norm_num [muq, tU])

/-- The oracle-frame torus is within `10⁻¹⁰` of the A surrogate (`z`). -/
theorem osc_Z : Bd 0 (rotψi z - xA 5) (1 / 10 ^ 10) := by
  have hq : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num
  have ht := Bd_tg_Z hq
  rw [← Zo_sub_xA] at ht
  exact (osc_close h.close.dz ht).le (by norm_num [muq, tZ])

/-- **The radial condition** about the common reference curve. -/
theorem radial_pos (θ φ : ℝ) :
    0 < (RofC u θ φ - Rref φ) * Real.cos θ + (Zof z θ φ - Zref φ) * Real.sin θ := by
  rw [rad_contract]
  exact radA_pos (isReal_rotψi' h.real_u) (isReal_rotψi' h.real_z) h.osc_U h.osc_Z θ (2 * φ)

/-- **The poloidal angle** of the exact torus A about the common reference curve. -/
theorem poloidalAngle : PoloidalAngle (RofC u) (Zof z) Rref Zref (Θref u z) :=
  poloidalAngle_ref h.ana_u h.ana_z h.radial_pos

/-- **The exact torus A has rotational transform `ι_A` in the sense of the contract.** -/
theorem iotaOnTorus :
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z)
      DommaschkKamDio.dkIotaA :=
  ⟨h.fieldTorus, Rref, Zref, Θref u z, h.poloidalAngle⟩

end ExactTorusA

/-! ## Torus C about the common reference curve -/

namespace ExactTorusC'

variable {u z : FA} (h : DommaschkKamC.ExactTorusC u z)
include h

/-- The oracle-frame torus C is within `10⁻¹⁰` of the C surrogate (`U`). -/
theorem osc_U : Bd 0 (rotψi u - DommaschkKamC.xA 4) (1 / 10 ^ 10) := by
  have hq : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num
  have ht := DommaschkKamC.Bd_tg_U hq
  rw [← DommaschkKamC.Uo_sub_xA] at ht
  exact (osc_close h.close.du ht).le (by norm_num [DommaschkKamC.muq, DommaschkKamC.tU])

/-- The oracle-frame torus C is within `10⁻¹⁰` of the C surrogate (`z`). -/
theorem osc_Z : Bd 0 (rotψi z - DommaschkKamC.xA 5) (1 / 10 ^ 10) := by
  have hq : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num
  have ht := DommaschkKamC.Bd_tg_Z hq
  rw [← DommaschkKamC.Zo_sub_xA] at ht
  exact (osc_close h.close.dz ht).le (by norm_num [DommaschkKamC.muq, DommaschkKamC.tZ])

/-- The radial condition of torus C about the common reference curve. -/
theorem radial_pos (θ φ : ℝ) :
    0 < (RofC u θ φ - Rref φ) * Real.cos θ + (Zof z θ φ - Zref φ) * Real.sin θ := by
  rw [rad_contract]
  exact radC_pos (isReal_rotψi' h.real_u) (isReal_rotψi' h.real_z) (osc_U h) (osc_Z h) θ (2 * φ)

/-- The poloidal angle of the exact torus C about the common reference curve. -/
theorem poloidalAngle : PoloidalAngle (RofC u) (Zof z) Rref Zref (Θref u z) :=
  poloidalAngle_ref h.ana_u h.ana_z (radial_pos h)

/-- **The exact torus C has rotational transform `ι_C` about the common reference curve.** -/
theorem iotaOnTorusRef :
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z)
      DommaschkKamDio.dkIotaC :=
  ⟨h.fieldTorus, Rref, Zref, Θref u z, poloidalAngle h⟩

end ExactTorusC'

/-! ## Clause C1 for torus A -/

/-- The C1 surface data of a torus `(u, z)` with transform `ι_A` (poloidal loop at `φ = 0`). -/
def surfaceA (u z : FA) : SurfaceData where
  R := RofC u
  z := Zof z
  iota := DommaschkKamDio.dkIotaA
  φ₀ := 0

/-- **Sanity (concrete)**: `|ι_A| = (19 + √5)/89 ≥ 0.2386`. -/
theorem iotaA_ge : (1193 / 5000 : ℝ) ≤ |DommaschkKamDio.dkIotaA| := by
  have h5 : (22354 / 10000 : ℝ) ≤ √5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [DommaschkKamDio.dkIotaA, abs_neg, abs_of_pos (by positivity)]
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- **Sanity (concrete)**: `|ι_A| < 0.24`. -/
theorem iotaA_lt : |DommaschkKamDio.dkIotaA| < 6 / 25 := by
  have h5 : √5 < 2237 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [DommaschkKamDio.dkIotaA, abs_neg, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- **C1 from the exact torus A**: clause C1 holds for `field candidate` with `I_max = 0` and
`ι_min = 0.2386` on the one-surface family `{surfaceA u z}`, for every `μ₀ > 0`. -/
theorem dommaschkA_C1_of_exact {u z : FA} (h : ExactTorusA u z) {μ₀ : ℝ} (hμ : 0 < μ₀) :
    CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {surfaceA u z} 0
      (1193 / 5000) :=
  DommaschkQA2R.candidate_currentFreeTransform hμ (Set.singleton_nonempty _) (by norm_num)
    (by rintro s rfl; exact h.iotaOnTorus)
    (by
      rintro s rfl
      exact ((contDiff_RofC h.ana_u).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num))
    (by
      rintro s rfl
      exact ((contDiff_Zof h.ana_z).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num))
    (by rintro s rfl; exact iotaA_ge)

/-- **Rejected fixture**: torus A does not certify `ι_min = 0.24` (`|ι_A| < 0.24`). -/
theorem not_C1_iotaMin_A {u z : FA} {μ₀ : ℝ} :
    ¬ CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {surfaceA u z} 0
      (6 / 25) := fun hC => by
  have := hC.iota_ge (surfaceA u z) rfl
  exact absurd this (not_le.mpr iotaA_lt)

/-- **The Dommaschk target has rotational transform `ι_A` on an exact invariant torus**,
conditional on the initial residual bounds of the KAM iteration for torus A. -/
theorem dommaschkA_iotaOnTorus
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ)) :
    ∃ R z : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z DommaschkKamDio.dkIotaA := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res e0R e0Z
  exact ⟨_, _, ExactTorusA.iotaOnTorus ⟨hu, hz, hur, hzr, hR, hZ, hC⟩⟩

/-- **Clause C1 for the Dommaschk target from torus A**, conditional only on the initial residual
bounds `e0R`, `e0Z` of the data torus A. -/
theorem dommaschkA_C1
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaA u₀A z₀A) (e0qDK : ℝ))
    {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 (1193 / 5000) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res e0R e0Z
  exact ⟨_, dommaschkA_C1_of_exact ⟨hu, hz, hur, hzr, hR, hZ, hC⟩ hμ⟩

end PlasmaLean.Design.DommaschkKamA
