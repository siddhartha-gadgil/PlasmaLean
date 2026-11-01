/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCRadial
public import PlasmaLean.Design.DommaschkKamCConsts
public import PlasmaLean.Design.DommaschkKamIdent
public import PlasmaLean.Theory.Contract.StellaratorContract
public import PlasmaLean.Design.DommaschkQA2R

/-!
# Clause C1 for the Dommaschk target from the exact torus C (N-33 plan item 10)

**On-demand module** (imports the on-demand `Design/DommaschkKamCConsts`). Build:
`lake build PlasmaLean.Design.DommaschkKamCContract`.

The contract link: an exact analytic real invariant torus of the flow form of `dkFieldTC`
(`resR = resZ = 0`, rotational transform `ι_C = −(85 + √5)/361`) that is `10⁻¹²`-close to the
data torus C (`ExactTorusC`, the conclusion of `dk_exact_of_res`) gives clause C1 of the
stellarator contract for the exact field `DommaschkQA2R.field candidate`.

**The real torus.** `R(θ, φ) = R₀ + Re u(θ, ψ(φ))` (`RofC`, `R₀ = 29/32`),
`z(θ, φ) = Re z(θ, ψ(φ))` (`KamNewton.Zof`), with the strip-algebra angle `ψ = 2φ − π/2`
(`KamTorusA.psi`; `cS = cos 2φ = −sin ψ`, `sS = sin 2φ = cos ψ`); `C²`, `2π`-periodic in both
angles (`π`-periodic in `φ`).

**`FieldTorus`** (`ExactTorusC.fieldTorus`). Evaluating `resR = D 𝓛u − n_R = 0` at `(θ, ψ(φ))`
gives `D(K) (∂_φR + ι ∂_θR) = n_R(K)` pointwise (`ExactTorusC.inv_R`, `inv_Z`), and the
identification `Dp_ident`, `nRp_ident`, `nZp_ident` (`Design/DommaschkKamIdent`) turns it into
`R⁷B_φ · Ṙ = R⁸B_R`, `R⁷B_φ · ż = R⁸B_z`. `D` is a unit of the strip algebra (the frame field
`unit_D` of `AdmBoundsG`, `dk_hadmC`), so `B_φ ≠ 0` on the torus (`Bphi_ne`), and the image of
each line `t ↦ (θ + ι t, φ + t)` has velocity `(R/B_φ) • B`. `R > 0` from `‖u‖ ≤ 0.1378`
(`hu` of `AdmBoundsG`).

**`PoloidalAngle`** (`ExactTorusC.poloidalAngle`). The reference curve is the `θ`-average of the
torus, `R̄(φ) = R₀ + Re ū(ψ(φ))`, `z̄(φ) = Re z̄(ψ(φ))` (`R0refC`, `Z0refC`; `thProj`, a continuous
`2π`-periodic curve inside each cross-section), and the angle is the smooth lift
`Θ = angF θ (R − R̄) (z − z̄)` (`ΘC`), a polar angle of `(R − R̄, z − z̄)` by the radial condition
`(R − R̄) cos θ + (z − z̄) sin θ ≥ 0.002` (`radial_ge_of_close`, `Design/DommaschkKamCRadial`), with
`Θ(θ + 2π, φ) = Θ + 2π` and `Θ(θ, φ + 2π) = Θ`. (About the moving centre `cenR`, `cenZ` of the
KAM frame the same `ℓ¹` criterion fails: tail `0.0282 > c₀ = 0.0232`, float estimate; the
contract accepts any continuous periodic reference curve.)

**Results.**
* `ExactTorusC.iotaOnTorus : IotaOnTorus (field candidate) R z ι_C`;
* `dommaschk_C1_of_exact`: C1 with `I_max = 0`, `ι_min = 0.24` on the one-surface family
  (`surfaceC`, poloidal loop at `φ = 0`), for every `μ₀ > 0`, via
  `candidate_currentFreeTransform` (zero loop current: `candidate_loopCurrent_eq_zero`);
* **`dommaschk_C1`** `(e0R) (e0Z)`: `∃ S, CurrentFreeTransform μ₀ (field candidate) S 0 0.24`,
  conditional only on the initial residual bounds of `dk_exact_of_res` (the high-resolution
  residual chain); `dommaschk_iotaOnTorus` likewise.

**Sanity.** `iotaC_ge` (`|ι_C| ≥ 0.24`, concrete), `iotaC_lt` (`|ι_C| < 0.25`: `ι_min = 0.25` is
out of reach), `RofC_zero` (degenerate: the zero torus is the circle `R = R₀`), and the rejected
fixture `not_C1_iotaMin` (no family certifies `ι_min > |ι_C|` through this torus alone).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Design.KamTorusA (psi angF angF_polar hasDerivAt_line hasDerivAt_toLp3
  cos_two_mul_eq sin_two_mul_eq)

/-! ## The real torus and the reference curve -/

/-- `R(θ, φ) = R₀ + Re u(θ, ψ(φ))` of a torus `u = R − R₀` of the strip algebra. -/
def RofC (u : FA) (θ φ : ℝ) : ℝ := DommaschkKam.dkR0 + Zof u θ φ

/-- The reference radius: `R₀ + Re ū(ψ(φ))`, `ū` the `θ`-average of `u`. -/
def R0refC (u : FA) (φ : ℝ) : ℝ := DommaschkKam.dkR0 + (eval (thProj u) 0 (psi φ)).re

/-- The reference height: `Re z̄(ψ(φ))`, `z̄` the `θ`-average of `z`. -/
def Z0refC (z : FA) (φ : ℝ) : ℝ := (eval (thProj z) 0 (psi φ)).re

/-- The poloidal angle: the smooth polar angle of `(R − R̄, z − z̄)` near the direction `θ`. -/
def ΘC (u z : FA) (θ φ : ℝ) : ℝ := angF θ (RofC u θ φ - R0refC u φ) (Zof z θ φ - Z0refC z φ)

/-- `ψ(φ + 2π) = ψ(φ) + 2π + 2π`. -/
theorem psi_add_two_pi (φ : ℝ) : psi (φ + 2 * Real.pi) = psi φ + 2 * Real.pi + 2 * Real.pi := by
  simp only [psi]; ring

/-- `ψ` is continuous. -/
theorem continuous_psi : Continuous psi := by unfold psi; fun_prop

/-- **Sanity (degenerate)**: the zero torus is the circle `R = R₀`. -/
theorem RofC_zero (θ φ : ℝ) : RofC 0 θ φ = 29 / 32 := by
  simp [RofC, Zof, DommaschkKam.dkR0]

/-- `R` is `C²`. -/
theorem contDiff_RofC {u : FA} (hu : Ana u) : ContDiff ℝ 2 (fun p : ℝ × ℝ => RofC u p.1 p.2) :=
  contDiff_const.add (contDiff_Zof hu)

/-- `θ`-derivative of `R`. -/
theorem hasDerivAt_RofC_θ {u : FA} (hu : Ana u) (θ φ : ℝ) :
    HasDerivAt (fun θ' => RofC u θ' φ) (eval (dTh u) θ (psi φ)).re θ :=
  (hasDerivAt_Zof_θ hu θ φ).const_add _

/-- `φ`-derivative of `R`. -/
theorem hasDerivAt_RofC_φ {u : FA} (hu : Ana u) (θ φ : ℝ) :
    HasDerivAt (fun φ' => RofC u θ φ') (eval (dPh u) θ (psi φ)).re φ :=
  (hasDerivAt_Zof_φ hu θ φ).const_add _

/-- The reference radius is continuous. -/
theorem continuous_R0refC {u : FA} (hu : Ana u) : Continuous (R0refC u) :=
  continuous_const.add (Complex.continuous_re.comp
    ((continuous_evalP (ana_thProj hu)).comp (continuous_const.prodMk continuous_psi)))

/-- The reference height is continuous. -/
theorem continuous_Z0refC {z : FA} (hz : Ana z) : Continuous (Z0refC z) :=
  Complex.continuous_re.comp
    ((continuous_evalP (ana_thProj hz)).comp (continuous_const.prodMk continuous_psi))

/-- The transport `𝓛x = ι ∂_θx + ∂_φx` of a real analytic `x` at `(θ, ψ(φ))` is the real
derivative along the line of slope `ι`. -/
theorem eval_Lt_real {x : FA} (hx : Ana x) (hxr : IsReal x) (ι θ φ : ℝ) :
    eval (Lt ι x) θ (psi φ) =
      (((eval (dPh x) θ (psi φ)).re + ι * (eval (dTh x) θ (psi φ)).re : ℝ) : ℂ) := by
  have hdP : IsReal (dPh x) := by
    have := hxr.dS 0 2; change IsReal (dS 0 2 x); norm_num at this; exact this
  have h1 := (isReal_dTh hxr).eval_im θ (psi φ)
  have h2 := hdP.eval_im θ (psi φ)
  rw [Lt_eq ι hx, eval_add', eval_smul']
  apply Complex.ext
  · simp [h1]; ring
  · simp [h1, h2]

/-! ## The exact torus -/

/-- **The exact torus C** (the conclusion of `dk_exact_of_res`): a real analytic torus solving the
flow form of `dkFieldTC` exactly with rotational transform `ι_C`, `10⁻¹²`-close to the data torus
on the strip `9/1400`. -/
structure ExactTorusC (u z : FA) : Prop where
  /-- `u` is analytic. -/
  ana_u : Ana u
  /-- `z` is analytic. -/
  ana_z : Ana z
  /-- `u` is real. -/
  real_u : IsReal u
  /-- `z` is real. -/
  real_z : IsReal z
  /-- Exact invariance, `R`-component. -/
  resR : dkFieldTC.resR DommaschkKamDio.dkIotaC u z = 0
  /-- Exact invariance, `z`-component. -/
  resZ : dkFieldTC.resZ DommaschkKamDio.dkIotaC u z = 0
  /-- Closeness to the data torus C. -/
  close : Close (9 / 1400) DommaschkKamDio.dkIotaC u z u₀C z₀C (muq : ℝ)

namespace ExactTorusC

variable {u z : FA} (h : ExactTorusC u z)
include h

/-- The admissibility bounds hold at the exact torus (`dk_hadmC`, strip `9/1400`). -/
theorem adm : dkFieldTC.AdmBoundsG cDK DommaschkKamDio.dkIotaC (9 / 1400) u z :=
  dk_hadmC _ u z (by norm_num [cDK]) (by norm_num [cDK]) h.ana_u h.ana_z h.close

/-- `|R − R₀| ≤ 0.1378`. -/
theorem abs_Zof_u (θ φ : ℝ) : |Zof u θ φ| ≤ 5509 / 40000 := by
  have h1 := norm_eval_le_of_Bd (by norm_num) h.adm.hu θ (psi φ)
  have h2 := Complex.abs_re_le_norm (eval u θ (psi φ))
  have e : cDK.au = ((auC : ℚ) : ℝ) := rfl
  rw [e, auC] at h1
  unfold Zof
  push_cast at h1
  linarith

/-- The torus stays off the axis: `R ≥ 29/32 − 0.1378 > 0`. -/
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
  simp only [eval_mul, eval_one] at h1
  rw [h.eval_Dof] at h1
  intro h0
  rw [h0, mul_zero, Complex.ofReal_zero, zero_mul] at h1
  exact zero_ne_one h1

/-- **Exact invariance, `R`-component, pointwise**: `R⁷B_φ (∂_φR + ι ∂_θR) = R⁸B_R`. -/
theorem inv_R (θ φ : ℝ) :
    RofC u θ φ ^ 7 * DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) *
        (deriv (fun φ' => RofC u θ φ') φ +
          DommaschkKamDio.dkIotaC * deriv (fun θ' => RofC u θ' φ) θ) =
      RofC u θ φ ^ 8 * DommaschkKam.cylBR (RofC u θ φ) φ (Zof z θ φ) := by
  have h0 := congrArg (fun x => eval x θ (psi φ)) h.resR
  simp only [eval_zero'] at h0
  rw [FlowFieldG.resR_eq, eval_sub', eval_mul, h.eval_Dof, eval_Lt_real h.ana_u h.real_u,
    eval_polyExpr, h.eval_xB_pt, show dkFieldTC.nRp = DommaschkKam.nRp from rfl,
    DommaschkKam.nRp_ident (h.R_pos θ φ)] at h0
  rw [(hasDerivAt_RofC_φ h.ana_u θ φ).deriv, (hasDerivAt_RofC_θ h.ana_u θ φ).deriv]
  exact_mod_cast sub_eq_zero.mp h0

/-- **Exact invariance, `z`-component, pointwise**: `R⁷B_φ (∂_φz + ι ∂_θz) = R⁸B_z`. -/
theorem inv_Z (θ φ : ℝ) :
    RofC u θ φ ^ 7 * DommaschkKam.cylBphi (RofC u θ φ) φ (Zof z θ φ) *
        (deriv (fun φ' => Zof z θ φ') φ +
          DommaschkKamDio.dkIotaC * deriv (fun θ' => Zof z θ' φ) θ) =
      RofC u θ φ ^ 8 * DommaschkKam.cylBz (RofC u θ φ) φ (Zof z θ φ) := by
  have h0 := congrArg (fun x => eval x θ (psi φ)) h.resZ
  simp only [eval_zero'] at h0
  rw [FlowFieldG.resZ_eq, eval_sub', eval_mul, h.eval_Dof, eval_Lt_real h.ana_z h.real_z,
    eval_polyExpr, h.eval_xB_pt, show dkFieldTC.nZp = DommaschkKam.nZp from rfl,
    DommaschkKam.nZp_ident (h.R_pos θ φ)] at h0
  rw [(hasDerivAt_Zof_φ h.ana_z θ φ).deriv, (hasDerivAt_Zof_θ h.ana_z θ φ).deriv]
  exact_mod_cast sub_eq_zero.mp h0

/-- **The exact torus is a `FieldTorus` of `field candidate` with rotation number `ι_C`**: the
image of each line `t ↦ (θ + ι_C t, φ + t)` has velocity `(R/B_φ) • B`. -/
theorem fieldTorus :
    FieldTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z)
      DommaschkKamDio.dkIotaC where
  continuous_R := (contDiff_RofC h.ana_u).continuous
  continuous_z := (contDiff_Zof h.ana_z).continuous
  R_pos := h.R_pos
  per_θ_R θ φ := by simp only [RofC, Zof, eval_periodic_θ]
  per_θ_z θ φ := by simp only [Zof, eval_periodic_θ]
  per_φ_R θ φ := by simp only [RofC, Zof, psi_add_two_pi, eval_periodic_ψ]
  per_φ_z θ φ := by simp only [Zof, psi_add_two_pi, eval_periodic_ψ]
  flow θ φ := by
    set ι := DommaschkKamDio.dkIotaC
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

/-- `‖u − u₀C‖ ≤ 10⁻¹²` in `ℓ¹`. -/
theorem Bd_du : Bd 0 (u - u₀C) (1 / 10 ^ 12) :=
  (h.close.du.strip (by norm_num)).le (by norm_num [muq])

/-- `‖z − z₀C‖ ≤ 10⁻¹²` in `ℓ¹`. -/
theorem Bd_dz : Bd 0 (z - z₀C) (1 / 10 ^ 12) :=
  (h.close.dz.strip (by norm_num)).le (by norm_num [muq])

/-- **The radial condition** about the `θ`-average: `(R − R̄) cos θ + (z − z̄) sin θ > 0.002`. -/
theorem radial_pos (θ φ : ℝ) :
    0 < (RofC u θ φ - R0refC u φ) * Real.cos θ + (Zof z θ φ - Z0refC z φ) * Real.sin θ := by
  have hg := radial_ge_of_close h.real_u h.real_z h.Bd_du h.Bd_dz θ (psi φ)
  have hm : ((1 / 500 : ℚ) : ℝ) < (radMargin : ℝ) := Rat.cast_lt.mpr radMargin_pos
  push_cast at hm
  have e1 : RofC u θ φ - R0refC u φ =
      (eval u θ (psi φ)).re - (eval (thProj u) 0 (psi φ)).re := by
    simp only [RofC, R0refC, Zof]; ring
  have e2 : Zof z θ φ - Z0refC z φ =
      (eval z θ (psi φ)).re - (eval (thProj z) 0 (psi φ)).re := rfl
  rw [e1, e2]
  linarith

/-- **The poloidal angle** of the exact torus about its `θ`-average. -/
theorem poloidalAngle : PoloidalAngle (RofC u) (Zof z) (R0refC u) (Z0refC z) (ΘC u z) where
  continuous_R₀ := continuous_R0refC h.ana_u
  continuous_z₀ := continuous_Z0refC h.ana_z
  per_R₀ φ := by simp only [R0refC, psi_add_two_pi, eval_periodic_ψ]
  per_z₀ φ := by simp only [Z0refC, psi_add_two_pi, eval_periodic_ψ]
  continuous := by
    have hR : Continuous fun p : ℝ × ℝ => RofC u p.1 p.2 := (contDiff_RofC h.ana_u).continuous
    have hZ : Continuous fun p : ℝ × ℝ => Zof z p.1 p.2 := (contDiff_Zof h.ana_z).continuous
    have hR0 : Continuous fun p : ℝ × ℝ => R0refC u p.2 :=
      (continuous_R0refC h.ana_u).comp continuous_snd
    have hZ0 : Continuous fun p : ℝ × ℝ => Z0refC z p.2 :=
      (continuous_Z0refC h.ana_z).comp continuous_snd
    have hnum : Continuous fun p : ℝ × ℝ =>
        (Zof z p.1 p.2 - Z0refC z p.2) * Real.cos p.1 -
          (RofC u p.1 p.2 - R0refC u p.2) * Real.sin p.1 := by fun_prop
    have hden : Continuous fun p : ℝ × ℝ =>
        (RofC u p.1 p.2 - R0refC u p.2) * Real.cos p.1 +
          (Zof z p.1 p.2 - Z0refC z p.2) * Real.sin p.1 := by fun_prop
    exact continuous_fst.add (Real.continuous_arctan.comp
      (hnum.div hden fun p => (h.radial_pos p.1 p.2).ne'))
  polar θ φ := by
    have hr := h.radial_pos θ φ
    set a := RofC u θ φ - R0refC u φ
    set b := Zof z θ φ - Z0refC z φ
    have hab : 0 < a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a * Real.sin θ - b * Real.cos θ), Real.sin_sq_add_cos_sq θ]
    exact ⟨√(a ^ 2 + b ^ 2), Real.sqrt_pos.mpr hab, (angF_polar hr).1, (angF_polar hr).2⟩
  wind_θ θ φ := by
    simp only [ΘC, angF, RofC, Zof, eval_periodic_θ, Real.cos_add_two_pi, Real.sin_add_two_pi]
    ring
  wind_φ θ φ := by
    simp only [ΘC, RofC, R0refC, Zof, Z0refC, psi_add_two_pi, eval_periodic_ψ]

/-- **The exact torus C has rotational transform `ι_C` in the sense of the contract.** -/
theorem iotaOnTorus :
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC u) (Zof z)
      DommaschkKamDio.dkIotaC :=
  ⟨h.fieldTorus, R0refC u, Z0refC z, ΘC u z, h.poloidalAngle⟩

end ExactTorusC

/-! ## Clause C1 -/

/-- The C1 surface data of a torus `(u, z)` with transform `ι_C` (poloidal loop at `φ = 0`). -/
def surfaceC (u z : FA) : SurfaceData where
  R := RofC u
  z := Zof z
  iota := DommaschkKamDio.dkIotaC
  φ₀ := 0

/-- **Sanity (concrete)**: `|ι_C| = (85 + √5)/361 ≥ 0.24`. -/
theorem iotaC_ge : (6 / 25 : ℝ) ≤ |DommaschkKamDio.dkIotaC| := by
  have h5 : (41 / 25 : ℝ) ≤ √5 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  rw [DommaschkKamDio.dkIotaC, abs_neg, abs_of_pos (by positivity)]
  rw [le_div_iff₀ (by norm_num)]
  linarith

/-- **Sanity (concrete)**: `|ι_C| < 0.25`. -/
theorem iotaC_lt : |DommaschkKamDio.dkIotaC| < 1 / 4 := by
  have h5 : √5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [DommaschkKamDio.dkIotaC, abs_neg, abs_of_pos (by positivity)]
  rw [div_lt_iff₀ (by norm_num)]
  linarith

/-- **C1 from the exact torus**: clause C1 holds for `field candidate` with `I_max = 0` and
`ι_min = 0.24` on the one-surface family `{surfaceC u z}`, for every `μ₀ > 0`. -/
theorem dommaschk_C1_of_exact {u z : FA} (h : ExactTorusC u z) {μ₀ : ℝ} (hμ : 0 < μ₀) :
    CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {surfaceC u z} 0
      (6 / 25) :=
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
    (by rintro s rfl; exact iotaC_ge)

/-- **Rejected fixture**: the one-surface family of the exact torus does not certify
`ι_min = 0.25`. -/
theorem not_C1_iotaMin {u z : FA} {μ₀ : ℝ} :
    ¬ CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) {surfaceC u z} 0
      (1 / 4) := fun hC => by
  have := hC.iota_ge (surfaceC u z) rfl
  exact absurd this (not_le.mpr iotaC_lt)

/-- **The Dommaschk target has rotational transform `ι_C` on an exact invariant torus**,
conditional on the initial residual bounds of the KAM iteration. -/
theorem dommaschk_iotaOnTorus
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ)) :
    ∃ R z : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R z DommaschkKamDio.dkIotaC := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res e0R e0Z
  exact ⟨_, _, ExactTorusC.iotaOnTorus ⟨hu, hz, hur, hzr, hR, hZ, hC⟩⟩

/-- **Clause C1 for the Dommaschk target** (`field candidate`, a vacuum field): for every
`μ₀ > 0` there is a nonempty family of invariant tori with zero enclosed current and
`|ι| ≥ 0.24` (the exact KAM torus near torus C, `ι_C = −(85 + √5)/361`), conditional only on the
initial residual bounds `e0R`, `e0Z` of the data torus (the high-resolution residual chain). -/
theorem dommaschk_C1
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ))
    {μ₀ : ℝ} (hμ : 0 < μ₀) :
    ∃ S : Set SurfaceData,
      CurrentFreeTransform μ₀ (DommaschkQA2R.field DommaschkQA2R.candidate) S 0 (6 / 25) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := dk_exact_of_res e0R e0Z
  exact ⟨_, dommaschk_C1_of_exact ⟨hu, hz, hur, hzr, hR, hZ, hC⟩ hμ⟩

end PlasmaLean.Design.DommaschkKamC
