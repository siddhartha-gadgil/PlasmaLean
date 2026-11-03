/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCResChain
public import PlasmaLean.Design.DommaschkKamCAdmFrame

/-!
# The initial invariance error of Dommaschk torus C (N-33 plan item 7)

**Result.** `dk_e0R`, `dk_e0Z`: the flow-form residuals of the `96 × 80` data torus C
(`u₀C`, `z₀C`, `Design/DommaschkKamCTorus`) for the Dommaschk field with the moving frame centre
(`dkFieldTC`) at the rotational transform `ι_C = −(85 + √5)/361` satisfy
`Bd (9/200) (dkFieldTC.resR ι_C u₀C z₀C) e0q` and the same for `resZ`, with
`e0q = (123 / 10 ^ 29 : ℚ)`
(`≈ 1.23e-27`; the oracle value of `‖E‖_{0.045}` is `5.9e-29`): exactly the fields
`e0R`, `e0Z` of `FlowFieldG.KamHG` (`Design/KamFlowIterationG`) for strips `c.ρ = 9/200`.

**Proof.** The residuals are `rotψ` of the oracle-frame residuals `D 𝓛U − n_R`, `D 𝓛z − n_z`
(`resR_eq`, `Dof_rot`, `evPE_rot`, `Lt_rot`; `rotψ` is an isometry). In the oracle frame,
`𝓛_{ι_C} = 𝓛_{ι_q} + (ι_C − ι_q) ∂_θ` with `|ι_C − ι_q| ≤ 2^{−128}` (`iotaqC_close`); the `ι_q` part
is the value of the norm nodes `NR = D LU − R G`, `NZ = D LZ − s F` of the high-resolution ball
chain (`Design/DommaschkKamCResChain`; the `R`-form field polynomials are identified with `dD`,
`dnR`, `dnZ` by `subst_D`, `subst_nR`, `subst_nZ` and the Horner regrouping `horH`), and the
correction is bounded by `2^{−128} ‖D‖ ‖∂_θ x‖` with the Cauchy estimate
`‖∂_θ x‖_{9/200} ≤ ‖x‖_{1/20}/(e/200) ≤ 75 ‖x‖_{1/20}` (centre checks on the strip
`e^r ≤ 68897/2^16`).

**Sanity.** `e0q_pos`, `e0q_small` (the KAM constants need `e₀ ≲ 1.3e-23`), `horH_D` (the
Horner regrouping of `dDR` is `dDR` itself, as a list), `e0q_not_tiny` (rejected fixture: the
certificate does not give `e₀ ≤ 10⁻³⁰`, below the chain's rounding level).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex

/-- **The certified initial invariance error** `e₀` of torus C on the strip `r = 9/200`. -/
def e0q : ℚ := (123 / 10 ^ 29 : ℚ)

/-- `e₀ > 0`. -/
theorem e0q_pos : 0 < e0q := by norm_num [e0q]

/-- **Sanity**: `e₀ ≤ 10⁻²⁴`, far below the `≈ 1.3·10⁻²³` the KAM constants need. -/
theorem e0q_small : e0q ≤ 1 / 10 ^ 24 := by norm_num [e0q]

/-- **Rejected fixture**: `e₀` is not below `10⁻³⁰` (the rounding level of the chain). -/
theorem e0q_not_tiny : ¬ e0q ≤ 1 / 10 ^ 30 := by norm_num [e0q]

/-- `e^{1/20} ≤ 68897/2^16` (the strip of the derivative bound). -/
theorem exp_dk1_le : Real.exp (1 / 20) ≤ (68897 : ℕ) / 2 ^ 16 := by
  have h := Real.exp_bound' (x := 1 / 20) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The Horner regrouping of `dDR` is `dDR`. -/
theorem horH_D : horH (polyH 0) 0 8 0 = dDR := by kernel_fact

/-- The Horner regrouping of `dnRh` is `dnRh`. -/
theorem horH_G : horH (polyH 1) 0 8 0 = dnRh := by kernel_fact

/-- The Horner regrouping of `dnZR` is `R² ·` the `F` polynomial. -/
theorem horH_F : DkPoly.mulMono ⟨1, 2, 0, 0, 0⟩ (horH (polyH 2) 2 8 0) = dnZR := by kernel_fact

/-- The oracle-frame point of the data torus is the `R`-form point after substitution. -/
theorem xRH_eq : ![algebraMap ℂ FA ((R0q : ℚ) : ℂ) + xBo Uo Zo 0, xBo Uo Zo 1, xBo Uo Zo 2,
    xBo Uo Zo 3, 0, 0] = xRH := by
  funext i; fin_cases i <;> rfl

/-- `D` at the data torus is the chain value of `D`. -/
theorem Fo_D : Fo dD Uo Zo = XH 32 := by
  rw [Fo, ← subst_D, ev_substR_H, xRH_eq]
  change DkPoly.ev xRH dDR = DkPoly.ev xRH (horH (polyH 0) 0 8 0)
  rw [horH_D]

/-- `n_R` at the data torus is `R G`. -/
theorem Fo_nR : Fo dnR Uo Zo = XH 8 * XH 48 := by
  rw [Fo, ← subst_nR, ev_substR_H, xRH_eq, DkPoly.ev_mulMono]
  change _ = RvH * DkPoly.ev xRH (horH (polyH 1) 0 8 0)
  rw [horH_G]
  simp [DkPoly.Tm.ev, xRH]

/-- `n_z` at the data torus is `s F`. -/
theorem Fo_nZ : Fo dnZ Uo Zo = XH 9 * XH 65 := by
  rw [Fo, ← subst_nZ, ev_substR_H, xRH_eq, ← horH_F, DkPoly.ev_mulMono]
  change _ = RvH * RvH * DkPoly.ev xRH (horH (polyH 2) 2 8 0)
  simp [DkPoly.Tm.ev, xRH, sq]

/-- `LU` is `𝓛_{ι_q} U`. -/
theorem XH_LU : XH 14 = Lt iotaqC Uo := by
  change ((2 : ℂ) ^ Qc)⁻¹ • LUv = _
  rw [LUv, Lt, show ((-(Iqc : ℤ) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * ((iotaqC : ℝ) : ℂ) by
      rw [iotaqC]; push_cast; field_simp,
    show (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * 2 by push_cast; ring,
    dS_smul_symbol _ _ _ ana_Uo, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/-- `LZ` is `𝓛_{ι_q} z`. -/
theorem XH_LZ : XH 15 = Lt iotaqC Zo := by
  change ((2 : ℂ) ^ Qc)⁻¹ • LZv = _
  rw [LZv, Lt, show ((-(Iqc : ℤ) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * ((iotaqC : ℝ) : ℂ) by
      rw [iotaqC]; push_cast; field_simp,
    show (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * 2 by push_cast; ring,
    dS_smul_symbol _ _ _ ana_Zo, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/-- `𝓛_ι − 𝓛_{ι_q} = (ι − ι_q) ∂_θ`. -/
theorem Lt_sub_Lt (ι ι' : ℝ) {x : FA} (hx : Ana x) :
    Lt ι x - Lt ι' x = ((ι - ι' : ℝ) : ℂ) • dTh x := by
  rw [Lt, Lt, dTh, sub_eq_iff_eq_add, ← dS_smul_symbol _ _ _ hx, ← dS_add_symbol _ _ _ _ hx]
  congr 1 <;> push_cast <;> ring

/-- The Cauchy bound of `∂_θ` from a bound on the wider strip `1/20`. -/
theorem Bd_dTh_of {x : FA} {B : ℝ} (hB : 0 ≤ B) (hx : Bd (1 / 20) x B) :
    Bd (9 / 200) (dTh x) (75 * B) := by
  have h := hx.dS (δ := 1 / 200) (by norm_num) (by norm_num) 1 0
  rw [show (1 / 20 : ℝ) - 1 / 200 = 9 / 200 by norm_num] at h
  refine h.le ?_
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hm : max ‖(1 : ℂ)‖ ‖(0 : ℂ)‖ = 1 := by simp
  rw [hm]
  have : 1 / (Real.exp 1 * (1 / 200)) ≤ 75 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

set_option linter.style.longLine false in
/-- `‖U‖_{1/20}` (centre check on the wider strip). -/
theorem bU1 : Bd (1 / 20) Uo (((138631 / 10 ^ 6 : ℚ) : ℚ) : ℝ) := by
  rw [← xH_U]
  exact center_fullw exp_dk1_le boxH l1H kronH (fun _ => rfl) 4 0 135 193 8 8 96 80 2366831225660901919130286226906787233723629196362611425492037093201836963733068060976553640687769211310520910882630182078761896395530793663177098852778103523911789586416634523939973944898108907488729517684090525555624532359343131630814336971083641961013495343550455108151069392738254561413511651313885706261451291925499784292111267496226591430368700799621127192468618685361316505627327222807843772405725222500133031688880688079971719650559222718219783436439367975413846653130770536877198456557852076636973230004456035917669819453965382492681280220301967583026781453965168558411754857034256231043475277816051907348042626819484984485835479429988997210642307403954037077176535332043966633801336988319305958362589130613188254030007471313130889765640216382331773391004255835555977150020388264875891728767440164266639431031203296434801063894516097527090310842239875178813135189271589699977216 ((138631 / 10 ^ 6 : ℚ)) rfl
    (by kernel_fact) (by kron_lt) rfl c1H_U (by kernel_fact)

set_option linter.style.longLine false in
/-- `‖z‖_{1/20}` (centre check on the wider strip). -/
theorem bZ1 : Bd (1 / 20) Zo (((1195711 / 10 ^ 7 : ℚ) : ℚ) : ℝ) := by
  rw [← xH_Z]
  exact center_fullw exp_dk1_le boxH l1H kronH (fun _ => rfl) 5 1 134 193 8 8 96 80 2041423731966026657213015585009984670746600720755973343141642287456323388449526700868744607291090615304132407600532973131807599187169541919346185127822496425989276188758963359074066249689577934116641203332970437006426765168992101702783215997030031962657287891241217044243645607177270586379589472051829283284098714895828436497387610352887685813496166234334703043271121080923214925372344383832065175514727803234542057691005882143885647548819548388470498407234727200714853240229018657318044779526082829437067870696443568137343554308396155660735716975249835035733324353299143416790345583899004281859125028356392960702020361225435585091624935847202912675343831271132236738811518265697947609791924625874778821039635793057844469727352519496465934663357828761444972202851082584639015213001444631874659182589648893014754018274334622278391058925695277188345067346593850506459092671883985889001472 ((1195711 / 10 ^ 7 : ℚ)) rfl
    (by kernel_fact) (by kron_lt) rfl c1H_Z (by kernel_fact)

/-- The value of the norm node `NR`. -/
theorem eval_NR : Ex.eval XH trH_NR = Fo dD Uo Zo * Lt iotaqC Uo - Fo dnR Uo Zo := by
  rw [Fo_D, Fo_nR, ← XH_LU]; rfl

/-- The value of the norm node `NZ`. -/
theorem eval_NZ : Ex.eval XH trH_NZ = Fo dD Uo Zo * Lt iotaqC Zo - Fo dnZ Uo Zo := by
  rw [Fo_D, Fo_nZ, ← XH_LZ]; rfl

/-- The `ι − ι_q` correction. -/
theorem Bd_corr {x : FA} (hx : Ana x) {B : ℚ} (hB0 : 0 ≤ B) (hB : Bd (1 / 20) x (B : ℝ)) :
    Bd (9 / 200) (Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC x - Lt iotaqC x))
      (((BH 32 + EH 32 : ℚ) : ℝ) * ((1 / 2 ^ Qc : ℝ) * (75 * (B : ℝ)))) := by
  have hD : Bd (9 / 200) (Fo dD Uo Zo) ((BH 32 + EH 32 : ℚ) : ℝ) := by
    rw [Fo_D]; exact valH_le (by norm_num) exp_dk_le 32 (by norm_num)
  rw [Lt_sub_Lt _ _ hx]
  refine hD.mul (by norm_num) ?_
  have h1 := (Bd_dTh_of (by exact_mod_cast hB0) hB).smul
    (((DommaschkKamDio.dkIotaC - iotaqC : ℝ) : ℂ))
  refine h1.le ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have := iotaqC_close
  have h75 : (0 : ℝ) ≤ 75 * (B : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right this h75

set_option linter.style.longLine false in
/-- **The oracle-frame `R`-residual.** -/
theorem resO_R : Bd (9 / 200) (Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Uo - Fo dnR Uo Zo)
    ((e0q : ℚ) : ℝ) := by
  have h1 := nH_NR_bd (by norm_num) exp_dk_le
  rw [eval_NR] at h1
  have h2 := Bd_corr ana_Uo (by norm_num) bU1
  have h3 := h1.add h2
  rw [show Fo dD Uo Zo * Lt iotaqC Uo - Fo dnR Uo Zo +
      Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC Uo - Lt iotaqC Uo) =
      Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Uo - Fo dnR Uo Zo by ring] at h3
  refine h3.le ?_
  have := (show ((611429 / 500000000000000000000000000000000 : ℚ) : ℚ) + (BH 32 + EH 32) * (1 / 2 ^ Qc * (75 * (138631 / 10 ^ 6 : ℚ))) ≤ e0q by kernel_fact)
  have := (Rat.cast_le (K := ℝ)).2 this
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
/-- **The oracle-frame `z`-residual.** -/
theorem resO_Z : Bd (9 / 200) (Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Zo - Fo dnZ Uo Zo)
    ((e0q : ℚ) : ℝ) := by
  have h1 := nH_NZ_bd (by norm_num) exp_dk_le
  rw [eval_NZ] at h1
  have h2 := Bd_corr ana_Zo (by norm_num) bZ1
  have h3 := h1.add h2
  rw [show Fo dD Uo Zo * Lt iotaqC Zo - Fo dnZ Uo Zo +
      Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC Zo - Lt iotaqC Zo) =
      Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Zo - Fo dnZ Uo Zo by ring] at h3
  refine h3.le ?_
  have := (show ((1099 / 10 ^ 30 : ℚ) : ℚ) + (BH 32 + EH 32) * (1 / 2 ^ Qc * (75 * (1195711 / 10 ^ 7 : ℚ))) ≤ e0q by kernel_fact)
  have := (Rat.cast_le (K := ℝ)).2 this
  push_cast at this ⊢
  linarith

/-- **The `R`-residual of torus C** (`KamHG.e0R`, strip `9/200`). -/
theorem dk_e0R :
    Bd (9 / 200) (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) ((e0q : ℚ) : ℝ) := by
  rw [FlowFieldG.resR_eq, u₀C, z₀C, Dof_rot, Lt_rot _ ana_Uo,
    show dkFieldTC.nRp = DkPoly.toPE dnR from rfl, evPE_rot, ← rotψ_mul, ← rotψ_sub]
  exact Bd_rotψ resO_R

/-- **The `z`-residual of torus C** (`KamHG.e0Z`, strip `9/200`). -/
theorem dk_e0Z :
    Bd (9 / 200) (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) ((e0q : ℚ) : ℝ) := by
  rw [FlowFieldG.resZ_eq, u₀C, z₀C, Dof_rot, Lt_rot _ ana_Zo,
    show dkFieldTC.nZp = DkPoly.toPE dnZ from rfl, evPE_rot, ← rotψ_mul, ← rotψ_sub]
  exact Bd_rotψ resO_Z

end PlasmaLean.Design.DommaschkKamC
