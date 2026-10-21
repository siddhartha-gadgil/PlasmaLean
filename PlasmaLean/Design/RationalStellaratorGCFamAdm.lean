/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFamOutH
public import PlasmaLean.Design.RationalStellaratorGCFamOutL
public import PlasmaLean.Design.RationalStellaratorGCFamMaj
public import PlasmaLean.Design.RationalStellaratorGCTorusExact

/-!
# Admissibility, residual and constants of the guiding-centre torus family

For every parameter `|c| = 1` (`ρ = ρF c = (64 + Re c)/2^14 ∈ [63/16384, 65/16384]`), from the
two family ball chains (`Design/RationalStellaratorGCFamOut{H,L}`):

* the bounds of the family torus `K(c) = (1 + xHF c 4, xHF c 5)` on the strip `r_A`
  (`Bd_uF`, …): `‖u‖ ≤ 0.1947`, `‖z‖ ≤ 0.1636`, `‖∂_θu‖ ≤ 0.1647`, `‖∂_θz‖ ≤ 0.1629`,
  `‖𝓛u‖ ≤ 0.1105`, `‖𝓛z‖ ≤ 0.1048`;
* **the residual** (`famResR`, `famResZ`): `‖D̃ 𝓛K − ñ‖_{r_A} ≤ e₀ = 2.7 × 10⁻²¹` for the
  guiding-centre field `gcFlow (ρF c)`;
* the distances to the low-resolution family and to the `ρ = 1/256` low-resolution torus;
* **admissibility** (`famAdm`): every analytic torus `μ = 10⁻¹¹`-close to `K(c)` satisfies the
  bounds of the Newton step with the constants `cF` (uniform over the cell).

**Sanity.** `ρF_mem`: `ρF c ∈ [63/16384, 65/16384]` for `|c| = 1`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-! ## The parameter -/

/-- **Sanity**: the parameter of the family lies in the cell. -/
theorem ρF_mem {c : ℂ} (hc : ‖c‖ = 1) : 63 / 16384 ≤ ρF c ∧ ρF c ≤ 65 / 16384 := by
  have h := Complex.abs_re_le_norm c
  rw [hc] at h
  have h' := abs_le.mp h
  constructor <;> rw [ρF] <;> linarith [h'.1, h'.2]

/-- `|ρF c| ≤ 65/16384`. -/
theorem abs_ρF_le {c : ℂ} (hc : ‖c‖ = 1) : |ρF c| ≤ 65 / 16384 := by
  obtain ⟨h1, h2⟩ := ρF_mem hc
  rw [abs_le]; constructor <;> linarith

/-! ## Constants -/

/-- The displacement budget `μ = 10⁻¹¹`. -/
def μF : ℝ := 1 / 10 ^ 11

/-- The initial error `e₀ = 2.7 × 10⁻²¹`. -/
def e0F : ℝ := 27 / 10 ^ 22

/-- `‖u‖ + μ`. -/
def auF : ℝ := 1947 / 10000 + μF
/-- `‖z‖ + μ`. -/
def azF : ℝ := 409 / 2500 + μF
/-- `‖∂_θ u‖ + μ`. -/
def aRtF : ℝ := 1647 / 10000 + μF
/-- `‖∂_θ z‖ + μ`. -/
def aztF : ℝ := 1629 / 10000 + μF
/-- `‖𝓛u‖ + μ`. -/
def aLRF : ℝ := 221 / 2000 + μF
/-- `‖𝓛z‖ + μ`. -/
def aLzF : ℝ := 131 / 1250 + μF
/-- `‖D̃⁻¹‖`. -/
def sDF : ℝ := 16389 / 10000
/-- `‖R⁻¹‖`. -/
def sRF : ℝ := 1 / (1 - auF)
/-- `‖W₀⁻¹‖`. -/
def sWF : ℝ := 8871 / 50
/-- The torsion bound. -/
def tTF : ℝ := 3799 / 100
/-- The twist bound. -/
def τF : ℝ := 411 / 1000

/-- **The step constants for the guiding-centre torus family** (uniform over the cell). -/
def cF : SC where
  ρ := KamTorusA.rA
  δ0 := δ0G
  γ := 687 / 10000
  θ := e0F / δ0G ^ 4
  au := auF
  az := azF
  aRt := aRtF
  azt := aztF
  aLR := aLRF
  aLz := aLzF
  ac := acG
  bD := 12791 / 10000
  bDu := 22391 / 10000
  bDz := 20441 / 100000
  bnR := 10201 / 100000
  bnRu := 95121 / 100000
  bnRz := 74651 / 100000
  bnZ := 10601 / 100000
  bnZu := 87241 / 100000
  bnZz := 82001 / 100000
  sD := sDF
  sR := sRF
  sW := sWF
  tT := tTF
  τ := τF
  C2 := (RationalStellaratorGCFamily.C2Q : ℝ)
  E1 := 2718 / 1000
  cKb := 6170
  cLb := 21400

/-- **Sanity**: the torus bound of `cF` is `‖u‖ + μ`. -/
theorem cF_au : cF.au = 1947 / 10000 + 1 / 10 ^ 11 := rfl

/-! ## The family torus -/

/-- The values of the high-resolution chain at `r_A`. -/
theorem valHF_rA {c : ℂ} (hc : ‖c‖ = 1) (i : ℕ) (hi : i < 78) :
    Bd KamTorusA.rA (XHF c i) ((BHF i + EHF i : ℚ) : ℝ) :=
  valHF_le rA_nonneg' exp_rA_le' hc i hi

/-- `‖u‖_{r_A} ≤ 0.1947`. -/
theorem Bd_uF {c : ℂ} (hc : ‖c‖ = 1) : Bd KamTorusA.rA (xHF c 4) (1947 / 10000) := by
  have h := valHF_rA hc 4 (by norm_num)
  rw [XHF_eq_U hc] at h
  refine h.le ?_
  have := qle (show BHF 4 + EHF 4 ≤ 1947 / 10000 by decide +kernel)
  push_cast at this ⊢; exact this

/-- `‖z‖_{r_A} ≤ 0.1636`. -/
theorem Bd_zF {c : ℂ} (hc : ‖c‖ = 1) : Bd KamTorusA.rA (xHF c 5) (409 / 2500) := by
  have h := valHF_rA hc 5 (by norm_num)
  rw [XHF_eq_Z hc] at h
  refine h.le ?_
  have := qle (show BHF 5 + EHF 5 ≤ 409 / 2500 by decide +kernel)
  push_cast at this ⊢; exact this

/-- `∂_θ` of the family torus. -/
theorem dTh_xHF_U {c : ℂ} (hc : ‖c‖ = 1) : xHF c 8 = dTh (xHF c 4) := by
  rw [xHF_der_thU (ne_zero_of_norm_one hc)]; simp [dTh]

/-- `∂_θ` of the family torus. -/
theorem dTh_xHF_Z {c : ℂ} (hc : ‖c‖ = 1) : xHF c 9 = dTh (xHF c 5) := by
  rw [xHF_der_thZ (ne_zero_of_norm_one hc)]; simp [dTh]

/-- `‖∂_θ u‖_{r_A} ≤ 0.1647`. -/
theorem Bd_dTh_uF {c : ℂ} (hc : ‖c‖ = 1) : Bd KamTorusA.rA (dTh (xHF c 4)) (1647 / 10000) := by
  rw [← dTh_xHF_U hc]
  refine (normHF exp_rA_le' hc 8 (by norm_num)).le ?_
  have := qle (show BHF 8 ≤ 1647 / 10000 by decide +kernel); push_cast at this ⊢; exact this

/-- `‖∂_θ z‖_{r_A} ≤ 0.1629`. -/
theorem Bd_dTh_zF {c : ℂ} (hc : ‖c‖ = 1) : Bd KamTorusA.rA (dTh (xHF c 5)) (1629 / 10000) := by
  rw [← dTh_xHF_Z hc]
  refine (normHF exp_rA_le' hc 9 (by norm_num)).le ?_
  have := qle (show BHF 9 ≤ 1629 / 10000 by decide +kernel); push_cast at this ⊢; exact this

/-- `‖𝓛 u‖_{r_A} ≤ 0.1105`. -/
theorem Bd_Lt_uF {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (Lt KamTorusA.iota (xHF c 4)) (221 / 2000) := by
  have h := valHF_rA hc 6 (by norm_num)
  rw [XHF_spec c (i := 6) (by decide +kernel)] at h
  refine (Bd_inv_pow96 h).le ?_
  have := qle (show (BHF 6 + EHF 6) / 2 ^ 96 ≤ 221 / 2000 by decide +kernel)
  push_cast at this ⊢; exact this

/-- `‖𝓛 z‖_{r_A} ≤ 0.1048`. -/
theorem Bd_Lt_zF {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (Lt KamTorusA.iota (xHF c 5)) (131 / 1250) := by
  have h := valHF_rA hc 7 (by norm_num)
  rw [XHF_spec c (i := 7) (by decide +kernel)] at h
  refine (Bd_inv_pow96 h).le ?_
  have := qle (show (BHF 7 + EHF 7) / 2 ^ 96 ≤ 131 / 1250 by decide +kernel)
  push_cast at this ⊢; exact this

/-- The family torus is analytic. -/
theorem ana_uF {c : ℂ} (hc : ‖c‖ = 1) : Ana (xHF c 4) := by
  rw [xHF_fam (ne_zero_of_norm_one hc) (i := 4) (by decide +kernel) (p := 0) rfl]
  exact ana_famCtr _ _ _ _ _ _ _ _ c _ _

/-- The family torus is analytic. -/
theorem ana_zF {c : ℂ} (hc : ‖c‖ = 1) : Ana (xHF c 5) := by
  rw [xHF_fam (ne_zero_of_norm_one hc) (i := 5) (by decide +kernel) (p := 1) rfl]
  exact ana_famCtr _ _ _ _ _ _ _ _ c _ _

/-- The family torus is real. -/
theorem isReal_uF {c : ℂ} (hc : ‖c‖ = 1) : IsReal (xHF c 4) := by
  rw [xHF_fam (ne_zero_of_norm_one hc) (i := 4) (by decide +kernel) (p := 0) rfl]
  have := isReal_famCtr SHF NHF MHF 0 1 hc 0 (famHF 4)
  simpa [oddHF, oddHFl, c0HF, c0HFl] using this

/-- The family torus is real. -/
theorem isReal_zF {c : ℂ} (hc : ‖c‖ = 1) : IsReal (xHF c 5) := by
  rw [xHF_fam (ne_zero_of_norm_one hc) (i := 5) (by decide +kernel) (p := 1) rfl]
  have := isReal_famCtr SHF NHF MHF 1 1 hc 0 (famHF 5)
  simpa [oddHF, oddHFl, c0HF, c0HFl] using this

/-! ## The residual -/

/-- The `R`-residual node is `2^96` times the flow-form residual. -/
theorem eval_trHFN_resR (c : ℂ) (hc : ‖c‖ = 1) :
    Ex.eval (XHF c) (toEx trHFN_resR) =
      (2 : ℂ) ^ 96 • (gcFlow (ρF c)).resR KamTorusA.iota (xHF c 4) (xHF c 5) := by
  rw [FlowFieldS.resR_eq]
  have e73 : XHF c 73 = PolyExprS.eval (xB (xHF c 4) (xHF c 5)) (gcD (ρF c)) := rfl
  have e75 : XHF c 75 = PolyExprS.eval (xB (xHF c 4) (xHF c 5)) (gcNR (ρF c)) := rfl
  have e6 : XHF c 6 = (2 : ℂ) ^ 96 • Lt KamTorusA.iota (xHF c 4) := rfl
  simp only [trHFN_resR, toEx, Ex.eval, e73, e75, e6, XHF_eq_t hc, xHF_t (ne_zero_of_norm_one hc),
    FlowFieldS.Dof, gcFlow, Algebra.smul_def, map_pow, map_ofNat, Int.cast_ofNat]
  norm_num
  ring

/-- The `z`-residual node is `2^96` times the flow-form residual. -/
theorem eval_trHFN_resZ (c : ℂ) (hc : ‖c‖ = 1) :
    Ex.eval (XHF c) (toEx trHFN_resZ) =
      (2 : ℂ) ^ 96 • (gcFlow (ρF c)).resZ KamTorusA.iota (xHF c 4) (xHF c 5) := by
  rw [FlowFieldS.resZ_eq]
  have e73 : XHF c 73 = PolyExprS.eval (xB (xHF c 4) (xHF c 5)) (gcD (ρF c)) := rfl
  have e77 : XHF c 77 = PolyExprS.eval (xB (xHF c 4) (xHF c 5)) (gcNZ (ρF c)) := rfl
  have e7 : XHF c 7 = (2 : ℂ) ^ 96 • Lt KamTorusA.iota (xHF c 5) := rfl
  simp only [trHFN_resZ, toEx, Ex.eval, e73, e77, e7, XHF_eq_t hc, xHF_t (ne_zero_of_norm_one hc),
    FlowFieldS.Dof, gcFlow, Algebra.smul_def, map_pow, map_ofNat, Int.cast_ofNat]
  norm_num
  ring

/-- **The residual of the family torus** (`R`-component): `‖D̃ 𝓛u − ñ_R‖_{r_A} ≤ 2.7 × 10⁻²¹`. -/
theorem famResR {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA ((gcFlow (ρF c)).resR KamTorusA.iota (xHF c 4) (xHF c 5)) e0F := by
  have h := normHF_resR rA_nonneg' exp_rA_le' hc
  rw [eval_trHFN_resR c hc] at h
  refine (Bd_inv_pow96 h).le ?_
  norm_num [e0F]

/-- **The residual of the family torus** (`z`-component): `‖D̃ 𝓛z − ñ_z‖_{r_A} ≤ 2.7 × 10⁻²¹`. -/
theorem famResZ {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA ((gcFlow (ρF c)).resZ KamTorusA.iota (xHF c 4) (xHF c 5)) e0F := by
  have h := normHF_resZ rA_nonneg' exp_rA_le' hc
  rw [eval_trHFN_resZ c hc] at h
  refine (Bd_inv_pow96 h).le ?_
  norm_num [e0F]

/-! ## Distances -/

/-- `‖u − u_L‖_{r_A} ≤ 1.163 × 10⁻⁸` (the low-resolution family). -/
theorem fdist_u {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (xHF c 4 - xLF c 4) ((1163 / 10 ^ 11 : ℚ) : ℝ) := by
  have h := normHF_dU rA_nonneg' exp_rA_le' hc
  have e : XHF c 10 = xLF c 4 := rfl
  simpa [trHFN_dU, toEx, Ex.eval, XHF_eq_U hc, e] using h

/-- `‖z − z_L‖_{r_A} ≤ 1.145 × 10⁻⁸`. -/
theorem fdist_z {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (xHF c 5 - xLF c 5) ((229 / 20000000000 : ℚ) : ℝ) := by
  have h := normHF_dZ rA_nonneg' exp_rA_le' hc
  have e : XHF c 11 = xLF c 5 := rfl
  simpa [trHFN_dZ, toEx, Ex.eval, XHF_eq_Z hc, e] using h

/-- `‖∂_θ u − ∂_θ u_L‖_{r_A} ≤ 1.161 × 10⁻⁸`. -/
theorem fdist_a {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (dTh (xHF c 4) - dTh (xLF c 4)) ((1161 / 10 ^ 11 : ℚ) : ℝ) := by
  have h := normHF_dA rA_nonneg' exp_rA_le' hc
  have e1 : XHF c 8 = dTh (xHF c 4) := rfl
  have e2 : XHF c 12 = dTh (xLF c 4) := rfl
  simpa [trHFN_dA, toEx, Ex.eval, e1, e2] using h

/-- `‖∂_θ z − ∂_θ z_L‖_{r_A} ≤ 1.159 × 10⁻⁸`. -/
theorem fdist_b {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA (dTh (xHF c 5) - dTh (xLF c 5)) ((1159 / 10 ^ 11 : ℚ) : ℝ) := by
  have h := normHF_dB rA_nonneg' exp_rA_le' hc
  have e1 : XHF c 9 = dTh (xHF c 5) := rfl
  have e2 : XHF c 13 = dTh (xLF c 5) := rfl
  simpa [trHFN_dB, toEx, Ex.eval, e1, e2] using h


/-! ## The low-resolution family: field, winding form and torsion -/

section Field

variable {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
  {u z : FA} (hU : Bd r (u - xLF c 4) (ELF 4)) (hZ : Bd r (z - xLF c 5) (ELF 5))
  (hA : Bd r (dTh u - xLF c 6) (ELF 6)) (hB : Bd r (dTh z - xLF c 7) (ELF 7))
include hr hq hc hU hZ hA hB

/-- `‖D̃ − d₀‖ ≤ 0.3341` at every torus near the low-resolution family torus. -/
theorem Bd_DdevF : Bd r ((gcFlow (ρF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ))
    (752400000000000 / 2 ^ 51) := by
  have h := normLF_DdevF hr hq hc hU hZ hA hB
  have hk : algebraMap ℂ FA ((2 : ℂ) ^ 51 * ((d0G : ℝ) : ℂ)) = (2126414735707981 : FA) := by
    rw [show ((2 : ℂ) ^ 51 * ((d0G : ℝ) : ℂ)) = (2126414735707981 : ℂ) by
      simp only [d0G]; push_cast; ring]
    exact map_ofNat _ _
  have e116 : XLF c u z 116 = PolyExprS.eval (xB u z) (gcD (ρF c)) := rfl
  have e0 : XLF c u z 0 = 1 := rfl
  have e : Ex.eval (XLF c u z) (toEx trLFN_DdevF) =
      (2 ^ 51 : ℂ) • ((gcFlow (ρF c)).Dof u z - algebraMap ℂ FA (d0G : ℂ)) := by
    simp only [trLFN_DdevF, toEx, Ex.eval, e116, e0, FlowFieldS.Dof, gcFlow, Int.cast_ofNat]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, ← map_mul, hk, map_pow, map_ofNat]
    norm_num
  rw [e] at h
  have h2 := h.smul ((2 ^ 51 : ℂ))⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at h2
  refine h2.le (le_of_eq ?_)
  rw [norm_inv, norm_pow, Complex.norm_ofNat]; push_cast; ring

/-- `‖W₀ − w₀‖ ≤ 0.003728` at every torus near the low-resolution family torus. -/
theorem Bd_WdevF : Bd r (W0of u z - algebraMap ℂ FA (w0G : ℂ)) (2149000000000000 / 2 ^ 59) := by
  have h := normLF_WdevF hr hq hc hU hZ hA hB
  have hk : algebraMap ℂ FA ((2 : ℂ) ^ 59 * ((w0G : ℝ) : ℂ)) = -(5398240620830529 : FA) := by
    rw [show ((2 : ℂ) ^ 59 * ((w0G : ℝ) : ℂ)) = -(5398240620830529 : ℂ) by
      simp only [w0G]; push_cast; ring]
    rw [map_neg, map_ofNat]
  have e108 : XLF c u z 108 = W0of u z := rfl
  have e0 : XLF c u z 0 = 1 := rfl
  have e : Ex.eval (XLF c u z) (toEx trLFN_WdevF) =
      (2 ^ 59 : ℂ) • (W0of u z - algebraMap ℂ FA (w0G : ℂ)) := by
    simp only [trLFN_WdevF, toEx, Ex.eval, e108, e0, Int.cast_ofNat]
    rw [smul_sub, Algebra.smul_def, Algebra.smul_def, ← map_mul, hk, map_pow, map_ofNat]
    norm_num
    ring
  rw [e] at h
  have h2 := h.smul ((2 ^ 59 : ℂ))⁻¹
  rw [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at h2
  refine h2.le (le_of_eq ?_)
  rw [norm_inv, norm_pow, Complex.norm_ofNat]; push_cast; ring

/-- `‖q D̃³ W₀² − 1‖ ≤ 1.337 × 10⁻⁵`. -/
theorem Bd_XtorF : Bd r (xLF c 136 * (PolyExprS.eval (xB u z) (gcD (ρF c)) ^ 3 * W0of u z ^ 2) -
    1) (1337 / 10 ^ 8) := by
  have h := normLF_XF hr hq hc hU hZ hA hB
  have e135 : XLF c u z 135 = PolyExprS.eval (xB u z) (gcD (ρF c)) ^ 3 * W0of u z ^ 2 := rfl
  have e136 : XLF c u z 136 = xLF c 136 := rfl
  have e0 : XLF c u z 0 = 1 := rfl
  have e : Ex.eval (XLF c u z) (toEx trLFN_XF) =
      xLF c 136 * (PolyExprS.eval (xB u z) (gcD (ρF c)) ^ 3 * W0of u z ^ 2) - 1 := by
    simp only [trLFN_XF, toEx, Ex.eval, e135, e136, e0]; ring
  rw [e] at h
  refine h.le (le_of_eq ?_); push_cast; ring

end Field

/-- The centre entry of the leading Chebyshev coefficient of the torsion centre. -/
theorem avgY0 : sliceG NLF MLF (if oddLF 137 then -1 else 1) (c0LF 137 : ℤ) 0 0
    ((famLF 137).headD SliceData.zero) NLF MLF = 509165477863147786 := by
  decide +kernel

/-- The centre entries of the other Chebyshev coefficients of the torsion centre. -/
theorem avgY1 : avgB NLF MLF (if oddLF 137 then -1 else 1) (c0LF 137 : ℤ) (famLF 137).tail =
    365841897391020 := by
  decide +kernel

/-- **The average of the torsion centre** at every parameter value. -/
theorem avg_xLF_Y {c : ℂ} (hc : ‖c‖ = 1) :
    ‖avg (xLF c 137) - ((509165477863147786 / 2 ^ 60 : ℝ) : ℂ)‖ ≤ 365841897391020 / 2 ^ 59 := by
  rw [xLF_fam (ne_zero_of_norm_one hc) (i := 137) (by decide +kernel) (p := 0) rfl,
    show famLF 137 = (famLF 137).headD SliceData.zero :: (famLF 137).tail from rfl,
    avg_famCtr_cons, avgY0]
  have h := norm_avg_famCtr_le SLF NLF MLF (if oddLF 137 then -1 else 1) (c0LF 137 : ℤ) hc 1
    (famLF 137).tail le_rfl
  rw [avgY1] at h
  have e : (c ^ 0 + if (0 : ℕ) = 0 then 0 else (c ^ 0)⁻¹) * (((2 : ℂ) ^ SLF)⁻¹ *
      (((509165477863147786 : ℤ)) : ℂ)) = ((509165477863147786 / 2 ^ 60 : ℝ) : ℂ) := by
    simp only [pow_zero, ↓reduceIte, add_zero, one_mul, SLF]; push_cast; ring
  rw [e, add_sub_cancel_left]
  refine h.trans (le_of_eq ?_)
  simp only [SLF]; push_cast; ring

section Adm

variable {r : ℝ} (hr0 : 0 < r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
  {u z : FA} (hU : Bd r (u - xLF c 4) (ELF 4)) (hZ : Bd r (z - xLF c 5) (ELF 5))
  (hA : Bd r (dTh u - xLF c 6) (ELF 6)) (hB : Bd r (dTh z - xLF c 7) (ELF 7))
include hr0 hq hc hU hZ hA hB

/-- **`D̃` is invertible**, `‖D̃⁻¹‖ ≤ 1.6389`. -/
theorem adm_Di_F : IsUnit ((gcFlow (ρF c)).Dof u z) ∧
    Bd r (Ring.inverse ((gcFlow (ρF c)).Dof u z)) sDF := by
  have h := Bd_DdevF hr0.le hq hc hU hZ hA hB
  have hn : ‖((d0G : ℝ) : ℂ)‖ = d0G := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num [d0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [d0G])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [d0G, sDF])⟩

/-- **`W₀` is invertible**, `‖W₀⁻¹‖ ≤ 177.42`. -/
theorem adm_Wi_F : IsUnit (W0of u z) ∧ Bd r (Ring.inverse (W0of u z)) sWF := by
  have h := Bd_WdevF hr0.le hq hc hU hZ hA hB
  have hn : ‖((w0G : ℝ) : ℂ)‖ = -w0G := by
    rw [Complex.norm_real, Real.norm_of_nonpos (by norm_num [w0G])]
  obtain ⟨hu, hb⟩ := Bd.inverse hr0.le h (by rw [hn]; norm_num [w0G])
  exact ⟨hu, hb.le (by rw [hn]; norm_num [w0G, sWF])⟩

/-- **Torsion and twist**: `‖T₀‖ ≤ 37.99`, `|⟨T₀⟩| ≥ 0.411`. -/
theorem adm_T_F : Bd r ((gcFlow (ρF c)).Talg u z) tTF ∧
    τF ≤ ‖avg ((gcFlow (ρF c)).Talg u z)‖ := by
  have hr := hr0.le
  set F := (gcFlow (ρF c)).Dof u z ^ 3 * W0of u z ^ 2 with hF
  set q := xLF c 136 with hq_def
  have hX : Bd r (q * F - algebraMap ℂ FA 1) ((1337 / 10 ^ 8 : ℚ) : ℝ) := by
    rw [map_one]
    have := Bd_XtorF hr hq hc hU hZ hA hB
    refine this.le (le_of_eq ?_); push_cast; ring
  obtain ⟨hUq, hInv⟩ := Bd.inverse hr hX (by rw [norm_one]; norm_num)
  rw [norm_one] at hInv
  have hY := valLF_le hr hq hc hU hZ hA hB 137 (by norm_num)
  have hYc := (ballLF_all hr hq hc hU hZ hA hB) 137 (by norm_num)
  have hXe : Bd r (q * F - 1) ((1337 / 10 ^ 8 : ℚ) : ℝ) := by rwa [map_one] at hX
  set Y := XLF c u z 137 with hY_def
  obtain ⟨hDu, -⟩ := adm_Di_F hr0 hq hc hU hZ hA hB
  obtain ⟨hWu, -⟩ := adm_Wi_F hr0 hq hc hU hZ hA hB
  have hYe : Y = (1 + u) ^ 3 * (gcFlow (ρF c)).Pof u z * q := rfl
  have hrep : (gcFlow (ρF c)).Talg u z = Y * Ring.inverse (q * F) := by
    refine ext_eval fun θ ψ => ?_
    have hD := eval_ne_zero_of_unit hDu θ ψ
    have hW := eval_ne_zero_of_unit hWu θ ψ
    have hQ := eval_ne_zero_of_unit hUq θ ψ
    rw [eval_mul, eval_inverse hUq, hYe]
    rw [hF] at hQ ⊢
    simp only [FlowFieldS.Talg, FlowFieldS.Di, Wi, eval_mul, eval_pow', eval_inverse hDu,
      eval_inverse hWu, eval_add', eval_one] at hQ ⊢
    have hq0 : eval q θ ψ ≠ 0 := left_ne_zero_of_mul hQ
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hrep]
    refine (hY.mul hr hInv).le ?_
    have h1 := qle (show BLF 137 + ELF 137 ≤ 379886 / 10000 by decide +kernel)
    push_cast at h1 ⊢
    rw [tTF]
    calc ((BLF 137 : ℝ) + ELF 137) * (1 / (1 - 1337 / 10 ^ 8)) ≤
        (379886 / 10000) * (1 / (1 - 1337 / 10 ^ 8)) := by gcongr
      _ ≤ 3799 / 100 := by norm_num
  · have hI : Ring.inverse (q * F) = 1 - (q * F - 1) * Ring.inverse (q * F) := by
      have := Ring.mul_inverse_cancel _ hUq
      linear_combination this
    have e : (gcFlow (ρF c)).Talg u z = Y - Y * (q * F - 1) * Ring.inverse (q * F) := by
      rw [hrep]; nth_rewrite 1 [hI]; ring
    rw [e, avg_sub]
    have h1 : ‖avg (Y * (q * F - 1) * Ring.inverse (q * F))‖ ≤
        ((BLF 137 + ELF 137 : ℚ) : ℝ) * ((1337 / 10 ^ 8 : ℚ) : ℝ) *
          (1 / (1 - ((1337 / 10 ^ 8 : ℚ) : ℝ))) :=
      ((hY.mul hr hXe).mul hr hInv).norm_avg_le hr
    have h2 : ‖avg (Y - xLF c 137)‖ ≤ ((ELF 137 : ℚ) : ℝ) := hYc.norm_avg_le hr
    rw [avg_sub] at h2
    have hav := avg_xLF_Y hc
    have h3 : (509165477863147786 / 2 ^ 60 : ℝ) - 365841897391020 / 2 ^ 59 - ((ELF 137 : ℚ) : ℝ) ≤
        ‖avg Y‖ := by
      have h4 := norm_sub_norm_le (((509165477863147786 / 2 ^ 60 : ℝ) : ℂ))
        (((509165477863147786 / 2 ^ 60 : ℝ) : ℂ) - avg Y)
      rw [sub_sub_cancel, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h4
      have h5 : ‖((509165477863147786 / 2 ^ 60 : ℝ) : ℂ) - avg Y‖ ≤
          365841897391020 / 2 ^ 59 + ((ELF 137 : ℚ) : ℝ) := by
        have := norm_add_le (avg (xLF c 137) - ((509165477863147786 / 2 ^ 60 : ℝ) : ℂ))
          (avg Y - avg (xLF c 137))
        rw [show avg (xLF c 137) - ((509165477863147786 / 2 ^ 60 : ℝ) : ℂ) +
          (avg Y - avg (xLF c 137)) = -(((509165477863147786 / 2 ^ 60 : ℝ) : ℂ) - avg Y) by ring,
          norm_neg] at this
        linarith
      linarith
    have h5 := norm_sub_norm_le (avg Y) (avg (Y * (q * F - 1) * Ring.inverse (q * F)))
    have hB1 := qle (show BLF 137 + ELF 137 ≤ 379886 / 10000 by decide +kernel)
    have hE1 := qle (show ELF 137 ≤ 286 / 10 ^ 4 by decide +kernel)
    push_cast at h1 hB1 hE1 h3
    have h6 : ((BLF 137 : ℝ) + ELF 137) * (1337 / 10 ^ 8) * (1 / (1 - 1337 / 10 ^ 8)) ≤
        (379886 / 10000) * (1337 / 10 ^ 8) * (1 / (1 - 1337 / 10 ^ 8)) := by gcongr
    rw [τF]
    norm_num at h6 h3 ⊢
    linarith

end Adm

/-- The bounds `(‖u‖, ‖z‖, ‖cos 2φ‖, ‖sin 2φ‖, 0, 0)` of the torus variables. -/
def avF : Fin 6 → ℝ := ![auF, azF, acG, acG, 0, 0]

/-- The torus variable bounds are below the validity bounds of the family. -/
theorem avF_le : (∀ i, 0 ≤ avF i) ∧ ∀ i, avF i ≤ (RationalStellaratorGCFamily.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    norm_num [avF, RationalStellaratorGCFamily.aTQ, auF, azF, acG, μF]

/-- The inputs of the low-resolution family chain from `μ`-closeness to the family torus. -/
theorem inputs_LF {ρ : ℝ} (hρA : ρ ≤ KamTorusA.rA) {c : ℂ} (hc : ‖c‖ = 1) {u z : FA}
    (hC : Close ρ KamTorusA.iota u z (xHF c 4) (xHF c 5) μF) :
    Bd ρ (u - xLF c 4) (ELF 4) ∧ Bd ρ (z - xLF c 5) (ELF 5) ∧ Bd ρ (dTh u - xLF c 6) (ELF 6) ∧
      Bd ρ (dTh z - xLF c 7) (ELF 7) := by
  have hc0 := ne_zero_of_norm_one hc
  have e1 := qle (show (1 / 10 ^ 11 + 1163 / 10 ^ 11 : ℚ) ≤ ELF 4 by decide +kernel)
  have e2 := qle (show (1 / 10 ^ 11 + 229 / 20000000000 : ℚ) ≤ ELF 5 by decide +kernel)
  have e3 := qle (show (1 / 10 ^ 11 + 1161 / 10 ^ 11 : ℚ) ≤ ELF 6 by decide +kernel)
  have e4 := qle (show (1 / 10 ^ 11 + 1159 / 10 ^ 11 : ℚ) ≤ ELF 7 by decide +kernel)
  push_cast at e1 e2 e3 e4
  have hA6 : xLF c 6 = dTh (xLF c 4) := by rw [xLF_der_A hc0]; simp [dTh]
  have hB7 : xLF c 7 = dTh (xLF c 5) := by rw [xLF_der_B hc0]; simp [dTh]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hC.du.add ((fdist_u hc).strip hρA)
    rw [sub_add_sub_cancel] at this; exact this.le (by rw [μF]; push_cast; linarith)
  · have := hC.dz.add ((fdist_z hc).strip hρA)
    rw [sub_add_sub_cancel] at this; exact this.le (by rw [μF]; push_cast; linarith)
  · have := hC.dut.add ((fdist_a hc).strip hρA)
    rw [sub_add_sub_cancel, ← hA6] at this; exact this.le (by rw [μF]; push_cast; linarith)
  · have := hC.dzt.add ((fdist_b hc).strip hρA)
    rw [sub_add_sub_cancel, ← hB7] at this; exact this.le (by rw [μF]; push_cast; linarith)

/-- **Admissibility of every torus `μ`-close to the family torus** on a strip `0 < ρ ≤ r_A`, for
every parameter `|c| = 1`, with the constants `cF` (uniform over the cell). -/
theorem famAdm {ρ : ℝ} (hρ : 0 < ρ) (hρA : ρ ≤ KamTorusA.rA) {c : ℂ} (hc : ‖c‖ = 1) {u z : FA}
    (hu : Ana u) (hz : Ana z) (hC : Close ρ KamTorusA.iota u z (xHF c 4) (xHF c 5) μF) :
    (gcFlow (ρF c)).AdmBounds cF KamTorusA.iota ρ u z := by
  have hq : Real.exp ρ ≤ (74315 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hρA).trans exp_rA_le'
  obtain ⟨hU, hZ, hA, hB⟩ := inputs_LF hρA hc hC
  have hρ0 := hρ.le
  have tu : Bd ρ u auF := by
    have := hC.du.add ((Bd_uF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [auF]; linarith)
  have tz : Bd ρ z azF := by
    have := hC.dz.add ((Bd_zF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [azF]; linarith)
  have tRt : Bd ρ (dTh u) aRtF := by
    have := hC.dut.add ((Bd_dTh_uF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aRtF]; linarith)
  have tzt : Bd ρ (dTh z) aztF := by
    have := hC.dzt.add ((Bd_dTh_zF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aztF]; linarith)
  have tLR : Bd ρ (Lt KamTorusA.iota u) aLRF := by
    have := hC.duL.add ((Bd_Lt_uF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLRF]; linarith)
  have tLz : Bd ρ (Lt KamTorusA.iota z) aLzF := by
    have := hC.dzL.add ((Bd_Lt_zF hc).strip hρA); rw [sub_add_cancel] at this
    exact this.le (by rw [aLzF]; linarith)
  obtain ⟨hDu, hDb⟩ := adm_Di_F hρ hq hc hU hZ hA hB
  obtain ⟨hWu, hWb⟩ := adm_Wi_F hρ hq hc hU hZ hA hB
  have hR1 : Bd ρ ((1 + u) - algebraMap ℂ FA 1) auF := by
    rw [map_one, add_sub_cancel_left]; exact tu
  obtain ⟨hRu, hRb⟩ := Bd.inverse hρ0 hR1 (by rw [norm_one]; norm_num [auF, μF])
  rw [norm_one] at hRb
  obtain ⟨hT, hτ⟩ := adm_T_F hρ hq hc hU hZ hA hB
  have hgood : (gcFlow (ρF c)).Good u z := by
    refine ⟨ρ, hρ, avF, fun i => ?_,
      (gcFlow_valid _ avF (RationalStellaratorGCFamily.gc_maj_E_lt avF_le.1 avF_le.2)).1⟩
    have hcq : Real.exp ρ ≤ acG := by
      have := hq; push_cast at this; rw [acG]; linarith
    fin_cases i
    · exact tu
    · exact tz
    · exact (Bd_cS ρ).le hcq
    · exact (Bd_sS ρ).le hcq
    · exact Bd_zero ρ
    · exact Bd_zero ρ
  have fb : ∀ {X : FA} {i : ℕ} {q : ℚ}, Bd ρ X ((BLF i + ELF i : ℚ) : ℝ) → BLF i + ELF i ≤ q →
      Bd ρ X (q : ℝ) := fun h hq => h.le (qle hq)
  have v := valLF_le hρ0 hq hc hU hZ hA hB
  exact
  { frame := ⟨hu, hz, hDu, hRu, hWu, ⟨ρ, _, hρ, hDb⟩, ⟨ρ, _, hρ, hRb⟩, ⟨ρ, _, hρ, hWb⟩, hgood⟩
    hu := tu
    hz := tz
    hRt := tRt
    hzt := tzt
    hLR := tLR
    hLz := tLz
    hbD := by
      have := fb (v 116 (by norm_num)) (q := 12791 / 10000) (by decide +kernel)
      push_cast at this; exact this
    hbDu := by
      have := fb (v 122 (by norm_num)) (q := 22391 / 10000) (by decide +kernel)
      push_cast at this; exact this
    hbDz := by
      have := fb (v 124 (by norm_num)) (q := 20441 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnR := by
      have := fb (v 118 (by norm_num)) (q := 10201 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnRu := by
      have := fb (v 126 (by norm_num)) (q := 95121 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnRz := by
      have := fb (v 128 (by norm_num)) (q := 74651 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZ := by
      have := fb (v 120 (by norm_num)) (q := 10601 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZu := by
      have := fb (v 130 (by norm_num)) (q := 87241 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hbnZz := by
      have := fb (v 132 (by norm_num)) (q := 82001 / 100000) (by decide +kernel)
      push_cast at this; exact this
    hsD := hDb
    hsR := hRb
    hsW := hWb
    hT := hT
    hτ := hτ }

end PlasmaLean.Design.RationalStellaratorGC
