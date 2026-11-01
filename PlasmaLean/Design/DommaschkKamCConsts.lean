/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCAdm
public import PlasmaLean.Design.DommaschkKamCJet

/-!
# The constants of the KAM iteration for Dommaschk torus C (N-33 plan item 9)

**On-demand module** (imports the on-demand `Design/DommaschkKamCAdm`; not imported by
`PlasmaLean.lean`). Build: `lake build PlasmaLean.Design.DommaschkKamCConsts` (after
`lake build PlasmaLean.Design.DommaschkKamCAdm`).

The constants record `cDK : SCG` (`Design/KamFlowStepG`) of the generalised Newton step for torus C:
strip `ρ = 0.045`, initial loss `δ₀ = 9/1400 = ρ/7`, split Diophantine data `dlow = 0.1208`,
`γ = 0.2671`, `Klow = 1` (`DommaschkKamDio.dkIotaC_period_split`), exponent `p = 7`, error scale
`θ = e₀/δ₀⁴` with the error budget `e0qDK = 10⁻²⁴`, the certified admissibility constants
`auC … tauC` of `Design/DommaschkKamCAdmOut` (so `ConstsOK cDK` holds with equality, `cDK_ok`),
`ac = 68553/2¹⁶ ≥ e^{0.045}`, `E1 = 2.718`, `cKb = 30496`, `cLb = 930856` and the Taylor constant
`C₂ = 4.0797 × 10¹²`.

**Results.**
* `dk_globalHG : dkFieldTC.GlobalHG cDK ι_C`: all global conditions of the generalised KAM
  iteration (`FlowFieldG.GlobalHG`, `Design/KamFlowIterationG`). The Taylor constant comes from the
  rational jet mirror of `PolyExpr.majD2` (`Design/DommaschkKamCJet`, `majD2_resRp`,
  `majD2_resZp`), bounded by `kernel_fact`: `½ P̂''` is `4.05556 × 10¹²` (`R`) and
  `4.07969 × 10¹²` (`z`).
* The closed numeric fields of `FlowFieldG.KamHG … e0qDK muq`: `dk_δ0_pos`, `dk_ρ6`, `dk_θ`,
  `dk_e0_nonneg`, `dk_kap_pos`, `dk_small` (`32 κ e₀/δ₀⁴ ≈ 0.0764 ≤ 1`), `dk_cK_nonneg`,
  `dk_cL_nonneg`, `dk_μK`, `dk_μt`, `dk_μL` (budget `μ = 10⁻¹²`; actual `1.5 × 10⁻¹⁵`,
  `8.4 × 10⁻¹⁴`, `4.5 × 10⁻¹⁴`), and `dk_hadmC` (the field `hadm`, from `dk_hadm`).
* `dk_kamHG`: `FlowFieldG.KamHG dkFieldTC cDK ι_C u₀C z₀C e0qDK muq`, conditional only on the
  initial residual bounds `e0R`, `e0Z` (strip `0.045`, bound `e0qDK`), and `dk_exact_of_res`: the
  exact invariant torus (strip `9/1400`, `10⁻¹²`-close to torus C) under the same hypotheses.
* Certified values (cross-checked with `scripts/dommaschk_kam/kam_constants.py`, recomputed
  exactly by `scripts/dommaschk_kam/check_consts.py`): `cK = 30495.72`, `cL = 930855.43`,
  `κ = 4.07970 × 10¹²` (`dk_kap_le`); the largest admissible initial error is
  `δ₀⁴/(32κ) = 1.308 × 10⁻²³` for the smallness condition and `1.184 × 10⁻²³` for the displacement
  budget `hμt` with `μ = 10⁻¹²`. Any `e0qDK ≤ 1.15 × 10⁻²³` passes all checks of this module
  with the same `cKb`, `cLb`, `C₂` (adjust `e0qDK` and rebuild).

**Sanity.** `cDK_ok` (the certified constants are dominated with equality), `dk_kap_le`
(concrete), `dk_small_fails` (rejected fixture: the smallness condition fails for `e₀ = 10⁻²²`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Design.DommaschkKam WEll1Z2

/-! ## The constants -/

/-- **The error budget** `e₀ = 10⁻²⁴` of the initial residual on the strip `ρ = 0.045` (any value
`≤ 1.15 × 10⁻²³` passes the checks of this module). -/
def e0qDK : ℚ := 1 / 10 ^ 24

/-- The bound `cKb ≥ cK`. -/
def cKbq : ℚ := 30496

/-- The bound `cLb ≥ cL`. -/
def cLbq : ℚ := 930856

/-- The Taylor constant `C₂ = 4.0797 × 10¹²`. -/
def C2q : ℚ := 40797 * 10 ^ 8

/-- The bound `ac = 68553/2¹⁶ ≥ e^{0.045}` of `cos 2φ`, `sin 2φ`. -/
def acq : ℚ := 68553 / 2 ^ 16

/-- **The constants of the generalised Newton step for Dommaschk torus C.** -/
def cDK : SCG where
  ρ := 9 / 200
  δ0 := 9 / 1400
  γ := 2671 / 10000
  θ := (e0qDK : ℝ) / (9 / 1400) ^ 4
  au := (auC : ℝ)
  az := (azC : ℝ)
  aRt := (aRtC : ℝ)
  azt := (aztC : ℝ)
  aLR := (aLRC : ℝ)
  aLz := (aLzC : ℝ)
  ac := (acq : ℝ)
  bD := (bDC : ℝ)
  bDu := (bDuC : ℝ)
  bDz := (bDzC : ℝ)
  bnR := (bnRC : ℝ)
  bnRu := (bnRuC : ℝ)
  bnRz := (bnRzC : ℝ)
  bnZ := (bnZC : ℝ)
  bnZu := (bnZuC : ℝ)
  bnZz := (bnZzC : ℝ)
  sD := (sDC : ℝ)
  sR := (sRC : ℝ)
  sW := (sWC : ℝ)
  tT := (tTC : ℝ)
  τ := (tauC : ℝ)
  C2 := (C2q : ℝ)
  E1 := 2718 / 1000
  cKb := (cKbq : ℝ)
  cLb := (cLbq : ℝ)
  avR := (avRC : ℝ)
  avZ := (avZC : ℝ)
  aR := (aRC : ℝ)
  p := 7
  dlow := 1208 / 10000
  Klow := 1

/-- **Sanity**: `cDK` dominates the certified admissibility constants (with equality). -/
theorem cDK_ok : ConstsOK cDK := by
  refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl,
    le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/-! ## The derived constants -/

/-- Unfolding set for the derived constants of `cDK`. -/
macro "cDK_norm" : tactic =>
  `(tactic| (simp only [SCG.cK, SCG.k1, SCG.k2, SCG.kc, SCG.k20, SCG.g, SCG.kη1, SCG.kη2, SCG.kh,
    SCG.kE, SCG.tTot, SCG.τ', SCG.kTc, SCG.eM, SCG.mA, SCG.mV, SCG.cL, SCG.kA, SCG.XRb, SCG.XZb,
    SCG.kRem, SCG.kS, SCG.kap, cDK, e0qDK, cKbq, cLbq, C2q, acq, muq, auC, azC, avRC, avZC, aRC,
    aRtC, aztC, aLRC, aLzC, bDC, bDuC, bDzC, bnRC, bnRuC, bnRzC, bnZC, bnZuC, bnZzC, sDC, sRC, sWC,
    tTC, tauC, max_def]; norm_num))

/-- The twist margin `τ' > 0`. -/
theorem dk_τ' : 0 < cDK.τ' := by cDK_norm

/-- `cK ≤ cKb`. -/
theorem dk_cK : cDK.cK ≤ cDK.cKb := by cDK_norm

/-- `cL ≤ cLb`. -/
theorem dk_cL : cDK.cL ≤ cDK.cLb := by cDK_norm

/-- `cK ≥ 0`. -/
theorem dk_cK_nonneg : 0 ≤ cDK.cK := by cDK_norm

/-- `cL ≥ 0`. -/
theorem dk_cL_nonneg : 0 ≤ cDK.cL := by cDK_norm

/-- **Sanity (concrete)**: `κ ≤ 4.0798 × 10¹²` (certified value `4.07970 × 10¹²`). -/
theorem dk_kap_le : cDK.kap ≤ 40798 * 10 ^ 8 := by cDK_norm

/-- `κ > 0`. -/
theorem dk_kap_pos : 0 < cDK.kap := by cDK_norm

/-! ## The Taylor constant -/

/-- The rational scale `Tq = θ δ₀²`. -/
def TqQ : ℚ := e0qDK / (9 / 1400) ^ 4 * (9 / 1400) ^ 2

/-- `Tq` of `cDK` is the rational `TqQ`. -/
theorem cDK_Tq : cDK.Tq = (TqQ : ℝ) := by
  simp only [SCG.Tq, cDK, TqQ]; push_cast; ring

/-- The point of the Taylor estimate, coordinate `i`. -/
theorem cDK_pt (i : Fin 6) :
    (cDK.avec + cDK.Tq • cDK.mvec) i = cDK.avec i + (TqQ : ℝ) * cDK.mvec i := by
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, cDK_Tq]

/-- The rational `R`-Taylor majorant bound (kernel-checked). -/
theorem c2R_le : c2Q (auC + TqQ * cKbq) (azC + TqQ * cKbq) acq cKbq cKbq (aLRC + TqQ * cLbq) cLbq
    DommaschkKam.dnR ≤ C2q := by
  kernel_fact

/-- The rational `z`-Taylor majorant bound (kernel-checked). -/
theorem c2Z_le : c2Q (auC + TqQ * cKbq) (azC + TqQ * cKbq) acq cKbq cKbq (aLzC + TqQ * cLbq) cLbq
    DommaschkKam.dnZ ≤ C2q := by
  kernel_fact

/-- Unfolding of the Taylor point coordinates. -/
macro "dk_pt_tac" : tactic =>
  `(tactic| (rw [cDK_pt]; simp only [SCG.avec, SCG.mvec, cDK, Matrix.cons_val,
    Fin.isValue]; push_cast; ring))

/-- **The Taylor constant (`R`)**. -/
theorem dk_C2R : PolyExpr.majD2 (cDK.avec + cDK.Tq • cDK.mvec) cDK.mvec dkFieldTC.resRp / 2 ≤
    cDK.C2 := by
  rw [majD2_resRp (A0 := auC + TqQ * cKbq) (A1 := azC + TqQ * cKbq) (C := acq)
    (A4 := aLRC + TqQ * cLbq) (B0 := cKbq) (B1 := cKbq) (B4 := cLbq)
    (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac)
    (by simp [SCG.mvec, cDK]) (by simp [SCG.mvec, cDK]) (by simp [SCG.mvec])
    (by simp [SCG.mvec]) (by simp [SCG.mvec, cDK])]
  exact (Rat.cast_le (K := ℝ)).2 c2R_le

/-- **The Taylor constant (`z`)**. -/
theorem dk_C2Z : PolyExpr.majD2 (cDK.avec + cDK.Tq • cDK.mvec) cDK.mvec dkFieldTC.resZp / 2 ≤
    cDK.C2 := by
  rw [majD2_resZp (A0 := auC + TqQ * cKbq) (A1 := azC + TqQ * cKbq) (C := acq)
    (A5 := aLzC + TqQ * cLbq) (B0 := cKbq) (B1 := cKbq) (B5 := cLbq)
    (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac) (by dk_pt_tac)
    (by simp [SCG.mvec, cDK]) (by simp [SCG.mvec, cDK]) (by simp [SCG.mvec])
    (by simp [SCG.mvec]) (by simp [SCG.mvec, cDK])]
  exact (Rat.cast_le (K := ℝ)).2 c2Z_le

/-! ## The global conditions -/

/-- `e^{0.045} ≤ ac`. -/
theorem dk_hac : Real.exp cDK.ρ ≤ cDK.ac := by
  have h := exp_dk_le
  simp only [cDK, acq]; push_cast at h ⊢; exact h

/-- `0 < E1 ≤ e`. -/
theorem dk_hE1 : 0 < cDK.E1 ∧ cDK.E1 ≤ Real.exp 1 := by
  have := Real.exp_one_gt_d9
  simp only [cDK]; constructor <;> norm_num at this ⊢; linarith

/-- **The global conditions of the generalised KAM iteration for Dommaschk torus C.** -/
theorem dk_globalHG : dkFieldTC.GlobalHG cDK DommaschkKamDio.dkIotaC where
  hp := rfl
  dio := DommaschkKamDio.dkIotaC_period_split
  hK := le_rfl
  hd := by norm_num [cDK]
  γ_pos := by norm_num [cDK]
  hlow := DommaschkKamDio.dkC_low_δ0
  hτ' := dk_τ'
  hC2R := dk_C2R
  hC2Z := dk_C2Z
  hac := dk_hac
  hE1 := dk_hE1
  hcb := ⟨dk_cK, dk_cL⟩

/-! ## The closed numeric fields of `KamHG` (error budget `e0qDK`, displacement `μ = muq`) -/

/-- `δ₀ > 0`. -/
theorem dk_δ0_pos : 0 < cDK.δ0 := by norm_num [cDK]

/-- Room for the losses: `6δ₀ < ρ`. -/
theorem dk_ρ6 : 6 * cDK.δ0 < cDK.ρ := by norm_num [cDK]

/-- The error scale `θ = e₀/δ₀⁴`. -/
theorem dk_θ : cDK.θ = (e0qDK : ℝ) / cDK.δ0 ^ 4 := rfl

/-- `e₀ ≥ 0`. -/
theorem dk_e0_nonneg : 0 ≤ (e0qDK : ℝ) := by norm_num [e0qDK]

/-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1` (actual value `0.0764`). -/
theorem dk_small : 32 * cDK.kap * (e0qDK : ℝ) / cDK.δ0 ^ 4 ≤ 1 := by cDK_norm

/-- Displacement budget (torus). -/
theorem dk_μK : 2 * cDK.cK * (e0qDK : ℝ) / cDK.δ0 ^ 2 ≤ (muq : ℝ) := by cDK_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem dk_μt : 2 * (cDK.cK / cDK.E1) * (e0qDK : ℝ) / cDK.δ0 ^ 3 ≤ (muq : ℝ) := by cDK_norm

/-- Displacement budget (transport). -/
theorem dk_μL : 2 * cDK.cL * (e0qDK : ℝ) / cDK.δ0 ^ 2 ≤ (muq : ℝ) := by cDK_norm

/-- **Sanity (rejected fixture)**: the smallness condition fails for `e₀ = 10⁻²²`. -/
theorem dk_small_fails : ¬ 32 * cDK.kap * (1 / 10 ^ 22 : ℝ) / cDK.δ0 ^ 4 ≤ 1 := by
  rw [not_le]; cDK_norm

/-- **Admissibility** (the field `hadm` of `KamHG`, from `dk_hadm`): every `muq`-close analytic
torus is admissible for `cDK` on the strips `[ρ − 6δ₀, ρ]`. -/
theorem dk_hadmC : ∀ ρ u z, cDK.ρ - 6 * cDK.δ0 ≤ ρ → ρ ≤ cDK.ρ → Ana u → Ana z →
    Close ρ DommaschkKamDio.dkIotaC u z u₀C z₀C (muq : ℝ) →
    dkFieldTC.AdmBoundsG cDK DommaschkKamDio.dkIotaC ρ u z :=
  dk_hadm cDK_ok le_rfl le_rfl (by norm_num [cDK])

/-! ## Assembly, conditional on the initial residual -/

/-- **The KAM hypotheses for torus C, conditional on the initial residual bounds**: every field of
`FlowFieldG.KamHG dkFieldTC cDK ι_C u₀C z₀C e0qDK muq` except the initial errors `e0R`, `e0Z`
(the high-resolution residual chain) is closed here. -/
theorem dk_kamHG
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ)) :
    dkFieldTC.KamHG cDK DommaschkKamDio.dkIotaC u₀C z₀C (e0qDK : ℝ) (muq : ℝ) where
  G := dk_globalHG
  hδ0 := dk_δ0_pos
  hρ6 := dk_ρ6
  hθ := dk_θ
  he₀ := dk_e0_nonneg
  hκ := dk_kap_pos
  hsmall := dk_small
  hcK := dk_cK_nonneg
  hcL := dk_cL_nonneg
  hμK := dk_μK
  hμt := dk_μt
  hμL := dk_μL
  hadm := dk_hadmC
  ana_u₀ := ana_u₀C
  ana_z₀ := ana_z₀C
  real_u₀ := isReal_u₀C
  real_z₀ := isReal_z₀C
  e0R := e0R
  e0Z := e0Z

/-- The limiting strip `ρ_∞ = ρ − 6δ₀ = 9/1400`. -/
theorem dk_rInf : rInf cDK.toSC = 9 / 1400 := by
  unfold rInf; norm_num [cDK]

/-- **An exact invariant torus near torus C, conditional on the initial residual**: if the
residuals of the data torus are at most `e0qDK` on the strip `0.045`, there is a real analytic
torus solving the flow-form invariance equation of `dkFieldTC` exactly with rotational transform
`ι_C = −(85 + √5)/361`, `10⁻¹²`-close to torus C on the strip `9/1400`. -/
theorem dk_exact_of_res
    (e0R : Bd cDK.ρ (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ))
    (e0Z : Bd cDK.ρ (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) (e0qDK : ℝ)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      dkFieldTC.resR DommaschkKamDio.dkIotaC u z = 0 ∧
      dkFieldTC.resZ DommaschkKamDio.dkIotaC u z = 0 ∧
      Close (9 / 1400) DommaschkKamDio.dkIotaC u z u₀C z₀C (muq : ℝ) := by
  have h := (dk_kamHG e0R e0Z).kam_flow_torus
  rwa [dk_rInf] at h

end PlasmaLean.Design.DommaschkKamC
