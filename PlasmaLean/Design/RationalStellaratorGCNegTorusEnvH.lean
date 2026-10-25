/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallGrid
public import PlasmaLean.Design.RationalStellaratorGCNegTorusDataH1
public import PlasmaLean.Design.RationalStellaratorGCNegTorusDataH2
public import PlasmaLean.Design.RationalStellaratorGCNegTorusDataH3
public import PlasmaLean.Design.RationalStellaratorGCNegTorusDataH4
public import PlasmaLean.Design.RationalStellaratorGCNegTorusEnvL
public import PlasmaLean.Design.RationalStellaratorGCNegIota
public import PlasmaLean.Certificates.KernelFact

/-!
# The high-resolution ball environment of the guiding-centre torus certificate (`v∥ < 0`)

The variables of the high-resolution ball pipeline (`Certificates/KronBall`): layout
`N = 40`, `M = 30`, scale `2^{−101}`; the grids `gH i` of the centres, their polynomials `PH i`,
weights `WtH i`, degree boxes `BxH i`, `ℓ¹` bounds `LH i`, Kronecker images `KvH b W i`, and the
honest centres `xH i`; the norm bounds `BH i` of the centres and the radii `EH i` of the balls
(supplied by the oracle, checked in `Design/RationalStellaratorGCNegTorusCheckH*`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos 2φ`, `sin 2φ` (`xH_t`, `xH_V`, `xH_c`, `xH_s`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton

/-- Layout: poloidal half width. -/
def NH : ℕ := 40
/-- Layout: toroidal half width. -/
def MH : ℕ := 30
/-- Layout: scale exponent. -/
def SH : ℕ := 101
/-- Layout: field width of the packed data. -/
def FH : ℕ := 112

/-- Grid of the centre `U`. -/
def gH_U : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_U)

/-- Grid of the centre `Z`. -/
def gH_Z : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_Z)

/-- Grid of the centre `LRx`. -/
def gH_LRx : ℕ → ℕ → ℤ :=
  fun i j => (((IqB : ℕ) : ℤ) * ((i : ℤ) - NH) +
    ((2 ^ 97 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_U i j

/-- Grid of the centre `LZx`. -/
def gH_LZx : ℕ → ℕ → ℤ :=
  fun i j => (((IqB : ℕ) : ℤ) * ((i : ℤ) - NH) +
    ((2 ^ 97 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_Z i j

/-- Grid of the centre `thU`. -/
def gH_thU : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NH) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_U i j

/-- Grid of the centre `thZ`. -/
def gH_thZ : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NH) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_Z i j

/-- Grid of the centre `Ue`. -/
def gH_Ue : ℕ → ℕ → ℤ :=
  embedGrid NL ML (NH - NL) (MH - ML) (SH - SL) gL_U

/-- Grid of the centre `Ze`. -/
def gH_Ze : ℕ → ℕ → ℤ :=
  embedGrid NL ML (NH - NL) (MH - ML) (SH - SL) gL_Z

/-- Grid of the centre `thUe`. -/
def gH_thUe : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NH) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_Ue i j

/-- Grid of the centre `thZe`. -/
def gH_thZe : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NH) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MH)) * gH_Ze i j

/-- Grid of the centre `m02`. -/
def gH_m02 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_m02)

/-- Grid of the centre `m11`. -/
def gH_m11 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_m11)

/-- Grid of the centre `m20`. -/
def gH_m20 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_m20)

/-- Grid of the centre `m03`. -/
def gH_m03 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_m03)

/-- Grid of the centre `m12`. -/
def gH_m12 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_m12)

/-- Grid of the centre `m21`. -/
def gH_m21 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_m21)

/-- Grid of the centre `m30`. -/
def gH_m30 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_m30)

/-- Grid of the centre `m13`. -/
def gH_m13 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_m13)

/-- Grid of the centre `m22`. -/
def gH_m22 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_m22)

/-- Grid of the centre `m31`. -/
def gH_m31 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_m31)

/-- Grid of the centre `m40`. -/
def gH_m40 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_m40)

/-- Grid of the centre `m41`. -/
def gH_m41 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_m41)

/-- Grid of the centre `m50`. -/
def gH_m50 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_m50)

/-- Grid of the centre `m51`. -/
def gH_m51 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_m51)

/-- Grid of the centre `m60`. -/
def gH_m60 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_m60)

/-- Grid of the centre `Dp`. -/
def gH_Dp : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_Dp)

/-- Grid of the centre `nRp`. -/
def gH_nRp : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_nRp)

/-- Grid of the centre `nZp`. -/
def gH_nZp : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_nZp)

/-- Grid of the centre `DuP`. -/
def gH_DuP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_DuP)

/-- Grid of the centre `DzP`. -/
def gH_DzP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_DzP)

/-- Grid of the centre `DphP`. -/
def gH_DphP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_DphP)

/-- Grid of the centre `nRuP`. -/
def gH_nRuP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_nRuP)

/-- Grid of the centre `nRzP`. -/
def gH_nRzP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_nRzP)

/-- Grid of the centre `nRphP`. -/
def gH_nRphP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_nRphP)

/-- Grid of the centre `nZuP`. -/
def gH_nZuP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_nZuP)

/-- Grid of the centre `nZzP`. -/
def gH_nZzP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_nZzP)

/-- Grid of the centre `nZphP`. -/
def gH_nZphP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_nZphP)

/-- Grid of the centre `PuP`. -/
def gH_PuP : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_PuP)

/-- Grid of the centre `RD`. -/
def gH_RD : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_RD)

/-- Grid of the centre `RDu`. -/
def gH_RDu : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_RDu)

/-- Grid of the centre `RDz`. -/
def gH_RDz : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_RDz)

/-- Grid of the centre `RDph`. -/
def gH_RDph : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 1) (halfGridR FH NH datH_RDph)

/-- Grid of the centre `q`. -/
def gH_q : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_q)

/-- Grid of the centre `qR`. -/
def gH_qR : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_qR)

/-- Grid of the centre `qz`. -/
def gH_qz : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_qz)

/-- Grid of the centre `qph`. -/
def gH_qph : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_qph)

/-- Grid of the centre `P2`. -/
def gH_P2 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_P2)

/-- Grid of the centre `E`. -/
def gH_E : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_E)

/-- Grid of the centre `V0`. -/
def gH_V0 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_V0)

/-- Grid of the centre `W`. -/
def gH_W : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_W)

/-- Grid of the centre `W2`. -/
def gH_W2 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_W2)

/-- Grid of the centre `W3`. -/
def gH_W3 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_W3)

/-- Grid of the centre `R2`. -/
def gH_R2 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_R2)

/-- Grid of the centre `R3`. -/
def gH_R3 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_R3)

/-- Grid of the centre `A1`. -/
def gH_A1 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_A1)

/-- Grid of the centre `A2`. -/
def gH_A2 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_A2)

/-- Grid of the centre `K1`. -/
def gH_K1 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_K1)

/-- Grid of the centre `K2`. -/
def gH_K2 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_K2)

/-- Grid of the centre `K3`. -/
def gH_K3 : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_K3)

/-- Grid of the centre `KD`. -/
def gH_KD : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_KD)

/-- Grid of the centre `KR`. -/
def gH_KR : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_KR)

/-- Grid of the centre `KZ`. -/
def gH_KZ : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 2) (halfGridR FH NH datH_KZ)

/-- Grid of the centre `Dt`. -/
def gH_Dt : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_Dt)

/-- Grid of the centre `nRt`. -/
def gH_nRt : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 3) (halfGridR FH NH datH_nRt)

/-- Grid of the centre `nZt`. -/
def gH_nZt : ℕ → ℕ → ℤ :=
  symGrid NH MH ((-1) ^ 0) (halfGridR FH NH datH_nZt)

/-- Grid of the centre `Vn` (the centre `V0`). -/
def gH_Vn : ℕ → ℕ → ℤ :=
  gH_V0

/-- The grids of the variables (list; the constants `0, …, 3` have no grid). -/
def gHl : List (ℕ → ℕ → ℤ) :=
  [fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, gH_U, gH_Z, gH_LRx, gH_LZx, gH_thU,
    gH_thZ, gH_Ue, gH_Ze, gH_thUe, gH_thZe, gH_m02, gH_m11, gH_m20, gH_m03, gH_m12, gH_m21,
    gH_m30, gH_m13, gH_m22, gH_m31, gH_m40, gH_m41, gH_m50, gH_m51, gH_m60, gH_Dp, gH_nRp, gH_nZp,
    gH_DuP, gH_DzP, gH_DphP, gH_nRuP, gH_nRzP, gH_nRphP, gH_nZuP, gH_nZzP, gH_nZphP, gH_PuP,
    gH_RD, gH_RDu, gH_RDz, gH_RDph, gH_q, gH_qR, gH_qz, gH_qph, gH_P2, gH_E, gH_V0, gH_Vn, gH_W,
    gH_W2, gH_W3, gH_R2, gH_R3, gH_A1, gH_A2, gH_K1, gH_K2, gH_K3, gH_KD, gH_KR, gH_KZ, gH_Dt,
    gH_nRt, gH_nZt]

/-- The grids of the variables. -/
def gH (i : ℕ) : ℕ → ℕ → ℤ := gHl.getD i (fun _ _ => 0)

/-- The grids vanish beyond the last variable. -/
theorem gH_out (n : ℕ) : gH (n + 70) = fun _ _ => 0 := by
  unfold gH
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [gHl])]
  rfl

/-- The polynomials of the variables. -/
def PH : ℕ → P2
  | 0 => Tpoly SH NH MH
  | 1 => Vpoly
  | 2 => cPoly
  | 3 => sPoly
  | n + 4 => gridPolyNM NH MH (gH (n + 4))

/-- The weights of the variables (list). -/
def WtHl : List (ℕ × ℕ × ℕ) := 
  [(1, 0, 0), (0, 1, 0), (0, 1, 3), (0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 2), (1, 0, 0),
    (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 2),
    (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 0)]

/-- The weights of the variables. -/
def WtH (i : ℕ) : ℕ × ℕ × ℕ := WtHl.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def BxH : ℕ → ℕ × ℕ
  | 0 => (NH, MH)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NH, 2 * MH)

/-- The `ℓ¹` bounds of the variable polynomials (static: from the field width of the data). -/
def LH : ℕ → ℕ
  | 0 => 2 ^ SH
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 5 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 6 => (2 * NH + 1) * (2 * MH + 1) * ((IqB * NH + 2 ^ 97 * MH) * 2 ^ FH)
  | 7 => (2 * NH + 1) * (2 * MH + 1) * ((IqB * NH + 2 ^ 97 * MH) * 2 ^ FH)
  | 8 => (2 * NH + 1) * (2 * MH + 1) * ((1 * NH + 0 * MH) * 2 ^ FH)
  | 9 => (2 * NH + 1) * (2 * MH + 1) * ((1 * NH + 0 * MH) * 2 ^ FH)
  | 10 => (2 * NH + 1) * (2 * MH + 1) * (2 ^ (SH - SL) * 2 ^ FL)
  | 11 => (2 * NH + 1) * (2 * MH + 1) * (2 ^ (SH - SL) * 2 ^ FL)
  | 12 => (2 * NH + 1) * (2 * MH + 1) * ((1 * NH + 0 * MH) * (2 ^ (SH - SL) * 2 ^ FL))
  | 13 => (2 * NH + 1) * (2 * MH + 1) * ((1 * NH + 0 * MH) * (2 ^ (SH - SL) * 2 ^ FL))
  | 14 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 15 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 16 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 17 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 18 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 19 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 20 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 21 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 22 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 23 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 24 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 25 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 26 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 27 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 28 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 29 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 30 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 31 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 32 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 33 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 34 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 35 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 36 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 37 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 38 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 39 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 40 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 41 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 42 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 43 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 44 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 45 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 46 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 47 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 48 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 49 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 50 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 51 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 52 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 53 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 54 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 55 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 56 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 57 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 58 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 59 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 60 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 61 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 62 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 63 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 64 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 65 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 66 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 67 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 68 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | 69 => (2 * NH + 1) * (2 * MH + 1) * 2 ^ FH
  | _ => 0

/-- The Kronecker images of the variable polynomials. -/
def KvH (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SH * ((1 <<< (b * (NH + W * MH)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | n + 4 => packGridNM b W NH (gH (n + 4)) (2 * MH + 1)

/-- The honest centres. -/
def xH (i : ℕ) : FA := ctr SH NH MH (WtH i) (PH i)

/-- The phases are below `4`. -/
theorem hWH : ∀ i, (WtH i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxH : ∀ i, InBox (PH i) (BxH i).1 (BxH i).2
  | 0 => InBox.monomial NH MH _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_cPoly
  | 3 => box_sPoly
  | _ + 4 => box_gridPolyNM NH MH _

/-- `ℓ¹` bounds. -/
theorem l1H : ∀ i, l1 (PH i) ≤ LH i
  | 0 => l1_Tpoly SH NH MH
  | 1 => l1_Vpoly
  | 2 => l1_cPoly
  | 3 => l1_sPoly
  | 4 =>
    l1_dataGrid_le NH MH FH datH_U 0 (by kernel_fact)
  | 5 =>
    l1_dataGrid_le NH MH FH datH_Z 1 (by kernel_fact)
  | 6 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH IqB (2 ^ 97) (fun i j =>
      abs_dataGrid_le NH MH FH datH_U 0 (by kernel_fact) i j) hi hj
  | 7 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH IqB (2 ^ 97) (fun i j =>
      abs_dataGrid_le NH MH FH datH_Z 1 (by kernel_fact) i j) hi hj
  | 8 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH 1 0 (fun i j =>
      abs_dataGrid_le NH MH FH datH_U 0 (by kernel_fact) i j) hi hj
  | 9 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH 1 0 (fun i j =>
      abs_dataGrid_le NH MH FH datH_Z 1 (by kernel_fact) i j) hi hj
  | 10 =>
    l1_gridPolyNM_le_const NH MH fun i j _ _ => abs_embedGridN_le NL ML (NH - NL) (MH - ML) (SH
      - SL) (fun i j => abs_dataGrid_le NL ML FL datL_U 0 (by kernel_fact) i j) i j
  | 11 =>
    l1_gridPolyNM_le_const NH MH fun i j _ _ => abs_embedGridN_le NL ML (NH - NL) (MH - ML) (SH
      - SL) (fun i j => abs_dataGrid_le NL ML FL datL_Z 1 (by kernel_fact) i j) i j
  | 12 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH 1 0 (fun i j =>
      abs_embedGridN_le NL ML (NH - NL) (MH - ML) (SH - SL) (fun i j => abs_dataGrid_le NL ML FL
      datL_U 0 (by kernel_fact) i j) i j) hi hj
  | 13 =>
    l1_gridPolyNM_le_const NH MH fun i j hi hj => abs_wgridN_le NH MH 1 0 (fun i j =>
      abs_embedGridN_le NL ML (NH - NL) (MH - ML) (SH - SL) (fun i j => abs_dataGrid_le NL ML FL
      datL_Z 1 (by kernel_fact) i j) i j) hi hj
  | 14 =>
    l1_dataGrid_le NH MH FH datH_m02 2 (by kernel_fact)
  | 15 =>
    l1_dataGrid_le NH MH FH datH_m11 1 (by kernel_fact)
  | 16 =>
    l1_dataGrid_le NH MH FH datH_m20 0 (by kernel_fact)
  | 17 =>
    l1_dataGrid_le NH MH FH datH_m03 3 (by kernel_fact)
  | 18 =>
    l1_dataGrid_le NH MH FH datH_m12 2 (by kernel_fact)
  | 19 =>
    l1_dataGrid_le NH MH FH datH_m21 1 (by kernel_fact)
  | 20 =>
    l1_dataGrid_le NH MH FH datH_m30 0 (by kernel_fact)
  | 21 =>
    l1_dataGrid_le NH MH FH datH_m13 3 (by kernel_fact)
  | 22 =>
    l1_dataGrid_le NH MH FH datH_m22 2 (by kernel_fact)
  | 23 =>
    l1_dataGrid_le NH MH FH datH_m31 1 (by kernel_fact)
  | 24 =>
    l1_dataGrid_le NH MH FH datH_m40 0 (by kernel_fact)
  | 25 =>
    l1_dataGrid_le NH MH FH datH_m41 1 (by kernel_fact)
  | 26 =>
    l1_dataGrid_le NH MH FH datH_m50 0 (by kernel_fact)
  | 27 =>
    l1_dataGrid_le NH MH FH datH_m51 1 (by kernel_fact)
  | 28 =>
    l1_dataGrid_le NH MH FH datH_m60 0 (by kernel_fact)
  | 29 =>
    l1_dataGrid_le NH MH FH datH_Dp 0 (by kernel_fact)
  | 30 =>
    l1_dataGrid_le NH MH FH datH_nRp 3 (by kernel_fact)
  | 31 =>
    l1_dataGrid_le NH MH FH datH_nZp 0 (by kernel_fact)
  | 32 =>
    l1_dataGrid_le NH MH FH datH_DuP 0 (by kernel_fact)
  | 33 =>
    l1_dataGrid_le NH MH FH datH_DzP 3 (by kernel_fact)
  | 34 =>
    l1_dataGrid_le NH MH FH datH_DphP 1 (by kernel_fact)
  | 35 =>
    l1_dataGrid_le NH MH FH datH_nRuP 3 (by kernel_fact)
  | 36 =>
    l1_dataGrid_le NH MH FH datH_nRzP 0 (by kernel_fact)
  | 37 =>
    l1_dataGrid_le NH MH FH datH_nRphP 0 (by kernel_fact)
  | 38 =>
    l1_dataGrid_le NH MH FH datH_nZuP 0 (by kernel_fact)
  | 39 =>
    l1_dataGrid_le NH MH FH datH_nZzP 1 (by kernel_fact)
  | 40 =>
    l1_dataGrid_le NH MH FH datH_nZphP 3 (by kernel_fact)
  | 41 =>
    l1_dataGrid_le NH MH FH datH_PuP 0 (by kernel_fact)
  | 42 =>
    l1_dataGrid_le NH MH FH datH_RD 0 (by kernel_fact)
  | 43 =>
    l1_dataGrid_le NH MH FH datH_RDu 0 (by kernel_fact)
  | 44 =>
    l1_dataGrid_le NH MH FH datH_RDz 3 (by kernel_fact)
  | 45 =>
    l1_dataGrid_le NH MH FH datH_RDph 1 (by kernel_fact)
  | 46 =>
    l1_dataGrid_le NH MH FH datH_q 2 (by kernel_fact)
  | 47 =>
    l1_dataGrid_le NH MH FH datH_qR 0 (by kernel_fact)
  | 48 =>
    l1_dataGrid_le NH MH FH datH_qz 3 (by kernel_fact)
  | 49 =>
    l1_dataGrid_le NH MH FH datH_qph 3 (by kernel_fact)
  | 50 =>
    l1_dataGrid_le NH MH FH datH_P2 0 (by kernel_fact)
  | 51 =>
    l1_dataGrid_le NH MH FH datH_E 2 (by kernel_fact)
  | 52 =>
    l1_dataGrid_le NH MH FH datH_V0 0 (by kernel_fact)
  | 53 =>
    l1_dataGrid_le NH MH FH datH_V0 0 (by kernel_fact)
  | 54 =>
    l1_dataGrid_le NH MH FH datH_W 0 (by kernel_fact)
  | 55 =>
    l1_dataGrid_le NH MH FH datH_W2 0 (by kernel_fact)
  | 56 =>
    l1_dataGrid_le NH MH FH datH_W3 0 (by kernel_fact)
  | 57 =>
    l1_dataGrid_le NH MH FH datH_R2 0 (by kernel_fact)
  | 58 =>
    l1_dataGrid_le NH MH FH datH_R3 0 (by kernel_fact)
  | 59 =>
    l1_dataGrid_le NH MH FH datH_A1 0 (by kernel_fact)
  | 60 =>
    l1_dataGrid_le NH MH FH datH_A2 3 (by kernel_fact)
  | 61 =>
    l1_dataGrid_le NH MH FH datH_K1 0 (by kernel_fact)
  | 62 =>
    l1_dataGrid_le NH MH FH datH_K2 3 (by kernel_fact)
  | 63 =>
    l1_dataGrid_le NH MH FH datH_K3 2 (by kernel_fact)
  | 64 =>
    l1_dataGrid_le NH MH FH datH_KD 0 (by kernel_fact)
  | 65 =>
    l1_dataGrid_le NH MH FH datH_KR 3 (by kernel_fact)
  | 66 =>
    l1_dataGrid_le NH MH FH datH_KZ 2 (by kernel_fact)
  | 67 =>
    l1_dataGrid_le NH MH FH datH_Dt 0 (by kernel_fact)
  | 68 =>
    l1_dataGrid_le NH MH FH datH_nRt 3 (by kernel_fact)
  | 69 =>
    l1_dataGrid_le NH MH FH datH_nZt 0 (by kernel_fact)
  | n + 70 =>
    (l1_gridPolyNM_le_const NH MH (C := 0) fun i j _ _ => by rw [gH_out n]; simp).trans
      (by simp)

/-- Kronecker images. -/
theorem kronH : ∀ b W i, kron b W (PH i) = KvH b W i
  | b, W, 0 => kron_Tpoly SH NH MH b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_cPoly b W
  | b, W, 3 => kron_sPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NH MH _

/-- The centre of `t` is `1`. -/
theorem xH_t : xH 0 = 1 := ctr_Tpoly SH NH MH

/-- The centre of `V` is `1`. -/
theorem xH_V : xH 1 = 1 := ctr_Vpoly SH NH MH

/-- The norm bounds of the centres (list). -/
def BHl : List ℚ := 
  [(1 : ℚ), (1 : ℚ), (74315 / 2 ^ 16 : ℚ), (74315 / 2 ^ 16 : ℚ), (1087 / 5000 : ℚ),
    (897 / 5000 : ℚ), (10450000000000000000000000000 : ℚ), (9679000000000000000000000000 : ℚ),
    (909 / 5000 : ℚ), (1749 / 10 ^ 4 : ℚ), (1087 / 5000 : ℚ), (897 / 5000 : ℚ), (909 / 5000 : ℚ),
    (1749 / 10 ^ 4 : ℚ), (71 / 2500 : ℚ), (999 / 50000 : ℚ), (4241 / 10 ^ 5 : ℚ),
    (4437 / 10 ^ 6 : ℚ), (711 / 250000 : ℚ), (3347 / 10 ^ 6 : ℚ), (1047 / 125000 : ℚ),
    (3583 / 10 ^ 7 : ℚ), (3309 / 10 ^ 7 : ℚ), (5463 / 10 ^ 7 : ℚ), (1637 / 10 ^ 6 : ℚ),
    (9579 / 10 ^ 8 : ℚ), (319 / 10 ^ 6 : ℚ), (421 / 25000000 : ℚ), (6187 / 10 ^ 8 : ℚ),
    (731 / 500 : ℚ), (1699 / 10 ^ 4 : ℚ), (853 / 5000 : ℚ), (603 / 250 : ℚ), (307 / 1250 : ℚ),
    (3539 / 10 ^ 5 : ℚ), (1317 / 10 ^ 3 : ℚ), (3871 / 5000 : ℚ), (3679 / 10 ^ 4 : ℚ),
    (133 / 125 : ℚ), (1927 / 2000 : ℚ), (629 / 2000 : ℚ), (733 / 500 : ℚ), (7 / 2 ^ 2 : ℚ),
    (107 / 40 : ℚ), (2759 / 10 ^ 4 : ℚ), (4183 / 10 ^ 5 : ℚ), (1511 / 500 : ℚ), (358 / 25 : ℚ),
    (6901 / 10 ^ 4 : ℚ), (757 / 5000 : ℚ), (409 / 200 : ℚ), (857 / 25000 : ℚ), (509 / 500 : ℚ),
    (509 / 500 : ℚ), (737 / 500 : ℚ), (517 / 250 : ℚ), (2911 / 10 ^ 3 : ℚ), (1471 / 10 ^ 3 : ℚ),
    (1777 / 10 ^ 3 : ℚ), (859 / 50 : ℚ), (7939 / 10 ^ 4 : ℚ), (1037 / 10 ^ 3 : ℚ),
    (303 / 250 : ℚ), (1207 / 10 ^ 2 : ℚ), (1481 / 10 ^ 3 : ℚ), (1929 / 10 ^ 3 : ℚ),
    (1041 / 50 : ℚ), (1463 / 10 ^ 3 : ℚ), (1691 / 10 ^ 4 : ℚ), (407 / 2500 : ℚ)]

/-- The norm bounds of the centres. -/
def BH (i : ℕ) : ℚ := BHl.getD i 0

/-- The radii of the balls (list). -/
def EHl : List ℚ := 
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (1441 / 10 ^ 4 : ℚ), (693 / 5000 : ℚ),
    (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (117 / 10 ^ 28 : ℚ),
    (117 / 10 ^ 28 : ℚ), (113 / 10 ^ 28 : ℚ), (131 / 10 ^ 28 : ℚ), (13 / 10 ^ 27 : ℚ),
    (133 / 10 ^ 28 : ℚ), (7 / 500000000000000000000000000 : ℚ),
    (61 / 5000000000000000000000000000 : ℚ), (33 / 2500000000000000000000000000 : ℚ),
    (1 / 78125000000000000000000000 : ℚ), (139 / 10 ^ 28 : ℚ), (131 / 10 ^ 28 : ℚ),
    (143 / 10 ^ 28 : ℚ), (127 / 10 ^ 28 : ℚ), (141 / 10 ^ 28 : ℚ), (757 / 10 ^ 28 : ℚ),
    (137 / 10 ^ 27 : ℚ), (11 / 10 ^ 26 : ℚ), (697 / 10 ^ 28 : ℚ), (427 / 10 ^ 28 : ℚ),
    (59 / 500000000000000000000000000 : ℚ), (259 / 10 ^ 27 : ℚ),
    (29 / 250000000000000000000000000 : ℚ), (131 / 500000000000000000000000000 : ℚ),
    (149 / 10 ^ 27 : ℚ), (201 / 2500000000000000000000000000 : ℚ), (207 / 10 ^ 27 : ℚ),
    (7 / 6250000000000000000000000 : ℚ), (53 / 500000000000000000000000000 : ℚ),
    (981 / 10 ^ 28 : ℚ), (13 / 200000000000000000000000000 : ℚ), (157 / 10 ^ 27 : ℚ),
    (59 / 125000000000000000000000000 : ℚ), (7 / 3125000000000000000000000 : ℚ),
    (159 / 200000000000000000000000000 : ℚ), (907 / 10 ^ 27 : ℚ), (331 / 10 ^ 26 : ℚ),
    (11 / 10 ^ 24 : ℚ), (0 : ℚ), (63 / 10 ^ 25 : ℚ), (21 / 2000000000000000000000000 : ℚ),
    (31 / 10 ^ 24 : ℚ), (27 / 400000000000000000000000 : ℚ), (113 / 10 ^ 28 : ℚ),
    (259 / 10 ^ 28 : ℚ), (11 / 4000000000000000000000000 : ℚ),
    (493 / 500000000000000000000000000 : ℚ), (597 / 10 ^ 26 : ℚ), (201 / 10 ^ 26 : ℚ),
    (161 / 10 ^ 25 : ℚ), (441 / 50000000000000000000000000 : ℚ), (363 / 10 ^ 26 : ℚ),
    (29 / 10 ^ 24 : ℚ), (21 / 62500000000000000000000000 : ℚ), (427 / 10 ^ 27 : ℚ),
    (19 / 6250000000000000000000000 : ℚ)]

/-- The radii of the balls. -/
def EH (i : ℕ) : ℚ := EHl.getD i 0

end PlasmaLean.Design.RationalStellaratorGCNeg
