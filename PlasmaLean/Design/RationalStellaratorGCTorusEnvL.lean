/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronBallGrid
public import PlasmaLean.Design.RationalStellaratorGCTorusDataL
public import PlasmaLean.Design.KamFlowField
public import PlasmaLean.Certificates.KernelFact

/-!
# The low-resolution ball environment of the guiding-centre torus certificate

The variables of the low-resolution ball pipeline (`Certificates/KronBall`): layout
`N = 16`, `M = 12`, scale `2^{−60}`; the grids `gL i` of the centres, their polynomials `PL i`,
weights `WtL i`, degree boxes `BxL i`, `ℓ¹` bounds `LL i`, Kronecker images `KvL b W i`, and the
honest centres `xL i`; the norm bounds `BL i` of the centres and the radii `EL i` of the balls
(supplied by the oracle, checked in `Design/RationalStellaratorGCTorusCheckL*`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos 2φ`, `sin 2φ` (`xL_t`, `xL_V`, `xL_c`, `xL_s`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton

/-- Layout: poloidal half width. -/
def NL : ℕ := 16
/-- Layout: toroidal half width. -/
def ML : ℕ := 12
/-- Layout: scale exponent. -/
def SL : ℕ := 60
/-- Layout: field width of the packed data. -/
def FL : ℕ := 80

/-- Grid of the centre `U`. -/
def gL_U : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_U)

/-- Grid of the centre `Z`. -/
def gL_Z : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_Z)

/-- Grid of the centre `A`. -/
def gL_A : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NL) + ((0 : ℕ) : ℤ) * ((j : ℤ) - ML)) * gL_U i j

/-- Grid of the centre `B`. -/
def gL_B : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NL) + ((0 : ℕ) : ℤ) * ((j : ℤ) - ML)) * gL_Z i j

/-- Grid of the centre `m02`. -/
def gL_m02 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_m02)

/-- Grid of the centre `m11`. -/
def gL_m11 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_m11)

/-- Grid of the centre `m20`. -/
def gL_m20 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_m20)

/-- Grid of the centre `m03`. -/
def gL_m03 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_m03)

/-- Grid of the centre `m12`. -/
def gL_m12 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_m12)

/-- Grid of the centre `m21`. -/
def gL_m21 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_m21)

/-- Grid of the centre `m30`. -/
def gL_m30 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_m30)

/-- Grid of the centre `m13`. -/
def gL_m13 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_m13)

/-- Grid of the centre `m22`. -/
def gL_m22 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_m22)

/-- Grid of the centre `m31`. -/
def gL_m31 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_m31)

/-- Grid of the centre `m40`. -/
def gL_m40 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_m40)

/-- Grid of the centre `m41`. -/
def gL_m41 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_m41)

/-- Grid of the centre `m50`. -/
def gL_m50 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_m50)

/-- Grid of the centre `m51`. -/
def gL_m51 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_m51)

/-- Grid of the centre `m60`. -/
def gL_m60 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_m60)

/-- Grid of the centre `Dp`. -/
def gL_Dp : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Dp)

/-- Grid of the centre `nRp`. -/
def gL_nRp : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRp)

/-- Grid of the centre `nZp`. -/
def gL_nZp : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZp)

/-- Grid of the centre `DuP`. -/
def gL_DuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_DuP)

/-- Grid of the centre `DzP`. -/
def gL_DzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_DzP)

/-- Grid of the centre `DphP`. -/
def gL_DphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_DphP)

/-- Grid of the centre `nRuP`. -/
def gL_nRuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRuP)

/-- Grid of the centre `nRzP`. -/
def gL_nRzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nRzP)

/-- Grid of the centre `nRphP`. -/
def gL_nRphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nRphP)

/-- Grid of the centre `nZuP`. -/
def gL_nZuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZuP)

/-- Grid of the centre `nZzP`. -/
def gL_nZzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_nZzP)

/-- Grid of the centre `nZphP`. -/
def gL_nZphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nZphP)

/-- Grid of the centre `PuP`. -/
def gL_PuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_PuP)

/-- Grid of the centre `PdP`. -/
def gL_PdP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_PdP)

/-- Grid of the centre `DuuP`. -/
def gL_DuuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_DuuP)

/-- Grid of the centre `DuzP`. -/
def gL_DuzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_DuzP)

/-- Grid of the centre `DzzP`. -/
def gL_DzzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_DzzP)

/-- Grid of the centre `DuphP`. -/
def gL_DuphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_DuphP)

/-- Grid of the centre `DzphP`. -/
def gL_DzphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_DzphP)

/-- Grid of the centre `nRuuP`. -/
def gL_nRuuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRuuP)

/-- Grid of the centre `nRuzP`. -/
def gL_nRuzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nRuzP)

/-- Grid of the centre `nRzzP`. -/
def gL_nRzzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRzzP)

/-- Grid of the centre `nRuphP`. -/
def gL_nRuphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nRuphP)

/-- Grid of the centre `nRzphP`. -/
def gL_nRzphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRzphP)

/-- Grid of the centre `nZuuP`. -/
def gL_nZuuP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZuuP)

/-- Grid of the centre `nZuzP`. -/
def gL_nZuzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_nZuzP)

/-- Grid of the centre `nZzzP`. -/
def gL_nZzzP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZzzP)

/-- Grid of the centre `nZuphP`. -/
def gL_nZuphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nZuphP)

/-- Grid of the centre `nZzphP`. -/
def gL_nZzphP : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZzphP)

/-- Grid of the centre `RD`. -/
def gL_RD : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_RD)

/-- Grid of the centre `RDu`. -/
def gL_RDu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_RDu)

/-- Grid of the centre `RDz`. -/
def gL_RDz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_RDz)

/-- Grid of the centre `RDph`. -/
def gL_RDph : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_RDph)

/-- Grid of the centre `q`. -/
def gL_q : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_q)

/-- Grid of the centre `qR`. -/
def gL_qR : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qR)

/-- Grid of the centre `qz`. -/
def gL_qz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_qz)

/-- Grid of the centre `qph`. -/
def gL_qph : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_qph)

/-- Grid of the centre `P2`. -/
def gL_P2 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_P2)

/-- Grid of the centre `E`. -/
def gL_E : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_E)

/-- Grid of the centre `V0`. -/
def gL_V0 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_V0)

/-- Grid of the centre `W`. -/
def gL_W : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W)

/-- Grid of the centre `W2`. -/
def gL_W2 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W2)

/-- Grid of the centre `W3`. -/
def gL_W3 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W3)

/-- Grid of the centre `R2`. -/
def gL_R2 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_R2)

/-- Grid of the centre `R3`. -/
def gL_R3 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_R3)

/-- Grid of the centre `A1`. -/
def gL_A1 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_A1)

/-- Grid of the centre `A2`. -/
def gL_A2 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_A2)

/-- Grid of the centre `K1`. -/
def gL_K1 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_K1)

/-- Grid of the centre `K2`. -/
def gL_K2 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_K2)

/-- Grid of the centre `K3`. -/
def gL_K3 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_K3)

/-- Grid of the centre `KD`. -/
def gL_KD : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_KD)

/-- Grid of the centre `KR`. -/
def gL_KR : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_KR)

/-- Grid of the centre `KZ`. -/
def gL_KZ : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_KZ)

/-- Grid of the centre `Dt`. -/
def gL_Dt : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Dt)

/-- Grid of the centre `nRt`. -/
def gL_nRt : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRt)

/-- Grid of the centre `nZt`. -/
def gL_nZt : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZt)

/-- Grid of the centre `qRu`. -/
def gL_qRu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qRu)

/-- Grid of the centre `qRz`. -/
def gL_qRz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_qRz)

/-- Grid of the centre `qzz`. -/
def gL_qzz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qzz)

/-- Grid of the centre `qzu`. -/
def gL_qzu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_qzu)

/-- Grid of the centre `qphu`. -/
def gL_qphu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_qphu)

/-- Grid of the centre `qphz`. -/
def gL_qphz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qphz)

/-- Grid of the centre `qu`. -/
def gL_qu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qu)

/-- Grid of the centre `qzd`. -/
def gL_qzd : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_qzd)

/-- Grid of the centre `Eu`. -/
def gL_Eu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_Eu)

/-- Grid of the centre `Ez`. -/
def gL_Ez : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_Ez)

/-- Grid of the centre `V3`. -/
def gL_V3 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_V3)

/-- Grid of the centre `Wu`. -/
def gL_Wu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Wu)

/-- Grid of the centre `Wz`. -/
def gL_Wz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_Wz)

/-- Grid of the centre `W3u`. -/
def gL_W3u : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W3u)

/-- Grid of the centre `W3z`. -/
def gL_W3z : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_W3z)

/-- Grid of the centre `KDu`. -/
def gL_KDu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_KDu)

/-- Grid of the centre `KDz`. -/
def gL_KDz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_KDz)

/-- Grid of the centre `KRu`. -/
def gL_KRu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_KRu)

/-- Grid of the centre `KRz`. -/
def gL_KRz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_KRz)

/-- Grid of the centre `KZu`. -/
def gL_KZu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 2) (halfGridR FL NL datL_KZu)

/-- Grid of the centre `KZz`. -/
def gL_KZz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_KZz)

/-- Grid of the centre `Dtu`. -/
def gL_Dtu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Dtu)

/-- Grid of the centre `Dtz`. -/
def gL_Dtz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_Dtz)

/-- Grid of the centre `nRtu`. -/
def gL_nRtu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 3) (halfGridR FL NL datL_nRtu)

/-- Grid of the centre `nRtz`. -/
def gL_nRtz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nRtz)

/-- Grid of the centre `nZtu`. -/
def gL_nZtu : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_nZtu)

/-- Grid of the centre `nZtz`. -/
def gL_nZtz : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 1) (halfGridR FL NL datL_nZtz)

/-- Grid of the centre `Ptor`. -/
def gL_Ptor : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Ptor)

/-- Grid of the centre `W0`. -/
def gL_W0 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W0)

/-- Grid of the centre `Dt3`. -/
def gL_Dt3 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Dt3)

/-- Grid of the centre `W02`. -/
def gL_W02 : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_W02)

/-- Grid of the centre `F`. -/
def gL_F : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_F)

/-- Grid of the centre `qi`. -/
def gL_qi : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_qi)

/-- Grid of the centre `Y`. -/
def gL_Y : ℕ → ℕ → ℤ :=
  symGrid NL ML ((-1) ^ 0) (halfGridR FL NL datL_Y)

/-- Grid of the centre `Vn` (the centre `V0`). -/
def gL_Vn : ℕ → ℕ → ℤ :=
  gL_V0

/-- The grids of the variables (list; the constants `0, …, 3` have no grid). -/
def gLl : List (ℕ → ℕ → ℤ) :=
  [fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, gL_U, gL_Z, gL_A, gL_B, gL_m02, gL_m11,
    gL_m20, gL_m03, gL_m12, gL_m21, gL_m30, gL_m13, gL_m22, gL_m31, gL_m40, gL_m41, gL_m50,
    gL_m51, gL_m60, gL_Dp, gL_nRp, gL_nZp, gL_DuP, gL_DzP, gL_DphP, gL_nRuP, gL_nRzP, gL_nRphP,
    gL_nZuP, gL_nZzP, gL_nZphP, gL_PuP, gL_PdP, gL_DuuP, gL_DuzP, gL_DzzP, gL_DuphP, gL_DzphP,
    gL_nRuuP, gL_nRuzP, gL_nRzzP, gL_nRuphP, gL_nRzphP, gL_nZuuP, gL_nZuzP, gL_nZzzP, gL_nZuphP,
    gL_nZzphP, gL_RD, gL_RDu, gL_RDz, gL_RDph, gL_q, gL_qR, gL_qz, gL_qph, gL_P2, gL_E, gL_V0,
    gL_Vn, gL_W, gL_W2, gL_W3, gL_R2, gL_R3, gL_A1, gL_A2, gL_K1, gL_K2, gL_K3, gL_KD, gL_KR,
    gL_KZ, gL_Dt, gL_nRt, gL_nZt, gL_qRu, gL_qRz, gL_qzz, gL_qzu, gL_qphu, gL_qphz, gL_qu, gL_qzd,
    gL_Eu, gL_Ez, gL_V3, gL_Wu, gL_Wz, gL_W3u, gL_W3z, gL_KDu, gL_KDz, gL_KRu, gL_KRz, gL_KZu,
    gL_KZz, gL_Dtu, gL_Dtz, gL_nRtu, gL_nRtz, gL_nZtu, gL_nZtz, gL_Ptor, gL_W0, gL_Dt3, gL_W02,
    gL_F, gL_qi, gL_Y]

/-- The grids of the variables. -/
def gL (i : ℕ) : ℕ → ℕ → ℤ := gLl.getD i (fun _ _ => 0)

/-- The grids vanish beyond the last variable. -/
theorem gL_out (n : ℕ) : gL (n + 114) = fun _ _ => 0 := by
  unfold gL
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [gLl])]
  rfl

/-- The polynomials of the variables. -/
def PL : ℕ → P2
  | 0 => Tpoly SL NL ML
  | 1 => Vpoly
  | 2 => cPoly
  | 3 => sPoly
  | n + 4 => gridPolyNM NL ML (gL (n + 4))

/-- The weights of the variables (list). -/
def WtLl : List (ℕ × ℕ × ℕ) := 
  [(1, 0, 0), (0, 1, 0), (0, 1, 3), (0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1),
    (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 3),
    (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0)]

/-- The weights of the variables. -/
def WtL (i : ℕ) : ℕ × ℕ × ℕ := WtLl.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def BxL : ℕ → ℕ × ℕ
  | 0 => (NL, ML)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NL, 2 * ML)

/-- The `ℓ¹` bounds of the variable polynomials (static: from the field width of the data). -/
def LL : ℕ → ℕ
  | 0 => 2 ^ SL
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 5 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 6 => (2 * NL + 1) * (2 * ML + 1) * ((1 * NL + 0 * ML) * 2 ^ FL)
  | 7 => (2 * NL + 1) * (2 * ML + 1) * ((1 * NL + 0 * ML) * 2 ^ FL)
  | 8 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 9 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 10 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 11 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 12 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 13 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 14 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 15 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 16 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 17 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 18 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 19 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 20 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 21 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 22 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 23 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 24 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 25 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 26 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 27 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 28 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 29 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 30 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 31 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 32 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 33 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 34 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 35 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 36 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 37 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 38 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 39 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 40 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 41 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 42 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 43 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 44 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 45 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 46 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 47 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 48 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 49 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 50 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 51 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 52 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 53 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 54 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 55 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 56 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 57 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 58 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 59 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 60 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 61 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 62 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 63 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 64 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 65 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 66 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 67 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 68 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 69 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 70 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 71 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 72 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 73 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 74 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 75 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 76 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 77 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 78 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 79 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 80 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 81 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 82 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 83 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 84 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 85 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 86 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 87 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 88 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 89 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 90 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 91 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 92 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 93 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 94 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 95 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 96 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 97 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 98 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 99 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 100 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 101 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 102 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 103 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 104 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 105 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 106 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 107 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 108 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 109 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 110 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 111 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 112 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | 113 => (2 * NL + 1) * (2 * ML + 1) * 2 ^ FL
  | _ => 0

/-- The Kronecker images of the variable polynomials. -/
def KvL (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SL * ((1 <<< (b * (NL + W * ML)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | n + 4 => packGridNM b W NL (gL (n + 4)) (2 * ML + 1)

/-- The honest centres. -/
def xL (i : ℕ) : FA := ctr SL NL ML (WtL i) (PL i)

/-- The phases are below `4`. -/
theorem hWL : ∀ i, (WtL i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxL : ∀ i, InBox (PL i) (BxL i).1 (BxL i).2
  | 0 => InBox.monomial NL ML _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_cPoly
  | 3 => box_sPoly
  | _ + 4 => box_gridPolyNM NL ML _

/-- `ℓ¹` bounds. -/
theorem l1L : ∀ i, l1 (PL i) ≤ LL i
  | 0 => l1_Tpoly SL NL ML
  | 1 => l1_Vpoly
  | 2 => l1_cPoly
  | 3 => l1_sPoly
  | 4 =>
    l1_dataGrid_le NL ML FL datL_U 0 (by kernel_fact)
  | 5 =>
    l1_dataGrid_le NL ML FL datL_Z 1 (by kernel_fact)
  | 6 =>
    l1_gridPolyNM_le_const NL ML fun i j hi hj => abs_wgridN_le NL ML 1 0 (fun i j =>
      abs_dataGrid_le NL ML FL datL_U 0 (by kernel_fact) i j) hi hj
  | 7 =>
    l1_gridPolyNM_le_const NL ML fun i j hi hj => abs_wgridN_le NL ML 1 0 (fun i j =>
      abs_dataGrid_le NL ML FL datL_Z 1 (by kernel_fact) i j) hi hj
  | 8 =>
    l1_dataGrid_le NL ML FL datL_m02 2 (by kernel_fact)
  | 9 =>
    l1_dataGrid_le NL ML FL datL_m11 1 (by kernel_fact)
  | 10 =>
    l1_dataGrid_le NL ML FL datL_m20 0 (by kernel_fact)
  | 11 =>
    l1_dataGrid_le NL ML FL datL_m03 3 (by kernel_fact)
  | 12 =>
    l1_dataGrid_le NL ML FL datL_m12 2 (by kernel_fact)
  | 13 =>
    l1_dataGrid_le NL ML FL datL_m21 1 (by kernel_fact)
  | 14 =>
    l1_dataGrid_le NL ML FL datL_m30 0 (by kernel_fact)
  | 15 =>
    l1_dataGrid_le NL ML FL datL_m13 3 (by kernel_fact)
  | 16 =>
    l1_dataGrid_le NL ML FL datL_m22 2 (by kernel_fact)
  | 17 =>
    l1_dataGrid_le NL ML FL datL_m31 1 (by kernel_fact)
  | 18 =>
    l1_dataGrid_le NL ML FL datL_m40 0 (by kernel_fact)
  | 19 =>
    l1_dataGrid_le NL ML FL datL_m41 1 (by kernel_fact)
  | 20 =>
    l1_dataGrid_le NL ML FL datL_m50 0 (by kernel_fact)
  | 21 =>
    l1_dataGrid_le NL ML FL datL_m51 1 (by kernel_fact)
  | 22 =>
    l1_dataGrid_le NL ML FL datL_m60 0 (by kernel_fact)
  | 23 =>
    l1_dataGrid_le NL ML FL datL_Dp 0 (by kernel_fact)
  | 24 =>
    l1_dataGrid_le NL ML FL datL_nRp 3 (by kernel_fact)
  | 25 =>
    l1_dataGrid_le NL ML FL datL_nZp 0 (by kernel_fact)
  | 26 =>
    l1_dataGrid_le NL ML FL datL_DuP 0 (by kernel_fact)
  | 27 =>
    l1_dataGrid_le NL ML FL datL_DzP 3 (by kernel_fact)
  | 28 =>
    l1_dataGrid_le NL ML FL datL_DphP 1 (by kernel_fact)
  | 29 =>
    l1_dataGrid_le NL ML FL datL_nRuP 3 (by kernel_fact)
  | 30 =>
    l1_dataGrid_le NL ML FL datL_nRzP 0 (by kernel_fact)
  | 31 =>
    l1_dataGrid_le NL ML FL datL_nRphP 0 (by kernel_fact)
  | 32 =>
    l1_dataGrid_le NL ML FL datL_nZuP 0 (by kernel_fact)
  | 33 =>
    l1_dataGrid_le NL ML FL datL_nZzP 1 (by kernel_fact)
  | 34 =>
    l1_dataGrid_le NL ML FL datL_nZphP 3 (by kernel_fact)
  | 35 =>
    l1_dataGrid_le NL ML FL datL_PuP 0 (by kernel_fact)
  | 36 =>
    l1_dataGrid_le NL ML FL datL_PdP 0 (by kernel_fact)
  | 37 =>
    l1_dataGrid_le NL ML FL datL_DuuP 0 (by kernel_fact)
  | 38 =>
    l1_dataGrid_le NL ML FL datL_DuzP 3 (by kernel_fact)
  | 39 =>
    l1_dataGrid_le NL ML FL datL_DzzP 0 (by kernel_fact)
  | 40 =>
    l1_dataGrid_le NL ML FL datL_DuphP 1 (by kernel_fact)
  | 41 =>
    l1_dataGrid_le NL ML FL datL_DzphP 0 (by kernel_fact)
  | 42 =>
    l1_dataGrid_le NL ML FL datL_nRuuP 3 (by kernel_fact)
  | 43 =>
    l1_dataGrid_le NL ML FL datL_nRuzP 0 (by kernel_fact)
  | 44 =>
    l1_dataGrid_le NL ML FL datL_nRzzP 3 (by kernel_fact)
  | 45 =>
    l1_dataGrid_le NL ML FL datL_nRuphP 0 (by kernel_fact)
  | 46 =>
    l1_dataGrid_le NL ML FL datL_nRzphP 3 (by kernel_fact)
  | 47 =>
    l1_dataGrid_le NL ML FL datL_nZuuP 0 (by kernel_fact)
  | 48 =>
    l1_dataGrid_le NL ML FL datL_nZuzP 1 (by kernel_fact)
  | 49 =>
    l1_dataGrid_le NL ML FL datL_nZzzP 0 (by kernel_fact)
  | 50 =>
    l1_dataGrid_le NL ML FL datL_nZuphP 3 (by kernel_fact)
  | 51 =>
    l1_dataGrid_le NL ML FL datL_nZzphP 0 (by kernel_fact)
  | 52 =>
    l1_dataGrid_le NL ML FL datL_RD 0 (by kernel_fact)
  | 53 =>
    l1_dataGrid_le NL ML FL datL_RDu 0 (by kernel_fact)
  | 54 =>
    l1_dataGrid_le NL ML FL datL_RDz 3 (by kernel_fact)
  | 55 =>
    l1_dataGrid_le NL ML FL datL_RDph 1 (by kernel_fact)
  | 56 =>
    l1_dataGrid_le NL ML FL datL_q 2 (by kernel_fact)
  | 57 =>
    l1_dataGrid_le NL ML FL datL_qR 0 (by kernel_fact)
  | 58 =>
    l1_dataGrid_le NL ML FL datL_qz 3 (by kernel_fact)
  | 59 =>
    l1_dataGrid_le NL ML FL datL_qph 3 (by kernel_fact)
  | 60 =>
    l1_dataGrid_le NL ML FL datL_P2 0 (by kernel_fact)
  | 61 =>
    l1_dataGrid_le NL ML FL datL_E 2 (by kernel_fact)
  | 62 =>
    l1_dataGrid_le NL ML FL datL_V0 0 (by kernel_fact)
  | 63 =>
    l1_dataGrid_le NL ML FL datL_V0 0 (by kernel_fact)
  | 64 =>
    l1_dataGrid_le NL ML FL datL_W 0 (by kernel_fact)
  | 65 =>
    l1_dataGrid_le NL ML FL datL_W2 0 (by kernel_fact)
  | 66 =>
    l1_dataGrid_le NL ML FL datL_W3 0 (by kernel_fact)
  | 67 =>
    l1_dataGrid_le NL ML FL datL_R2 0 (by kernel_fact)
  | 68 =>
    l1_dataGrid_le NL ML FL datL_R3 0 (by kernel_fact)
  | 69 =>
    l1_dataGrid_le NL ML FL datL_A1 0 (by kernel_fact)
  | 70 =>
    l1_dataGrid_le NL ML FL datL_A2 3 (by kernel_fact)
  | 71 =>
    l1_dataGrid_le NL ML FL datL_K1 0 (by kernel_fact)
  | 72 =>
    l1_dataGrid_le NL ML FL datL_K2 3 (by kernel_fact)
  | 73 =>
    l1_dataGrid_le NL ML FL datL_K3 2 (by kernel_fact)
  | 74 =>
    l1_dataGrid_le NL ML FL datL_KD 0 (by kernel_fact)
  | 75 =>
    l1_dataGrid_le NL ML FL datL_KR 3 (by kernel_fact)
  | 76 =>
    l1_dataGrid_le NL ML FL datL_KZ 2 (by kernel_fact)
  | 77 =>
    l1_dataGrid_le NL ML FL datL_Dt 0 (by kernel_fact)
  | 78 =>
    l1_dataGrid_le NL ML FL datL_nRt 3 (by kernel_fact)
  | 79 =>
    l1_dataGrid_le NL ML FL datL_nZt 0 (by kernel_fact)
  | 80 =>
    l1_dataGrid_le NL ML FL datL_qRu 0 (by kernel_fact)
  | 81 =>
    l1_dataGrid_le NL ML FL datL_qRz 3 (by kernel_fact)
  | 82 =>
    l1_dataGrid_le NL ML FL datL_qzz 0 (by kernel_fact)
  | 83 =>
    l1_dataGrid_le NL ML FL datL_qzu 3 (by kernel_fact)
  | 84 =>
    l1_dataGrid_le NL ML FL datL_qphu 1 (by kernel_fact)
  | 85 =>
    l1_dataGrid_le NL ML FL datL_qphz 0 (by kernel_fact)
  | 86 =>
    l1_dataGrid_le NL ML FL datL_qu 0 (by kernel_fact)
  | 87 =>
    l1_dataGrid_le NL ML FL datL_qzd 3 (by kernel_fact)
  | 88 =>
    l1_dataGrid_le NL ML FL datL_Eu 2 (by kernel_fact)
  | 89 =>
    l1_dataGrid_le NL ML FL datL_Ez 3 (by kernel_fact)
  | 90 =>
    l1_dataGrid_le NL ML FL datL_V3 0 (by kernel_fact)
  | 91 =>
    l1_dataGrid_le NL ML FL datL_Wu 0 (by kernel_fact)
  | 92 =>
    l1_dataGrid_le NL ML FL datL_Wz 3 (by kernel_fact)
  | 93 =>
    l1_dataGrid_le NL ML FL datL_W3u 0 (by kernel_fact)
  | 94 =>
    l1_dataGrid_le NL ML FL datL_W3z 3 (by kernel_fact)
  | 95 =>
    l1_dataGrid_le NL ML FL datL_KDu 0 (by kernel_fact)
  | 96 =>
    l1_dataGrid_le NL ML FL datL_KDz 3 (by kernel_fact)
  | 97 =>
    l1_dataGrid_le NL ML FL datL_KRu 3 (by kernel_fact)
  | 98 =>
    l1_dataGrid_le NL ML FL datL_KRz 0 (by kernel_fact)
  | 99 =>
    l1_dataGrid_le NL ML FL datL_KZu 2 (by kernel_fact)
  | 100 =>
    l1_dataGrid_le NL ML FL datL_KZz 3 (by kernel_fact)
  | 101 =>
    l1_dataGrid_le NL ML FL datL_Dtu 0 (by kernel_fact)
  | 102 =>
    l1_dataGrid_le NL ML FL datL_Dtz 3 (by kernel_fact)
  | 103 =>
    l1_dataGrid_le NL ML FL datL_nRtu 3 (by kernel_fact)
  | 104 =>
    l1_dataGrid_le NL ML FL datL_nRtz 0 (by kernel_fact)
  | 105 =>
    l1_dataGrid_le NL ML FL datL_nZtu 0 (by kernel_fact)
  | 106 =>
    l1_dataGrid_le NL ML FL datL_nZtz 1 (by kernel_fact)
  | 107 =>
    l1_dataGrid_le NL ML FL datL_Ptor 0 (by kernel_fact)
  | 108 =>
    l1_dataGrid_le NL ML FL datL_W0 0 (by kernel_fact)
  | 109 =>
    l1_dataGrid_le NL ML FL datL_Dt3 0 (by kernel_fact)
  | 110 =>
    l1_dataGrid_le NL ML FL datL_W02 0 (by kernel_fact)
  | 111 =>
    l1_dataGrid_le NL ML FL datL_F 0 (by kernel_fact)
  | 112 =>
    l1_dataGrid_le NL ML FL datL_qi 0 (by kernel_fact)
  | 113 =>
    l1_dataGrid_le NL ML FL datL_Y 0 (by kernel_fact)
  | n + 114 =>
    (l1_gridPolyNM_le_const NL ML (C := 0) fun i j _ _ => by rw [gL_out n]; simp).trans
      (by simp)

/-- Kronecker images. -/
theorem kronL : ∀ b W i, kron b W (PL i) = KvL b W i
  | b, W, 0 => kron_Tpoly SL NL ML b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_cPoly b W
  | b, W, 3 => kron_sPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NL ML _

/-- The centre of `t` is `1`. -/
theorem xL_t : xL 0 = 1 := ctr_Tpoly SL NL ML

/-- The centre of `V` is `1`. -/
theorem xL_V : xL 1 = 1 := ctr_Vpoly SL NL ML

/-- The norm bounds of the centres (list). -/
def BLl : List ℚ := 
  [(1 : ℚ), (1 : ℚ), (74315 / 2 ^ 16 : ℚ), (74315 / 2 ^ 16 : ℚ), (1929 / 10 ^ 4 : ℚ),
    (811 / 5000 : ℚ), (817 / 5000 : ℚ), (101 / 625 : ℚ), (441 / 20000 : ℚ), (1653 / 10 ^ 5 : ℚ),
    (3193 / 10 ^ 5 : ℚ), (771 / 250000 : ℚ), (2177 / 10 ^ 6 : ℚ), (2453 / 10 ^ 6 : ℚ),
    (5263 / 10 ^ 6 : ℚ), (603 / 2500000 : ℚ), (2253 / 10 ^ 7 : ℚ), (431 / 1250000 : ℚ),
    (8633 / 10 ^ 7 : ℚ), (2583 / 50000000 : ℚ), (1413 / 10 ^ 7 : ℚ), (3877 / 500000000 : ℚ),
    (23 / 10 ^ 6 : ℚ), (51 / 40 : ℚ), (1001 / 10 ^ 4 : ℚ), (501 / 5000 : ℚ), (2237 / 10 ^ 3 : ℚ),
    (128 / 625 : ℚ), (1169 / 50000 : ℚ), (9391 / 10 ^ 4 : ℚ), (3687 / 5000 : ℚ), (81 / 400 : ℚ),
    (8631 / 10 ^ 4 : ℚ), (1623 / 2000 : ℚ), (2013 / 10 ^ 4 : ℚ), (903 / 500 : ℚ),
    (6557 / 10 ^ 3 : ℚ), (1783 / 500 : ℚ), (29 / 25 : ℚ), (417 / 250 : ℚ), (4161 / 10 ^ 4 : ℚ),
    (2107 / 5000 : ℚ), (491 / 125 : ℚ), (1183 / 2500 : ℚ), (1639 / 10 ^ 3 : ℚ), (473 / 250 : ℚ),
    (59 / 40 : ℚ), (2601 / 10 ^ 3 : ℚ), (1639 / 10 ^ 3 : ℚ), (213 / 10 ^ 2 : ℚ),
    (1719 / 10 ^ 3 : ℚ), (1633 / 10 ^ 3 : ℚ), (701 / 500 : ℚ), (2371 / 10 ^ 3 : ℚ),
    (2007 / 10 ^ 4 : ℚ), (2269 / 10 ^ 5 : ℚ), (1877 / 10 ^ 3 : ℚ), (4937 / 500 : ℚ),
    (3431 / 10 ^ 4 : ℚ), (4833 / 10 ^ 5 : ℚ), (399 / 125 : ℚ), (3589 / 10 ^ 5 : ℚ),
    (1019 / 10 ^ 3 : ℚ), (1019 / 10 ^ 3 : ℚ), (459 / 250 : ℚ), (3297 / 10 ^ 3 : ℚ),
    (2911 / 500 : ℚ), (253 / 200 : ℚ), (281 / 200 : ℚ), (273 / 25 : ℚ), (1813 / 5000 : ℚ),
    (601 / 2000 : ℚ), (1113 / 2500 : ℚ), (2721 / 500 : ℚ), (3509 / 10 ^ 4 : ℚ),
    (5419 / 10 ^ 4 : ℚ), (7227 / 10 ^ 3 : ℚ), (51 / 40 : ℚ), (503 / 5000 : ℚ), (209 / 2000 : ℚ),
    (949 / 20 : ℚ), (867 / 200 : ℚ), (4541 / 10 ^ 3 : ℚ), (867 / 200 : ℚ), (9803 / 10 ^ 4 : ℚ),
    (4423 / 5000 : ℚ), (4937 / 500 : ℚ), (3431 / 10 ^ 4 : ℚ), (1211 / 2500 : ℚ),
    (447 / 10 ^ 3 : ℚ), (132 / 125 : ℚ), (1769 / 250 : ℚ), (473 / 1250 : ℚ), (3313 / 50 : ℚ),
    (3131 / 10 ^ 3 : ℚ), (788 / 125 : ℚ), (677 / 200 : ℚ), (219 / 20 : ℚ), (8657 / 10 ^ 3 : ℚ),
    (1657 / 20 : ℚ), (2449 / 500 : ℚ), (447 / 200 : ℚ), (1011 / 5000 : ℚ), (189 / 200 : ℚ),
    (1861 / 2500 : ℚ), (2171 / 2500 : ℚ), (8167 / 10 ^ 4 : ℚ), (2759 / 10 ^ 6 : ℚ),
    (129 / 10 ^ 4 : ℚ), (233 / 125 : ℚ), (1561 / 10 ^ 7 : ℚ), (1241 / 10 ^ 7 : ℚ), (28650 : ℚ),
    (3711 / 10 ^ 2 : ℚ)]

/-- The norm bounds of the centres. -/
def BL (i : ℕ) : ℚ := BLl.getD i 0

/-- The radii of the balls (list). -/
def ELl : List ℚ := 
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (101 / 10 ^ 14 : ℚ), (101 / 10 ^ 14 : ℚ),
    (103 / 10 ^ 14 : ℚ), (103 / 10 ^ 14 : ℚ), (33 / 10 ^ 14 : ℚ), (361 / 10 ^ 15 : ℚ),
    (393 / 10 ^ 15 : ℚ), (389 / 5000000000000000 : ℚ), (77 / 10 ^ 15 : ℚ), (883 / 10 ^ 16 : ℚ),
    (111 / 10 ^ 15 : ℚ), (1 / 62500000000000 : ℚ), (23 / 1250000000000000 : ℚ),
    (21 / 10 ^ 15 : ℚ), (57 / 2000000000000000 : ℚ), (561 / 10 ^ 17 : ℚ),
    (381 / 50000000000000000 : ℚ), (109 / 50000000000000000 : ℚ), (69 / 25000000000000000 : ℚ),
    (21 / 6250000000000 : ℚ), (233 / 10 ^ 14 : ℚ), (127 / 50000000000000 : ℚ),
    (261 / 50000000000000 : ℚ), (293 / 10 ^ 14 : ℚ), (19 / 10 ^ 13 : ℚ),
    (329 / 50000000000000 : ℚ), (3 / 10 ^ 12 : ℚ), (233 / 50000000000000 : ℚ),
    (523 / 10 ^ 14 : ℚ), (7 / 1562500000000 : ℚ), (507 / 10 ^ 14 : ℚ), (717 / 10 ^ 14 : ℚ),
    (349 / 10 ^ 13 : ℚ), (11 / 2000000000000 : ℚ), (743 / 10 ^ 15 : ℚ),
    (173 / 50000000000000 : ℚ), (319 / 50000000000000 : ℚ), (117 / 20000000000000 : ℚ),
    (191 / 10 ^ 13 : ℚ), (659 / 10 ^ 14 : ℚ), (73 / 12500000000000 : ℚ), (33 / 2500000000000 : ℚ),
    (599 / 10 ^ 14 : ℚ), (187 / 25000000000000 : ℚ), (73 / 12500000000000 : ℚ),
    (413 / 10 ^ 14 : ℚ), (21 / 2000000000000 : ℚ), (7 / 781250000000 : ℚ), (531 / 10 ^ 14 : ℚ),
    (17 / 2000000000000 : ℚ), (371 / 10 ^ 14 : ℚ), (23 / 10 ^ 13 : ℚ), (159 / 10 ^ 13 : ℚ),
    (833 / 10 ^ 13 : ℚ), (217 / 10 ^ 13 : ℚ), (107 / 10 ^ 13 : ℚ), (131 / 5000000000000 : ℚ),
    (101 / 10 ^ 12 : ℚ), (0 : ℚ), (73 / 1250000000000 : ℚ), (57 / 500000000000 : ℚ),
    (427 / 10 ^ 12 : ℚ), (61 / 50000000000 : ℚ), (121 / 50000000000000 : ℚ), (417 / 10 ^ 14 : ℚ),
    (11 / 10 ^ 11 : ℚ), (263 / 10 ^ 13 : ℚ), (933 / 10 ^ 13 : ℚ), (201 / 5000000000000 : ℚ),
    (59 / 125000000000 : ℚ), (119 / 10 ^ 12 : ℚ), (587 / 10 ^ 13 : ℚ), (687 / 10 ^ 12 : ℚ),
    (139 / 25000000000000 : ℚ), (431 / 10 ^ 14 : ℚ), (139 / 5000000000000 : ℚ),
    (203 / 500000000000 : ℚ), (11 / 10 ^ 11 : ℚ), (423 / 5000000000000 : ℚ),
    (27 / 250000000000 : ℚ), (477 / 5000000000000 : ℚ), (639 / 10 ^ 13 : ℚ), (833 / 10 ^ 13 : ℚ),
    (217 / 10 ^ 13 : ℚ), (33 / 25000000000 : ℚ), (157 / 2000000000000 : ℚ),
    (23 / 125000000000 : ℚ), (9 / 5000000000 : ℚ), (171 / 10 ^ 12 : ℚ), (29 / 10 ^ 9 : ℚ),
    (311 / 10 ^ 11 : ℚ), (29 / 20000000000 : ℚ), (57 / 10 ^ 11 : ℚ), (701 / 10 ^ 12 : ℚ),
    (307 / 10 ^ 12 : ℚ), (831 / 10 ^ 11 : ℚ), (953 / 10 ^ 12 : ℚ), (361 / 5000000000000 : ℚ),
    (41 / 2000000000000 : ℚ), (397 / 5000000000000 : ℚ), (311 / 10 ^ 13 : ℚ), (799 / 10 ^ 12 : ℚ),
    (77 / 10 ^ 12 : ℚ), (37 / 625000000000 : ℚ), (349 / 500000000000000 : ℚ),
    (17 / 625000000000 : ℚ), (39 / 2000000000000000 : ℚ), (21 / 500000000000000 : ℚ), (0 : ℚ),
    (441 / 50000000 : ℚ)]

/-- The radii of the balls. -/
def EL (i : ℕ) : ℚ := ELl.getD i 0

end PlasmaLean.Design.RationalStellaratorGC
