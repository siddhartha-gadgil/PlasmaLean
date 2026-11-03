/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCKronW
public import PlasmaLean.Design.DommaschkKamCAdmData1
public import PlasmaLean.Design.DommaschkKamCAdmData2
public import PlasmaLean.Design.DommaschkKamCAdmData3
public import PlasmaLean.Design.DommaschkKamCAdmData4
public import PlasmaLean.Design.DommaschkKamCAdmData5
public import PlasmaLean.Design.DommaschkKamCAdmData6

/-!
# The ball environment of the torus-C admissibility chain

The variables of the low-resolution ball chain of Dommaschk torus C (N-33 plan item 8): layout
`N = 24`, `M = 28`, scale `2^{−64}`, oracle angle `ψₒ = 2φ`, strip weights `68553^s 2^{16(K − s)}`
(`e^r ≤ 68553/2^16`, `Design/DommaschkKamCKronW`); the grids `gA i` of the centres, their
polynomials `PlA i`, weights `WtA i`, degree boxes `BxA i`, `ℓ¹` bounds `LA i`, Kronecker images
`KvA b W i`, the honest centres `xA i`, the norm bounds `BA i` of the centres and the radii
`EA i` of the balls (supplied by the oracle `scripts/dommaschk_kam/emit_adm.py`, checked in
`Design/DommaschkKamCAdmCheck*`), and the monomial table `monoA a b` (the variable of `R^a z^b`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos ψₒ`, `sin ψₒ` (`xA_t`, `xA_V`, `xA_C`, `xA_S`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex

/-- Layout: poloidal half width. -/
def NA : ℕ := 24
/-- Layout: toroidal half width. -/
def MA : ℕ := 28
/-- Layout: scale exponent. -/
def SA : ℕ := 64

/-- Grid of the centre `U`. -/
def gA_U : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 60 NA datA_U)

/-- Grid of the centre `Z`. -/
def gA_Z : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_Z)

/-- Grid of the centre `A`. -/
def gA_A : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NA) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MA)) * gA_U i j

/-- Grid of the centre `B`. -/
def gA_B : ℕ → ℕ → ℤ :=
  fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - NA) + ((0 : ℕ) : ℤ) * ((j : ℤ) - MA)) * gA_Z i j

/-- Grid of the centre `Pu`. -/
def gA_Pu : ℕ → ℕ → ℤ :=
  fun i j => (((0 : ℕ) : ℤ) * ((i : ℤ) - NA) + ((1 : ℕ) : ℤ) * ((j : ℤ) - MA)) * gA_U i j

/-- Grid of the centre `Pz`. -/
def gA_Pz : ℕ → ℕ → ℤ :=
  fun i j => (((0 : ℕ) : ℤ) * ((i : ℤ) - NA) + ((1 : ℕ) : ℤ) * ((j : ℤ) - MA)) * gA_Z i j

/-- Grid of the centre `R`. -/
def gA_R : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R)

/-- Grid of the centre `R2`. -/
def gA_R2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R2)

/-- Grid of the centre `R3`. -/
def gA_R3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R3)

/-- Grid of the centre `R4`. -/
def gA_R4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R4)

/-- Grid of the centre `R5`. -/
def gA_R5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R5)

/-- Grid of the centre `R6`. -/
def gA_R6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R6)

/-- Grid of the centre `R7`. -/
def gA_R7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R7)

/-- Grid of the centre `R8`. -/
def gA_R8 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R8)

/-- Grid of the centre `R9`. -/
def gA_R9 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 65 NA datA_R9)

/-- Grid of the centre `R10`. -/
def gA_R10 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R10)

/-- Grid of the centre `R11`. -/
def gA_R11 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R11)

/-- Grid of the centre `R12`. -/
def gA_R12 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R12)

/-- Grid of the centre `R13`. -/
def gA_R13 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R13)

/-- Grid of the centre `R14`. -/
def gA_R14 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R14)

/-- Grid of the centre `R15`. -/
def gA_R15 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R15)

/-- Grid of the centre `R16`. -/
def gA_R16 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R16)

/-- Grid of the centre `R17`. -/
def gA_R17 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R17)

/-- Grid of the centre `R18`. -/
def gA_R18 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_R18)

/-- Grid of the centre `z2`. -/
def gA_z2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 57 NA datA_z2)

/-- Grid of the centre `z3`. -/
def gA_z3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_z3)

/-- Grid of the centre `z4`. -/
def gA_z4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 49 NA datA_z4)

/-- Grid of the centre `z5`. -/
def gA_z5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 45 NA datA_z5)

/-- Grid of the centre `m1_1`. -/
def gA_m1_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m1_1)

/-- Grid of the centre `m1_2`. -/
def gA_m1_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m1_2)

/-- Grid of the centre `m1_3`. -/
def gA_m1_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m1_3)

/-- Grid of the centre `m1_4`. -/
def gA_m1_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 49 NA datA_m1_4)

/-- Grid of the centre `m1_5`. -/
def gA_m1_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 45 NA datA_m1_5)

/-- Grid of the centre `m2_1`. -/
def gA_m2_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m2_1)

/-- Grid of the centre `m2_2`. -/
def gA_m2_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m2_2)

/-- Grid of the centre `m2_3`. -/
def gA_m2_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m2_3)

/-- Grid of the centre `m2_4`. -/
def gA_m2_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 48 NA datA_m2_4)

/-- Grid of the centre `m2_5`. -/
def gA_m2_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 45 NA datA_m2_5)

/-- Grid of the centre `m3_1`. -/
def gA_m3_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m3_1)

/-- Grid of the centre `m3_2`. -/
def gA_m3_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m3_2)

/-- Grid of the centre `m3_3`. -/
def gA_m3_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m3_3)

/-- Grid of the centre `m3_4`. -/
def gA_m3_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 48 NA datA_m3_4)

/-- Grid of the centre `m3_5`. -/
def gA_m3_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 44 NA datA_m3_5)

/-- Grid of the centre `m4_1`. -/
def gA_m4_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m4_1)

/-- Grid of the centre `m4_2`. -/
def gA_m4_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m4_2)

/-- Grid of the centre `m4_3`. -/
def gA_m4_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m4_3)

/-- Grid of the centre `m4_4`. -/
def gA_m4_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 48 NA datA_m4_4)

/-- Grid of the centre `m5_1`. -/
def gA_m5_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m5_1)

/-- Grid of the centre `m5_2`. -/
def gA_m5_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m5_2)

/-- Grid of the centre `m5_3`. -/
def gA_m5_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m5_3)

/-- Grid of the centre `m6_1`. -/
def gA_m6_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m6_1)

/-- Grid of the centre `m6_2`. -/
def gA_m6_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m6_2)

/-- Grid of the centre `m7_1`. -/
def gA_m7_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m7_1)

/-- Grid of the centre `m7_2`. -/
def gA_m7_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m7_2)

/-- Grid of the centre `m7_3`. -/
def gA_m7_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 52 NA datA_m7_3)

/-- Grid of the centre `m8_1`. -/
def gA_m8_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 60 NA datA_m8_1)

/-- Grid of the centre `m8_2`. -/
def gA_m8_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m8_2)

/-- Grid of the centre `m8_3`. -/
def gA_m8_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m8_3)

/-- Grid of the centre `m9_1`. -/
def gA_m9_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m9_1)

/-- Grid of the centre `m9_2`. -/
def gA_m9_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 56 NA datA_m9_2)

/-- Grid of the centre `m9_3`. -/
def gA_m9_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m9_3)

/-- Grid of the centre `m9_4`. -/
def gA_m9_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 48 NA datA_m9_4)

/-- Grid of the centre `m9_5`. -/
def gA_m9_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 44 NA datA_m9_5)

/-- Grid of the centre `m10_1`. -/
def gA_m10_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m10_1)

/-- Grid of the centre `m10_2`. -/
def gA_m10_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m10_2)

/-- Grid of the centre `m10_3`. -/
def gA_m10_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m10_3)

/-- Grid of the centre `m10_4`. -/
def gA_m10_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 47 NA datA_m10_4)

/-- Grid of the centre `m10_5`. -/
def gA_m10_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 44 NA datA_m10_5)

/-- Grid of the centre `m11_1`. -/
def gA_m11_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m11_1)

/-- Grid of the centre `m11_2`. -/
def gA_m11_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m11_2)

/-- Grid of the centre `m11_3`. -/
def gA_m11_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m11_3)

/-- Grid of the centre `m11_4`. -/
def gA_m11_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 47 NA datA_m11_4)

/-- Grid of the centre `m11_5`. -/
def gA_m11_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 43 NA datA_m11_5)

/-- Grid of the centre `m12_1`. -/
def gA_m12_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m12_1)

/-- Grid of the centre `m12_2`. -/
def gA_m12_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m12_2)

/-- Grid of the centre `m12_3`. -/
def gA_m12_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m12_3)

/-- Grid of the centre `m12_4`. -/
def gA_m12_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 47 NA datA_m12_4)

/-- Grid of the centre `m12_5`. -/
def gA_m12_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 43 NA datA_m12_5)

/-- Grid of the centre `m13_1`. -/
def gA_m13_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m13_1)

/-- Grid of the centre `m13_2`. -/
def gA_m13_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m13_2)

/-- Grid of the centre `m13_3`. -/
def gA_m13_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m13_3)

/-- Grid of the centre `m13_4`. -/
def gA_m13_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 47 NA datA_m13_4)

/-- Grid of the centre `m13_5`. -/
def gA_m13_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 43 NA datA_m13_5)

/-- Grid of the centre `m14_1`. -/
def gA_m14_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m14_1)

/-- Grid of the centre `m14_2`. -/
def gA_m14_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m14_2)

/-- Grid of the centre `m14_3`. -/
def gA_m14_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m14_3)

/-- Grid of the centre `m14_4`. -/
def gA_m14_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 47 NA datA_m14_4)

/-- Grid of the centre `m15_1`. -/
def gA_m15_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m15_1)

/-- Grid of the centre `m15_2`. -/
def gA_m15_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m15_2)

/-- Grid of the centre `m15_3`. -/
def gA_m15_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 51 NA datA_m15_3)

/-- Grid of the centre `m16_1`. -/
def gA_m16_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m16_1)

/-- Grid of the centre `m16_2`. -/
def gA_m16_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 55 NA datA_m16_2)

/-- Grid of the centre `m17_1`. -/
def gA_m17_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_m17_1)

/-- Grid of the centre `D_1`. -/
def gA_D_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 64 NA datA_D_1)

/-- Grid of the centre `D_2`. -/
def gA_D_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_D_2)

/-- Grid of the centre `D_3`. -/
def gA_D_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_3)

/-- Grid of the centre `D_4`. -/
def gA_D_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_D_4)

/-- Grid of the centre `D_5`. -/
def gA_D_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_5)

/-- Grid of the centre `D_6`. -/
def gA_D_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_6)

/-- Grid of the centre `D_7`. -/
def gA_D_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_7)

/-- Grid of the centre `D_8`. -/
def gA_D_8 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_8)

/-- Grid of the centre `D_9`. -/
def gA_D_9 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D_9)

/-- Grid of the centre `D`. -/
def gA_D : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_D)

/-- Grid of the centre `Du_1`. -/
def gA_Du_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 67 NA datA_Du_1)

/-- Grid of the centre `Du_2`. -/
def gA_Du_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 69 NA datA_Du_2)

/-- Grid of the centre `Du_3`. -/
def gA_Du_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du_3)

/-- Grid of the centre `Du_4`. -/
def gA_Du_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du_4)

/-- Grid of the centre `Du_5`. -/
def gA_Du_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 69 NA datA_Du_5)

/-- Grid of the centre `Du_6`. -/
def gA_Du_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du_6)

/-- Grid of the centre `Du_7`. -/
def gA_Du_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du_7)

/-- Grid of the centre `Du_8`. -/
def gA_Du_8 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du_8)

/-- Grid of the centre `Du`. -/
def gA_Du : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_Du)

/-- Grid of the centre `Dz_1`. -/
def gA_Dz_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_Dz_1)

/-- Grid of the centre `Dz_2`. -/
def gA_Dz_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 69 NA datA_Dz_2)

/-- Grid of the centre `Dz_3`. -/
def gA_Dz_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 66 NA datA_Dz_3)

/-- Grid of the centre `Dz_4`. -/
def gA_Dz_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 66 NA datA_Dz_4)

/-- Grid of the centre `Dz_5`. -/
def gA_Dz_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_Dz_5)

/-- Grid of the centre `Dz_6`. -/
def gA_Dz_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_Dz_6)

/-- Grid of the centre `Dz_7`. -/
def gA_Dz_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 66 NA datA_Dz_7)

/-- Grid of the centre `Dz`. -/
def gA_Dz : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 62 NA datA_Dz)

/-- Grid of the centre `nR_1`. -/
def gA_nR_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nR_1)

/-- Grid of the centre `nR_2`. -/
def gA_nR_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 65 NA datA_nR_2)

/-- Grid of the centre `nR_3`. -/
def gA_nR_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 65 NA datA_nR_3)

/-- Grid of the centre `nR_4`. -/
def gA_nR_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nR_4)

/-- Grid of the centre `nR_5`. -/
def gA_nR_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 65 NA datA_nR_5)

/-- Grid of the centre `nR_6`. -/
def gA_nR_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 66 NA datA_nR_6)

/-- Grid of the centre `nR_7`. -/
def gA_nR_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nR_7)

/-- Grid of the centre `nR_8`. -/
def gA_nR_8 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nR_8)

/-- Grid of the centre `nR_9`. -/
def gA_nR_9 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nR_9)

/-- Grid of the centre `nR`. -/
def gA_nR : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 61 NA datA_nR)

/-- Grid of the centre `nRu_1`. -/
def gA_nRu_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 64 NA datA_nRu_1)

/-- Grid of the centre `nRu_2`. -/
def gA_nRu_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nRu_2)

/-- Grid of the centre `nRu_3`. -/
def gA_nRu_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nRu_3)

/-- Grid of the centre `nRu_4`. -/
def gA_nRu_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nRu_4)

/-- Grid of the centre `nRu_5`. -/
def gA_nRu_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nRu_5)

/-- Grid of the centre `nRu_6`. -/
def gA_nRu_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 69 NA datA_nRu_6)

/-- Grid of the centre `nRu_7`. -/
def gA_nRu_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nRu_7)

/-- Grid of the centre `nRu_8`. -/
def gA_nRu_8 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nRu_8)

/-- Grid of the centre `nRu_9`. -/
def gA_nRu_9 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nRu_9)

/-- Grid of the centre `nRu`. -/
def gA_nRu : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 63 NA datA_nRu)

/-- Grid of the centre `nRz_1`. -/
def gA_nRz_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_nRz_1)

/-- Grid of the centre `nRz_2`. -/
def gA_nRz_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 67 NA datA_nRz_2)

/-- Grid of the centre `nRz_3`. -/
def gA_nRz_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nRz_3)

/-- Grid of the centre `nRz_4`. -/
def gA_nRz_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nRz_4)

/-- Grid of the centre `nRz_5`. -/
def gA_nRz_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_nRz_5)

/-- Grid of the centre `nRz_6`. -/
def gA_nRz_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_nRz_6)

/-- Grid of the centre `nRz_7`. -/
def gA_nRz_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nRz_7)

/-- Grid of the centre `nRz`. -/
def gA_nRz : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 63 NA datA_nRz)

/-- Grid of the centre `nZ_1`. -/
def gA_nZ_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_nZ_1)

/-- Grid of the centre `nZ_2`. -/
def gA_nZ_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nZ_2)

/-- Grid of the centre `nZ_3`. -/
def gA_nZ_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_nZ_3)

/-- Grid of the centre `nZ_4`. -/
def gA_nZ_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 64 NA datA_nZ_4)

/-- Grid of the centre `nZ_5`. -/
def gA_nZ_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nZ_5)

/-- Grid of the centre `nZ_6`. -/
def gA_nZ_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 65 NA datA_nZ_6)

/-- Grid of the centre `nZ_7`. -/
def gA_nZ_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 63 NA datA_nZ_7)

/-- Grid of the centre `nZ`. -/
def gA_nZ : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 61 NA datA_nZ)

/-- Grid of the centre `nZu_1`. -/
def gA_nZu_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 66 NA datA_nZu_1)

/-- Grid of the centre `nZu_2`. -/
def gA_nZu_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_nZu_2)

/-- Grid of the centre `nZu_3`. -/
def gA_nZu_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 67 NA datA_nZu_3)

/-- Grid of the centre `nZu_4`. -/
def gA_nZu_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 68 NA datA_nZu_4)

/-- Grid of the centre `nZu_5`. -/
def gA_nZu_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 70 NA datA_nZu_5)

/-- Grid of the centre `nZu_6`. -/
def gA_nZu_6 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 69 NA datA_nZu_6)

/-- Grid of the centre `nZu_7`. -/
def gA_nZu_7 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 67 NA datA_nZu_7)

/-- Grid of the centre `nZu`. -/
def gA_nZu : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 63 NA datA_nZu)

/-- Grid of the centre `nZz_1`. -/
def gA_nZz_1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nZz_1)

/-- Grid of the centre `nZz_2`. -/
def gA_nZz_2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 68 NA datA_nZz_2)

/-- Grid of the centre `nZz_3`. -/
def gA_nZz_3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nZz_3)

/-- Grid of the centre `nZz_4`. -/
def gA_nZz_4 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nZz_4)

/-- Grid of the centre `nZz_5`. -/
def gA_nZz_5 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 67 NA datA_nZz_5)

/-- Grid of the centre `nZz`. -/
def gA_nZz : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 63 NA datA_nZz)

/-- Grid of the centre `V0R`. -/
def gA_V0R : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 59 NA datA_V0R)

/-- Grid of the centre `V0Z`. -/
def gA_V0Z : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 59 NA datA_V0Z)

/-- Grid of the centre `W0`. -/
def gA_W0 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 55 NA datA_W0)

/-- Grid of the centre `AR1`. -/
def gA_AR1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 61 NA datA_AR1)

/-- Grid of the centre `AZ1`. -/
def gA_AZ1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 61 NA datA_AZ1)

/-- Grid of the centre `DD`. -/
def gA_DD : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 64 NA datA_DD)

/-- Grid of the centre `G1`. -/
def gA_G1 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 3) (halfGridR 57 NA datA_G1)

/-- Grid of the centre `G2`. -/
def gA_G2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 61 NA datA_G2)

/-- Grid of the centre `G3`. -/
def gA_G3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 57 NA datA_G3)

/-- Grid of the centre `YR`. -/
def gA_YR : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 1) (halfGridR 55 NA datA_YR)

/-- Grid of the centre `YZ`. -/
def gA_YZ : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 55 NA datA_YZ)

/-- Grid of the centre `P`. -/
def gA_P : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 49 NA datA_P)

/-- Grid of the centre `qD`. -/
def gA_qD : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 66 NA datA_qD)

/-- Grid of the centre `qW`. -/
def gA_qW : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 76 NA datA_qW)

/-- Grid of the centre `qR`. -/
def gA_qR : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 66 NA datA_qR)

/-- Grid of the centre `PR`. -/
def gA_PR : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 49 NA datA_PR)

/-- Grid of the centre `qD2`. -/
def gA_qD2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 67 NA datA_qD2)

/-- Grid of the centre `qD3`. -/
def gA_qD3 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 69 NA datA_qD3)

/-- Grid of the centre `qW2`. -/
def gA_qW2 : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 87 NA datA_qW2)

/-- Grid of the centre `qDW`. -/
def gA_qDW : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 0) (halfGridR 90 NA datA_qDW)

/-- Grid of the centre `Y`. -/
def gA_Y : ℕ → ℕ → ℤ :=
  symGrid NA MA ((-1) ^ 2) (halfGridR 72 NA datA_Y)

/-- The grids of the variables (list; the constants `0, …, 3` have no grid). -/
def gAl : List (ℕ → ℕ → ℤ) :=
  [fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, gA_U, gA_Z, gA_A, gA_B, gA_Pu, gA_Pz,
    gA_R, gA_R2, gA_R3, gA_R4, gA_R5, gA_R6, gA_R7, gA_R8, gA_R9, gA_R10, gA_R11, gA_R12, gA_R13,
    gA_R14, gA_R15, gA_R16, gA_R17, gA_R18, gA_z2, gA_z3, gA_z4, gA_z5, gA_m1_1, gA_m1_2, gA_m1_3,
    gA_m1_4, gA_m1_5, gA_m2_1, gA_m2_2, gA_m2_3, gA_m2_4, gA_m2_5, gA_m3_1, gA_m3_2, gA_m3_3,
    gA_m3_4, gA_m3_5, gA_m4_1, gA_m4_2, gA_m4_3, gA_m4_4, gA_m5_1, gA_m5_2, gA_m5_3, gA_m6_1,
    gA_m6_2, gA_m7_1, gA_m7_2, gA_m7_3, gA_m8_1, gA_m8_2, gA_m8_3, gA_m9_1, gA_m9_2, gA_m9_3,
    gA_m9_4, gA_m9_5, gA_m10_1, gA_m10_2, gA_m10_3, gA_m10_4, gA_m10_5, gA_m11_1, gA_m11_2,
    gA_m11_3, gA_m11_4, gA_m11_5, gA_m12_1, gA_m12_2, gA_m12_3, gA_m12_4, gA_m12_5, gA_m13_1,
    gA_m13_2, gA_m13_3, gA_m13_4, gA_m13_5, gA_m14_1, gA_m14_2, gA_m14_3, gA_m14_4, gA_m15_1,
    gA_m15_2, gA_m15_3, gA_m16_1, gA_m16_2, gA_m17_1, gA_D_1, gA_D_2, gA_D_3, gA_D_4, gA_D_5,
    gA_D_6, gA_D_7, gA_D_8, gA_D_9, gA_D, gA_Du_1, gA_Du_2, gA_Du_3, gA_Du_4, gA_Du_5, gA_Du_6,
    gA_Du_7, gA_Du_8, gA_Du, gA_Dz_1, gA_Dz_2, gA_Dz_3, gA_Dz_4, gA_Dz_5, gA_Dz_6, gA_Dz_7, gA_Dz,
    gA_nR_1, gA_nR_2, gA_nR_3, gA_nR_4, gA_nR_5, gA_nR_6, gA_nR_7, gA_nR_8, gA_nR_9, gA_nR,
    gA_nRu_1, gA_nRu_2, gA_nRu_3, gA_nRu_4, gA_nRu_5, gA_nRu_6, gA_nRu_7, gA_nRu_8, gA_nRu_9,
    gA_nRu, gA_nRz_1, gA_nRz_2, gA_nRz_3, gA_nRz_4, gA_nRz_5, gA_nRz_6, gA_nRz_7, gA_nRz, gA_nZ_1,
    gA_nZ_2, gA_nZ_3, gA_nZ_4, gA_nZ_5, gA_nZ_6, gA_nZ_7, gA_nZ, gA_nZu_1, gA_nZu_2, gA_nZu_3,
    gA_nZu_4, gA_nZu_5, gA_nZu_6, gA_nZu_7, gA_nZu, gA_nZz_1, gA_nZz_2, gA_nZz_3, gA_nZz_4,
    gA_nZz_5, gA_nZz, gA_V0R, gA_V0Z, gA_W0, gA_AR1, gA_AZ1, gA_DD, gA_G1, gA_G2, gA_G3, gA_YR,
    gA_YZ, gA_P, gA_qD, gA_qW, gA_qR, gA_PR, gA_qD2, gA_qD3, gA_qW2, gA_qDW, gA_Y]

/-- The grids of the variables. -/
def gA (i : ℕ) : ℕ → ℕ → ℤ := gAl.getD i (fun _ _ => 0)

/-- The polynomials of the variables. -/
def PlA : ℕ → P2
  | 0 => Tpoly SA NA MA
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NA MA (gA (n + 4))

/-- The weights of the variables (list). -/
def WtAl : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 0), (0, 1, 0), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1),
    (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3),
    (1, 0, 0), (1, 0, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 1),
    (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 1), (1, 0, 2),
    (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 1), (1, 0, 2),
    (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1),
    (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3),
    (1, 0, 0), (1, 0, 1), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 1),
    (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 3), (1, 0, 1), (1, 0, 2),
    (1, 0, 1), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3),
    (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3),
    (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3),
    (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 1),
    (1, 0, 0), (1, 0, 1), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 2)]

/-- The weights of the variables. -/
def WtA (i : ℕ) : ℕ × ℕ × ℕ := WtAl.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def BxA : ℕ → ℕ × ℕ
  | 0 => (NA, MA)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NA, 2 * MA)

/-- The static `ℓ¹` bound of a data grid of field width `F`. -/
def lwA (F : ℕ) : ℕ := (2 * NA + 1) * (2 * MA + 1) * 2 ^ F

/-- The static `ℓ¹` bound of a weighted (derived) data grid. -/
def lwdA (a b F : ℕ) : ℕ := (2 * NA + 1) * (2 * MA + 1) * ((a * NA + b * MA) * 2 ^ F)

/-- The `ℓ¹` bounds of the variable polynomials (list; static, from the field widths). -/
def LAl : List ℕ :=
  [2 ^ SA, 2, 2, 2, lwA 60, lwA 60, lwdA 1 0 60, lwdA 1 0 60, lwdA 0 1 60, lwdA 0 1 60, lwA 65,
    lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 64, lwA 64, lwA 64,
    lwA 64, lwA 64, lwA 64, lwA 64, lwA 64, lwA 64, lwA 57, lwA 52, lwA 49, lwA 45, lwA 60,
    lwA 56, lwA 52, lwA 49, lwA 45, lwA 60, lwA 56, lwA 52, lwA 48, lwA 45, lwA 60, lwA 56,
    lwA 52, lwA 48, lwA 44, lwA 60, lwA 56, lwA 52, lwA 48, lwA 60, lwA 56, lwA 52, lwA 60,
    lwA 56, lwA 60, lwA 56, lwA 52, lwA 60, lwA 56, lwA 51, lwA 59, lwA 56, lwA 51, lwA 48,
    lwA 44, lwA 59, lwA 55, lwA 51, lwA 47, lwA 44, lwA 59, lwA 55, lwA 51, lwA 47, lwA 43,
    lwA 59, lwA 55, lwA 51, lwA 47, lwA 43, lwA 59, lwA 55, lwA 51, lwA 47, lwA 43, lwA 59,
    lwA 55, lwA 51, lwA 47, lwA 59, lwA 55, lwA 51, lwA 59, lwA 55, lwA 59, lwA 64, lwA 66,
    lwA 65, lwA 66, lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 65, lwA 67, lwA 69, lwA 68,
    lwA 68, lwA 69, lwA 68, lwA 68, lwA 68, lwA 68, lwA 68, lwA 69, lwA 66, lwA 66, lwA 68,
    lwA 67, lwA 66, lwA 62, lwA 64, lwA 65, lwA 65, lwA 64, lwA 65, lwA 66, lwA 64, lwA 64,
    lwA 64, lwA 61, lwA 64, lwA 67, lwA 67, lwA 67, lwA 68, lwA 69, lwA 68, lwA 68, lwA 68,
    lwA 63, lwA 68, lwA 67, lwA 66, lwA 66, lwA 68, lwA 68, lwA 66, lwA 63, lwA 65, lwA 66,
    lwA 65, lwA 64, lwA 66, lwA 65, lwA 63, lwA 61, lwA 66, lwA 68, lwA 67, lwA 68, lwA 70,
    lwA 69, lwA 67, lwA 63, lwA 68, lwA 68, lwA 67, lwA 67, lwA 67, lwA 63, lwA 59, lwA 59,
    lwA 55, lwA 61, lwA 61, lwA 64, lwA 57, lwA 61, lwA 57, lwA 55, lwA 55, lwA 49, lwA 66,
    lwA 76, lwA 66, lwA 49, lwA 67, lwA 69, lwA 87, lwA 90, lwA 72]

/-- The `ℓ¹` bounds of the variable polynomials. -/
def LA (i : ℕ) : ℕ := LAl.getD i 0

/-- The Kronecker images of the variable polynomials. -/
def KvA (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SA * ((1 <<< (b * (NA + W * MA)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => packGridNM b W NA (gA (n + 4)) (2 * MA + 1)

/-- The honest centres. -/
def xA (i : ℕ) : FA := ctr SA NA MA (WtA i) (PlA i)

/-- The phases are below `4`. -/
theorem hWA : ∀ i, (WtA i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxA : ∀ i, InBox (PlA i) (BxA i).1 (BxA i).2
  | 0 => InBox.monomial NA MA _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NA MA _

/-- The grids vanish beyond the last variable. -/
theorem gA_out (n : ℕ) : gA (n + 195) = fun _ _ => 0 := by
  unfold gA
  have h : gAl.length = 195 := by rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `ℓ¹` bounds: the empty chain. -/
theorem l1A_0 : ∀ i, i < 0 → l1 (PlA i) ≤ LA i := fun i h => absurd h (Nat.not_lt_zero i)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `t`. -/
theorem l1A_1 : ∀ i, i < 1 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_0
    (l1_Tpoly SA NA MA)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `V`. -/
theorem l1A_2 : ∀ i, i < 2 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_1
    (l1_Vpoly)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `C`. -/
theorem l1A_3 : ∀ i, i < 3 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_2
    (l1_sPoly)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `S`. -/
theorem l1A_4 : ∀ i, i < 4 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_3
    (l1_cPoly)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `U`. -/
theorem l1A_5 : ∀ i, i < 5 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_4
    (l1_dataGrid_le NA MA 60 datA_U 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Z`. -/
theorem l1A_6 : ∀ i, i < 6 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_5
    (l1_dataGrid_le NA MA 60 datA_Z 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `A`. -/
theorem l1A_7 : ∀ i, i < 7 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_6
    (l1_gridPolyNM_le_const NA MA fun i j hi hj => abs_wgridN_le NA MA 1 0 (fun i j =>
      abs_dataGrid_le NA MA 60 datA_U 0 (by kernel_fact) i j) hi hj)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `B`. -/
theorem l1A_8 : ∀ i, i < 8 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_7
    (l1_gridPolyNM_le_const NA MA fun i j hi hj => abs_wgridN_le NA MA 1 0 (fun i j =>
      abs_dataGrid_le NA MA 60 datA_Z 1 (by kernel_fact) i j) hi hj)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Pu`. -/
theorem l1A_9 : ∀ i, i < 9 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_8
    (l1_gridPolyNM_le_const NA MA fun i j hi hj => abs_wgridN_le NA MA 0 1 (fun i j =>
      abs_dataGrid_le NA MA 60 datA_U 0 (by kernel_fact) i j) hi hj)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Pz`. -/
theorem l1A_10 : ∀ i, i < 10 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_9
    (l1_gridPolyNM_le_const NA MA fun i j hi hj => abs_wgridN_le NA MA 0 1 (fun i j =>
      abs_dataGrid_le NA MA 60 datA_Z 1 (by kernel_fact) i j) hi hj)

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R`. -/
theorem l1A_11 : ∀ i, i < 11 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_10
    (l1_dataGrid_le NA MA 65 datA_R 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R2`. -/
theorem l1A_12 : ∀ i, i < 12 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_11
    (l1_dataGrid_le NA MA 65 datA_R2 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R3`. -/
theorem l1A_13 : ∀ i, i < 13 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_12
    (l1_dataGrid_le NA MA 65 datA_R3 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R4`. -/
theorem l1A_14 : ∀ i, i < 14 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_13
    (l1_dataGrid_le NA MA 65 datA_R4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R5`. -/
theorem l1A_15 : ∀ i, i < 15 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_14
    (l1_dataGrid_le NA MA 65 datA_R5 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R6`. -/
theorem l1A_16 : ∀ i, i < 16 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_15
    (l1_dataGrid_le NA MA 65 datA_R6 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R7`. -/
theorem l1A_17 : ∀ i, i < 17 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_16
    (l1_dataGrid_le NA MA 65 datA_R7 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R8`. -/
theorem l1A_18 : ∀ i, i < 18 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_17
    (l1_dataGrid_le NA MA 65 datA_R8 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R9`. -/
theorem l1A_19 : ∀ i, i < 19 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_18
    (l1_dataGrid_le NA MA 65 datA_R9 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R10`. -/
theorem l1A_20 : ∀ i, i < 20 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_19
    (l1_dataGrid_le NA MA 64 datA_R10 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R11`. -/
theorem l1A_21 : ∀ i, i < 21 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_20
    (l1_dataGrid_le NA MA 64 datA_R11 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R12`. -/
theorem l1A_22 : ∀ i, i < 22 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_21
    (l1_dataGrid_le NA MA 64 datA_R12 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R13`. -/
theorem l1A_23 : ∀ i, i < 23 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_22
    (l1_dataGrid_le NA MA 64 datA_R13 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R14`. -/
theorem l1A_24 : ∀ i, i < 24 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_23
    (l1_dataGrid_le NA MA 64 datA_R14 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R15`. -/
theorem l1A_25 : ∀ i, i < 25 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_24
    (l1_dataGrid_le NA MA 64 datA_R15 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R16`. -/
theorem l1A_26 : ∀ i, i < 26 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_25
    (l1_dataGrid_le NA MA 64 datA_R16 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R17`. -/
theorem l1A_27 : ∀ i, i < 27 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_26
    (l1_dataGrid_le NA MA 64 datA_R17 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `R18`. -/
theorem l1A_28 : ∀ i, i < 28 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_27
    (l1_dataGrid_le NA MA 64 datA_R18 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `z2`. -/
theorem l1A_29 : ∀ i, i < 29 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_28
    (l1_dataGrid_le NA MA 57 datA_z2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `z3`. -/
theorem l1A_30 : ∀ i, i < 30 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_29
    (l1_dataGrid_le NA MA 52 datA_z3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `z4`. -/
theorem l1A_31 : ∀ i, i < 31 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_30
    (l1_dataGrid_le NA MA 49 datA_z4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `z5`. -/
theorem l1A_32 : ∀ i, i < 32 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_31
    (l1_dataGrid_le NA MA 45 datA_z5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m1_1`. -/
theorem l1A_33 : ∀ i, i < 33 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_32
    (l1_dataGrid_le NA MA 60 datA_m1_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m1_2`. -/
theorem l1A_34 : ∀ i, i < 34 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_33
    (l1_dataGrid_le NA MA 56 datA_m1_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m1_3`. -/
theorem l1A_35 : ∀ i, i < 35 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_34
    (l1_dataGrid_le NA MA 52 datA_m1_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m1_4`. -/
theorem l1A_36 : ∀ i, i < 36 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_35
    (l1_dataGrid_le NA MA 49 datA_m1_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m1_5`. -/
theorem l1A_37 : ∀ i, i < 37 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_36
    (l1_dataGrid_le NA MA 45 datA_m1_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m2_1`. -/
theorem l1A_38 : ∀ i, i < 38 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_37
    (l1_dataGrid_le NA MA 60 datA_m2_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m2_2`. -/
theorem l1A_39 : ∀ i, i < 39 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_38
    (l1_dataGrid_le NA MA 56 datA_m2_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m2_3`. -/
theorem l1A_40 : ∀ i, i < 40 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_39
    (l1_dataGrid_le NA MA 52 datA_m2_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m2_4`. -/
theorem l1A_41 : ∀ i, i < 41 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_40
    (l1_dataGrid_le NA MA 48 datA_m2_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m2_5`. -/
theorem l1A_42 : ∀ i, i < 42 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_41
    (l1_dataGrid_le NA MA 45 datA_m2_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m3_1`. -/
theorem l1A_43 : ∀ i, i < 43 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_42
    (l1_dataGrid_le NA MA 60 datA_m3_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m3_2`. -/
theorem l1A_44 : ∀ i, i < 44 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_43
    (l1_dataGrid_le NA MA 56 datA_m3_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m3_3`. -/
theorem l1A_45 : ∀ i, i < 45 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_44
    (l1_dataGrid_le NA MA 52 datA_m3_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m3_4`. -/
theorem l1A_46 : ∀ i, i < 46 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_45
    (l1_dataGrid_le NA MA 48 datA_m3_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m3_5`. -/
theorem l1A_47 : ∀ i, i < 47 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_46
    (l1_dataGrid_le NA MA 44 datA_m3_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m4_1`. -/
theorem l1A_48 : ∀ i, i < 48 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_47
    (l1_dataGrid_le NA MA 60 datA_m4_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m4_2`. -/
theorem l1A_49 : ∀ i, i < 49 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_48
    (l1_dataGrid_le NA MA 56 datA_m4_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m4_3`. -/
theorem l1A_50 : ∀ i, i < 50 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_49
    (l1_dataGrid_le NA MA 52 datA_m4_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m4_4`. -/
theorem l1A_51 : ∀ i, i < 51 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_50
    (l1_dataGrid_le NA MA 48 datA_m4_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m5_1`. -/
theorem l1A_52 : ∀ i, i < 52 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_51
    (l1_dataGrid_le NA MA 60 datA_m5_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m5_2`. -/
theorem l1A_53 : ∀ i, i < 53 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_52
    (l1_dataGrid_le NA MA 56 datA_m5_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m5_3`. -/
theorem l1A_54 : ∀ i, i < 54 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_53
    (l1_dataGrid_le NA MA 52 datA_m5_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m6_1`. -/
theorem l1A_55 : ∀ i, i < 55 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_54
    (l1_dataGrid_le NA MA 60 datA_m6_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m6_2`. -/
theorem l1A_56 : ∀ i, i < 56 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_55
    (l1_dataGrid_le NA MA 56 datA_m6_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m7_1`. -/
theorem l1A_57 : ∀ i, i < 57 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_56
    (l1_dataGrid_le NA MA 60 datA_m7_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m7_2`. -/
theorem l1A_58 : ∀ i, i < 58 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_57
    (l1_dataGrid_le NA MA 56 datA_m7_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m7_3`. -/
theorem l1A_59 : ∀ i, i < 59 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_58
    (l1_dataGrid_le NA MA 52 datA_m7_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m8_1`. -/
theorem l1A_60 : ∀ i, i < 60 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_59
    (l1_dataGrid_le NA MA 60 datA_m8_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m8_2`. -/
theorem l1A_61 : ∀ i, i < 61 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_60
    (l1_dataGrid_le NA MA 56 datA_m8_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m8_3`. -/
theorem l1A_62 : ∀ i, i < 62 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_61
    (l1_dataGrid_le NA MA 51 datA_m8_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m9_1`. -/
theorem l1A_63 : ∀ i, i < 63 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_62
    (l1_dataGrid_le NA MA 59 datA_m9_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m9_2`. -/
theorem l1A_64 : ∀ i, i < 64 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_63
    (l1_dataGrid_le NA MA 56 datA_m9_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m9_3`. -/
theorem l1A_65 : ∀ i, i < 65 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_64
    (l1_dataGrid_le NA MA 51 datA_m9_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m9_4`. -/
theorem l1A_66 : ∀ i, i < 66 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_65
    (l1_dataGrid_le NA MA 48 datA_m9_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m9_5`. -/
theorem l1A_67 : ∀ i, i < 67 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_66
    (l1_dataGrid_le NA MA 44 datA_m9_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m10_1`. -/
theorem l1A_68 : ∀ i, i < 68 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_67
    (l1_dataGrid_le NA MA 59 datA_m10_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m10_2`. -/
theorem l1A_69 : ∀ i, i < 69 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_68
    (l1_dataGrid_le NA MA 55 datA_m10_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m10_3`. -/
theorem l1A_70 : ∀ i, i < 70 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_69
    (l1_dataGrid_le NA MA 51 datA_m10_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m10_4`. -/
theorem l1A_71 : ∀ i, i < 71 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_70
    (l1_dataGrid_le NA MA 47 datA_m10_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m10_5`. -/
theorem l1A_72 : ∀ i, i < 72 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_71
    (l1_dataGrid_le NA MA 44 datA_m10_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m11_1`. -/
theorem l1A_73 : ∀ i, i < 73 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_72
    (l1_dataGrid_le NA MA 59 datA_m11_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m11_2`. -/
theorem l1A_74 : ∀ i, i < 74 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_73
    (l1_dataGrid_le NA MA 55 datA_m11_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m11_3`. -/
theorem l1A_75 : ∀ i, i < 75 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_74
    (l1_dataGrid_le NA MA 51 datA_m11_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m11_4`. -/
theorem l1A_76 : ∀ i, i < 76 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_75
    (l1_dataGrid_le NA MA 47 datA_m11_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m11_5`. -/
theorem l1A_77 : ∀ i, i < 77 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_76
    (l1_dataGrid_le NA MA 43 datA_m11_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m12_1`. -/
theorem l1A_78 : ∀ i, i < 78 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_77
    (l1_dataGrid_le NA MA 59 datA_m12_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m12_2`. -/
theorem l1A_79 : ∀ i, i < 79 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_78
    (l1_dataGrid_le NA MA 55 datA_m12_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m12_3`. -/
theorem l1A_80 : ∀ i, i < 80 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_79
    (l1_dataGrid_le NA MA 51 datA_m12_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m12_4`. -/
theorem l1A_81 : ∀ i, i < 81 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_80
    (l1_dataGrid_le NA MA 47 datA_m12_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m12_5`. -/
theorem l1A_82 : ∀ i, i < 82 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_81
    (l1_dataGrid_le NA MA 43 datA_m12_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m13_1`. -/
theorem l1A_83 : ∀ i, i < 83 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_82
    (l1_dataGrid_le NA MA 59 datA_m13_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m13_2`. -/
theorem l1A_84 : ∀ i, i < 84 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_83
    (l1_dataGrid_le NA MA 55 datA_m13_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m13_3`. -/
theorem l1A_85 : ∀ i, i < 85 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_84
    (l1_dataGrid_le NA MA 51 datA_m13_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m13_4`. -/
theorem l1A_86 : ∀ i, i < 86 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_85
    (l1_dataGrid_le NA MA 47 datA_m13_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m13_5`. -/
theorem l1A_87 : ∀ i, i < 87 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_86
    (l1_dataGrid_le NA MA 43 datA_m13_5 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m14_1`. -/
theorem l1A_88 : ∀ i, i < 88 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_87
    (l1_dataGrid_le NA MA 59 datA_m14_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m14_2`. -/
theorem l1A_89 : ∀ i, i < 89 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_88
    (l1_dataGrid_le NA MA 55 datA_m14_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m14_3`. -/
theorem l1A_90 : ∀ i, i < 90 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_89
    (l1_dataGrid_le NA MA 51 datA_m14_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m14_4`. -/
theorem l1A_91 : ∀ i, i < 91 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_90
    (l1_dataGrid_le NA MA 47 datA_m14_4 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m15_1`. -/
theorem l1A_92 : ∀ i, i < 92 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_91
    (l1_dataGrid_le NA MA 59 datA_m15_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m15_2`. -/
theorem l1A_93 : ∀ i, i < 93 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_92
    (l1_dataGrid_le NA MA 55 datA_m15_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m15_3`. -/
theorem l1A_94 : ∀ i, i < 94 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_93
    (l1_dataGrid_le NA MA 51 datA_m15_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m16_1`. -/
theorem l1A_95 : ∀ i, i < 95 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_94
    (l1_dataGrid_le NA MA 59 datA_m16_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m16_2`. -/
theorem l1A_96 : ∀ i, i < 96 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_95
    (l1_dataGrid_le NA MA 55 datA_m16_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `m17_1`. -/
theorem l1A_97 : ∀ i, i < 97 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_96
    (l1_dataGrid_le NA MA 59 datA_m17_1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_1`. -/
theorem l1A_98 : ∀ i, i < 98 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_97
    (l1_dataGrid_le NA MA 64 datA_D_1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_2`. -/
theorem l1A_99 : ∀ i, i < 99 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_98
    (l1_dataGrid_le NA MA 66 datA_D_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_3`. -/
theorem l1A_100 : ∀ i, i < 100 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_99
    (l1_dataGrid_le NA MA 65 datA_D_3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_4`. -/
theorem l1A_101 : ∀ i, i < 101 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_100
    (l1_dataGrid_le NA MA 66 datA_D_4 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_5`. -/
theorem l1A_102 : ∀ i, i < 102 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_101
    (l1_dataGrid_le NA MA 65 datA_D_5 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_6`. -/
theorem l1A_103 : ∀ i, i < 103 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_102
    (l1_dataGrid_le NA MA 65 datA_D_6 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_7`. -/
theorem l1A_104 : ∀ i, i < 104 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_103
    (l1_dataGrid_le NA MA 65 datA_D_7 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_8`. -/
theorem l1A_105 : ∀ i, i < 105 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_104
    (l1_dataGrid_le NA MA 65 datA_D_8 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D_9`. -/
theorem l1A_106 : ∀ i, i < 106 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_105
    (l1_dataGrid_le NA MA 65 datA_D_9 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `D`. -/
theorem l1A_107 : ∀ i, i < 107 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_106
    (l1_dataGrid_le NA MA 65 datA_D 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_1`. -/
theorem l1A_108 : ∀ i, i < 108 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_107
    (l1_dataGrid_le NA MA 67 datA_Du_1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_2`. -/
theorem l1A_109 : ∀ i, i < 109 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_108
    (l1_dataGrid_le NA MA 69 datA_Du_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_3`. -/
theorem l1A_110 : ∀ i, i < 110 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_109
    (l1_dataGrid_le NA MA 68 datA_Du_3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_4`. -/
theorem l1A_111 : ∀ i, i < 111 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_110
    (l1_dataGrid_le NA MA 68 datA_Du_4 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_5`. -/
theorem l1A_112 : ∀ i, i < 112 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_111
    (l1_dataGrid_le NA MA 69 datA_Du_5 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_6`. -/
theorem l1A_113 : ∀ i, i < 113 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_112
    (l1_dataGrid_le NA MA 68 datA_Du_6 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_7`. -/
theorem l1A_114 : ∀ i, i < 114 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_113
    (l1_dataGrid_le NA MA 68 datA_Du_7 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du_8`. -/
theorem l1A_115 : ∀ i, i < 115 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_114
    (l1_dataGrid_le NA MA 68 datA_Du_8 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Du`. -/
theorem l1A_116 : ∀ i, i < 116 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_115
    (l1_dataGrid_le NA MA 68 datA_Du 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_1`. -/
theorem l1A_117 : ∀ i, i < 117 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_116
    (l1_dataGrid_le NA MA 68 datA_Dz_1 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_2`. -/
theorem l1A_118 : ∀ i, i < 118 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_117
    (l1_dataGrid_le NA MA 69 datA_Dz_2 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_3`. -/
theorem l1A_119 : ∀ i, i < 119 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_118
    (l1_dataGrid_le NA MA 66 datA_Dz_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_4`. -/
theorem l1A_120 : ∀ i, i < 120 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_119
    (l1_dataGrid_le NA MA 66 datA_Dz_4 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_5`. -/
theorem l1A_121 : ∀ i, i < 121 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_120
    (l1_dataGrid_le NA MA 68 datA_Dz_5 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_6`. -/
theorem l1A_122 : ∀ i, i < 122 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_121
    (l1_dataGrid_le NA MA 67 datA_Dz_6 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz_7`. -/
theorem l1A_123 : ∀ i, i < 123 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_122
    (l1_dataGrid_le NA MA 66 datA_Dz_7 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Dz`. -/
theorem l1A_124 : ∀ i, i < 124 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_123
    (l1_dataGrid_le NA MA 62 datA_Dz 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_1`. -/
theorem l1A_125 : ∀ i, i < 125 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_124
    (l1_dataGrid_le NA MA 64 datA_nR_1 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_2`. -/
theorem l1A_126 : ∀ i, i < 126 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_125
    (l1_dataGrid_le NA MA 65 datA_nR_2 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_3`. -/
theorem l1A_127 : ∀ i, i < 127 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_126
    (l1_dataGrid_le NA MA 65 datA_nR_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_4`. -/
theorem l1A_128 : ∀ i, i < 128 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_127
    (l1_dataGrid_le NA MA 64 datA_nR_4 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_5`. -/
theorem l1A_129 : ∀ i, i < 129 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_128
    (l1_dataGrid_le NA MA 65 datA_nR_5 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_6`. -/
theorem l1A_130 : ∀ i, i < 130 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_129
    (l1_dataGrid_le NA MA 66 datA_nR_6 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_7`. -/
theorem l1A_131 : ∀ i, i < 131 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_130
    (l1_dataGrid_le NA MA 64 datA_nR_7 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_8`. -/
theorem l1A_132 : ∀ i, i < 132 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_131
    (l1_dataGrid_le NA MA 64 datA_nR_8 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR_9`. -/
theorem l1A_133 : ∀ i, i < 133 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_132
    (l1_dataGrid_le NA MA 64 datA_nR_9 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nR`. -/
theorem l1A_134 : ∀ i, i < 134 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_133
    (l1_dataGrid_le NA MA 61 datA_nR 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_1`. -/
theorem l1A_135 : ∀ i, i < 135 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_134
    (l1_dataGrid_le NA MA 64 datA_nRu_1 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_2`. -/
theorem l1A_136 : ∀ i, i < 136 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_135
    (l1_dataGrid_le NA MA 67 datA_nRu_2 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_3`. -/
theorem l1A_137 : ∀ i, i < 137 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_136
    (l1_dataGrid_le NA MA 67 datA_nRu_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_4`. -/
theorem l1A_138 : ∀ i, i < 138 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_137
    (l1_dataGrid_le NA MA 67 datA_nRu_4 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_5`. -/
theorem l1A_139 : ∀ i, i < 139 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_138
    (l1_dataGrid_le NA MA 68 datA_nRu_5 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_6`. -/
theorem l1A_140 : ∀ i, i < 140 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_139
    (l1_dataGrid_le NA MA 69 datA_nRu_6 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_7`. -/
theorem l1A_141 : ∀ i, i < 141 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_140
    (l1_dataGrid_le NA MA 68 datA_nRu_7 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_8`. -/
theorem l1A_142 : ∀ i, i < 142 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_141
    (l1_dataGrid_le NA MA 68 datA_nRu_8 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu_9`. -/
theorem l1A_143 : ∀ i, i < 143 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_142
    (l1_dataGrid_le NA MA 68 datA_nRu_9 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRu`. -/
theorem l1A_144 : ∀ i, i < 144 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_143
    (l1_dataGrid_le NA MA 63 datA_nRu 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_1`. -/
theorem l1A_145 : ∀ i, i < 145 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_144
    (l1_dataGrid_le NA MA 68 datA_nRz_1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_2`. -/
theorem l1A_146 : ∀ i, i < 146 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_145
    (l1_dataGrid_le NA MA 67 datA_nRz_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_3`. -/
theorem l1A_147 : ∀ i, i < 147 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_146
    (l1_dataGrid_le NA MA 66 datA_nRz_3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_4`. -/
theorem l1A_148 : ∀ i, i < 148 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_147
    (l1_dataGrid_le NA MA 66 datA_nRz_4 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_5`. -/
theorem l1A_149 : ∀ i, i < 149 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_148
    (l1_dataGrid_le NA MA 68 datA_nRz_5 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_6`. -/
theorem l1A_150 : ∀ i, i < 150 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_149
    (l1_dataGrid_le NA MA 68 datA_nRz_6 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz_7`. -/
theorem l1A_151 : ∀ i, i < 151 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_150
    (l1_dataGrid_le NA MA 66 datA_nRz_7 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nRz`. -/
theorem l1A_152 : ∀ i, i < 152 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_151
    (l1_dataGrid_le NA MA 63 datA_nRz 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_1`. -/
theorem l1A_153 : ∀ i, i < 153 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_152
    (l1_dataGrid_le NA MA 65 datA_nZ_1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_2`. -/
theorem l1A_154 : ∀ i, i < 154 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_153
    (l1_dataGrid_le NA MA 66 datA_nZ_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_3`. -/
theorem l1A_155 : ∀ i, i < 155 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_154
    (l1_dataGrid_le NA MA 65 datA_nZ_3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_4`. -/
theorem l1A_156 : ∀ i, i < 156 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_155
    (l1_dataGrid_le NA MA 64 datA_nZ_4 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_5`. -/
theorem l1A_157 : ∀ i, i < 157 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_156
    (l1_dataGrid_le NA MA 66 datA_nZ_5 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_6`. -/
theorem l1A_158 : ∀ i, i < 158 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_157
    (l1_dataGrid_le NA MA 65 datA_nZ_6 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ_7`. -/
theorem l1A_159 : ∀ i, i < 159 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_158
    (l1_dataGrid_le NA MA 63 datA_nZ_7 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZ`. -/
theorem l1A_160 : ∀ i, i < 160 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_159
    (l1_dataGrid_le NA MA 61 datA_nZ 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_1`. -/
theorem l1A_161 : ∀ i, i < 161 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_160
    (l1_dataGrid_le NA MA 66 datA_nZu_1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_2`. -/
theorem l1A_162 : ∀ i, i < 162 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_161
    (l1_dataGrid_le NA MA 68 datA_nZu_2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_3`. -/
theorem l1A_163 : ∀ i, i < 163 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_162
    (l1_dataGrid_le NA MA 67 datA_nZu_3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_4`. -/
theorem l1A_164 : ∀ i, i < 164 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_163
    (l1_dataGrid_le NA MA 68 datA_nZu_4 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_5`. -/
theorem l1A_165 : ∀ i, i < 165 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_164
    (l1_dataGrid_le NA MA 70 datA_nZu_5 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_6`. -/
theorem l1A_166 : ∀ i, i < 166 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_165
    (l1_dataGrid_le NA MA 69 datA_nZu_6 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu_7`. -/
theorem l1A_167 : ∀ i, i < 167 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_166
    (l1_dataGrid_le NA MA 67 datA_nZu_7 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZu`. -/
theorem l1A_168 : ∀ i, i < 168 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_167
    (l1_dataGrid_le NA MA 63 datA_nZu 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz_1`. -/
theorem l1A_169 : ∀ i, i < 169 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_168
    (l1_dataGrid_le NA MA 68 datA_nZz_1 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz_2`. -/
theorem l1A_170 : ∀ i, i < 170 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_169
    (l1_dataGrid_le NA MA 68 datA_nZz_2 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz_3`. -/
theorem l1A_171 : ∀ i, i < 171 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_170
    (l1_dataGrid_le NA MA 67 datA_nZz_3 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz_4`. -/
theorem l1A_172 : ∀ i, i < 172 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_171
    (l1_dataGrid_le NA MA 67 datA_nZz_4 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz_5`. -/
theorem l1A_173 : ∀ i, i < 173 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_172
    (l1_dataGrid_le NA MA 67 datA_nZz_5 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `nZz`. -/
theorem l1A_174 : ∀ i, i < 174 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_173
    (l1_dataGrid_le NA MA 63 datA_nZz 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `V0R`. -/
theorem l1A_175 : ∀ i, i < 175 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_174
    (l1_dataGrid_le NA MA 59 datA_V0R 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `V0Z`. -/
theorem l1A_176 : ∀ i, i < 176 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_175
    (l1_dataGrid_le NA MA 59 datA_V0Z 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `W0`. -/
theorem l1A_177 : ∀ i, i < 177 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_176
    (l1_dataGrid_le NA MA 55 datA_W0 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `AR1`. -/
theorem l1A_178 : ∀ i, i < 178 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_177
    (l1_dataGrid_le NA MA 61 datA_AR1 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `AZ1`. -/
theorem l1A_179 : ∀ i, i < 179 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_178
    (l1_dataGrid_le NA MA 61 datA_AZ1 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `DD`. -/
theorem l1A_180 : ∀ i, i < 180 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_179
    (l1_dataGrid_le NA MA 64 datA_DD 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `G1`. -/
theorem l1A_181 : ∀ i, i < 181 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_180
    (l1_dataGrid_le NA MA 57 datA_G1 3 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `G2`. -/
theorem l1A_182 : ∀ i, i < 182 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_181
    (l1_dataGrid_le NA MA 61 datA_G2 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `G3`. -/
theorem l1A_183 : ∀ i, i < 183 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_182
    (l1_dataGrid_le NA MA 57 datA_G3 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `YR`. -/
theorem l1A_184 : ∀ i, i < 184 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_183
    (l1_dataGrid_le NA MA 55 datA_YR 1 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `YZ`. -/
theorem l1A_185 : ∀ i, i < 185 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_184
    (l1_dataGrid_le NA MA 55 datA_YZ 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `P`. -/
theorem l1A_186 : ∀ i, i < 186 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_185
    (l1_dataGrid_le NA MA 49 datA_P 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qD`. -/
theorem l1A_187 : ∀ i, i < 187 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_186
    (l1_dataGrid_le NA MA 66 datA_qD 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qW`. -/
theorem l1A_188 : ∀ i, i < 188 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_187
    (l1_dataGrid_le NA MA 76 datA_qW 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qR`. -/
theorem l1A_189 : ∀ i, i < 189 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_188
    (l1_dataGrid_le NA MA 66 datA_qR 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `PR`. -/
theorem l1A_190 : ∀ i, i < 190 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_189
    (l1_dataGrid_le NA MA 49 datA_PR 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qD2`. -/
theorem l1A_191 : ∀ i, i < 191 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_190
    (l1_dataGrid_le NA MA 67 datA_qD2 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qD3`. -/
theorem l1A_192 : ∀ i, i < 192 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_191
    (l1_dataGrid_le NA MA 69 datA_qD3 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qW2`. -/
theorem l1A_193 : ∀ i, i < 193 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_192
    (l1_dataGrid_le NA MA 87 datA_qW2 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `qDW`. -/
theorem l1A_194 : ∀ i, i < 194 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_193
    (l1_dataGrid_le NA MA 90 datA_qDW 0 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds up to the variable `Y`. -/
theorem l1A_195 : ∀ i, i < 195 → l1 (PlA i) ≤ LA i :=
  chain_succ l1A_194
    (l1_dataGrid_le NA MA 72 datA_Y 2 (by kernel_fact))

set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds. -/
theorem l1A (i : ℕ) : l1 (PlA i) ≤ LA i := by
  rcases lt_or_ge i 195 with h | h
  · exact l1A_195 i h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact (l1_gridPolyNM_le_const NA MA (C := 0) fun i j _ _ => by rw [gA_out n]; simp).trans
      (by simp)

/-- The Kronecker images. -/
theorem kronA : ∀ b W i, kron b W (PlA i) = KvA b W i
  | b, W, 0 => kron_Tpoly SA NA MA b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NA MA _

/-- The centre of `t` is `1`. -/
theorem xA_t : xA 0 = 1 := ctr_Tpoly SA NA MA

/-- The centre of `V` is `1`. -/
theorem xA_V : xA 1 = 1 := ctr_Vpoly SA NA MA

/-- The centre of `C` is `cos ψₒ`. -/
theorem xA_C : xA 2 = cSo := ctr_C_o SA NA MA

/-- The centre of `S` is `sin ψₒ`. -/
theorem xA_S : xA 3 = sSo := ctr_S_o SA NA MA

/-- The norm bounds of the centres (list). -/
def BAl : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (68553 / 2 ^ 16 : ℚ), (68553 / 2 ^ 16 : ℚ), (34431 / 250000 : ℚ),
    (2967 / 25000 : ℚ), (545863 / 10 ^ 7 : ℚ), (4118 / 78125 : ℚ), (3141 / 25000 : ℚ),
    (1244069 / 10 ^ 7 : ℚ), (521987 / 500000 : ℚ), (536859 / 500000 : ℚ), (273133 / 250000 : ℚ),
    (55121 / 50000 : ℚ), (110487 / 10 ^ 5 : ℚ), (110127 / 10 ^ 5 : ℚ), (109273 / 10 ^ 5 : ℚ),
    (3376 / 3125 : ℚ), (53673 / 50000 : ℚ), (16637 / 15625 : ℚ), (527121 / 500000 : ℚ),
    (521633 / 500000 : ℚ), (128933 / 125000 : ℚ), (255193 / 250000 : ℚ), (507849 / 500000 : ℚ),
    (1009751 / 10 ^ 6 : ℚ), (501603 / 500000 : ℚ), (99647 / 10 ^ 5 : ℚ), (287577 / 25000000 : ℚ),
    (1061983 / 10 ^ 9 : ℚ), (61491 / 625000000 : ℚ), (224271 / 25000000000 : ℚ),
    (54363 / 500000 : ℚ), (1038301 / 10 ^ 8 : ℚ), (240521 / 250000000 : ℚ),
    (446051 / 5000000000 : ℚ), (254527 / 31250000000 : ℚ), (1008791 / 10 ^ 7 : ℚ),
    (937361 / 10 ^ 8 : ℚ), (435773 / 500000000 : ℚ), (404987 / 5000000000 : ℚ),
    (1852767 / 250000000000 : ℚ), (468267 / 5000000 : ℚ), (52923 / 6250000 : ℚ),
    (31571 / 40000000 : ℚ), (367697 / 5000000000 : ℚ), (842981 / 125000000000 : ℚ),
    (108721 / 1250000 : ℚ), (766841 / 10 ^ 8 : ℚ), (715851 / 10 ^ 9 : ℚ),
    (83521 / 1250000000 : ℚ), (808187 / 10 ^ 7 : ℚ), (704519 / 10 ^ 8 : ℚ),
    (325027 / 500000000 : ℚ), (772191 / 10 ^ 7 : ℚ), (647719 / 10 ^ 8 : ℚ), (92687 / 1250000 : ℚ),
    (37443 / 6250000 : ℚ), (268537 / 500000000 : ℚ), (88939 / 1250000 : ℚ), (562783 / 10 ^ 8 : ℚ),
    (246049 / 500000000 : ℚ), (6821191 / 10 ^ 8 : ℚ), (13517 / 2500000 : ℚ),
    (90483 / 200000000 : ℚ), (51787 / 1250000000 : ℚ), (192227 / 50000000000 : ℚ),
    (6539077 / 10 ^ 8 : ℚ), (518821 / 10 ^ 8 : ℚ), (855773 / 2000000000 : ℚ),
    (117973 / 3125000000 : ℚ), (3503629 / 10 ^ 12 : ℚ), (3144043 / 50000000 : ℚ),
    (497443 / 10 ^ 8 : ℚ), (126917 / 312500000 : ℚ), (87361 / 2500000000 : ℚ),
    (63899 / 20000000000 : ℚ), (3039773 / 50000000 : ℚ), (47663 / 10 ^ 7 : ℚ),
    (192649 / 500000000 : ℚ), (40899 / 1250000000 : ℚ), (117157 / 40000000000 : ℚ),
    (5877523 / 10 ^ 8 : ℚ), (4562799 / 10 ^ 9 : ℚ), (1427 / 3906250 : ℚ), (307813 / 10 ^ 10 : ℚ),
    (2711317 / 10 ^ 12 : ℚ), (1139283 / 20000000 : ℚ), (436439 / 10 ^ 8 : ℚ),
    (346241 / 10 ^ 9 : ℚ), (144839 / 5000000000 : ℚ), (276131 / 5000000 : ℚ),
    (4173337 / 10 ^ 9 : ℚ), (16411 / 50000000 : ℚ), (26777 / 500000 : ℚ),
    (997771 / 250000000 : ℚ), (129839 / 2500000 : ℚ), (35529 / 12500 : ℚ), (153293 / 25000 : ℚ),
    (576609 / 10 ^ 5 : ℚ), (261647 / 50000 : ℚ), (221481 / 50000 : ℚ), (247023 / 50000 : ℚ),
    (252659 / 50000 : ℚ), (735129 / 200000 : ℚ), (113481 / 50000 : ℚ), (1150781 / 10 ^ 6 : ℚ),
    (94527 / 5000 : ℚ), (16099 / 625 : ℚ), (309953 / 10 ^ 4 : ℚ), (23154 / 625 : ℚ),
    (256343 / 5000 : ℚ), (11479 / 250 : ℚ), (476003 / 10 ^ 4 : ℚ), (6419 / 250 : ℚ),
    (647639 / 10 ^ 5 : ℚ), (121281 / 5000 : ℚ), (362467 / 10 ^ 4 : ℚ), (506273 / 50000 : ℚ),
    (166579 / 20000 : ℚ), (300713 / 10 ^ 4 : ℚ), (278071 / 10 ^ 4 : ℚ), (898153 / 10 ^ 5 : ℚ),
    (53067 / 10 ^ 5 : ℚ), (260281 / 10 ^ 5 : ℚ), (338807 / 10 ^ 5 : ℚ), (321743 / 10 ^ 5 : ℚ),
    (807909 / 500000 : ℚ), (2724829 / 10 ^ 6 : ℚ), (513789 / 10 ^ 5 : ℚ), (2178211 / 500000 : ℚ),
    (1124427 / 250000 : ℚ), (2018341 / 10 ^ 6 : ℚ), (1536923 / 10 ^ 7 : ℚ), (284319 / 10 ^ 5 : ℚ),
    (3343 / 200 : ℚ), (7933 / 500 : ℚ), (41983 / 3125 : ℚ), (2342419 / 10 ^ 5 : ℚ),
    (79613 / 1250 : ℚ), (127521 / 2000 : ℚ), (656953 / 10 ^ 4 : ℚ), (8671 / 250 : ℚ),
    (1544909 / 10 ^ 6 : ℚ), (111843 / 5000 : ℚ), (190347 / 10 ^ 4 : ℚ), (703097 / 10 ^ 5 : ℚ),
    (86387 / 10 ^ 4 : ℚ), (83441 / 2500 : ℚ), (40497 / 10 ^ 3 : ℚ), (659717 / 50000 : ℚ),
    (8909 / 4000 : ℚ), (86501 / 25000 : ℚ), (74631 / 12500 : ℚ), (284773 / 10 ^ 5 : ℚ),
    (2214647 / 10 ^ 6 : ℚ), (681061 / 10 ^ 5 : ℚ), (5224763 / 10 ^ 6 : ℚ), (771309 / 500000 : ℚ),
    (86909 / 500000 : ℚ), (745619 / 10 ^ 5 : ℚ), (163071 / 5000 : ℚ), (601347 / 25000 : ℚ),
    (136087 / 5000 : ℚ), (55261 / 625 : ℚ), (205031 / 2500 : ℚ), (256117 / 10 ^ 4 : ℚ),
    (389083 / 250000 : ℚ), (240019 / 10 ^ 4 : ℚ), (14669 / 625 : ℚ), (779857 / 50000 : ℚ),
    (1584929 / 10 ^ 5 : ℚ), (698563 / 50000 : ℚ), (178303 / 10 ^ 5 : ℚ), (132917 / 2500000 : ℚ),
    (227979 / 5000000 : ℚ), (3419817 / 5000000000 : ℚ), (1917219 / 10 ^ 7 : ℚ),
    (1931079 / 10 ^ 7 : ℚ), (280157 / 250000 : ℚ), (306533 / 5000000 : ℚ), (135687 / 625000 : ℚ),
    (616677 / 10 ^ 7 : ℚ), (228649 / 20000000 : ℚ), (1176583 / 10 ^ 8 : ℚ),
    (175341 / 500000000 : ℚ), (381957 / 10 ^ 5 : ℚ), (342681 / 125 : ℚ), (123759 / 10 ^ 5 : ℚ),
    (276023 / 10 ^ 9 : ℚ), (1394173 / 10 ^ 5 : ℚ), (253977 / 5000 : ℚ), (7015240 : ℚ),
    (186023800 : ℚ), (2746757 / 10 ^ 3 : ℚ)]

/-- The norm bounds of the centres. -/
def BA (i : ℕ) : ℚ := BAl.getD i 0

/-- The radii of the balls (list). -/
def EAl : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (0 : ℚ), (2031 / 10 ^ 16 : ℚ), (543 / 10 ^ 15 : ℚ), (97 / 10 ^ 14 : ℚ), (1447 / 10 ^ 15 : ℚ),
    (39 / 20000000000000 : ℚ), (2457 / 10 ^ 15 : ℚ), (297 / 10 ^ 14 : ℚ),
    (867 / 250000000000000 : ℚ), (99 / 25000000000000 : ℚ), (4443 / 10 ^ 15 : ℚ),
    (493 / 10 ^ 14 : ℚ), (5413 / 10 ^ 15 : ℚ), (591 / 10 ^ 14 : ℚ), (641 / 10 ^ 14 : ℚ),
    (173 / 25000000000000 : ℚ), (149 / 20000000000000 : ℚ), (799 / 10 ^ 14 : ℚ),
    (671 / 10 ^ 16 : ℚ), (253 / 10 ^ 16 : ℚ), (389 / 50000000000000000 : ℚ),
    (507 / 250000000000000000 : ℚ), (331 / 5000000000000000 : ℚ), (813 / 10 ^ 16 : ℚ),
    (307 / 10 ^ 16 : ℚ), (111 / 12500000000000000 : ℚ), (2353 / 10 ^ 18 : ℚ),
    (27 / 200000000000000 : ℚ), (943 / 10 ^ 16 : ℚ), (87 / 2500000000000000 : ℚ),
    (961 / 10 ^ 17 : ℚ), (127 / 50000000000000000 : ℚ), (51 / 250000000000000 : ℚ),
    (267 / 2500000000000000 : ℚ), (1891 / 50000000000000000 : ℚ), (1017 / 10 ^ 17 : ℚ),
    (1333 / 500000000000000000 : ℚ), (1347 / 5000000000000000 : ℚ), (119 / 10 ^ 15 : ℚ),
    (201 / 5000000000000000 : ℚ), (529 / 50000000000000000 : ℚ), (3317 / 10 ^ 16 : ℚ),
    (1291 / 10 ^ 16 : ℚ), (419 / 10 ^ 16 : ℚ), (39 / 10 ^ 14 : ℚ), (277 / 2000000000000000 : ℚ),
    (4459 / 10 ^ 16 : ℚ), (731 / 5000000000000000 : ℚ), (437 / 10 ^ 16 : ℚ), (499 / 10 ^ 15 : ℚ),
    (153 / 10 ^ 15 : ℚ), (439 / 10 ^ 16 : ℚ), (5501 / 10 ^ 16 : ℚ), (791 / 5000000000000000 : ℚ),
    (11 / 250000000000000 : ℚ), (1103 / 10 ^ 17 : ℚ), (567 / 200000000000000000 : ℚ),
    (601 / 10 ^ 15 : ℚ), (163 / 10 ^ 15 : ℚ), (439 / 10 ^ 16 : ℚ), (549 / 50000000000000000 : ℚ),
    (141 / 50000000000000000 : ℚ), (653 / 10 ^ 15 : ℚ), (1661 / 10 ^ 16 : ℚ), (437 / 10 ^ 16 : ℚ),
    (1089 / 10 ^ 17 : ℚ), (1397 / 500000000000000000 : ℚ), (353 / 500000000000000 : ℚ),
    (17 / 10 ^ 14 : ℚ), (217 / 5000000000000000 : ℚ), (1079 / 10 ^ 17 : ℚ),
    (69 / 25000000000000000 : ℚ), (381 / 500000000000000 : ℚ), (429 / 2500000000000000 : ℚ),
    (43 / 10 ^ 15 : ℚ), (533 / 50000000000000000 : ℚ), (1361 / 500000000000000000 : ℚ),
    (819 / 10 ^ 15 : ℚ), (7 / 40000000000000 : ℚ), (213 / 5000000000000000 : ℚ),
    (211 / 20000000000000000 : ℚ), (219 / 250000000000000 : ℚ), (89 / 500000000000000 : ℚ),
    (53 / 1250000000000000 : ℚ), (233 / 250000000000000 : ℚ), (181 / 10 ^ 15 : ℚ),
    (99 / 10 ^ 14 : ℚ), (117 / 2500000000000 : ℚ), (229 / 2000000000000 : ℚ),
    (1021 / 5000000000000 : ℚ), (337 / 10 ^ 12 : ℚ), (203 / 500000000000 : ℚ),
    (129 / 250000000000 : ℚ), (109 / 200000000000 : ℚ), (8723 / 10 ^ 13 : ℚ),
    (553 / 500000000000 : ℚ), (61 / 50000000000 : ℚ), (953 / 5000000000000 : ℚ),
    (529 / 10 ^ 12 : ℚ), (879 / 10 ^ 12 : ℚ), (191 / 200000000000 : ℚ), (1109 / 500000000000 : ℚ),
    (509 / 10 ^ 11 : ℚ), (1521 / 250000000000 : ℚ), (193 / 20000000000 : ℚ), (1071 / 10 ^ 11 : ℚ),
    (23 / 62500000000 : ℚ), (991 / 10 ^ 12 : ℚ), (1361 / 10 ^ 12 : ℚ), (717 / 500000000000 : ℚ),
    (981 / 500000000000 : ℚ), (51 / 15625000000 : ℚ), (4549 / 10 ^ 12 : ℚ), (33 / 6250000000 : ℚ),
    (683 / 12500000000000 : ℚ), (1167 / 10 ^ 13 : ℚ), (91 / 500000000000 : ℚ),
    (1243 / 5000000000000 : ℚ), (1303 / 5000000000000 : ℚ), (409 / 10 ^ 12 : ℚ),
    (37 / 50000000000 : ℚ), (13 / 15625000000 : ℚ), (77 / 62500000000 : ℚ),
    (339 / 250000000000 : ℚ), (117 / 2500000000000 : ℚ), (7 / 39062500000 : ℚ),
    (1871 / 5000000000000 : ℚ), (651 / 10 ^ 12 : ℚ), (187 / 250000000000 : ℚ),
    (57 / 25000000000 : ℚ), (3137 / 500000000000 : ℚ), (747 / 10 ^ 11 : ℚ), (33 / 2500000000 : ℚ),
    (1519 / 10 ^ 11 : ℚ), (473 / 1250000000000 : ℚ), (91 / 10 ^ 11 : ℚ), (1129 / 10 ^ 12 : ℚ),
    (593 / 500000000000 : ℚ), (1781 / 10 ^ 12 : ℚ), (1907 / 500000000000 : ℚ),
    (557 / 10 ^ 11 : ℚ), (629 / 10 ^ 11 : ℚ), (691 / 10 ^ 13 : ℚ), (283 / 1250000000000 : ℚ),
    (707 / 2000000000000 : ℚ), (403 / 10 ^ 12 : ℚ), (281 / 500000000000 : ℚ),
    (431 / 500000000000 : ℚ), (223 / 200000000000 : ℚ), (39 / 31250000000 : ℚ),
    (631 / 5000000000000 : ℚ), (1 / 1600000000 : ℚ), (309 / 250000000000 : ℚ),
    (161 / 10 ^ 11 : ℚ), (337 / 10 ^ 11 : ℚ), (723 / 10 ^ 11 : ℚ), (1093 / 10 ^ 11 : ℚ),
    (653 / 50000000000 : ℚ), (173 / 500000000000 : ℚ), (227 / 250000000000 : ℚ),
    (1147 / 10 ^ 12 : ℚ), (7 / 4000000000 : ℚ), (1613 / 500000000000 : ℚ),
    (993 / 250000000000 : ℚ), (623 / 5000000000000000000000 : ℚ), (591 / 10 ^ 22 : ℚ),
    (421 / 2000000000000000 : ℚ), (33 / 312500000000000000000 : ℚ),
    (127 / 1250000000000000000000 : ℚ), (2813 / 10 ^ 12 : ℚ), (1103 / 10 ^ 12 : ℚ),
    (51 / 62500000000 : ℚ), (443 / 500000000000 : ℚ), (507 / 125000000000 : ℚ),
    (371 / 10 ^ 11 : ℚ), (153 / 400000000000 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (419 / 10 ^ 12 : ℚ),
    (1007 / 2000000000000 : ℚ), (193 / 25000000000 : ℚ), (1923 / 5000 : ℚ), (2147 / 10 ^ 2 : ℚ),
    (423 / 5000 : ℚ)]

/-- The radii of the balls. -/
def EA (i : ℕ) : ℚ := EAl.getD i 0

/-- The monomial table: entry `8a + b` is the variable of `R^a z^b`. -/
def monoTab : List ℕ :=
  [0, 5, 28, 29, 30, 31, 0, 0, 10, 32, 33, 34, 35, 36, 0, 0, 11, 37, 38, 39, 40, 41, 0, 0, 12, 42,
    43, 44, 45, 46, 0, 0, 13, 47, 48, 49, 50, 0, 0, 0, 14, 51, 52, 53, 0, 0, 0, 0, 15, 54, 55, 0,
    0, 0, 0, 0, 16, 56, 57, 58, 0, 0, 0, 0, 17, 59, 60, 61, 0, 0, 0, 0, 18, 62, 63, 64, 65, 66, 0,
    0, 19, 67, 68, 69, 70, 71, 0, 0, 20, 72, 73, 74, 75, 76, 0, 0, 21, 77, 78, 79, 80, 81, 0, 0,
    22, 82, 83, 84, 85, 86, 0, 0, 23, 87, 88, 89, 90, 0, 0, 0, 24, 91, 92, 93, 0, 0, 0, 0, 25, 94,
    95, 0, 0, 0, 0, 0, 26, 96, 0, 0, 0, 0, 0, 0, 27, 0, 0, 0, 0, 0, 0, 0]

/-- The variable of the monomial `R^a z^b`. -/
def monoA (a b : ℕ) : ℕ := monoTab.getD (a * 8 + b) 0

/-- The monomials of the chain. -/
def pairsA : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
    (3, 5), (4, 0), (4, 1), (4, 2), (4, 3), (4, 4), (5, 0), (5, 1), (5, 2), (5, 3), (6, 0),
    (6, 1), (6, 2), (7, 0), (7, 1), (7, 2), (7, 3), (8, 0), (8, 1), (8, 2), (8, 3), (9, 0),
    (9, 1), (9, 2), (9, 3), (9, 4), (9, 5), (10, 0), (10, 1), (10, 2), (10, 3), (10, 4), (10, 5),
    (11, 0), (11, 1), (11, 2), (11, 3), (11, 4), (11, 5), (12, 0), (12, 1), (12, 2), (12, 3),
    (12, 4), (12, 5), (13, 0), (13, 1), (13, 2), (13, 3), (13, 4), (13, 5), (14, 0), (14, 1),
    (14, 2), (14, 3), (14, 4), (15, 0), (15, 1), (15, 2), (15, 3), (16, 0), (16, 1), (16, 2),
    (17, 0), (17, 1), (18, 0)]

/-- The R-form polynomials of the field quantities `D, D_u, D_z, n_R, n_R,u, n_R,z, n_z, n_z,u,
n_z,z` (`R = R₀ + u`; `Design/DommaschkKamFieldData`, `DommaschkKamIdentCheck`). -/
def polyA : ℕ → DkPoly.SP
  | 0 => dDR
  | 1 => DkPoly.dU dDR
  | 2 => DkPoly.dZ dDR
  | 3 => DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh
  | 4 => DkPoly.dU (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)
  | 5 => DkPoly.dZ (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)
  | 6 => dnZR
  | 7 => DkPoly.dU dnZR
  | 8 => DkPoly.dZ dnZR
  | _ => []

end PlasmaLean.Design.DommaschkKamC
