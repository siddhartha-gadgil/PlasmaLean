/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCResKron
public import PlasmaLean.Design.DommaschkKamCResData1
public import PlasmaLean.Design.DommaschkKamCResData2
public import PlasmaLean.Design.DommaschkKamCResData3
public import PlasmaLean.Design.DommaschkKamCResData4
public import PlasmaLean.Design.DommaschkKamCResData5
public import PlasmaLean.Design.DommaschkKamCResData6
public import PlasmaLean.Design.DommaschkKamCResData7
public import PlasmaLean.Design.DommaschkKamCResData8
public import PlasmaLean.Design.DommaschkKamCResData9

/-!
# The ball environment of the torus-C residual chain

The variables of the high-resolution ball chain of Dommaschk torus C (N-33 plan item 7): layout
`N = 96`, `M = 80` (the box of the data torus), scale `2^{−128}`, oracle angle `ψₒ = 2φ`, strip
weights `68553^s 2^{16(K − s)}` (`e^r ≤ 68553/2^16`, `Design/DommaschkKamCKronW`). The grids are
salted packed rows (`rowsH i`, `Design/DommaschkKamCResKron`); their polynomials `PlH i`,
weights `WtH i`, boxes `BxH i`, static `ℓ¹` bounds `LH i = rowsL1 (rowsH i)`, Kronecker images
`KvH b W i` (`imgR` for `b ≥ 1`), the honest centres `xH i`, the norm bounds `BH i` and radii
`EH i` (supplied by the oracle `scripts/dommaschk_kam/emit_res.py`, checked in
`Design/DommaschkKamCResCheck*` and `Design/DommaschkKamCResChain`), and the monomial table
`monoH` (`z^b`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos ψₒ`, `sin ψₒ`; `4 … 7` the data `U`, `Z`,
`LUx`, `LZx`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamC

open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex

/-- Layout: poloidal half width. -/
def NH : ℕ := 96
/-- Layout: toroidal half width. -/
def MH : ℕ := 80
/-- Layout: scale exponent. -/
def SH : ℕ := 128

/-- The salted rows of the variables (list; the constants have none). -/
def rowsHl : List (List RowR) :=
  [[], [], [], [], rowsH_U, rowsH_Z, rowsH_LUx, rowsH_LZx, rowsH_R, rowsH_s, rowsH_z2, rowsH_z3,
    rowsH_z4, rowsH_z5, rowsH_LU, rowsH_LZ, rowsH_Dc8, rowsH_Dc7, rowsH_D7, rowsH_Dc6, rowsH_D6,
    rowsH_Dc5, rowsH_D5, rowsH_Dc4, rowsH_D4, rowsH_Dc3, rowsH_D3, rowsH_Dc2, rowsH_D2, rowsH_Dc1,
    rowsH_D1, rowsH_Dc0, rowsH_D0, rowsH_Gc8, rowsH_Gc7, rowsH_G7, rowsH_Gc6, rowsH_G6, rowsH_Gc5,
    rowsH_G5, rowsH_Gc4, rowsH_G4, rowsH_G3, rowsH_Gc2, rowsH_G2, rowsH_Gc1, rowsH_G1, rowsH_Gc0,
    rowsH_G0, rowsH_Fc8, rowsH_Fc7, rowsH_F7, rowsH_Fc6, rowsH_F6, rowsH_Fc5, rowsH_F5, rowsH_Fc4,
    rowsH_F4, rowsH_Fc3, rowsH_F3, rowsH_Fc2, rowsH_F2, rowsH_Fc1, rowsH_F1, rowsH_Fc0, rowsH_F0]

/-- The salted rows of variable `i`. -/
def rowsH (i : ℕ) : List RowR := rowsHl.getD i []

/-- The polynomials of the variables. -/
def PlH : ℕ → P2
  | 0 => Tpoly SH NH MH
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NH MH (gridR (rowsH (n + 4)))

/-- The weights of the variables (list). -/
def WtHl : List (ℕ × ℕ × ℕ) :=
  [(1, 0, 0), (0, 1, 0), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 0),
    (1, 0, 2), (1, 0, 0), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 1), (1, 0, 3),
    (1, 0, 1), (1, 0, 3), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3),
    (1, 0, 3), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2), (1, 0, 2),
    (1, 0, 2), (1, 0, 2)]

/-- The weights of the variables. -/
def WtH (i : ℕ) : ℕ × ℕ × ℕ := WtHl.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def BxH : ℕ → ℕ × ℕ
  | 0 => (NH, MH)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NH, 2 * MH)

/-- The static `ℓ¹` bounds of the variable polynomials. -/
def LH : ℕ → ℕ
  | 0 => 2 ^ SH
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | n + 4 => rowsL1 (rowsH (n + 4))

/-- The Kronecker images of the variable polynomials (fast row images for `b ≥ 1`). -/
def KvH (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SH * ((1 <<< (b * (NH + W * MH)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => cond (Nat.ble 1 b) (imgR b W (rowsH (n + 4)) (2 * MH + 1))
      (packGridNM b W NH (gridR (rowsH (n + 4))) (2 * MH + 1))

/-- The honest centres. -/
def xH (i : ℕ) : FA := ctr SH NH MH (WtH i) (PlH i)

/-- The phases are below `4`. -/
theorem hWH : ∀ i, (WtH i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxH : ∀ i, InBox (PlH i) (BxH i).1 (BxH i).2
  | 0 => InBox.monomial NH MH _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NH MH _

/-- `ℓ¹` bounds. -/
theorem l1H : ∀ i, l1 (PlH i) ≤ LH i
  | 0 => l1_Tpoly SH NH MH
  | 1 => l1_Vpoly
  | 2 => l1_sPoly
  | 3 => l1_cPoly
  | _ + 4 => l1_gridR_le NH MH _

/-- All rows lie in the box. -/
theorem rowsH_ok : ∀ rs ∈ rowsHl, rowsOK NH rs = true := by kernel_fact

/-- The rows of every variable lie in the box. -/
theorem rowsH_ok' (i : ℕ) : rowsOK NH (rowsH i) = true :=
  getD_prop (Pr := fun rs => rowsOK NH rs = true) rowsH_ok rfl i

/-- The Kronecker images. -/
theorem kronH : ∀ b W i, kron b W (PlH i) = KvH b W i
  | b, W, 0 => kron_Tpoly SH NH MH b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, n + 4 => by
    change kron b W (gridPolyNM NH MH (gridR (rowsH (n + 4)))) =
      cond (Nat.ble 1 b) (imgR b W (rowsH (n + 4)) (2 * MH + 1))
        (packGridNM b W NH (gridR (rowsH (n + 4))) (2 * MH + 1))
    rcases Nat.lt_or_ge b 1 with hb | hb
    · have h : Nat.ble 1 b = false := Bool.eq_false_iff.2 fun h => by
        have := Nat.le_of_ble_eq_true h; omega
      rw [h, Bool.cond_false, kron_gridPolyNM]
    · rw [Nat.ble_eq_true_of_le hb, Bool.cond_true]
      exact kron_gridR b W NH MH hb (by norm_num [MH]) _ (rowsH_ok' _)

/-- The centre of `t` is `1`. -/
theorem xH_t : xH 0 = 1 := ctr_Tpoly SH NH MH

/-- The centre of `V` is `1`. -/
theorem xH_V : xH 1 = 1 := ctr_Vpoly SH NH MH

/-- The centre of `C` is `cos ψₒ`. -/
theorem xH_C : xH 2 = cSo := ctr_C_o SH NH MH

/-- The centre of `S` is `sin ψₒ`. -/
theorem xH_S : xH 3 = sSo := ctr_S_o SH NH MH

/-- The norm bounds of the centres (list). -/
def BHl : List ℚ :=
  [(1 : ℚ), (1 : ℚ), (68553 / 2 ^ 16 : ℚ), (68553 / 2 ^ 16 : ℚ), (34431 / 250000 : ℚ),
    (593399 / 5000000 : ℚ), (86314400000000000000000000000000000000 : ℚ),
    (85832600000000000000000000000000000000 : ℚ), (521987 / 500000 : ℚ), (544941 / 500000 : ℚ),
    (140849 / 10 ^ 7 : ℚ), (835797 / 500000000 : ℚ), (396769 / 2000000000 : ℚ),
    (235443 / 10 ^ 10 : ℚ), (2536553 / 10 ^ 7 : ℚ), (1261197 / 5000000 : ℚ), (174051 / 20000 : ℚ),
    (696351 / 20000 : ℚ), (27689 / 625 : ℚ), (468069 / 10 ^ 4 : ℚ), (950913 / 10 ^ 4 : ℚ),
    (47091 / 2000 : ℚ), (635919 / 5000 : ℚ), (254977 / 10 ^ 5 : ℚ), (352913 / 2500 : ℚ),
    (1002001 / 50000 : ℚ), (347787 / 2000 : ℚ), (509059 / 10 ^ 4 : ℚ), (24043 / 10 ^ 2 : ℚ),
    (479829 / 10 ^ 4 : ℚ), (3100233 / 10 ^ 4 : ℚ), (1532559 / 10 ^ 5 : ℚ), (70643 / 200 : ℚ),
    (145043 / 10 ^ 4 : ℚ), (493377 / 10 ^ 4 : ℚ), (814321 / 12500 : ℚ), (70111 / 1250 : ℚ),
    (12709 / 10 ^ 2 : ℚ), (48713 / 2000 : ℚ), (1628697 / 10 ^ 4 : ℚ), (254977 / 10 ^ 5 : ℚ),
    (900293 / 5000 : ℚ), (1962427 / 10 ^ 4 : ℚ), (526269 / 25000 : ℚ), (234933 / 10 ^ 3 : ℚ),
    (108586 / 3125 : ℚ), (181748 / 625 : ℚ), (1532559 / 10 ^ 5 : ℚ), (16613 / 50 : ℚ),
    (5613459 / 10 ^ 6 : ℚ), (3142123 / 10 ^ 5 : ℚ), (375393 / 10 ^ 4 : ℚ), (497887 / 10 ^ 4 : ℚ),
    (453511 / 5000 : ℚ), (258447 / 10 ^ 4 : ℚ), (623497 / 5000 : ℚ), (640809 / 10 ^ 5 : ℚ),
    (711579 / 5000 : ℚ), (133369 / 20000 : ℚ), (1617759 / 10 ^ 4 : ℚ), (425091 / 10 ^ 4 : ℚ),
    (1094129 / 5000 : ℚ), (269283 / 5000 : ℚ), (292351 / 10 ^ 3 : ℚ), (519347 / 25000 : ℚ),
    (169701 / 500 : ℚ)]

/-- The norm bounds of the centres. -/
def BH (i : ℕ) : ℚ := BHl.getD i 0

/-- The radii of the balls (list). -/
def EHl : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (2419 / 10 ^ 34 : ℚ), (21 / 10 ^ 33 : ℚ), (201 / 25000000000000000000000000000000000 : ℚ),
    (239 / 10 ^ 35 : ℚ), (99 / 125000000000000000000000000000000000 : ℚ),
    (179 / 500000000000000000000000000000000000 : ℚ), (33 / 10 ^ 35 : ℚ),
    (357 / 50000000000000000000000000000000 : ℚ), (3403 / 10 ^ 32 : ℚ),
    (17 / 312500000000000000000000000000 : ℚ), (411 / 10 ^ 31 : ℚ),
    (93 / 625000000000000000000000000000 : ℚ), (659 / 50000000000000000000000000000000 : ℚ),
    (2393 / 10 ^ 31 : ℚ), (267 / 250000000000000000000000000000000 : ℚ),
    (1527 / 5000000000000000000000000000000 : ℚ), (1041 / 10 ^ 33 : ℚ),
    (1871 / 5000000000000000000000000000000 : ℚ), (359 / 12500000000000000000000000000000 : ℚ),
    (5037 / 10 ^ 31 : ℚ), (411 / 10 ^ 31 : ℚ), (347 / 500000000000000000000000000000 : ℚ),
    (7 / 400000000000000000000000000000 : ℚ), (437 / 500000000000000000000000000000 : ℚ),
    (119 / 10 ^ 31 : ℚ), (4487 / 10 ^ 32 : ℚ), (197 / 2500000000000000000000000000000 : ℚ),
    (1079 / 25000000000000000000000000000000 : ℚ), (1969 / 10 ^ 31 : ℚ),
    (667 / 50000000000000000000000000000000 : ℚ), (609 / 2000000000000000000000000000000 : ℚ),
    (267 / 250000000000000000000000000000000 : ℚ), (383 / 10 ^ 30 : ℚ),
    (233 / 500000000000000000000000000000 : ℚ), (969 / 10 ^ 32 : ℚ),
    (71 / 125000000000000000000000000000 : ℚ), (279 / 10 ^ 31 : ℚ),
    (363 / 500000000000000000000000000000 : ℚ), (873 / 50000000000000000000000000000000 : ℚ),
    (451 / 500000000000000000000000000000 : ℚ),
    (91 / 62500000000000000000000000000000000000000 : ℚ),
    (169 / 12500000000000000000000000000000 : ℚ), (9 / 400000000000000000000000000000 : ℚ),
    (313 / 10 ^ 31 : ℚ), (931 / 10 ^ 31 : ℚ), (61 / 4000000000000000000000000000000 : ℚ),
    (1753 / 10 ^ 31 : ℚ), (513 / 10 ^ 33 : ℚ), (311 / 1250000000000000000000000000000 : ℚ),
    (483 / 10 ^ 41 : ℚ), (779 / 2500000000000000000000000000000 : ℚ), (831 / 10 ^ 32 : ℚ),
    (3987 / 10 ^ 31 : ℚ), (1471 / 50000000000000000000000000000000 : ℚ),
    (1393 / 2500000000000000000000000000000 : ℚ), (497 / 25000000000000000000000000000000 : ℚ),
    (3589 / 5000000000000000000000000000000 : ℚ)]

/-- The radii of the balls. -/
def EH (i : ℕ) : ℚ := EHl.getD i 0

/-- The monomial table: the variable of `z^b` (`b ≤ 5`; `t` for `b = 0`). -/
def monoH (_a b : ℕ) : ℕ := [0, 5, 10, 11, 12, 13].getD b 0

end PlasmaLean.Design.DommaschkKamC
