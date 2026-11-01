/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCResKron
public import PlasmaLean.Design.DommaschkKamATorus
public import PlasmaLean.Design.DommaschkKamAResData1
public import PlasmaLean.Design.DommaschkKamAResData2
public import PlasmaLean.Design.DommaschkKamAResData3
public import PlasmaLean.Design.DommaschkKamAResData4
public import PlasmaLean.Design.DommaschkKamAResData5
public import PlasmaLean.Design.DommaschkKamAResData6
public import PlasmaLean.Design.DommaschkKamAResData7
public import PlasmaLean.Design.DommaschkKamAResData8
public import PlasmaLean.Design.DommaschkKamAResData9

/-!
# The ball environment of the torus-A residual chain

The variables of the high-resolution ball chain of Dommaschk torus A (N-33 plan item 7): layout
`N = 96`, `M = 80` (the box of the data torus), scale `2^{−128}`, oracle angle `ψₒ = 2φ`, strip
weights `68553^s 2^{16(K − s)}` (`e^r ≤ 68553/2^16`, `Design/DommaschkKamCKronW`). The grids are
salted packed rows (`rowsH i`, `Design/DommaschkKamCResKron`); their polynomials `PlH i`,
weights `WtH i`, boxes `BxH i`, static `ℓ¹` bounds `LH i = rowsL1 (rowsH i)`, Kronecker images
`KvH b W i` (`imgR` for `b ≥ 1`), the honest centres `xH i`, the norm bounds `BH i` and radii
`EH i` (supplied by the oracle `scripts/dommaschk_kam/emit_res.py`, checked in
`Design/DommaschkKamAResCheck*` and `Design/DommaschkKamAResChain`), and the monomial table
`monoH` (`z^b`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos ψₒ`, `sin ψₒ`; `4 … 7` the data `U`, `Z`,
`LUx`, `LZx`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamA

open PlasmaLean.Design.DommaschkKamC

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
  [(1 : ℚ), (1 : ℚ), (68553 / 2 ^ 16 : ℚ), (68553 / 2 ^ 16 : ℚ), (792573 / 5000000 : ℚ),
    (675509 / 5000000 : ℚ), (94520000000000000000000000000000000000 : ℚ),
    (94365100000000000000000000000000000000 : ℚ), (212953 / 200000 : ℚ), (45349 / 40000 : ℚ),
    (7301 / 400000 : ℚ), (1232973 / 500000000 : ℚ), (166577 / 500000000 : ℚ),
    (225049 / 5000000000 : ℚ), (27777 / 10 ^ 5 : ℚ), (1386571 / 5000000 : ℚ),
    (185113 / 20000 : ℚ), (3783937 / 10 ^ 5 : ℚ), (30208 / 625 : ℚ), (159903 / 3125 : ℚ),
    (1059651 / 10 ^ 4 : ℚ), (315447 / 12500 : ℚ), (1453711 / 10 ^ 4 : ℚ), (2761573 / 10 ^ 6 : ℚ),
    (67029 / 400 : ℚ), (405299 / 20000 : ℚ), (2102461 / 10 ^ 4 : ℚ), (5438457 / 10 ^ 5 : ℚ),
    (2927459 / 10 ^ 4 : ℚ), (265313 / 5000 : ℚ), (96239 / 250 : ℚ), (87417 / 5000 : ℚ),
    (4539177 / 10 ^ 4 : ℚ), (96413 / 6250 : ℚ), (6696 / 125 : ℚ), (3552847 / 50000 : ℚ),
    (6115627 / 10 ^ 5 : ℚ), (1417153 / 10 ^ 4 : ℚ), (52211 / 2000 : ℚ), (1867717 / 10 ^ 4 : ℚ),
    (2761573 / 10 ^ 6 : ℚ), (1072547 / 5000 : ℚ), (2431947 / 10 ^ 4 : ℚ), (449323 / 20000 : ℚ),
    (2981821 / 10 ^ 4 : ℚ), (480067 / 12500 : ℚ), (188231 / 500 : ℚ), (87417 / 5000 : ℚ),
    (2221439 / 5000 : ℚ), (5613459 / 10 ^ 6 : ℚ), (329941 / 10 ^ 4 : ℚ), (393583 / 10 ^ 4 : ℚ),
    (132791 / 2500 : ℚ), (9773789 / 10 ^ 5 : ℚ), (2742647 / 10 ^ 5 : ℚ), (172793 / 1250 : ℚ),
    (649089 / 10 ^ 5 : ℚ), (1632107 / 10 ^ 4 : ℚ), (133369 / 20000 : ℚ), (958523 / 5000 : ℚ),
    (436809 / 10 ^ 4 : ℚ), (652553 / 2500 : ℚ), (287777 / 5000 : ℚ), (3534817 / 10 ^ 4 : ℚ),
    (461259 / 20000 : ℚ), (211907 / 500 : ℚ)]

/-- The norm bounds of the centres. -/
def BH (i : ℕ) : ℚ := BHl.getD i 0

/-- The radii of the balls (list). -/
def EHl : List ℚ :=
  [(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ),
    (991 / 10 ^ 32 : ℚ), (699 / 500000000000000000000000000000000 : ℚ), (449 / 10 ^ 33 : ℚ),
    (973 / 10 ^ 34 : ℚ), (411 / 20000000000000000000000000000000000 : ℚ),
    (237 / 250000000000000000000000000000000000 : ℚ),
    (439 / 500000000000000000000000000000000000 : ℚ), (129 / 500000000000000000000000000000 : ℚ),
    (1253 / 10 ^ 30 : ℚ), (953 / 500000000000000000000000000000 : ℚ), (161 / 10 ^ 29 : ℚ),
    (5313 / 10 ^ 30 : ℚ), (371 / 500000000000000000000000000000 : ℚ), (923 / 10 ^ 29 : ℚ),
    (27 / 400000000000000000000000000000 : ℚ), (127 / 10 ^ 28 : ℚ), (7 / 10 ^ 29 : ℚ),
    (41 / 2500000000000000000000000000 : ℚ), (1427 / 10 ^ 30 : ℚ), (227 / 10 ^ 28 : ℚ),
    (41 / 20000000000000000000000000000 : ℚ), (319 / 10 ^ 28 : ℚ),
    (7 / 8000000000000000000000000000 : ℚ), (83 / 2000000000000000000000000000 : ℚ),
    (43 / 10 ^ 29 : ℚ), (1639 / 10 ^ 30 : ℚ), (273 / 10 ^ 29 : ℚ),
    (7 / 4000000000000000000000000000 : ℚ), (707 / 10 ^ 29 : ℚ),
    (19 / 25000000000000000000000000000 : ℚ), (119 / 10 ^ 28 : ℚ),
    (27 / 400000000000000000000000000000 : ℚ), (1601 / 10 ^ 29 : ℚ),
    (511 / 25000000000000000000000000000 : ℚ), (111 / 200000000000000000000000000000 : ℚ),
    (131 / 5000000000000000000000000000 : ℚ), (29 / 20000000000000000000000000000 : ℚ),
    (347 / 10 ^ 28 : ℚ), (7 / 8000000000000000000000000000 : ℚ),
    (223 / 5000000000000000000000000000 : ℚ),
    (91 / 62500000000000000000000000000000000000000 : ℚ),
    (339 / 500000000000000000000000000000 : ℚ), (113 / 10 ^ 29 : ℚ),
    (817 / 500000000000000000000000000000 : ℚ), (4829 / 10 ^ 30 : ℚ),
    (177 / 200000000000000000000000000000 : ℚ), (27 / 3125000000000000000000000000 : ℚ),
    (21 / 10 ^ 30 : ℚ), (1189 / 10 ^ 29 : ℚ), (483 / 10 ^ 41 : ℚ), (153 / 10 ^ 28 : ℚ),
    (1157 / 2000000000000000000000000000000 : ℚ), (201 / 10 ^ 28 : ℚ),
    (81 / 50000000000000000000000000000 : ℚ), (57 / 2000000000000000000000000000 : ℚ),
    (51 / 50000000000000000000000000000 : ℚ), (1889 / 50000000000000000000000000000 : ℚ)]

/-- The radii of the balls. -/
def EH (i : ℕ) : ℚ := EHl.getD i 0

/-- The monomial table: the variable of `z^b` (`b ≤ 5`; `t` for `b = 0`). -/
def monoH (_a b : ℕ) : ℕ := [0, 5, 10, 11, 12, 13].getD b 0

end PlasmaLean.Design.DommaschkKamA
