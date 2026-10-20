/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.ValidatedBVP

/-!
# Certificate data for the validated slab equilibrium

Exact rational data, produced by the untrusted oracle `scripts/validated_slab_oracle.py`, for
the normalized slab Grad–Shafranov problem

  `φ'' + a (e^φ - 1) = 0`, `a = 51/50`, `φ` even and `2π`-periodic,

together with the finite rational inequalities that the radii-polynomial argument of
`PlasmaLean.Design.ValidatedSlabEquilibrium` needs. Every check is an exact computation on
`ℚ` closed by `decide +kernel` (finite sums over integer intervals).

* `ubarq`: candidate cosine coefficients `ū_k = ū_{|k|}`, `|k| ≤ 10`, over `10¹⁴`.
* `Pq n`: rounded Taylor terms `P_n ≈ ūⁿ/n!` (`n ≤ 16`, `|k| ≤ 16`, over `10¹⁶`);
  `Pq 0 = δ₀`.
  `check_taylor` bounds the one-step defects `‖ū P_n/(n+1) - P_{n+1}‖₁ ≤ 2·10⁻¹⁵`.
* `Ebarq = ∑ₙ Pq n` (`check_Ebar`), the rational enclosure centre of `e^ū`.
* `Aq`: the `21×21` block (rows/columns `|k| ≤ 10`, over `10⁵`) of the approximate inverse;
  the identity's negative on the tail.
* `Jq`: block of the symmetrized derivative `DF̃(ū)h = -h + Λ(P_e h + a Ē ⋆ P_e h)`
  (rows `|l| ≤ 10`, columns `|m| ≤ 26`), with `P_e h = (h + Rh)/2`.

Checks: `check_Zblock` (`Z` block `≤ 31/10⁴`), `check_AL` (column sums of `AΛ ≤ 34`),
`check_inj` (`‖I - J A‖ ≤ 1/2` on the block, so `A` is injective), `check_normU`,
`check_normE`, `check_Y` (residual of the rational problem `≤ 25·10⁻¹³`).
-/
public section

namespace PlasmaLean.Design.ValidatedSlab

open scoped BigOperators

/-- The parameter `a = 51/50` (the linearization frequency² about `φ = 0`). -/
@[expose] def aq : ℚ := 51 / 50

/-- The candidate block `|k| ≤ 10`. -/
@[expose] def blk : Finset ℤ := Finset.Icc (-10) 10

/-- The support `|k| ≤ 16` of the Taylor terms and of `Ē`. -/
@[expose] def blkK : Finset ℤ := Finset.Icc (-16) 16

/-- The column range `|m| ≤ 26 = 10 + 16`. -/
@[expose] def blk2 : Finset ℤ := Finset.Icc (-26) 26

/-- Numerators (over `10¹⁴`) of `ū₀, …, ū₁₀`. -/
@[expose] def ubarNum : List ℤ := [-5985333477778, 24505911963996, 992592654498, 60436676094,
                                   4254894286, 322447177, 25549560, 2086018, 174028, 14757, 1267]

/-- Candidate coefficient `ūₖ` (even, zero for `|k| > 10`). -/
@[expose] def ubarq (k : ℤ) : ℚ :=
  if k.natAbs ≤ 10 then (ubarNum.getD k.natAbs 0 : ℚ) / 10 ^ 14 else 0

/-- Numerators (over `10¹⁶`) of the Taylor terms `P_n`, `n = 0, …, 16`, entries `k = 0..16`. -/
@[expose] def PNum : List (List ℤ) :=
  [[10000000000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [-598533347777800, 2450591196399600, 99259265449800, 6043667609400, 425489428600, 32244717700,
     2554956000, 208601800, 17402800, 1475700, 126700, 0, 0, 0, 0, 0, 0],
    [619440740585563, -122291419541657, 295814161386391, 24067246223077, 1956136340679,
     162957308074, 13849905628, 1195119561, 104341053, 9194114, 813558, 73329, 3889, 249, 17, 1, 0],
    [-30370377187968, 76939047900889, -11889799607126, 23562906134975, 2903082779528,
     295820138096, 28569841090, 2702429828, 253259241, 23630213, 2200524, 204065, 19122, 1454,
     111, 8, 1],
    [9829923682578, -3492032969699, 6278544106664, -715265960621, 1400189985446, 232660610068,
     28560161747, 3144015166, 328325496, 33282886, 3312347, 325708, 31671, 3083, 271, 23, 2],
    [-435193185200, 823880063712, -259412584016, 379606472654, -28233799692, 66562272942,
     13960833412, 2007251825, 248384837, 28421601, 3103199, 328593, 34068, 3471, 351, 34, 3],
    [70858911002, -34623436120, 51063508655, -14098799161, 18179083616, -636099344, 2651861176,
     670231444, 110466649, 15187827, 1891281, 221480, 24886, 2716, 290, 30, 3],
    [-2887501687, 4501171973, -2018775366, 2500792839, -597632078, 719895810, 3535617, 91600035,
     26864797, 4987405, 754287, 101590, 12709, 1511, 173, 19, 2],
    [292729155, -175460380, 225651314, -92573089, 100961793, -20495666, 24303732, 1112842,
     2815202, 926434, 190809, 31465, 4558, 607, 76, 9, 1],
    [-11015664, 15007584, -8376705, 9313354, -3484855, 3460880, -580087, 715864, 62895, 78520,
     28108, 6335, 1130, 175, 25, 3, 0],
    [785950, -541576, 632832, -328727, 325920, -110816, 102967, -13617, 18740, 2456, 2017, 763,
     186, 36, 6, 1, 0],
    [-27299, 33820, -21862, 22606, -10929, 9883, -3037, 2705, -261, 443, 77, 48, 19, 5, 1, 0, 0],
    [1484, -1127, 1232, -748, 699, -315, 264, -73, 64, -4, 10, 2, 1, 0, 0, 0, 0],
    [-48, 55, -39, 39, -22, 19, -8, 6, -2, 1, 0, 0, 0, 0, 0, 0, 0],
    [2, -2, 2, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Rounded Taylor term `P_n(k) ≈ (ūⁿ/n!)_k` (even, zero for `|k| > 16`). -/
@[expose] def Pq (n : ℕ) (k : ℤ) : ℚ :=
  if k.natAbs ≤ 16 then ((PNum.getD n []).getD k.natAbs 0 : ℚ) / 10 ^ 16 else 0

/-- Numerators (over `10¹⁶`) of `Ē = ∑ₙ Pₙ`. -/
@[expose] def EbarNum : List ℤ := [10000000000000068, 2402540388627072, 389252021371776,
                                   53326478906597, 6674343978706, 790311707330, 90174918501,
                                   10021067386, 1091941511, 117187596, 12422917, 1293378, 132239,
                                   13307, 1321, 128, 12]

/-- `Ēₖ` (even, zero for `|k| > 16`). -/
@[expose] def Ebarq (k : ℤ) : ℚ :=
  if k.natAbs ≤ 16 then (EbarNum.getD k.natAbs 0 : ℚ) / 10 ^ 16 else 0

/-- Numerators (over `10⁵`) of the block of the approximate inverse, `k, l = -10, …, 10`. -/
@[expose] def ANum : List (List ℤ) :=
  [[-101021, -127, -21, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -21, -127, -1021],
    [-156, -101264, -158, -27, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -4, -27, -158, -1264, -156],
    [-33, -200, -101605, -203, -34, -5, -1, 0, 0, 0, 0, 0, 0, 0, -1, -5, -34, -203, -1605, -200,
     -33],
    [-6, -44, -264, -102108, -271, -47, -7, -1, -1, -1, 0, -1, -1, -1, -7, -47, -271, -2108, -264,
     -44, -6],
    [-1, -9, -61, -366, -102893, -381, -69, -12, -6, -15, 4, -15, -6, -12, -69, -381, -2893, -366,
     -61, -9, -1],
    [0, -2, -13, -90, -543, -104226, -585, -122, -57, -160, 40, -160, -57, -122, -585, -4226,
     -543, -90, -13, -2, 0],
    [0, 0, -3, -22, -150, -895, -106793, -1104, -596, -1693, 422, -1693, -596, -1104, -6793, -895,
     -150, -22, -3, 0, 0],
    [0, 0, -1, -6, -46, -317, -1877, -113492, -6109, -18024, 4493, -18024, -6109, -13492, -1877,
     -317, -46, -6, -1, 0, 0],
    [0, 0, -1, -5, -41, -299, -2027, -12217, -172560, -197051, 49264, -197051, -72560, -12217,
     -2027, -299, -41, -5, -1, 0, 0],
    [0, -1, -5, -36, -282, -2085, -14389, -90119, -492628, -2570128, 613239, -2470128, -492628,
     -90119, -14389, -2085, -282, -36, -5, -1, 0],
    [0, 0, 2, 18, 140, 1038, 7168, 44933, 246319, 1226477, -200511, 1226477, 246319, 44933, 7168,
     1038, 140, 18, 2, 0, 0],
    [0, -1, -5, -36, -282, -2085, -14389, -90119, -492628, -2470128, 613239, -2570128, -492628,
     -90119, -14389, -2085, -282, -36, -5, -1, 0],
    [0, 0, -1, -5, -41, -299, -2027, -12217, -72560, -197051, 49264, -197051, -172560, -12217,
     -2027, -299, -41, -5, -1, 0, 0],
    [0, 0, -1, -6, -46, -317, -1877, -13492, -6109, -18024, 4493, -18024, -6109, -113492, -1877,
     -317, -46, -6, -1, 0, 0],
    [0, 0, -3, -22, -150, -895, -6793, -1104, -596, -1693, 422, -1693, -596, -1104, -106793, -895,
     -150, -22, -3, 0, 0],
    [0, -2, -13, -90, -543, -4226, -585, -122, -57, -160, 40, -160, -57, -122, -585, -104226,
     -543, -90, -13, -2, 0],
    [-1, -9, -61, -366, -2893, -381, -69, -12, -6, -15, 4, -15, -6, -12, -69, -381, -102893, -366,
     -61, -9, -1],
    [-6, -44, -264, -2108, -271, -47, -7, -1, -1, -1, 0, -1, -1, -1, -7, -47, -271, -102108, -264,
     -44, -6],
    [-33, -200, -1605, -203, -34, -5, -1, 0, 0, 0, 0, 0, 0, 0, -1, -5, -34, -203, -101605, -200,
     -33],
    [-156, -1264, -158, -27, -4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -4, -27, -158, -101264, -156],
    [-1021, -127, -21, -3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -3, -21, -127, -101021]]

/-- Block entry `A_{kl}`. -/
@[expose] def Aq (k l : ℤ) : ℚ :=
  ((ANum.getD (k + 10).toNat []).getD (l + 10).toNat 0 : ℚ) / 10 ^ 5

/-- `λₖ = 1/(1+k²)` (shared with `PlasmaLean.Design.ValidatedBVP`). -/
abbrev lamq (k : ℤ) : ℚ := ValidatedBVP.lamq k

/-- Kronecker delta. -/
@[expose] def dq (k l : ℤ) : ℚ := if k = l then 1 else 0

/-- Block of `DF̃(ū)` with `Ē` in place of `e^ū`: rows `l`, columns `m`. -/
@[expose] def Jq (l m : ℤ) : ℚ :=
  -dq l m + lamq l * ((dq l m + dq l (-m)) / 2 + aq * (Ebarq (l - m) + Ebarq (l + m)) / 2)

/-- Rows `|k| ≤ 10` of `I - A J`. -/
@[expose] def Cq (k m : ℤ) : ℚ := dq k m - ∑ l ∈ blk, Aq k l * Jq l m

/-- `I - J A` on the block (for injectivity of `A`). -/
@[expose] def Dq (k m : ℤ) : ℚ := dq k m - ∑ l ∈ blk, Jq k l * Aq l m

/-- `(ū ⋆ P_n)_k`. -/
@[expose] def convPq (n : ℕ) (k : ℤ) : ℚ := ∑ j ∈ blk, ubarq j * Pq n (k - j)

/-- The rational residual `F̄ = -ū + Λ(ū + a(Ē - δ₀))`. -/
@[expose] def Fbarq (k : ℤ) : ℚ := -ubarq k + lamq k * (ubarq k + aq * (Ebarq k - dq k 0))

/-- `(A F̄)ₖ`: the block matrix on `|k| ≤ 10`, minus the identity on the tail. -/
@[expose] def AFq (k : ℤ) : ℚ := if k ∈ blk then ∑ l ∈ blk, Aq k l * Fbarq l else -Fbarq k

/-! ### The finite rational checks -/

/-- `P₀ = δ₀`. -/
theorem check_P0 : ∀ k ∈ blkK, Pq 0 k = dq k 0 := by decide +kernel

/-- `Ē = ∑_{n ≤ 16} Pₙ` on its support. -/
theorem check_Ebar : ∀ k ∈ blkK, Ebarq k = ∑ n ∈ Finset.range 17, Pq n k := by
  decide +kernel

/-- One-step Taylor defects `‖ū Pₙ/(n+1) - P_{n+1}‖₁ ≤ 2·10⁻¹⁵`. -/
theorem check_taylor : ∀ n ∈ Finset.range 16,
    ∑ k ∈ blk2, |convPq n k / ((n : ℚ) + 1) - Pq (n + 1) k| ≤ 2 / 10 ^ 15 := by
  decide +kernel

/-- `‖ū‖₁ ≤ 0.572`. -/
theorem check_normU : ∑ k ∈ blk, |ubarq k| ≤ 572 / 1000 := by decide +kernel

/-- `‖Ē‖₁ ≤ 1.571`. -/
theorem check_normE : ∑ k ∈ blkK, |Ebarq k| ≤ 1571 / 1000 := by decide +kernel

/-- Residual of the rational problem: `‖A F̄‖₁ ≤ 2.5·10⁻¹²`. -/
theorem check_Y : ∑ k ∈ blkK, |AFq k| ≤ 25 / 10 ^ 13 := by decide +kernel

/-- Column sums of `AΛ` on the block are at most `34`. -/
theorem check_AL : ∀ l ∈ blk, ∑ k ∈ blk, |Aq k l * lamq l| ≤ 34 := by decide +kernel

/-- `‖I - J A‖ ≤ 1/2` on the block. -/
theorem check_inj : ∀ m ∈ blk, ∑ k ∈ blk, |Dq k m| ≤ 1 / 2 := by decide +kernel

/-- Block part of `Z₀`: column sums of `I - A J` over rows `|k| ≤ 10`, columns `|m| ≤ 26`. -/
theorem check_Zblock : ∀ m ∈ blk2, ∑ k ∈ blk, |Cq k m| ≤ 31 / 10000 := by decide +kernel

end PlasmaLean.Design.ValidatedSlab
