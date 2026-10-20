/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronExpr
public import PlasmaLean.Design.KamTorusAData

/-!
# Data of the frame and torsion certificate of torus A (KAM route, stage K3, lemma 5)

Untrusted data, produced by `scripts/kam_oracle/frame_emit.py`; every property is proved in
`Design/KamTorusAFrameCheck` and `Design/KamTorusAFrame`.

* A low-degree **surrogate torus** `(R̃, z̃)`: the Fourier modes `0 ≤ k ≤ n₁ = 7`, `|m| ≤ m₁ = 5`
  of torus A rounded to `2^{-32}` (`listA` holds `R̃ − 1`, `listB` holds `z̃`). Its distance to
  torus A (with first `θ`-derivatives) is certified to be `≤ 2.3 × 10⁻⁷`.
* A **zero-mean certificate function** `g` (`listG`): minus the oscillating part of the torsion
  density, so that `T₀ + g ≈ ⟨T₀⟩` pointwise.
* A **positivity multiplier** `s` (`listS`), `s ≈ (D³ W²)^{-1/2}` up to a constant, so that
  `s² · F` is close to a constant and its positivity follows from centre dominance.
* The **expression trees**: nine atoms (the cleared field `16 X = (A₁, A₂)/D_l`, `D_l = 16 D`, and
  their partial derivatives in `R` and `z`) as polynomials in `r = R − 1, z, C = cos 2φ,
  S = sin 2φ`, homogenized with the scale variables `t` (weight of one Fourier factor) and
  `V = 2v`; and the top tree `phiEx = s² F`, `F = 10·16 R³ G + D_l³ W₀² (10 g − 3)`.

All series are stored on the big grid of `Design/KamTorusAData` (`i ≥ N` half grid, mode
`(i − N, j − M)`), restricted to the window `N ≤ i ≤ N + n₁`, `|j − M| ≤ m₁`.
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA.Frame

open PlasmaLean.Certificates.KronExpr

/-- Poloidal window `n₁` of the surrogate data. -/
def n1 : ℕ := 7
/-- Toroidal window `m₁` of the surrogate data. -/
def m1 : ℕ := 5
/-- Coefficient scale: surrogate coefficients are integers over `2^pS`. -/
def pS : ℕ := 32

/-- Window lookup on the big grid: entry `(i, j)` of a row-major window list, zero outside the
window `N ≤ i ≤ N + n₁`, `M − m₁ ≤ j ≤ M + m₁`. -/
def win (l : List ℤ) (i j : ℕ) : ℤ :=
  if N ≤ i ∧ i ≤ N + n1 ∧ M - m1 ≤ j ∧ j ≤ M + m1 then
    l.getD ((i - N) * (2 * m1 + 1) + (j - (M - m1))) 0
  else 0

/-- Sum of a list of trees (left fold). -/
def sumEx : List Ex → Ex
  | [] => .cst 0
  | e :: es => es.foldl .add e

/-- The monomial `k · x_{v₁} ⋯ x_{vₙ}` (left fold). -/
def monoEx (k : ℤ) (vs : List ℕ) : Ex := vs.foldl (fun e i => .mul e (.var i)) (.cst k)

/-- `2^p ×` the cosine coefficients of `R̃ − 1` on the window
(row-major in `(k, m)`, `0 ≤ k ≤ n₁`, `|m| ≤ m₁`). -/
def listA : List ℤ :=
  [0, 0, 0, 0, 0, 2194351, 17490042, 2187345, 205647, 3830, 186, 658, 11770, 37949, 439241,
    161852105, 601771710, 2055061, 231137, 69549, 3972, 310, 454, 18444, 219066, 1961560,
    -9415349, 18789690, 6891419, 847970, 13769, 801, 146, 789, 860, 23016, 398883, -134726,
    -264288, 345223, 141358, 9414, 815, 42, 414, 2054, 3827, -83750, -15913, -101451, 32023,
    14920, 1173, 261, 20, -95, -102, 2259, 1434, -957, -8264, 947, 1765, 331, 51, 4, 23, -19,
    -769, -20, 1861, 1035, -168, 11, 46, 12, 1, -3, 27, 51, 40, -132, 57, 15, -1, 3, 1, 0]

/-- `2^p ×` the sine coefficients of `z̃`. -/
def listB : List ℤ :=
  [0, 0, 0, 0, 0, 0, 17308225, -2123352, 182173, 2460, -306, 444, -11044, 83611, -141875,
    -161938004, 598612886, 408628, -351902, 65830, -2910, 171, -332, -15328, 211664, -1951441,
    4038044, 18356566, -6719834, 781756, 8226, -1170, 118, -729, 6828, -15331, -395134, 539680,
    -307881, -584505, 135082, -7127, 443, 29, -258, 1650, -6354, 62051, 80942, -98430, -9320,
    8960, -1827, 210, -7, 117, -189, -2438, 195, 4594, -15852, 2835, -855, -26, 35, -4, 10, -14,
    575, 340, -1705, 667, 443, -187, 20, -2, 0, -2, -26, -30, -36, 96, 33, -6, -8, 3, -1, 0]

/-- `2^p ×` the cosine coefficients of the zero-mean certificate function `g`. -/
def listG : List ℤ :=
  [0, 0, 0, 0, 0, 0, -549930164, 1275402321, 180941796, 2205028, 11989970, 1919294, 13448983,
    1536270376, -36161828, -15828061668, -940577229, 106804958, 5572174012, 43477217, 18426233,
    4371382, 7364, 66947473, 209379932, -624271548, -1116380468, 511393133, 1689681867,
    324830752, 10929761, 57789056, 1183102, 3092366, 157803632, -57915913, -4238827355,
    8439355285, 121471760, 6743060232, 88203173, 51693761, 11641941, 293224, 12225579, -8856424,
    -157004487, -551883768, -226375099, 61735099, 376979071, 16685722, 121263311, 2681736,
    625451, 3862955, -15710782, -57229513, 396694614, 72333448, -11654451, 69350358, 45945204,
    16882227, 610790, 1244281, -3857293, -20976974, 120170814, -210553281, -11411138, -44454425,
    5793116, 88314689, 3304439, 1089205, 322030, -1256909, -4879473, 30454229, 7463689, -4831428,
    -2671644, 2550982, 9768787, 558968, 1725786, 76833]

/-- `2^p ×` the cosine coefficients of the positivity multiplier `s`. -/
def listS : List ℤ :=
  [0, 0, 0, 0, 0, 4294967296, 120699218, -12794973, -1285464, 0, 0, 0, 0, 875436, 673412,
    -576561177, -2206261505, -8862415, 16584362, 385393, 0, 0, 0, 0, -1805604, 13611535,
    293105402, 313934137, -32462515, -8394044, -2886, 0, 0, 0, 0, 488776, 1919738, -153516636,
    -24558260, 57604529, 1341295, -141156, 0, 0, 0, 0, -688870, 12380844, 33275183, -2162952,
    -10959804, -91983, 281196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Atom `16 D` (the cleared denominator). -/
def atomDl : Ex := sumEx [
  monoEx 16 [4, 4, 4, 4, 4, 5],
  monoEx 8 [1, 1, 3, 4, 4, 4],
  monoEx 8 [1, 1, 1, 2, 4, 4],
  monoEx 32 [0, 4, 4, 4, 4, 5],
  monoEx 16 [0, 1, 2, 4, 4, 4],
  monoEx 16 [0, 0, 4, 4, 4, 5],
  monoEx (-8) [0, 0, 3, 4, 4, 4],
  monoEx (-8) [0, 0, 0, 3, 4, 4],
  monoEx (-8) [0, 0, 0, 1, 2, 4],
  monoEx (-2) [0, 0, 0, 0, 3, 4],
  monoEx (-2) [0, 0, 0, 0, 1, 2]]

/-- Atom `∂_R (16 D)`. -/
def atomDlR : Ex := sumEx [
  monoEx 32 [4, 4, 4, 4, 5],
  monoEx 16 [1, 2, 4, 4, 4],
  monoEx 32 [0, 4, 4, 4, 5],
  monoEx (-16) [0, 3, 4, 4, 4],
  monoEx (-24) [0, 0, 3, 4, 4],
  monoEx (-24) [0, 0, 1, 2, 4],
  monoEx (-8) [0, 0, 0, 3, 4],
  monoEx (-8) [0, 0, 0, 1, 2]]

/-- Atom `∂_z (16 D)`. -/
def atomDlz : Ex := sumEx [
  monoEx 16 [1, 3, 4, 4, 4],
  monoEx 24 [1, 1, 2, 4, 4],
  monoEx 16 [0, 2, 4, 4, 4],
  monoEx (-8) [0, 0, 0, 2, 4],
  monoEx (-2) [0, 0, 0, 0, 2]]

/-- Atom `16 X̃_R = 8 R Ps` (numerator of `dR/dφ`). -/
def atomA1 : Ex := sumEx [
  monoEx 8 [1, 3, 4, 4, 4, 4, 4],
  monoEx 8 [1, 1, 2, 4, 4, 4, 4],
  monoEx (-8) [1, 1, 1, 3, 4, 4, 4],
  monoEx 8 [0, 2, 4, 4, 4, 4, 4],
  monoEx 8 [0, 1, 1, 2, 4, 4, 4],
  monoEx (-8) [0, 1, 1, 1, 3, 4, 4],
  monoEx 20 [0, 0, 2, 4, 4, 4, 4],
  monoEx (-20) [0, 0, 1, 3, 4, 4, 4],
  monoEx 20 [0, 0, 0, 2, 4, 4, 4],
  monoEx (-20) [0, 0, 0, 1, 3, 4, 4],
  monoEx 10 [0, 0, 0, 0, 2, 4, 4],
  monoEx (-10) [0, 0, 0, 0, 1, 3, 4],
  monoEx 2 [0, 0, 0, 0, 0, 2, 4],
  monoEx (-2) [0, 0, 0, 0, 0, 1, 3]]

/-- Atom `∂_R (8 R Ps)`. -/
def atomA1R : Ex := sumEx [
  monoEx 8 [2, 4, 4, 4, 4, 4],
  monoEx 8 [1, 1, 2, 4, 4, 4],
  monoEx (-8) [1, 1, 1, 3, 4, 4],
  monoEx 40 [0, 2, 4, 4, 4, 4],
  monoEx (-40) [0, 1, 3, 4, 4, 4],
  monoEx 60 [0, 0, 2, 4, 4, 4],
  monoEx (-60) [0, 0, 1, 3, 4, 4],
  monoEx 40 [0, 0, 0, 2, 4, 4],
  monoEx (-40) [0, 0, 0, 1, 3, 4],
  monoEx 10 [0, 0, 0, 0, 2, 4],
  monoEx (-10) [0, 0, 0, 0, 1, 3]]

/-- Atom `∂_z (8 R Ps)`. -/
def atomA1z : Ex := sumEx [
  monoEx 8 [3, 4, 4, 4, 4, 4],
  monoEx 16 [1, 2, 4, 4, 4, 4],
  monoEx (-24) [1, 1, 3, 4, 4, 4],
  monoEx 16 [0, 1, 2, 4, 4, 4],
  monoEx (-24) [0, 1, 1, 3, 4, 4],
  monoEx (-20) [0, 0, 3, 4, 4, 4],
  monoEx (-20) [0, 0, 0, 3, 4, 4],
  monoEx (-10) [0, 0, 0, 0, 3, 4],
  monoEx (-2) [0, 0, 0, 0, 0, 3]]

/-- Atom `16 X̃_z = 4 R² Pz` (numerator of `dz/dφ`). -/
def atomA2 : Ex := sumEx [
  monoEx (-8) [1, 2, 4, 4, 4, 4, 4],
  monoEx 12 [1, 1, 3, 4, 4, 4, 4],
  monoEx 8 [0, 3, 4, 4, 4, 4, 4],
  monoEx (-16) [0, 1, 2, 4, 4, 4, 4],
  monoEx 24 [0, 1, 1, 3, 4, 4, 4],
  monoEx 16 [0, 0, 3, 4, 4, 4, 4],
  monoEx (-8) [0, 0, 1, 2, 4, 4, 4],
  monoEx 12 [0, 0, 1, 1, 3, 4, 4],
  monoEx 4 [0, 0, 0, 3, 4, 4, 4],
  monoEx (-9) [0, 0, 0, 0, 3, 4, 4],
  monoEx (-6) [0, 0, 0, 0, 0, 3, 4],
  monoEx (-1) [0, 0, 0, 0, 0, 0, 3]]

/-- Atom `∂_R (4 R² Pz)`. -/
def atomA2R : Ex := sumEx [
  monoEx 8 [3, 4, 4, 4, 4, 4],
  monoEx (-16) [1, 2, 4, 4, 4, 4],
  monoEx 24 [1, 1, 3, 4, 4, 4],
  monoEx 32 [0, 3, 4, 4, 4, 4],
  monoEx (-16) [0, 1, 2, 4, 4, 4],
  monoEx 24 [0, 1, 1, 3, 4, 4],
  monoEx 12 [0, 0, 3, 4, 4, 4],
  monoEx (-36) [0, 0, 0, 3, 4, 4],
  monoEx (-30) [0, 0, 0, 0, 3, 4],
  monoEx (-6) [0, 0, 0, 0, 0, 3]]

/-- Atom `∂_z (4 R² Pz)`. -/
def atomA2z : Ex := sumEx [
  monoEx (-8) [2, 4, 4, 4, 4, 4],
  monoEx 24 [1, 3, 4, 4, 4, 4],
  monoEx (-16) [0, 2, 4, 4, 4, 4],
  monoEx 48 [0, 1, 3, 4, 4, 4],
  monoEx (-8) [0, 0, 2, 4, 4, 4],
  monoEx 24 [0, 0, 1, 3, 4, 4]]

/-- `2^pS ×` the coefficient grid of `R̃ − 1` (big-grid indices). -/
def tA (i j : ℕ) : ℤ := win listA i j
/-- `2^pS ×` the coefficient grid of `z̃`. -/
def tB (i j : ℕ) : ℤ := win listB i j
/-- `2^pS ×` the coefficient grid of `g`. -/
def tG (i j : ℕ) : ℤ := win listG i j
/-- `2^pS ×` the coefficient grid of `s`. -/
def tS (i j : ℕ) : ℤ := win listS i j

/-! ## The top tree

Variables: `0 … 8` the atoms `D_l, ∂_R D_l, ∂_z D_l, A₁, ∂_R A₁, ∂_z A₁, A₂, ∂_R A₂, ∂_z A₂`,
`9 r = R − 1`, `10 z`, `11 a = ∂_θ R`, `12 b = ∂_θ z`, `13 y = g`, `14 s`, `15 t`, `16 V`. -/

/-- `D_l² (X − DX·V₀)` for one component:
`D_l A − ((D_l A_R − A D_{l,R}) r + (D_l A_z − A D_{l,z}) z)`. -/
def eY (A AR Az : Ex) : Ex :=
  .sub (.mul (.var 0) A)
    (.add (.mul (.sub (.mul (.var 0) AR) (.mul A (.var 1))) (.var 9))
      (.mul (.sub (.mul (.var 0) Az) (.mul A (.var 2))) (.var 10)))

/-- `G = Y₁ z − Y₂ r`, the cross product `(D_l² (X − DX·V₀)) × V₀`. -/
def eG : Ex :=
  .sub (.mul (eY (.var 3) (.var 4) (.var 5)) (.var 10))
    (.mul (eY (.var 6) (.var 7) (.var 8)) (.var 9))

/-- `W₀ = a z − b r = ∂_θK × V₀` (minus the winding rate). -/
def eW0 : Ex := .sub (.mul (.var 11) (.var 10)) (.mul (.var 12) (.var 9))

/-- `R = r + t`. -/
def eR : Ex := .add (.var 9) (.var 15)

/-- The homogenizing factor `t⁵ V`. -/
def eT5V : Ex :=
  .mul (.mul (.mul (.mul (.mul (.var 15) (.var 15)) (.var 15)) (.var 15)) (.var 15)) (.var 16)

/-- `F = 160 R³ G t⁵V + D_l³ W₀² (10 g − 3 t)` (`= 10 D_l³ W₀² (T₀ + g − 3/10)` at `t = V = 1`). -/
def eF : Ex :=
  .add (.mul (.mul (.mul (.cst 160) (.mul (.mul eR eR) eR)) eG) eT5V)
    (.mul (.mul (.mul (.mul (.var 0) (.var 0)) (.var 0)) (.mul eW0 eW0))
      (.sub (.mul (.cst 10) (.var 13)) (.mul (.cst 3) (.var 15))))

/-- The certified expression `s² F`. -/
def phiEx : Ex := .mul (.mul (.var 14) (.var 14)) eF

/-! ## Weights `(t-degree, v-degree, phase)` -/

/-- Weights of the base variables `r, z, C, S, t, V`. -/
def WB : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | 1 => (1, 0, 1)
  | 2 => (0, 1, 3)
  | 3 => (0, 1, 0)
  | 4 => (1, 0, 0)
  | 5 => (0, 1, 0)
  | _ => (0, 0, 0)

/-- Weights of the variables of the top tree (atom weights as computed by `Ex.wt`). -/
def WT : ℕ → ℕ × ℕ × ℕ
  | 0 => (5, 1, 0)
  | 1 => (4, 1, 0)
  | 2 => (4, 1, 1)
  | 3 => (6, 1, 1)
  | 4 => (5, 1, 3)
  | 5 => (5, 1, 0)
  | 6 => (6, 1, 0)
  | 7 => (5, 1, 0)
  | 8 => (5, 1, 3)
  | 9 => (1, 0, 0)
  | 10 => (1, 0, 1)
  | 11 => (1, 0, 3)
  | 12 => (1, 0, 0)
  | 13 => (1, 0, 0)
  | 14 => (1, 0, 0)
  | 15 => (1, 0, 0)
  | 16 => (0, 1, 0)
  | _ => (0, 0, 0)

/-- The atoms, indexed as the top-tree variables `0 … 8`. -/
def atom : ℕ → Ex
  | 0 => atomDl
  | 1 => atomDlR
  | 2 => atomDlz
  | 3 => atomA1
  | 4 => atomA1R
  | 5 => atomA1z
  | 6 => atomA2
  | 7 => atomA2R
  | 8 => atomA2z
  | _ => .cst 0

end PlasmaLean.Design.KamTorusA.Frame
