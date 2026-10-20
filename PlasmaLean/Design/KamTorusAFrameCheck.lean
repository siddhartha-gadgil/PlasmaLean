/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAFrameData
public import PlasmaLean.Design.KamTorusAForms

/-!
# Kernel computations for the torsion certificate of torus A

Every theorem here is a single kernel evaluation (`decide +kernel`) of exact integer or rational
arithmetic on the data of `Design/KamTorusAFrameData` and `Design/KamTorusAData`:

* the weights and degree boxes of the expression trees (`wt_atoms`, `wt_phiEx`, `box_phiEx`);
* the distance from the surrogate torus to torus A (`close_R`, `close_Z`, `close_Rθ`, `close_Zθ`):
  `ℓ¹` norms of coefficient differences, i.e. sup-norm bounds;
* `ℓ¹` bounds of `g` and `s` (`l1_tG`, `l1_tS`) and the zero mean of `g` (`tG_centre`);
* the **Kronecker certificate** `check_phi`: the integer polynomial `−Φ̂` representing `s² F` on the
  surrogate torus has centre coefficient `c0Phi` and `‖−Φ̂ − c0Phi · u^{154} v^{113}‖₁ ≤
  (c0Phi − 0.9 κ)`, `κ = σ₁²² · 8`, with the a priori bound `apriori_phi` that makes the digit sum
  exact (`b = 752` bits per slot, `W = 309`, `2^17` slots);
* the **perturbation majorant** `dmaj_phi`: moving from the surrogate torus to torus A changes
  `s² F` by at most `0.3`.

The semantic consequences are drawn in `Design/KamTorusAFrame`.
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA.Frame

open PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.Kron2

/-! ## Variable assignments -/

/-- Assignment of the base variables `r, z, C, S, t, V` (indices `0 … 5`). -/
def envB {α : Type*} [Zero α] (r z C S t V : α) : ℕ → α
  | 0 => r
  | 1 => z
  | 2 => C
  | 3 => S
  | 4 => t
  | 5 => V
  | _ => 0

/-- Assignment of the top-tree variables: atoms `A 0 … A 8`, then `r, z, a, b, y, s, t, V`. -/
def envT {α : Type*} [Zero α] (A : ℕ → α) (r z a b y s t V : α) : ℕ → α
  | 0 => A 0
  | 1 => A 1
  | 2 => A 2
  | 3 => A 3
  | 4 => A 4
  | 5 => A 5
  | 6 => A 6
  | 7 => A 7
  | 8 => A 8
  | 9 => r
  | 10 => z
  | 11 => a
  | 12 => b
  | 13 => y
  | 14 => s
  | 15 => t
  | 16 => V
  | _ => 0

/-! ## Compact grids -/

/-- The scale `σ₁ = 2^{pS+1}` of the compact grid polynomials. -/
def sig1 : ℕ := 2 ^ (pS + 1)

/-- Restriction of a big-grid function to the window, in compact coordinates
`(i', j') ∈ [0, 2n₁] × [0, 2m₁]`. -/
def cpt (G : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := G (i + (N - n1)) (j + (M - m1))

/-- Big-grid cosine symmetrization `c + c ∘ refl`. -/
def symC (c : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := c i j + c (2 * N - i) (2 * M - j)
/-- Big-grid sine symmetrization `c − c ∘ refl`. -/
def symS (c : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := c i j - c (2 * N - i) (2 * M - j)

/-- Compact grid of `r̂ = t r̃`. -/
def gRc (i j : ℕ) : ℤ := cpt (symC tA) i j
/-- Compact grid of `ẑ = t (i z̃)`. -/
def gZc (i j : ℕ) : ℤ := cpt (symS tB) i j
/-- Compact grid of `â = −i t ∂_θ R̃`. -/
def gAc (i j : ℕ) : ℤ := ((i : ℤ) - n1) * gRc i j
/-- Compact grid of `b̂ = t ∂_θ z̃`. -/
def gBc (i j : ℕ) : ℤ := ((i : ℤ) - n1) * gZc i j
/-- Compact grid of `ŷ = t g`. -/
def gYc (i j : ℕ) : ℤ := cpt (symC tG) i j
/-- Compact grid of `ŝ = t s`. -/
def gSc (i j : ℕ) : ℤ := cpt (symC tS) i j

/-- `∑ |g i j|` over the compact grid (computable). -/
def gridL1c (g : ℕ → ℕ → ℤ) : ℕ :=
  rsum (fun j => rsum (fun i => (g i j).natAbs) (2 * n1 + 1)) (2 * m1 + 1)

/-- `∑_{i < n} f i · 2^{b i}` (compact rows). -/
def packRow1 (b : ℕ) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => packRow1 b f n + f n * ((2 ^ (b * n) : ℕ) : ℤ)

/-- Kronecker image of a compact grid polynomial:
`∑_{j < m} (∑_{i ≤ 2n₁} g i j 2^{b i}) 2^{b W j}`. -/
def packGrid1 (b W : ℕ) (g : ℕ → ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => packGrid1 b W g m + packRow1 b (fun i => g i m) (2 * n1 + 1) *
      ((2 ^ (b * W * m) : ℕ) : ℤ)

/-- Kronecker image of `t = σ₁ u^{n₁} v^{m₁}`. -/
def tInt (b W : ℕ) : ℤ := ((sig1 * 2 ^ (b * (n1 + W * m1)) : ℕ) : ℤ)

/-- Kronecker images of the base variables. -/
def baseInt (b W : ℕ) : ℕ → ℤ :=
  envB (packGrid1 b W gRc (2 * m1 + 1)) (packGrid1 b W gZc (2 * m1 + 1))
    (((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1) ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) (tInt b W)
    ((2 * 2 ^ (b * W) : ℕ) : ℤ)

/-- Kronecker images of the top-tree variables. -/
def topInt (b W : ℕ) : ℕ → ℤ :=
  envT (fun k => Ex.evH WB (baseInt b W) (atom k)) (packGrid1 b W gRc (2 * m1 + 1))
    (packGrid1 b W gZc (2 * m1 + 1)) (packGrid1 b W gAc (2 * m1 + 1))
    (packGrid1 b W gBc (2 * m1 + 1)) (packGrid1 b W gYc (2 * m1 + 1))
    (packGrid1 b W gSc (2 * m1 + 1)) (tInt b W) ((2 * 2 ^ (b * W) : ℕ) : ℤ)

/-- Kronecker image of `Φ̂` (the phased integer polynomial of `s² F`). -/
def phiInt (b W : ℕ) : ℤ := Ex.evH WT (topInt b W) phiEx

/-! ## Degree boxes, `ℓ¹` and real bounds of the variables -/

/-- Degree boxes of the base polynomials. -/
def BxB : ℕ → ℕ × ℕ := envB (2 * n1, 2 * m1) (2 * n1, 2 * m1) (0, 2) (0, 2) (n1, m1) (0, 1)
/-- Degree boxes of the top-tree variables. -/
def BxT : ℕ → ℕ × ℕ :=
  envT (fun k => Ex.box BxB (atom k)) (2 * n1, 2 * m1) (2 * n1, 2 * m1) (2 * n1, 2 * m1)
    (2 * n1, 2 * m1) (2 * n1, 2 * m1) (2 * n1, 2 * m1) (n1, m1) (0, 1)

/-- `ℓ¹` bounds of the base polynomials. -/
def LB : ℕ → ℕ := envB (gridL1c gRc) (gridL1c gZc) 2 2 sig1 2
/-- `ℓ¹` bounds of the top-tree variables. -/
def LT : ℕ → ℕ :=
  envT (fun k => Ex.majN LB (atom k)) (gridL1c gRc) (gridL1c gZc) (gridL1c gAc) (gridL1c gBc)
    (gridL1c gYc) (gridL1c gSc) sig1 2

/-- Sup bounds of the base variables on torus A: `|r|, |z| ≤ 0.19`, `|C|, |S| ≤ 1`, `t = V = 1`. -/
def BB : ℕ → ℚ := envB (19 / 100) (19 / 100) 1 1 1 1
/-- Distances surrogate–torus A of the base variables. -/
def EB : ℕ → ℚ := envB (73 / 10 ^ 9) (63 / 10 ^ 9) 0 0 0 0
/-- Sup bounds of the top-tree variables on torus A (`|∂_θ R|, |∂_θ z| ≤ 1/5`, `|g| ≤ 12.446`,
`|s| ≤ 1.91`). -/
def BT : ℕ → ℚ :=
  envT (fun k => Ex.majQ BB (atom k)) (19 / 100) (19 / 100) (1 / 5) (1 / 5) (6223 / 500)
    (191 / 100) 1 1
/-- Distances surrogate–torus A of the top-tree variables. -/
def ET : ℕ → ℚ :=
  envT (fun k => Ex.dmajQ BB EB (atom k)) (73 / 10 ^ 9) (63 / 10 ^ 9) (223 / 10 ^ 9)
    (217 / 10 ^ 9) 0 0 0 0

/-! ## Kernel checks -/

/-- `2^n` as `(2^⌊n/2⌋)² 2^(n mod 2)` (the kernel caps the size of a single `Nat.pow`). -/
def pow2F (n : ℕ) : ℕ := 2 ^ (n / 2) * 2 ^ (n / 2) * 2 ^ (n % 2)

/-- `pow2F n = 2^n`. -/
theorem pow2F_eq (n : ℕ) : pow2F n = 2 ^ n := by
  rw [pow2F, ← pow_add, ← pow_add]; congr 1; omega

/-- The atoms are homogeneous, with the weights recorded in `WT`. -/
theorem wt_atoms : ∀ k, k < 9 → Ex.wt WB (atom k) = some (WT k) := by
  intro k hk
  interval_cases k <;> decide +kernel

/-- `Φ̂` is homogeneous of weight `(22, 3, 2)`: `evalC Φ̂ = T²² (2v)³ i² · (s² F)`. -/
theorem wt_phiEx : Ex.wt WT phiEx = some (22, 3, 2) := by decide +kernel

/-- The degree box of `Φ̂`. -/
theorem box_phiEx : Ex.box BxT phiEx = (308, 226) := by decide +kernel

set_option linter.style.longLine false in
/-- Oracle value of `−` the centre coefficient of `Φ̂` (at `u^{154} v^{113}`); any value is
sound. -/
def c0Phi : ℕ := 3077192682580859586801559043575406395130723677647462311173987540587159665675590777962055353550371932884471232629497268456631030140752486256142442020338041336674951530005874311339465642899646778656146074148669960365206112

/-- A priori bound: `‖Φ̂‖₁ + c0Phi < 2^751`, so the digit sums are exact. -/
theorem apriori_phi : Ex.majN LT phiEx + c0Phi < 2 ^ (752 - 1) := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The Kronecker certificate.** `10 ‖−Φ̂ − c0Phi u^{154} v^{113}‖₁ + 9 σ₁²² 8 ≤ 10 c0Phi`, i.e.
`s² F ≥ 0.9` on the whole surrogate torus. -/
theorem check_phi :
    10 * l1Kron 752 17
        (-phiInt 752 309 - (c0Phi : ℤ) * ((pow2F (752 * (154 + 309 * 113)) : ℕ) : ℤ)) +
      9 * (sig1 ^ 22 * 8) ≤ 10 * c0Phi := by
  decide +kernel

/-- `∑ |cA − 2^{58} tA − 2^{90} δ_{centre}| ≤ 7.3 × 10⁻⁸ · 2^{90}`, i.e.
`|R − (1 + r̃)| ≤ 7.3 × 10⁻⁸`. -/
theorem close_R :
    10 ^ 9 * gridL1 (fun i j => cA i j - 2 ^ (P - pS) * tA i j -
      (if i = N ∧ j = M then 2 ^ P else 0)) ≤ 73 * 2 ^ P := by
  decide +kernel

/-- `|z − z̃| ≤ 6.3 × 10⁻⁸`. -/
theorem close_Z : 10 ^ 9 * gridL1 (fun i j => cB i j - 2 ^ (P - pS) * tB i j) ≤ 63 * 2 ^ P := by
  decide +kernel

/-- `|∂_θ R − ∂_θ R̃| ≤ 2.23 × 10⁻⁷`. -/
theorem close_Rθ :
    10 ^ 9 * gridL1 (fun i j => ((i : ℤ) - N) * (cA i j - 2 ^ (P - pS) * tA i j -
      (if i = N ∧ j = M then 2 ^ P else 0))) ≤ 223 * 2 ^ P := by
  decide +kernel

/-- `|∂_θ z − ∂_θ z̃| ≤ 2.17 × 10⁻⁷`. -/
theorem close_Zθ :
    10 ^ 9 * gridL1 (fun i j => ((i : ℤ) - N) * (cB i j - 2 ^ (P - pS) * tB i j)) ≤
      217 * 2 ^ P := by
  decide +kernel

/-- `‖g‖_∞ ≤ ∑ |ĝ| ≤ 12.446`. -/
theorem l1_tG : 500 * gridL1 tG ≤ 6223 * 2 ^ pS := by decide +kernel

/-- `‖s‖_∞ ≤ ∑ |ŝ| ≤ 1.91`. -/
theorem l1_tS : 100 * gridL1 tS ≤ 191 * 2 ^ pS := by decide +kernel

/-- `g` has zero mean: its constant coefficient vanishes. -/
theorem tG_centre : tG N M = 0 := by decide +kernel

/-- **Perturbation majorant**: `|s² F(torus A) − s² F(surrogate)| ≤ 0.3`. -/
theorem dmaj_phi : Ex.dmajQ BT ET phiEx ≤ 3 / 10 := by decide +kernel

end PlasmaLean.Design.KamTorusA.Frame
