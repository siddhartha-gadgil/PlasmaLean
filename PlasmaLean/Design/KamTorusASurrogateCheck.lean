/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusASurrogateData
public import PlasmaLean.Design.KamTorusAFrameCheck
public import PlasmaLean.Design.KamTorusAWeightedCheck

/-!
# Kernel computations for the surrogate-torus certificates of torus A

Every theorem here is a single kernel evaluation (`decide +kernel`) of exact integer arithmetic on
the data of `Design/KamTorusASurrogateData`, `Design/KamTorusAFrameData` (the surrogate torus,
modes `0 ≤ k ≤ 7`, `|m| ≤ 5`, coefficients over `2^32`) and `Design/KamTorusAData` (torus A):

* the weights, degree boxes and a priori `ℓ¹` bounds of the trees `treeD`, `treeP`, `treeW`;
* the separable weighted digit sums (`wl1KronP`, weights `74315^s 2^{16(K − s)}`, i.e.
  `e^{r_A s}` with `e^{r_A} ≤ 74315/2^16`) of the Kronecker images of
  - `q̂ D̂³ Ŵ₀² − 512 t^{21} V³` (`b = 720`, `W = 295`, centre `(147, 108)`): `wcheck4`;
  - `(t + r̂)³ P̂ q̂` (`b = 560`, `W = 225`, centre `(112, 82)`): `wcheck5`, and its centre digit
    `digit5`;
  - `Ŵ₀ − c0W u^{14} v^{10}` (`b = 80`, `W = 29`): `wcheckW`; `q̂` (`b = 96`, `W = 29`): `wcheckQ`;
* the weighted distances from the surrogate torus to torus A (big grid `b = 128`, `W = 65`):
  `wcheck_du`, `wcheck_dz`, `wcheck_da`, `wcheck_db`.

The predictions come from the untrusted oracle `scripts/kam_oracle/surrogate_emit.py`. The
semantic consequences are drawn in `Design/KamTorusASurrogate`.
-/

@[expose] public section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.Kron2 PlasmaLean.Design.KamTorusA
  PlasmaLean.Design.KamTorusA.Frame

/-! ## Variables, weights, boxes -/

/-- Assignment of the variables `r, z, C, S, t, V, a, b` (indices `0 … 7`). -/
def envS {α : Type*} [Zero α] (r z C S t V a b : α) : ℕ → α
  | 0 => r
  | 1 => z
  | 2 => C
  | 3 => S
  | 4 => t
  | 5 => V
  | 6 => a
  | 7 => b
  | _ => 0

/-- Weights `(t-degree, v-degree, phase)` of the variables. -/
def WS : ℕ → ℕ × ℕ × ℕ
  | 0 => (1, 0, 0)
  | 1 => (1, 0, 1)
  | 2 => (0, 1, 3)
  | 3 => (0, 1, 0)
  | 4 => (1, 0, 0)
  | 5 => (0, 1, 0)
  | 6 => (1, 0, 3)
  | 7 => (1, 0, 0)
  | _ => (0, 0, 0)

/-- Degree boxes of the variable polynomials. -/
def BxS : ℕ → ℕ × ℕ :=
  envS (2 * n1, 2 * m1) (2 * n1, 2 * m1) (0, 2) (0, 2) (n1, m1) (0, 1) (2 * n1, 2 * m1)
    (2 * n1, 2 * m1)

/-- `ℓ¹` bounds of the variable polynomials. -/
def LS : ℕ → ℕ :=
  envS (gridL1c gRc) (gridL1c gZc) 2 2 sig1 2 (gridL1c gAc) (gridL1c gBc)

/-! ## The `q` grid -/

/-- `∑_{i < n} f i · 2^{b i}` (rows of the `q` grid). -/
def packRowQ (b : ℕ) (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => packRowQ b f n + f n * ((2 ^ (b * n) : ℕ) : ℤ)

/-- Kronecker image of a grid polynomial of width `29`:
`∑_{j < m} (∑_{i ≤ 28} g i j 2^{b i}) 2^{b W j}`. -/
def packGridQ (b W : ℕ) (g : ℕ → ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | m + 1 => packGridQ b W g m + packRowQ b (fun i => g i m) 29 * ((2 ^ (b * W * m) : ℕ) : ℤ)

/-- `∑ |g i j|` over the `29 × 21` grid. -/
def gridL1Q (g : ℕ → ℕ → ℤ) : ℕ := rsum (fun j => rsum (fun i => (g i j).natAbs) 29) 21

/-! ## Kronecker images -/

/-- Kronecker images of the variables `r̂, ẑ, Ĉ = v² − 1, Ŝ = v² + 1, t̂, V̂ = 2v, â, b̂`. -/
def bInt (b W : ℕ) : ℕ → ℤ :=
  envS (packGrid1 b W gRc (2 * m1 + 1)) (packGrid1 b W gZc (2 * m1 + 1))
    (((2 ^ (b * (2 * W)) : ℕ) : ℤ) - 1) ((2 ^ (b * (2 * W)) + 1 : ℕ) : ℤ) (tInt b W)
    ((2 * 2 ^ (b * W) : ℕ) : ℤ) (packGrid1 b W gAc (2 * m1 + 1)) (packGrid1 b W gBc (2 * m1 + 1))

/-- Kronecker image of `q̂`. -/
def qInt (b W : ℕ) : ℤ := packGridQ b W gQc 21

/-- Kronecker image of `q̂ D̂³ Ŵ₀² − 512 t^{21} V³`. -/
def int4 (b W : ℕ) : ℤ :=
  qInt b W * Ex.evH WS (bInt b W) treeD ^ 3 * Ex.evH WS (bInt b W) treeW ^ 2 -
    512 * tInt b W ^ 21 * ((2 * 2 ^ (b * W) : ℕ) : ℤ) ^ 3

/-- Kronecker image of `(t + r̂)³ P̂ q̂`. -/
def int5 (b W : ℕ) : ℤ :=
  (tInt b W + packGrid1 b W gRc (2 * m1 + 1)) ^ 3 * Ex.evH WS (bInt b W) treeP * qInt b W

/-- Kronecker image of `Ŵ₀ − c0W u^{14} v^{10}`. -/
def intW (b W : ℕ) : ℤ :=
  Ex.evH WS (bInt b W) treeW - c0W * ((2 ^ (b * (14 + W * 10)) : ℕ) : ℤ)

/-! ## Weights, boxes and a priori bounds -/

/-- `8 D̂` is homogeneous of weight `(5, 1, 0)`. -/
theorem wt_treeD : Ex.wt WS treeD = some (5, 1, 0) := by decide +kernel

/-- `128 P̂` is homogeneous of weight `(11, 2, 0)`. -/
theorem wt_treeP : Ex.wt WS treeP = some (11, 2, 0) := by decide +kernel

/-- `Ŵ₀` is homogeneous of weight `(2, 0, 0)`. -/
theorem wt_treeW : Ex.wt WS treeW = some (2, 0, 0) := by decide +kernel

/-- Degree box of `8 D̂`. -/
theorem box_treeD : Ex.box BxS treeD = (70, 52) := by decide +kernel

/-- Degree box of `128 P̂`. -/
theorem box_treeP : Ex.box BxS treeP = (154, 114) := by decide +kernel

/-- Degree box of `Ŵ₀`. -/
theorem box_treeW : Ex.box BxS treeW = (28, 20) := by decide +kernel

/-- A priori bound for `q̂ D̂³ Ŵ₀² − 512 t^{21} V³`: below `2^719`. -/
theorem apriori4 :
    gridL1Q gQc * Ex.majN LS treeD ^ 3 * Ex.majN LS treeW ^ 2 + 512 * (sig1 ^ 21 * 2 ^ 3) <
      2 ^ (720 - 1) := by
  decide +kernel

/-- A priori bound for `(t + r̂)³ P̂ q̂`: below `2^559`. -/
theorem apriori5 : (sig1 + gridL1c gRc) ^ 3 * Ex.majN LS treeP * gridL1Q gQc < 2 ^ (560 - 1) := by
  decide +kernel

/-- A priori bound for `Ŵ₀ − c0W u^{14} v^{10}`: below `2^79`. -/
theorem aprioriW : Ex.majN LS treeW + c0W.natAbs < 2 ^ (80 - 1) := by decide +kernel

/-- A priori bound for `q̂`: below `2^95`. -/
theorem aprioriQ : gridL1Q gQc < 2 ^ (96 - 1) := by decide +kernel

/-! ## Weighted digit sums -/

set_option maxRecDepth 100000 in
/-- **`‖q D³ W₀² − 1‖_{r_A} ≤ 5.13 × 10⁻⁶`** on the surrogate torus (scaled by
`4096 σ₁^{21} 2^{16·255}`). -/
theorem wcheck4 :
    wl1KronP 720 295 9 8 (216 + 1) (fun i => kwtS 74315 16 147 (ndist i 147))
        (fun j => kwtS 74315 16 108 (ndist j 108)) (int4 720 295) * 10 ^ 8 ≤
      513 * (4096 * sig1 ^ 21 * 2 ^ (16 * (147 + 108))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖R³ P q‖_{r_A} ≤ 19.655`** on the surrogate torus (scaled by `512 σ₁^{16} 2^{16·194}`). -/
theorem wcheck5 :
    wl1KronP 560 225 8 8 (164 + 1) (fun i => kwtS 74315 16 112 (ndist i 112))
        (fun j => kwtS 74315 16 82 (ndist j 82)) (int5 560 225) * 1000 ≤
      19655 * (512 * sig1 ^ 16 * 2 ^ (16 * (112 + 82))) := by
  decide +kernel

/-- **The centre digit** of the Kronecker image of `(t + r̂)³ P̂ q̂` (slot `112 + 225 · 82`). -/
theorem digit5 :
    ((int5 560 225 + offs (2 ^ (560 - 1)) 560 16).toNat >>> (560 * (112 + 225 * 82))) %
      2 ^ 560 = e0T := by
  decide +kernel

/-- `w_S = c0W/σ₁² ∈ [−0.01814, −0.01813]`. -/
theorem check_wS :
    -1814 * (sig1 : ℤ) ^ 2 ≤ c0W * 100000 ∧ c0W * 100000 ≤ -1813 * (sig1 : ℤ) ^ 2 := by
  decide +kernel

/-- The average: `0.3986 ≤ (e0T − 2^559) / (512 σ₁^{16})`. -/
theorem check_avg : 3986 * (512 * (sig1 : ℤ) ^ 16) ≤ ((e0T : ℤ) - 2 ^ (560 - 1)) * 10000 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖W₀ − w_S‖_{r_A} ≤ 0.004078`** on the surrogate torus. -/
theorem wcheckW :
    wl1KronP 80 29 5 5 (20 + 1) (fun i => kwtS 74315 16 14 (ndist i 14))
        (fun j => kwtS 74315 16 10 (ndist j 10)) (intW 80 29) * 10 ^ 6 ≤
      4078 * (sig1 ^ 2 * 2 ^ (16 * (14 + 10))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖q‖_{r_A} ≤ 16162`**. -/
theorem wcheckQ :
    wl1KronP 96 29 5 5 (20 + 1) (fun i => kwtS 74315 16 14 (ndist i 14))
        (fun j => kwtS 74315 16 10 (ndist j 10)) (qInt 96 29) * 10 ≤
      161620 * (sig1 ^ 2 * 2 ^ (16 * (14 + 10))) := by
  decide +kernel

/-! ## Distances to torus A (big grid) -/

/-- Big-grid weight `(i − N) G i j`. -/
def wθ (G : ℕ → ℕ → ℤ) (i j : ℕ) : ℤ := ((i : ℤ) - N) * G i j

/-- Kronecker image of `R̂ − t − 2^{58} R̃̂` (big grid, `b = 128`, `W = 65`). -/
def distU : ℤ :=
  packGrid 128 65 gR (2 * M + 1) - tGrid - 2 ^ 58 * packGrid 128 65 (symC tA) (2 * M + 1)
/-- Kronecker image of `Ẑ − 2^{58} Z̃̂`. -/
def distZ : ℤ := packGrid 128 65 gZ (2 * M + 1) - 2 ^ 58 * packGrid 128 65 (symS tB) (2 * M + 1)
/-- Kronecker image of `R̂_θ − 2^{58} R̃̂_θ`. -/
def distA : ℤ :=
  packGrid 128 65 gRth (2 * M + 1) - 2 ^ 58 * packGrid 128 65 (wθ (symC tA)) (2 * M + 1)
/-- Kronecker image of `Ẑ_θ − 2^{58} Z̃̂_θ`. -/
def distB : ℤ :=
  packGrid 128 65 gZth (2 * M + 1) - 2 ^ 58 * packGrid 128 65 (wθ (symS tB)) (2 * M + 1)

/-- A priori bounds of the distance polynomials: below `2^127`. -/
theorem apriori_dist :
    gridL1 gR + sig + 2 ^ 58 * gridL1 (symC tA) < 2 ^ (128 - 1) ∧
      gridL1 gZ + 2 ^ 58 * gridL1 (symS tB) < 2 ^ (128 - 1) ∧
      gridL1 gRth + 2 ^ 58 * gridL1 (wθ (symC tA)) < 2 ^ (128 - 1) ∧
      gridL1 gZth + 2 ^ 58 * gridL1 (wθ (symS tB)) < 2 ^ (128 - 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖u₀ − u_S‖_{r_A} ≤ 2.2 × 10⁻⁷`**. -/
theorem wcheck_du :
    wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) distU * 10 ^ 8 ≤
      22 * (sig * 2 ^ (16 * (32 + 22))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖z₀ − z_S‖_{r_A} ≤ 2.2 × 10⁻⁷`**. -/
theorem wcheck_dz :
    wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) distZ * 10 ^ 8 ≤
      22 * (sig * 2 ^ (16 * (32 + 22))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖∂_θ u₀ − ∂_θ u_S‖_{r_A} ≤ 7.7 × 10⁻⁷`**. -/
theorem wcheck_da :
    wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) distA * 10 ^ 8 ≤
      77 * (sig * 2 ^ (16 * (32 + 22))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖∂_θ z₀ − ∂_θ z_S‖_{r_A} ≤ 7.7 × 10⁻⁷`**. -/
theorem wcheck_db :
    wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) distB * 10 ^ 8 ≤
      77 * (sig * 2 ^ (16 * (32 + 22))) := by
  decide +kernel

end PlasmaLean.Design.KamNewton
