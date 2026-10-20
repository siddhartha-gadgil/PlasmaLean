/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusACheck
public import PlasmaLean.Certificates.Kronecker2DWeighted

/-!
# Kernel computations for the weighted K2 certificate of torus A (KAM route, lemma K3.3)

Each `wcheck_*` theorem is a single `decide +kernel` evaluation of exact big-integer arithmetic:
a Kronecker image from `Design/KamTorusAForms` and its separable weighted digit sum `wl1KronP`
(`Certificates/Kronecker2DWeighted`). The weights dominate `e^{r(|k| + |m|)}` for
`e^r ≤ 74315 / 2^16`. In `Design/KamTorusAWeighted` this is applied with `r = 0.1257`. A mode at
distance `(s_i, s_j)` from the centre gets the integer weight
`74315^{s_i} 2^{16(K_i − s_i)} · 74315^{s_j} 2^{16(K_j − s_j)}`, and the bound is read after
dividing by `2^{16(K_i + K_j)}`. Parameters:

* residuals `R̂_R`, `R̂_z` and the `ι − ι_q` correction products `D̂ R̂_θ`, `D̂ Ẑ_θ` (degree 6):
  `b = 656`, rows of `W = 385` digits (`2^9` columns of the column tree), `267` rows,
  centre `(6N, 6M+1)`, `K_i = 192`, `K_j = 133`;
* `D̂ − c0D u^{5N} v^{5M+1}` (degree 5): same `b`, `W`, `223` rows, centre `(5N, 5M+1)`,
  `K_i = 160`, `K_j = 111`;
* the torus grids (`R̂ − t`, `Ẑ`, `R̂_θ`, `Ẑ_θ`, `R̂_ψ`, `Ẑ_ψ`): `b = 128`, `W = 2N + 1 = 65`,
  `45` rows, centre `(N, M)`, `K_i = 32`, `K_j = 22`.

The predictions come from the untrusted oracle `scripts/kam_oracle/weighted_cert.py`.
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA

open PlasmaLean.Certificates.Kron2

/-- Kronecker image of `D̂ R̂_θ` (`b = 656`, `W = 385`). -/
def DRthint : ℤ := Dint 656 385 * packGrid 656 385 gRth (2 * M + 1)

/-- Kronecker image of `D̂ Ẑ_θ` (`b = 656`, `W = 385`). -/
def DZthint : ℤ := Dint 656 385 * packGrid 656 385 gZth (2 * M + 1)

/-- Kronecker image of `D̂ − c0D u^{5N} v^{5M+1}` (`b = 656`, `W = 385`). -/
def Dsubint : ℤ := Dint 656 385 - (c0D : ℤ) * ((pow2 (656 * (5 * N + 385 * (5 * M + 1))) : ℕ) : ℤ)

/-- Kronecker image of `t = σ u^N v^M` for the grid parameters `b = 128`, `W = 65`. -/
def tGrid : ℤ := ((sig * 2 ^ (128 * (N + 65 * M)) : ℕ) : ℤ)

/-- A priori bound for `D̂ R̂_θ`: below `2^655`. -/
theorem apriori_DRth : Dbd (gridL1 gR) (gridL1 gZ) sig * gridL1 gRth < 2 ^ (656 - 1) := by
  decide +kernel

/-- A priori bound for `D̂ Ẑ_θ`: below `2^655`. -/
theorem apriori_DZth : Dbd (gridL1 gR) (gridL1 gZ) sig * gridL1 gZth < 2 ^ (656 - 1) := by
  decide +kernel

/-- A priori bounds for the torus grids: below `2^127`. -/
theorem apriori_grid :
    gridL1 gR + sig < 2 ^ (128 - 1) ∧ gridL1 gZ < 2 ^ (128 - 1) ∧
      gridL1 gRth < 2 ^ (128 - 1) ∧ gridL1 gZth < 2 ^ (128 - 1) ∧
      gridL1 gRps < 2 ^ (128 - 1) ∧ gridL1 gZps < 2 ^ (128 - 1) := by
  decide +kernel

/-- The centre of `D̂`: `1 ≤ c0D / (16σ⁵) ≤ 1.007`. -/
theorem check_c0D : 16 * sig ^ 5 ≤ c0D ∧ c0D * 1000 ≤ 1007 * (16 * sig ^ 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Weighted `‖R̂_R‖_r ≤ 5.829 × 10⁻²² · 2^{Q+4} σ⁶`** (scaled by `2^{16·325}`). -/
theorem wcheck_RR :
    wl1KronP 656 385 9 9 (12 * M + 2 + 1) (fun i => kwtS 74315 16 192 (ndist i (6 * N)))
        (fun j => kwtS 74315 16 133 (ndist j (6 * M + 1))) (RRint 656 385) * 10 ^ 25 ≤
      5829 * (2 ^ (Q + 4) * sig ^ 6 * 2 ^ (16 * (192 + 133))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Weighted `‖R̂_z‖_r ≤ 3.464 × 10⁻²² · 2^{Q+5} σ⁶`**. -/
theorem wcheck_RZ :
    wl1KronP 656 385 9 9 (12 * M + 2 + 1) (fun i => kwtS 74315 16 192 (ndist i (6 * N)))
        (fun j => kwtS 74315 16 133 (ndist j (6 * M + 1))) (RZint 656 385) * 10 ^ 25 ≤
      3464 * (2 ^ (Q + 5) * sig ^ 6 * 2 ^ (16 * (192 + 133))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Weighted `‖D̂ R̂_θ‖_r ≤ 0.28 · 16σ⁶` (the `ι − ι_q` correction of the `R`-residual). -/
theorem wcheck_DRth :
    wl1KronP 656 385 9 9 (12 * M + 2 + 1) (fun i => kwtS 74315 16 192 (ndist i (6 * N)))
        (fun j => kwtS 74315 16 133 (ndist j (6 * M + 1))) DRthint * 100 ≤
      28 * (16 * sig ^ 6 * 2 ^ (16 * (192 + 133))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Weighted `‖D̂ Ẑ_θ‖_r ≤ 0.29 · 16σ⁶` (the `ι − ι_q` correction of the `z`-residual). -/
theorem wcheck_DZth :
    wl1KronP 656 385 9 9 (12 * M + 2 + 1) (fun i => kwtS 74315 16 192 (ndist i (6 * N)))
        (fun j => kwtS 74315 16 133 (ndist j (6 * M + 1))) DZthint * 100 ≤
      29 * (16 * sig ^ 6 * 2 ^ (16 * (192 + 133))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Weighted `‖D̂ − c0D u^{5N} v^{5M+1}‖_r ≤ 0.483 · 16σ⁵`. -/
theorem wcheck_Dsub :
    wl1KronP 656 385 9 8 (10 * M + 2 + 1) (fun i => kwtS 74315 16 160 (ndist i (5 * N)))
        (fun j => kwtS 74315 16 111 (ndist j (5 * M + 1))) Dsubint * 1000 ≤
      483 * (16 * sig ^ 5 * 2 ^ (16 * (160 + 111))) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Weighted norms of the torus grids (each scaled by `σ · 2^{16·54}`):
`‖R − 1‖_r ≤ 0.228`, `‖z‖_r ≤ 0.224`, `‖∂_θR‖_r ≤ 0.236`, `‖∂_θz‖_r ≤ 0.231`,
`‖∂_ψR‖_r ≤ 0.065`, `‖∂_ψz‖_r ≤ 0.063`. -/
theorem wcheck_grid :
    wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gR (2 * M + 1) - tGrid) * 1000 ≤
        228 * (sig * 2 ^ (16 * (32 + 22))) ∧
      wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gZ (2 * M + 1)) * 1000 ≤
        224 * (sig * 2 ^ (16 * (32 + 22))) ∧
      wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gRth (2 * M + 1)) * 1000 ≤
        236 * (sig * 2 ^ (16 * (32 + 22))) ∧
      wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gZth (2 * M + 1)) * 1000 ≤
        231 * (sig * 2 ^ (16 * (32 + 22))) ∧
      wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gRps (2 * M + 1)) * 1000 ≤
        65 * (sig * 2 ^ (16 * (32 + 22))) ∧
      wl1KronP 128 65 7 6 (2 * M + 1) (fun i => kwtS 74315 16 32 (ndist i N))
        (fun j => kwtS 74315 16 22 (ndist j M)) (packGrid 128 65 gZps (2 * M + 1)) * 1000 ≤
        63 * (sig * 2 ^ (16 * (32 + 22))) := by
  decide +kernel

end PlasmaLean.Design.KamTorusA
