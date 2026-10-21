/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusEnvH
public import PlasmaLean.Design.KamTorusACheck

/-!
# Kernel checks: the guiding-centre torus `K₀` is star-shaped about the magnetic axis

Two exact integer computations on the high-resolution data of the guiding-centre torus
`K₀ = (1 + u₀G, z₀G)` (`Design/RationalStellaratorGCTorusEnvH`: grids `gH_U`, `gH_Z`, `gH_thU`,
`gH_thZ`, Kronecker images `KvH`), used by `Design/RationalStellaratorGCStar`:

* `check_radG`: the radial polynomial `Ŵ = (P_U + P_Z) + (P_U − P_Z) u²` (whose value on the torus
  is `2^{102} u^{N+1} v^M ((R − 1) cos θ + z sin θ)`) has centre coefficient `c0radG` and
  `ℓ¹` deviation `L` with `(c0radG − L)/2^{102} ≥ 0.035`;
* `check_windG`: the winding polynomial `N̂ = P_U P_{θZ} − P_Z P_{θU}` (value
  `2^{202} u^{2N} v^{2M} ((R − 1) ∂_θ z − z ∂_θ R)`) has centre coefficient `c0windG` and deviation
  `L` with `(c0windG − L)/2^{202} ≥ 0.0064`.

The `ℓ¹` norms are exact digit sums of Kronecker images (`l1Kron`), with a priori bounds
(`apriori_radG`, `apriori_windG`) from the static bounds `LH`. The centre coefficients are oracle
values (`scripts/gc_kam`-style decoding of the packed grids; any value is sound).
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Design.KamTorusA

set_option linter.style.longLine false in
/-- Oracle value of the centre coefficient of the radial polynomial (at `u^{N+1} v^M`). -/
def c0radG : ℕ := 509930499502162457500793002220

set_option linter.style.longLine false in
/-- Oracle value of the centre coefficient of the winding polynomial (at `u^{2N} v^{2M}`). -/
def c0windG : ℕ := 60192394302749703710688795359550321811233437291295476301968

/-- The Kronecker image of `Ŵ − c0radG u^{N+1} v^M` (`b = 130`, `W = 83`). -/
def radIntG : ℤ :=
  (KvH 130 83 4 + KvH 130 83 5) + (KvH 130 83 4 - KvH 130 83 5) * ((2 ^ (130 * 2) : ℕ) : ℤ) -
    (c0radG : ℤ) * ((pow2 (130 * ((NH + 1) + 83 * MH)) : ℕ) : ℤ)

/-- The Kronecker image of `N̂ − c0windG u^{2N} v^{2M}` (`b = 257`, `W = 161`). -/
def windIntG : ℤ :=
  KvH 257 161 4 * KvH 257 161 9 - KvH 257 161 5 * KvH 257 161 8 -
    (c0windG : ℤ) * ((pow2 (257 * (2 * NH + 161 * (2 * MH))) : ℕ) : ℤ)

/-- A priori bound for `Ŵ − c0radG · mono`: below `2^129`. -/
theorem apriori_radG : 2 * (LH 4 + LH 5) + c0radG < 2 ^ (130 - 1) := by
  decide +kernel

/-- A priori bound for `N̂ − c0windG · mono`: below `2^256`. -/
theorem apriori_windG : LH 4 * LH 9 + LH 5 * LH 8 + c0windG < 2 ^ (257 - 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖Ŵ − c0radG u^{N+1} v^M‖₁ ≤ L` with `(c0radG − L)/2^{102} ≥ 0.035`. -/
theorem check_radG : 200 * l1Kron 130 13 radIntG + 7 * 2 ^ 102 ≤ 200 * c0radG := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖N̂ − c0windG u^{2N} v^{2M}‖₁ ≤ L` with `(c0windG − L)/2^{202} ≥ 0.0064`. -/
theorem check_windG : 625 * l1Kron 257 15 windIntG + 4 * 2 ^ 202 ≤ 625 * c0windG := by
  decide +kernel

end PlasmaLean.Design.RationalStellaratorGC
