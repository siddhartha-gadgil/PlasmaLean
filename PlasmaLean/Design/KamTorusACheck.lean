/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAForms

/-!
# Kernel computations for torus A (KAM route, stage K2)

Every theorem here is a single `decide +kernel` evaluation of exact big-integer arithmetic:
Kronecker images (`RRint`, `RZint`, `Dint`, `Nint`, `rt2int`, `dK2int` of `Design/KamTorusAForms`,
built from the packed data of `Design/KamTorusAData`) and their digit sums `l1Kron`
(`Certificates/Kronecker2D`), together with the a priori `ℓ¹` bounds that make the digit sums
equal to the `ℓ¹` norms of the formal polynomials. Parameters:

* residuals (degree 6): `b = 656` bits per slot, `W = 12N + 1 = 385`, `2^17` slots;
* `D̂` (degree 5): same Kronecker parameters, centre monomial `u^{5N} v^{5M+1}`, centre
  coefficient `c0D` (supplied by the oracle; any value is sound);
* graph quantities (degree 2): `b = 192`, `W = 4N + 1 = 129`, `2^14` slots, centre `u^{2N} v^{2M}`.

The semantic consequences are drawn in `Design/KamTorusA`.
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA

open PlasmaLean.Certificates.Kron2

/-- `2^n` computed as `(2^⌊n/2⌋)² 2^(n mod 2)` (the kernel caps the size of a single `Nat.pow`). -/
def pow2 (n : ℕ) : ℕ := 2 ^ (n / 2) * 2 ^ (n / 2) * 2 ^ (n % 2)

theorem pow2_eq (n : ℕ) : pow2 n = 2 ^ n := by
  rw [pow2, ← pow_add, ← pow_add]; congr 1; omega

set_option linter.style.longLine false in
/-- Oracle value of the centre coefficient of `D̂` (at `u^{5N} v^{5M+1}`). -/
def c0D : ℕ := 1497829697890505117423261317586091192243358451745844281282756269272892177505483987164806341019131132689280335426443611037997419970979813664

/-- Oracle value of the centre coefficient of `N̂` (at `u^{2N} v^{2M}`). -/
def c0N : ℕ := 111167639963713380168436107633862206808587006558413144

/-- A priori bound for `R̂_R`: below `2^655`, so digit sums are exact. -/
theorem apriori_RR :
    RRbd (gridL1 gR) (gridL1 gZ) (gridL1 gRth) (gridL1 gRps) sig < 2 ^ (656 - 1) := by
  decide +kernel

/-- A priori bound for `R̂_z`. -/
theorem apriori_RZ :
    RZbd (gridL1 gR) (gridL1 gZ) (gridL1 gZth) (gridL1 gZps) sig < 2 ^ (656 - 1) := by
  decide +kernel

/-- A priori bound for `D̂ − c0D · mono`. -/
theorem apriori_D : Dbd (gridL1 gR) (gridL1 gZ) sig + c0D < 2 ^ (656 - 1) := by
  decide +kernel

/-- A priori bound for `N̂ − c0N · mono`. -/
theorem apriori_N :
    (gridL1 gR + sig) * gridL1 gZth + gridL1 gZ * gridL1 gRth + c0N < 2 ^ (192 - 1) := by
  decide +kernel

/-- A priori bound for `(R̂ − t)² − Ẑ²`. -/
theorem apriori_rt2 : (gridL1 gR + sig) ^ 2 + gridL1 gZ ^ 2 < 2 ^ (192 - 1) := by
  decide +kernel

/-- A priori bound for `Ẑ_θ² − R̂_θ²`. -/
theorem apriori_dK2 : gridL1 gZth ^ 2 + gridL1 gRth ^ 2 < 2 ^ (192 - 1) := by
  decide +kernel

/-- `∑ |(i − N) gR| ≤ σ/5`, i.e. `‖∂_θ R‖_∞ ≤ 1/5`. -/
theorem gridL1_gRth_le : 5 * gridL1 gRth ≤ sig := by decide +kernel

/-- `∑ |(i − N) gZ| ≤ σ/5`, i.e. `‖∂_θ z‖_∞ ≤ 1/5`. -/
theorem gridL1_gZth_le : 5 * gridL1 gZth ≤ sig := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖R̂_R‖₁ ≤ 1.22 × 10⁻²³ · 2^{Q+4} σ⁶`** (exact digit sum of the Kronecker image). -/
theorem check_RR : l1Kron 656 17 (RRint 656 385) * 10 ^ 25 ≤ 122 * (2 ^ (Q + 4) * sig ^ 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **`‖R̂_z‖₁ ≤ 6.93 × 10⁻²⁴ · 2^{Q+5} σ⁶`**. -/
theorem check_RZ : l1Kron 656 17 (RZint 656 385) * 10 ^ 26 ≤ 693 * (2 ^ (Q + 5) * sig ^ 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖D̂ − c0D u^{5N} v^{5M+1}‖₁ ≤ L` with `(c0D − L)/(16σ⁵) ≥ 0.59` and
`(c0D + L)/(16σ⁵) ≤ 1.42`. -/
theorem check_D :
    100 * l1Kron 656 17
        (Dint 656 385 - (c0D : ℤ) * ((pow2 (656 * (5 * N + 385 * (5 * M + 1))) : ℕ) : ℤ)) +
        59 * (16 * sig ^ 5) ≤ 100 * c0D ∧
      100 * c0D + 100 * l1Kron 656 17
        (Dint 656 385 - (c0D : ℤ) * ((pow2 (656 * (5 * N + 385 * (5 * M + 1))) : ℕ) : ℤ)) ≤
        142 * (16 * sig ^ 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖N̂ − c0N u^{2N} v^{2M}‖₁ ≤ L` with `(c0N − L)/σ² ≥ 0.015`. -/
theorem check_N :
    1000 * l1Kron 192 14
        (Nint 192 129 - (c0N : ℤ) * ((pow2 (192 * (2 * N + 129 * (2 * M))) : ℕ) : ℤ)) +
        15 * sig ^ 2 ≤ 1000 * c0N := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖(R̂ − t)² − Ẑ²‖₁ ≤ 0.0358 σ²`. -/
theorem check_rt2 : 10000 * l1Kron 192 14 (rt2int 192 129) ≤ 358 * sig ^ 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `‖Ẑ_θ² − R̂_θ²‖₁ ≤ 0.0367 σ²`. -/
theorem check_dK2 : 10000 * l1Kron 192 14 (dK2int 192 129) ≤ 367 * sig ^ 2 := by
  decide +kernel

end PlasmaLean.Design.KamTorusA
