/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCEw1RelH
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH1
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH2
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH3
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH4
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH5
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH6
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH7
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH8
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH9
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH10
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH11
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH12
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH13
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH14
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH15
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH16
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH17
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH18
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH19
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH20
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH21
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH22
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH23
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH24
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH25
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH26
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH27
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH28
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH29
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH30
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH31
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH32
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH33
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH34
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH35
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH36
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH37
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH38
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH39
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH40
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH41
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH42
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH43
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH44
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH45
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH46
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH47
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH48
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH49
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH50
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH51
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH52
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH53
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH54
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH55
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH56
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH57
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH58
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH59
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH60
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH61
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH62
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH63
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH64
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH65
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH66
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH67
public import PlasmaLean.Design.RationalStellaratorGCEw1CheckH68
public import PlasmaLean.Design.RationalStellaratorGCMuCommon
public import PlasmaLean.Design.RationalStellaratorGCEw1LowMemH

/-!
# The high-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the high-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`, built
variable by variable (`ballHE1_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCEw1CheckH*` (`node3_fullN`), the node identities of
`Design/RationalStellaratorGCEw1RelH` and the node step `vstep`.
Generated by `scripts/gc_kam/ew_emit_lean.py`.

Energy-window node 1: gyro-length `ρ_1 = 1/256 − 2⁻³²`, its own family torus `K_1(λ)`; the
fields at `ρ_1` are the nodes `DtJ`, `nRtJ`, `nZtJ`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LRx` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHE1_LRx : KvHE1 221 73 55 6 = famPack 221 73 55 NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 10888383889117653077957113864) ((c0HE1 4 : ℤ) * 158456325028528675187087900672) ddHE1 drHE1 0 (famHE1 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `LRx` is the symbol family of `U` (equal Kronecker images). -/
theorem PHE1_der_LRx : PHE1 6 = famPoly NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 10888383889117653077957113864) ((c0HE1 4 : ℤ) * 158456325028528675187087900672) 0 (famHE1 4) := by
  have hk : kron 221 73 (flat 55 (PHE1 6)) = kron 221 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 10888383889117653077957113864) ((c0HE1 4 : ℤ) * 158456325028528675187087900672) 0 (famHE1 4))) := by
    rw [kronHE1, ← famPack_eq 221 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 4)
      fun sd h => ((staticHE1 4 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_LRx
  have hbox := boxHE1 6
  rw [bx6HE1 6 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 6) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 4 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `LRx` is a derivative of the centre `U`. -/
theorem xHE1_der_LRx {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 6 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHE1 c 4) := by
  rw [xHE1_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHE1, PHE1_der_LRx,
    show WtHE1 6 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LZx` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHE1_LZx : KvHE1 221 73 55 7 = famPack 221 73 55 NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 10888383889117653077957113864) ((c0HE1 5 : ℤ) * 158456325028528675187087900672) ddHE1 drHE1 0 (famHE1 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `LZx` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHE1_der_LZx : PHE1 7 = famPoly NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 10888383889117653077957113864) ((c0HE1 5 : ℤ) * 158456325028528675187087900672) 0 (famHE1 5) := by
  have hk : kron 221 73 (flat 55 (PHE1 7)) = kron 221 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 10888383889117653077957113864) ((c0HE1 5 : ℤ) * 158456325028528675187087900672) 0 (famHE1 5))) := by
    rw [kronHE1, ← famPack_eq 221 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 5)
      fun sd h => ((staticHE1 5 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_LZx
  have hbox := boxHE1 7
  rw [bx6HE1 7 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 7) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 5 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `LZx` is a derivative of the centre `Z`. -/
theorem xHE1_der_LZx {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 7 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHE1 c 5) := by
  rw [xHE1_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHE1, PHE1_der_LZx,
    show WtHE1 7 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thU` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHE1_thU : KvHE1 125 73 55 8 = famPack 125 73 55 NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 1) ((c0HE1 4 : ℤ) * 0) ddHE1 drHE1 0 (famHE1 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `thU` is the symbol family of `U` (equal Kronecker images). -/
theorem PHE1_der_thU : PHE1 8 = famPoly NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 1) ((c0HE1 4 : ℤ) * 0) 0 (famHE1 4) := by
  have hk : kron 125 73 (flat 55 (PHE1 8)) = kron 125 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 4 then -1 else 1) 0
    ((c0HE1 4 : ℤ) * 1) ((c0HE1 4 : ℤ) * 0) 0 (famHE1 4))) := by
    rw [kronHE1, ← famPack_eq 125 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 4)
      fun sd h => ((staticHE1 4 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_thU
  have hbox := boxHE1 8
  rw [bx6HE1 8 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 8) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 4 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `thU` is a derivative of the centre `U`. -/
theorem xHE1_der_thU {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 8 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 4) := by
  rw [xHE1_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHE1, PHE1_der_thU,
    show WtHE1 8 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZ` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHE1_thZ : KvHE1 125 73 55 9 = famPack 125 73 55 NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 1) ((c0HE1 5 : ℤ) * 0) ddHE1 drHE1 0 (famHE1 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `thZ` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHE1_der_thZ : PHE1 9 = famPoly NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 1) ((c0HE1 5 : ℤ) * 0) 0 (famHE1 5) := by
  have hk : kron 125 73 (flat 55 (PHE1 9)) = kron 125 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 5 then -1 else 1) 0
    ((c0HE1 5 : ℤ) * 1) ((c0HE1 5 : ℤ) * 0) 0 (famHE1 5))) := by
    rw [kronHE1, ← famPack_eq 125 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 5)
      fun sd h => ((staticHE1 5 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_thZ
  have hbox := boxHE1 9
  rw [bx6HE1 9 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 9) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 5 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `thZ` is a derivative of the centre `Z`. -/
theorem xHE1_der_thZ {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 9 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 5) := by
  rw [xHE1_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHE1, PHE1_der_thZ,
    show WtHE1 9 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thUe` and the symbol family of `Ue` have the same
Kronecker image. -/
theorem kderHE1_thUe : KvHE1 125 73 55 12 = famPack 125 73 55 NHE1 MHE1 DHE1 (if oddHE1 10 then -1 else 1) 0
    ((c0HE1 10 : ℤ) * 1) ((c0HE1 10 : ℤ) * 0) ddHE1 drHE1 0 (famHE1 10) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `thUe` is the symbol family of `Ue` (equal Kronecker images). -/
theorem PHE1_der_thUe : PHE1 12 = famPoly NHE1 MHE1 DHE1 (if oddHE1 10 then -1 else 1) 0
    ((c0HE1 10 : ℤ) * 1) ((c0HE1 10 : ℤ) * 0) 0 (famHE1 10) := by
  have hk : kron 125 73 (flat 55 (PHE1 12)) = kron 125 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 10 then -1 else 1) 0
    ((c0HE1 10 : ℤ) * 1) ((c0HE1 10 : ℤ) * 0) 0 (famHE1 10))) := by
    rw [kronHE1, ← famPack_eq 125 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 10)
      fun sd h => ((staticHE1 10 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_thUe
  have hbox := boxHE1 12
  rw [bx6HE1 12 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 12) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 10 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `thUe` is a derivative of the centre `Ue`. -/
theorem xHE1_der_thUe {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 12 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 10) := by
  rw [xHE1_fam hc (i := 10) rfl (p := 0) rfl, dS_famCtr, xHE1, PHE1_der_thUe,
    show WtHE1 12 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZe` and the symbol family of `Ze` have the same
Kronecker image. -/
theorem kderHE1_thZe : KvHE1 125 73 55 13 = famPack 125 73 55 NHE1 MHE1 DHE1 (if oddHE1 11 then -1 else 1) 0
    ((c0HE1 11 : ℤ) * 1) ((c0HE1 11 : ℤ) * 0) ddHE1 drHE1 0 (famHE1 11) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `thZe` is the symbol family of `Ze` (equal Kronecker images). -/
theorem PHE1_der_thZe : PHE1 13 = famPoly NHE1 MHE1 DHE1 (if oddHE1 11 then -1 else 1) 0
    ((c0HE1 11 : ℤ) * 1) ((c0HE1 11 : ℤ) * 0) 0 (famHE1 11) := by
  have hk : kron 125 73 (flat 55 (PHE1 13)) = kron 125 73 (flat 55 (famPoly NHE1 MHE1 DHE1 (if oddHE1 11 then -1 else 1) 0
    ((c0HE1 11 : ℤ) * 1) ((c0HE1 11 : ℤ) * 0) 0 (famHE1 11))) := by
    rw [kronHE1, ← famPack_eq 125 73 55 NHE1 MHE1 DHE1 _ _ _ _ 0 (famHE1 11)
      fun sd h => ((staticHE1 11 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kderHE1_thZe
  have hbox := boxHE1 13
  rw [bx6HE1 13 (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE1 55 13) (l1_flat_famPoly_le 55 NHE1 MHE1 DHE1
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((staticHE1 11 (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `thZe` is a derivative of the centre `Ze`. -/
theorem xHE1_der_thZe {c : ℂ} (hc : c ≠ 0) :
    xHE1 c 13 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 11) := by
  rw [xHE1_fam hc (i := 11) rfl (p := 1) rfl, dS_famCtr, xHE1, PHE1_der_thZe,
    show WtHE1 13 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

/-- The embedded low-resolution family centre `Ue`. -/
theorem xHE1_embed_Ue {c : ℂ} (hc : c ≠ 0) : xHE1 c 10 = xLM c 4 := by
  rw [xHE1_fam hc (i := 10) rfl (p := 0) rfl, xLM_fam hc (i := 4) rfl (p := 0) rfl]
  exact famCtr_embed SLM NLM MLM 0 (NHE1 - NLM) (MHE1 - MLM) (SHE1 - SLM) _ c 0 (famLM 4)
    (by decide +kernel)

/-- The embedded low-resolution family centre `Ze`. -/
theorem xHE1_embed_Ze {c : ℂ} (hc : c ≠ 0) : xHE1 c 11 = xLM c 5 := by
  rw [xHE1_fam hc (i := 11) rfl (p := 1) rfl, xLM_fam hc (i := 5) rfl (p := 1) rfl]
  exact famCtr_embed SLM NLM MLM 1 (NHE1 - NLM) (MHE1 - MLM) (SHE1 - SLM) _ c 0 (famLM 5)
    (by decide +kernel)

set_option linter.unusedVariables false in
/-- The variable `t` is exact. -/
theorem XHE1_eq_t {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 0 = xHE1 c 0 := by
  rw [xHE1_t (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `V` is exact. -/
theorem XHE1_eq_V {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 1 = xHE1 c 1 := by
  rw [xHE1_V]; rfl

set_option linter.unusedVariables false in
/-- The variable `c` is exact. -/
theorem XHE1_eq_c {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 2 = xHE1 c 2 := by
  rw [xHE1_c, ctr_cPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `s` is exact. -/
theorem XHE1_eq_s {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 3 = xHE1 c 3 := by
  rw [xHE1_s, ctr_sPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `U` is exact. -/
theorem XHE1_eq_U {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 4 = xHE1 c 4 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Z` is exact. -/
theorem XHE1_eq_Z {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 5 = xHE1 c 5 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `thU` is exact. -/
theorem XHE1_eq_thU {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 8 = xHE1 c 8 := by
  rw [XHE1_spec c (i := 8) rfl, xHE1_der_thU (ne_zero_of_norm_one_mu hc)]
  simp [XHE1spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZ` is exact. -/
theorem XHE1_eq_thZ {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 9 = xHE1 c 9 := by
  rw [XHE1_spec c (i := 9) rfl, xHE1_der_thZ (ne_zero_of_norm_one_mu hc)]
  simp [XHE1spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `Ue` is exact. -/
theorem XHE1_eq_Ue {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 10 = xHE1 c 10 := by
  rw [XHE1_spec c (i := 10) rfl, xHE1_embed_Ue (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `Ze` is exact. -/
theorem XHE1_eq_Ze {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 11 = xHE1 c 11 := by
  rw [XHE1_spec c (i := 11) rfl, xHE1_embed_Ze (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `thUe` is exact. -/
theorem XHE1_eq_thUe {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 12 = xHE1 c 12 := by
  rw [XHE1_spec c (i := 12) rfl, xHE1_der_thUe (ne_zero_of_norm_one_mu hc), xHE1_embed_Ue (ne_zero_of_norm_one_mu hc)]
  simp [XHE1spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZe` is exact. -/
theorem XHE1_eq_thZe {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 13 = xHE1 c 13 := by
  rw [XHE1_spec c (i := 13) rfl, xHE1_der_thZe (ne_zero_of_norm_one_mu hc), xHE1_embed_Ze (ne_zero_of_norm_one_mu hc)]
  simp [XHE1spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `V0` is exact. -/
theorem XHE1_eq_V0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 52 = xHE1 c 52 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Dt0` is exact. -/
theorem XHE1_eq_Dt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 68 = xHE1 c 68 := by
  rw [xHE1_zero c (i := 68) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nRt0` is exact. -/
theorem XHE1_eq_nRt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 69 = xHE1 c 69 := by
  rw [xHE1_zero c (i := 69) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nZt0` is exact. -/
theorem XHE1_eq_nZt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 70 = xHE1 c 70 := by
  rw [xHE1_zero c (i := 70) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `r` is exact. -/
theorem XHE1_eq_r {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 71 = xHE1 c 71 := by
  rw [XHE1_rel c (i := 71) rfl]
  change XLM c (xHE1 c 4) (xHE1 c 5) 114 = _
  rw [XLM_new c _ _ (j := 114) rfl]
  change algebraMap ℂ FA (((63 + 32 * lamF c : ℝ)) : ℂ) = _
  rw [xHE1_r (ne_zero_of_norm_one_mu hc), param_eq_mu hc]

set_option linter.unusedVariables false in
/-- The variable `V40` is exact. -/
theorem XHE1_eq_V40 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 79 = xHE1 c 79 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `N0` is exact. -/
theorem XHE1_eq_N0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE1 c 86 = xHE1 c 86 := by
  rfl

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- **Norms of the centres.** -/
theorem normHE1 {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 99 → Bd r (xHE1 c i) (BHE1 i)
  | 0, _ => by rw [xHE1_t (ne_zero_of_norm_one_mu hc)]; exact (Bd_one r).le (by norm_num [BHE1, BHE1l])
  | 1, _ => by rw [xHE1_V]; exact (Bd_one r).le (by norm_num [BHE1, BHE1l])
  | 2, _ => by rw [xHE1_c, ctr_cPoly]; exact (Bd_cS_q hq).le (by norm_num [BHE1, BHE1l])
  | 3, _ => by rw [xHE1_s, ctr_sPoly]; exact (Bd_sS_q hq).le (by norm_num [BHE1, BHE1l])
  | 4, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 4 0 119 73 25 11 1 73 36 27
      85868366090367129019734386824381402397411191377516217216927619125901404340006074907896115022685172222660967669468614679079542228329147774207642520826990387577508190240240144268276920625881424987178660001542211706175972196914256407688198761211382462271148355957065995958165969266511441372750671365637574518015379531319149737666169274368 (BHE1 4) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_U cHE1_U (by decide +kernel)
  | 5, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 5 1 119 73 25 11 1 73 36 27
      72209710579524435657526709882554666648075137148565972517392782529371941796458465439000049481732611241692431599376616724667187637780172671819538543427124312997107307420355844228245323572956694554327315704851609334758891826793180810868474529558052600867987302540001934998053474886008947998370403015095733076420002514536423058176999424000 (BHE1 5) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_Z cHE1_Z (by decide +kernel)
  | 6, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 6 3 221 73 25 11 1 73 36 27
      3855256309044197615836796488354407682442455801915905121174919848329534104135676956503670489470283007176435149084985513480278479593328799241686794330606141549614143931092619131095343853491842968385431058602372886411580184279108949643361849553123337781726382451714375570265421527016973019891227291317877296540897028849384495118235379839465975829454576907995326709760 (BHE1 6) (kronHE1 221 73 55) rfl (by decide +kernel) clHE1_LRx cHE1_LRx (by decide +kernel)
  | 7, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 7 0 221 73 25 11 1 73 36 27
      3655661287867031750895918624802007307325223012536503569845225806691027084374806817733323030283946814736768083029279422701527033038919925755714149412179999126293831491711072195573681887619071393606002925959447197066530931756428697099508185908612903402574205668263043297850061704274287416343133151970774607406047054050928758407234850376079470085445459136882724044800 (BHE1 7) (kronHE1 221 73 55) rfl (by decide +kernel) clHE1_LZx cHE1_LZx (by decide +kernel)
  | 8, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 8 3 125 73 25 11 1 73 36 27
      72728004162940076852311291933160432075546472253929517955986004253493274973660667218113579122686728118626542261723597120032702604281036509361012650857685016943833482712138398010410621877875728013259303058804414503074263049452656030298879764661341788260559549875507082735143906686753826820613773008971785450943984888546139474823028408320 (BHE1 8) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_thU cHE1_thU (by decide +kernel)
  | 9, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 9 0 125 73 25 11 1 73 36 27
      71928721240674387275224338511225605601550924229802413331188150788091449969317506176734496663617415674302976139579862148087475978771319384976758552358420681990707982102575461312249398043153742330277002054101769478161504802552791823819325897508320215252297934707142522304910345129028879715544987021757126815735026822525923693923244441600 (BHE1 9) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_thZ cHE1_thZ (by decide +kernel)
  | 10, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 10 0 119 73 25 11 8 10 36 27
      127851892760837724279445547993531155933966158517778688691437555192970059617708139673364712271013175352062085908847818465626513013879417831113051489752313227048297978941561537174552325389892027276649521583864559441751640071163086964626807533984980423021293487351997124183550557436499438510440831293989808899438662653057576820382105600000 (BHE1 10) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_Ue cHE1_Ue (by decide +kernel)
  | 11, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 11 1 119 73 25 11 8 10 36 27
      105418199702671940687587185900788720098161834334999805375289230993403724820309205906660895678677713088485654508690223786103484497935275556223281171961484838763104139598079804303796229103419807096146591202091609902464530056436849945131216286393188296769443395383593532704695932486921421000440168198260720798658834052580974126075740160000 (BHE1 11) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_Ze cHE1_Ze (by decide +kernel)
  | 12, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 12 3 125 73 25 11 8 10 36 27
      105061925581715585637867725836733851934764247322786501268704853420075859413845047658684870262427858377799061962600518822973491286413812958687050190107102563504240947443804445671848068240837614223931504532168351428281009275196873579279959081215351769652061380490355280561253320335762364145585079324282000793341744399149202598264832000000 (BHE1 12) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_thUe cHE1_thUe (by decide +kernel)
  | 13, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 13 0 125 73 25 11 8 10 36 27
      103991936885312502901650488240118186811772515815930252385444932917497140650424973542225328391457849572113936595604722220815190145894224655394095981800653933291694831781578563299569413487489596082207170531903868844746409994524263095447510266924786837887548725821888837966310513936055153855233358548549048376737047825243700732603924480000 (BHE1 13) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_thZe cHE1_thZe (by decide +kernel)
  | 14, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 14 2 115 73 25 11 8 10 36 27
      14124926069299291266310010059497846508711232341228512340338234682754385454605703867946901677578503294241401077057258452422558487947333121421379778520926439332728993280240326976340974092174524628570180468108500506437687584373322928502948476507552544421505834944386058770963969719835745989922499538895508338166830564940216847229255680000 (BHE1 14) (kronHE1 115 73 55) rfl (by decide +kernel) clHE1_m02 cHE1_m02 (by decide +kernel)
  | 15, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 15 1 115 73 25 11 8 10 36 27
      10412665856817670202035197061073883065919226081980591528266130290571699089191859888074450093479144037381708100213058140972337253503160008171131308147341000497652019615771469339673013065918730566037986512407797165832208814215664454697675877595034184912718263635637509271196249111497817909502082078023461950591187639387039984391290880000 (BHE1 15) (kronHE1 115 73 55) rfl (by decide +kernel) clHE1_m11 cHE1_m11 (by decide +kernel)
  | 16, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 16 0 115 73 25 11 8 10 36 27
      20629244317420584043057864179917418917566582297736666022125410087626923698819929356499466247175280427052835711699758450382537499568384013564070020655394523655388127783440620841161351791085666839344705539224134612142977533882681880063299999895222077377092858370123144558767848723519223269680965850965095891965519084934363794259312640000 (BHE1 16) (kronHE1 115 73 55) rfl (by decide +kernel) clHE1_m20 cHE1_m20 (by decide +kernel)
  | 17, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 17 3 112 73 25 11 8 10 36 27
      1887994419489599062855905807048074409897567822963765920033548746889569606336804818087878545210974860422289432179699045617594431932057142908266887692309732264655397075785909415667869862024089872032097207806518936712963789733782641352124829928695593423194269818825158475883260072759855537615738839707208488122570826641401247254446080000 (BHE1 17) (kronHE1 112 73 55) rfl (by decide +kernel) clHE1_m03 cHE1_m03 (by decide +kernel)
  | 18, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 18 2 111 73 25 11 8 10 36 27
      1332961642672007317768827626101233979099748012381946150170703882061704913743959179023541081949347256780861984245014294065319179370524799418179753348504476204360926842202608125829650969443818461515699280392887266652274002337322198732631002298878829585262987848750682980479607690494584032799831888071484898027395165790794643375390720000 (BHE1 18) (kronHE1 111 73 55) rfl (by decide +kernel) clHE1_m12 cHE1_m12 (by decide +kernel)
  | 19, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 19 1 111 73 25 11 8 10 36 27
      1503228065422790705571509588702390072420752717436494637589359226709370852500300229821735587095457198403733196524304940994019532129234859496062213965260652966289515544043877398237724648201168315710354856806641762035651586222551509624469521887189589379544397059175546053382277621036363340515352368204785682510827050800291375501803520000 (BHE1 19) (kronHE1 111 73 55) rfl (by decide +kernel) clHE1_m21 cHE1_m21 (by decide +kernel)
  | 20, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 20 0 113 73 25 11 8 10 36 27
      3300730275701844854459239191472491934193618085639225425168991332485460595449226189723091694243563365592818640176790701543967254432460753408761340232843514884466300511773822852546315240149405696507184807577457007701229563773452617177534494449216078104316479987823521539767612604793629944315351063107253525632129343582447494506741760000 (BHE1 20) (kronHE1 113 73 55) rfl (by decide +kernel) clHE1_m30 cHE1_m30 (by decide +kernel)
  | 21, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 21 3 108 73 25 11 8 10 36 27
      154519521881069050327725349235955325548590964426143577505425042613054847923624473333097484156475817059199432647203861964262314473151358261407628606188095831130104388249795735094810515741058222293524295742194782088289756957313476508902525864513291956779746665131120038111776882404958861734777954863797958748427930682865928707768320000 (BHE1 21) (kronHE1 108 73 55) rfl (by decide +kernel) clHE1_m13 cHE1_m13 (by decide +kernel)
  | 22, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 22 2 107 73 25 11 8 10 36 27
      142975017688092029363185844986766006586052561275037733859191494193005141389788310936863526131242767520177307378050765150921179797886554367747481734279802498540813572084761491419019430843424855883023064447465496666032406396662465111519245156560673720961712343890212854500872977211919622505228031431900115279360806509174455606968320000 (BHE1 22) (kronHE1 107 73 55) rfl (by decide +kernel) clHE1_m22 cHE1_m22 (by decide +kernel)
  | 23, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 23 1 108 73 25 11 8 10 36 27
      217613332759711952025646502280703963364853164851164892263983124060576324881050496885827922690863101597382350185271719851992510151011905640060888208914370960583271915932136529169071907862708553612131005851895015924040502688400781355135537465835411825204306666265934027474775616325272252769199994899211912882801490979153055234129920000 (BHE1 23) (kronHE1 108 73 55) rfl (by decide +kernel) clHE1_m31 cHE1_m31 (by decide +kernel)
  | 24, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 24 0 109 73 25 11 8 10 36 27
      548492897512839181928050015002854488842969781325308610649981740465443105895995035410525373200371067465536849865698160741253606366200450205403572124574333950001602198341985350362688565448183329864184892642442639199562464106343685746570006301344539960857599551504041501593677641407454409757934801226120646742814547014214294637117440000 (BHE1 24) (kronHE1 109 73 55) rfl (by decide +kernel) clHE1_m40 cHE1_m40 (by decide +kernel)
  | 25, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 25 1 105 73 25 11 8 10 36 27
      33104570287784259261047485419241747232409147153727391550467761957512579125240714611345956695672094876760908642054710413914295133611754001492625762812231726004952787484181377593254105163919413395540433123702447560634599771997219615923068281958434611957866161861811429199424193501834365963261799408772738403119392675591049644605440000 (BHE1 25) (kronHE1 105 73 55) rfl (by decide +kernel) clHE1_m41 cHE1_m41 (by decide +kernel)
  | 26, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 26 0 107 73 25 11 8 10 36 27
      90153997530490662107911575343069546467036242529336561848914076307310929641429079856326039784559511878012610286742787550318706706779607917601890415800513171067995988015437053617368134535328764354865620101396045883760278525784510910184551182143524956485592250419619987765271948791020875743626505636993484865360599941906825257943040000 (BHE1 26) (kronHE1 107 73 55) rfl (by decide +kernel) clHE1_m50 cHE1_m50 (by decide +kernel)
  | 27, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 27 1 102 73 25 11 8 10 36 27
      5078317505228837109456751118338533122044441948988544522111607172353754913742028784923585687924207193495141858164729717228601462103785887009657629565286919449951336257622335889553839947688919986183090625871291148163558727729446071058492072780574894076459491745018090553116856631692927835136670962609530822658773379931981595279360000 (BHE1 27) (kronHE1 102 73 55) rfl (by decide +kernel) clHE1_m51 cHE1_m51 (by decide +kernel)
  | 28, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 28 0 104 73 25 11 8 10 36 27
      14879594058157336314286933895051333152808331055825523844984613311396159287786911686329633284033514026642310774240474908892143297859741931639337697740850072677471331077000455356429064297782844992486943165462881435069156631484723046634993199778720844926096619258254843759592077321232567395346335133426599080916983152318034487541760000 (BHE1 28) (kronHE1 104 73 55) rfl (by decide +kernel) clHE1_m60 cHE1_m60 (by decide +kernel)
  | 29, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 29 0 122 73 25 11 8 10 36 27
      908498515907267013327372156385652691867735095288853712515614295651937640780827843696576617567623178253471430280344389542625386056750565835644830076035940060799219319451170186967224934224189784927001197260521558219875277556445677044497544716476206694360710219702615174189878022577786029764475420860678756638328034875023018730455040000000 (BHE1 29) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_Dp cHE1_Dp (by decide +kernel)
  | 30, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 30 3 118 73 25 11 8 10 36 27
      64496778902831578218383846499349967696103945274946133678684521022578908084903473628344498355536019014527563382367447596403281995569406567770613822423254836695714288238578146762673721222460579954376120280614555982555669975682289245562029123182845954933010132929610684873943454214548119316245753392681123502309349243811679612373565440000 (BHE1 30) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nRp cHE1_nRp (by decide +kernel)
  | 31, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 31 0 118 73 25 11 8 10 36 27
      64320072972190509797001434931146162607688469566378102818918764494485591616562802837994724129157096623466081023925119225153874841214646799782331012132202892762796557524443196387458290152852384456914940559514453889507681970289029607679992136584815108371911436150495946663605274646051820854265731175488402069803988240134278720121733120000 (BHE1 31) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nZp cHE1_nZp (by decide +kernel)
  | 32, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 32 0 123 73 25 11 8 10 36 27
      1620055219542992347556285489130597721404353444301036109984029399892384653446873061473579397677715116126985137552599613047435750948322083500391398816174306141016949632937708799157835247842173571823327227862659542226385109525251361758288590069363619976735153014661185159345860879346133799678705839735935325921852090869820774730453483520000 (BHE1 32) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_DuP cHE1_DuP (by decide +kernel)
  | 33, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 33 3 119 73 25 11 8 10 36 27
      133977456726026237977152274793886174964088347646199483326011263078263613044170414120936879399115145181493340834317719483695223098381561738094567952227454934608611452348980013284272211080263178901300284045049924723677972396023548984829329560482658811514788882418697973492774294793121148129653466316788104755908828145849921495577395200000 (BHE1 33) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_DzP cHE1_DzP (by decide +kernel)
  | 34, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 34 1 116 73 25 11 8 10 36 27
      13984930163681888774907204682790658737383733272571064594652399208269145491433359157162617907253087107648412755503991070908987259889723965816678488233496249755379972232316364981413956210193463184229513567528202979157273049097673979322991055360459962890356803942802580700960421396768894824961314078057082939064293433244194627743907840000 (BHE1 34) (kronHE1 116 73 55) rfl (by decide +kernel) clHE1_DphP cHE1_DphP (by decide +kernel)
  | 35, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 35 3 121 73 25 11 8 10 36 27
      650554783236260043028099305680837515468805746227994832138674298487107857663917556372751477657664255388663142052854062193200112982080525816049409107878167579221660062510121930668021205898798446741588459253749699835444736099516046262288214938148576967461896748506730579325922357544018945049693945924892260368474965855029522510611742720000 (BHE1 35) (kronHE1 121 73 55) rfl (by decide +kernel) clHE1_nRuP cHE1_nRuP (by decide +kernel)
  | 36, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 36 0 121 73 25 11 8 10 36 27
      524789678903941976214643953396799031244289943200273772774710973996804224807308095004292685210392280214780951146725504151815955356665738211659029432792394823669633740495967857545119345915925986959597344366270083984556550247589543469900532415151647897975267300392079950010020900930623876415186985670285102047574017472554302064704880640000 (BHE1 36) (kronHE1 121 73 55) rfl (by decide +kernel) clHE1_nRzP cHE1_nRzP (by decide +kernel)
  | 37, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 37 0 119 73 25 11 8 10 36 27
      130656058247188305913946311904596015723933628387761133659627345145214077040608005403112839806246032637683358121893240259579261177986036011063015719794531724434253958624204052662517763218610903485726679260938752662297478449947431398397847594464791783649533016983332966218529337648604758019446438673176034247377036976039140947824476160000 (BHE1 37) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_nRphP cHE1_nRphP (by decide +kernel)
  | 38, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 38 0 121 73 25 11 8 10 36 27
      604384838678597300454496939890342886787827989030375239325855229871173838776133892253127204924969214484223100460416259452980420581491712065455972705821113475805260790125572117356571441527207773683926697267509268174132404392195964014710549998406091557903467080000565397011590066170012362726437442855419598069044265159457833712122593280000 (BHE1 38) (kronHE1 121 73 55) rfl (by decide +kernel) clHE1_nZuP cHE1_nZuP (by decide +kernel)
  | 39, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 39 1 121 73 25 11 8 10 36 27
      571080425819539692345965668585067834133538921455599235461506689960670961096152128581397703530145093476031526577773777784095507265275463844131006965184941283488675627112878902403816368576953643102801278838213025785686413150237920232856545781182118494979473801068307589027426552824300238596597189782728228276681645986907856060725329920000 (BHE1 39) (kronHE1 121 73 55) rfl (by decide +kernel) clHE1_nZzP cHE1_nZzP (by decide +kernel)
  | 40, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 40 3 119 73 25 11 8 10 36 27
      129323668524172948219664206393310804264756702716586609580460717205647087683043814364352294835187900576386848098283095444840483329211551631471067759154142263403866771452331071372230357279698303774922699537073079696480494016495409067952303059871017107073277641144337691789585452268481140726972570737291275958764882287440783993439518720000 (BHE1 40) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_nZphP cHE1_nZphP (by decide +kernel)
  | 41, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 41 0 123 73 25 11 8 10 36 27
      1266582218950621893501404747877610343984269010716820164678574045447234521912391785180986756704373218552872196997080924608303416411590487438854790833256262158458011594936502136911278934010095463842761175216395881504990314810182804956242962331554844916416173344567893034171094881836029547304609531199007561932939553530458951250786385920000 (BHE1 41) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_PuP cHE1_PuP (by decide +kernel)
  | 42, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 42 0 122 73 25 11 8 10 36 27
      988473909670918993497273772487781640882104948855457588999682340573411911798400681859084156296658862479431493218585267302112925319927936923089474748085780049810785447843602833703776530843571013892984511627768173456730421796105872562732968731449506644356564843850341767458429017309696918836779827443289770370480890486197615656771256320000 (BHE1 42) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_RD cHE1_RD (by decide +kernel)
  | 43, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 43 0 123 73 25 11 8 10 36 27
      1699920384201591824226168952022047463989690181455228311690428972320059001334365508573529431919255006936517211837286576328534915741088715264269089850840071713608328999005617481094140667928204605371100098607780795999989584349470928097893467793596616418957527971162686428207881574704601404797777658675460357737732197053791242542739619840000 (BHE1 43) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_RDu cHE1_RDu (by decide +kernel)
  | 44, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 44 3 119 73 25 11 8 10 36 27
      130215063993887577453502027434984734254357622469387674029424060862969532031460070029348523049637967372435532331701002138090839180548754320459497226608863879834380120641207743042632046712865146865248887436227575469913584651467124369459104469312559407735966562269495997493631469429233730232240199291362240622789554539020693624428953600000 (BHE1 44) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_RDz cHE1_RDz (by decide +kernel)
  | 45, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 45 1 116 73 25 11 8 10 36 27
      13432387720287077316481806178037891194235450574032685550967556236671669035411841778859094197077478585547819988731658583828020362894307402750884994047263099165583648719530425002533780658124138916101882249101430262351016695033304663937009536188365483074242899182191738042651519346742320173270380918250212828352312824903615734748282880000 (BHE1 45) (kronHE1 116 73 55) rfl (by decide +kernel) clHE1_RDph cHE1_RDph (by decide +kernel)
  | 46, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 46 2 122 73 25 11 8 10 36 27
      1284085325408966139502881050122744441003245844693122043636905059242682924312736544048523519465305280311479698014008140521626445389678112667936961549988581140030278880305110176865073221803339199322468147896057752421077010651018727104210037442194636578783508313339294316032391996272826632345941279893433561026376277960508807175282360320000 (BHE1 46) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_q cHE1_q (by decide +kernel)
  | 47, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 47 0 125 73 25 11 8 10 36 27
      6835548498045817743447470155053164166313331483002000024714382498172306293113505218020096109608901863001303570045503373072086362255909734214563539730463343630581745754467856725771678847724005743699532784858113693567028113317595620207424699803620708523674771915983831808783626885869746547550061443587969198372560167769754943070960353280000 (BHE1 47) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_qR cHE1_qR (by decide +kernel)
  | 48, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 48 3 120 73 25 11 8 10 36 27
      215984426460810060748925146490362603735318744811133444068459862669729496518881865563756155822774813938021118150074311582796547638863330101074229465830467352983759061275918222574563624630010372538861606807786651213563622361946927077392349919424141112443371466217443211584218782616921880862046286406456409480913955851573987429329141760000 (BHE1 48) (kronHE1 120 73 55) rfl (by decide +kernel) clHE1_qz cHE1_qz (by decide +kernel)
  | 49, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 49 3 116 73 25 11 8 10 36 27
      28584064752545351546327921776225705869811947835181536611928137765009072233835834577267305913246213042362562442569403020733777356326104250181835314804540222102222309108158707448275112585589777511767786729554517786617564912548479058693514720980194970459615394216605968663377385329510746155064007683212055666551135561476585792995328000000 (BHE1 49) (kronHE1 116 73 55) rfl (by decide +kernel) clHE1_qph cHE1_qph (by decide +kernel)
  | 50, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 50 0 123 73 25 11 8 10 36 27
      2168885216525510390496921149314756840325336495625235332111950514596907488740090829167636652216272191709092393729462403099298447359386345556760252096767471950467364967849471675743518556795975817077454418554504862717633034306869063621227323482312849278983905122432913260585521107166451551248349079420998540345982319322525935993125601280000 (BHE1 50) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_P2 cHE1_P2 (by decide +kernel)
  | 51, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 51 2 116 73 25 11 8 10 36 27
      22191294142289776027693127788737782569550984396267874661733045137952924602890411133325199016336395796533248226670780018261070386153102339637262409356532002413486698106478116681607598373596961748456146801037467041510942500861583390316409492860308227318466385617886201542037130202813095225247860553259548426929557297669824953681182720000 (BHE1 51) (kronHE1 116 73 55) rfl (by decide +kernel) clHE1_E cHE1_E (by decide +kernel)
  | 52, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 52 0 123 73 25 11 8 10 36 27
      747266191081929749851855248469789133128953501025127230661270218141328500507575817504254269672609466265162224537389199576795961601996686572869330684214323714353690066525958277528061176336129573091850577430109803996514704978382400551152011473156590710638498941982055180868840859732781312352019039628527811673692123728357390920942878720000 (BHE1 52) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_V0 cHE1_V0 (by decide +kernel)
  | 53, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 53 0 123 73 25 11 8 10 36 27
      758782825016789772199069161285453164333660584567145292058365661507480560178100398154215548032437077259204388114370132527280753293236032099744513845458726464154079706004654250395593738463279560043916111598409321222750252986539493856443237883982075865562503729617598593200552753336917329593089658632657704759552999081963483300594974720000 (BHE1 53) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_V2 cHE1_V2 (by decide +kernel)
  | 54, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 54 0 123 73 25 11 8 10 36 27
      747266191081929749851855248469789133128953501025127230661270218141328500507575817504254269672609466265162224537389199576795961601996686572869330684214323714353690066525958277528061176336129573091850577430109803996514704978382400551152011473156590710638498941982055180868840859732781312352019039628527811673692123728357390920942878720000 (BHE1 54) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_Vn cHE1_Vn (by decide +kernel)
  | 55, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 55 0 123 73 25 11 8 10 36 27
      1285602828125576313682808275919506038211252817922901955652092227947187093008235416612776534634272538196545061464652074812975097525479707591870050712260394554829486365721340415120348348160982603521811681900559001677430601317659545685693397214145343532216129878802295904944873509503798557675489973047157166682328467606133699253161164800000 (BHE1 55) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_W cHE1_W (by decide +kernel)
  | 56, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 56 0 123 73 25 11 8 10 36 27
      2233869495468540892279928312844893423088965140069497472059342164703747332229727781421960950237111737214870050230604864279458668908551373047544499623471954546724071530613172359385106748358268399537473967727548759533923994493728037055798177055486814521462279461224645251919915941751817226156855689627243788989013259783541290551242563887500 (BHE1 56) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_W2 cHE1_W2 (by decide +kernel)
  | 57, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 57 0 123 73 25 11 8 10 36 27
      3861226087661781928108313226264521972652629462523327591703933230994310139991417246323401298386248823537651346337747031768044807129123723121614010430635137064463860126503794893909025239131320972453134672769671964944002024287722215130625563909762148900952837282817449490692770597745947774293657043169994375410456117635664914237926543361250 (BHE1 57) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_W3 cHE1_W3 (by decide +kernel)
  | 58, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 58 0 122 73 25 11 8 10 36 27
      902724502926699121938226063571148729600217847918087053072771616974269557044220613372877948069902916754451323677462964037228965217544589417916212216901039595652814790250291726755824166113909003296822511489156080663463598115376967116681611199976308217124021068611005361934264554520755953535650993066456368747202139987769093556304609280000 (BHE1 58) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_R2 cHE1_R2 (by decide +kernel)
  | 59, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 59 0 122 73 25 11 8 10 36 27
      990255082115136546644055816688869068008892850008519453903336777431978627780205111879830467532757378122680518763326036149266355442100984619537959111634829308489842630810764213927712272102613333928922082553593497412256434649377446115701564767864517980892822231950475680817033158186031019619456781142613782850873492704243785049424527360000 (BHE1 59) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_R3 cHE1_R3 (by decide +kernel)
  | 60, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 60 0 125 73 25 11 8 10 36 27
      7487506509089602340026128174822452464284554490632665218513016359173592264537045886556003627812809500235407325458327965921865134203073585430488642978666516681283114220005129874527118822130626034713796569547840543362132726760668909622510421333061421585619607469292576352945661104557624681755585135661160517812383933501367097718367846400000 (BHE1 60) (kronHE1 125 73 55) rfl (by decide +kernel) clHE1_A1 cHE1_A1 (by decide +kernel)
  | 61, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 61 3 120 73 25 11 8 10 36 27
      227086019470720105840501527998968051730785354404878374923826744658875118868498974792641324595796097739697986540367726295308284324552683684467185664175932751987378710427154551660748587731835456782052894493715563646190332160239173947346557262509420023586704079204756635086207093166423754073509550208573137542467871275420253807947284480000 (BHE1 61) (kronHE1 120 73 55) rfl (by decide +kernel) clHE1_A2 cHE1_A2 (by decide +kernel)
  | 62, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 62 0 119 73 25 11 8 10 36 27
      189092592979846192567640139846130351301399775356989106420864930282769336885335627529321049181272303397489521769796976166128977457421517368190810213777493379548804531849987315507762522423531679985762581609474812845705716600193147096213449583197757941820119237540124569315359021807193273604960569576011452863005500431572820909809991680000 (BHE1 62) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_K1 cHE1_K1 (by decide +kernel)
  | 63, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 63 3 120 73 25 11 8 10 36 27
      277742069881378086318642260620467285347403658361689649541151732554436603587198858433690682518636389932772081921616604518691395543443313495131845673905542353864500496336835039794812958653449263879196939908132445324019490790740264556452231939779887707221567495788716225479245800511082612665934490737844603010483118400409341106333941760000 (BHE1 63) (kronHE1 120 73 55) rfl (by decide +kernel) clHE1_K2 cHE1_K2 (by decide +kernel)
  | 64, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 64 2 123 73 25 11 8 10 36 27
      3626621044128276754708869799084713976563400236552404101700620835247356737292644449956024567691395980924995761145839898418363507463939341069343265921672095441444405681893015786958657709303791739123066683149437521422118955499089562616390914832165049142362141131888768409498328397378269968021693603611180068368727022434559882429254860800000 (BHE1 64) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_K3 cHE1_K3 (by decide +kernel)
  | 65, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 65 0 119 73 25 11 8 10 36 27
      220545635082188697353400978641407403888448358737921936010708151899738266534570071035205444483839682576461615996603382787853795141165405556569362970590717917138689853172780756925873032833370595628546537230921192120378745249494525306219268672306156441084566441213030218421202423783050940174711494541146084430207115784818325927797719040000 (BHE1 65) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_KD cHE1_KD (by decide +kernel)
  | 66, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 66 3 120 73 25 11 8 10 36 27
      337592024258491709770058587826293689461110181804051697909635012211913756267808193166325477278507681233662853806277268546764108938565720569575707761343445016136882921574819020973561413176827976500297167450037518664030402804486783461720698408789583031633210361400095777538297751952908547436522469933239410783691714034769013006086963200000 (BHE1 66) (kronHE1 120 73 55) rfl (by decide +kernel) clHE1_KR cHE1_KR (by decide +kernel)
  | 67, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 67 2 124 73 25 11 8 10 36 27
      4743872969317088706326794448186415061802983980368043009999319232765736121249164422003246405829972410748850636952765184141257722251167729412881301063305548521624168589869045105022551034352952217926599215431677060656390893067972702885337657602610379862617733802247346369478320490484483276484656463243334172073588298244295974392682250240000 (BHE1 67) (kronHE1 124 73 55) rfl (by decide +kernel) clHE1_KZ cHE1_KZ (by decide +kernel)
  | 68, _ => by rw [xHE1_zero c (i := 68) rfl]; exact (Bd_zero r).le (by norm_num [BHE1, BHE1l])
  | 69, _ => by rw [xHE1_zero c (i := 69) rfl]; exact (Bd_zero r).le (by norm_num [BHE1, BHE1l])
  | 70, _ => by rw [xHE1_zero c (i := 70) rfl]; exact (Bd_zero r).le (by norm_num [BHE1, BHE1l])
  | 71, _ => center3_fullN hq hc boxHE1 (l1HE1 28) (fun _ => rfl) 71 0 129 37 14 9 8 5 36 27
      47834884316007366514710390827141909056247197529154234916542103802407984085589703716965365859903507820084146323974520578972347030084068806794468413262517742892203982563350372956891322394333781733012029615515798159953099748338049650562216420357787671704849251083839316479703000964440975522015003522729942892111187804867539538673873715200000 (BHE1 71) (kronHE1 129 37 28) rfl (by decide +kernel) clHE1_r cHE1_r (by decide +kernel)
  | 72, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 72 0 123 73 25 11 8 10 36 27
      1516057023259478375669851355337273078112202896932958724797061426288990561751599198001060591276009424093684262530900373107990930757935805945119163008674007099991308776505197974334329323936733409074801180596836922742816466476092506122056098793535955721646564680358717444864314031430396587827497846482051853445699630701112834913919303680000 (BHE1 72) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_P4P cHE1_P4P (by decide +kernel)
  | 73, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 73 0 122 73 25 11 8 10 36 27
      1081824941501827891014873806461359123222926003322897945485556269856410660154198628264872655625017125931750180464408256160086148905431369443155303967081799744452396345589935872991459320304905039578416373650856818780146387093999223667554438831031479850797755230888276641608418920960191165560409578564975590379387035130494485684520222720000 (BHE1 73) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_R4 cHE1_R4 (by decide +kernel)
  | 74, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 74 0 122 73 25 11 8 10 36 27
      1549419473222796968576250616973679784572147359458103506747608743204503735467846112691882769864204502389615389954400051709135648295232497931290255018821615631766427966543069707596116538555176086445605871066325430394102106268093520020708766528889635554824311272495010888048494010653547911010040798669837830616087187761592654481189765120000 (BHE1 74) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_R8 cHE1_R8 (by decide +kernel)
  | 75, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 75 0 123 73 25 11 8 10 36 27
      3095069443489300687252053722610167379376748895572180738105551594067687815119509134731141860808689702945052439443362679531158348386947736640054404688909665846035487153811668400196191583235690789625390012461475402172390635924314368230076737699161619702721818995630549005812352579467188137389940151157917763748739961375355204724777287680000 (BHE1 75) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_P42 cHE1_P42 (by decide +kernel)
  | 76, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 76 0 108 73 25 11 8 10 36 27
      371155873588935572776919238035533072700998647842011713063016251961836302630847024465290273535868475936396681840181178032100096102654971332268915691991111573304483668936290075646720387012109091812495554028815218323711618619923907857634141219308592101875676364564730269128399118927335159395449048772287280669161786711399110037995520000 (BHE1 76) (kronHE1 108 73 55) rfl (by decide +kernel) clHE1_E4P cHE1_E4P (by decide +kernel)
  | 77, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 77 0 123 73 25 11 8 10 36 27
      2591548071366030484057110383146738665421302325634678430170423849603936234941840741422769911823701843060067511975296798306284601721253402764212604668430763345487454883980259767370447523285036691681869980829642639487294708490883823454001308797311955894917017946027585780452179234844290240797171857254130994357072709831332983852719144960000 (BHE1 77) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_PP4 cHE1_PP4 (by decide +kernel)
  | 78, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 78 2 123 73 25 11 8 10 36 27
      874394079638041782647244756436024544213062843305617127269321673398787990626886722464979585585920151072361430643368707250979471964087416246584466028386812314433775318662764833497572756946958045144656919216372617072363045933247912948498707933657258496023077010667241675272029204461381366655562486844553593823715676101380309150628577280000 (BHE1 78) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_QPP4P cHE1_QPP4P (by decide +kernel)
  | 79, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 79 0 123 73 25 11 8 10 36 27
      736106934729800355975895398581589020201072049919261031595945508639026887028360775942483465705465291660244061566339253331623745265473270009938961281986581461140448014922887786745382007712385038136337939616300226399551274254754182320206486799691103063217177781615670485920523329764295642341602503859862946606442972833290600735351767040000 (BHE1 79) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_V40 cHE1_V40 (by decide +kernel)
  | 80, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 80 0 123 73 25 11 8 10 36 27
      736292612062959383969818190125212593656578742388326939335496037867197596397221363933500548892206273564603964826729246082574470795100075094716353486696834440611561569189883955658471527001409925700167788395959853311881968292396213719150816247139660037645712141189908581313454203472713363555743135732280044044257041728729271117021184000000 (BHE1 80) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_V42 cHE1_V42 (by decide +kernel)
  | 81, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 81 0 123 73 25 11 8 10 36 27
      736106934729800355975895398581589020201072049919261031595945508639026887028360775942483465705465291660244061566339253331623745265473270009938961281986581461140448014922887786745382007712385038136337939616300226399551274254754182320206486799691103063217177781615670485920523329764295642341602503859862946606442972833290600735351767040000 (BHE1 81) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_V4n cHE1_V4n (by decide +kernel)
  | 82, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 82 0 123 73 25 11 8 10 36 27
      747378866247882256878543483043920835206690022970455075858448807205907632327179141521065689105865831517625627977811159667503117277626423615373972772763539303862153041979060177800589796570506261053632613061494618407625549039854032739627522712762521998352724962939430405189804483053499439625390717822800487843283133437316371451876474880000 (BHE1 82) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_VV4 cHE1_VV4 (by decide +kernel)
  | 83, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 83 2 123 73 25 11 8 10 36 27
      873897969126459171958351835096194122850997485758901634390872146413476484667858109927518459956361634979748397128312711550748985947514149448317811046474483809809018738559032504682869508662388891573178705874402973146579573426859034499907891088183929480484678712950000637299986868941847995337553076180555688397295353220038242421492940800000 (BHE1 83) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_Bm cHE1_Bm (by decide +kernel)
  | 84, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 84 0 119 73 25 11 8 10 36 27
      45995081073084006264144606564559527938699228393417533573598176733084600082297792035543621019137988288542448388437039018242641375080835391148527320444728598934811521695529204766241656148397867050973105399534421307647211296478893894771361942651718915100816587580614727384329808619654784155783657233394175857799219043141864941032570880000 (BHE1 84) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_lamv cHE1_lamv (by decide +kernel)
  | 85, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 85 2 119 73 25 11 8 10 36 27
      54618616983599572397729121518479666810376928466126627221032481683916609374180891654792908686892349461552269856145189906238148333006466753439900460380938332704322268503755876477990732981679367531216519956563730423641201100827819449053468659793442802620737797968175118771191992538168896738991472552606797363370221846328668449836892160000 (BHE1 85) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_EN cHE1_EN (by decide +kernel)
  | 86, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 86 0 123 73 25 11 8 10 36 27
      764838273761956816714507640933571707780844381092252870751771916850565009509317990290335114259324268653916719495706916178915206862798929977537807102317473787662297784346286862027805766931104709357029712934106951168698185513508689318245561348679550696788374878279726483418867176770111268570792839647636655872319679440492547894033776640000 (BHE1 86) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_N0 cHE1_N0 (by decide +kernel)
  | 87, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 87 0 124 73 25 11 8 10 36 27
      794882785522483908761811410348125269217537307922631983129146282557534612757209130290086407043940040371226656611470215932507253547166262079552136617868507983451016907046880393223169877221076623491200649535208633881295117976508329589022720886810109084796218911574833909584771433368846183533385058335026822869988066175905832889850265600000 (BHE1 87) (kronHE1 124 73 55) rfl (by decide +kernel) clHE1_N2 cHE1_N2 (by decide +kernel)
  | 88, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 88 0 123 73 25 11 8 10 36 27
      764838273761956816714507640933571707780844381092252870751771916850565009509317990290335114259324268653916719495706916178915206862798929977537807102317473787662297784346286862027805766931104709357029712934106951168698185513508689318245561348679550696788374878279726483418867176770111268570792839647636655872319679440492547894033776640000 (BHE1 88) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_Nn cHE1_Nn (by decide +kernel)
  | 89, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 89 0 123 73 25 11 8 10 36 27
      736464611891258390103582350911216220841536396846923773368623888062654195697717503635469215386520712327099552230250411503787658884894116567769378846550480657208620832725060806470853761615686908754330443247760446616096103379378821867569573300748048327402374546099348273665949341634533945138666935888233651747757017654566493360645734400000 (BHE1 89) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_Fv cHE1_Fv (by decide +kernel)
  | 90, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 90 0 119 73 25 11 8 10 36 27
      130689525916115830301643160497898075581790870022997436578835642894957494600270458844124164571804519167243297871491305030570588717587254378961836791509963271325185587603867840467918912478602954523701188551210960289928110661031079997733303678978141394095133047266995421732065122145426701697165756872651936247723049084797986135993221120000 (BHE1 90) (kronHE1 119 73 55) rfl (by decide +kernel) clHE1_YDt cHE1_YDt (by decide +kernel)
  | 91, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 91 0 122 73 25 11 8 10 36 27
      908288775020858109150526084780229284983777149421251807941037011061467323884543271166596244307419287409826261069554912976758645943340541343124384838118862110854882672623589307223195830171908125428440069438568791556758941587998852320105114014425591373988959714185762655723996714347322209242021851661711273146117794529478208751759523840000 (BHE1 91) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_DtF cHE1_DtF (by decide +kernel)
  | 92, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 92 3 120 73 25 11 8 10 36 27
      214732326683037781559247183707407567623083732602910321030307304945194958747125174952492078344307504238965442136299495120261839715716238097605069671350932048949613418849031176973769399474030308879666267368670243650909251887602879505480359007597653893626010595088586073015574460273482225549320095417618455116423141955640006259227729920000 (BHE1 92) (kronHE1 120 73 55) rfl (by decide +kernel) clHE1_YnRt cHE1_YnRt (by decide +kernel)
  | 93, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 93 3 118 73 25 11 8 10 36 27
      64847943704385548594794886716832005917984492088568120202668032706512378751967045901729316019093216377384950819179898997360614367328887013196731991723954590254816008430192065978607899009352377562243321897574390995981175216975931350676798574821798493036403441523243130731103692891128143869339460521699357489576880460017385990206259200000 (BHE1 93) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nRtF cHE1_nRtF (by decide +kernel)
  | 94, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 94 2 123 73 25 11 8 10 36 27
      2197659079233564194819410045073498118607203933075911491919190775765757981213739338028230388673183674974039651733856327505455030793616513138047323470296231374593126098213991850143768322422597229079017824372864481363265989809987420831612083461448696824347312395171485307181186922152053138653602713572903244793482765581898284309673472379375 (BHE1 94) (kronHE1 123 73 55) rfl (by decide +kernel) clHE1_YnZt cHE1_YnZt (by decide +kernel)
  | 95, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 95 0 118 73 25 11 8 10 36 27
      67321069968191599875558715338229408307269033769967352906741077545944594466443747915282111310716487814362824070533457524204142338781371716796507435620198042954934416831291465031398116000169352569945018865125512062990699212211094492535349606136618634133799735214304619914085136595060650650406160615999742164048496447031200777345433600000 (BHE1 95) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nZtF cHE1_nZtF (by decide +kernel)
  | 96, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 96 0 122 73 25 11 8 10 36 27
      908288775033359640179684061417291047436162066535670753318724758449825367133004396077251663334756627131916908057598163269746741256991750938060204128044577468601590600691285039313938899000566216360796282483493777068431139439051390255935849938968053307265725760046370150947609750100880135060475446814760236966368975034072003284199014400000 (BHE1 96) (kronHE1 122 73 55) rfl (by decide +kernel) clHE1_DtJ cHE1_DtJ (by decide +kernel)
  | 97, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 97 3 118 73 25 11 8 10 36 27
      64847943683454443670653843991773901190796948233361992341199806790284168901895162452517787485199990831137645917718551566668091556963693858478133413885627203256082000957378608548872501747870389198946361145010496070420889514686162190590397084096445289500111503000296304492429048271908732396030828827327020202760987972361145276086353920000 (BHE1 97) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nRtJ cHE1_nRtJ (by decide +kernel)
  | 98, _ => center3_fullN hq hc boxHE1 (l1HE1 55) (fun _ => rfl) 98 0 118 73 25 11 8 10 36 27
      67321069716799586027555587835436649376605005473771230935551096546876639783719738407424597864890528409408215178537495955205968971740871519092588584966353944329919219471750320941525960435841576353327537524768875417979899110849560631013861595602836186477215270720589292376272914090859856491993635748998378599768023746297617108214743040000 (BHE1 98) (kronHE1 118 73 55) rfl (by decide +kernel) clHE1_nZtJ cHE1_nZtJ (by decide +kernel)
  | n + 99, h => absurd h (by omega)

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Vn`. -/
theorem vnodeHE1_Vn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 54 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i)) :
    Bd r (XHE1 c 54 - xHE1 c 54) (EHE1 54) := by
  have hn : ∀ i, i < 54 → Bd r (xHE1 c i) (BHE1 i) := fun i hi => normHE1 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl) hn hE trHE1N_Vm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 11344893912585649625541543436836686109765846730446693483699390411974899190811144935556333366401653648483050322396575284913699600703320314492893557098666131396705719397491001268194677961763700276280891037559063074159324234720098234810220390729088069025433540692219542719563921818304765859480523894220997948904619038087551864421744640000
      (2549 / 10 ^ 5 : ℚ) (kronHE1 123 73 55) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_Vm1 kHE1_Vm1 (by decide +kernel)
  have h2 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl) hn hE trHE1N_V2m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 22861527847445671972755456252500717314472930272464754880794833778126958861335725585517611726229264642525213899377508235398491291942665841368076718343068881197095358876186974135727240088913687228346425205858580300394872242877191540101446801554573223949438328327762955051275815422440783100551142898350891034765494391693644244073840640000
      (5137 / 10 ^ 5 : ℚ) (kronHE1 123 73 55) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_V2m1 kHE1_V2m1 (by decide +kernel)
  have h3 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl) hn hE trHE1N_eta (2, 0, 0)
      144 108 48 237 145 49 13 8 19 72 54 43937042649749459137906202411281456236167256622161793359795727905251412410097299975088283878054100973521273272439354404066307830194237284941204172642136126783691792050374892627403884528350469266079228574148255833711122832015853422290844860661639209065758054668954512013222933614592449332570155533135470630815680756616929411846857590599905410495173032062137845559550064212732255167800316602404703294458481689540634974511473648466463981537009412366879115639871639280449147366286065795281343241171115498912231073463493512100459314896907226665416493515422482830542384064053286976223814087974927226760238437347043911021856379463576569717960212480000000
      (23 / 40000000000000000000000 : ℚ) (kronHE1 237 145 109) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_eta kHE1_eta (by decide +kernel)
  have e1 : Ex.eval (XHE1 c) (toEx trHE1N_Vm1) = xHE1 c 52 - 1 := by
    simp only [trHE1N_Vm1, toEx, Ex.eval, XHE1_eq_V0 hc, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
  have e2 : Ex.eval (XHE1 c) (toEx trHE1N_V2m1) = xHE1 c 52 ^ 2 - 1 := by
    simp only [trHE1N_V2m1, toEx, Ex.eval, XHE1_spec c (i := 53) rfl, XHE1spec, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE1 c) (toEx trHE1N_eta) = xHE1 c 52 ^ 2 * (1 + XHE1 c 51) - 1 := by
    simp only [trHE1N_eta, toEx, Ex.eval, XHE1_spec c (i := 53) rfl, XHE1spec, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hEb : Bd r (XHE1 c 51) ((BHE1 51 + EHE1 51 : ℚ) : ℝ) := by
    have := (hn 51 (by norm_num)).add (hE 51 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep (a := (((2549 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (n2 := (((5137 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((23 / 40000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((12827 / 12500 : ℚ) : ℚ) : ℝ)) (m := (((541 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((102821 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHE1 54 : ℚ) : ℝ))
    hr h1 h2 h3 hEb
    (by exact_mod_cast (show (2549 / 10 ^ 5 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show 1 / (1 - (2549 / 10 ^ 5 : ℚ)) ≤ (12827 / 12500 : ℚ) by decide +kernel))
    (by exact_mod_cast (show (12827 / 12500 : ℚ) ^ 2 * (5137 / 10 ^ 5 : ℚ) ≤ (541 / 10 ^ 4 : ℚ) by decide +kernel))
    (by exact_mod_cast (show BHE1 51 + EHE1 51 ≤ (541 / 10 ^ 4 : ℚ) by decide +kernel))
    (by exact_mod_cast (show (541 / 10 ^ 4 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show (0 : ℚ) ≤ (102821 / 10 ^ 5 : ℚ) by decide +kernel))
    (by exact_mod_cast (show 1 ≤ (102821 / 10 ^ 5 : ℚ) ^ 2 * (1 - (541 / 10 ^ 4 : ℚ)) by decide +kernel))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * (541 / 10 ^ 4 : ℚ) + (2549 / 10 ^ 5 : ℚ) < 2 by decide +kernel))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((12827 / 12500 : ℚ) ^ 2 * (23 / 40000000000000000000000 : ℚ)) ≤ EHE1 54 by decide +kernel))
  have eX : XHE1 c 54 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE1 c 51) := by
    rw [XHE1_rel c (i := 54) rfl, XHE1_rel c (i := 51) rfl]
    change XLM c _ _ 63 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 61)
    rw [XLM_old c _ _ (j := 63) rfl, XLM_old c _ _ (j := 61) rfl]
    simp only [XL, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHE1 c 54 = xHE1 c 52 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `V4n`. -/
theorem vnodeHE1_V4n {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 81 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i)) :
    Bd r (XHE1 c 81 - xHE1 c 81) (EHE1 81) := by
  have hn : ∀ i, i < 81 → Bd r (xHE1 c i) (BHE1 i) := fun i hi => normHE1 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl) hn hE trHE1N_V4m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 185637560456255749581693548636573181884395624580494418374680909673285711596103373785529399257479043564887351346629039741483264179903751562524154870923878183463667794420510485515509338019165320768253223749485477195893511091880003864695717263600421604112380325834847771246391849819095849063988125556132881655468143020761678830632960000
      (4171 / 10 ^ 7 : ℚ) (kronHE1 123 73 55) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_V4m1 kHE1_V4m1 (by decide +kernel)
  have h3 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl) hn hE trHE1N_etaV4 (2, 0, 0)
      144 108 48 231 145 49 13 8 19 72 54 1676378536475216651360388339022797537164021482926621828958975154063510348111324927631007287282470303878254747733350031603292134696138258742954419035963408250928524414772358357370148928660180870215320395306162435496269405794040015648971385292711277227462607407463681675013630632906584562747757221068691445305330764131216128788600382670634936630081508825312202683925237909911088976775568386951570311814386609390345378026848465711482976366181905870260989282131413765527764535374982349982482586446844877794000842736487396303402807928879391342321477247057804139205130696835685167634462394180204315343610296261709090543428007461540996265510174720000000
      (3 / 2000000000000000000000 : ℚ) (kronHE1 231 145 109) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_etaV4 kHE1_etaV4 (by decide +kernel)
  have e1 : Ex.eval (XHE1 c) (toEx trHE1N_V4m1) = xHE1 c 79 - 1 := by
    simp only [trHE1N_V4m1, toEx, Ex.eval, XHE1_eq_V40 hc, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE1 c) (toEx trHE1N_etaV4) = xHE1 c 79 ^ 2 * (1 + XHE1 c 76) - 1 := by
    simp only [trHE1N_etaV4, toEx, Ex.eval, XHE1_spec c (i := 80) rfl, XHE1spec, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHE1 c 76) ((BHE1 76 + EHE1 76 : ℚ) : ℝ) := by
    have := (hn 76 (by norm_num)).add (hE 76 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((4171 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (η := (((3 / 2000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (m := (((417 / 500000 : ℚ) : ℚ) : ℝ)) (g := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (ε := ((EHE1 81 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (4171 / 10 ^ 7 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show 1 / (1 - (4171 / 10 ^ 7 : ℚ)) ≤ (50021 / 50000 : ℚ) by decide +kernel))
    (by exact_mod_cast (show BHE1 76 + EHE1 76 + (50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ) ≤ (417 / 500000 : ℚ) by decide +kernel))
    (by exact_mod_cast (show (417 / 500000 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show (0 : ℚ) ≤ (50021 / 50000 : ℚ) by decide +kernel))
    (by exact_mod_cast (show 1 ≤ (50021 / 50000 : ℚ) ^ 2 * (1 - (417 / 500000 : ℚ)) by decide +kernel))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * (417 / 500000 : ℚ) + (4171 / 10 ^ 7 : ℚ) < 2 by decide +kernel))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * ((50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ)) ≤ EHE1 81 by decide +kernel))
  have eX : XHE1 c 81 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE1 c 76) := by
    rw [XHE1_rel c (i := 81) rfl, XHE1_rel c (i := 76) rfl]
    change XLM c _ _ 124 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 120)
    rw [XLM_new c _ _ (j := 124) rfl, XLM_new c _ _ (j := 120) rfl]
    simp only [XLMnew, eV4, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHE1 c 81 = xHE1 c 79 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Nn`. -/
theorem vnodeHE1_Nn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 88 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i)) :
    Bd r (XHE1 c 88 - xHE1 c 88) (EHE1 88) := by
  have hn : ∀ i, i < 88 → Bd r (xHE1 c i) (BHE1 i) := fun i hi => normHE1 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl) hn hE trHE1N_Nm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 28916976592612716488193935900619260761656726797572333574201089121211408192553317721637177953116456037237545280714291887032944861505563719161369975201816204705313437217819585767939268556738836541460026541556210246342804769846387001903770266252048055175309476989890845269590238855634722078254323913329842147532174750222708837512642560000
      (6497 / 10 ^ 5 : ℚ) (kronHE1 123 73 55) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_Nm1 kHE1_Nm1 (by decide +kernel)
  have h3 := norm3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl) hn hE trHE1N_etaN (2, 0, 0)
      144 108 48 240 145 49 13 8 19 72 54 100330259967244309821335892805237273385712022956778041316180463304690998406264058538403460070119621755252385453299044006934624131617555994733104274893482918165144984157729220928551813162715185609737533213522812885211992831750799449886769724838312283807313686126099720410633143945051001722323454675313768040856441872473902298954753907626319241689821264953141424651295001839731452238335714037026374820256009324635441588474937168076954925590867500015797306143997327713789733875370584587315320326523756459007552986478112053663604305081813354698752724466402362852392047656054011749346852397128006463254373701920790089580339393788435679592344190976000000000
      (17 / 10 ^ 22 : ℚ) (kronHE1 240 145 109) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) lHE1_etaN kHE1_etaN (by decide +kernel)
  have e1 : Ex.eval (XHE1 c) (toEx trHE1N_Nm1) = xHE1 c 86 - 1 := by
    simp only [trHE1N_Nm1, toEx, Ex.eval, XHE1_eq_N0 hc, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE1 c) (toEx trHE1N_etaN) = xHE1 c 86 ^ 2 * (1 + XHE1 c 85) - 1 := by
    simp only [trHE1N_etaN, toEx, Ex.eval, XHE1_spec c (i := 87) rfl, XHE1spec, XHE1_eq_t hc, xHE1_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHE1 c 85) ((BHE1 85 + EHE1 85 : ℚ) : ℝ) := by
    have := (hn 85 (by norm_num)).add (hE 85 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((6497 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((17 / 10 ^ 22 : ℚ) : ℚ) : ℝ))
    (b := (((106949 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (m := (((1229 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((106777 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHE1 88 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (6497 / 10 ^ 5 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show 1 / (1 - (6497 / 10 ^ 5 : ℚ)) ≤ (106949 / 10 ^ 5 : ℚ) by decide +kernel))
    (by exact_mod_cast (show BHE1 85 + EHE1 85 + (106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ) ≤ (1229 / 10 ^ 4 : ℚ) by decide +kernel))
    (by exact_mod_cast (show (1229 / 10 ^ 4 : ℚ) < 1 by decide +kernel))
    (by exact_mod_cast (show (0 : ℚ) ≤ (106777 / 10 ^ 5 : ℚ) by decide +kernel))
    (by exact_mod_cast (show 1 ≤ (106777 / 10 ^ 5 : ℚ) ^ 2 * (1 - (1229 / 10 ^ 4 : ℚ)) by decide +kernel))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * (1229 / 10 ^ 4 : ℚ) + (6497 / 10 ^ 5 : ℚ) < 2 by decide +kernel))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ)) ≤ EHE1 88 by decide +kernel))
  have eX : XHE1 c 88 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE1 c 85) := by
    rw [XHE1_rel c (i := 88) rfl, XHE1_rel c (i := 85) rfl]
    change XLM c _ _ 130 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 128)
    rw [XLM_new c _ _ (j := 130) rfl, XLM_new c _ _ (j := 128) rfl]
    simp only [XLMnew, eN, PolyExprS.eval]
    rfl
  rw [eX, show xHE1 c 88 = xHE1 c 86 from rfl]
  exact hv

/-- The transport input `LRx`. -/
theorem stepHE1_LRx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHE1 c 6 - xHE1 c 6) (EHE1 6) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHE1 c 4)) ((BHE1 8 : ℚ) : ℝ) := by
    have h := normHE1 hq hc 8 (by norm_num)
    rwa [xHE1_der_thU hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 4) = dTh (xHE1 c 4) by simp [dTh]] at h
  have hana : Ana (xHE1 c 4) := by
    rw [xHE1_fam hc0 (i := 4) rfl (p := 0) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHE1_spec c (i := 6) rfl]
  exact step_Linput hana (by rw [xHE1_der_LRx hc0]; norm_num [KamTorusA.Iq]) hth (by decide +kernel)

/-- The transport input `LZx`. -/
theorem stepHE1_LZx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHE1 c 7 - xHE1 c 7) (EHE1 7) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHE1 c 5)) ((BHE1 9 : ℚ) : ℝ) := by
    have h := normHE1 hq hc 9 (by norm_num)
    rwa [xHE1_der_thZ hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE1 c 5) = dTh (xHE1 c 5) by simp [dTh]] at h
  have hana : Ana (xHE1 c 5) := by
    rw [xHE1_fam hc0 (i := 5) rfl (p := 1) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHE1_spec c (i := 7) rfl]
  exact step_Linput hana (by rw [xHE1_der_LZx hc0]; norm_num [KamTorusA.Iq]) hth (by decide +kernel)

set_option linter.unusedVariables false in
/-- The empty chain. -/
theorem ballHE1_0 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 0 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  fun i h => absurd h (Nat.not_lt_zero i)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `t`. -/
theorem ballHE1_1 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 1 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_0 hr hq hc)
    (step_exact (XHE1_eq_t hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V`. -/
theorem ballHE1_2 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 2 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_1 hr hq hc)
    (step_exact (XHE1_eq_V hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `c`. -/
theorem ballHE1_3 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 3 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_2 hr hq hc)
    (step_exact (XHE1_eq_c hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `s`. -/
theorem ballHE1_4 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 4 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_3 hr hq hc)
    (step_exact (XHE1_eq_s hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `U`. -/
theorem ballHE1_5 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 5 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_4 hr hq hc)
    (step_exact (XHE1_eq_U hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Z`. -/
theorem ballHE1_6 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 6 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_5 hr hq hc)
    (step_exact (XHE1_eq_Z hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LRx`. -/
theorem ballHE1_7 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 7 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_6 hr hq hc)
    (stepHE1_LRx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LZx`. -/
theorem ballHE1_8 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 8 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_7 hr hq hc)
    (stepHE1_LZx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thU`. -/
theorem ballHE1_9 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 9 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_8 hr hq hc)
    (step_exact (XHE1_eq_thU hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZ`. -/
theorem ballHE1_10 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 10 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_9 hr hq hc)
    (step_exact (XHE1_eq_thZ hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ue`. -/
theorem ballHE1_11 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 11 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_10 hr hq hc)
    (step_exact (XHE1_eq_Ue hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ze`. -/
theorem ballHE1_12 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 12 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_11 hr hq hc)
    (step_exact (XHE1_eq_Ze hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thUe`. -/
theorem ballHE1_13 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 13 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_12 hr hq hc)
    (step_exact (XHE1_eq_thUe hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZe`. -/
theorem ballHE1_14 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 14 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_13 hr hq hc)
    (step_exact (XHE1_eq_thZe hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m02`. -/
theorem ballHE1_15 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 15 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_14 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_14 hr hq hc) trHE1N_m02 1 0 2 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 89553497099500119862037047473702981301459502708917742951010759834987517133228563118162410053590909963000013242730058742459049439755462421483349388221987717539524718044969182814059291754676223766393024594187166279838522354383669166319379792722699437040958533692051496168688090026109333743463727837247802761299726644817341431434662819585944627745296928281004802401826365065495183236411435915395125902582713310042250520789543038705626506823193929138144446188680472519042176879331299029586988718541941235210668353176666398757420449584250045065123809808879572303010473948532839038489622764708827421387718895557277288652360585249815547516393881600000000
      (kronHE1 236 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m02 kHE1_m02 (by decide +kernel) (relHE1_m02 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m11`. -/
theorem ballHE1_16 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 16 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_15 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_15 hr hq hc) trHE1N_m11 1 0 1 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 52506401579037017428909208228761843971224951175651005572637710972770731737880515242147025852364130864185651863130032280639509838753213866276790517021092768797096463734383629620665882249854948156729727576828749650718353093054464157325180634299759464510061818672885246981533366271833997724499958029272766194374256884108989347886020134532479068377647170949298357236783300063174991438334328898946511028079197757333978248497272559858627624229779696505382880381915472137969836047314944965779406301537296806168072330470942525796285254236289125921946001285242289362178988470284091271020368923278781609714349358237208481254027439917971771020625838080000000
      (kronHE1 236 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m11 kHE1_m11 (by decide +kernel) (relHE1_m11 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m20`. -/
theorem ballHE1_17 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 17 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_16 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_16 hr hq hc) trHE1N_m20 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 106467956495813125808272526928191710136544193946956199245195972315691972768063780383321031901121834301047973406977468341298133689259816775485784979915895334803547917255431304992043882564301985202307243341445375104162338105602258960352477122051177494314000936587721539533906415495045423653323784312849997689342785001121159125884622913182602314516477982723411997419724589055500731460797569343509431809617483839663974677847936175786850087085915042629877266200633573399272866987574978596424404027215437172670696334062497276983102086022286934748261485699271289108067648628244406142199067642970163534992244118550497128266764360730440281925322014720000000
      (kronHE1 236 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m20 kHE1_m20 (by decide +kernel) (relHE1_m20 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m03`. -/
theorem ballHE1_18 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 18 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_17 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_17 hr hq hc) trHE1N_m03 1 0 3 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 27676915300498985192130716511236306261549690550980833659521528870547587126955135668096919543467784354063548257800294301486034462513480286614643529440755922395079050665372478818456159423208845418973721495394827925793733051314479574253798022676303080264902979514982692500501354728257905832632943961690586127323858960564520055666873490153954396678397384765355726502361215897475161481757065851066019418701142349918523234354093051186469763474957021472250104110852109591107008154743880853032137478871016333219395037682355513009087150975671805262511957447253423524112236067774388919968155251705551635650228810183995832718189832882565211739914240000000000
      (kronHE1 232 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m03 kHE1_m03 (by decide +kernel) (relHE1_m03 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m12`. -/
theorem ballHE1_19 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 19 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_18 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_18 hr hq hc) trHE1N_m12 1 0 2 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 16842932449011497559806980482014517886311196586288345203480908624317386953707261574207406549308747226391688242909758936083451648460176720668817408360156930554427051948192388380104056123451785114806211706099731950884659780649018758322225009915400706031945865941532395280154848782779581322914538120923493134615184941487347367690680823808468889693352062411986728797654835245867705696179377160790215053441404008905833801043484768115615364207209901967543439205786199916702118699812911416986965961781309373262167115881558955615011017790127583928392274235831015491018664529523275319572875870064478147460765336825429935156237452592007979373470679040000000
      (kronHE1 232 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m12 kHE1_m12 (by decide +kernel) (relHE1_m12 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m21`. -/
theorem ballHE1_20 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 20 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_19 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_19 hr hq hc) trHE1N_m21 1 0 1 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 18443302138293967575329491631190794888539697529827806589281153214944144896346332681317387678794421387166913675093026889894049043355145464393525824588148878693217831459362111703875130643174627291455465568902376478519303214682270820292054983970848312730838976020949668269360934242699130086899565653847383088738998245358551280256233314439768274426825733257936865921700083351733210358087222289100931547386509574764596043514684708524383759437474361880988294452984438972072449687200045866069565209760819378154739115485234084096420716249231965013438610943934834315119943850350435408572652821220574295480701371515927758275538611541804157257415393280000000
      (kronHE1 232 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m21 kHE1_m21 (by decide +kernel) (relHE1_m21 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m30`. -/
theorem ballHE1_21 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 21 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_20 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_20 hr hq hc) trHE1N_m30 1 0 0 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 38989690180193520881597685392254378005950755140800570853666613615947839513718443089515585037459038792708512575206599891186280032671699814680017782698122274100491209884030441196405174130207715663471448520435337711810531148548359924994513216461678985232385158429169259437526806197309435161146467565398357157036016408519464292391267081490316348087062972006365437613852943194058949063773674174562570652837004906428679679402909627707452277194841561714486200490448338888345645908944446836583807543105511707101535896150795585905710490930160113177543490650642710812161670105502572467187562125060155872039384445171487802854814751685156059159870832640000000
      (kronHE1 232 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m30 kHE1_m30 (by decide +kernel) (relHE1_m30 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m13`. -/
theorem ballHE1_22 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 22 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_21 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_21 hr hq hc) trHE1N_m13 1 0 3 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 3447384063541465508352638671921809089045495404182769663151079355187041559649426639309069526247116854641209942977367287334690886545778351323325569408798258582993290804117076508670577997572339543305376024544307862304454540104078836319642374200622669632048586180098338629946793154883492093712259192248329506935421733913083356394543084526589076984149881357735597462526396456131449816930953703034574789972793880967446969882678722117523214311629418468179789838076304775318138050603799732177444640068166220964421788341463822027142038208056957411423817017092209787432944186532084880516944889555303455757048415624008998990186193632650200703293194240000000
      (kronHE1 228 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m13 kHE1_m13 (by decide +kernel) (relHE1_m13 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m22`. -/
theorem ballHE1_23 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 23 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_22 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_22 hr hq hc) trHE1N_m22 1 0 2 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 3100977873949920787533219004745446133247655529156743261648600715157589778546380637507009312806974068604639775798835725831813752965235691034730332697041749351795340964492826436850423892112980653508920788101887947006551574400731438417309175891007478829384110602259255954059240259382045142450542960847282705956316727378973569285266158122962979997940793138220862911087926203330689823553778505082887129840198587157698026613425009776853158843752615267570188413408373863077334278391964414294220737659394018157696578572112733685377601690650873089925481902702986583912327591340971775048309830183679186332327442580426152724604433058313927872185630720000000
      (kronHE1 228 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m22 kHE1_m22 (by decide +kernel) (relHE1_m22 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m31`. -/
theorem ballHE1_24 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 24 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_23 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_23 hr hq hc) trHE1N_m31 1 0 1 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 4592764530273433304914140000379664060612135642474873591403692264484967337920275108558736916790405611035261585585579676766656488366861079762973315086140187229886676907838929083788451300119623454282132707093682991768877442061861771098922991284860006532462970857069442596833578202219906262166611241306294154682563952430670256372791226180821652816185695456577450726353639967690470522056849965330702591761232247253547330042899215399298729335691030625416311887516814216596315271996386924784026125999969656898150313728434400150220858547904994108850100684612707943590321210628311458841343172368965234596046079113626454282159001719534724969985474560000000
      (kronHE1 228 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m31 kHE1_m31 (by decide +kernel) (relHE1_m31 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m40`. -/
theorem ballHE1_25 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 25 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_24 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_24 hr hq hc) trHE1N_m40 1 0 0 (1 : ℤ)
      144 108 48 230 145 49 13 8 19 72 54 10826830666787619677731401604573996807119912033564915800743786140639885645482642544145721308406146923405011735048773879689857807302122608932157979616798942550105537446232736998060622146739419285197383624042664375810840674790884705300142713285924198158270461274800450984577920490011620554784957031953693675500510400017899099005573531941553811925244403032270574493926673271584627728892991664410719953253449063777862368364342962820626669479051070462913899667043144107668800322898792419386144262239890996612670899218257331191974202113808268529190844195782746076300867810651913687444678631718923711030261683765082066689411685533806617301132247040000000
      (kronHE1 230 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m40 kHE1_m40 (by decide +kernel) (relHE1_m40 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m41`. -/
theorem ballHE1_26 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 26 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_25 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_25 hr hq hc) trHE1N_m41 1 0 1 (1 : ℤ)
      144 108 48 225 145 49 13 8 19 72 54 1326756527836429653597716669728366450827858410746952267538948123052410974467571830824264921226106184323805653386228582266119011517359173098992440952042989699691306143943787429933544028970080405642918065105924791220001283827885004220725956526188348562153848077902119392227481617279337370505426773828742031069024041789902679626188410311890529570063984953984916029687645035171589025485269200582155103714835031213316328093297645890160533341107948273817148044145301833029055008200965649569608867288312112332027904378393299051323811768423185746221352424104052803069401060005263299469419736463328973964784285405016971810537891346005024099784458240000000
      (kronHE1 225 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m41 kHE1_m41 (by decide +kernel) (relHE1_m41 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m50`. -/
theorem ballHE1_27 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 27 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_26 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_26 hr hq hc) trHE1N_m50 1 0 0 (1 : ℤ)
      144 108 48 226 145 49 13 8 19 72 54 2911466155755944012582567442698306765956274837233081980007203278373717455912311825473753829918772412304648783003171481089572718212222258895941485994844825352471052581366322581687338941971635973902825360196985088955436420755435628943407323197285688070944230688537689467918260523657091661036098395455410297097968202919694460447819906111253795611318354575137625618821885950605385924585392696594211942796219355819060906270743547199742761953686854346281102801949450412408014592426228603424780873489148705218053040742053100021061008804531112188050925964898249653592534916495086665890544999361629549050367867421248034534143650395760115478419210240000000
      (kronHE1 226 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m50 kHE1_m50 (by decide +kernel) (relHE1_m50 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m51`. -/
theorem ballHE1_28 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 28 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_27 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_27 hr hq hc) trHE1N_m51 1 0 1 (1 : ℤ)
      144 108 48 222 145 49 13 8 19 72 54 550495595190634127185127238741282010682106336915125919374294104003699914477748136831416103098199845892924220289915451637998180579259869254864045446271272554391654394747323099302366420770177058699098493349325208177773507753064465115325415238465759930271178389701864693202636600621499011541523966542372901840130692997180854513240739909397682542797368828533292106545749267405343907017512256320504368565643627968389972116819456740818650004980925822315575892446456480175159381687005709079756963634619391491838589960240029568514539279642615039026439083497994868481916431583387644377135861902323369607297765958412713535568325954541865599332515840000000
      (kronHE1 222 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m51 kHE1_m51 (by decide +kernel) (relHE1_m51 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m60`. -/
theorem ballHE1_29 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 29 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_28 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_28 hr hq hc) trHE1N_m60 1 0 0 (1 : ℤ)
      144 108 48 224 145 49 13 8 19 72 54 957382569789222736881712430417921994238837707784253116249588560044430644998655723107600481294557122546127761202003133981293509254734573952023852345849529558479038240780120126970813462493811622547876549853546658964765748451181408282047812743028785410476073717451496375422378030427617369495957202774279550472369080989746687785040610971246283064129322477140221497103184217363041913688310347743181683397347274367874656573093216964902968345969182797150314842161907765475341930956379163892384132328454530219936772539111501860591127342264062501588435104174775419885136408695138202593225342515519344696431304140081612516218440236866316487203225600000000
      (kronHE1 224 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_m60 kHE1_m60 (by decide +kernel) (relHE1_m60 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dp`. -/
theorem ballHE1_30 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 30 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_29 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_29 hr hq hc) trHE1N_Dp 0 1 0 (8 : ℤ)
      72 56 24 127 73 25 11 8 10 36 28 971067776174487032715325064845640406279841122376197025070094753993646054021782356187250225055548905269109852044849645740353452915442971809795940038599134979337025689711012926460150398344623457379884040641440461300030037264818442753963578125011214644306508508127722464618105238998213972531843185055491453616128000000
      (kronHE1 127 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_Dp kHE1_Dp (by decide +kernel) (relHE1_Dp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRp`. -/
theorem ballHE1_31 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 31 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_30 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_30 hr hq hc) trHE1N_nRp 0 1 3 (8 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 990145235363723308686474644541778108184306700794335612581918216265602766596220781821044213514634707888647031007046580347451818671443533861449604393861248088745014316540190476504582423828333726845175206613060963159250432045312487496871326707095371548150819160076646814105170909582241526210015416298612321157120000000
      (kronHE1 124 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRp kHE1_nRp (by decide +kernel) (relHE1_nRp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZp`. -/
theorem ballHE1_32 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 32 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_31 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_31 hr hq hc) trHE1N_nZp 0 1 0 (16 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 2028671346412693839222393802614939484630406479385545578947202478116321126106337643905545861758067348198806278263768369910037977305529341401005945597765819366512966515419450459891987551691570675096221086690570809418644597671590527536878520464537399331225981615651943668884266258028780981927468905234219445423964160000
      (kronHE1 125 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZp kHE1_nZp (by decide +kernel) (relHE1_nZp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DuP`. -/
theorem ballHE1_33 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 33 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_32 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_32 hr hq hc) trHE1N_DuP 0 1 0 (2 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 253490539489269570827071566388545618308793272784671624589538891959247368239431178698802329510145945214976492855204332127155917580353544217723907783523716367088097267131369750067358314224660740843981494842014803594098345151390767372631313469779323753124308771018575488394350912263009716587711856074361069560135680000
      (kronHE1 126 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_DuP kHE1_DuP (by decide +kernel) (relHE1_DuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DzP`. -/
theorem ballHE1_34 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 34 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_33 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_33 hr hq hc) trHE1N_DzP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 995655484340091926541296632419452899959205824156891807332776465177723997898532422682585799968969778993078643791569972339708322720923316831069451996719316961859214275767159695374902844172464507338156607231875983907825582482825104388408904704497252822431439012824677633651706805874702214165271604241598748787998720000
      (kronHE1 125 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_DzP kHE1_DzP (by decide +kernel) (relHE1_DzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DphP`. -/
theorem ballHE1_35 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 35 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_34 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_34 hr hq hc) trHE1N_DphP 0 1 1 (4 : ℤ)
      72 56 24 121 73 25 11 8 10 36 28 505297733174846360062497018946978811855494563891673798486377473002946756333854138005110692830261969406450741122124342324880332042785725184778809753683831078954746491424605918678597016426470117768794872232320360505817454034165114226392699670660582170333168601211291912672886712821247632754852046428654882951004160000
      (kronHE1 121 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_DphP kHE1_DphP (by decide +kernel) (relHE1_DphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRuP`. -/
theorem ballHE1_36 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 36 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_35 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_35 hr hq hc) trHE1N_nRuP 0 1 3 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 988046904668100103536619860821570932708491581974024221235501253862967347233418575669989407254041270587432539465304682118690061652908429461371927137285226192999140386294525661471790973244919454706760974031692560104279361421608675327671324567925608090831515763331422875096578954278849080381806796726603863566581760000
      (kronHE1 126 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRuP kHE1_nRuP (by decide +kernel) (relHE1_nRuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRzP`. -/
theorem ballHE1_37 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 37 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_36 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_36 hr hq hc) trHE1N_nRzP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1026457696135488480346875167997459377323815498961330202075707070662119875039083380940843878567312381917831444442298145178470561390516739527895955034434277601679728217277792859233611794307021695046556240807321334519798579929704240649303117440851219432241369120402670905701303433262847617108434954996509575888240640000
      (kronHE1 126 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRzP kHE1_nRzP (by decide +kernel) (relHE1_nRzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRphP`. -/
theorem ballHE1_38 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 38 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_37 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_37 hr hq hc) trHE1N_nRphP 0 1 0 (4 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 509050732481553731568504933639252591134765502323330583458195007969522818117735174250680136212225880991721677193742300694772887820916059287290898098341591346042178412256027198043069172156879782718577405045526230656095399718870672531743441947864250275026996227535657617782470554490759229234418326365864877369589760000
      (kronHE1 124 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRphP kHE1_nRphP (by decide +kernel) (relHE1_nRphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZuP`. -/
theorem ballHE1_39 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 39 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_38 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_38 hr hq hc) trHE1N_nZuP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1009841214306393802341682775070153458811355604424583902541890445173641488735021558802180747334753517028544068934057466004618079272011501421298933238721380192641020803517451924793825889416085881232832011423060817179995323015295035100733732827356867578469911261897801466660713858009202045096148918744212414083891200000
      (kronHE1 126 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZuP kHE1_nZuP (by decide +kernel) (relHE1_nZuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZzP`. -/
theorem ballHE1_40 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 40 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_39 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_39 hr hq hc) trHE1N_nZzP 0 1 1 (2 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 244443479270760639538906032204232631398351652393992639900078423898275656773597638360788858000872378253389737810524802348811243675203594257385965788351352729009499759160002186525814939360101793423014767007970748280143085910614674597872082329562236435585802602912749678947164618089541368251762434471680352012206080000
      (kronHE1 124 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZzP kHE1_nZzP (by decide +kernel) (relHE1_nZzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZphP`. -/
theorem ballHE1_41 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 41 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_40 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 57) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_40 hr hq hc) trHE1N_nZphP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 1000139442599750921249864356830933830509747384003683530876384585835048597858806267546499862431826260985240131136604039734638444378612893153989051951836008229568622685540023411779548279613597159999244888004238080222715566174234591439755185020892114138516098560368997329421606219130533024403897732433214963795886080000
      (kronHE1 125 73 57) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZphP kHE1_nZphP (by decide +kernel) (relHE1_nZphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PuP`. -/
theorem ballHE1_42 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 42 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_41 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_41 hr hq hc) trHE1N_PuP 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHE1 124 73 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_PuP kHE1_PuP (by decide +kernel) (relHE1_PuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RD`. -/
theorem ballHE1_43 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 43 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_42 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_42 hr hq hc) trHE1N_RD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 204047896820057014842031076438486824109173355768645210182051490713737058466339702375864239587570259350273941007611993346339923028072625973643151319615578847165795792702635659981514633846994842967167292052859752369191047037936652571505748219843675901021550786479543854367754662313392229338030403685463591850902620120759189091041480242337995596303507237550281256439858126682961057824656261356907902729004133368046628597335015149290858191779479075633213515684695171696812914956673063089551338829976311345025373914811362318438133440474345953366768305140278550693834674890855106471755076941809881067509156897087133881285542834216179249644463718400000000
      (kronHE1 239 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_RD kHE1_RD (by decide +kernel) (relHE1_RD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDu`. -/
theorem ballHE1_44 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 44 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_43 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_43 hr hq hc) trHE1N_RDu 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 148127513462940358861818223212493770648580192513171956777661964255758596980259398957471661158873008513677785380108117520151654888442936105646535532675608061583759210590850311747984064437123639374104780034693176308691880706581765887377723021697726409318436737513788058666701729630375055953644224653417392564094453577912372105624256888790607681198603836558157869602362262448874974327925389241522841337009255655630590467163605390341275485829611782463354760120725904745952175097023665752722687085449057652561793104543646505599813004048012551213296936991892798064994440476773750068392876675931982443491718415389156187376991634191646589326291107840000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_RDu kHE1_RDu (by decide +kernel) (relHE1_RDu c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDz`. -/
theorem ballHE1_45 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 45 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_44 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_44 hr hq hc) trHE1N_RDz 1 0 3 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 82224562050362108811898546042605393039898798964549002054234128193525474720172790992217248173558141779782514575743675969238005737926645322095091597510178474110006343408148005913445223917185760391752235852314870426585709698754049635439525997667287191781600625589653967886730276201188290239346088757373194204758966181458627857928618119207788388969129045768936479828525985780198181272839983050834241337231558664511167577267625402329851523895547446194391743532276425027402104318265083422609857712681364821263379747539919603441442856315310604365403904912464169625620432066548696408632926115386591279639496025950538524253881424036208395577269944320000000
      (kronHE1 236 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_RDz kHE1_RDz (by decide +kernel) (relHE1_RDz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDph`. -/
theorem ballHE1_46 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 46 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_45 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_45 hr hq hc) trHE1N_RDph 1 0 1 (1 : ℤ)
      144 108 48 233 145 49 13 8 19 72 54 24277921918323127031341974383687322977799329637348930172485536477609378801798263007717502333978800194864065313174427432993146077771587722295348521899668191033605802663985040841594007548999301296553355833833795861164179513964391111811280190655615047608490323892182420165034319731683415689885087872957815511919530685033912927244195435363129671891485167504718802206011428823575294311820031507772862894541667713174393651502858973656657424698069638113848533234797414233277816181838450894775811938309103168516607886837517331389960460779997801699138964202608528566967073101705983872525478665245945424484115667896012255411484062314353596746830970880000000
      (kronHE1 233 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_RDph kHE1_RDph (by decide +kernel) (relHE1_RDph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `q`. -/
theorem ballHE1_47 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 47 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_46 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_46 hr hq hc) trHE1N_q 1 0 2 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 940936947808635460645470225980328941556499602185826170536316524389317263747850977450488222755772640653580896188316933793358469841139257877375001475532383418886864214939818376040798709920922717881465921439991000679043364483287913829496411678908822123695164087423053984800126497402695030673322548814591138402131875504138066048216845664674306814685942936067199717152026693576564972292447058079607868342235309121464835010562738747495977931356754694263349658222799197631926715585875677946525963120553613576993537576193947577047310846759513932221913564024300125733556220904802083928173273026502865897430134648457711935010154924058046532306505564160000000
      (kronHE1 242 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_q kHE1_q (by decide +kernel) (relHE1_q c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qR`. -/
theorem ballHE1_48 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 48 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_47 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_47 hr hq hc) trHE1N_qR 1 0 0 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 2871214645594995525121316185238976651192394206662994063766719997295067928054125956882520586674588243750823124217623800063486673503292718979207204537807762449532564968204406702667866042091497763461673013592514183376559590371544883563372401299201614184826240775495842629040989450732245064809724282971395837050240503412579667277342189180939328367451380396946706197482517428170251289785735136126105969580802926676466301961968021932983549690274853464015901367409352723559126233050118726346440056332886653566922119617388541628639732738054964949893380206864403522710325498238036750974348824675910636678677161191383658293499163931346833541217386496000000000
      (kronHE1 245 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_qR kHE1_qR (by decide +kernel) (relHE1_qR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qz`. -/
theorem ballHE1_49 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 49 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_48 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_48 hr hq hc) trHE1N_qz 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 529885747370252449552727732989933436653859155426829605758164750666213756481166824863532882303532984612131330888529844977209581096336959206205984321522728378805822762882160065780203170894931087717817072265952844650044171662078779423245312739395636708851722701020908579141836728150724925841541537958601280721396209897518100038537881107948755328956367306012928010057726518404857656512445099521369384991186908186107811118831996455169786897873937811651499415125213117357491907188007444977873429074259752509410276823205084827311808575203392508134933200063697705914294801344629395343459357156643318754667830198726998972765672299167455250744554291200000000
      (kronHE1 241 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_qz kHE1_qz (by decide +kernel) (relHE1_qz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qph`. -/
theorem ballHE1_50 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 50 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_49 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_49 hr hq hc) trHE1N_qph 1 0 3 (1 : ℤ)
      144 108 48 238 145 49 13 8 19 72 54 147306628574033650205329327330902443211762436164415392358480409635121935712050268983390945889898674115041458278860641990436970522233230845073575153746219531270430554867859320232429217317459820900356936648033836194972085954356209307525347002291055914152252175627412082936098881826683109068258961550166318277211963171621661585181262222082421387679918462851275007130406069918765022081433702502211850004747971863908210525029722241299780976141399762716700354386781263366754162751959571057748361761338707472994843416152441031327446353206633183937972920712522996149833977561252704774075681157483815961531267887884513966446552080345692808697641697280000000
      (kronHE1 238 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_qph kHE1_qph (by decide +kernel) (relHE1_qph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P2`. -/
theorem ballHE1_51 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 51 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_50 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_50 hr hq hc) trHE1N_P2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 4438573250059671258179633584503249639715322694635094439755348860236512681871211937510694466726777958874950579874386393324858228554608303172126726481249612807755119480417381340072659859241006253530665388816198920178298257653482117719188459691466445810737685492702610720056737290315404466410603431145183076290159378934346643119471592937908758280382127951560812716160699246801783809437847711855449138215210444483705374804117615241173396457697575039140518202422823567099691859006091537319303744158232894695232842982056182795445064991853558136960997223484227954328498585192997837342933402538588228487285132453156281841345572533316339675933473505280000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_P2 kHE1_P2 (by decide +kernel) (relHE1_P2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E`. -/
theorem ballHE1_52 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 52 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_51 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_51 hr hq hc) trHE1N_E 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 5394735824706228288663021599793031232043822884689487086465992024489834777572475566265990776698776986520595805581652714736613666028798910964695548895185056330350225722581405296812796301845969045042877776750826842891087545398146347537493046242448205894126138303429455823562527458768743424211028727213441091692182443520649405131373271995239455802341931800290164729344763590914640222781492055171792110628967910200999847180036942103446362214001455332425107862176990040303619984822108089368050332935940086335435554633667175440508895463294917391418743159050238062632723990890498409234397434689023850750629488016564785769808902163046610320923264286720000000
      (kronHE1 243 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_E kHE1_E (by decide +kernel) (relHE1_E c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V0`. -/
theorem ballHE1_53 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 53 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_52 hr hq hc)
    (step_exact (XHE1_eq_V0 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V2`. -/
theorem ballHE1_54 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 54 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_53 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_53 hr hq hc) trHE1N_V2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 16336205560218843772292471064650752077318609885840044480272847628378825138338527700395510766403410794286866658764439892663345012871013930498065326270642561916639659802789887461637995415494777758878480770733564643784952949678724812975906575718866585400065019190198918712569867861104670978349505811593855897747035530044134214693882305599279302285804619599826668687049614183386631794293925719712644470398240699936428833966764996607106660642503427382110501750125698634511622517147338832753451555382468758291682436817260610938968408238066881022020828850474579800265658329795829664499202711288610603043855848735531668058769901541967554171539292160000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_V2 kHE1_V2 (by decide +kernel) (relHE1_V2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Vn`. -/
theorem ballHE1_55 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 55 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_54 hr hq hc)
    (vnodeHE1_Vn hr hq hc (ballHE1_54 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W`. -/
theorem ballHE1_56 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 56 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_55 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_55 hr hq hc) trHE1N_W 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 177223912492763491314043295541201827151319752307521011122441067575737097252218288879456456832237759421954593480662573582469877865429180869444243091716403028628088640907268689765653788349041203384990545629932113282991898951612812337415251534453723131731845995057025772873727595532856042188830650163148733609094951781472968082251030721525624218303849935889368282140421230261281551244856658841188020875675316384014701370123571078170453877793873653278586971407540844964746852177577480041716835698300168840245754673246432413260715283308596671972134454760678198867626646412965400220177227877975009895082843252248145583387114135027150676174884044800000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_W kHE1_W (by decide +kernel) (relHE1_W c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W2`. -/
theorem ballHE1_57 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 57 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_56 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_56 hr hq hc) trHE1N_W2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 5316301434671602317257688007896876604490328904813230358908921122048530254652060782099289379049829169618983391330093173140578753122830428377955402118648435331279657929767568478933534086602286966330524645653963499180383145351233639224212767066552935709043189505097404949230143131098460412620844824981736814436081663440609488852430873450688395674492456227720572499612829577735101616377813099192882524244286112977448586869716665648423042535300987823606134852705177088230249464899678268686905111280748534038537728185343090360238126552665456962709279913636905465488128610485971327378981872889197889460258547483743835808850408680419363623350629826560000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_W2 kHE1_W2 (by decide +kernel) (relHE1_W2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W3`. -/
theorem ballHE1_58 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 58 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_57 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_57 hr hq hc) trHE1N_W3 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 20304312211514098001155930726690743016518306438823518386597871790376377790240428786212418749174024528525147294642187605677844769275149767002246200975839119711135197205149726630808991578563985416541245548295822046238516494089832111185354122863937022290672965882569586074357813462729865230000589941174594212691869353672167457998090391781336032414873208872583817794875420871669395992641463086847685252851159284202268560795448671746251010450731716650034125840514557150207728619478572279765536610690297722957164224715947527255470711063056445538525582764868359308139706135360439825519029403574606707118956992197451895743170432639609231389750743531520000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_W3 kHE1_W3 (by decide +kernel) (relHE1_W3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R2`. -/
theorem ballHE1_59 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 59 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_58 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_58 hr hq hc) trHE1N_R2 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 106467956495813125808272526928191710136544193946956199245195972315691972768063780383321031901121834301047973406977468341298133689259816775485784979915895334803547917255431304992043882564301985202307243341445375104162338105602258960352477122051177494314000936587721539533906415495045423653323784312849997689342785001121159125884622913182602314516477982723411997419724589055500731460797569343509431809617483839663974677847936175786850087085915042629877266200633573399272866987574978596424404027215437172670696334062497276983102086022286934748261485699271289108067648628244406142199067642970163534992244118550497128266764360730440281925322014720000000
      (kronHE1 236 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_R2 kHE1_R2 (by decide +kernel) (relHE1_R2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R3`. -/
theorem ballHE1_60 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 60 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_59 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_59 hr hq hc) trHE1N_R3 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 188170776922821314524702759996128912317103295493815584845218893264704871273854177684988519728864060302079588289409054966022074170053945204804621209033039113936485400326172683575126804342750065403246205611548438469848457373204984670815472524705462453189574735246222846578796205160463789322779140506544474253408067528763638101709855552050294160907538745028161248011970220439055746298854614767217305521810934037388150216517122147058966645882638719742759483211967046213793034073543983113182987968830506472015156798290167177067447741505944197689259960452405448242951245787443515694243117739326718480394056676547017258373900201510524403988530462720000000
      (kronHE1 239 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_R3 kHE1_R3 (by decide +kernel) (relHE1_R3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A1`. -/
theorem ballHE1_61 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 61 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_60 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_60 hr hq hc) trHE1N_A1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 2838494483538568367786877717359690280018140630027081134483361047924355094351209521634127087658585882503613338317549023121713515063595736032964124984360482845285335255993742253992232775910755704456755360137319700369386638721324547112955943436741058835034880290801058204260365214327454707394842322538987827322658219701646436993277619498057929869298986964465677745326270908428173563844654840602105316527962356501709438494880201498193232127659467060399032850108162684414906484604155010948787940884299236960968610923124967360437737328524413445542525445585203943302746585967926446489409833489410447953079784733742454080673282579567064266319278899200000000
      (kronHE1 242 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_A1 kHE1_A1 (by decide +kernel) (relHE1_A1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A2`. -/
theorem ballHE1_62 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 62 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_61 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_61 hr hq hc) trHE1N_A2 1 0 3 (1 : ℤ)
      144 108 48 237 145 49 13 8 19 72 54 217633264978772338835489624671400866669602715890831213142686605838496563295906542696365091367258614548981354356453818848952607421028639946257550322569858410926366526749597836330024901719408113919391163964486673438520982121344074669552279303211764382923907004311695686011723482270731679711624010815412129687315054626288937163041653773571934894070209295694154288453726887995211785978599250594294900877211251060326411424348939698784910480762668562768791045745315682295386111099923954091723957070091886916451976524568463227419818425546051799650642065796029046837121344238244742119333484671367582178108363055206552857249765765627521570085588172800000000
      (kronHE1 237 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_A2 kHE1_A2 (by decide +kernel) (relHE1_A2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K1`. -/
theorem ballHE1_63 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 63 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_62 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_62 hr hq hc) trHE1N_K1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 1327521296155095246101514354575715820458400841190189642874685950692301310434590038349838181873232162844294873188355493799023341466793173277016799570067411311882940683022949265095630116938170463761590156826312208559820143968461563063996376467643326101181524589870830912326642438133039693440349461900584477623907725834833109200714265451532709183825202664032480438323746832920826102997979992620340345052939520620631873931596259782637629447332085781039178322179229204172384158575763515064787096965273954422314320944272264196716835364407853537270077856186103760119742603208793899484776826208329947136328944254698605614663950366619355546936892456960000000
      (kronHE1 242 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_K1 kHE1_K1 (by decide +kernel) (relHE1_K1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K2`. -/
theorem ballHE1_64 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 64 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_63 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_63 hr hq hc) trHE1N_K2 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 907030127075650290088049165141609083645525559285248142689425872501305820187438949751185278576238199586351230279403675298529514616935702092528254598546873436877606431999532812346725900201243643931421968999037769296540054081701041385091493449379605917261783590272826093573891736572733606644336871801737148335274510182620379559631088900946095854902245378029107672944933148790591601448156204541499759201567440197623619181639080783010290180867422354140479723979150139460773598417446785819835797403941108495887693332274342115283740667948761829325844170952278142986689693276873849612359694191001082022440405465024900533652579371642914159545244712960000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_K2 kHE1_K2 (by decide +kernel) (relHE1_K2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K3`. -/
theorem ballHE1_65 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 65 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_64 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_64 hr hq hc) trHE1N_K3 1 0 2 (1 : ℤ)
      144 108 48 246 145 49 13 8 19 72 54 6223446326065911695737891432145474242253539400954716255484525668100950170465985483397211270111295812493112495320552136769678818129755788460058682397320488355975638907579464917731732999887009475231870598758005488981527198860313575552183444439955497239333895517112341861827934372628919120470074143609726383170699463273650412399417723463471562367711571615090146828010899364260291690283520696213341485063776317371979941492813822995666306915274254324709585508720724126734795234600523501564324599173255714653316755590332978280026520923300050533107864860937553208586777741173219333332902433409027469770555028910127141149273906595427268962237703782400000000
      (kronHE1 246 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_K3 kHE1_K3 (by decide +kernel) (relHE1_K3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KD`. -/
theorem ballHE1_66 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 66 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_65 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_65 hr hq hc) trHE1N_KD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 768206622241816641123227693619891921359183040174665554231447464066517730705931545612327807242032775119433086211759224431579543703528250322622171006904997541206085043460547615106781557628253716340548308217269984790003488677196060005063292566142522975414220106500553176353151028108645453081702525572729878309223392202376110825948212536080073359827828582065940899414325791835059477929356117224125744300421788558925726548474795833776761365107018461005811276085378846634853047179264073420739245082015512107504651275383783348790653221630273246484011599413157861174784663571779990896749022612016182291309344418327652056115308759272455900467015188480000000
      (kronHE1 239 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_KD kHE1_KD (by decide +kernel) (relHE1_KD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KR`. -/
theorem ballHE1_67 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 67 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_66 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_66 hr hq hc) trHE1N_KR 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 1389531525971459719907464934299954912620902031732032374350880086779309166752843260470438102825241423307440092488504072199992161057012434704430923294829147084986749824767686706389249586765385444332551026281087705690786101269842649879585291484826761241634429534811382076272397105715406620654808954725510819220744534958945251289788849695474433487899878737741060921923716727885109938370434379713770198209902257791897664101426762271900199105526572297518684085737441996277581859808139668248961543032268203395507183809874749785192104530410094606125646111599650760371130793109353578222029087239269242997591779977901452791157430586052375282903332945920000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_KR kHE1_KR (by decide +kernel) (relHE1_KR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KZ`. -/
theorem ballHE1_68 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 68 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_67 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_67 hr hq hc) trHE1N_KZ 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 12675486848800493939385474898761758449536305841992849924971714757187703884087690291167093080275534280696406430605451117764978931727721756774488371631830147382232863885190561723776732110586567483389351877412390769576976556442091654556203810158331567002243913962657001698334608586826631310297296060704981927167701973510439032941212968683594777927703407537944480820528924560767784184090051766509187328220510869991061825531863092390431189800711831166519766835357999839771276644333860374089116833653284227629733597507381586317980648767676113912491895754153226488341869822465943870345001077262599980224995240728762657195920339438999411673767178403840000000
      (kronHE1 243 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_KZ kHE1_KZ (by decide +kernel) (relHE1_KZ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dt0`. -/
theorem ballHE1_69 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 69 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_68 hr hq hc)
    (step_exact (XHE1_eq_Dt0 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRt0`. -/
theorem ballHE1_70 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 70 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_69 hr hq hc)
    (step_exact (XHE1_eq_nRt0 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZt0`. -/
theorem ballHE1_71 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 71 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_70 hr hq hc)
    (step_exact (XHE1_eq_nZt0 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `r`. -/
theorem ballHE1_72 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 72 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_71 hr hq hc)
    (step_exact (XHE1_eq_r hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P4P`. -/
theorem ballHE1_73 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 73 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_72 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_72 hr hq hc) trHE1N_P4P 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHE1 124 73 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_P4P kHE1_P4P (by decide +kernel) (relHE1_P4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R4`. -/
theorem ballHE1_74 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 74 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_73 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_73 hr hq hc) trHE1N_R4 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 354655187062246607627470965226749941517227318874577990514593468299395184289157661996462902254519625188964334467383684427430463759157197494756596369568121642921350638193082177569195893712837828380055354182168305145273613516909408868721140980064665116858752582995556458698138702464223504506175410544563841470823917760665548705615335737553765445440348175201647585756021255854243829341963055723906580934277890432961527399314313705385594075290830385317034921057011884591899241870366299145373595143332602238243428736923380218485814387904309310313224352573442389048936295800381579568888392649258394770288756824066776655495443445893007206857027092480000000
      (kronHE1 242 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_R4 kHE1_R4 (by decide +kernel) (relHE1_R4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R8`. -/
theorem ballHE1_75 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 75 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_74 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_74 hr hq hc) trHE1N_R8 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 2155222141184563620743345635109154255130473490966652790668999710499770132445580356520886017183794350872755403603156681634537136447577368580288038851024532896357036874368618546644240135954604760686220539755184533791439668695713108830752917619997231321832336128806228584965704174951519229414587209240224071530421952045315888364427954082969943102026030278506448307364402416889909402548854282903331125921828058787333056262371820716878252420289302700114593029925792477589794304969955447231626630466197668296299773127107518023675062314701555236225775732483337342383834785476453925363266745074964991496952368007193474408514729519198406330581862318080000000
      (kronHE1 242 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_R8 kHE1_R8 (by decide +kernel) (relHE1_R8 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P42`. -/
theorem ballHE1_76 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 76 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_75 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_75 hr hq hc) trHE1N_P42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 11818804895543410386725204843291131143144014856585389835613087263815757469120942655900410750478917619018602795807500162435102285826492371404895948396544278896471517038878687391843806323416547161974307381234081977421963377182613120060602435383752644774365478568931424388627676963829095608853984432066687033738546185492634135975075635460764171103886551529634991226494477038004715142080841946338070073944749215745390097265877302802906296713542190745497575355242488818116919766674773370443486784844472668922314637913995025798026917868792093233332509463168527599741021841063946901119130234494646250001338005712737484703436451005078047806534241484800000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_P42 kHE1_P42 (by decide +kernel) (relHE1_P42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E4P`. -/
theorem ballHE1_77 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 77 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_76 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_76 hr hq hc) trHE1N_E4P 1 0 0 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 9316341698484693651110589406904946629622945008880948680312486267700811122415194424328751833310989251199231577294885966984576539640616372517071902885009407757062560366903605119058666444625029782823857299359505505340090778645536592736945083414051040209077938061476380174609260821941388071891626266427945468856009968746852021568585753268720793870873739835015103816670269658349286026655037215301616575815895565904491992047582049827171375384851646838379409640850778748358428812437984758290407865701907631394283607372084834101293024611891055496008939092213587265151302019589238589265893183007969018744648417258716976249408410154680483472191751454720000000
      (kronHE1 243 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_E4P kHE1_E4P (by decide +kernel) (relHE1_E4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PP4`. -/
theorem ballHE1_78 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 78 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_77 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_77 hr hq hc) trHE1N_PP4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 7246684902801321204583734634007990676536344008325227322124581470923378032853274924270786884659769042699064732966247742380652947902372927001034599117310881687553715646878692924419720733452356453607803878829583174202106244081913105537590762538645764712674094604977109083761400552851642913130890835246883534107429161646690880417509052229334293713060787355550985332841048003069404526595161872850246852430388738654445793202878196963864917935646739889265909882064001824031984576309079643888216823333387918260197783546859181411155473342034964434121131409876864384215399092937073281854613585380088832703476590404896905081339332134257962850880113868800000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_PP4 kHE1_PP4 (by decide +kernel) (relHE1_PP4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `QPP4P`. -/
theorem ballHE1_79 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 79 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_78 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_78 hr hq hc) trHE1N_QPP4P 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 7717793298131031313702737715258255934102249175113951927617782024192343731604974499099043399108930702372849545792210945943330554531021206797456048815332493958533817053994338590413517769723079263930988791514949515572977022129047794319307364928789202821469464708703118199838641403712449617189557277705305536027431014570972506928786316328346720923248639837674812538634214767585996265096243804779439151962473225696817499282645460745371347033377614477056709208544273869884812804838068802933745559675650662052782614133756473990321045009305785238327223452712088253542704161143118998823623471356252790569559231446760039050682541518780992943695404728320000000
      (kronHE1 243 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_QPP4P kHE1_QPP4P (by decide +kernel) (relHE1_QPP4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V40`. -/
theorem ballHE1_80 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 80 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_79 hr hq hc)
    (step_exact (XHE1_eq_V40 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V42`. -/
theorem ballHE1_81 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 81 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_80 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_80 hr hq hc) trHE1N_V42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 650078274189216823975399235842840269154783463177671463726266759048520803558238734776873823072086094274077672363445757967245997324859863630863464398073794655841969162956844596670509557182899400150897162556750169099105958588905726588247726235101447565034789690718424412187303653521752062888573758039747943061700256349842218205424059670065625663774683667023814817286772914546674418813702384547033062338696187254969478423021810868003789164763527119213842520061000997053290114939474426232895672304235283412316113744778876292022969371405119553985269243845473860019027612170370935864930600766056764984000412291800690753380377946258053217376010240000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_V42 kHE1_V42 (by decide +kernel) (relHE1_V42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V4n`. -/
theorem ballHE1_82 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 82 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_81 hr hq hc)
    (vnodeHE1_V4n hr hq hc (ballHE1_81 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `VV4`. -/
theorem ballHE1_83 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 83 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_82 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_82 hr hq hc) trHE1N_VV4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 1139140558461367140521288502663021387317890849682600275218521040634877877513397127055636354663622233021988789664818622043097335122458195163648946843377588876465534786656863163181104803425117299739345867537144218262436295629498395014346562341204176021332631662774836891294627066985800412577247424435378178420386602998963568077609693610330872515179881259750441469899899811393463865398829178668270210292092389803748837554646994466301523906087586904599397437258559717245077426882109408243504074129248769511202686025342694712838973592926639652881157082674550613109434470866398501901921182521141775249760716951190971446260281593583837201595105280000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_VV4 kHE1_VV4 (by decide +kernel) (relHE1_VV4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Bm`. -/
theorem ballHE1_84 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 84 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_83 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_83 hr hq hc) trHE1N_Bm 1 0 2 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 31270787795913974229281538428763508857247295077728608856257507310916638944098394832662436307947722614529693334121014307636611576389854479948927595306881437845432076536565951307859237037354904627217726467648273047112907606478526945994341715938657952930435652854058990959655611185984500655030557404438162903677064871240790112088551286282632759727139394420643646696923836473174875887704853718274042826885092092066822756119484920825703123018071646753756532572114333823048478692306677727038266024865842315557719575863245913602422056648867871140567212785129358919754343589498631034816494513848309637356521301843178977667949214755907707359136317440000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_Bm kHE1_Bm (by decide +kernel) (relHE1_Bm c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `lamv`. -/
theorem ballHE1_85 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 85 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_84 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 55) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_84 hr hq hc) trHE1N_lamv 0 0 0 (32 : ℤ)
      72 54 24 130 73 25 11 8 10 36 27 0
      (kronHE1 130 73 55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_lamv kHE1_lamv (by decide +kernel) (relHE1_lamv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `EN`. -/
theorem ballHE1_86 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 86 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_85 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_85 hr hq hc) trHE1N_EN 1 0 2 (-1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 581452433949605349380721470511556011873898255795370284269476131593936478981075442459337202243196605561321987971212746752581004130912229789601047650252817930835751502330045592426720521211158672315789881397077444392580199382900310289996283039621468478467100939663468304230432113618290462541650094779493557874994725549023836073861459500782845078351432638523269354333306362105268686266787907408758566746442744166242563667266318904144615695130508147465514326438218901114457005942647697135687970443972545143385273258443962381305501611859155301191257583199236004950932888307191868061720744290206654534925063865917584016217858642941013870438609059840000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_EN kHE1_EN (by decide +kernel) (relHE1_EN c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N0`. -/
theorem ballHE1_87 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 87 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_86 hr hq hc)
    (step_exact (XHE1_eq_N0 hc) (by decide +kernel))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N2`. -/
theorem ballHE1_88 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 88 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_87 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_87 hr hq hc) trHE1N_N2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 65728734244131064445408950637506317884942711878517749668681897374327989374236360824325684215405318826320073634000508411711482092322027190627034302395485993721798147098099330912301530100068597282715537594173888189744770168777288914462846827316170696360097280180276751078641478422954435838564132909654112449274243955965286641119910460031369734172996025345244797766980934977093800278140164855536490191515508189284085163712554276010898744717623857872599880038420733187960565355524838527351509708296476560486966001043229448997011483307941035411652528332476006028018035789265483454985632046610383135597809825754841014453711958907003734498855113195520000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_N2 kHE1_N2 (by decide +kernel) (relHE1_N2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Nn`. -/
theorem ballHE1_89 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 89 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_88 hr hq hc)
    (vnodeHE1_Nn hr hq hc (ballHE1_88 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Fv`. -/
theorem ballHE1_90 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 90 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_89 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_89 hr hq hc) trHE1N_Fv 1 0 0 (2 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 19176521077726455764480889035210855028174394327200449544459638418122054167602080190465873144949003778781902897670307028123697958679923251395014744548269764246317219124373041955989656938129985722769943653755506166530845021800933084406257241059286871509322688297425351681265864200093183681163592177912695487664059969665953938920308414601254492244683849669404924354094169427589855343320017329900402962284352227187675420421937656026468198914298532086160707862763092633608578675683217947927166189454840644605293264024501979062432708965724975674652051081374102021740067969914723951392234727852249842170641631037537107855212777329515184231984849223680000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_Fv kHE1_Fv (by decide +kernel) (relHE1_Fv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YDt`. -/
theorem ballHE1_91 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 91 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_90 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_90 hr hq hc) trHE1N_YDt 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 1776339010380496497832446825650294858405811008964362262413991293401347763230478626479077814039490936407239977782095666780506315069417155780738120415817847163289868930544004291759210488254963524513999878058079577953858382085534181300066558484871812556179951628310835635716460101886944734608349325730231276923419304446912776967881252915113287817916367822723019551492443837835583524831338219088158015534005836217191793264521896795747336544360459661582383293859484211953983939757309179561810524768274747917642842918703848395572923570844205690685788482505874983724310861186665198035514653877087247366625748348371133299356350905336961038191888957440000000
      (kronHE1 240 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_YDt kHE1_YDt (by decide +kernel) (relHE1_YDt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DtF`. -/
theorem ballHE1_92 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 92 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_91 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_91 hr hq hc) trHE1N_DtF 1 0 0 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 719288141414077970608691509835408024399929197302380407687081560206105812988863270296541801731698452932227877613543840994864249385689102162712810480882079153745679080695129149168473340262418065393386742847107367434979914402732308105420455215162527146417286338343665806713176686413804951334344837379408535445511705762794995493782689971174192378923878296527932499088391985716763824453334077827131428416368374961375689901477472669199488566860634982704120417395911457439090818533075965856503899030746968793278699264070390457240804019880341312308451606631603389827465784039990075329844491679056158954365769486183024871407831520928307566674486231040000000
      (kronHE1 241 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_DtF kHE1_DtF (by decide +kernel) (relHE1_DtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnRt`. -/
theorem ballHE1_93 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 93 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_92 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_92 hr hq hc) trHE1N_YnRt 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 2662287302204646523405364152596986627042785198773029604884850593170267169380100016799323668956275627822090787608194593269451468296104764360601258384205269015708349510636976906040114850325650407926427149334252698666519688253284001930501356917788475335360000818779664529065588217331833811893154921108458130401618436019569513324808656877098336818051041997661106431689146910704924878514813926558551890438315001239394597250828489974035816705927148014149757640299312688031200195341591045744260857585135004587066596877435273035646545751128607565922643691557498391179959128227945166192356220830909914323658844562032035714485734108242370066228581498880000000
      (kronHE1 241 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_YnRt kHE1_YnRt (by decide +kernel) (relHE1_YnRt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRtF`. -/
theorem ballHE1_94 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 94 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_93 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_93 hr hq hc) trHE1N_nRtF 1 0 3 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 973832669424172966870302872956247880400201738335031458527359763105250234470187355762434393583749447691156735630599154337432703859465006174671207411573855450385681909307298251215496025898704851087831448885800741794943158051615300022593328252800100698122164808174992019563114335771733990603637670880974579370943984699073844250055452639732800726719739263970017433529970967909147332180345953651380947578390626688059247477582666431217631966360999241672586047779703411307618573325318726391708322704446070013241946557791560581737787681250882309008393110827105801725431641515801448642932365257389889880514797784814100910777794775030769741240247255040000000
      (kronHE1 241 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRtF kHE1_nRtF (by decide +kernel) (relHE1_nRtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnZt`. -/
theorem ballHE1_95 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 95 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_94 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_94 hr hq hc) trHE1N_YnZt 1 0 2 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 22787826982710701966442594844795838955211857025193981125214754442074894836873356830179144749731209656745257115732698532141358200067665438717682211273742672507305306002780723061760008339948679089169714666566215650455237250967766163402435511045529431401130779941496806287530244255820655771075981862331947352236837429275177264514516099855973881298384804269885629158469701703807416973443493305564046896421070671301388202772353551043712776910142450362324577630641868629374267914483982260547823738565347108647579714724725632866856597822021637088798003419259835309636916739898705257506768745407339826324164896445140529991547107256313255641177716162560000000
      (kronHE1 245 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_YnZt kHE1_YnZt (by decide +kernel) (relHE1_YnZt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZtF`. -/
theorem ballHE1_96 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 96 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_95 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_95 hr hq hc) trHE1N_nZtF 1 0 0 (512 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 4551154482083805840507908017869036590891354445173656454493018026743192154896069267657362614601552965416732644479074672789682531674066011915534403355046135447380827963277879249825255041290191869410459519524088652699077373736859740467170168120510904811730763839622844707339311706401898841153779923596266742696305049579755139820364505823135980166300132553277698849230362760002904177371869879927426288767335093836846567689726561321165244241706243532505164875800333592171962496686598724367709707876748064089000470655934571788994750144778995596039921511660069589577671888549969184200632504774146703750394262785846057096327076236875895854309457264640000000
      (kronHE1 244 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZtF kHE1_nZtF (by decide +kernel) (relHE1_nZtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DtJ`. -/
theorem ballHE1_97 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 97 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_96 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_96 hr hq hc) trHE1N_DtJ 1 0 0 (8589934592 : ℤ)
      144 108 48 263 145 49 13 8 19 72 54 603664118856452988137360458123624001961248317805883832982805319767188824443505892630726915908110712358847547415613600398258825842496216413895499051853248998592390666481706337450826035357705889617465913581413016694607227191631468961815399796202366591521699451754658100055723452531659409476392643504902341802323282815209279554849059260128418412451731661154131338748952719327855982108321648098132310320301899382619448033096476292985164509545624499400929300693272006416080301850752979155856265680526572276863405875946806592043674028619428216959391406743595354788236093456083214504107370521964215781557742775383452289339644308676101708525765264576348160000000
      (kronHE1 263 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_DtJ kHE1_DtJ (by decide +kernel) (relHE1_DtJ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRtJ`. -/
theorem ballHE1_98 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 98 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_97 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_97 hr hq hc) trHE1N_nRtJ 1 0 3 (8589934592 : ℤ)
      144 108 48 259 145 49 13 8 19 72 54 720612797408328076442481401171160708444463111446982092766771944790134250572896390970451684108232289870710525406741092693297150440074106358840226572374494631647574073537123906720393362775124451127703324782656446055956811318012990569835630958019549322616670848211121942449850920897128017567273547347346288041671404137214358738458412137717892173474886304242974635671513543061207285343972610196130423083839619790666719757863913926635989137393806573391131187728867778274023116091438200918142150472460712824156444397601686351106488326814766106464209574772553925432252981496840186802902363099697239716511486952345475556957580881611864648901858281924853760000000
      (kronHE1 259 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nRtJ kHE1_nRtJ (by decide +kernel) (relHE1_nRtJ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZtJ`. -/
theorem ballHE1_99 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 99 → Bd r (XHE1 c i - xHE1 c i) (EHE1 i) :=
  chain_succ (ballHE1_98 hr hq hc)
    (node3_fullN hr hq hc hWHE1 boxHE1 (l1HE1 109) (fun _ => rfl)
      (fun i hi => normHE1 hq hc i (by omega)) (ballHE1_98 hr hq hc) trHE1N_nZtJ 1 0 0 (8589934592 : ℤ)
      144 108 48 259 145 49 13 8 19 72 54 734712156690177065777869996332346261520875836727102763376991113116979097025534667243358858318572308563042972282655786795600060481158628632724742371269195482463131661643504208364570139027459449945692431283807605264561627204609190741607884929633234833562705739761949316361757515704626498519490673105111308554048998713091016489257036062367034075047190868337576588610349283006392075199982689090203970098930164568724878602452272427044046674877995979380803314667318054079812010746587701538317804336966016837827612749528426747633576383631084160804294529685709277616976972181816212428285707251758876653613396806486750357395990345406534741651473466843463680000000
      (kronHE1 259 145 109) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)
      lHE1_nZtJ kHE1_nZtJ (by decide +kernel) (relHE1_nZtJ c))

end PlasmaLean.Design.RationalStellaratorGC
