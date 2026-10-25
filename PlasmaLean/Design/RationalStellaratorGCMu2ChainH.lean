/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMu2RelH
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH1
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH2
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH3
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH4
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH5
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH6
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH7
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH8
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH9
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH10
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH11
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH12
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH13
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH14
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH15
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH16
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH17
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH18
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH19
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH20
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH21
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH22
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH23
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH24
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH25
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH26
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH27
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH28
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH29
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH30
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH31
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH32
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH33
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH34
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH35
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH36
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH37
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH38
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH39
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH40
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH41
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH42
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH43
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH44
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH45
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH46
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH47
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH48
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH49
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH50
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH51
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH52
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH53
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH54
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH55
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH56
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH57
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH58
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH59
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH60
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH61
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH62
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH63
public import PlasmaLean.Design.RationalStellaratorGCMu2CheckH64
public import PlasmaLean.Design.RationalStellaratorGCMuCommon
public import PlasmaLean.Design.RationalStellaratorGCMu2LowMemH
public import PlasmaLean.Certificates.KernelFact

/-!
# The high-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the high-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`, built
variable by variable (`ballHM_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCMu2CheckH*` (`node3_fullN`), the node identities of
`Design/RationalStellaratorGCMu2RelH` and the node step `vstep`.
Generated by `scripts/gc_kam/lam_emit_lean.py`.

Pitch cell `λ ∈ [1/16, 1/8]`: modules `RationalStellaratorGCMu2*`,
namespace `PlasmaLean.Design.RationalStellaratorGC.Mu2`; generated by
`scripts/gc_kam/lamcell` from the pipeline of the cell `[0, 1/16]`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC.Mu2

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LRx` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHM_LRx : KvHM 221 73 55 6 = famPack 221 73 55 NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 10888383889117653077957113864) ((c0HM 4 : ℤ) * 158456325028528675187087900672) ddHM drHM 0 (famHM 4) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `LRx` is the symbol family of `U` (equal Kronecker images). -/
theorem PHM_der_LRx : PHM 6 = famPoly NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 10888383889117653077957113864) ((c0HM 4 : ℤ) * 158456325028528675187087900672) 0 (famHM 4) := by
  have hk : kron 221 73 (flat 55 (PHM 6)) = kron 221 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 10888383889117653077957113864) ((c0HM 4 : ℤ) * 158456325028528675187087900672) 0 (famHM 4))) := by
    rw [kronHM, ← famPack_eq 221 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 4)
      fun sd h => ((staticHM 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_LRx
  have hbox := boxHM 6
  rw [bx6HM 6 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 6) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `LRx` is a derivative of the centre `U`. -/
theorem xHM_der_LRx {c : ℂ} (hc : c ≠ 0) :
    xHM c 6 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHM c 4) := by
  rw [xHM_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHM, PHM_der_LRx,
    show WtHM 6 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LZx` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHM_LZx : KvHM 221 73 55 7 = famPack 221 73 55 NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 10888383889117653077957113864) ((c0HM 5 : ℤ) * 158456325028528675187087900672) ddHM drHM 0 (famHM 5) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `LZx` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHM_der_LZx : PHM 7 = famPoly NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 10888383889117653077957113864) ((c0HM 5 : ℤ) * 158456325028528675187087900672) 0 (famHM 5) := by
  have hk : kron 221 73 (flat 55 (PHM 7)) = kron 221 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 10888383889117653077957113864) ((c0HM 5 : ℤ) * 158456325028528675187087900672) 0 (famHM 5))) := by
    rw [kronHM, ← famPack_eq 221 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 5)
      fun sd h => ((staticHM 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_LZx
  have hbox := boxHM 7
  rw [bx6HM 7 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 7) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `LZx` is a derivative of the centre `Z`. -/
theorem xHM_der_LZx {c : ℂ} (hc : c ≠ 0) :
    xHM c 7 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHM c 5) := by
  rw [xHM_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHM, PHM_der_LZx,
    show WtHM 7 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thU` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHM_thU : KvHM 125 73 55 8 = famPack 125 73 55 NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 1) ((c0HM 4 : ℤ) * 0) ddHM drHM 0 (famHM 4) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thU` is the symbol family of `U` (equal Kronecker images). -/
theorem PHM_der_thU : PHM 8 = famPoly NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 1) ((c0HM 4 : ℤ) * 0) 0 (famHM 4) := by
  have hk : kron 125 73 (flat 55 (PHM 8)) = kron 125 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 1) ((c0HM 4 : ℤ) * 0) 0 (famHM 4))) := by
    rw [kronHM, ← famPack_eq 125 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 4)
      fun sd h => ((staticHM 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_thU
  have hbox := boxHM 8
  rw [bx6HM 8 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 8) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thU` is a derivative of the centre `U`. -/
theorem xHM_der_thU {c : ℂ} (hc : c ≠ 0) :
    xHM c 8 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 4) := by
  rw [xHM_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHM, PHM_der_thU,
    show WtHM 8 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZ` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHM_thZ : KvHM 125 73 55 9 = famPack 125 73 55 NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 1) ((c0HM 5 : ℤ) * 0) ddHM drHM 0 (famHM 5) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thZ` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHM_der_thZ : PHM 9 = famPoly NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 1) ((c0HM 5 : ℤ) * 0) 0 (famHM 5) := by
  have hk : kron 125 73 (flat 55 (PHM 9)) = kron 125 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 5 then -1 else 1) 0
    ((c0HM 5 : ℤ) * 1) ((c0HM 5 : ℤ) * 0) 0 (famHM 5))) := by
    rw [kronHM, ← famPack_eq 125 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 5)
      fun sd h => ((staticHM 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_thZ
  have hbox := boxHM 9
  rw [bx6HM 9 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 9) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thZ` is a derivative of the centre `Z`. -/
theorem xHM_der_thZ {c : ℂ} (hc : c ≠ 0) :
    xHM c 9 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 5) := by
  rw [xHM_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHM, PHM_der_thZ,
    show WtHM 9 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thUe` and the symbol family of `Ue` have the same
Kronecker image. -/
theorem kderHM_thUe : KvHM 125 73 55 12 = famPack 125 73 55 NHM MHM DHM (if oddHM 10 then -1 else 1) 0
    ((c0HM 10 : ℤ) * 1) ((c0HM 10 : ℤ) * 0) ddHM drHM 0 (famHM 10) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thUe` is the symbol family of `Ue` (equal Kronecker images). -/
theorem PHM_der_thUe : PHM 12 = famPoly NHM MHM DHM (if oddHM 10 then -1 else 1) 0
    ((c0HM 10 : ℤ) * 1) ((c0HM 10 : ℤ) * 0) 0 (famHM 10) := by
  have hk : kron 125 73 (flat 55 (PHM 12)) = kron 125 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 10 then -1 else 1) 0
    ((c0HM 10 : ℤ) * 1) ((c0HM 10 : ℤ) * 0) 0 (famHM 10))) := by
    rw [kronHM, ← famPack_eq 125 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 10)
      fun sd h => ((staticHM 10 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_thUe
  have hbox := boxHM 12
  rw [bx6HM 12 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 12) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 10 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thUe` is a derivative of the centre `Ue`. -/
theorem xHM_der_thUe {c : ℂ} (hc : c ≠ 0) :
    xHM c 12 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 10) := by
  rw [xHM_fam hc (i := 10) rfl (p := 0) rfl, dS_famCtr, xHM, PHM_der_thUe,
    show WtHM 12 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZe` and the symbol family of `Ze` have the same
Kronecker image. -/
theorem kderHM_thZe : KvHM 125 73 55 13 = famPack 125 73 55 NHM MHM DHM (if oddHM 11 then -1 else 1) 0
    ((c0HM 11 : ℤ) * 1) ((c0HM 11 : ℤ) * 0) ddHM drHM 0 (famHM 11) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thZe` is the symbol family of `Ze` (equal Kronecker images). -/
theorem PHM_der_thZe : PHM 13 = famPoly NHM MHM DHM (if oddHM 11 then -1 else 1) 0
    ((c0HM 11 : ℤ) * 1) ((c0HM 11 : ℤ) * 0) 0 (famHM 11) := by
  have hk : kron 125 73 (flat 55 (PHM 13)) = kron 125 73 (flat 55 (famPoly NHM MHM DHM (if oddHM 11 then -1 else 1) 0
    ((c0HM 11 : ℤ) * 1) ((c0HM 11 : ℤ) * 0) 0 (famHM 11))) := by
    rw [kronHM, ← famPack_eq 125 73 55 NHM MHM DHM _ _ _ _ 0 (famHM 11)
      fun sd h => ((staticHM 11 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHM_thZe
  have hbox := boxHM 13
  rw [bx6HM 13 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HM 55 13) (l1_flat_famPoly_le 55 NHM MHM DHM
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHM 11 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thZe` is a derivative of the centre `Ze`. -/
theorem xHM_der_thZe {c : ℂ} (hc : c ≠ 0) :
    xHM c 13 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 11) := by
  rw [xHM_fam hc (i := 11) rfl (p := 1) rfl, dS_famCtr, xHM, PHM_der_thZe,
    show WtHM 13 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

/-- The embedded low-resolution family centre `Ue`. -/
theorem xHM_embed_Ue {c : ℂ} (hc : c ≠ 0) : xHM c 10 = xLM c 4 := by
  rw [xHM_fam hc (i := 10) rfl (p := 0) rfl, xLM_fam hc (i := 4) rfl (p := 0) rfl]
  exact famCtr_embed SLM NLM MLM 0 (NHM - NLM) (MHM - MLM) (SHM - SLM) _ c 0 (famLM 4)
    (by kernel_fact)

/-- The embedded low-resolution family centre `Ze`. -/
theorem xHM_embed_Ze {c : ℂ} (hc : c ≠ 0) : xHM c 11 = xLM c 5 := by
  rw [xHM_fam hc (i := 11) rfl (p := 1) rfl, xLM_fam hc (i := 5) rfl (p := 1) rfl]
  exact famCtr_embed SLM NLM MLM 1 (NHM - NLM) (MHM - MLM) (SHM - SLM) _ c 0 (famLM 5)
    (by kernel_fact)

set_option linter.unusedVariables false in
/-- The variable `t` is exact. -/
theorem XHM_eq_t {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 0 = xHM c 0 := by
  rw [xHM_t (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `V` is exact. -/
theorem XHM_eq_V {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 1 = xHM c 1 := by
  rw [xHM_V]; rfl

set_option linter.unusedVariables false in
/-- The variable `c` is exact. -/
theorem XHM_eq_c {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 2 = xHM c 2 := by
  rw [xHM_c, ctr_cPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `s` is exact. -/
theorem XHM_eq_s {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 3 = xHM c 3 := by
  rw [xHM_s, ctr_sPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `U` is exact. -/
theorem XHM_eq_U {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 4 = xHM c 4 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Z` is exact. -/
theorem XHM_eq_Z {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 5 = xHM c 5 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `thU` is exact. -/
theorem XHM_eq_thU {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 8 = xHM c 8 := by
  rw [XHM_spec c (i := 8) rfl, xHM_der_thU (ne_zero_of_norm_one_mu hc)]
  simp [XHMspec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZ` is exact. -/
theorem XHM_eq_thZ {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 9 = xHM c 9 := by
  rw [XHM_spec c (i := 9) rfl, xHM_der_thZ (ne_zero_of_norm_one_mu hc)]
  simp [XHMspec, dTh]

set_option linter.unusedVariables false in
/-- The variable `Ue` is exact. -/
theorem XHM_eq_Ue {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 10 = xHM c 10 := by
  rw [XHM_spec c (i := 10) rfl, xHM_embed_Ue (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `Ze` is exact. -/
theorem XHM_eq_Ze {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 11 = xHM c 11 := by
  rw [XHM_spec c (i := 11) rfl, xHM_embed_Ze (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `thUe` is exact. -/
theorem XHM_eq_thUe {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 12 = xHM c 12 := by
  rw [XHM_spec c (i := 12) rfl, xHM_der_thUe (ne_zero_of_norm_one_mu hc), xHM_embed_Ue (ne_zero_of_norm_one_mu hc)]
  simp [XHMspec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZe` is exact. -/
theorem XHM_eq_thZe {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 13 = xHM c 13 := by
  rw [XHM_spec c (i := 13) rfl, xHM_der_thZe (ne_zero_of_norm_one_mu hc), xHM_embed_Ze (ne_zero_of_norm_one_mu hc)]
  simp [XHMspec, dTh]

set_option linter.unusedVariables false in
/-- The variable `V0` is exact. -/
theorem XHM_eq_V0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 52 = xHM c 52 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Dt0` is exact. -/
theorem XHM_eq_Dt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 68 = xHM c 68 := by
  rw [xHM_zero c (i := 68) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nRt0` is exact. -/
theorem XHM_eq_nRt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 69 = xHM c 69 := by
  rw [xHM_zero c (i := 69) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nZt0` is exact. -/
theorem XHM_eq_nZt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 70 = xHM c 70 := by
  rw [xHM_zero c (i := 70) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `r` is exact. -/
theorem XHM_eq_r {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 71 = xHM c 71 := by
  rw [XHM_rel c (i := 71) rfl]
  change XLM c (xHM c 4) (xHM c 5) 114 = _
  rw [XLM_new c _ _ (j := 114) rfl]
  change algebraMap ℂ FA (((61 + 32 * lamF c : ℝ)) : ℂ) = _
  rw [xHM_r (ne_zero_of_norm_one_mu hc), param_eq_mu hc]

set_option linter.unusedVariables false in
/-- The variable `V40` is exact. -/
theorem XHM_eq_V40 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 79 = xHM c 79 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `N0` is exact. -/
theorem XHM_eq_N0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHM c 86 = xHM c 86 := by
  rfl

set_option maxHeartbeats 400000 in
-- 178 `kernel_fact` side conditions, each a small proof term to elaborate
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- **Norms of the centres.** -/
theorem normHM {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 96 → Bd r (xHM c i) (BHM i)
  | 0, _ => by rw [xHM_t (ne_zero_of_norm_one_mu hc)]; exact (Bd_one r).le (by norm_num [BHM, BHMl])
  | 1, _ => by rw [xHM_V]; exact (Bd_one r).le (by norm_num [BHM, BHMl])
  | 2, _ => by rw [xHM_c, ctr_cPoly]; exact (Bd_cS_q hq).le (by norm_num [BHM, BHMl])
  | 3, _ => by rw [xHM_s, ctr_sPoly]; exact (Bd_sS_q hq).le (by norm_num [BHM, BHMl])
  | 4, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 4 0 119 73 25 11 1 73 36 27
      85984101127012205299395481202021910100118713654622572912485966291567321850168526695228507407631922267383104531740988122314964365540600161875237729741128366156379530805210402402352348209691143906202757660157346069674862193111719774222033711740570694286499295197800584125515592142577230145688710704392827317702181392036205810818303918080 (BHM 4) (kronHM 119 73 55) rfl (by kernel_fact) clHM_U cHM_U (by kernel_fact)
  | 5, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 5 1 119 73 25 11 1 73 36 27
      72298869898664123285912015241317024708175108950400957959845073053594457561097177533366634879547022789287054786611653172688019706731404260717717371822661123354759032781360776981504959076296851190998258096379019433292313045818790093835920693417318827590175695371064723059489847664594853115013206955393024893187613299928749694328084889600 (BHM 5) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Z cHM_Z (by kernel_fact)
  | 6, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 6 3 221 73 25 11 1 73 36 27
      3860783249572397558222324265436570844193559250480196308768778989444976845030131971781131454166424409543073473531767399356674410646003507584719054765877408963736187904303791355531260940987017421927486969989603481589519625526203384980308945107287259902603827794992110431785544143751931753833177719115499271911046278449872850332132077503857811026087926244684416942080 (BHM 6) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LRx cHM_LRx (by kernel_fact)
  | 7, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 7 0 221 73 25 11 1 73 36 27
      3660589335590352045637825657583612581538621593260400382570594134375883611154397305869652856609267423687357067832036576842713310786121962658279851344882577770506986046819380240739201482458322086741588693769376741039803204328194241896172022961523169771905830923016049220142974399286604217348425346920622675646102054141446406295285284534815677809573181647270633799680 (BHM 7) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LZx cHM_LZx (by kernel_fact)
  | 8, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 8 3 125 73 25 11 1 73 36 27
      72823892924893456678938925257797304707643268308380072630890442864786143210554495683554867082911512880783743815062786361702316721631041279551829682375984675416781908364192818249140155540138666531292141562057634768607171822762441756160814456668384473282836241066671526030282210083723421244351334350151522775294417639483066328189469982720 (BHM 8) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thU cHM_thU (by kernel_fact)
  | 9, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 9 0 125 73 25 11 1 73 36 27
      72019716221376141156624223330390273649446141723233685086731411034852110179117612468546416159880361470418160438299738006129980769395118544939216210712008296151336697965109487387022942219297671440280504935148724154768369447519173155189996462127522568187264486764880765383428164788790652849692597063274235288041772852358211297042120048640 (BHM 9) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZ cHM_thZ (by kernel_fact)
  | 10, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 10 0 119 73 25 11 8 10 36 27
      128024752394724081610262930060046185548044678163172111565370263349931200949443014956575201224412481613481324858879696681854914335623657907803050822930897719690481145365463395432261797873692523509262582886174617113208527102859672626543095025662120486374662509964647483063978934570481759859336633220056753755558856838885964746818846720000 (BHM 10) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ue cHM_Ue (by kernel_fact)
  | 11, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 11 1 119 73 25 11 8 10 36 27
      105548057209960261071185442442354298038292433495555613395222239352937794486567628054641518316591484745713937283066748015679528441885741685883941494612303404870865166443031223601445522144440960924068923507700766253713274536597932298789186252160574506709239137189146585108490462828028849334112752294818546532704617095673777916362096640000 (BHM 11) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ze cHM_Ze (by kernel_fact)
  | 12, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 12 3 125 73 25 11 8 10 36 27
      105199447434939451050173629022223552703845011429477907156755769096151889213462090309720250013145901255655317228679359334583085811746188649386079666482875101927011367935877667945543267056874145386291450841676545236324852689112544471624159078414785168360257856739945203870180500904613717726773226751116919436570020137075558639531458560000 (BHM 12) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thUe cHM_thUe (by kernel_fact)
  | 13, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 13 0 125 73 25 11 8 10 36 27
      104122575928621806560571762361942890333456152938822464481912229183120314696920590426725667909772141494955529732950803701089436339607629369892314368768184602192169536348736569123619479815091797141006697815985109609628758369115390198861976923404047002694081777928337037371220833373442473800562681352738269965690107343432357705867591680000 (BHM 13) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZe cHM_thZe (by kernel_fact)
  | 14, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 14 2 115 73 25 11 8 10 36 27
      14159001791501644387053051652346439764539439527016861158211890759130525504373845796646181214686900447993148401532930174794750482022217610777638086976189721950669367490135681763186609091306171275891693445170396103301867201247550309269441621484773644374592005052968512295223763869124355245439171039517947033119333720565833260020531200000 (BHM 14) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m02 cHM_m02 (by kernel_fact)
  | 15, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 15 1 115 73 25 11 8 10 36 27
      10439810641102123738052963950461276370882630152943965878931627421694517772714264863980322621607525195158677562819873163085646044489820322067467660504271630685601380256850715567121576666197986345915185444177131632210531306930983887006077834012170151632514199817364288304189734624567407470971477253324649852539159913870300323061432320000 (BHM 15) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m11 cHM_m11 (by kernel_fact)
  | 16, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 16 0 115 73 25 11 8 10 36 27
      20683933678558507074347540466748018357690979337506713845964609975760291399975330650128628828225961237914890888476252299210393062177188790622992060711656391007898973676520361943584303984477010677801081644441608565521722335105114028999347461771971472350969486869777813474974811494461684574062784796908993392946439542628629385261875200000 (BHM 16) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m20 cHM_m20 (by kernel_fact)
  | 17, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 17 3 112 73 25 11 8 10 36 27
      1894769938614609449210674922512466205387526492450094166531192645280101653351340188415585970163056068646168384533871860164360400978079733874830813042211638420896278547947138560321685460886163594503650926196011360273931069421681946586771579476676350144719323014005921768561328274622151517245340733390010677114893720848353940052377600000 (BHM 17) (kronHM 112 73 55) rfl (by kernel_fact) clHM_m03 cHM_m03 (by kernel_fact)
  | 18, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 18 2 111 73 25 11 8 10 36 27
      1338023372645550385732101058321722085326699985927950354957288170147116083003440743776752702180083219602637237844489874188130186322156306946727773877313239697114978637919184269231002088956121497622751056140688659755669732116891386907347547753559253289508058402918556382281235142493747587159438224350758292444384148740685406457036800000 (BHM 18) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m12 cHM_m12 (by kernel_fact)
  | 19, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 19 1 111 73 25 11 8 10 36 27
      1509102956158219748487503897352036328226333516521518342183925415462347347745591227877486551363564332593056053518909554237536377334218998626527543199751791405629892902705451920129701944910732960396252040577989727659408992745684534448454002962106793548269367626021769753484710172680461078330330593574954607540533334108973193966387200000 (BHM 19) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m21 cHM_m21 (by kernel_fact)
  | 20, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 20 0 113 73 25 11 8 10 36 27
      3313769482494010802711341490275601083932866636099532047983367628248305779965347009946676681010057671639042308501093582721025869511618943643571539697795538424498020495315526659254697526517176806378621086203958746885742167462463737557115086379303390392607150801759451190731726428547359051972583162855202158312151317814973151838208000000 (BHM 20) (kronHM 113 73 55) rfl (by kernel_fact) clHM_m30 cHM_m30 (by kernel_fact)
  | 21, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 21 3 108 73 25 11 8 10 36 27
      155288756619266012209936202966478064156332548907185766990536104027862115763796581915970002336413531803091622417958931905379287590032091966661605190632810642203962167877585518765160437053935042025660609809987912863116232068500197854647190267480235360301008309701352170631129624524335275985348707587694569792072491909712925939466240000 (BHM 21) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m13 cHM_m13 (by kernel_fact)
  | 22, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 22 2 107 73 25 11 8 10 36 27
      143713789041790638246229779403850232112694696486861722771349379045133123299987866192926447595259914161359397967633429363115692073188910669330347265955528586613806653459098826046760362373883240763552752649033552800571987679241279196680905333818869296681285187475630673552038578699657649241075323206681610234337583538978596344299520000 (BHM 22) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m22 cHM_m22 (by kernel_fact)
  | 23, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 23 1 108 73 25 11 8 10 36 27
      218751863769058288434143772419560346081324246158875668409852281386798964342140717192244760804993572666690962186069486939112937808342430352933701944920806649708014714703349446005945102559717700413302120106325938492697831524910604912992208509893238109159759408201710612414085648920345205743053042618074101909855713761703179478630400000 (BHM 23) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m31 cHM_m31 (by kernel_fact)
  | 24, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 24 0 109 73 25 11 8 10 36 27
      551372121601693181564044430709287281807159767395555509772369150710651947217962388978126752970320336798579564889463594832854011024795422078619244124391226876235065627084854116556272299981378623773286852515226072546434862484846060515621597793687858539738467137856379840179192897010080512251913725193226882815948627575225722622443520000 (BHM 24) (kronHM 109 73 55) rfl (by kernel_fact) clHM_m40 cHM_m40 (by kernel_fact)
  | 25, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 25 1 105 73 25 11 8 10 36 27
      33320739862696867006522171975542544597205947133939773176767449914128248978960523533749313274185771105209626095220247584120031317347837918453582255560594281243404512105144547779096226915994153096335201758806430608113605708018816480454115457678007426394809711154161463234237317685185634362060753089960139220869248649858680241520640000 (BHM 25) (kronHM 105 73 55) rfl (by kernel_fact) clHM_m41 cHM_m41 (by kernel_fact)
  | 26, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 26 0 107 73 25 11 8 10 36 27
      90743615226168291409206654173391715957884132153900292401177909797841796561443998358868994359911994871338589042795665976859814717188376433497895754602156283636872453528291182881639326559382931731871687826621285395772156199201363666557275573052630446250465493993470412939263028966320461593172182608674271522740308978742381688913920000 (BHM 26) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m50 cHM_m50 (by kernel_fact)
  | 27, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 27 1 102 73 25 11 8 10 36 27
      5118203277239883586998645747336280183414096587972601364736883023584088934117948992123478534257428127233816684644001101999555681448708131597682015677058375816623444562257523064014788274708673497307477901286404048227337915599828024311425892557150948398054317645480964294290446936377396023650085541688445275832830757623239614136320000 (BHM 27) (kronHM 102 73 55) rfl (by kernel_fact) clHM_m51 cHM_m51 (by kernel_fact)
  | 28, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 28 0 104 73 25 11 8 10 36 27
      14996200387870947270576637744924616258820396424258622513264283124198815111768952286520472448292265407979608341632414117366796726986323255408668517514629829989891758090452132237776632162164150962739173180758040937152930667935529884008927034592667235722799846560034597947341199831757230071820344654860076933578955446288412185722880000 (BHM 28) (kronHM 104 73 55) rfl (by kernel_fact) clHM_m60 cHM_m60 (by kernel_fact)
  | 29, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 29 0 122 73 25 11 8 10 36 27
      908751415750797069505445496257957355207076608031731650157895298163494327670994757584651911405726945814137958943994456875655229443219364714010896160941223642994702124287696384966362420564339680831149299364333040982846221966270823885792795355900841555516744296347708712093187836330286018918113244228335067232411069713190892764837969920000 (BHM 29) (kronHM 122 73 55) rfl (by kernel_fact) clHM_Dp cHM_Dp (by kernel_fact)
  | 30, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 30 3 118 73 25 11 8 10 36 27
      64576675082912971780003739252621722811719184309003299724410525108349866986999453999817127340096984774205725014288526173643487855230374422082778728705875478801144927797279700431490897983301610072392604199211233917949194772627447061073385675542911844889307271041110906198590097862007732218229008180636540230106974787753041818434928640000 (BHM 30) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRp cHM_nRp (by kernel_fact)
  | 31, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 31 0 118 73 25 11 8 10 36 27
      64399172719695940497476397758277186190155561176545693455250912069499957250494144663270987370235552308427259838100272711527799817553074490229972118916139461654515024741551409128008853608921913233698017119121298478521033846890307447700126049127294284458975502268978149165134078409490153521923181478054788818912612666541862292931215360000 (BHM 31) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZp cHM_nZp (by kernel_fact)
  | 32, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 32 0 123 73 25 11 8 10 36 27
      1620277695331137848739161700305529096453850246744000423124836022622340583497423130634147012936628815115660651754293847838860102812219387228320465658256615250417850628458901972005547261533029390449025976867890274065342651770034297843702264538405236890127424121069520537999313467307838007649649797251129009080796318159894881798476267520000 (BHM 32) (kronHM 123 73 55) rfl (by kernel_fact) clHM_DuP cHM_DuP (by kernel_fact)
  | 33, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 33 3 119 73 25 11 8 10 36 27
      134155207625423762798767892385708569141627366329162647490740199426703184178719080276935756317590813936463969957377649801217029155013032890741584329463984070133017850867128909057034855182343434097830345896312022182074474917843616899757902023540213874266357877679609635829914237772372003377803396076285521548891126173866064582017024000000 (BHM 33) (kronHM 119 73 55) rfl (by kernel_fact) clHM_DzP cHM_DzP (by kernel_fact)
  | 34, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 34 1 116 73 25 11 8 10 36 27
      14022438096655644532187336281932224398738420368560825059824890561808282643693677903141688794466497315002102427201607591772084204304588917371920877512868965156967553684433734962085459797873688541838802966178291239446027191510484521876536141392062936734387688522189517284280197753092713974631371197056952494301181720883471640994775040000 (BHM 34) (kronHM 116 73 55) rfl (by kernel_fact) clHM_DphP cHM_DphP (by kernel_fact)
  | 35, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 35 3 121 73 25 11 8 10 36 27
      650872461785972102123343891504915137942065504367766712502781938267502426561958091685465562874280650155215271289801739296193297846676026335281175392576547554240090265128068041187080095073383439600615088445961041034739694856850671786273335056291688972418939045071772025590270671030909454174047256575707618890595316338381400199449804800000 (BHM 35) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRuP cHM_nRuP (by kernel_fact)
  | 36, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 36 0 121 73 25 11 8 10 36 27
      524933820854936156235222151731869681266615916776637367865568593450765106298823324787271037286232312980520346848788754438523932135508669526853351317939368218870274396480052952531611821625134924318902072769328006402532871271280222849182244773054237041928378284030658805755830821109903264195475168505654276693190342325892873460698316800000 (BHM 36) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRzP cHM_nRzP (by kernel_fact)
  | 37, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 37 0 119 73 25 11 8 10 36 27
      130816423273290573127740843185167535105067726591359656241995364156681587030645943414027251918959208532995140872887330602603452966547139442811607204746216067148797730222685402073375129103885727148827107127958523527804820604667155348231857738623794046082391356756797431166765194717354646537421183105404643848280135144580898081011138560000 (BHM 37) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nRphP cHM_nRphP (by kernel_fact)
  | 38, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 38 0 121 73 25 11 8 10 36 27
      604644875905086753974928725754448713642761482853988183308865965872838280507440844912460466677627987198009808976447577436894895654540401130667439811113924931415684793763632640250464224116652608313116390026604737173416495663519565478919921404238766292725584905826944596077540930929586279613141430110186408426855333200492787684910039040000 (BHM 38) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZuP cHM_nZuP (by kernel_fact)
  | 39, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 39 1 121 73 25 11 8 10 36 27
      571284014908099250959108297089081012250608388888106664531928472033928364055560617560779884954628386387606129933696521277929181312794370213215939591969914036471936483441431686803642453772636573274566840783550160228928164868415501822048615218283383344648956145710571406176859000115599880226671941155712771838787869593049055572032225280000 (BHM 39) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZzP cHM_nZzP (by kernel_fact)
  | 40, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 40 3 119 73 25 11 8 10 36 27
      129486796765215169491180399249226709028964651869629405418876732958115114058221542267441850641130269478463564172551946186830946810827338220134426514408316823181178016273953892519317859679688942265830658544369036565831527923549010662340281976854201871327722998181253409588092448331777906458434653208627250428635455728936156543445893120000 (BHM 40) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nZphP cHM_nZphP (by kernel_fact)
  | 41, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 41 0 123 73 25 11 8 10 36 27
      1267570189009405284093904251618610270523641756053916164327604526120863860228216537190514763537839847412742431943545058093840376206154661653030565987422160220755449939381585077004301061713142126447553911437215713152035903770647997380519417734942438634533031288071950237444922291992589289079250384000837311235711569964643292955898019840000 (BHM 41) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PuP cHM_PuP (by kernel_fact)
  | 42, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 42 0 122 73 25 11 8 10 36 27
      988818438742315917300232367648081811382253211794560792232297782989428387859698312509384501283988695297975349468811590900395983648357427474631438766761682557618823286022052164476386121607298207440505424796632902317800652082530728014360761541703701108449817146394489400357284975673236755023216428690857042325883068392853022403219947520000 (BHM 42) (kronHM 122 73 55) rfl (by kernel_fact) clHM_RD cHM_RD (by kernel_fact)
  | 43, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 43 0 123 73 25 11 8 10 36 27
      1700280016071019209639960797309122241556545563009679125652147280764957067536233021596118555079268378514309066982653491923602684770443070619715591371653904887260149819209480213597281727927335671103698960737819465167086823502597436929799692923399138384469963177066278028768075495585872840343901188888118356221192225572435647411771146240000 (BHM 43) (kronHM 123 73 55) rfl (by kernel_fact) clHM_RDu cHM_RDu (by kernel_fact)
  | 44, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 44 3 119 73 25 11 8 10 36 27
      130381520112811609150823612745577908638270922969609493008262998208654727543159000078731188454793482117212899409616416637152070599184804022364476457208930292464014926832973881513597456020030337053578409853429340065765319767486915484948969178193703268441381869912739336820464364201363990127712759064241949824295747108264743348532674560000 (BHM 44) (kronHM 119 73 55) rfl (by kernel_fact) clHM_RDz cHM_RDz (by kernel_fact)
  | 45, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 45 1 116 73 25 11 8 10 36 27
      13467320346528334014137068719078139660989345469116530340271545551828704513553721336652924930726699102422400604134422091245790972953184881922729038636585654424715399472850959741768327603298528513379515922042880128132190963166103641908267617696850780330262140146653505073230397185995575875757714591876929253028256433343010081729413120000 (BHM 45) (kronHM 116 73 55) rfl (by kernel_fact) clHM_RDph cHM_RDph (by kernel_fact)
  | 46, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 46 2 122 73 25 11 8 10 36 27
      1284839632508221489519639845068815125922945338235948750386337206967440431214967975880801110110299095885680115038637879645760044853662980970942239613488720326542654724323588382452654741972438638348825279570923487230907670926646129414008630741160768122991795729771678229093897398991067707144462175117396101624858899511442386243100344320000 (BHM 46) (kronHM 122 73 55) rfl (by kernel_fact) clHM_q cHM_q (by kernel_fact)
  | 47, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 47 0 125 73 25 11 8 10 36 27
      6838889178593058836614760715043202217921908557851546518589754372511487898195403280680156457438072123147447803811447660068852275436276894524650835532850973187746770906129710259593803247979138434308975917230664888616027167001719813412049487790748371854549713405660311752991915941047139047317580284125594549609690248051253912173910425600000 (BHM 47) (kronHM 125 73 55) rfl (by kernel_fact) clHM_qR cHM_qR (by kernel_fact)
  | 48, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 48 3 120 73 25 11 8 10 36 27
      216293181461132416482472148228114903790595437620521700843864609405360394164966345386234322526820185423308541208350459948384481385944610109781145082223629212304817138159040864801025161409922164118495755829786850956719962364793616614215511788250315231363882798133672775240695469320990506357910091047980457830249807264651595314825789440000 (BHM 48) (kronHM 120 73 55) rfl (by kernel_fact) clHM_qz cHM_qz (by kernel_fact)
  | 49, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 49 3 116 73 25 11 8 10 36 27
      28660056856445851531924185709062110077514581036211593554194108602811961742866320717636481943760296518350605345412690042354499658726050436602943262910998253341520365047269137101057481029010740617105044228035081810383960447746702059972863638322338193932116452338174251771947386980857850327050763062791287260580769402135195267964600320000 (BHM 49) (kronHM 116 73 55) rfl (by kernel_fact) clHM_qph cHM_qph (by kernel_fact)
  | 50, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 50 0 123 73 25 11 8 10 36 27
      2172235063304109305691002576618035054211100284451834479992887900414495726538461546427295863666363315589343147755164169639313323587227348116340433706244690535275870685296159592423715124332886554538646686511221370133542665343556050116799486461982761989162529867265985386556400630222712099389453057611475413048244872401022888019356549120000 (BHM 50) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P2 cHM_P2 (by kernel_fact)
  | 51, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 51 2 116 73 25 11 8 10 36 27
      22259451934203474073463922028258745065615053720916347956554036804271910166218136376139500956049452392095159954350087839487319966652481613499478172697058711041165219247269082750759324669405487551698963241895232618117183876872590617005894291634801350494058655543371069747660484096531908893411632114422621353797770742658705861965250560000 (BHM 51) (kronHM 116 73 55) rfl (by kernel_fact) clHM_E cHM_E (by kernel_fact)
  | 52, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 52 0 123 73 25 11 8 10 36 27
      747301776094162437232524643167516552005135973411973295764837852142629792304169619452265111160500976544710991539831951384951565911771789110895706861190360972017462062132748500767032480097533137637270190276552215549942466659955501553201368070352969046180681338857640485572778682806006803766198196738459471775171046278955802381044940800000 (BHM 52) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V0 cHM_V0 (by kernel_fact)
  | 53, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 53 0 123 73 25 11 8 10 36 27
      758855054400290579901628462525526517854686639052472609166019867814719204147809959305120462697072758484605122796204931589220659766334859982423676995734834326924834083184007401853216791229778044959192466839473553639954489836416127995927129468813300895027838243275637247873390927405658234886456777097319291222826661911616984584080588800000 (BHM 53) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V2 cHM_V2 (by kernel_fact)
  | 54, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 54 0 123 73 25 11 8 10 36 27
      747301776094162437232524643167516552005135973411973295764837852142629792304169619452265111160500976544710991539831951384951565911771789110895706861190360972017462062132748500767032480097533137637270190276552215549942466659955501553201368070352969046180681338857640485572778682806006803766198196738459471775171046278955802381044940800000 (BHM 54) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Vn cHM_Vn (by kernel_fact)
  | 55, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 55 0 123 73 25 11 8 10 36 27
      1286664542729859778565039481899331881160484279474671676267757819165800696435753100844655615405472354038356682485661690647110142049629963520482795353585286620647332624057946427363624254151741057994484221843092334796799117254391753828633302243032599759547831236649094742220970871433200017950682608455457043260099343310202501595219886080000 (BHM 55) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W cHM_W (by kernel_fact)
  | 56, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 56 0 123 73 25 11 8 10 36 27
      2237521373650114499277591600286132366001801723362346105201147033102055703567531422493420951618839132851947408287299898322832304340292657761039190132729929367074914587716764859757757758753953390557515270976948120294412310426209938636742887251835610843641177087860825381128811503692619069085780836189451358298751240308370848420837105967500 (BHM 56) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W2 cHM_W2 (by kernel_fact)
  | 57, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 57 0 123 73 25 11 8 10 36 27
      3870624016791886564055579514570019185159092566886554925900736302883835496512736315418814683611985545764024894197851765258084510303961661882715283878936479446250256610418272858066540610067339590647230429242097232039690262174460821412424718040144744281707995250080407180820498448290620647238506926935368764963899625058999371372336193613125 (BHM 57) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W3 cHM_W3 (by kernel_fact)
  | 58, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 58 0 122 73 25 11 8 10 36 27
      902957167029847703780300874484536617270474582905408868742162423476255109790457812920816391964362646189876880435892431819364703613639458692959082897272166539959892187919770412933825150811309310978223219878685931306617065124431369756032851100410940848163534072253055178996843321754730141284187591789687422875196988623123296196157767680000 (BHM 58) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R2 cHM_R2 (by kernel_fact)
  | 59, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 59 0 122 73 25 11 8 10 36 27
      990598409917680902560973563972102078470210581511850973926767875257353975851806460213965261969952613369921750694998841017453683367834746018818315863136167830071491953894433325571529126048127523906593137932126807203714992036591664945888390814090833768001430812316773933224611100437475266387046306512486664670115481704218452567387013120000 (BHM 59) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R3 cHM_R3 (by kernel_fact)
  | 60, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 60 0 125 73 25 11 8 10 36 27
      7491724676883027081261930153673011473546524398097116279590190084532686971535411333254191860816998774435068463185295982148477078189008130299853157337439694791274115357785114642699885013998366388341055173955225760608606081835248078035771805114376609273189060894114136738977631558618610066989602121856420813477431033781593996335146598400000 (BHM 60) (kronHM 125 73 55) rfl (by kernel_fact) clHM_A1 cHM_A1 (by kernel_fact)
  | 61, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 61 3 120 73 25 11 8 10 36 27
      227459375147265145806051353668931046743051630207012327331591079636545954049601140981461033306451952345278941237892361350006925511392357133231258103494773938101484585505211240196926241800851925365247285255076245259651846188332522019168001172872362031882851387836785482702950668811004037139429816523563253452074683245789226965779087360000 (BHM 61) (kronHM 120 73 55) rfl (by kernel_fact) clHM_A2 cHM_A2 (by kernel_fact)
  | 62, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 62 0 119 73 25 11 8 10 36 27
      189439756383493714171188091837532480376993320457236756550721957765702807226024828749581902662972528649928314221791679647571544224774456999194279879916169551918786466817702503533035297748745177476561711641312761426337497872706003838133862424355053341333880454931534093963583588906016353492956143777138882587787690030516330582759178240000 (BHM 62) (kronHM 119 73 55) rfl (by kernel_fact) clHM_K1 cHM_K1 (by kernel_fact)
  | 63, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 63 3 120 73 25 11 8 10 36 27
      278238123046477018779596361941000620051868526510733460895398712963231265700969093106543870947845096375945143529723485850136335335614293599162414804036243095158984171038389424636896662588698945727301148642678305376708439000925020026931903188296592265121428656550627318393185468783729112099979886260362870492573721858608299517694443520000 (BHM 63) (kronHM 120 73 55) rfl (by kernel_fact) clHM_K2 cHM_K2 (by kernel_fact)
  | 64, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 64 2 123 73 25 11 8 10 36 27
      3629765571997725146620063594778623338103357038728133973755234550141633281459522356378201842406817382863381423138123526543506626357798042894371147760409540848924683084317153827243396544719254114358185412665538598205112783681237227239624401689137445438363026813206749542511737139152067293967598467157650194995266128808214016832454000640000 (BHM 64) (kronHM 123 73 55) rfl (by kernel_fact) clHM_K3 cHM_K3 (by kernel_fact)
  | 65, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 65 0 119 73 25 11 8 10 36 27
      220988344888982477205939200753682245383955116406813310621187480486543281795396201927751936381297157115447246722873641319294945046140934766814019464465719287706234577105469640704463445030542393072053215383139502344802979616096542792544356237210452755568231729244312417005028992395261159304960398873567697101674872969492044464688988160000 (BHM 65) (kronHM 119 73 55) rfl (by kernel_fact) clHM_KD cHM_KD (by kernel_fact)
  | 66, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 66 3 120 73 25 11 8 10 36 27
      338263558391793368737844366046277387805673095447007187639688490304615315660826508930795002027148850292262108799987382362077746716855160490968883909116163763846569954458914990004474910635148417831334401882843753464001417095344605898317839599048223272124217052171469619104995804634637048979385260122489707338488684660144492422144983040000 (BHM 66) (kronHM 120 73 55) rfl (by kernel_fact) clHM_KR cHM_KR (by kernel_fact)
  | 67, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 67 2 124 73 25 11 8 10 36 27
      4749430590710570004156523088785430460513943995224886751773160174892372273039819553258446127750277418758357213887682259517818825234788751887824869414697326082986914155423340224581285334687195751484978780036912169602187803334422039711343383906044672913388695848983305382072632699691024486088357351062937861852975703227034916935916584960000 (BHM 67) (kronHM 124 73 55) rfl (by kernel_fact) clHM_KZ cHM_KZ (by kernel_fact)
  | 68, _ => by rw [xHM_zero c (i := 68) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 69, _ => by rw [xHM_zero c (i := 69) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 70, _ => by rw [xHM_zero c (i := 70) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 71, _ => center3_fullN hq hc boxHM (l1HM 28) (fun _ => rfl) 71 0 129 37 14 9 8 5 36 27
      47834884316007366514710390827141909056247197529154234916542103802407984085589703716965365859903507820084146323974520578972347030084068806794468413262517742892203982563350372956891322394333781733012029615515798159953099748338049650562216420357787671704849251083839316479703000964440975522015003522729942892111187804867539538673873715200000 (BHM 71) (kronHM 129 37 28) rfl (by kernel_fact) clHM_r cHM_r (by kernel_fact)
  | 72, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 72 0 123 73 25 11 8 10 36 27
      1517627131885462470332057022272005063332594630540253324431152846557635527392507249880784469994563187038503519228631990141603216369188083525614611862225172330091778594801424127146126960588155058460588700087507368190899290126511454888826558621392596047267499811589710915824296456019727300000698814043952669284235124299671416321270087680000 (BHM 72) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P4P cHM_P4P (by kernel_fact)
  | 73, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 73 0 122 73 25 11 8 10 36 27
      1082287373785809763890366001473689286424741364140995009911759096445330204627712483511353847853938610254005456943610882146180964002004307117157761404159256213019151393968393324051877493007932795731399317623754320079682049351620906236266270332310515919129690550407674389135758016961555386901229319288838605968478327637582314981703024640000 (BHM 73) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R4 cHM_R4 (by kernel_fact)
  | 74, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 74 0 122 73 25 11 8 10 36 27
      1550572497830614029299759221672434215447588565085412464205701886129589563981293794720016955721893174583973873974129305065359955742790347553466118225055531063934523060089079853871298897033239575825604684454055514988989423796681846070017362535423439178144265819264514877035678035061377472944647927616544300000432346414007146025509191680000 (BHM 74) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R8 cHM_R8 (by kernel_fact)
  | 75, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 75 0 123 73 25 11 8 10 36 27
      3101406999118848397499398927275225136897657456692578831372418902784697785174529514688863505697476977542140827442173393833561579702841891091628543325645476595186530909051008341978182419114687177346856260684445522829678848815129184279619285676327546727663945160782108462489041195756574872539085648921818768005563504934173654596116807680000 (BHM 75) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P42 cHM_P42 (by kernel_fact)
  | 76, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 76 0 108 73 25 11 8 10 36 27
      374308615545773369817733157595592878261559080237142025750125593901733009125522998862008463105377418403199215225785265261972271968133420534868377771444274232663076351356090456583516470833327896015974204100419639584681937999468504399606828917185637372222823538824134509623008362737907508357091970725431004401752283019335780857282560000 (BHM 76) (kronHM 108 73 55) rfl (by kernel_fact) clHM_E4P cHM_E4P (by kernel_fact)
  | 77, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 77 0 123 73 25 11 8 10 36 27
      2596201191572317414152966698260618540708963020524397376018080079256647909281233016509480735819733614206427170201418126204529994926722871093520799295428605493216344139522058541697413760941907444721021677313752184170104275110428123197048389869550191933127792012834073112211510612932041434840128297482485044162700041968174865068075253760000 (BHM 77) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PP4 cHM_PP4 (by kernel_fact)
  | 78, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 78 2 123 73 25 11 8 10 36 27
      874599105891015837476261948804611690648511058957822417147571772095586120433061718166046580754456188762157919536920773924117249045879430875056882863667446514275606576200923833062740460413534927120696096458078781061816228726782086725447684184039137583634424750619774406159384496358624227326078087596600729656144566320788794002185912320000 (BHM 78) (kronHM 123 73 55) rfl (by kernel_fact) clHM_QPP4P cHM_QPP4P (by kernel_fact)
  | 79, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 79 0 123 73 25 11 8 10 36 27
      736108512116245127363192813782251932765338992798318698270717544381412923402690380402117602590262566585176049771851097020933023286350480441766404252506192140005796452498844983944668933035282111683105647501805084152184699118371483636965977111210496142292192094019980696813533604751351746189950155854223301713272399628036477834965811200000 (BHM 79) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V40 cHM_V40 (by kernel_fact)
  | 80, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 80 0 123 73 25 11 8 10 36 27
      736295767513290244917988142833631644053063009847948312855755157463474021749666619202458714329238978962168020368053440134030747779045350439858394253213596098567216362072365125123155342966462171983665393553945867343728876302382499025592736457366255336589524721136337915520981687405623010847919004727346049837307298693430138533492817920000 (BHM 80) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V42 cHM_V42 (by kernel_fact)
  | 81, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 81 0 123 73 25 11 8 10 36 27
      736108512116245127363192813782251932765338992798318698270717544381412923402690380402117602590262566585176049771851097020933023286350480441766404252506192140005796452498844983944668933035282111683105647501805084152184699118371483636965977111210496142292192094019980696813533604751351746189950155854223301713272399628036477834965811200000 (BHM 81) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V4n cHM_V4n (by kernel_fact)
  | 82, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 82 0 123 73 25 11 8 10 36 27
      747415503759801925823194382560878261645112419769768045536299697933609602081223180199952835589429840601397447893189785734574268956649024976625927812532127903177957963983929436044254408499623811246534703937882903813604076393428083787165366804406252186739181115906083614372441782921355892649528541616136924297569286923225010882645852160000 (BHM 82) (kronHM 123 73 55) rfl (by kernel_fact) clHM_VV4 cHM_VV4 (by kernel_fact)
  | 83, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 83 2 123 73 25 11 8 10 36 27
      874100829614231971533524073243560232667057963879277096506896393876647631498974126606923119893932554018675005030324910707499971503480752040940842659021332382380340350994358191673563691880156815076342882574945796688273548656810718854777164766520332859941184773761369685863498926614037668658915875915445818335496246538831741951871549440000 (BHM 83) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Bm cHM_Bm (by kernel_fact)
  | 84, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 84 0 120 73 25 11 8 10 36 27
      91990162146168012528289213129119055877398456786835067147196353466169200164595584071087242038275976577084896776874078036485282750161670782297054640889457197869623043391058409532483312296795734101946210799068842615294422592957787789542723885303437830201633175161229454768659617239309568311567314466788351715598438086283729882065141760000 (BHM 84) (kronHM 120 73 55) rfl (by kernel_fact) clHM_lamv cHM_lamv (by kernel_fact)
  | 85, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 85 2 120 73 25 11 8 10 36 27
      109262560714202512461990651613055298966072690700483158050494399382135774040472163776727847044498690420186914406199488273713839866495280745545389785926092008942909924951246694711347840035065578361960293528451340705389102891087994919201332232191422495120304127216192866263819719644513734215383245062079174166486560887551423104900136960000 (BHM 85) (kronHM 120 73 55) rfl (by kernel_fact) clHM_EN cHM_EN (by kernel_fact)
  | 86, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 86 0 123 73 25 11 8 10 36 27
      797437775055415368721346807748211259500906121733163743453711988036868993571551733400953032910328367972661135376691970045662887643152446645036519696692354865573275051886978393722719291198756685550658061491965085637616853178763392090270074015863292614069383198091315956207179427321548304388559608521226298489087156419723853816450252800000 (BHM 86) (kronHM 123 73 55) rfl (by kernel_fact) clHM_N0 cHM_N0 (by kernel_fact)
  | 87, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 87 0 124 73 25 11 8 10 36 27
      864052300513708695671997536813299665641439485994521085699244680076256768871777197031512318296497275936544353977265308232468204532403911073655066038432578613130221665922333001801884858058106405195785457619378870812359023735648763708523630005559723340610563437889454300357655018833806752306319177184961077581419107709124444465764761600000 (BHM 87) (kronHM 124 73 55) rfl (by kernel_fact) clHM_N2 cHM_N2 (by kernel_fact)
  | 88, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 88 0 123 73 25 11 8 10 36 27
      797437775055415368721346807748211259500906121733163743453711988036868993571551733400953032910328367972661135376691970045662887643152446645036519696692354865573275051886978393722719291198756685550658061491965085637616853178763392090270074015863292614069383198091315956207179427321548304388559608521226298489087156419723853816450252800000 (BHM 88) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Nn cHM_Nn (by kernel_fact)
  | 89, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 89 0 123 73 25 11 8 10 36 27
      738281138721650178898529089614561784582097303587064027896702421781838904777450021952495517122915461149429078298636341376145925613273929439352720590465853837509609686313800065000996878722394163663840615692169434960031892595871590084885478963563387432059530662116035381908499538386014448443049480948824830012311874929930450782314823680000 (BHM 89) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Fv cHM_Fv (by kernel_fact)
  | 90, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 90 0 119 73 25 11 8 10 36 27
      130859742783648177247876084457513294538691703570837459774280582393370328435256072094076213862651543982040283873528532578313434355562186061597134902308138585303479675525051845034080681167833097514242349627352662209466617185556657184169192308109274482904934977644777652080786605157888404232977506778978867696150215689190632464035348480000 (BHM 90) (kronHM 119 73 55) rfl (by kernel_fact) clHM_YDt cHM_YDt (by kernel_fact)
  | 91, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 91 0 122 73 25 11 8 10 36 27
      908541061782956539235678653853059926853955850909733577276629599331575191406540103880688523902100696446809889030943976921237863135648415203974942013915905132042866688723346650475665059824336952034833127213695836621149152785650878606699845752687026917583330184707737301315227703116272165454844988507388399638536493966773265377693532160000 (BHM 91) (kronHM 122 73 55) rfl (by kernel_fact) clHM_DtF cHM_DtF (by kernel_fact)
  | 92, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 92 3 120 73 25 11 8 10 36 27
      215016895376583763776878332448684847394637343880591903278584125367316653413732261950119753710649797129201073782828952800915805198555144109800495777905600564129294072890295766187257426413756996692594038283538342454249457075773212253214888846937577257351244027822560224229119350608713850327116925618783194589052644864771676886923714560000 (BHM 92) (kronHM 120 73 55) rfl (by kernel_fact) clHM_YnRt cHM_YnRt (by kernel_fact)
  | 93, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 93 3 118 73 25 11 8 10 36 27
      64928815328723047733691623985813783814763395750984243638741472496130540372560714630997722962864480538667359167428390693227649243655411720052725590168570957727946009751544672067497931201880841548346043394047327548739270129332990296777846123285703357665938059529918135241652109315073710117136680384536918903125680829696370003505315840000 (BHM 93) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRtF cHM_nRtF (by kernel_fact)
  | 94, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 94 2 123 73 25 11 8 10 36 27
      2198625068635679000052627697029390014557222529936097589095435935945702720009356894975324839039034675823505162740353965987892764587590783703400521212876180128930691213739444028463534321838456709697948704662291627443976408351875195778460057759435398180523766974117413733574194476680547989079952458258750397124905783933726806004309913979375 (BHM 94) (kronHM 123 73 55) rfl (by kernel_fact) clHM_YnZt cHM_YnZt (by kernel_fact)
  | 95, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 95 0 118 73 25 11 8 10 36 27
      67408093673665418340605092303906560016948643639914605468174214508922703107130616045396400715285784241013139374405717004108105545387918333203648164998984831819433379662233321531397251954712176578161898532090796516109477025462362622384621082642840949214755581938109611064784261948403163033630546969312915040413672842147686192733224960000 (BHM 95) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZtF cHM_nZtF (by kernel_fact)
  | n + 96, h => absurd h (by omega)

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Vn`. -/
theorem vnodeHM_Vn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 54 → Bd r (XHM c i - xHM c i) (EHM i)) :
    Bd r (XHM c 54 - xHM c 54) (EHM 54) := by
  have hn : ∀ i, i < 54 → Bd r (xHM c i) (BHM i) := fun i hi => normHM hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_Vm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 11380478924818337006210938134564104985948319117292758587267024413276190987404946883567174854293163928031817324839327093069303910478422852519269734074703389060477715004281224507165981723167264821700503884001474627587085916293199236859576987925466404567615937567804847423501744891530257273659681004152658050383541588685963324523806720000
      (2557 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Vm1 kHM_Vm1 (by kernel_fact)
  have h2 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_V2m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 22933757230946479675314757492574070835498984757792071988449040085365602831045286736422526390864945867925948581212307297338397765041493724047239868619176743967849736055540125593350292855412172143622780446922812717599109092753825679585338386385798253414772841985801609724113989491181688393918261363012477498039157221347145527559454720000
      (5153 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V2m1 kHM_V2m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_eta (2, 0, 0)
      144 108 48 237 145 49 13 8 19 72 54 108398915804641095308729456461636957651252412075507877807587350786385804895255213082134802089119943910313557186061000538229116007572691992589231725331064696655531651116171049091540750547493959502985434040884809931751604577879046857852659842374696205835374683852304543090393863868952384927517954276753672287253658884592100104306125868646041124482343752846107541308501101770334138025828293811526241656462286089712557879957848681452197207004272886783262993707086081550307554383825707184832599900345437310538221675912742568079156306354104831248565701229463163123137258782453531662112719062753167429223490169671704290979901900593015631375530721280000000
      (47 / 25000000000000000000000 : ℚ) (kronHM 237 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_eta kHM_eta (by kernel_fact)
  have e1 : Ex.eval (XHM c) (toEx trHMN_Vm1) = xHM c 52 - 1 := by
    simp only [trHMN_Vm1, toEx, Ex.eval, XHM_eq_V0 hc, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
  have e2 : Ex.eval (XHM c) (toEx trHMN_V2m1) = xHM c 52 ^ 2 - 1 := by
    simp only [trHMN_V2m1, toEx, Ex.eval, XHM_spec c (i := 53) rfl, XHMspec, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHM c) (toEx trHMN_eta) = xHM c 52 ^ 2 * (1 + XHM c 51) - 1 := by
    simp only [trHMN_eta, toEx, Ex.eval, XHM_spec c (i := 53) rfl, XHMspec, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hEb : Bd r (XHM c 51) ((BHM 51 + EHM 51 : ℚ) : ℝ) := by
    have := (hn 51 (by norm_num)).add (hE 51 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep (a := (((2557 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (n2 := (((5153 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((47 / 25000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((821 / 800 : ℚ) : ℚ) : ℝ)) (m := (((1357 / 25000 : ℚ) : ℚ) : ℝ)) (g := (((10283 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 54 : ℚ) : ℝ))
    hr h1 h2 h3 hEb
    (by exact_mod_cast (show (2557 / 10 ^ 5 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (2557 / 10 ^ 5 : ℚ)) ≤ (821 / 800 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (821 / 800 : ℚ) ^ 2 * (5153 / 10 ^ 5 : ℚ) ≤ (1357 / 25000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 51 + EHM 51 ≤ (1357 / 25000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (1357 / 25000 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (10283 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (10283 / 10 ^ 4 : ℚ) ^ 2 * (1 - (1357 / 25000 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (10283 / 10 ^ 4 : ℚ) ^ 3 / 2 * (1357 / 25000 : ℚ) + (2557 / 10 ^ 5 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (10283 / 10 ^ 4 : ℚ) ^ 3 / 2 * ((821 / 800 : ℚ) ^ 2 * (47 / 25000000000000000000000 : ℚ)) ≤ EHM 54 by kernel_fact))
  have eX : XHM c 54 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHM c 51) := by
    rw [XHM_rel c (i := 54) rfl, XHM_rel c (i := 51) rfl]
    change XLM c _ _ 63 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 61)
    rw [XLM_old c _ _ (j := 63) rfl, XLM_old c _ _ (j := 61) rfl]
    simp only [XL, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHM c 54 = xHM c 52 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `V4n`. -/
theorem vnodeHM_V4n {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 81 → Bd r (XHM c i - xHM c i) (EHM i)) :
    Bd r (XHM c 81 - xHM c 81) (EHM 81) := by
  have hn : ∀ i, i < 81 → Bd r (xHM c i) (BHM i) := fun i hi => normHM hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_V4m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 187214946901027136879108749299485746151338503638161093146716652059322085925707833419666284054753968496875556858472729050761285057114183389967125390534557048812105370377707684802434660916238867535961109254343229829318374709181320624186028782993500679126692730145058664256666836875199697411640119916487988484894937766638778444677120000
      (4207 / 10 ^ 7 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V4m1 kHM_V4m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaV4 (2, 0, 0)
      144 108 48 231 145 49 13 8 19 72 54 2074184122348886374697501058975114009087651456385893832964981416003266600023719587684740574963506781383534319354682068844380608317366461984643601624291518574022081819988903401052814402256771240096260618504283025344044018079367092954222691503125489913848635286197024133306474814925022431911475425448058048556141128419331988788437073074859291786428537362823171956751729960765145275012053082920337896250225595039451780289495006864927411261595185587210750426164222153019607255449012261436518288210860796890646513316352607385569242275747371641551356192538263992343734784300948236163116995855580809452738309385091033698313700950532608214612049920000000
      (49 / 10 ^ 22 : ℚ) (kronHM 231 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_etaV4 kHM_etaV4 (by kernel_fact)
  have e1 : Ex.eval (XHM c) (toEx trHMN_V4m1) = xHM c 79 - 1 := by
    simp only [trHMN_V4m1, toEx, Ex.eval, XHM_eq_V40 hc, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHM c) (toEx trHMN_etaV4) = xHM c 79 ^ 2 * (1 + XHM c 76) - 1 := by
    simp only [trHMN_etaV4, toEx, Ex.eval, XHM_spec c (i := 80) rfl, XHMspec, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHM c 76) ((BHM 76 + EHM 76 : ℚ) : ℝ) := by
    have := (hn 76 (by norm_num)).add (hE 76 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((4207 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (η := (((49 / 10 ^ 22 : ℚ) : ℚ) : ℝ))
    (b := (((100043 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (m := (((8411 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (g := (((100043 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 81 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (4207 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (4207 / 10 ^ 7 : ℚ)) ≤ (100043 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 76 + EHM 76 + (100043 / 10 ^ 5 : ℚ) ^ 2 * (49 / 10 ^ 22 : ℚ) ≤ (8411 / 10 ^ 7 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (8411 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (100043 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (100043 / 10 ^ 5 : ℚ) ^ 2 * (1 - (8411 / 10 ^ 7 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (100043 / 10 ^ 5 : ℚ) ^ 3 / 2 * (8411 / 10 ^ 7 : ℚ) + (4207 / 10 ^ 7 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (100043 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((100043 / 10 ^ 5 : ℚ) ^ 2 * (49 / 10 ^ 22 : ℚ)) ≤ EHM 81 by kernel_fact))
  have eX : XHM c 81 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHM c 76) := by
    rw [XHM_rel c (i := 81) rfl, XHM_rel c (i := 76) rfl]
    change XLM c _ _ 124 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 120)
    rw [XLM_new c _ _ (j := 124) rfl, XLM_new c _ _ (j := 120) rfl]
    simp only [XLMnew, eV4, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHM c 81 = xHM c 79 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Nn`. -/
theorem vnodeHM_Nn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 88 → Bd r (XHM c i - xHM c i) (EHM i)) :
    Bd r (XHM c 88 - xHM c 88) (EHM 88) := by
  have hn : ∀ i, i < 88 → Bd r (xHM c i) (BHM i) := fun i hi => normHM hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_Nm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 61516477886071268495033102715258812481718467438483206276141160307515392254787060832255096604120555355981961161699345753780625641859080386660082569576697282616290704758511117462852792824390812735088375099414344715261472435101089773928282933435789972456317796801480318057902489407071757896021092786919484764299651729454014759929118720000
      (1383 / 10 ^ 4 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Nm1 kHM_Nm1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaN (2, 0, 0)
      144 108 48 241 145 49 13 8 19 72 54 319975931139494085805046552162652484465484541746381428831807110417354231192354360344708753478504121554108714048645191914003873746480281651497272558376380059133287049517518869783837938302518748467557334651272196410879885652251778493234905943134342953331535082370327016762363097587173435776491585617432321722333347963321651970998403830437782893472902616464594813977684680353096108094026153752319941317682014191565573367467679943684968073996675152306662064327757905576698561768511925534806822056369185587726503614012755782065934274970766999271290739955100092811773022720657450954250952834536972467450028364872415741534608146374257447348268936724480000000
      (443 / 50000000000000000000000 : ℚ) (kronHM 241 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_etaN kHM_etaN (by kernel_fact)
  have e1 : Ex.eval (XHM c) (toEx trHMN_Nm1) = xHM c 86 - 1 := by
    simp only [trHMN_Nm1, toEx, Ex.eval, XHM_eq_N0 hc, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHM c) (toEx trHMN_etaN) = xHM c 86 ^ 2 * (1 + XHM c 85) - 1 := by
    simp only [trHMN_etaN, toEx, Ex.eval, XHM_spec c (i := 87) rfl, XHMspec, XHM_eq_t hc, xHM_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHM c 85) ((BHM 85 + EHM 85 : ℚ) : ℝ) := by
    have := (hn 85 (by norm_num)).add (hE 85 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((1383 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (η := (((443 / 50000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((2321 / 2000 : ℚ) : ℚ) : ℝ)) (m := (((307 / 1250 : ℚ) : ℚ) : ℝ)) (g := (((115133 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 88 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (1383 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (1383 / 10 ^ 4 : ℚ)) ≤ (2321 / 2000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 85 + EHM 85 + (2321 / 2000 : ℚ) ^ 2 * (443 / 50000000000000000000000 : ℚ) ≤ (307 / 1250 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (307 / 1250 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (115133 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (115133 / 10 ^ 5 : ℚ) ^ 2 * (1 - (307 / 1250 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (115133 / 10 ^ 5 : ℚ) ^ 3 / 2 * (307 / 1250 : ℚ) + (1383 / 10 ^ 4 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (115133 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((2321 / 2000 : ℚ) ^ 2 * (443 / 50000000000000000000000 : ℚ)) ≤ EHM 88 by kernel_fact))
  have eX : XHM c 88 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHM c 85) := by
    rw [XHM_rel c (i := 88) rfl, XHM_rel c (i := 85) rfl]
    change XLM c _ _ 130 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 128)
    rw [XLM_new c _ _ (j := 130) rfl, XLM_new c _ _ (j := 128) rfl]
    simp only [XLMnew, eN, PolyExprS.eval]
    rfl
  rw [eX, show xHM c 88 = xHM c 86 from rfl]
  exact hv

/-- The transport input `LRx`. -/
theorem stepHM_LRx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHM c 6 - xHM c 6) (EHM 6) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHM c 4)) ((BHM 8 : ℚ) : ℝ) := by
    have h := normHM hq hc 8 (by norm_num)
    rwa [xHM_der_thU hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 4) = dTh (xHM c 4) by simp [dTh]] at h
  have hana : Ana (xHM c 4) := by
    rw [xHM_fam hc0 (i := 4) rfl (p := 0) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHM_spec c (i := 6) rfl]
  exact step_Linput hana (by rw [xHM_der_LRx hc0]; norm_num [KamTorusA.Iq]) hth (by kernel_fact)

/-- The transport input `LZx`. -/
theorem stepHM_LZx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHM c 7 - xHM c 7) (EHM 7) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHM c 5)) ((BHM 9 : ℚ) : ℝ) := by
    have h := normHM hq hc 9 (by norm_num)
    rwa [xHM_der_thZ hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHM c 5) = dTh (xHM c 5) by simp [dTh]] at h
  have hana : Ana (xHM c 5) := by
    rw [xHM_fam hc0 (i := 5) rfl (p := 1) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHM_spec c (i := 7) rfl]
  exact step_Linput hana (by rw [xHM_der_LZx hc0]; norm_num [KamTorusA.Iq]) hth (by kernel_fact)

set_option linter.unusedVariables false in
/-- The empty chain. -/
theorem ballHM_0 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 0 → Bd r (XHM c i - xHM c i) (EHM i) :=
  fun i h => absurd h (Nat.not_lt_zero i)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `t`. -/
theorem ballHM_1 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 1 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_0 hr hq hc)
    (step_exact (XHM_eq_t hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V`. -/
theorem ballHM_2 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 2 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_1 hr hq hc)
    (step_exact (XHM_eq_V hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `c`. -/
theorem ballHM_3 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 3 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_2 hr hq hc)
    (step_exact (XHM_eq_c hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `s`. -/
theorem ballHM_4 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 4 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_3 hr hq hc)
    (step_exact (XHM_eq_s hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `U`. -/
theorem ballHM_5 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 5 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_4 hr hq hc)
    (step_exact (XHM_eq_U hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Z`. -/
theorem ballHM_6 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 6 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_5 hr hq hc)
    (step_exact (XHM_eq_Z hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LRx`. -/
theorem ballHM_7 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 7 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_6 hr hq hc)
    (stepHM_LRx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LZx`. -/
theorem ballHM_8 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 8 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_7 hr hq hc)
    (stepHM_LZx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thU`. -/
theorem ballHM_9 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 9 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_8 hr hq hc)
    (step_exact (XHM_eq_thU hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZ`. -/
theorem ballHM_10 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 10 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_9 hr hq hc)
    (step_exact (XHM_eq_thZ hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ue`. -/
theorem ballHM_11 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 11 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_10 hr hq hc)
    (step_exact (XHM_eq_Ue hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ze`. -/
theorem ballHM_12 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 12 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_11 hr hq hc)
    (step_exact (XHM_eq_Ze hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thUe`. -/
theorem ballHM_13 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 13 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_12 hr hq hc)
    (step_exact (XHM_eq_thUe hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZe`. -/
theorem ballHM_14 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 14 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_13 hr hq hc)
    (step_exact (XHM_eq_thZe hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m02`. -/
theorem ballHM_15 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 15 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_14 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_14 hr hq hc) trHMN_m02 1 0 2 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 288875056313927613686109472464145948186792116667511778618957382241205510157747191585503588512610587572855987358686881721942561213658866195139295373272361107444443370894555346427498127676634298456769063693821748521159663649018084422622184109093251480603263543087887658853062424244508987266118374131609477657574575233340802656701264144182946399948779504299238513214328472955853893790425162459501799707641651213334874188309743738920389886243950430033714589085268935082302762501448081945003858049552751310364015313952600429306508456484060677039722271541709134746969444488936825286510251490494401501050532277244896133194987135412776743114972856320000000
      (kronHM 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m02 kHM_m02 (by kernel_fact) (relHM_m02 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m11`. -/
theorem ballHM_16 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 16 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_15 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_15 hr hq hc) trHMN_m11 1 0 1 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 167086491926531387209303861738023722205725691151799471358413225854070164193042966283135346476205882699265850610924434688314966946218781370555846738961623936696901538326229873839186294562366615024453673525442868176346271092920884248956873354589238592650942099807295521562027988138945074399353490934976143110185467177823920224115973996647927912500309424913916654295151049025627892833492977288226111507454318675722739048516721861496348302925014356692094910866582941105473706555082864623087324305580311022175909386956952292465518144383321184088468095872329171616422737745063709235659357436525201142516354376838799820335384798351736870502704087040000000
      (kronHM 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m11 kHM_m11 (by kernel_fact) (relHM_m11 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m20`. -/
theorem ballHM_17 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 17 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_16 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_16 hr hq hc) trHMN_m20 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 339388333310057403946747499790096840287917315312915512267729432884442641886894712407833498310023834055799415806573040437298814469825089825452672860312777724023270594810902458080314592029376213199038905691344061959644605477369208709139257711197480468836952486776191824274950915203831188864743372303476000346951393706767716198587053458767540954619085521347810766018962361607540967972427196750277403496661436899889645164667065176385580274394169252616933151086171282015450957889676280845638213721256853631575064574026848503482185391326509513095778569671105216688603262279832055787195016132020175148475778540493832075233618080844106055421253386240000000
      (kronHM 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m20 kHM_m20 (by kernel_fact) (relHM_m20 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m03`. -/
theorem ballHM_18 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 18 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_17 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_17 hr hq hc) trHMN_m03 1 0 3 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 91975282606044837551506633849837622838218045192777971540549693779760609876153833468649961419231103540328435299446137751432306799427643496658909924495346919576176986961629191173630209737515756585346876924661224149170176800759513957860983781989892144101738050660499388299676548541224768481505225390600303608136275447724830959377765301859534821370734655742890174410035800776780739151713109386376993634967916278276936103779982731141475342161840385195077065132500777485528415982944932116640229436383404824774361609515405500868049411867777543647212022325252010565065615693619831329863811554666190053973144230277473549552720068467295564016469934080000000
      (kronHM 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m03 kHM_m03 (by kernel_fact) (relHM_m03 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m12`. -/
theorem ballHM_19 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 19 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_18 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_18 hr hq hc) trHMN_m12 1 0 2 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 54804219818454607645725939024067898565034605203999451126026788052546532313742503398893773506191583096229905016391615467800072715733615418042751381415920813090482659799577026357202813731030001912362959520504893333875100855898166701053663425158649185710373719053464653544704805586690503572558605756083519202449905925912457497661923285539773295652823635752138328665191618600485270354405701825155915879826171404899962338875583774432197463891241696137178362161954570439677600770706011775641175571988588592107679059897751632283720415615013272223969844602915309276224585267138845363933981562578340854461684153664030450656808021015028476486898155520000000
      (kronHM 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m12 kHM_m12 (by kernel_fact) (relHM_m12 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m21`. -/
theorem ballHM_20 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 20 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_19 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_19 hr hq hc) trHMN_m21 1 0 1 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 59997855902561590953814019707433446935164117399019325407332815999679067899447326426227921950259487826166930706384894457632556479086323099417891323671595686705886272071095802313263267867279401977001044524041381433021619262735213987486559849365797416128407364378597929114112215248406049511301042358514494594013800905784723520265313180098000249052409721837283933246357352839443130413871686992900280892929190773587707216488822426262463309490776529721290416100881971514419617469881884338868298143825672512032942180182954825966111530858017733179295908331255717763340377344494255084553788240652451230823088861901271028664012659855940227017044131840000000
      (kronHM 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m21 kHM_m21 (by kernel_fact) (relHM_m21 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m30`. -/
theorem ballHM_21 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 21 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_20 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_20 hr hq hc) trHMN_m30 1 0 0 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 127452606177848496333884887076488876369172628971270125633745124877820187564627762142687170003736472137453372378678280510794364914918214801800759383664646215655270876647694073502445215351262396270003026309613527405652616080969184003674667076899450829027815584536153692015863766381687517640662962556469964186403320012695130351229481887386841639144716999661538829407647393239949530648473019807990583319618014903803218401910577181537219399557742865918724558951315153815677001676471791299645777604258464206125521221590148442746972343521711519640578748322950966925681126025387551360280444990813011763459623749331026992946718259811669379610711162880000000
      (kronHM 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m30 kHM_m30 (by kernel_fact) (relHM_m30 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m13`. -/
theorem ballHM_22 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 22 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_21 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_21 hr hq hc) trHMN_m13 1 0 3 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 10906319133217277871551139553141620021721400555167852540238098985092883907800384657585007148251448029843853290937661455560782100971920898299368378822785871234149609594014961760049074524605462011336972854226827385796260634118460095145072265748513756364503611735985287503997894376402178055525372020167662725606245733579567452221346386157177590353610153962327141183078330763429780832714771001193987624847950323823134202777767867527652409545394351726796257907390944567577731790329802060226998270365554665843250408658509242768840922933430241090977833051159829556217044407425496719440710924037455612577923349093997298016259028187082840468021575680000000
      (kronHM 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m13 kHM_m13 (by kernel_fact) (relHM_m13 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m22`. -/
theorem ballHM_23 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 23 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_22 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_22 hr hq hc) trHMN_m22 1 0 2 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 9632418178738586272136255664878975892193018144456924288615981296758889129960343048320734207514159920380031711399709356028401964618682700841293887250198618083603141592679413316582395422308044365425645420892511639060510999958775014847652691343398880565231809115173613996572421803256571996706224563444043491038574375211716155580196142801694039802495726881861972732533700682260935367467316544194962071488982803429766512119534233675555872002892837145458214399215260723137721457193532489773722669449447847349467499515637099370007533658647312694441817772376493353485831606476833082476626734339907100328124215360395395356383178171584026857523118080000000
      (kronHM 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m22 kHM_m22 (by kernel_fact) (relHM_m22 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m31`. -/
theorem ballHM_24 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 24 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_23 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_23 hr hq hc) trHMN_m31 1 0 1 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 14673378201978703189364376432670767852847977736437398754423066559905664557395726154247779858470569013944970678816948327851936965713278731034767878127764519631077370657725513602832704103764863819597322108942968177338701371226356154585736648676040662246292984964338852848564248255008171793747721697053095354544203050213442568335183345371694881148603973220144474617234690205421527026032062474210520677350024146789880165981008832482131407111142963250472570939286694041188977014409074466001529916817344040375307458652420075268927253764342599753521361584128458554957283573063578414062607300720721980050872400805170576012948570767021063708103147520000000
      (kronHM 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m31 kHM_m31 (by kernel_fact) (relHM_m31 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m40`. -/
theorem ballHM_25 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 25 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_24 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_24 hr hq hc) trHMN_m40 1 0 0 (1 : ℤ)
      144 108 48 230 145 49 13 8 19 72 54 35656910957941611293249114647439250696251096296943503019411917006450192856767486091979000378573039546647869710382441159786447497392459548609111831170950917625215714229444132372337599334343607372083741943770479173249374079334284863401547371966111514189033351390051999895603315383049899842364459266978327679880310907254137104405923193388903088449092202702847769687246804602098418819226568960737260935067342329319482783579883460149242731664345799860545174248112716950208824252687458570344066787182927343448856936783829528162175829637164536646256599855483653969794618004970767462958652508818293848671473805573116124325574565008837477382037176320000000
      (kronHM 230 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m40 kHM_m40 (by kernel_fact) (relHM_m40 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m41`. -/
theorem ballHM_26 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 26 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_25 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_25 hr hq hc) trHMN_m41 1 0 1 (1 : ℤ)
      144 108 48 225 145 49 13 8 19 72 54 3716001848447456776247582385432138402069180259761142506075114313398061014197240287395798613941071447273869863396089624146015822708863635156836507142205512286758727870155298809326363127555014030636612432082212083724925665088932814197124699144165604280372628064091179123555135274412149327644517592322116139828625878746880487833543317462017538405613291057376313481176217367320660819760783153022396171716409966615242040151219180291610757635294461685798496347324544895511054012216269570198534553793935830237808165160008130578560835554863935875382170802901689350807707305057683176891098140452566796939942478554305117682811941171467134127214428160000000
      (kronHM 225 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m41 kHM_m41 (by kernel_fact) (relHM_m41 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m50`. -/
theorem ballHM_27 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 27 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_26 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_26 hr hq hc) trHMN_m50 1 0 0 (1 : ℤ)
      144 108 48 226 145 49 13 8 19 72 54 9202536261030487549810041496352186772690270698676100095648276512110838582568572213601590253167783035221983660358311799863226621445176344384176456070699056625326867282514097913723486419213455557518649767316977849394782969572238113590268430151784794752818292426900742627163772509992416348472796990939064730735196340708199709507174307060105821793244510548786644462981720395521834891195465027573214785070008970113322493755327059151298691718453293518432793628801734915796892937768487146380899687293245808243566718923355404079352941703664725193171069196206660287796863860203098545572098520752102806009725800726154105425364134396926071434693836800000000
      (kronHM 226 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m50 kHM_m50 (by kernel_fact) (relHM_m50 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m51`. -/
theorem ballHM_28 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 28 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_27 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_27 hr hq hc) trHMN_m51 1 0 1 (1 : ℤ)
      144 108 48 222 145 49 13 8 19 72 54 1080849729753684771245567598149312341189418104844230123834634330707176151872785766427865776912387858366241311631288316937822573575848435163711273172887821452503541861697974225364954241417841926948746606874534928214185963835068999603414942964271847535736057905703727118608818818362134788406443024730056667134028721590212210093565314339668333346773445892772046488835566729090014797798499090855714630375310365036937317543503696389137347465286488102549419470564782096552834020997059434433110405009283081850321458558122274695771804604582671747440759769817358671205158960179578629855812068896199193874101109981930600954833668446390307206106972160000000
      (kronHM 222 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m51 kHM_m51 (by kernel_fact) (relHM_m51 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m60`. -/
theorem ballHM_29 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 29 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_28 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_28 hr hq hc) trHMN_m60 1 0 0 (1 : ℤ)
      144 108 48 224 145 49 13 8 19 72 54 2446004948171528906091139050814874504247643230809218561569500524685707629313307488875712745815460577129949890702750520577278973026069008066241392082817210288132170100271872832440917694701320716713995481683947965040601658781980007552431606545345254674941142965653798268884735563397348867611190959827334486952659618460450794076332180643421188513425167145853952033814587925414446310530674164577206866605346984645869028565671468205817647931869277762086426729883322542254196664664911889729339766891314173620599440699469461077335250453227105293904674327188388118751700505727395469841746662498169222703084813889067429824076123771881263015405813760000000
      (kronHM 224 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_m60 kHM_m60 (by kernel_fact) (relHM_m60 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dp`. -/
theorem ballHM_30 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 30 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_29 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_29 hr hq hc) trHMN_Dp 0 1 0 (8 : ℤ)
      72 56 24 127 73 25 11 8 10 36 28 1052916002347471767162391401065641964509835687504942361618444630435255530241322654012277055425570726820085634182045420220561085925502789575678030037851934852700508295020979073745974811909374249718063126349565357473732232250708485155127345543668912032325908876108093624618914546983025792465005992702946940330967040000
      (kronHM 127 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_Dp kHM_Dp (by kernel_fact) (relHM_Dp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRp`. -/
theorem ballHM_31 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 31 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_30 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_30 hr hq hc) trHMN_nRp 0 1 3 (8 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 1071091789474058323570057250754879893298690304475379671195314111091334453701186040522015731405054873666980194527849239983641063577279547627273438057182540326821995806848387450118193994021797196187699764955073044262499183464614810165276790597764434999228934042816932147440592708135709888016830445218358362866974720000
      (kronHM 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nRp kHM_nRp (by kernel_fact) (relHM_nRp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZp`. -/
theorem ballHM_32 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 32 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_31 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_31 hr hq hc) trHMN_nZp 0 1 0 (16 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 2133559314350408909804312190472862410285140911650393999678931851782301690533252817301286812176993483709243126560181985997220271778221672823396077585549060848756373236686289354592803430270117824683311389255957905414882692554995243142861365624409917055183233850467038706851012557583881374049138088190994384368435200000
      (kronHM 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZp kHM_nZp (by kernel_fact) (relHM_nZp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DuP`. -/
theorem ballHM_33 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 33 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_32 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_32 hr hq hc) trHMN_DuP 0 1 0 (2 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 276681086736733520611729959608853198912268747871371883837604758954704906966844749349349755450946565054469555725862846230550205238065084171350897733322846240706609021614373276537861354598826546196585599900567391387077760748949910607288471586453356962434966551838857021242768244467266913990467883631328925119938560000
      (kronHM 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_DuP kHM_DuP (by kernel_fact) (relHM_DuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DzP`. -/
theorem ballHM_34 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 34 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_33 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_33 hr hq hc) trHMN_DzP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 1083751476881341924700391805946796822958454623640360830706690971857512831089574861861980291555834131820579332338876793094214336108052119220258668542347593914576799367096545924173188600446464779465869390967085162630857310241677139609159438120006673165842747967582501193244953649216490686326569174709763794848972800000
      (kronHM 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_DzP kHM_DzP (by kernel_fact) (relHM_DzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DphP`. -/
theorem ballHM_35 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 35 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_34 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_34 hr hq hc) trHMN_DphP 0 1 1 (4 : ℤ)
      72 56 24 121 73 25 11 8 10 36 28 540263890509005678584595354319902749569176513971970969752517553874206692000295978843870796996562038428043149021961568804310669068700982910420061164803964995841886256168897114078447808197341075382776241016910264463474096140484333800335792017843223895384520164108726757675744568540723744309755497999290765483704320000
      (kronHM 121 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_DphP kHM_DphP (by kernel_fact) (relHM_DphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRuP`. -/
theorem ballHM_36 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 36 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_35 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_35 hr hq hc) trHMN_nRuP 0 1 3 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1055950351296114519770465608258120413653793193712990314812656950664656387754583294482462942086676997267696774790817343517159052709251914891146600906377761092882172701507582887254034986764565811531664901477094978734747924884777556884050113148607385093221868396833913936486258859422642310262377856840398858826547200000
      (kronHM 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nRuP kHM_nRuP (by kernel_fact) (relHM_nRuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRzP`. -/
theorem ballHM_37 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 37 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_36 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_36 hr hq hc) trHMN_nRzP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1090690416991638093660205652476174040438390480529662980807419769811675223544468874355880574234560158136310532393075503724163181579643213411049062337410750287224309888608499000344176956864076295086090471551699938887256436466991871432545787872950417039640150063404874277536415785489536466131071656438770193714380800000
      (kronHM 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nRzP kHM_nRzP (by kernel_fact) (relHM_nRzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRphP`. -/
theorem ballHM_38 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 38 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_37 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_37 hr hq hc) trHMN_nRphP 0 1 0 (4 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 558658354233793771176648477057939976528861717926020347043484537103622369690177826900596918940814209154840221905244738019814998394880159555042641500939526860878272816690477727047204711014293694442518734393240055849165560478274821515813314577711791105724001454347711985285766824086944587708508843053644351044321280000
      (kronHM 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nRphP kHM_nRphP (by kernel_fact) (relHM_nRphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZuP`. -/
theorem ballHM_39 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 39 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_38 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_38 hr hq hc) trHMN_nZuP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1098402067214995518707578632294274935472410890266506194414526144270728156464429410618140536214012015941441808632325301935945130727338044857284147505213405208577341815211148168340462169749334921505290042183832175922396491107425512770287745496140437864814520538151714419288550840803102145312360510015134263599431680000
      (kronHM 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZuP kHM_nZuP (by kernel_fact) (relHM_nZuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZzP`. -/
theorem ballHM_40 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 40 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_39 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_39 hr hq hc) trHMN_nZzP 0 1 1 (2 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 262765385282502573298951174595104686541272798938542490440584903860562956704756594713673501394187509794840680733813797392813126608394386672840557881040802817424334007888383406886486113753558998037220291541712715785806295481001611268250653771980410171970157712557713676711376148556581710408325948121354495170969600000
      (kronHM 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZzP kHM_nZzP (by kernel_fact) (relHM_nZzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZphP`. -/
theorem ballHM_41 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 41 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_40 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 57) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_40 hr hq hc) trHMN_nZphP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 1070831435539764473665700963811741839083696421840791355566691005064064565440977529304888729075304320803492432720986920115952155834684066230538560299739648535348777735626111473423912907608770601031285062915777259256490717770054031234616183176054989720739890168138603234843739918057390769997609215185492041384591360000
      (kronHM 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZphP kHM_nZphP (by kernel_fact) (relHM_nZphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PuP`. -/
theorem ballHM_42 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 42 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_41 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_41 hr hq hc) trHMN_PuP 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHM 124 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_PuP kHM_PuP (by kernel_fact) (relHM_PuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RD`. -/
theorem ballHM_43 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 43 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_42 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_42 hr hq hc) trHMN_RD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 650515845066466559255619242733134526638519697585117692027442902555153258300977666066822494757601594160144005158370809292448760008498010527319920855239666144215652917401442327889028819744993517762735772391933662007314279809662372843162492891744433566615815969920067491616900757552720273813834099535772027888905407256683031252157729989283948837349246106937528685312001677899147557921375086006578602170947473839636143835230953991102732284665313325731229127385813704585045061611978204360122722853693848866529504803668298370880528539996369211610009662865154238803071920175191719368886550295778955017222751238059709763947830361129174844496905502720000000
      (kronHM 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_RD kHM_RD (by kernel_fact) (relHM_RD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDu`. -/
theorem ballHM_44 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 44 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_43 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_43 hr hq hc) trHMN_RDu 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 476276005881286192524623696719395339459301144377259162808638288568344954235071752100074037877591657976127780909098798169296818421867220806455907637608465377020377117964309971507172253460781053524951310926387411579850735360349294091145058409692333764488985831943511780563739554581358636562056801763269753958250698989262753294870121253223178690529736589245992313094616537620175347806857060774146745309935932979525108635144744113661618290905899557134369143156080954490734494807401793413092877217603930869635991892917584031444329393661757504323737805232600524543280709837808841675572653962383134714133992075025826772938865517424320444984920637440000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_RDu kHM_RDu (by kernel_fact) (relHM_RDu c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDz`. -/
theorem ballHM_45 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 45 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_44 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_44 hr hq hc) trHMN_RDz 1 0 3 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 263523112822303163843417784705020955571639721146432582959895915788088247676062348498701269240013042357252308971284550333275432526094025949686367960224911771679702403461286987535430990078626908882130971304314092260824018830114786236941567233326746859042505815561757555916267011813829574957951121231650498307636040161063915472825311065969324232805781980138080010076202349126190665112983339161058146006005236855262579668000988241479579694603796361903125677800546286070671037700417218866471088997698177058389556992020120289323091313348901724675989491039447119928845125516932898039969671910995016723096371005503259667076775464192327614628920033280000000
      (kronHM 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_RDz kHM_RDz (by kernel_fact) (relHM_RDz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDph`. -/
theorem ballHM_46 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 46 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_45 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_45 hr hq hc) trHMN_RDph 1 0 1 (1 : ℤ)
      144 108 48 233 145 49 13 8 19 72 54 78935184533931195876403632757920950697145660512617777766138039639259718588596641582940871061286920957995570026882171318419914689188239158164466421185154914147530486559713337205976406639221380068124075184676467543776641900643353627666464393555059486026229069099704885426269522343890758402683392665134127315297590592060869412920807705211142580576178610586515696795498378032283635750465411345337181520785814131843321115560873210771761986914246436210729320790035258086634399494549524322902783356325063617168996749475494475171655519061659321631679234865896401442879010768302857885069176551442696093331249713363181963687716583533527521304437063680000000
      (kronHM 233 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_RDph kHM_RDph (by kernel_fact) (relHM_RDph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `q`. -/
theorem ballHM_47 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 47 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_46 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_46 hr hq hc) trHMN_q 1 0 2 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 3144763156916024287045877918683326869824271934064439069709509182267533416615297297793674332328145814790148914449754994090100545411343494998515499665442427177904358010165833024289678983881166170746746285548809333959980958198256423274789716145778822978842219000210086585999837155477437216241684169161525219508868866747411693535837430081356640578193965699823323879903159902574539169322286979268528196162437216794156284621347134674671205153748557716112228791332533859419959433116520396328057821342331591305018583534669507492160424653995690559586108218064664616587498092087682243721193718587733976461695761765820780126754229523788932522522359889920000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_q kHM_q (by kernel_fact) (relHM_q c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qR`. -/
theorem ballHM_48 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 48 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_47 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_47 hr hq hc) trHMN_qR 1 0 0 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 9517365200162555504596256478685951919950274970654607777266920730575967778935131759279870447109249073395905853080069260909187895510255527449854477153876767594261733417830038363700305400691713100584715735729285864951332624614738914067691280795081401986800606983277985218312499360255791282980280641718557243669117720713205708525384907668812292611394340940770088094517059651889580908317847958535395515562374511402622731364300694249562953273566892564279433568155892082792469272707908686292164701870920152983668544358361080885518149072239409858919364356862801121572334752379513027589645011098465898318009601979529160684709481675113317507192858869760000000
      (kronHM 245 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_qR kHM_qR (by kernel_fact) (relHM_qR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qz`. -/
theorem ballHM_49 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 49 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_48 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_48 hr hq hc) trHMN_qz 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 1761258038811062051715367032880578091336175555556565285602773430857661072471132989143303818751798942188985079048410642897551903364603293109910150740573740363422464044652667994417523562946764456627467214264191448048160803566534794573945495699832972221995084698643379863473905119221266153262236065118555679234946414716221956423919174990580954559758508212322027841429650939442940587575712469695413641323234057765301445617244426373973434197338055035345259173281854875170053650457478133141478474415748193574127234010346605213624915359345928421010227316125352818056660837453146095164098910946201171022859190438988459513839149025940112211755768217600000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_qz kHM_qz (by kernel_fact) (relHM_qz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qph`. -/
theorem ballHM_50 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 50 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_49 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_49 hr hq hc) trHMN_qph 1 0 3 (1 : ℤ)
      144 108 48 238 145 49 13 8 19 72 54 495836502576684350547755000191406669843756079721870028612975954536309211044588996286326085409277212386769571084696569480816149622300844101740091267550436255280642048184924834869308331086712255514265582197322036972870402389252515018597362808885054408628973805686815659846729382826719592007744011320092159511942773618456492657366720843008008855944237952787559517511362101030352947083806812321812222118345049104057455379283077993770680567934795151399927376110865790465369723973441922476733177810850987945975035311228778653801701542844452990640942145696654968797022092100697496830454785273545998585391556637953816425272731725320320874849752842240000000
      (kronHM 238 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_qph kHM_qph (by kernel_fact) (relHM_qph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P2`. -/
theorem ballHM_51 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 51 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_50 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_50 hr hq hc) trHMN_P2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 14872052404716143212589778506217478471221618682091042477833184351212302932665259770730159176173484187467445152515125371379155714370781664110404085964579391642078453030698969960711797490668492298374577235289159827917800672399986979964018332982751671063494355398616053862192828186711760166093934695608870732480704667913849865427686255249427182817022115925534971402052506300551319346679790422840868465667243009128533548722484053793967573543959700952382036316273981382565160643575548044853827091056702789347818847172790693981515448098955575638850907749628169869562104348611089699987024587330169214629686437064268316909236577395868402519056182149120000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_P2 kHM_P2 (by kernel_fact) (relHM_P2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E`. -/
theorem ballHM_52 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 52 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_51 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_51 hr hq hc) trHMN_E 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 17416088727814237463512267347296346198433083558272955198793051919219117078448312232557013734845938691301198403619260508578941545124045935296155124883549560308122932654681603784634655936911169024133022714488468103783581218368583459712788956721570195557436615914035919914141773818609215048409942908967993383522592074462167917435896529851686983397704856069279637293983475284699338326450876662165944523780540833341671976693022832716993390669806675329485357712555343292600335193084106347456851796508282072115126428415884292281694373843384006800043763199542571430211961028806088801856205245599978091830497823187355523676078811326497659813851761213440000000
      (kronHM 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_E kHM_E (by kernel_fact) (relHM_E c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V0`. -/
theorem ballHM_53 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 53 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_52 hr hq hc)
    (step_exact (XHM_eq_V0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V2`. -/
theorem ballHM_54 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 54 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_53 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_53 hr hq hc) trHMN_V2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 33253841429678800872387449484730347622224248643157830034866623772090603307990587611016910124409261437486125070445775877021671029815268106627018636379857084953911749254573636163053213026816455892445650405012960458399741174361341078608316823125214837991139838904713255000591120038174788046054096149325294081358067758957674607518050385342004988056848997016575752122536323459491746732986280351103814904913130324727804714686727443665162724057359656687111709941276972245992635699597029954935509615890828392399532968496868567692497147118024798473179831232903532862681966289535708171783554709777452772566753776048374656293115969309722210752801013760000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_V2 kHM_V2 (by kernel_fact) (relHM_V2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Vn`. -/
theorem ballHM_55 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 55 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_54 hr hq hc)
    (vnodeHM_Vn hr hq hc (ballHM_54 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W`. -/
theorem ballHM_56 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 56 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_55 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_55 hr hq hc) trHMN_W 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 589405693540072225799344217586394346548163576597294269067800594777221887176418857536333436522192285047748980172713072064979168978164637600890022545568752966582937350038293543091419545340079020728086263621507438889979301762928580921047494277167897631749036997689358488535947969413497364976244060961067234635094545319179551597474713467780057350092114543558624228979822740566944396083126555377178844059361116943771165482076257070122969125194049367043867317233886455931348474863971512109132900899825369988216165542130749314880927404911530909392761150018795226700731980980900714148792348487104189780161038346909512222443333107377211461679930408960000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_W kHM_W (by kernel_fact) (relHM_W c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W2`. -/
theorem ballHM_57 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 57 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_56 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_56 hr hq hc) trHMN_W2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 17688256736765018470688017933793161974754240697303480554524351065185003134434479599713991331827318851613371933947271090629071058554559587135912500607844169711892530674077644210663163616847834008805190255322063161571188483668949367198978309908551209616364840570024810894547489017879723414082881143089435044681278860608564620319750645116518372252214667831527676713338972684918695182293702777470751334246361169047289026280766994300908890621684634524857167583412918325115227389970164095260232893738211150160328023654727205942605554284270917007505271491905066947626952532043221465985228936139903329569380715456522468152915689382864568516966864650240000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_W2 kHM_W2 (by kernel_fact) (relHM_W2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W3`. -/
theorem ballHM_58 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 58 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_57 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_57 hr hq hc) trHMN_W3 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 67665557939454759617854295665272551106139925961314949225456538815529757810022913075320681399392971092975147426191239335210139298930928505765433242691791861979432895788503454761562145224174689216454122023501897367466963251786099145511437927227916353071786304313317537012794661442543013732467797296800506094280892206980590467783550535320789885650073047460886000141393609931040864076533509877473294432662081608818066961976793978400949724354569188234015490031698148777288435624216913020152581692964755473862905968827656106652309883075798322303981703898234358283369230840027929987041977840335689368754657932336385818760541470244493123750036221460480000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_W3 kHM_W3 (by kernel_fact) (relHM_W3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R2`. -/
theorem ballHM_59 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 59 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_58 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_58 hr hq hc) trHMN_R2 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 339388333310057403946747499790096840287917315312915512267729432884442641886894712407833498310023834055799415806573040437298814469825089825452672860312777724023270594810902458080314592029376213199038905691344061959644605477369208709139257711197480468836952486776191824274950915203831188864743372303476000346951393706767716198587053458767540954619085521347810766018962361607540967972427196750277403496661436899889645164667065176385580274394169252616933151086171282015450957889676280845638213721256853631575064574026848503482185391326509513095778569671105216688603262279832055787195016132020175148475778540493832075233618080844106055421253386240000000
      (kronHM 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_R2 kHM_R2 (by kernel_fact) (relHM_R2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R3`. -/
theorem ballHM_60 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 60 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_59 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_59 hr hq hc) trHMN_R3 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 599539263960654056543720565186085921806445923958084913407891132104947597763453328251537088938087420624829153199499360308711333649715039027073947735435643653536509934195067880344665520546957147216701499767114148788642930377265944641798501860244417694673648090720138607797528032973088267669986488976627654410262546833857626221558396654754813102105462091509810023475174947319264541697416063368066750778711051358593839503480102094915754991714736806483210523006650800151098983841129638443757829882856492528703167530359224516591052059162545182471698363369274107936987611896946509993172593620870047243324816994606060030637536619335421007077247549440000000
      (kronHM 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_R3 kHM_R3 (by kernel_fact) (relHM_R3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A1`. -/
theorem ballHM_61 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 61 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_60 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_60 hr hq hc) trHMN_A1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 9481773543606179427951476339790816903857643706610335273660188984771052148741800345576588630630369847744278991325016219274093377041123636678470584926165133554714431468151786485730893282412263602962030564550155089184143464003199986092017008340480563039315072686752252227956791260617155306967962416636065247155377871840652187007105777617783818080738087579415452088403697379555587466003459347533959759876724604202899449568834735129659694177802275917630950921446697527727532257878639340600250575008451911349673685674561405367713062421569016197035916513202888418049314875764225213553333485563339326393299267315158115124705049068871473562572742983680000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_A1 kHM_A1 (by kernel_fact) (relHM_A1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A2`. -/
theorem ballHM_62 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 62 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_61 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_61 hr hq hc) trHMN_A2 1 0 3 (1 : ℤ)
      144 108 48 237 145 49 13 8 19 72 54 730432359867103626479049967565086396169192672947130503828608230957785524375994010894111549288129898143182535993961121086305216944500134085152743183148733310654292895454541641481173878198075063615112383764126634265178392440577462237590680569580814165959737533544120841837105438770141269848446995844913132502607782376187280088788507969793221610439637355265135691673930730016695046349726937237289289748198296792538143870524808993553803216395903944314511103385277407284136435326374217490053615482474842065836299556430215601827873460926765527207532717488052357608492846249479696497877683414122007812883625766727571601858798237923395513611316101120000000
      (kronHM 237 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_A2 kHM_A2 (by kernel_fact) (relHM_A2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K1`. -/
theorem ballHM_63 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 63 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_62 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_62 hr hq hc) trHMN_K1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 4528888578779386325642039698442002936711929432130391565536353389444460025718250991207822456716156166391504321190191483075440908171071872324683487750532954025536975303629095319876681169353648875580215140548955514225765541105386224112408507660218604201364139511150048935395430185342022069679068593045890930711665753748976819718296990547673740556086121371792333178127906263135208374253473727172598882131025732288728022533762706640616964096241616510438512069273071233744022356343348108744484252454569815065468618500205927150788820360881205072405677991265507806945915566421538759070438555430484620553929775565272318232035865068067045483451693137920000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_K1 kHM_K1 (by kernel_fact) (relHM_K1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K2`. -/
theorem ballHM_64 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 64 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_63 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_63 hr hq hc) trHMN_K2 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 3090515649249577950944629775061340029724916400958337458995471616286783703039662663495968674792054082261585731540619235871000099111702669799535782636724832735603963799602645529398007986648332930302408777913809029525087021625699102490553375547365926220742550956823475223938229504457971041310319397371619088248468834958087815250416919602070852656743203630305053482998336093367059232979208165900243166064945675927771970371944600030626841542300185071162651328640058409570245164573728402569775513716168803236687972773674114276492271276138026596392935343893660493078581943816409604504661584299718591454360214796366067271980749446650292236168472821760000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_K2 kHM_K2 (by kernel_fact) (relHM_K2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K3`. -/
theorem ballHM_65 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 65 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_64 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_64 hr hq hc) trHMN_K3 1 0 2 (1 : ℤ)
      144 108 48 246 145 49 13 8 19 72 54 21153542468860537627496101899490933106351443762870448036471164216931252028130782481934348701509588495359054673704907465805358759231495879458948072932273881442320918327911965640758618322650903123539618716526275424122654013511599992599112275113527253823643699024747865320786039835860608958735439257754535752276046342921990103255806007672233137649464761226122325470403180850645180128074931909132509401397471978019428072282283321728422781754400486833216849693851261081084271086183600046419026510195190447294250039828701470212112702087632320541507023514703799659661086041967682489906876695743857592517912764144900953462307936554050302484020367196160000000
      (kronHM 246 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_K3 kHM_K3 (by kernel_fact) (relHM_K3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KD`. -/
theorem ballHM_66 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 66 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_65 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_65 hr hq hc) trHMN_KD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 2670703095359206938577255132216773026691915610479660678463300543057047897968416411167772622487920017107148311510102373001780579057994385660507554635893860623893750798304640302519949604032181668278726626260499545656487660558812170938108458162067028178313458805111805007786706745581529191309294101811281916708289747786416121588066146670711520014680688055753531191344900780520507938589100835781702288483011837380203823853734867697178559718438268461449606617095068136209178254965899105326014885052244431880060472977153736633848037299672019572521905151050910972362068546969572464262030680813458000727415108406668273210167239826978750499231146967040000000
      (kronHM 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_KD kHM_KD (by kernel_fact) (relHM_KD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KR`. -/
theorem ballHM_67 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 67 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_66 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_66 hr hq hc) trHMN_KR 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 4803316586942668126311947838684909403510804310855156838640421475182997346934142836643608386399481543631530080366515504369882820871670150694076869371017378685244935700529314016885972586428415534298447580461056224577719485141145981461187791221467542758523048611019364549883791776085344223573156148689137852060335193031025332007827678366432995312339165089422408538009197211049401431810586949998410384486278369990865186630862452329224033000989332170291465480735347964238587577412179426103140078223254474398878313177341718032048712457250266081785865011246798123513020472911539131862944561990864509017521972982785025230509666925560089179458801500160000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_KR kHM_KR (by kernel_fact) (relHM_KR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KZ`. -/
theorem ballHM_68 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 68 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_67 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_67 hr hq hc) trHMN_KZ 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 43666293609587046145682573655024964304507404991871906768340247169788494944056523480445743504790571250347194354111372650224568784162139485549642245453643146012367850305003697424890508840813238964876140419402280276310356018150355411578955421244875894506570415614075449737880200474203068407514121426640529973735516271297093816163988947044593937857231328502189680478959120031100676922507148696485289732916667939007095394696715052683369027625228678042545381680884994359443743702793375050840753754764720230610972042553883786789292520422392682462324957686681354097734153272977255247469564709991441689075124255230860241200639609335341100032763048755200000000
      (kronHM 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_KZ kHM_KZ (by kernel_fact) (relHM_KZ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dt0`. -/
theorem ballHM_69 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 69 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_68 hr hq hc)
    (step_exact (XHM_eq_Dt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRt0`. -/
theorem ballHM_70 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 70 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_69 hr hq hc)
    (step_exact (XHM_eq_nRt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZt0`. -/
theorem ballHM_71 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 71 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_70 hr hq hc)
    (step_exact (XHM_eq_nZt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `r`. -/
theorem ballHM_72 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 72 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_71 hr hq hc)
    (step_exact (XHM_eq_r hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P4P`. -/
theorem ballHM_73 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 73 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_72 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_72 hr hq hc) trHMN_P4P 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHM 124 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_P4P kHM_P4P (by kernel_fact) (relHM_P4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R4`. -/
theorem ballHM_74 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 74 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_73 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_73 hr hq hc) trHMN_R4 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 1167405143809045807009624589566552443091558437627486276723249485368552801777112029134950037019819009659828132704240369645672796728866994823513299620780656969024755332899350863603199760789374645796461146550636524482122530202564879600616879865981782273290758315275937227892003804416210493723491165538434233516912055413170495808386534125582412057750432950663939815448728908797727612515731176486110314069386785176656512129103649067814915776351969812840601477565853381479217952302761717095446366437676415563790483797505305161681643082634828632876143778484847294601511733130626117286271495687236804338558560938599004554805206792145710681237057699840000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_R4 kHM_R4 (by kernel_fact) (relHM_R4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R8`. -/
theorem ballHM_75 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 75 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_74 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_74 hr hq hc) trHMN_R8 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 7292113040522658175563586308707500357956174843291015972829292909933930517369268658672686118596948601043132627686023000116920514064781725970478347331334046171136884339689653416166108861450958890412749126819030164220802708842588587861944665306945653569607623709693021891219645584329092160902899529059196921043159821165791797578328111618552075165135250779646270223281535228535703997826348049035000840989013883868258706202456394976743555980657820674235242521448034474046098318969838107052649133849002117767075937136419115250786354002511169226027889842019523344422243061271864258511637900501538672228333556950477654649637817809623575535353331712000000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_R8 kHM_R8 (by kernel_fact) (relHM_R8 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P42`. -/
theorem ballHM_76 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 76 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_75 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_75 hr hq hc) trHMN_P42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 40061248601539177621153537542510534140435787056792628523325562724187477210118001670814344099103454901777480530356625998334676687954166460261833698400744526088574342014113214173936294230202931557446690657660895329629271006241174074158034205817864916547585213611807191986028539333490097388162354618330992653968438205326778469964912814138747111585821399261262303185038008920647760907066860586166682323166540035966359196601641435248311212493193087115249466087788271478659739209973988346093409942934148967177324992527595965655095015533627637418615853636584233628282760597959670446763592936232738839298883856041661546540233276702328164637939041566720000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_P42 kHM_P42 (by kernel_fact) (relHM_P42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E4P`. -/
theorem ballHM_77 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 77 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_76 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_76 hr hq hc) trHMN_E4P 1 0 0 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 30132578300564838031834094157539438562674261448452229472466523095870329468230276342173880457753170571633356397812774798833258062878406087815470001754673120164161686028171432111954956435787377096573199233588512747128671148388224010757516977816079770019197348297506878712559220510215410842288433830457203530273184011556875877043704007403296994209810474026633158112559636567528334532458675761796071063418666856961762000142564427147707090721325147075127068194590784519022517962776485425595628885373259321061041838339926006333050451302282148599638075690988426316801949506624759056917881545219791830344886761073655862359206653762647809168235844075520000000
      (kronHM 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_E4P kHM_E4P (by kernel_fact) (relHM_E4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PP4`. -/
theorem ballHM_78 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 78 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_77 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_77 hr hq hc) trHMN_PP4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 24424119444948723263203681042732544735599028502858990412356114156313805269479246464853714508358353197525621208723428635978263851403571928598930899200185996221313230156942237142249124311222756334254530604948541804153224404193325565583709528959011654461833520351405307962269739566001010730914460389839575969157138650750295903585508445309838196441415734766724547086025377318621966151663621896008402381342039300603960682888690833349367015246286409719007490000485381632015278916975424152009515923191999088988331762689007695058371870594444325647394580096857336739396636912680680944370706602245638931926933952894330428098419893981210070675249147412480000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_PP4 kHM_PP4 (by kernel_fact) (relHM_PP4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `QPP4P`. -/
theorem ballHM_79 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 79 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_78 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_78 hr hq hc) trHMN_QPP4P 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 25092039551700174405314756456683013323950071706996137567205314477145498966063575049777052106755062060408535470878280500892435693065105060440009561703900490796617673003059368459945371679970566739868046659694357609918535495476191874282173225296154489935606277225767196653056970802909448099487879113385062471577014455556096396993873856121571798247575017852837481631937459782821695978364903905536563954434961445688531157525180882928152038200681033343613113844101559770637955112016045324242451776245979447519049599530542052448616606621025213688387946165348309774107796373080022864035010215277596709973050341903611201540486992525870256745389385318400000000
      (kronHM 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_QPP4P kHM_QPP4P (by kernel_fact) (relHM_QPP4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V40`. -/
theorem ballHM_80 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 80 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_79 hr hq hc)
    (step_exact (XHM_eq_V40 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V42`. -/
theorem ballHM_81 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 81 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_80 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_80 hr hq hc) trHMN_V42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 773960202119493825113551624328221268633860843279547622293053695564621186216579319055601222870358290558949346310523009732189954678526128069880019572676904117786166725656147552572517966009725948944788375106098257411712244483785221395815343415821191253424983466757190820464685812438483180050570183560876873531905092553606860722155361858584612730756103469989351194939723314301720363269089909256716572747533601224137192318669335487612745920447452173313002537969194912115611253999738350519565658373027199956980749306643019280994119639673789649246948406376792750126418430725102845073696965263689325194028016485535998978910470864605251018518691840000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_V42 kHM_V42 (by kernel_fact) (relHM_V42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V4n`. -/
theorem ballHM_82 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 82 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_81 hr hq hc)
    (vnodeHM_V4n hr hq hc (ballHM_81 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `VV4`. -/
theorem ballHM_83 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 83 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_82 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_82 hr hq hc) trHMN_VV4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 2231336220262564621759084449047905497927675242303471030272244701591401623668667241929001182146935381243442038992223045096093177458800608402543775389738621645945972313292022216855911783857224070874062739703662835974799990821275318431330314228049334420869176121080717937694282407961151493311249458657804441380115451213425689637728630827249283238464783913257009818950636536054188927938337345947091926604260748433794400463005214108288482935832402967808640754316699523274047906596374679527573037402378273572889959298266532116370056505775579239516191933483680380418389925786544840555086850575295754048299049755862722056307286648755785473479147520000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_VV4 kHM_VV4 (by kernel_fact) (relHM_VV4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Bm`. -/
theorem ballHM_84 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 84 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_83 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_83 hr hq hc) trHMN_Bm 1 0 2 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 90928894247439232932094099965711174131358633471778819294535852213692030796554164251429266199746223276538267669652793398104878306882441474103677627233321151607166457884486315825125675650240319472377757988757866193010022106322957357933533934072214208862809879475567203162556205999052184969240387368062961760571357921293283478679531417436429546326017267697825927284618389590399785815119323344992440917877229259426756781497967726239712434730141704468696053217455285611606042010177933414535138789105096304420362520754214564133569383764820833478206852927016891064485398468299079993675462513335416739762763186180088085515822267651921658772413480960000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_Bm kHM_Bm (by kernel_fact) (relHM_Bm c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `lamv`. -/
theorem ballHM_85 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 85 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_84 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_84 hr hq hc) trHMN_lamv 0 0 0 (32 : ℤ)
      72 54 24 130 73 25 11 8 10 36 27 0
      (kronHM 130 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_lamv kHM_lamv (by kernel_fact) (relHM_lamv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `EN`. -/
theorem ballHM_86 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 86 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_85 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_85 hr hq hc) trHMN_EN 1 0 2 (-1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 1607151888980161600851420900328643315879315456731218540175591035034770865644205460948537036715808092501843724676615457687850284778605121460661003469867545700162748555267795702844526406742679752110681951933957223793583597524002150065064836883654965927945132143421847043386842477988754100893005109746635323980106953264197996761544882995998357371630174556245047466228067043691030030094461364288981149696726820443265669746049089814347525562317032510912881418919808669061016102983015919336915286581181895116876128661866860255211871629823105523124864631996656891603575639328401474567263273234570030653648376462078242034039806224247105222876038430720000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_EN kHM_EN (by kernel_fact) (relHM_EN c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N0`. -/
theorem ballHM_87 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 87 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_86 hr hq hc)
    (step_exact (XHM_eq_N0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N2`. -/
theorem ballHM_88 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 88 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_87 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_87 hr hq hc) trHMN_N2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 225934178001885608002445350167681361034329431715689704901134060772832594330922916441084566513530857896419081766263809305599527170317183527237063285431498283642156255686929636915607903937270762113553296184145214980739993429892836885217414924821200119856426446479445930316008185595828341476640005273886848328612157071280736425625664236088709072520486359542541851752371429914172554034932836083629259418225319738255094366109629278833319338548507261414454235158281983344824654529683711694546800465808217483090940491147256377613117795856574606041059687160193931121239950901490871393785971969338820823924057445924062758530750274972422291662322511380480000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_N2 kHM_N2 (by kernel_fact) (relHM_N2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Nn`. -/
theorem ballHM_89 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 89 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_88 hr hq hc)
    (vnodeHM_Nn hr hq hc (ballHM_88 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Fv`. -/
theorem ballHM_90 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 90 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_89 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_89 hr hq hc) trHMN_Fv 1 0 0 (2 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 59206428743868138217879109156554983687536148876103736245522074705940530306768831159575481508142553828834512506409728991331456756465999254245505912661120235098036494976436540487221954201693277805758429830592639419691436571321227998757107471100222106906197986521066790675198071842975866763257261698217928757065509113438886070956571980441670967136333366986309927262191149248621341504043383344204158396721945306264281936235194883509809292243785273176414534565851921636114583198219663270835526306027073491949351270116058966783071756928887213996118632294862251016478545802342254662698110243246414052796561379221874786031714988998001329624516258693120000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_Fv kHM_Fv (by kernel_fact) (relHM_Fv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YDt`. -/
theorem ballHM_91 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 91 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_90 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_90 hr hq hc) trHMN_YDt 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 5869822644102972688506344711613995337630470191328057198081575534503128973300937383929618530042638307215894522581736057136598485378433143847295674350820175526581776875774481042122242303361541241909561478641034520509762266697560973639001709477678485786643279224467170581645637344495508082399956208989202137818341048621178118376936060812080487078517055132765100092213173029715524473122285302970872152163993166069290696230223824380324914806553345016596307045770453476483503206627408660198112948484155031717708045903774405844440264961392443823399710437202264323003109809852042849718651090395454090456837582465524112818982744136265284250741537505280000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_YDt kHM_YDt (by kernel_fact) (relHM_YDt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DtF`. -/
theorem ballHM_92 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 92 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_91 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_91 hr hq hc) trHMN_DtF 1 0 0 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 1839713554317014822476277148332741233570956221576455288408141797284782537689977615433550931608765000254567264950270478648808320641358656425749053280930958843906034968660770692234272810881557835131465666384335636155216831395619459206668748794633270641990305768241046786025253090364368289288953243061452792412682257489807328669246835037251109370531476370965561085991906853595412819841954648479151831060525793451314560259971338547374950630084795940390610014283479498350038603208203315872568971131240952015588635766200469107419613050770458123280080225465976459007929183327197307728805842102441894879279303832612938916454057310303919802791619461120000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_DtF kHM_DtF (by kernel_fact) (relHM_DtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnRt`. -/
theorem ballHM_93 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 93 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_92 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_92 hr hq hc) trHMN_YnRt 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 8700635462105548848679452677932370146981838252734629190914765276090814682861700078835948492935823974296896564160777827459648807476379381313345108903983117379794666806464076665453236330164760895316469044208185831320927783347697075344542824463310200502708553252647004482530232958959085579320370491363929620536717474083419187361973947889139545461852765799324796230109316219785808692759183190093779838458251037799225310027036371693102541092239576527560400398320514071682888198343107478315775361587289037398795131569991443674291986877219711950660653617995951657841043359608799056592053560463047992560689056753941967346051997420610684507574501376000000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_YnRt kHM_YnRt (by kernel_fact) (relHM_YnRt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRtF`. -/
theorem ballHM_94 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 94 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_93 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_93 hr hq hc) trHMN_nRtF 1 0 3 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 2604484844464121323223279889233256202641336453340287724126035254604648491049715877037216088863865845477250200915364402556788966974281783576476509154098801422478395518136713675927764632988297572939716396334855481049790363165528454597642228977067742248704110885325803774681244789340050832156947924308624864612953040737595145132270386894810098764001952274146718859029830027352422976353178430268638763164644131826474240479990982618206232417701802865684395241678844331064597807202146726805841905604124737831572934255087341164176218689581679773014360278112687075693684005742826261665765365158673586570562043154839652519149119229067168534527108710400000000
      (kronHM 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nRtF kHM_nRtF (by kernel_fact) (relHM_nRtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnZt`. -/
theorem ballHM_95 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 95 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_94 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_94 hr hq hc) trHMN_YnZt 1 0 2 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 71709336788656169257260554345405222588852311855953012863557486804636615455452146954393372889769547796866391698873883078831953988444104253231705132734929987158890004843616824069955961992674538848240822798402386990468729050741805084909456322445299227071877184102414690008951702295571228311385502972085264401886483634841919452221234817731973101066760338781425051624865695032810407945484140334145160362826753596251914787011388578989976576743847200466663159099855721305769989170803989970334005158083434531845803569313796209391528135123194057024371037517990458393939999174130893923087373689838563696461225834272477143605216209897619971381027028336640000000
      (kronHM 245 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_YnZt kHM_YnZt (by kernel_fact) (relHM_YnZt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZtF`. -/
theorem ballHM_96 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 96 → Bd r (XHM c i - xHM c i) (EHM i) :=
  chain_succ (ballHM_95 hr hq hc)
    (node3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl)
      (fun i hi => normHM hq hc i (by omega)) (ballHM_95 hr hq hc) trHMN_nZtF 1 0 0 (512 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 14693133789208297176773682015947749889777016858159773032885992028575213563211925653111236627168239717131723402388107973809154234691412940934322034090382173935019056266070265222184821993894117594124562372293600435994472164576658569170815693251207579608873465278123511369377880812775772957453268892193730912593889388048562379116903965181954145070216905462850164998340919732386848726158142877946003341255019905557497023847139809900666129134182221184565222264328786289419196618767513086103125869449620512024654987313749012928990843755894816565918630485151634213357701792342199301193351569825590540850168836751400859185729541819958964853030927728640000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZtF kHM_nZtF (by kernel_fact) (relHM_nZtF c))

end PlasmaLean.Design.RationalStellaratorGC.Mu2
