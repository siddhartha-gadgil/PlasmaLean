/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMu5RelH
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH1
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH2
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH3
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH4
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH5
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH6
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH7
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH8
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH9
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH10
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH11
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH12
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH13
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH14
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH15
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH16
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH17
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH18
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH19
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH20
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH21
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH22
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH23
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH24
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH25
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH26
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH27
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH28
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH29
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH30
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH31
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH32
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH33
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH34
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH35
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH36
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH37
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH38
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH39
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH40
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH41
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH42
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH43
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH44
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH45
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH46
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH47
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH48
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH49
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH50
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH51
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH52
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH53
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH54
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH55
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH56
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH57
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH58
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH59
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH60
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH61
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH62
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH63
public import PlasmaLean.Design.RationalStellaratorGCMu5CheckH64
public import PlasmaLean.Design.RationalStellaratorGCMuCommon
public import PlasmaLean.Design.RationalStellaratorGCMu5LowMemH
public import PlasmaLean.Certificates.KernelFact

/-!
# The high-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the high-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`, built
variable by variable (`ballHM_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCMu5CheckH*` (`node3_fullN`), the node identities of
`Design/RationalStellaratorGCMu5RelH` and the node step `vstep`.
Generated by `scripts/gc_kam/lam_emit_lean.py`.

Pitch cell `λ ∈ [7/32, 1/4]`: modules `RationalStellaratorGCMu5*`,
namespace `PlasmaLean.Design.RationalStellaratorGC.Mu5`; generated by
`scripts/gc_kam/lamcell` from the pipeline of the cell `[0, 1/16]`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC.Mu5

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
  change algebraMap ℂ FA (((49 + 64 * lamF c : ℝ)) : ℂ) = _
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
      86606780160462988694391527318163945883477856652157985562944711017496481573402477439763149187440659309683937688726314426456689511314745277594734262751493717928058653686092603023460420166158232153625218146134558056815455906622344449990732196960885965412678489003504252996905418021819059706676277583413576347416579211223251530506850795520 (BHM 4) (kronHM 119 73 55) rfl (by kernel_fact) clHM_U cHM_U (by kernel_fact)
  | 5, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 5 1 119 73 25 11 1 73 36 27
      72792472436165669390979613650091514537552202071085257216083007865966953753807589513966161392973820603093505437559689619107520223694124325548220208366911359738587360534850687386344361865363493882002152347806597974744693418976419899985403887018333795798005626185662142214526972736023582173982259793863505871057037717852683261628309831680 (BHM 5) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Z cHM_Z (by kernel_fact)
  | 6, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 6 3 221 73 25 11 1 73 36 27
      3890560712858697731021610294436633334395868747334937693942992596579228641376608051032600099858212129128662888542573020031467529047843863739293550168801646136229708057011159215841329679563065387555571197002302024762148723066449467412489475230874815128397796770341867753280123689387155189791596078238848363291750624648983860528122292672542801316412858461535495782400 (BHM 6) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LRx cHM_LRx (by kernel_fact)
  | 7, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 7 0 221 73 25 11 1 73 36 27
      3687289479136962827977352827891911602454421231124471079326770110252362264078844718986108957920454426265872436004736163387379112814420105448687034865315041221319721522841795027935261833086816530486882254202757065049873504330862993607961142928562067118252505957801210930866842421327963375745552323067548858916814505033594023987952236375935496719030730127393979105280 (BHM 7) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LZx cHM_LZx (by kernel_fact)
  | 8, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 8 3 125 73 25 11 1 73 36 27
      73359815020012980741165126747902734010314138805568194664867668986123755888414515137029797755299365031427610865234576348628517647307650657716336829358338451504106297787300232622400612197111245562041462965913501687220364593277672569710406298106429154497303937692302935558804122599668236736396377020041737159049488230973799928706912747520 (BHM 8) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thU cHM_thU (by kernel_fact)
  | 9, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 9 0 125 73 25 11 1 73 36 27
      72529510968964367319193058036122061129633675965053775698541136337532499455224755685241584837206506708242468740752780536373745965477686840405654397471249062920055610749301830361133425236434934609458077409330224077064047587228617448645168985340027129129347291127655781336087169040521697283980120263462494128301716418279478303054270300160 (BHM 9) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZ cHM_thZ (by kernel_fact)
  | 10, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 10 0 119 73 25 11 8 10 36 27
      128950918842163874234094648594010745048464495331608595930858866573898129679050300683981545528211525141352238651838886743444570973800823354561181564942432321717575777728941736588165343764384276654937190374274715496240538255841690586120149781642145739800291947917536749995608769053476152582419648995476055147418095055493853222094766080000 (BHM 10) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ue cHM_Ue (by kernel_fact)
  | 11, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 11 1 119 73 25 11 8 10 36 27
      106265813755882260162884315255212249717225738508582242922485807479491189151428793097794547824327401703891604050631357644820335407245619054762868671722113452475067891961055290471073668029378659823377533632745028360391959539448928245235094299162663660788843311738162379536186028683612899280640316592173220720406797990963825286127288320000 (BHM 11) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ze cHM_Ze (by kernel_fact)
  | 12, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 12 3 125 73 25 11 8 10 36 27
      105967897963717251343063553398619713569642880913879285780991090180995181264256770890704374245986315831077639756487450317789658518643160317948413501350626375282107826913363467188081753256925338556210303106142445624488837608851489473266986881991698865556514618463484480074990744788944894806997674755088782844717353385849286356285521920000 (BHM 12) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thUe cHM_thUe (by kernel_fact)
  | 13, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 13 0 125 73 25 11 8 10 36 27
      104854277590506222106579559007232109428544091521355331493501539780854561568371926452524375143195469906192610293274552975244135454834719190377724347394881170367562293260557207994958129310250972257039333342565190163735198306270725683642639677238586066609566859962721824089431227104902709119597374159213738744536620288083032449545666560000 (BHM 13) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZe cHM_thZe (by kernel_fact)
  | 14, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 14 2 115 73 25 11 8 10 36 27
      14348432280991250480256440883763705646554566150794703958213829096681156231231795972947937589220049983699055810872074269753164500864807190095234339799842239934405021862645840021078513992788169824031987471683847484492749006090459751350464551284876074580501561592203531548958495109608471464141843489543071828326322160061126241754808320000 (BHM 14) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m02 cHM_m02 (by kernel_fact)
  | 15, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 15 1 115 73 25 11 8 10 36 27
      10586441458835101203643286578860864529784642953439260482223218549891364520443826703279394495168628492301517764129608336910555791034701801688901311340918033920293184088188820881175846821696790314841334932521092034763790156996034842980926443818984243179038115395973515622736730007878243996842190393911238975023999317969646262461399040000 (BHM 15) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m11 cHM_m11 (by kernel_fact)
  | 16, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 16 0 115 73 25 11 8 10 36 27
      20977955674329058551740659466053978130912509476413361709988696845974349293975315082264588430431273717612859121640134766170702986468683197596409099495866886833228938886930789508689854518278922281006414509294198547000974816554317977161027481338369690400762036068628734232064538893695162338985504254564144987434643154950473469667573760000 (BHM 16) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m20 cHM_m20 (by kernel_fact)
  | 17, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 17 3 112 73 25 11 8 10 36 27
      1932630144259485777677919528293284002348228411448517872373481854695158886609472750611539379803272887424710990828672333137483509963688557745648967476405822547897267930197796465518475032844877068886266765819116625829368951111042861694019747508181124659830457581299093679643501081964730299649934294310376506027976155188011937185136640000 (BHM 17) (kronHM 112 73 55) rfl (by kernel_fact) clHM_m03 cHM_m03 (by kernel_fact)
  | 18, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 18 2 111 73 25 11 8 10 36 27
      1365807981154944917784839683545267021145387161758197492001824525411763596441745947464194290752829907219585803944134154070507132655399099857798936959881252087056200510296966136694794983312385828464514093042023329747429728332152274472049787015800749778515343880915834479889157647025214292617458642412620035217038039023572387962552320000 (BHM 18) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m12 cHM_m12 (by kernel_fact)
  | 19, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 19 1 111 73 25 11 8 10 36 27
      1541050425703674190214860417595772151558912739624503984742017010468219064345088547460463241120714576721563857366214887515989992539539838202936278915941562546889353298660615187949955911004986216608814837007813772499211015679407552045816320919253042520897227505398737868231709256442513929992598683693835999731293183526329699532800000000 (BHM 19) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m21 cHM_m21 (by kernel_fact)
  | 20, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 20 0 113 73 25 11 8 10 36 27
      3384128445516715570929393960943527794768058208604551743698169863485138851594314311506205220079176218590213225266847093652453647136410760369575792032845756718349518729129032244257100216443986205642189892644169715756690674823908882847302854131167022067277560549621522412656820482329874589644701215403187691991999842315893953276149760000 (BHM 20) (kronHM 113 73 55) rfl (by kernel_fact) clHM_m30 cHM_m30 (by kernel_fact)
  | 21, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 21 3 108 73 25 11 8 10 36 27
      159543459179146470550947549369375787058256959828948784714876344510803051104579252830016358950529092470591916608313796620500962952047231027909338939534588138154880092433842713409890850433938971878029441483062387520728864209306779703474769787024560778456259357441430942208762592194611058211089819142158472945527809210694620728524800000 (BHM 21) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m13 cHM_m13 (by kernel_fact)
  | 22, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 22 2 107 73 25 11 8 10 36 27
      147751386527076299102526827020719025274770483858518138949035860963202933290217970745638793518802307422486959017731981789461262718882691679848589124437754635922042054421719057554231634739356200197366293650317514904342968900261745231192288006455310226318892806577646977317539921645572976333117568282369777926724873602573800361164800000 (BHM 22) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m22 cHM_m22 (by kernel_fact)
  | 23, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 23 1 108 73 25 11 8 10 36 27
      224954375774075798504875478202124190056917895925816761798591583546113806951762225261890277162850910094729140922341780795825906353966038702838107861669869767851602931818135676982240455141303166308793971245893071355588917252656083270072599327764888823649423076760750638557398504121546861512427811651621300420571757403272635094138880000 (BHM 23) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m31 cHM_m31 (by kernel_fact)
  | 24, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 24 0 109 73 25 11 8 10 36 27
      567004642980060399701290979846133708380592434398665470498881757900712925268177219060926483491263765851839326239744535765916768891708844313228657105813510050748728579950964729272592416183177385406907220829927746110467748211858107469686169273913015368094937689009730574764848035613560266430133804830599105112414042210032349693870080000 (BHM 24) (kronHM 109 73 55) rfl (by kernel_fact) clHM_m40 cHM_m40 (by kernel_fact)
  | 25, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 25 1 105 73 25 11 8 10 36 27
      34503244701825848183683386585892029396125016547525456957599687278692925090465716108382615779508880836297712238925683112842556224491276013339094662480423575152453232607151862018706963533475101413034247240329430961469039321379770910983844269105572305393661913730966334431489412054987599642783516029404914956152073338188750850621440000 (BHM 25) (kronHM 105 73 55) rfl (by kernel_fact) clHM_m41 cHM_m41 (by kernel_fact)
  | 26, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 26 0 107 73 25 11 8 10 36 27
      93954546612366840912622656344605362369696417894932594609869785491042848104257243925997671671458236169900318715640762448679764002922782062022013769918666541771096170783798160625792593579135558656888339983277001453892849746965521806985064735602191191685162330730727516793535007871942176672570872426922083356570584071628332854149120000 (BHM 26) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m50 cHM_m50 (by kernel_fact)
  | 27, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 27 1 102 73 25 11 8 10 36 27
      5337025473502860422311173712406985284660368387936555273581243121641381158938034283977686123787698724600970678863056279688100681641143978250245022080148453935380954244738532411507864071262173196182464450582249685119680196100790569421867253924279336237529275399273204168534684858527809968713577701840105142118167339267759118745600000 (BHM 27) (kronHM 102 73 55) rfl (by kernel_fact) clHM_m51 cHM_m51 (by kernel_fact)
  | 28, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 28 0 104 73 25 11 8 10 36 27
      15633551276719077550281739279683257447809977145589246483437436070902249057703732299041612769729631898417197778590127423390249892441513953962841073224183436929783600331435186683997764363771957382909033894222726220484747939450190674307848047819189259259992937605544676582427191917108935589726587001457548343011238775052138289561600000 (BHM 28) (kronHM 104 73 55) rfl (by kernel_fact) clHM_m60 cHM_m60 (by kernel_fact)
  | 29, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 29 0 122 73 25 11 8 10 36 27
      909976634454711701737484619247551039418563912053458102022458402817023383805235260880804036051175880240002812099613070694450510628905749411424300794644715708732063632741882642483831059463186424887576042379663154646670191596090059275216555661325882981125893091648643553172613236114568076792342952951951924798047786797679260251612774400000 (BHM 29) (kronHM 122 73 55) rfl (by kernel_fact) clHM_Dp cHM_Dp (by kernel_fact)
  | 30, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 30 3 118 73 25 11 8 10 36 27
      65013234614737287486180961791891334591499712837752973182219832022871143925911452181653984280793869688553360691095178545443607907818230655180925667614927720869079672742386010629961327878398389982823563142408351063610102691494481931253914016523438614296313328599993331954205818709501934589007980777460071844831337600991972567453532160000 (BHM 30) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRp cHM_nRp (by kernel_fact)
  | 31, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 31 0 118 73 25 11 8 10 36 27
      64833364797917579652213466472525388060306697632934134763464883926690021111696772378862087169397745274931727747160208106549822631595377661375597586263931731429832780821772386936508582979013339449269801113456792403033995989208378520818539861637323822704514362039273489466598167604028915950645742451754327282694051410263681257009315840000 (BHM 31) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZp cHM_nZp (by kernel_fact)
  | 32, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 32 0 123 73 25 11 8 10 36 27
      1621314779266465913975119183476166601395003703424398827730731736155527357540835885083151092315442114997157435144370005407068589333117857331422571649406953886458102824318301906204703770161072449270500244519533304666386642261187476737859672444496344018217414944013927103650571297766275532328359663722659936701011965956005384744421294080000 (BHM 32) (kronHM 123 73 55) rfl (by kernel_fact) clHM_DuP cHM_DuP (by kernel_fact)
  | 33, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 33 3 119 73 25 11 8 10 36 27
      135115884160469919797889375666702409048939010196900732538481312844490832450133081192200524108543089584656075105631089267197360114831754193712232309298463049469174089594558023875197897309429999190485577897874226819994567898865979038801088669760197358948309825808917494263386540605902868717114688173123623948017465317474084253031464960000 (BHM 33) (kronHM 119 73 55) rfl (by kernel_fact) clHM_DzP cHM_DzP (by kernel_fact)
  | 34, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 34 1 116 73 25 11 8 10 36 27
      14224380303389233478691205757323615849550095152221546907100460680190315988897896316376317102362525576647948576636253831200006265975517164438369097801106656590925872337204446183824077903423988769383234684183627821438980953970710450094168290326039974251072067850167054564348305852779444359356854489513710905368103480909863852766658560000 (BHM 34) (kronHM 116 73 55) rfl (by kernel_fact) clHM_DphP cHM_DphP (by kernel_fact)
  | 35, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 35 3 121 73 25 11 8 10 36 27
      652582924726190939899531795735848705554555387525113641446398160932877774129244850369945453686108859282419683365591696731783808488409029888939817237651581308168428622935878893473662660192732991567830494168480124041789583268733894567277481241265497628854854109258465788400738116349582648794741757363209787178532011235418701639115079680000 (BHM 35) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRuP cHM_nRuP (by kernel_fact)
  | 36, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 36 0 121 73 25 11 8 10 36 27
      525639262407493735011286427703335286731907569862404883440933025292075026892174257379491384947073386170366080183478068054243613417083778154412883702461220993642379033180751341763437731604654024363064091952240747309822158084575985780767224535476104410826736371408410576223067428617699454719229824374925833431657570502763853830590300160000 (BHM 36) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRzP cHM_nRzP (by kernel_fact)
  | 37, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 37 0 119 73 25 11 8 10 36 27
      131688873767609096991919612122890906107389802032956725259215282587830534035184116937959012943484488314316957224869191686222284796388011179439832334486896401775710108534819405125609084446861585040335376505607302173722240153528009386660397896452360464379361700248044336875916294158226246038308766600097454280538805001802150209965260800000 (BHM 37) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nRphP cHM_nRphP (by kernel_fact)
  | 38, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 38 0 121 73 25 11 8 10 36 27
      605970591225431077837462062407026517046283654164208953008588973860980243685586960317801301772375366471686590736741786959768961822473861920491316956399889428705337073507185981200269497364955998623301413059700807079035013845684619963368258426267755366263329981093638576735873554223139482012520642210472751082051510351080945912224153600000 (BHM 38) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZuP cHM_nZuP (by kernel_fact)
  | 39, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 39 1 121 73 25 11 8 10 36 27
      572326189968125296906216515605450552100003625053378270873243246274786702557092810172977235367341712247706515237997320648304523524852911410687682395495673184305660889364222459243030794469947784410275004794396866047172438203658454863783511661926132823578473245751138880166144259855397176723590488414060518323098326418681713329658920960000 (BHM 39) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZzP cHM_nZzP (by kernel_fact)
  | 40, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 40 3 119 73 25 11 8 10 36 27
      130387667065348710529562057707237437158291862283966559151500602436438290725399593060423492385264915028487193801701753247471549884796695652662373563050195766238055193179970287212787404521187531373305783101795988497964002012212071600278971408635009428785432737672592639953583158824058230907381852344495863103471236725393463076706058240000 (BHM 40) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nZphP cHM_nZphP (by kernel_fact)
  | 41, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 41 0 123 73 25 11 8 10 36 27
      1272873519655305113094801277666395277444249246213031876786347435530668667910912984107320840413587462344145585613206128600721227228144538047300626012482159125418178285965689007950942778950432878156659150912088511809769905200953607746951729214564383687396635429253947820026439906140232169934457916024534189416202113051102196406461399040000 (BHM 41) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PuP cHM_PuP (by kernel_fact)
  | 42, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 42 0 122 73 25 11 8 10 36 27
      990546739915395310286954562087555244061990749880385726844678742104686082295019803603265840466840709586678455037782432814256528220485193239042387215453865301215978861199618302378710647776556010060308356366372247719005155340618392631570926980202529771567394780835769137902654033373378201693924928156222308824841501048279204632387911680000 (BHM 42) (kronHM 122 73 55) rfl (by kernel_fact) clHM_RD cHM_RD (by kernel_fact)
  | 43, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 43 0 123 73 25 11 8 10 36 27
      1701966465237732231819326178726622549548218354243899722107532907068008680132537720000683644685694264393985545096141386325608085951939143187473657765349324463254733933565315040147013035865713503437005567358957304286320119224803610530409655008472170186198581851975243793261277884831165891895190713073645009368136554464022793853358571520000 (BHM 43) (kronHM 123 73 55) rfl (by kernel_fact) clHM_RDu cHM_RDu (by kernel_fact)
  | 44, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 44 3 119 73 25 11 8 10 36 27
      131284795484412527344188302908835248369646862661839051931893212052543943496616810153199364565249490811997716415234285250299347341538137010363385327378345189010531274281870702216544479007414373712441225323052845840914223887534883659896436509366320932631594247896316448605507214177805393890612812700020587997160912109598803067897118720000 (BHM 44) (kronHM 119 73 55) rfl (by kernel_fact) clHM_RDz cHM_RDz (by kernel_fact)
  | 45, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 45 1 116 73 25 11 8 10 36 27
      13656380861884189558695131271890909537439057796850034671234202626069606022450358509662966282436080438161324798110179455947397171809613046610491768880761283039472233543449794135091128728262163765866813555049618060964630247228065361735126687816134513261329905875636553940491573789794007092637309591479461523357310428957051470217216000000 (BHM 45) (kronHM 116 73 55) rfl (by kernel_fact) clHM_RDph cHM_RDph (by kernel_fact)
  | 46, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 46 2 122 73 25 11 8 10 36 27
      1289115637605037565710544017260136712633627551760750261202198948730030295051380869968890533868709051735792416714763187386622663191644122027627798795203958208082734519238625715860096718475104952458695243266950898720019842472843799842115422604758762875112222656451572995785276914424789960460346691256316202976375491239934704502303621120000 (BHM 46) (kronHM 122 73 55) rfl (by kernel_fact) clHM_q cHM_q (by kernel_fact)
  | 47, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 47 0 125 73 25 11 8 10 36 27
      6857144176142117155182616916361779008276027309018424406026913447408701676336601208325221455889662464697758940220438480758590108782536849793104888152290112671053149903164268089150418628732062548761632391275250751677164855583135285092785903399918299130888641616692620122730521373363719384329812868279661801208711225601348765811841433600000 (BHM 47) (kronHM 125 73 55) rfl (by kernel_fact) clHM_qR cHM_qR (by kernel_fact)
  | 48, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 48 3 120 73 25 11 8 10 36 27
      217932121701873893758409898393961647216492182786138487587718486165415505847910875140193004907026598503888687514823529026453381141333064165302092366469584406338501912095207230886586037638193882010045757359593603013902927767376373653130176790448099242964862151312931683227009066872656563380457567143533463054949952808331750666728898560000 (BHM 48) (kronHM 120 73 55) rfl (by kernel_fact) clHM_qz cHM_qz (by kernel_fact)
  | 49, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 49 3 116 73 25 11 8 10 36 27
      29083102277934947555375230231123885139839637829472518710375447316508150460195833153269162578450681934690624509901036441907429460902409142004140276510806972086540862012365765980504233145435919997247243896212851729653479872136719558123315057245025874480085757269234217768523859596133836630682215042319672362023431358138295106142208000000 (BHM 49) (kronHM 116 73 55) rfl (by kernel_fact) clHM_qph cHM_qph (by kernel_fact)
  | 50, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 50 0 123 73 25 11 8 10 36 27
      2190262404442609644112750567590521033210720652865823322401757840944229467535878030822296363909996819284782485638122381646768527161119646111127703074569002109952085303823829354210014397339184700384269399482350432843085696973531390667879588527978665756063433215699084998855838772751842444393307978702495002070399826513745107682810920960000 (BHM 50) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P2 cHM_P2 (by kernel_fact)
  | 51, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 51 2 116 73 25 11 8 10 36 27
      22626290248282139016256912291607500725705427401604163486224748520487500851431037478758012980559457503595020005959397283372612374471594827967258464305022130931567449018975598417482134707193110304237512634435579219042474553383774645129001992039467193581559727082211904270127531323764046682331070646497686220501555394720422703566684160000 (BHM 51) (kronHM 116 73 55) rfl (by kernel_fact) clHM_E cHM_E (by kernel_fact)
  | 52, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 52 0 123 73 25 11 8 10 36 27
      747493460504063005814060212014204107462866209881329344863865155740450312132711509416762261048115282740605549419058823569405745904219934232636305866809710372437703132864646928165661837921420542463241039042527601326415724336173006119074123721901105605110998152924515094390302994691168680936051323533463729900977414534561673336093409280000 (BHM 52) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V0 cHM_V0 (by kernel_fact)
  | 53, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 53 0 123 73 25 11 8 10 36 27
      759244058872497304483432076069083603438933257897850368771458012029575001055660000669006234002385220609335354819894639293790911886181301916527426515972622921050664792270969716035402399618791953430774959819262770268947365572853426213234349752401528582428890903413540685163896840795234850740586302516245597340789454840447007605926133760000 (BHM 53) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V2 cHM_V2 (by kernel_fact)
  | 54, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 54 0 123 73 25 11 8 10 36 27
      747493460504063005814060212014204107462866209881329344863865155740450312132711509416762261048115282740605549419058823569405745904219934232636305866809710372437703132864646928165661837921420542463241039042527601326415724336173006119074123721901105605110998152924515094390302994691168680936051323533463729900977414534561673336093409280000 (BHM 54) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Vn cHM_Vn (by kernel_fact)
  | 55, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 55 0 123 73 25 11 8 10 36 27
      1292366538657911674071356152026232535061117142512548795246680966673011666629066865571807269673716943539989803079511126359547332372551552938890823398441989459184805392537658536476371545488834729941518751046148874089588047471438415767841109095667608483905552874047370314877662453738434192321904405478366166274394441705377459838553948160000 (BHM 55) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W cHM_W (by kernel_fact)
  | 56, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 56 0 123 73 25 11 8 10 36 27
      2257188439485520153974507601878073575063903728967557688988070706347821049844731666621126096318089142051124114840639084718218439697026888829199066538932024633416624942009348827315731049198841240584605470248321190855708337164815879463988217242930640254304889502027679607966977270569048308621952546064225948699254671844173270722332692859375 (BHM 56) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W2 cHM_W2 (by kernel_fact)
  | 57, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 57 0 123 73 25 11 8 10 36 27
      3921313962422399637727872563072712766715397184433486444000227699151057689280031445548369442391559939926968481466659000980180683450126150463513724764616976053945379178194246302061636932675133208769829515528767803220861186978593880886528744365917160370595098347132305255756830651078339830827013978961338435711702315585401706865820067083125 (BHM 57) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W3 cHM_W3 (by kernel_fact)
  | 58, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 58 0 122 73 25 11 8 10 36 27
      904092126257296500809934773089636954789515778856266266071234517539179775431231114910733990240540838839940866999867122257841638865413685421507795911136385792003043063643832699907204103486618577908824137195604335321143428575171000984280591711789636840418424490972010409390981148827970697042213337262468755395902523603967714633145384960000 (BHM 58) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R2 cHM_R2 (by kernel_fact)
  | 59, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 59 0 122 73 25 11 8 10 36 27
      992341364011193733888401549088294819417286639641753598389717948308533073719811423032839140023982436621989879604236063619112615067197812860282392765222031321345656686893987246622316549687302421601377752997477934670193063624569601347237953517710802561602005599529360380472632292576028020016940928047412495629609347208908297654165831680000 (BHM 59) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R3 cHM_R3 (by kernel_fact)
  | 60, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 60 0 125 73 25 11 8 10 36 27
      7515496511473513656857792883415902330467859893540460806687351669134298556849357763016762114516595670642176273940490522997800519751730614578398593044198352992809248187309705073432507528630999151894017557429744378821738538068148602528350564091301788334520319501942439262967529139865911455056685724278372846803565655313701859556012851200000 (BHM 60) (kronHM 125 73 55) rfl (by kernel_fact) clHM_A1 cHM_A1 (by kernel_fact)
  | 61, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 61 3 120 73 25 11 8 10 36 27
      229654535107640453541250139893262698496227193015222500412974769578732943743691301391802294288285628482013941520817376672356433883233184358376513226953667837185862159028027250417516506314837346967423768179493861797614973021762389154201890434063330511605135227620093165849811884945962252812832892534387889576318879171878394795172823040000 (BHM 61) (kronHM 120 73 55) rfl (by kernel_fact) clHM_A2 cHM_A2 (by kernel_fact)
  | 62, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 62 0 119 73 25 11 8 10 36 27
      191514004897562118984336801846110397662062515026109769122621210916671518453525347307835356145160493952678891546768433282904264957742044762923976909413747828240092107872936383169277389696854571549907534703474451548218386437187915253387106183324469314995596738175160853963945031314620058681518196441305976191873280129308675468563578880000 (BHM 62) (kronHM 119 73 55) rfl (by kernel_fact) clHM_K1 cHM_K1 (by kernel_fact)
  | 63, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 63 3 120 73 25 11 8 10 36 27
      281162378474482527146438083403164808468847187299455597976081997137939222913499229767103990616843687233846921509991350292552599934113804482363111081495988499116257587245517105456324172732768413133213746725825675542143778462361369941372124049960317936976093907945449070843918025096871515285747106287170613591678999306486667653089853440000 (BHM 63) (kronHM 120 73 55) rfl (by kernel_fact) clHM_K2 cHM_K2 (by kernel_fact)
  | 64, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 64 2 123 73 25 11 8 10 36 27
      3648960612359388357753548442456179760896437924127920972112036793651367475574361790125994246448181810681184639306876292838237330777638493804165306592386278575197270565014332352851621746669928102914313565947984231953075062687546543940295727134073568164044080890076562883060327444602637492167393588367401190158543086892743634308867031040000 (BHM 64) (kronHM 123 73 55) rfl (by kernel_fact) clHM_K3 cHM_K3 (by kernel_fact)
  | 65, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 65 0 119 73 25 11 8 10 36 27
      223609425556036917788326359173711193799063383413622035420430225563350895783580985109618454502762856605649719752361130159495596421396521298352416910203049949523712628394838574790300554771313478442277501618907032972801801671511110798892208262399338484022120122603845202784742921000172710094757941161150771489558055015561685238137487360000 (BHM 65) (kronHM 119 73 55) rfl (by kernel_fact) clHM_KD cHM_KD (by kernel_fact)
  | 66, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 66 3 120 73 25 11 8 10 36 27
      342191482170439082236317883331590900710475339175445386241559360234518062767620822554507422284434374113624608321625607683109120996138882698237218639999046560181061190819119615463837961871997141061845636197069867947546792770751020600688541869355440612344915518330641381795792130900417836087374782512879328055408235215502613379326935040000 (BHM 66) (kronHM 120 73 55) rfl (by kernel_fact) clHM_KR cHM_KR (by kernel_fact)
  | 67, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 67 2 124 73 25 11 8 10 36 27
      4783734485215666461328236557047759327596954743517165731724709119879518970993872255964963726616018279028422842125508253908303256317728543487252742303004690329989755555407880064534255135398585635834222185203045912630669201781299177258653843210763523975385534194721180147740458901667933435211364204201117190594588031395267046880848117760000 (BHM 67) (kronHM 124 73 55) rfl (by kernel_fact) clHM_KZ cHM_KZ (by kernel_fact)
  | 68, _ => by rw [xHM_zero c (i := 68) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 69, _ => by rw [xHM_zero c (i := 69) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 70, _ => by rw [xHM_zero c (i := 70) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 71, _ => center3_fullN hq hc boxHM (l1HM 28) (fun _ => rfl) 71 0 129 37 14 9 8 5 36 27
      47834884316007366514710390827141909056247197529154234916542103802407984085589703716965365859903507820084146323974520578972347030084068806794468413262517742892203982563350372956891322394333781733012029615515798159953099748338049650562216420357787671704849251083839316479703000964440975522015003522729942892111187804867539538673873715200000 (BHM 71) (kronHM 129 37 28) rfl (by kernel_fact) clHM_r cHM_r (by kernel_fact)
  | 72, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 72 0 123 73 25 11 8 10 36 27
      1526062193050198422224102021351508052387721801304183191583231405665568600337301561230325949193542110416629549264588255977580421022108021402031221089422194905854272706145873918033507776423201528438270055302990880733663021736174546222047660957379809050274698717304498985912482624366459930369244692194730759252352472930126267562873323520000 (BHM 72) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P4P cHM_P4P (by kernel_fact)
  | 73, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 73 0 122 73 25 11 8 10 36 27
      1084695255502541820381935045393743852400673191187978471627605381382435204279395701428551530113979730852167016875161728956452705386139675978399543030462074937785611267944747983036653541501123375590165468349955533595387650274717341304447210410865684894475623956178115704903852563052946205484664553977230204011404812075199345756408381440000 (BHM 73) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R4 cHM_R4 (by kernel_fact)
  | 74, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 74 0 122 73 25 11 8 10 36 27
      1557481301793305685258313516897526832424141766565957603030927350631121415437705664414168886545261889941045746006358119068340746060190268878039339048299860740137464916695330748695658660936737951220398029587197617214308454518622779178339446597951923508657788803021676969542491997235256320526824677715530186918709894017390866991027322880000 (BHM 74) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R8 cHM_R8 (by kernel_fact)
  | 75, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 75 0 123 73 25 11 8 10 36 27
      3135545627305858259913796771440524938568704420072276935505560806102554682782785918624990145203581163273477465878216614604535351235132248647040256313817159165317512445243217465029203163299068221550259201536325760422514230096565205126592841884641224486265203628693553937052391329984505767655178117627018011518721373251263472929467269120000 (BHM 75) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P42 cHM_P42 (by kernel_fact)
  | 76, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 76 0 108 73 25 11 8 10 36 27
      391571307177316051129251426080675787365394591607730266372154301479629745580318707999222657112812791120848368420004718601106767944829360475572778287888794001446795946387752085312668719728517929369329094605471041493692287450307943874120856940022384986055274531931654449634883303525044243245525446467404584999881376888129020430909440000 (BHM 76) (kronHM 108 73 55) rfl (by kernel_fact) clHM_E4P cHM_E4P (by kernel_fact)
  | 77, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 77 0 123 73 25 11 8 10 36 27
      2621263050060464849455447234900477950628089355678961722630401435577911007175584642135822091374211133929330337999432177660750244571781894426276838475576041853378156612365657315328201715192004134886052056726003515664534218871851170144041426374983632751506631110520208995763964924587006767050276379069833587560793093781310195571108085760000 (BHM 77) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PP4 cHM_PP4 (by kernel_fact)
  | 78, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 78 2 123 73 25 11 8 10 36 27
      875703687966586108126401647334330462099388971285052132771145086653942250765448881720913365183420059529801917532727170091787278541861861345535423488444907232601160689455055815712059134120096799507246856689669906921094498054593213217998105927048534162174839243823916246431548931792830935980385942193945262086425844013011643659819417600000 (BHM 78) (kronHM 123 73 55) rfl (by kernel_fact) clHM_QPP4P cHM_QPP4P (by kernel_fact)
  | 79, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 79 0 123 73 25 11 8 10 36 27
      736117149189354622770609689893079497598533654942081861144987190264210982627972414103964231378747069944655944949464570847268351075537157386012399066631040223939198675874747613506092366357870735692067472405030163009247351716217022252605886428695660815242908821162864363744058308222597877101921754572997850940586007629282123807604080640000 (BHM 79) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V40 cHM_V40 (by kernel_fact)
  | 80, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 80 0 123 73 25 11 8 10 36 27
      736313045480262621247776279048926261762801041184067133657100231103079029805467719247556933626502475724957958743855536333182581646725257525307695630822938104766014826391688506721921481324156434375069947224181651826444307256811010607256904206717490036789700820680427857342079219869271837254988391105090062357346257570735009152924385280000 (BHM 80) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V42 cHM_V42 (by kernel_fact)
  | 81, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 81 0 123 73 25 11 8 10 36 27
      736117149189354622770609689893079497598533654942081861144987190264210982627972414103964231378747069944655944949464570847268351075537157386012399066631040223939198675874747613506092366357870735692067472405030163009247351716217022252605886428695660815242908821162864363744058308222597877101921754572997850940586007629282123807604080640000 (BHM 81) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V4n cHM_V4n (by kernel_fact)
  | 82, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 82 0 123 73 25 11 8 10 36 27
      747612908469879904145756675271143172760199617785226963695410663726432446802556801303922247288043705474963594777239406097730601156834157919631890025553796063708536114915369972613619562398391733633464105400137964675235682324362430960449847106373405718366766605740880292058876759462709915069686831171704906141708010754972393040972349440000 (BHM 82) (kronHM 123 73 55) rfl (by kernel_fact) clHM_VV4 cHM_VV4 (by kernel_fact)
  | 83, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 83 2 123 73 25 11 8 10 36 27
      875187618074824837079861699207827935447298009751724955029833491299829035030656463739259245525939354008048622309931911603169948398238645923122444294477514734563696241026077130612133406933435965808470146307670437045954445496697924052085071088239217117660823986316210073508579283494618449204898097272793639090786942753951489774762065920000 (BHM 83) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Bm cHM_Bm (by kernel_fact)
  | 84, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 84 0 121 73 25 11 8 10 36 27
      183980324292336025056578426258238111754796913573670134294392706932338400329191168142174484076551953154169793553748156072970565500323341564594109281778914395739246086782116819064966624593591468203892421598137685230588845185915575579085447770606875660403266350322458909537319234478619136623134628933576703431196876172567459764130283520000 (BHM 84) (kronHM 121 73 55) rfl (by kernel_fact) clHM_lamv cHM_lamv (by kernel_fact)
  | 85, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 85 2 121 73 25 11 8 10 36 27
      218796750352117186267653993977582017645677735399778530939549779729289433689909038015805501813217890857042495377359117900023218512449026945855681826603462543987422903538631551627163968954089322779604648734377032676829784899624500762402047865000740841124951778862441134587465942330341673493026147012916761416921078331633820260724899840000 (BHM 85) (kronHM 121 73 55) rfl (by kernel_fact) clHM_EN cHM_EN (by kernel_fact)
  | 86, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 86 0 123 73 25 11 8 10 36 27
      877509134310430811769720864889279749393010456573428407792196601108316309332995879713937186908099773156880098577404679133456319265607442176541928707201654970469498151439086596602597998596222808336513442675058011665778151082485032246384549807439069336088071306940991657729878800307955377195968890607824612560949036049590175542039019520000 (BHM 86) (kronHM 123 73 55) rfl (by kernel_fact) clHM_N0 cHM_N0 (by kernel_fact)
  | 87, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 87 0 123 73 25 11 8 10 36 27
      1046071978624986694308397349265340872774817726376191529921997898465812908582489836686814606902416724086025844544368253856074556845424763704826050186307154924962447573323602567466682975361090723823904140187332919186399551993622662108994388119024596324252661584176885330201245460732761167941001401543404582031174911077332813555727073280000 (BHM 87) (kronHM 123 73 55) rfl (by kernel_fact) clHM_N2 cHM_N2 (by kernel_fact)
  | 88, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 88 0 123 73 25 11 8 10 36 27
      877509134310430811769720864889279749393010456573428407792196601108316309332995879713937186908099773156880098577404679133456319265607442176541928707201654970469498151439086596602597998596222808336513442675058011665778151082485032246384549807439069336088071306940991657729878800307955377195968890607824612560949036049590175542039019520000 (BHM 88) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Nn cHM_Nn (by kernel_fact)
  | 89, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 89 0 123 73 25 11 8 10 36 27
      747302967605306819095352357667710688130105772674713202318329817284009901421682274029915093982031941932816177437900054661665513579951159821402626717630295297352956834912024077618095975447297134411863870218143622533264719562105260648184153993328647764929620932914939838389187380187837152698132277273542438864305179034411357638691389440000 (BHM 89) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Fv cHM_Fv (by kernel_fact)
  | 90, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 90 0 119 73 25 11 8 10 36 27
      131799709173958065577844937489928753404358177672411288693547313230634284451944518899907985970453724836647897229779106829110356773313256891926189601553619718836696251177852160452845496849093187133831656283709575382030731070266338441509424057405401379938271139501890856058481340538445543192992027410966453723705671137050728839816151040000 (BHM 90) (kronHM 119 73 55) rfl (by kernel_fact) clHM_YDt cHM_YDt (by kernel_fact)
  | 91, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 91 0 122 73 25 11 8 10 36 27
      909763092427489984266406126102305915289104785467714412974902970215129951023152339744697721554801804079413318227354421794371061355284241716932453538230651969829282344912179924395101528297555659472429893700328144791513770222724799563484009799046575098560018950938757831965085535991280443296130398214756421960411134172925223290598850560000 (BHM 91) (kronHM 122 73 55) rfl (by kernel_fact) clHM_DtF cHM_DtF (by kernel_fact)
  | 92, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 92 3 120 73 25 11 8 10 36 27
      216583949662650387489236283401695802918182421647754006112249403417220135791807409176785178585559126027817721545153601504844172113273542473603140365740085871200506218390484946801981094084532849475168049730366588185821692104981610996656335035255236903270601317048293077262775087843484652799655216886388625569816579366303927465817624651875 (BHM 92) (kronHM 120 73 55) rfl (by kernel_fact) clHM_YnRt cHM_YnRt (by kernel_fact)
  | 93, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 93 3 118 73 25 11 8 10 36 27
      65370195098617685298078991254236987279714187262250357981005845303370871675357577597677841047310954298933994741879960666223855525103817760653623028007371712175083291388912262368395208501418214101780875742657441820004067436714095512384398110581235700576422469633498219959772436367347740359964479492610577471967319095659211149426032640000 (BHM 93) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRtF cHM_nRtF (by kernel_fact)
  | 94, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 94 2 123 73 25 11 8 10 36 27
      2203639773240343642968621662970618968818013390044040971569112745799526980957566919299834754582645044173122258403478599114383707137938998885807972696634751163239380991640925303672653705194440780208676322600274452068537845665621280551297852499858755162834231319373403825891029843461424120871201986942059699593399178548730158167808417943750 (BHM 94) (kronHM 123 73 55) rfl (by kernel_fact) clHM_YnZt cHM_YnZt (by kernel_fact)
  | 95, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 95 0 118 73 25 11 8 10 36 27
      67888965529836049911662868462883683422301590591555751931518491021950256165328499057966392427657695665485800064850001412024650578706676812016979420464762112076312560594240446222066270490018322562773201097116855435606155405973056943614518414043415820242933732432922865431963558624817892875473491483730128197479274120268113911039918080000 (BHM 95) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZtF cHM_nZtF (by kernel_fact)
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
      72 54 24 123 73 25 11 8 10 36 27 11572163334718905587746506981251660443678555586648807686294328011096710815946836848064324741907470123926375204066199277523483902926567974259868739694052789480718785736179651905795339547054669647671352649976860404060343592510703802732332639473602963497932751634679456241026056776692134443512807799156916176189909844291834279572275200000
      (13 / 500 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Vm1 kHM_Vm1 (by kernel_fact)
  have h2 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_V2m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 23322761703153204257118371036131156419745603603169831593887184300221399738895328100308297696177407992656180604902015001908649884887935658150989388856965338093680445142502439775535901244426080615205273426712029346591984829191123896892558669974025940815825502123705047014619902880758304248047786781938783616001950150177168549404999680000
      (5241 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V2m1 kHM_V2m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_eta (2, 0, 0)
      144 108 48 237 145 49 13 8 19 72 54 22379810011691919942099026076855101790031517380404450622938763815442409809532865844319161854428820139445916908708143770434539624255862539809047557205468109680260183777180534682299392319041516854497958781602683622822637201844363064995583290732821347966777198427105330904713585557473067286072933101110646711928898579986752082022701019847248474945806032426168364825241985619385598575244193533970856227967043138988616730572392682010786804014977350949356211472021857906338721002547257682412857692058586888056258488481144852938003734880554103167382002443759611120007923349194356554511526468091207167750254660714230921264551856967414656764089466880000000
      (117 / 10 ^ 25 : ℚ) (kronHM 237 145 109) (by kernel_fact)
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
  have hv := vstep (a := (((13 / 500 : ℚ) : ℚ) : ℝ)) (n2 := (((5241 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((117 / 10 ^ 25 : ℚ) : ℚ) : ℝ))
    (b := (((10267 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (m := (((221 / 4000 : ℚ) : ℚ) : ℝ)) (g := (((102883 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 54 : ℚ) : ℝ))
    hr h1 h2 h3 hEb
    (by exact_mod_cast (show (13 / 500 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (13 / 500 : ℚ)) ≤ (10267 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (10267 / 10 ^ 4 : ℚ) ^ 2 * (5241 / 10 ^ 5 : ℚ) ≤ (221 / 4000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 51 + EHM 51 ≤ (221 / 4000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (221 / 4000 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (102883 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (102883 / 10 ^ 5 : ℚ) ^ 2 * (1 - (221 / 4000 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (102883 / 10 ^ 5 : ℚ) ^ 3 / 2 * (221 / 4000 : ℚ) + (13 / 500 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (102883 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((10267 / 10 ^ 4 : ℚ) ^ 2 * (117 / 10 ^ 25 : ℚ)) ≤ EHM 54 by kernel_fact))
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
      72 54 24 123 73 25 11 8 10 36 27 195852020010522544295984860127050579346000647401323967416362534857381311207741535266295072539257327976770734471946555386089074243791127635961939515382640982214328746280337246225867983504862876497786012479422086891970972554719936264095346268158173629843419873028725594781370308121330609383238838691037215798502939012284751082946560000
      (4401 / 10 ^ 7 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V4m1 kHM_V4m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaV4 (2, 0, 0)
      144 108 48 231 145 49 13 8 19 72 54 1612661351442437098842399572292866778026480066301113421629117704995909202010907024869846565724725721781193122822015336580266773816149283915114882479211357527317243833164115795491631776796252735427271339957375191765450084623372352593415311653153640993115188773284405189506256283874535517864900141936230924303230648396454781475963914939081922355221883014726789291559975600679199950249186165181072620084937947044425447568108670572641180871373555360991510991030887495882368973129030071422907368810220709991704184603316395327848007053366832815436771787126362181035397300005542735554802702481545821346586098458431308623604387864209627801955860480000000
      (347 / 10 ^ 25 : ℚ) (kronHM 231 145 109) (by kernel_fact)
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
  have hv := vstep2 (a := (((4401 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (η := (((347 / 10 ^ 25 : ℚ) : ℚ) : ℝ))
    (b := (((20009 / 20000 : ℚ) : ℚ) : ℝ)) (m := (((8799 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (g := (((20009 / 20000 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 81 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (4401 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (4401 / 10 ^ 7 : ℚ)) ≤ (20009 / 20000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 76 + EHM 76 + (20009 / 20000 : ℚ) ^ 2 * (347 / 10 ^ 25 : ℚ) ≤ (8799 / 10 ^ 7 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (8799 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (20009 / 20000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (20009 / 20000 : ℚ) ^ 2 * (1 - (8799 / 10 ^ 7 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (20009 / 20000 : ℚ) ^ 3 / 2 * (8799 / 10 ^ 7 : ℚ) + (4401 / 10 ^ 7 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (20009 / 20000 : ℚ) ^ 3 / 2 * ((20009 / 20000 : ℚ) ^ 2 * (347 / 10 ^ 25 : ℚ)) ≤ EHM 81 by kernel_fact))
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
      72 54 24 123 73 25 11 8 10 36 27 141587837141086711543407159856327302373822802278747870614625773378962708016231207145239250601891960540200924362412054841574057264314075918165491580085997387512513804310619320342731500221856935520943756282507270743422770338822729930042758725011566694475005905651156019580601862393478830703430374873517798836161531359320336485517885440000
      (1591 / 5000 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Nm1 kHM_Nm1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaN (2, 0, 0)
      144 108 48 242 145 49 13 8 19 72 54 828550451870329589194563193224266218341402824823263405227209520646642423630326882984631793271152902035425285751565922987613064160524081948442327197165803531475499612980920142954573519803942299106238227665666165243935537275176444696358614071431802081127591573498733943430418811813679707092864363119759443427015811637272381210847278853326553038915243891604989116829486931355517317487623896637885479136931123305233636025211022037112989831351341870757089949089753774453898594861021107024683152266221790148612308397587845512830591380514199413144558257255699379285422367159507732031174867554131284759443481686228895685428393278895748425911684300800000000
      (53 / 500000000000000000000000 : ℚ) (kronHM 242 145 109) (by kernel_fact)
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
  have hv := vstep2 (a := (((1591 / 5000 : ℚ) : ℚ) : ℝ)) (η := (((53 / 500000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((146671 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (m := (((4917 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((140263 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 88 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (1591 / 5000 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (1591 / 5000 : ℚ)) ≤ (146671 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 85 + EHM 85 + (146671 / 10 ^ 5 : ℚ) ^ 2 * (53 / 500000000000000000000000 : ℚ) ≤ (4917 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (4917 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (140263 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (140263 / 10 ^ 5 : ℚ) ^ 2 * (1 - (4917 / 10 ^ 4 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (140263 / 10 ^ 5 : ℚ) ^ 3 / 2 * (4917 / 10 ^ 4 : ℚ) + (1591 / 5000 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (140263 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((146671 / 10 ^ 5 : ℚ) ^ 2 * (53 / 500000000000000000000000 : ℚ)) ≤ EHM 88 by kernel_fact))
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
      144 108 48 236 145 49 13 8 19 72 54 1142000646667128699612274810379122630365075089606158149695227590536988306348672181078491099865193640351474481023401705589086717479144204477569273788839307400788657684858535341565552946757031125885753456660218660954349755066800235890819471478640447455291487071789422016392750196943626455184439873526753424479067533651014702168070398992623371524256935009722373719034393978016148271202953517422081592441325496176651571866337729286208186169090392115442682659104448355625407074186644098012407642680078605688960746860093692393314725312959708671667978547851190804749925541839432089378007728415241636114426574361063468901367096325500889598714183680000000
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
      144 108 48 236 145 49 13 8 19 72 54 833663679952973864453661081418201060093260967589018530337305574372734121478074036000397037999149315820712870285930177359455333109455281439594424427621133102350214726304181485925635803196030708572107076027274174570183284187508867664528179837340674928627084851995268420658723651309309345925728589981838962237648679626175842224849660052607478736949058040996035507732475888553473045660402211786201911056608461028310401928699260391822414580093433495219000877367810773928184716193745742436229934930577118029205569366296818950191166351923861604410688435419665338196065038801373231999472796774598691101933251900557726769041480774348147142573424640000000
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
      144 108 48 236 145 49 13 8 19 72 54 1251046515822119861683437539441650149641075490313327870734286194645626402755949191459365657267103160304948361762525277235204736395343759947172125999965270503280547186322091040072647406236709956382229331159724633990500516480489133067708588805662306399077244277057161463694425244446336505019436404765825191791128950794151814425269171466458601955057915599231949106395278968766785892231954347691563195465516661241059647331183210193291948520286379975096109379774361691577391100950804370228980149789502211657779190157047179849927059984681357133403948824900302298868499722778275562225718299739659474063346488164321629346797588972160386774954147840000000
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
      144 108 48 232 145 49 13 8 19 72 54 646602434203643322175580267018029785109623207734450160503657475013175117093536686748392337263710054728762367535528954670400441163242554325168069878175387349032385908743748564367751793963310451416877246681908796501378156052552445259792742406238586927409918676349243187847547949417976914104396154646158864495733840158835747575906317296665520129355136625092191289673182587675861718750280155022570039492558154734920678719280362578633198857299925621106326289245985003761989638374853635723728089546295344282748160162110423446458355298229502644468670017338072203903290330990545361903288081033678538456091634864828250110539157604140145055010652160000000
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
      144 108 48 232 145 49 13 8 19 72 54 547431257248271129960106528974109164148599929556935192418704651499681593328864334362856233070395948582413939914818599922826935161461565726386025287767770743003337437331295826614998673353864774801796151371865039700261674540429464938685173939664064107101630237373920383590337057645515170715918377846518153357640809344228241692621656464279658326426933224389026524549611596035147092121854967196941409922794650835203006751497495557277461833897814610202317709651783403164977810739678237891962350293291985243114554307638976013565538065001830483641005124295197808931826308700431436679087480435989476694806147965785098934122028399270951267849994240000000
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
      144 108 48 232 145 49 13 8 19 72 54 569275305970880971987934236356600365506696790692753096428104091584458555598244252288212235302704987191314336481187101635896682845877032163580315582739104900445121642142964551473475486308128997402027290919276125868086463789462195630771070948465014260095546006898367107751576015883819072958771640244790619357187825830274011089670776894661188581968115778739958171343926390062879012817465568678508526650790174513707163727754923937887571841418434815311182214492598844951311400623294198190922226811595273386396324349396432917042931689917985354694267127840368150069138868942015015229493463874015601338070397112389749412589507231310568277734850560000000
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
      144 108 48 232 145 49 13 8 19 72 54 764200133043763718374160408042290326547838780081475342964559434063303210188678600058819089789992703147123863949324722862765759278769116827817573810878446852932521151105313683563008180726861946788594346216487929258754185560471238944784309658377672387856526222706254545873124701170020532673853371066291147891598550762792426216409880510828747776357835413221969404655657417719931674811324704247650523982936780147187613281953757687917353990348259155663574623639794556335300249993873575907197123008576457823269020497335976522478106970889302641718833236246817759503133204062437786728105767238151918120605599277053796079138838602246723452450897920000000
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
      144 108 48 228 145 49 13 8 19 72 54 410173496378949381345847989761736586022411323030197920684921914664637228714111884971239210488342937007985277399356161875829209431864114085322624791542237371796629328042177395304865226040824597631236913619519548045849081430698177506448385528307657653266361241239784340408204365068895796310381933687027827849216583370474109664751569145867031534987532488785826826113979086477356009610710062900178223239800480250223037398719215240727894724664474556155940983437530883670174340868157562406431202053667366386280134508094047975416054622126171059708468121342060132536859919368157497251977464416282145390814308924759623824259618783132795626544168960000000
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
      144 108 48 228 145 49 13 8 19 72 54 404850354712158585187366764533987489268042539526905643174459417010059390725286284147932328309876456255380118641277544331164858069670109771491656381984123580687416938756284492812164936556751987902475565610595613821058129600417531605418803490804367090714977947254834108915334391818043190008663887295307335569684338248656438610100606391454684402490991590882590801109149589454598138802404521167346681542340494850886562604831711952273471340446335074992424046452449739679348385912414797820149264337557142542433000491442601611253003525464324210848637094039864645602311873794211125089578259237651040670193421435165874202321826639381402142900224000000000
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
      144 108 48 228 145 49 13 8 19 72 54 439527548122463313603718894090889721802953059738021748187592701212046739545292970572696505968537640810842359485877677161214242237185186368685558030679250672905689560258220120125982289969758362606789746014746956516445431791350577279504182568449988963903745256751145099957179686101752561643882400685258273955542489874568785057522572513712488031806556948678621573387786651110804043390354895116355035831832045837015299429951362643268741855002973338284346641504318175849188329651011105871590491470552949339812184703677400855429695424267820373769248719707233829593568140799043024945422955670259980244060641820507551025737369047477969805513850880000000
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
      144 108 48 230 145 49 13 8 19 72 54 524971233520772518874934873821531562781033712121786894910358376928762459078937686700271516052203568063619254257964788454463254173760889624412184118297324764681461052888265027739642280682184759486095855725405315497362194986118993596209904667919248169527827235530613925227825372331976720032987663311639540322912420747027088734300327922999067115540316449320466994156027928403227181344948523308844757625852993830550338374586530374807835506351028958946297549526791238779565128016455108190536316760375524355790224615766592364996128310654998870889496159527662893256357348338045635170657843399790465626501233922374761835004537077760476612520837120000000
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
      144 108 48 225 145 49 13 8 19 72 54 392334233700306805065844231918487133285153002378219641810324011476505716879818267442786046786145745899440141062807460462530633313901711208951977104497629284770717919484353663944388760758492732709127141146647733922651012828370082191409476374553548541148156442131472127643705789504117035200077157830527209187892097914157853290278093495126103428325961741970731298311510860513590766148698505946986032968504517798597028390377986822067076348807689788289277708435768693446108619171233290288720260742507143078997581692011919556480483141915504322714852015477118293358596434472832623950751087729641573468364569109370097009621467426808101448439562240000000
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
      144 108 48 226 145 49 13 8 19 72 54 433289945863154970977802612194159359532137409473994477985359229375228725824823222165046258931181242773977272875012970380410229409196184245244011108743046596764678231457707636964726140830601478241975409571446268355236408566133482566351085900284108209063703894575372627128266356572579520759863349617240892648517137979873173161775540084696989910149629107565474523415835772975709256994785674714946621848961325122461670211304100530211686140577347441818670194417744932165884565656121024827668639484669362185605308565376628054049594634190921384301861401126663565398887082160032798956707899621004348487666779226462476424773889072808435390947000320000000
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
      144 108 48 222 145 49 13 8 19 72 54 363832125824238574005188884695262647165675727190174870285862377395669910553771743624563990903700842295777460460063758757098709008147646382207237049500218628461648335836276445761195709405074141225285101853995741109105913937247426373935412293369423098657268096890983742908821020517594152026983333871072817894495635587924982306948035163482238108540295008407373419096879251241362726600338076154977649823017962509587635175553706519070958134238954270543232678955277167888597461560732159050781330331959890719107298653339508098332709788976595887273467682416996807477244203087142959932961698631038195314832990603265967037325161552921186034673254400000000
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
      144 108 48 224 145 49 13 8 19 72 54 398129678072921090648251746076805701672898339135479603224955385441896343930270944734802901854530138105985881510272466140741659072444210221231372771188916015608825561578793386245284158189609417533920809687481614333512503681432066824836640959273494264868915899213335424515346782308106778774128291127099958818446573502631959570519890724845750631468358586632923665195078897209051332587638354237170211494044429838389800529044708489254611978911835401925934490544345795138814629138842496666090595260761770957569130232503567466796390576354874325623063971919557612546712575148475610247224625604435976612342437411146596888535976539559512040800256000000000
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
      72 56 24 127 73 25 11 8 10 36 28 1000346179693806562939331722697067684663819870302107549160273297723347159487217186899341232565440866158727961476304080462092254278202128351278986809849417479092142040026965068073624690628468249696830852919048965454816120645660172656379184798277214680375764427501004410445620961269035470166724227649041266659819520000
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
      72 56 24 124 73 25 11 8 10 36 28 1043541524849759340550251538988343231097767326597161356527682195663757766210773789878632193863509838615181690653815391700744605394625964622078143921978455264466502353158306697799181571726265076533346239172777148170017053365230771534853324882694755439576216155151070241122184286324774467151601982997462971045642240000
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
      72 56 24 125 73 25 11 8 10 36 28 2089764143572046556743055230843305786786522226495055209062107011834332461085845109499297956022429581010864811474374622638483164778414525704884461492700408668764551528228023355472856606843754390630698344519424837194826232807174001178261302590699255575784719144303430643073787499121216720834395128033947811462512640000
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
      72 56 24 126 73 25 11 8 10 36 28 257086485039822142114844206122640376354126103725430301813255312593064373899111131933489512096977701596425475443439813838021805211006063556272912069313498297719596872261072674064789687914371751602675380849827472892877018704284384250704985714712783530919444757941901145157458102932459706431354895955802680543150080000
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
      72 56 24 125 73 25 11 8 10 36 28 1051402742983414550137272906883281728585510889093067480326653373582286904591968763906359592791819464687247029287267875540414332482457040525065925130739198949046675080106401060409565754047441366167886557462667131538232155169703923594581543032410356358575602708434363144095575305643852312158985629201769252865966080000
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
      72 56 24 121 73 25 11 8 10 36 28 509737956314357700453833340360583496982940342669174304412471487627026837441880231083542024150449458297044539300970334910528490241794217224842049008315763997571408316704506834348174219427669940692376868594558126552346624230539269813820761684330472660498459228846526992910233731972695597036583956037759348800225280000
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
      72 56 24 126 73 25 11 8 10 36 28 1031766473965756215847493447587764581468153922599951881945059245070150625583237679567724901839896837095912602959619288568332177683689512509308641324250484005245240349684721950778085879271744810561202521702912125585325834635702630868051611247858844559163042113276685616773656464089961253581700999344209318243205120000
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
      72 56 24 126 73 25 11 8 10 36 28 1055240061164719651572136206922796242945695481496432077809019273300176268025968500434471833734874332044091652806427387914586800512317952628162239074119978011721696059175055912897415478312279077636302483916873552218078363264166397603814214145234163845707948101358297919668318274593149706766877640129403039829196800000
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
      72 56 24 124 73 25 11 8 10 36 28 516185301818369075718456855484651805342116321206556281055972948279975874055020931039064972818350488152087808833793973959691640829154420357871738603623425993502950875423665825595076520188734805200280958678406195078834955475060466753964537905706401831536898703328516267823948102125672991974655469144403874645278720000
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
      72 56 24 126 73 25 11 8 10 36 28 1027446093456850349481170433974385140079586887801374626145318660625777341724631971031935634932687137504046600590509232922339136984810507745096632034144677899285855393957815115310894869380174122176497105980081805964254294557184152863435522916862223845350693495596525463409941436861929688495845576190667451583692800000
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
      72 56 24 124 73 25 11 8 10 36 28 243260922097117233201557831010553243427341766456743569767085184111988524049240102809433864485470387918688167800648376407885614708607681445811497663773323870196207311174336048398789502558648508525116837747951824090642557947523672121138855088180266219578736556095114888931049859242019509148945766278725670335938560000
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
      72 56 24 125 73 25 11 8 10 36 28 1041302819664461567863582361639842162211586817287057867628580401682196462751781335341109015911553658799931828478865351255163870944758710798149491647527755443372552835856571405438850077883753325879901045505882978218640318489041187677213909675685928107619366238868422298968274785961779380870408842627383930514309120000
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
      144 108 48 239 145 49 13 8 19 72 54 2035206077815618719642820229251758153978101510680424911401005226894107349710149918022667138020423921734313694229282057007888419641510112557702849763202485894845098088214879573955302794519916868418431519814522324973131695459260998031974532707777707994691766403917171655523136674176199503451009007074225574688085181674115467395366841489217907942642584659081958677145503260628101950943375284681745951161701476213032199970683625000850929244382596860992711200843585037036307452661993484382926787978070075831814818951090217359925464029888485063113621972433228422648329735445985419087051021747549041259358791164296500316779775224160820808164311040000000
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
      144 108 48 240 145 49 13 8 19 72 54 1669679045859788196330100844810433472181915791140437802727076578653547324724993923027509160709576883566948643165557858847373520231556608068935744646754813712882052779725700603970920490343203765554613258600823932742773872206317968450029863040009510301568039857904444752163365267074427202799848432513744493086044100803919399733865672694118866481303279633177813831193934765617399756085455913215787985212393879634897268180065789687507420434981519892179404743948429433598116754651302518245451798623984771429828364529325238290759356764339654624567496448523374262439802531830568643437910577965735998235407945900567738735773085717027655507100303360000000
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
      144 108 48 236 145 49 13 8 19 72 54 1105930273172433543407409543494004046156081012763021806377680705134252304046019361349577768821235578661808173147354694733908647015067205402064004679211747548080142962507499320952268764417210289924366200934081203966800585947719376220838358200091875430073619788951138298360263375166040101926408858006213961517239334835042696409941614576380493950885406653149821625244795447232333126730659656585714750643584868336919429996387188412968877937035213353312501753304852778078924952232511832792406819283177332716265842343369285160160710681860215841544356871699029630726325323802299547284202382095575504335026773727550850098463895260446761781643182080000000
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
      144 108 48 233 145 49 13 8 19 72 54 652672693425578252388758884998441441401096062706848494812507550515830491031845903159516909469494997481224395017972065134783933050699422810050826042578559782035690067776937308334469282920187425672064842611060972194043878823587610970806518020517419569041618286423712890391205117521226836698181855370222609853821285786340112996971058109041846799573365474338683353534570776536214956820023675417547688373078571855743941666713330453338116049620655854136282634439385781235884569924086879868124595893683061650621322251224053129769635243592085231420404812360801127065144636319190897293136495799550385650481402377324030500802189147274300313357516800000000
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
      144 108 48 242 145 49 13 8 19 72 54 9028627001924520252273448925953191319935171490406999169917965517580115455007973109068885858833929951797129836495404345688889636568765401127270856944745302892318965768393020994383213933348591006878486046281931232319589879391371661934574620936591332814530713176774805144059199686988394813105082236309742482213668591133732164183046650148002320113582427279582996321261937314698705101850693590230915464894617152389076802375209189716978083926717175813830177546314786851775183959669108841466364420039272839488603329210118332641587666501452613672601922098520356818587288772246842475977165501730590341134485421371610982245022305911975434101614182400000000
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
      144 108 48 245 145 49 13 8 19 72 54 25927192491752705805713892136083933986001570974254150878023954005917990797748098440092384481660896500391522883525981900729579185674570772376369577513581392952072216686561327586859298315871225352858094632874578851870676049822093568911632604993427324394048653828044112194812819182699424274800535916362923532663111546476477374424565363434974005491735106599974699475475340625206818180585756876699543098296542495040118054690508953503589081007043584279439165422582099461685944348504468696786385539949086443986000911673591712643693813885368111792253503642046971813360802445199887374979785507756747058654299548015133383263532799331262624021925068800000000
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
      144 108 48 241 145 49 13 8 19 72 54 5273443319363383251322558911659709093213043291628387159313116309658194422208323027171649302584113269146679324091071575080996431399488241025620955222011296115696310034111332246704634188223664799889315917874842446684843834870664713599694410403715972886425224083242087314259006259543179047655165714898353668776400302753419785859501083891539140434487021847599516042631425082948073976475569360639247806471995145978126423270933036732349183943995764179704481955942111104020519132585331093707769755717596312470364010769771461860175259734240045868332920857963757125648468658839577728562040852514513917486451623338238958656417904608458277455984066560000000
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
      144 108 48 238 145 49 13 8 19 72 54 2009315377949005932555973609743873582337107530474066754152184250432652958994975370294014545841832402584170035181232363905989988801308885845669709135148524040855540535809342811646006382441694621102598973881504862374887457222425946831834022851063818766022105077127541722761791100038521380060164497622798740760530960058333271371990562434528568174985594940325027732882571516393809070096728029639096745009595936374472662484498243383756155739300353202202756923076003775448058422776199186441425127919389604676536574282706725832548338648424917504332882841469663962399845252338564262238994925888747590694695307109472137383699630267197040852876656640000000
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
      144 108 48 244 145 49 13 8 19 72 54 41932653577446297773185415819385452429890408053606474382249203354693370361253330481886101146011997896608204814308918211408223633247336966654885120247535326222643252119307791313109261767525751428841072870169490559026817063740185876236890153458493465821074842716896328865102596757755022124957351284968308185179527318479031300150413301560221537220998379912735769451325816150138802196003027639246532448121499149835452758779247344200273328604331001951702106051899683674091883852155901604574567044143059186235181150053391345366309825404926997850574274047324237159729751226544306898758503100799733753464415578932226131310629158849060776064403374080000000
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
      144 108 48 243 145 49 13 8 19 72 54 44723403035566126382586488694889354605369872861191661324339973632742611195930253352455859380728804509939338270193288159198131891840201493811125217296199189951805454899147504475918970851627961368912599839191061850788400706894599003717134554403715643654518310825129710904389178310158818121680117632729039448762329431443646935144527967198630584424530426944995626983984786417520580787189433197918301574132220545759005186157726165326028859579115353944119639359557390069646786837699997411370498361115019802192171097638948955412392411460443408357795132279927068176197617493061119197953747985902605062179974955835455868173078724903253513760826982400000000
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
      144 108 48 244 145 49 13 8 19 72 54 11832217527902614914049844457900955954181231648502591847077869296690394768663571548464966082678441024621521565350167655393053555969632831886111389668278910914731011857824892045128927474241857873586751490186656593540368108047891714885941970380617461061185334395800701430194738020033226710363673368170645045277891178584958280091740644715321472646523333074718547401032835549949175773884065510020187397628466311181735141246022820122339651415093828686645396687962326760554101714210611842371726239332260377861081351374371915120547465766854868614134901734046893487108846415990749025099687700374911799868874000064811881439486909744256198184869560320000000
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
      144 108 48 244 145 49 13 8 19 72 54 10300752333829282533891677075974977249975700665223012655243899591625735249318876654757541202582081586566376527683269831956646286354490389681064941823444916120913120840590542707906001137836887892518887034523953326119930786023664658615496973719992324936874293481283681284106946032482844442021469630255992193331821728026593323569157612697840262957016893435416373197567348104246003781069616371393508653305785420918719160656121344904868045072700102042884314397823866145071736501312455947154909472382654970234457086664436350912889275700352464173650729621666200012078001168468588190584666607430481164129873512227831447308097565030450924292082237440000000
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
      144 108 48 244 145 49 13 8 19 72 54 180637327033022260473661012272356226072731017573705355588078477855473022641523592417320149687375169302835104079332273822231568485773572547268028605987641676009832070197250961710675275520040365654967170016369173906141290201228332985958943425837167688711947083765590505187448694179173378741788695696760268376835778302759551188866829325716073235838232662923138125436547925142029605089158009764747480876205403224400108798068092040581288626149554629530268426608982029621166151569051249585595477759279465260308829650884019676993332059255723034050112834654009029368537785034508909665117851205264369302694467656552290140477717408390748516716872990720000000
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
      144 108 48 244 145 49 13 8 19 72 54 1287936234031131594820567927241780987438803354132251876770875773271204944054230815580996506155062510616186608316912795305556789170390498204540623303193913623027413118215511661589789441517915204396331222959542309950671147165114696432086673550711284763439530114028305291174230806234138036882816848586834369554004001329048402967051431378438558933293539836658436496648380914902023722595087662316984166658920115251484507009451599563724041687134319394090807871825168274990265166889100723535173339821829516220004358552752947380987846815916581065628168744038213528452727564114406884286653372710913393011606820264785241551006051678943565243262078812160000000
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
      144 108 48 236 145 49 13 8 19 72 54 1251046515822119861683437539441650149641075490313327870734286194645626402755949191459365657267103160304948361762525277235204736395343759947172125999965270503280547186322091040072647406236709956382229331159724633990500516480489133067708588805662306399077244277057161463694425244446336505019436404765825191791128950794151814425269171466458601955057915599231949106395278968766785892231954347691563195465516661241059647331183210193291948520286379975096109379774361691577391100950804370228980149789502211657779190157047179849927059984681357133403948824900302298868499722778275562225718299739659474063346488164321629346797588972160386774954147840000000
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
      144 108 48 239 145 49 13 8 19 72 54 1893279177383196117702447161312009152760328250831119944758821564706814999384889961620910096020575172224256947270850029617326830473293194592336555596089641374739998552917146445145019885436019119027248392429776547519363475878055794309234910308818341039509354404383779677750168649402881550189709356873673006588316566033181257295540967829094836580797086476796354980025883034015671348999413323612313612514144914055581762106433689903348894364766363868684849393926735310722763375713184393472893497395944662354526334853422814984063890553224593762331202852413499198717130851332385169117019220236957185528026342947763226948533200436260655016034959360000000
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
      144 108 48 242 145 49 13 8 19 72 54 26182160706077353124139828832798480700671167342158346963952639951223679734279297307299119732949126785821092892529246142098943593862170314545951736876540333003182823095745207427280151476882352854264772360067266564277277437856013127916656502266231652477413800252384687710256881034571498824334399420153500263541493371883651244042986409331503382605600525500264071381011978546401694103797989156597702264957041940740153471422981577522366912098584317976407104936865345004753999728860499011861450372338814680731622255787838592558086763685197291149549080453604940995334010106804470169532471221974246185599109063764957878262265431371480348214700277760000000
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
      144 108 48 237 145 49 13 8 19 72 54 2520204157681924684873431875695750719168273643596163440743165819136246502495770094709482944196876223083794034978786934800561399941283681283991401994319943821177506962009136573557710767702553818904759541244861858442688200449659576215476688905533954536464996045285740223409726589477448544294952958289828092470610963617486868023909588662247045328975835394315830961684445100254907105405509980811242813616034412274612091660992922980668347580755114712610657851297186579354566554077790420277907879790652241016238078941089041188187913024685019496208358326982264588762638688566265665132378865598361970624835183362325785657193277847060890856235991040000000
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
      144 108 48 242 145 49 13 8 19 72 54 13568667708477766447506459276559945302853999102902476864623173317205241577175347707609211849559983317299618412574264027983592894122827116482981880071081558761729259842148260729169711806177022926952877654884730914721655339062871408467059568582302046112421013843085411187208600776603687873997564812287917268818138718928105846941644684388388163207253257459957398538869382128833335015691821226521831547322212079946908068113554057057002442836230274865856406756124234374288998783537532515054418925911694361803295196880115530951259091663330066721401120766565498237340941851949577944433704779255091848235454366761443017544314193719384474955263508480000000
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
      144 108 48 240 145 49 13 8 19 72 54 9398262907669294486010847317699073195591265273538118290761242411296290286510892338426250208547463527118709855596113571951705488691807640239618768521888883667211842923940026232193229104123923820805779011484963336365113744006742704778322120004004554393284256497875914720115641291158128789311799733195331823964750413837515996556253390726533293171607273028303459707049244632203342462061938518252923851508062186252551296694508748077443803814417346795124683246841217844363105021655333193872622946126861376757714188018671399806181210128520794244451380214664953063173626467831831989246093248289589571645417059095503385928346750529729124351355125760000000
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
      144 108 48 246 145 49 13 8 19 72 54 60504861518205600291417377471763752781077513761191165270591805080560595208042160892856029891279202843217444298890364228712005669995998427699308066953069659153832510211164328906718721409822361388161644454257579862004963347635727560040420244337513953162941770319514838815067947234725607040565573388216329760046370239618445273582740468037626251155704747468817912207642303013640746011577795785508998323641692911282645192164726344412588634690563158368374872399794373541182430311375596116523008044796925576996809244011817257369587128620593628796744248787356000961031451140810406227700750583899448787357754357055100947361430943604812522427022049280000000
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
      144 108 48 239 145 49 13 8 19 72 54 8628751440489326920099854466852209825567479665979765773682641168486473428188660625423400464981845330204751511249918587309508117883385274720536994416886983865211854563539328687323746323151573968439139321863304171167013007835252809249129763763453732129454842658155672315319583655737739582179809804417477118024477859112471175947751917861563550785785040436216205293412229793890703067487130471105544884392949362673587933872986739275617441414670775617243982635979616734739261777288863694380004673370495291580107433967879520423508178143095955614925322281668590628469691639922241865962955058866472741236189730041267506316735457138697627471519416320000000
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
      144 108 48 240 145 49 13 8 19 72 54 14851939090295548260090713051628185247403641196383187156570709786384985368870392273758497983021765418566907677499446410215503438877265324371985073245814102708868659296789776882501092858715014685890982001134377797168501479724594500738989004950825921164037982503279071919369025255900422160155540399368664948915695100629305401499179222590092875362562423656444813397173351308538351181553986517803756655893911167192252073928154953557083964473656599604861911249586829973884541501811500595688017033548856153949674427223073583900110795964289147372413816643693473513386388123201309541933099833451694757517134407183145581213792712340463345187044720640000000
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
      144 108 48 243 145 49 13 8 19 72 54 128846421894258352987292020887411213705740660115410913727608326292773519092561753534261326550710504922425037748478423971310861107398751917856416802756938521334771902532443492235853795906905239053889715452667285942923138467381095541869537107001482842749985476788806934433913139828063885496274508540712787608467555063273319090054721968773097747500074362839783547698776927277374918466905874544914738407025970544662825113346900621908294016819347502724811869686056102161521736252095473757767209031664946722195816393768405881369816869693578528887253308889072575742314650678704881773701061692974580823294712535053819262231896064384505308987973959680000000
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
      144 108 48 242 145 49 13 8 19 72 54 3554479248120477569226236395458688779651636717518652775218310405324878571923709348125707064322745543964151704034947101215272524044308375058679451603283881289682372815896770777160744915912724860313517370336843293522556273617189622471897250777415952631302504437319853787955430987654546180011305506143458687801442805286106964488285098211364466881967323040761956965317181263227251125446514200917450451966540180727744035538800170282782246436952508074154015982887998830993142675052269274775257859781603043348697926710455699991621048505943523531892370731536493298170234085176700970201321309347837105629962035689413669233732986010335641443133030400000000
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
      144 108 48 242 145 49 13 8 19 72 54 20908169449808889861257560672364880144842437280405718271497820763682868834336610393991888614556754417563898049580551899277000971739209718489792568383032560620149836287690345005303661898111019940939693346755138096361244408324410450040105921009750404466581667181069552172228971606051687807884061793162864120267455822887039989536618057771012480307371888223736717317418599399842576942835593205663678559660335071904338246654487544408723488343732640619227347539451138166979158982092796754452926579471220069823949741988978492484412094902643399162345174889639559935237263275565029269842664351251081909570286495189782119579132441398775900950725918720000000
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
      144 108 48 244 145 49 13 8 19 72 54 115214821809425938240410550448922850006848634239217629148917069503102797192663175203311647982103778547452406377200282907165699617298674360591670000701818349496708754268254388698419078983924734735766172795019997642845438037993271826646271157743083376652983710559512671520769993556223938489563856860556101627323696988237735010845509195462809754340893260343696988265631758017248452575231019233505397720417456971273612133403462547831352358792141658228431608871335257371736946668558689040231566499271209498961729426409932694076793102579564508195929192012586214503028732871830716817205390540137147300665279234251298999267177592964128688648298168320000000
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
      144 108 48 243 145 49 13 8 19 72 54 77528723585079517906447393727247254113638547983712292167101623824096933114596054364655143066969235039758894660142052302173096862059331921598859756655012871126754063772602582584833815046061954981163698949819462679954336514015790056917924052599456199253333246337202855417348563640247949081193195874507764265342419896476706222200455004535878955771349098451811626323689831786025957251129786058002020738995734012394761908468265121329445295988574086320899591682232446784663893003557768141131818032545034777062454721270104774603015190215766707192245371448001754802750881188403597196248522827569882929813677741256303974569822210812219393115600977920000000
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
      144 108 48 244 145 49 13 8 19 72 54 69468751412305548529419690647076210582748583998870704723216880129669686104383513291701010188507407323444480350811782367083815840715255323589777395516138196811482341602889811230358590194159045903735159480947964073810852185726887267104918191630134219499006458524450373373076732947492555623377181220799559270976187532830677339780464482169824003145786081294234703648895284794477672765097792635766843814142428459907363522367102100037754924484896043976618778790075521155185928573000425975002720603481256523631486925785831645131448376946803915181456785640768015273341193190869752908606910221158919814184942185313522725382325008736230643338523443200000000
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
      144 108 48 243 145 49 13 8 19 72 54 65302271713295299875782257834293666160975090143551535844862685704519012408122084564343885286371164934672422227836642079409296097170484763209423487705295160432938382447835773126098440481793640993689041720240191372942904952506296951462619763521396033016113701407757415560441993830678880475376059419194467023645623244481007430952957094461374853628139444302039054149940222686930967379679999668485889890552321408788232012597863332299903474075645080026192658948129209143025652824758987086744183733204433945512970246126660617006808743596131000088156232119989033592733738657595732729073761090078557899377317542175324975922829373642242064671058165760000000
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
      144 108 48 244 145 49 13 8 19 72 54 664220027820342340032810510207016766664074318111581785761358839492493604217592978889488992108424598930164927800679237332988136806376062229878087302230041744808945142884106270216771982408421044648212880647640467354180168240575828490690504624046855881435588627727518155825651379298598463198886812245756766121866647939619708838638836052235874753633969944814864242798784943078317413285519530447569758757959564241723783784979820088329032692510490801321077178075183352136797315464125788519746594053491076546888089797998303401078186007567134709503408348745819134651471035207419686286551607274097431833224477106663677543626355010167944709039718400000000
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
      144 108 48 244 145 49 13 8 19 72 54 829550384473889196705267265567190730742137640583101285480527611760656863816488581360511397998815713726434297944843379399610331809210459657191370969329726186274253818896017004722306442074918211395885159410937430792598497400621094591401512873141662254683343924690142032713761832245329387307221189290197693003457662111724500914680732673417111085227841919895544253507231940400019825104806121448071380333608726937593221370918318667294995784661884445848569552867543714371322257042580087728269167827869210463185865044147968382263848100341121322743713459654634346755448865970658894791719999820016292496802562369872584876629509255967113764027760640000000
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
      144 108 48 244 145 49 13 8 19 72 54 7304476576221127324636623120763646136926069897548718982905521932845680280902752384714074520721834477527871970505495704347713304403591614481579233433678117459145748700551609177091995477601999427335082891651882223732250042185530313461850056378770448408966189037785477514725306538953898139557271857488506210450762332776366219043310404285169305777166544442441297917108646765998473421553099602916400677055904422103966519632086167322383600803787173241840068521610518646148043701761457181422745667291578298132767676666177916358696986678680471447350708853484920264894008355198016935921640505741699580438702759876507279026982926603246756834238791680000000
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
      (fun i hi => normHM hq hc i (by omega)) (ballHM_84 hr hq hc) trHMN_lamv 0 0 0 (64 : ℤ)
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
      144 108 48 242 145 49 13 8 19 72 54 3681612426546520222125531678779412644256938954384131512984915491407525548812767883036185363162168246671842608774315877812260305835474529031981254502658503526515759492842678091111595206888630320100863035860184111831689966714486117837583721177050190750466826023834568150504730062198973845491820372896336157017236159781227894678258469288696267672498702846674814044657252370249484755001131676509833912236013114620400104087229738300205563381964759124600227389612685605180049981205326226670738034165590364187170958329210182211042800752545025106407381325410610488304942395718547149175084990620369631851071526778502023054832188351854186334508810240000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
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
      144 108 48 244 145 49 13 8 19 72 54 711502719596616914824160792940935168463473577772414806785005801149625871327036185339612447447698335221567272223176021144766009769784776558536636085049978659823699488713716176430226615713421384491666848606873018875994917049421093747168232007144807469548689580430450209186235804675573028695482754517975693408517180325752730597849761309995573166348551612387901321054504637824909065703525865027991821911577679013806447444766367406808294113419893756191808472464888717680003121942377152219802291504799941907545216752254521316098589893919370710723859315615856841639190486476054365975659865572391826098888538827409699223189337656884710675265649377280000000
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
      144 108 48 242 145 49 13 8 19 72 54 142970689296848714419517785275955903839097572784973205166379924903397803059701091059300105331195332190434649892335583353797427789335392995835284561786458194199346218491723339511422626929981870156456275162288418697194003025814597865206371422601792789088587765477178102790164669731883230201888637343926820595437646436515489979180910845500571343775818511479734082818719314622865898955904419859643425412259756629781556393821653174633225066084271775394888087851238954711499627141419029153568505103468763387012008393647147575129962029022600827939246047464698638908920694643114802880755007462242675676484803284360127218262323624047850055106318827520000000
      (kronHM 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
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
      144 108 48 240 145 49 13 8 19 72 54 69373196128004405758502167766953963803618120250242329964788168787407764140992505640108779798501721490265652451570055344057148131662660702374120334093836821174666861048291932612176567386858880228400624778337177798142893655483037516576777196660174615971729377316684425881542898074901312071135828525068445322371105438052058278641373875474069517111474759309825824536889952257910215296409053013396220589663062951793117171209184179481331221457162437146365704853147419517897769083346078212537616957191343521196177018722525071731849155240091393395415264485170823583017382555164598831123181446131233004850400156317094364642364369285663790129144135680000000
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
      144 108 48 241 145 49 13 8 19 72 54 243687699942678912787738016228095019891245133896824317022438854623366659525382479880813583106437205821339077781429129089090658381922383947866384604245387021983526807641998711600087821070461772639739720393150571951200230566684947410564464803370810318103255027921232005212199197624243583291761563770621356869089964698189427283544146685244173084310274330530317359947717195367568921855131793102711435802551804414166051649812678818506127186622780657527845844464774435187098315527572118159400726964171620424907294319191883576025572343482471407699001874707745987477955603170467952589262526904579825630492948216473766481921109910500775667886372945920000000
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
      144 108 48 241 145 49 13 8 19 72 54 148803520233197966621016167764297529899120725306138270887428454193970519778329406713618417480146602668691668550045010634644871156137713966564009235975263637936283243151655605761303839838253368718689072202681352701194350429606633382585581744757472020417059093537238346912736874826155032823583101816501130658016149954690121248361372339181616070900590690140432853512077060006162927369901658339390600883404069810212587895490684576644841556974061196900941458674515511653954132639355974655537266012181014094427177604649436236959896837651372367855472290929638863691457343490726048159469590602458915516706098805328794168478350504026753193886550589440000000
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
      144 108 48 241 145 49 13 8 19 72 54 275375248296109491692536146497027011750424580996472953219185665380264707991420336814885903044091959855812643873879468960435185915242509409423147821384598853150653273191087160137700817701703955727797373292605727919072527481682772561435926259358816714801424373244798204795207214502221162620894232279949590767838795562595155018202621770230854048354434209446739269381266823699130980257840035394668075742067604874550679661721607263187023535755851964564999818495260971343051697413758797815744244220966179036705521975267894612154011146756773804892424800319271150378349601300926444235903038038052304020398265814357200621045259397208464242060830965760000000
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
      144 108 48 245 145 49 13 8 19 72 54 1022793403768517060968839263634294852264569938704086909199314125867875092744112981287735326528886898650013368448533762264426986777123656634315582826979991100362084210375311330837029677899688638861649804845859755564786196648646601264505090857236172485453019012518219088879032006477214121804422066222424493578418067742317285526917804102934619006678085394198874794332322143542857971558242433695932771624707091632923026582399457635566385530418252955908647774140184808144950190051139649324062214086108970708582446678463701034008038496164169890855486483606266653917962491349617649706153258145565377185040262157680816139972061528382769542553581649920000000
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
      144 108 48 244 145 49 13 8 19 72 54 326742076327599208640271267300160877313347168917708870927252854753447263746911742158492408318371808891048597134714726733924914775247244163097175459016099960062055763703415775921219847219952828041515630424377084167076895029218480629404102913674120958551485351366249910255998452440419517514403250822148667256961899632347660530501746924826327799493580786193085510415199485836207793037617011643888148986243045271941798339539194038232697329502853004784921547063789106746215222797756208775996169685829845320109340768344740402691346959048846037103265717466347603693498140140876530915055046336849648167028632546461140177164988320244686240468319600640000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZtF kHM_nZtF (by kernel_fact) (relHM_nZtF c))

end PlasmaLean.Design.RationalStellaratorGC.Mu5
