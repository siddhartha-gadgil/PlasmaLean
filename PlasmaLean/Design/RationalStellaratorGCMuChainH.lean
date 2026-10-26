/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuRelH
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH1
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH2
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH3
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH4
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH5
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH6
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH7
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH8
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH9
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH10
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH11
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH12
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH13
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH14
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH15
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH16
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH17
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH18
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH19
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH20
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH21
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH22
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH23
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH24
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH25
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH26
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH27
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH28
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH29
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH30
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH31
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH32
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH33
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH34
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH35
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH36
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH37
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH38
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH39
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH40
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH41
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH42
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH43
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH44
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH45
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH46
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH47
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH48
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH49
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH50
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH51
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH52
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH53
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH54
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH55
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH56
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH57
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH58
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH59
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH60
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH61
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH62
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH63
public import PlasmaLean.Design.RationalStellaratorGCMuCheckH64
public import PlasmaLean.Design.RationalStellaratorGCMuCommon
public import PlasmaLean.Design.RationalStellaratorGCMuLowMemH
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.FamPackCert

/-!
# The high-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the high-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`, built
variable by variable (`ballHM_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCMuCheckH*` (`node3_fullN`), the node identities of
`Design/RationalStellaratorGCMuRelH` and the node step `vstep`.
Generated by `scripts/gc_kam/lam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC

-- kernel_fact side conditions: elaboration budget for the proof terms

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LRx` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHM_LRx : KvHM 221 73 55 6 = famPack 221 73 55 NHM MHM DHM (if oddHM 4 then -1 else 1) 0
    ((c0HM 4 : ℤ) * 10888383889117653077957113864) ((c0HM 4 : ℤ) * 158456325028528675187087900672) ddHM drHM 0 (famHM 4) := by
  fampack_cert

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
  fampack_cert

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
  fampack_cert

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
  fampack_cert

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
  fampack_cert

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
  fampack_cert

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
  change algebraMap ℂ FA (((63 + 32 * lamF c : ℝ)) : ℂ) = _
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
      85868365177543368524933876537781276945454596481461966769471067728288241427889394127025443240677336288212601515274523672352807834400975654194479593356218805911775805902153031112822196872914442474282485659520160340858837801140470236113889165886386491875908267201070929218127682501134821034403924232802769377153416272206024866023396605952 (BHM 4) (kronHM 119 73 55) rfl (by kernel_fact) clHM_U cHM_U (by kernel_fact)
  | 5, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 5 1 119 73 25 11 1 73 36 27
      72209708901727424692743606474143544807852600357842853831392270683970538468224984629812125434910374732315295420011718503823645783014884540943049663680568472848462151580848774638097197726659563661912659588727610604423395814229887185380511565511286857707612729564712032744739434787828029448780344934419556072006151812908270629165287342080 (BHM 5) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Z cHM_Z (by kernel_fact)
  | 6, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 6 3 221 73 25 11 1 73 36 27
      3855256262806443601910926968745642750055106649824747583231185459334684261832228904485490067517752708892865677101483993142367372341084566279056775172602337049193405538942277198602851670098801058195046567802473748130793668677536684159472840601909343063554663940562756378362423440153542172545118734620010197313637476698195999108702761167609049847049175832971423252480 (BHM 6) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LRx cHM_LRx (by kernel_fact)
  | 7, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 7 0 221 73 25 11 1 73 36 27
      3655661236279295353612094303799984207110108855109635691677130103058896407304288054292104389488545006586614943414625023825334564603673285593855929811973945663497218097650863586218981287387104681994557317793512257259515924421995142584419347802102549265477234851469235863131015742357132565164653608306431542282752647826437471608940318669950255737607337088629719695360 (BHM 7) (kronHM 221 73 55) rfl (by kernel_fact) clHM_LZx cHM_LZx (by kernel_fact)
  | 8, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 8 3 125 73 25 11 1 73 36 27
      72728002021350351709167848623794490459456641861644483334065373780139267797708591530037604229738710011300672277499748514472841773421194538626010461602147276084833123318800716862134281588660030557363377723027266404433130432033314830052365752862377641249997205828090732364576348287900516906835188510635382628308906351797195267628859392000 (BHM 8) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thU cHM_thU (by kernel_fact)
  | 9, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 9 0 125 73 25 11 1 73 36 27
      71928719131788903974500827417427986575447508824393374387495413823351000577177977904065666392276308459586041571015429626216772558542070998877780125570820068353734753729278109300966441159906430060385650717053933728784865292429697173792402505408279690030997824286831933900478835527528091590464489875567655430102954513660112857745011507200 (BHM 9) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZ cHM_thZ (by kernel_fact)
  | 10, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 10 0 119 73 25 11 8 10 36 27
      127851892760837724279445547993531155933966158517778688691437555192970059617708139673364712271013175352062085908847818465626513013879417831113051489752313227048297978941561537174552325389892027276649521583864559441751640071163086964626807533984980423021293487351997124183550557436499438510440831293989808899438662653057576820382105600000 (BHM 10) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ue cHM_Ue (by kernel_fact)
  | 11, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 11 1 119 73 25 11 8 10 36 27
      105418199702671940687587185900788720098161834334999805375289230993403724820309205906660895678677713088485654508690223786103484497935275556223281171961484838763104139598079804303796229103419807096146591202091609902464530056436849945131216286393188296769443395383593532704695932486921421000440168198260720798658834052580974126075740160000 (BHM 11) (kronHM 119 73 55) rfl (by kernel_fact) clHM_Ze cHM_Ze (by kernel_fact)
  | 12, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 12 3 125 73 25 11 8 10 36 27
      105061925581715585637867725836733851934764247322786501268704853420075859413845047658684870262427858377799061962600518822973491286413812958687050190107102563504240947443804445671848068240837614223931504532168351428281009275196873579279959081215351769652061380490355280561253320335762364145585079324282000793341744399149202598264832000000 (BHM 12) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thUe cHM_thUe (by kernel_fact)
  | 13, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 13 0 125 73 25 11 8 10 36 27
      103991936885312502901650488240118186811772515815930252385444932917497140650424973542225328391457849572113936595604722220815190145894224655394095981800653933291694831781578563299569413487489596082207170531903868844746409994524263095447510266924786837887548725821888837966310513936055153855233358548549048376737047825243700732603924480000 (BHM 13) (kronHM 125 73 55) rfl (by kernel_fact) clHM_thZe cHM_thZe (by kernel_fact)
  | 14, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 14 2 115 73 25 11 8 10 36 27
      14124925421078425901280667537823795507113118116734329230618673671436149326841795703648806712901901156431284015605766361554906790877524928590374490077413502827782640267414394487678505672617294080277025351460713895732126000616338720415356605794934266991394798882622173444045687739145379400895666350768940237977162405426113841903697920000 (BHM 14) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m02 cHM_m02 (by kernel_fact)
  | 15, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 15 1 115 73 25 11 8 10 36 27
      10412665639484128928256648697289402113127843865407522858073990017057548802800000509561143608340275873510741597284240464293012820219780446764785809101297992072163167914738880274141511681263956232578108811496309822783187619554522597837272772729792547509950157490338036845381836354580604408170509538069495145461073690456581189643796480000 (BHM 15) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m11 cHM_m11 (by kernel_fact)
  | 16, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 16 0 115 73 25 11 8 10 36 27
      20629243980812528188204918742920098391555385258244365572731567038969380384262923580665948211753510417123431751811063775550577442077806174220819058748243491491644890944864595786385193427277576286508768480870455234534001941462058632014951125191579625731826348684742563159128680550591376139487941754554089673173362082344345324832686080000 (BHM 16) (kronHM 115 73 55) rfl (by kernel_fact) clHM_m20 cHM_m20 (by kernel_fact)
  | 17, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 17 3 112 73 25 11 8 10 36 27
      1887994287610667931118604280081310020206946039576023483010711753458220894521637032087484491126203166236560777196837302839762095355415229607368027941510458891864635001044904506320291666185512374222531355885156500675883040998624691354595393792861206960456413656862730892659256659219680368901934860884091999238987915203429277473177600000 (BHM 17) (kronHM 112 73 55) rfl (by kernel_fact) clHM_m03 cHM_m03 (by kernel_fact)
  | 18, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 18 2 111 73 25 11 8 10 36 27
      1332961578979461575216610749857771681359387619161562635076688358264397301063038592038098432878149010251000317184577887916488389979234134343190427176786135374778137721321871710847360807260989835359677396516099339586547336255380872534784805143719123089958891151645973344716440659714803879917131399113073086663176222818810310541967360000 (BHM 18) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m12 cHM_m12 (by kernel_fact)
  | 19, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 19 1 111 73 25 11 8 10 36 27
      1503228012803649755143761079360649485980701169187759182560201229771948471641274896009321703980600856981052411293749186031756345897932373635799938804558342491704145445868797311500552196111251884163620670247512000898910735223353087458786845753274557408933668805540072317228027680383320833699960120771155199011946792217239310345175040000 (BHM 19) (kronHM 111 73 55) rfl (by kernel_fact) clHM_m21 cHM_m21 (by kernel_fact)
  | 20, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 20 0 113 73 25 11 8 10 36 27
      3300730196198432011429328360091850567864198161141678541921223918331404390266912294007766090294303148362148843124421153527111934215262436931499209389056410002612012689445650763268768816744195082118306790390209741788462924047923801579015232609288241859377205132195559519441737701804959187523774113308808897766895564232098706609930240000 (BHM 20) (kronHM 113 73 55) rfl (by kernel_fact) clHM_m30 cHM_m30 (by kernel_fact)
  | 21, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 21 3 108 73 25 11 8 10 36 27
      154519511038405862325325291221375333906825076454628689180824066586071642513288317609872023152834169830186433485789514538662537023318440423917725992598477759366085022369675480196832464085711256924706058750325498526833552747560368318068114049371759786738673861973328968743996095360535844747411107143578201217223258846093620470087680000 (BHM 21) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m13 cHM_m13 (by kernel_fact)
  | 22, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 22 2 107 73 25 11 8 10 36 27
      142975010726403009037011729451497293850544469072390983352678261571641176432910333663144298907098858998280510381162054401619244012518220316675097930825391571239975127649538878003623899137825655331991473598207136809794775768912687691809467168834722339647753752467934020067053002884179320650965556744886193519478234081055574159523840000 (BHM 22) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m22 cHM_m22 (by kernel_fact)
  | 23, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 23 1 108 73 25 11 8 10 36 27
      217613323547201737749620896913832368294534321629529026081367331071541696822938469147977907785058984587661059751980276152645085348753346350323044813528037447195608976274965779299304927896711703054165466859945039354459637215947774641343004915766456926111010814398713322065153673110406590208870015164852853307063582364625550243266560000 (BHM 23) (kronHM 108 73 55) rfl (by kernel_fact) clHM_m31 cHM_m31 (by kernel_fact)
  | 24, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 24 0 109 73 25 11 8 10 36 27
      548492878008773342389328757798156106030088107578530591131245579397522154531345119492177129658294817038100219185249105145796617710232751680707204768679467408891352122045332883945724185053575784889529270941560140046743366137313104295360069130924378764164638415980522769150338214346995109363567150006141767943768457235050013371924480000 (BHM 24) (kronHM 109 73 55) rfl (by kernel_fact) clHM_m40 cHM_m40 (by kernel_fact)
  | 25, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 25 1 105 73 25 11 8 10 36 27
      33104568540760795532994350200789786966079393096578317915486579834951248230259502449134227990912159965810960318952273482807142611356438119349313411764568127525595219562859474104670775452733409321859540175422704022386673541485283906628901504723608046069196413223691332978245945729754799781021553386669033373510576827524556469043200000 (BHM 25) (kronHM 105 73 55) rfl (by kernel_fact) clHM_m41 cHM_m41 (by kernel_fact)
  | 26, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 26 0 107 73 25 11 8 10 36 27
      90153993750737058970391675985211362223176751013356881187258913523732782668521474434010494250426168099249292472978154289511999183498595414924185839991686067563219165911366792102415126345467146741237914046110334969097235396779980324088001178806867543197648281214654612405065902794008264181366140310254477945748971811126746672005120000 (BHM 26) (kronHM 107 73 55) rfl (by kernel_fact) clHM_m50 cHM_m50 (by kernel_fact)
  | 27, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 27 1 102 73 25 11 8 10 36 27
      5078317201891114714385685691580554790496124104661846213201636736569357660213735448176581847966131355273360391026957714921149096354082478800068419589051807415580020822837962773344478774079377463668133374501752590728566820558616208247957787546189647913115692489202323093565501489879517455345169214025846034473667797031788006604800000 (BHM 27) (kronHM 102 73 55) rfl (by kernel_fact) clHM_m51 cHM_m51 (by kernel_fact)
  | 28, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 28 0 104 73 25 11 8 10 36 27
      14879593317884529639870389626773448734117288095819168798607168022371470106211631299167976481904365460045756603576127679061025469480791119072465050035685306160137767782636761087770070952992853142740891581113355997862553296197735919454541452019127565912252809059153972079342324280261690513023472385702892351369734794427123692994560000 (BHM 28) (kronHM 104 73 55) rfl (by kernel_fact) clHM_m60 cHM_m60 (by kernel_fact)
  | 29, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 29 0 122 73 25 11 8 10 36 27
      908498508221912670742562084510935766441756527973097340508474618288196883191433824435894991679477802779478821010066170190744440776039550504392505903626102589607813810082403027749331249901317738997601206764343228743938357415421536089083813483791571559627878565336408297324874642383275539853939618140074615761672267078384453774517207040000 (BHM 29) (kronHM 122 73 55) rfl (by kernel_fact) clHM_Dp cHM_Dp (by kernel_fact)
  | 30, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 30 3 118 73 25 11 8 10 36 27
      64496778148440573537014338180325219112064692829019211863742940840254605569164179721885942667090787609837196959695823997632392769231946199631128901993825518257385613751012889316829867162225930318067625706231510823221042716665478245732266476317351223944803902804285641343812240080956543848206313362478192577633807068318727739518484480000 (BHM 30) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRp cHM_nRp (by kernel_fact)
  | 31, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 31 0 118 73 25 11 8 10 36 27
      64320072077699494327608306743864406427705313612108792327644453377717728854659340642929189811640566489106317593009862595342501808871685759687019077404561418996629614872757969577092052120426513295614216598244459455277202645241503914399699789661048599475128422195152835546222120805049962574465439886175565529523336120040132229243863040000 (BHM 31) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZp cHM_nZp (by kernel_fact)
  | 32, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 32 0 123 73 25 11 8 10 36 27
      1620055212765802926536977957400379290786907506336987236861868597189990688184936028853407488320417290006440090880647504777748830941894683344776654339872424793488218760049315222671909304979206955005379414907480066828383511293717298697719352287453167568544354544487077830941194757878909635639207101880616896904776928138293902814488821760000 (BHM 32) (kronHM 123 73 55) rfl (by kernel_fact) clHM_DuP cHM_DuP (by kernel_fact)
  | 33, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 33 3 119 73 25 11 8 10 36 27
      133977455021452537536828001165832305490568309035720033179972642337394760379213449607559935326281978924053535223238147810186741858924222663274769779480231648332914653894828499134282459720756883848899741780935593758683637618718870958482824646506518855085036015465203646612409509215187535318978238668887489105555622487888392717389004800000 (BHM 33) (kronHM 119 73 55) rfl (by kernel_fact) clHM_DzP cHM_DzP (by kernel_fact)
  | 34, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 34 1 116 73 25 11 8 10 36 27
      13984929915261657146506317366133611587037342875528002439554137558200880362305294277985351652637531679588875005619032320230608133673749170540523753689292846566479662095426138006811726949123790512680986233444239269606263208765693443636242893445495232575278091112831106902260917878676102829135487448241757538701083786090510655611207680000 (BHM 34) (kronHM 116 73 55) rfl (by kernel_fact) clHM_DphP cHM_DphP (by kernel_fact)
  | 35, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 35 3 121 73 25 11 8 10 36 27
      650554767968289921089499667098928485185440162683414319838052739490326550643687578105239309323208082002822638459114843717777619780958033748664491757458671155938916652134455749612138245338265816860005039254880276516901022338908482966785182183774124198766346842001206529087782347134758159682735780921240742309498995822575592582697451520000 (BHM 35) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRuP cHM_nRuP (by kernel_fact)
  | 36, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 36 0 121 73 25 11 8 10 36 27
      524789676296537964405518417357372361105876282940730825905203739353988751643820044278232573527817918538734685204119475319572099010093034574389279505503504763647900789361019070418067904163043754621535646836472362666893156137380437558583341673969644695879930083777464388677355369473941553498007662280396624086946370135874896520858828800000 (BHM 36) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nRzP cHM_nRzP (by kernel_fact)
  | 37, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 37 0 119 73 25 11 8 10 36 27
      130656056980660358080302610554855563783325659581619564629547844697191397609117703861516488017682862601813142693149855003336959643865132396824718365782768682266841068938891745318227273991223122526635958425083216001683523842782180840548602053927210647017216878770797582509940555896668324080185533017279586780881499003790642514933841920000 (BHM 37) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nRphP cHM_nRphP (by kernel_fact)
  | 38, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 38 0 121 73 25 11 8 10 36 27
      604384829107967104344888400184767808255953177392082885223484361329369076989648289478650292359766888816214221031065232377785318888453169848385294262829985341317587059742480027254423016337582141312829139452513678852472832556291353104644287168484430255901897771417204838658718189074868024569073426627923806649539051180460179449037455360000 (BHM 38) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZuP cHM_nZuP (by kernel_fact)
  | 39, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 39 1 121 73 25 11 8 10 36 27
      571080419499984876143717559651535187472206319422015275160614122692618511427354441921677887771721444890058146594269082395570637497740447664689051681811087738884480165216721537234960028043274693076132320898435516152478271657081927463071257174037909509710319999583947035201326619173656035178616575206746442892686732148860551906784706560000 (BHM 39) (kronHM 121 73 55) rfl (by kernel_fact) clHM_nZzP cHM_nZzP (by kernel_fact)
  | 40, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 40 3 119 73 25 11 8 10 36 27
      129323666410162959452990453016925134769351012690107311156928999891376896239853869120334338446593239061225135724102594790235054618982004427420021316455908427148530303695509641523864080195162277688173180741670993757835657522229536738188612606387920499378770383976413856265730514338167534585360978896706235161333472342754189277124362240000 (BHM 40) (kronHM 119 73 55) rfl (by kernel_fact) clHM_nZphP cHM_nZphP (by kernel_fact)
  | 41, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 41 0 123 73 25 11 8 10 36 27
      1266582213034459524153905073798956241349956752379502327369832886749163552369406738253592778490411920548266518771944356862839744063348029463802442550758124542764661649518244004148756753997469584580925401576860971069607762173259558738581219217229310553351394634552842618201962280844828678636528445090876145283950376681543585674842603520000 (BHM 41) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PuP cHM_PuP (by kernel_fact)
  | 42, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 42 0 122 73 25 11 8 10 36 27
      988473897545709436511835465692934233385412222310639567239924524778909310067131698803339709375670305157381636187808390050656516786521878783184458407464495659276639577401173891129574382206508686070808255303167421511814367516757727390751138975768579411969364874008625897541886478198780701506366369162244543765111689617455970107208499200000 (BHM 42) (kronHM 122 73 55) rfl (by kernel_fact) clHM_RD cHM_RD (by kernel_fact)
  | 43, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 43 0 123 73 25 11 8 10 36 27
      1699920370040173871795704206174475079119147767060592679032283855755027840328262795313119052520553217599133254643028067476248572008463778042183786189253673488210807503486436698643569120121500706673224294465516477866683523513157318120219534009728724711819691787768607234201179351857845172257901555387690213868602696731214413775178301440000 (BHM 43) (kronHM 123 73 55) rfl (by kernel_fact) clHM_RDu cHM_RDu (by kernel_fact)
  | 44, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 44 3 119 73 25 11 8 10 36 27
      130215062149429204617445575513758146595502456968434201341309754462522787080152532220183946917571590850205741777022131199332871501681122742841981019685971409701863029326728038547313483068297448121340546292147085526219099600841059593484404798606631253267018981145094217803375822261518308002877430700557787336373835003995047779924705280000 (BHM 44) (kronHM 119 73 55) rfl (by kernel_fact) clHM_RDz cHM_RDz (by kernel_fact)
  | 45, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 45 1 116 73 25 11 8 10 36 27
      13432387434134400786216838322656584364183884367093408601832908389878581966886780747218013860279371365343913346663997088308191545941125550013882907816155064910915366670091255140307493270406859736357826124249360554269389941432186058134448902579892416506309798038540942097631058571229910083734429149196347591421246704802825378568601600000 (BHM 45) (kronHM 116 73 55) rfl (by kernel_fact) clHM_RDph cHM_RDph (by kernel_fact)
  | 46, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 46 2 122 73 25 11 8 10 36 27
      1284085285806037204834921429845228182225172621492344808127600026489519532811168429580152589402707737412924551714017620831077323946035866076200781213183694404706947996129067994921962266871553973711778023506658094549764532701599548991779727965390599478298107057615522038082853018112802458880707472040072073003626976802916495607390535680000 (BHM 46) (kronHM 122 73 55) rfl (by kernel_fact) clHM_q cHM_q (by kernel_fact)
  | 47, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 47 0 125 73 25 11 8 10 36 27
      6835548328187328261413538499235523151601539789991243289023538818297427658021411082541478514365407288395625399589662014112534909126642903352946635866603397172683264948011988720717519303382577523165990297603898519188506205918823633005190124011861632910138156054241501174896448563087826992236808280783427535490638655532843084000452935680000 (BHM 47) (kronHM 125 73 55) rfl (by kernel_fact) clHM_qR cHM_qR (by kernel_fact)
  | 48, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 48 3 120 73 25 11 8 10 36 27
      215984421599058788434350675305770787601197892609480264911721844022007884923585348496518759075921149426692474577207365382807517100155468369562254821507878552214146980849398602438783796735961942074400374165354676097898522780732033998758382487004240786286366862315098504768473307944788125552737248505849151910148438000566087605645475840000 (BHM 48) (kronHM 120 73 55) rfl (by kernel_fact) clHM_qz cHM_qz (by kernel_fact)
  | 49, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 49 3 116 73 25 11 8 10 36 27
      28584063315735721407723158154728314600871357100902054257878637670304910242335535649350656089835764281701407366206968362143039359752767763373764039548322657621514606157774747550510764473027566528904169794866562183423511698458381121778893571104326479594319146732419904927583999882755707504623149024235634950729109435782278840141742080000 (BHM 49) (kronHM 116 73 55) rfl (by kernel_fact) clHM_qph cHM_qph (by kernel_fact)
  | 50, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 50 0 123 73 25 11 8 10 36 27
      2168885196280646080597503176978817626080266184199550247344612179298038495961666901864315029789623269790325302060075448552060395899296606827847068844484074174734892492982814876376223290242734192035345007612779117877252585947773180007431335596114481889855515584796598630492555433047466140208456257271157483443365823313460440821630238720000 (BHM 50) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P2 cHM_P2 (by kernel_fact)
  | 51, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 51 2 116 73 25 11 8 10 36 27
      22191293738230194181527646658697476826866262389295945960357676800416298632036481836812196618325079464603505964017152451201330785032511433987066277531462998356721939629381326614690875263719134628832055501725846535489873440532736442580810554311463185467433461539401180255326860568018592435905189047968956332021030832969984132094361600000 (BHM 51) (kronHM 116 73 55) rfl (by kernel_fact) clHM_E cHM_E (by kernel_fact)
  | 52, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 52 0 123 73 25 11 8 10 36 27
      747266190868036235108834009693710652040748722564885581213412381554748553599317143924471618100992097019776484472054136389835915872343061599913293103793235257323506121150399424472362621028203857467116244641025174718095030695957748953530482271738504249046663143640195725286703238238591329679414960324655730871883668134716320801609482240000 (BHM 52) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V0 cHM_V0 (by kernel_fact)
  | 53, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 53 0 123 73 25 11 8 10 36 27
      758782824580498974043766556732914724733591812392719000775086294592945473589927736495704233543335149470798202903691985414037658311269597083148620158588011048946729145756165039364259757894161003285915268041420743815181522380347951556422412504588355821045940162996797858414485633739110302228580268989787604071974600049329038634401136640000 (BHM 53) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V2 cHM_V2 (by kernel_fact)
  | 54, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 54 0 123 73 25 11 8 10 36 27
      747266190868036235108834009693710652040748722564885581213412381554748553599317143924471618100992097019776484472054136389835915872343061599913293103793235257323506121150399424472362621028203857467116244641025174718095030695957748953530482271738504249046663143640195725286703238238591329679414960324655730871883668134716320801609482240000 (BHM 54) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Vn cHM_Vn (by kernel_fact)
  | 55, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 55 0 123 73 25 11 8 10 36 27
      1285602821729773179557527596339894007421997602572973590761504556698762869938132178420580315307177347961876573677589913143166224300814639148117152085374919487990662615893408903354614519655140333898329391156916770975516566945926353200289165639314702749563594562326514498568963737817083304122221828419275746018779772472702382667926077440000 (BHM 55) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W cHM_W (by kernel_fact)
  | 56, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 56 0 123 73 25 11 8 10 36 27
      2233869473208389426841595626119486851466604811047880128326218838063255152055765871432415144971323017902919663324298847535052127575720449090685832653602438592566166696574430869759726146426723198187467942958092612953411005464064304144910044408484787572469743695796909686403841334410815950792057679694371991275172534977276717973013438767500 (BHM 56) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W2 cHM_W2 (by kernel_fact)
  | 57, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 57 0 123 73 25 11 8 10 36 27
      3861226029635810614796884944899149344040396252131947317664679604057152601002021275948685021731418038557203321169993216210616388047157806607839384640624976755709558200664044737533928044816536070920144819555867794763763900525143937553419023012586902947694345913772990462912978644687544359615882913232375851668105310132595591051961569281250 (BHM 57) (kronHM 123 73 55) rfl (by kernel_fact) clHM_W3 cHM_W3 (by kernel_fact)
  | 58, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 58 0 122 73 25 11 8 10 36 27
      902724495143757274189156235768664384915236762553204304960094895057623744390362171808103260602360744817488509029215581417322785590082352808488165523470792917424720720476921022338316674210619486517884988735475743098849510736744355437558902884834480297923746132628238828634197032023683501247345676996293004201151383412578036899716792320000 (BHM 58) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R2 cHM_R2 (by kernel_fact)
  | 59, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 59 0 122 73 25 11 8 10 36 27
      990255069464067688423419389643003372220030734227581550660755360777547529655360489776706154766516063958313357995043209147040011573219191698768696404713100018653079500819887350237005746213283524090970105484601460427341058091693825665758707221420800902005391883778485873953767900533526665400990586360262387979638025968028378803575193600000 (BHM 59) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R3 cHM_R3 (by kernel_fact)
  | 60, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 60 0 125 73 25 11 8 10 36 27
      7487506285599968060583840656590311681617296084237594602191147431314385974817510943010307677642186148544762514852889858460726382997106945917611297499997829732075207772043600085457632484654673472790059695606542617091961561652438106694360033837892610255348675485152577396588126293625105287246638150012832645575423863169234051355010662400000 (BHM 60) (kronHM 125 73 55) rfl (by kernel_fact) clHM_A1 cHM_A1 (by kernel_fact)
  | 61, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 61 3 120 73 25 11 8 10 36 27
      227086003881853812451487438898110297473346408319665242305488146230360754772092599472193487570429211807232347447600289916464808495872132845385406546553757826385218597647876985759316907433715776171929098148353532445892168366579992140159501113610750383342866337535626606133114115536211553576631209355605797477180620893980312391909376000000 (BHM 61) (kronHM 120 73 55) rfl (by kernel_fact) clHM_A2 cHM_A2 (by kernel_fact)
  | 62, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 62 0 119 73 25 11 8 10 36 27
      189092576563807604220691119108037436692171135345693733584423157594447210922390824620877699715130568429841721072401431727569192517490630931426433059540697946040939935668781350046603131138728176015383778602401518785127112727350098668114584125910694310380480910598514851851319999270431413099846115214429523389041053707695802927892398080000 (BHM 62) (kronHM 119 73 55) rfl (by kernel_fact) clHM_K1 cHM_K1 (by kernel_fact)
  | 63, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 63 3 120 73 25 11 8 10 36 27
      277742048708961850043328988151432881128143610374992426597321467124762827424186354480080466723996671603265712456197742483095140753216534422365262483247802268995942753655366876793519917817236592359649396976806133606285282705353392816059332481988621022654058337995339646492255164527873542393585650865875943530869044458910814235420262400000 (BHM 63) (kronHM 120 73 55) rfl (by kernel_fact) clHM_K2 cHM_K2 (by kernel_fact)
  | 64, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 64 2 123 73 25 11 8 10 36 27
      3626620867500379962767210265391984254450584321175502923207826464726066974041959494920225411678123945625727602700092903492994318530280031590363009779740999218954439656456684651909745465509694449971510070881596206786246388319731544946459407788883684286982850127124489432640538930076828691566128350221693269835417429713201560588249989120000 (BHM 64) (kronHM 123 73 55) rfl (by kernel_fact) clHM_K3 cHM_K3 (by kernel_fact)
  | 65, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 65 0 119 73 25 11 8 10 36 27
      220545614052120134487793893186474632595127889640745081274638945240996959367592653136814867757976818343018680572882804043551130716786598570125949018358518320867965721919356000557262639808390537891409136810924699105117323792837403466950947027568332543862136268963407924390905638498980259900777543510374046977472682901236203594868326400000 (BHM 65) (kronHM 119 73 55) rfl (by kernel_fact) clHM_KD cHM_KD (by kernel_fact)
  | 66, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 66 3 120 73 25 11 8 10 36 27
      337591995214488574645848758527182248893698949601081468095737470874630743724389637636714140971766394399333340972723878027329422917856069413846392412987254696312524869247222055856179529052082893229135015731152959253430497806446181570230037048249280562697564627070006524044586049926131959887093458706469684480558431405713872395981291520000 (BHM 66) (kronHM 120 73 55) rfl (by kernel_fact) clHM_KR cHM_KR (by kernel_fact)
  | 67, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 67 2 124 73 25 11 8 10 36 27
      4743872627525778311862557384085316930198360147644912854324417413040183718866076981125740370782790096739911730572899508584428792059658464170625270432604159725363604019838079330761554852919246033556359108016969674944217466010693065972329568534879121107687531854442870192103067135063729822356367362850799571510793288837441428366064353280000 (BHM 67) (kronHM 124 73 55) rfl (by kernel_fact) clHM_KZ cHM_KZ (by kernel_fact)
  | 68, _ => by rw [xHM_zero c (i := 68) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 69, _ => by rw [xHM_zero c (i := 69) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 70, _ => by rw [xHM_zero c (i := 70) rfl]; exact (Bd_zero r).le (by norm_num [BHM, BHMl])
  | 71, _ => center3_fullN hq hc boxHM (l1HM 28) (fun _ => rfl) 71 0 129 37 14 9 8 5 36 27
      47834884316007366514710390827141909056247197529154234916542103802407984085589703716965365859903507820084146323974520578972347030084068806794468413262517742892203982563350372956891322394333781733012029615515798159953099748338049650562216420357787671704849251083839316479703000964440975522015003522729942892111187804867539538673873715200000 (BHM 71) (kronHM 129 37 28) rfl (by kernel_fact) clHM_r cHM_r (by kernel_fact)
  | 72, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 72 0 123 73 25 11 8 10 36 27
      1516057013835793987395489497076295764881781959329645574603809999100710346103004530179981418658862031483799417947255134348754056399399369141168565604373800454589548959210090432111750406757381486437456721105204528199284973695493710303089283363601853749789694892938452311193850245817895976435794424051607704750419343463384077565448683520000 (BHM 72) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P4P cHM_P4P (by kernel_fact)
  | 73, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 73 0 122 73 25 11 8 10 36 27
      1081824923157926676968427029809186282766050930444108154030629550402599701813936543726172850249952616527190337249708877482871673604837876246740053572910214200455697076602558305579552725362085612080859103018097342360907813059498478182159689265100589731204732678665743981462758521392816502370659952952554858285788807392732715264004587520000 (BHM 73) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R4 cHM_R4 (by kernel_fact)
  | 74, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 74 0 122 73 25 11 8 10 36 27
      1549419408152766938822673604340300324072239797383913806647172102970954185423785340013169345019329613724290797395282028505536489991673765538140889573363468032137173738916091779119511165847772839782951756047680329850347400105697892893275568838973442381119280418667938427943727892273107731324712401759911733110067238299854393765894553600000 (BHM 74) (kronHM 122 73 55) rfl (by kernel_fact) clHM_R8 cHM_R8 (by kernel_fact)
  | 75, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 75 0 123 73 25 11 8 10 36 27
      3095069404980423989481133680239675568043205319714815145128792483508828613555038437628990911789464423173659408824708427049573224085580464642301373275721439698533322607907591954064232475282226547574803306482608499782793169091195119552962586240595747696969246179373331224989209467217086275616018928211725404487745544134081076782369341440000 (BHM 75) (kronHM 123 73 55) rfl (by kernel_fact) clHM_P42 cHM_P42 (by kernel_fact)
  | 76, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 76 0 108 73 25 11 8 10 36 27
      371155853749046873799759819520583934021249036152597476974508848446713647405543373460913028377724109004694899305987956171962542729269849999357660746135844591342952490886441696445334791461040000757852967177958649539272973652276601908370736774257712256138985626699792452697640352922705130584289216509756801254137426142136941338951680000 (BHM 76) (kronHM 108 73 55) rfl (by kernel_fact) clHM_E4P cHM_E4P (by kernel_fact)
  | 77, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 77 0 123 73 25 11 8 10 36 27
      2591548043127621328765323331090265508213573932997538962326129153742212890575316261060229581012039402026567377368034234247043065982098157549594780628338974311435501779106108100198372615139196846013572508344387542130469740971523363921699925782263146215586867983613780153181310147406891129471471393630958859051312218312505692323735142400000 (BHM 77) (kronHM 123 73 55) rfl (by kernel_fact) clHM_PP4 cHM_PP4 (by kernel_fact)
  | 78, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 78 2 123 73 25 11 8 10 36 27
      874394077976603125192574129829425104190900027328489719002616808963836069790334734500160226215882028850137448260157443718596240864028414785912262072303026820734750818659715789896709976359769038316186727135363116870921317404579552452357760059710033821312638914370302772507148674831688304548452093524726981081788187505113530163066306560000 (BHM 78) (kronHM 123 73 55) rfl (by kernel_fact) clHM_QPP4P cHM_QPP4P (by kernel_fact)
  | 79, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 79 0 123 73 25 11 8 10 36 27
      736106934719874438744195462090381733587214156563811892259599882133059438598552143707339030329122021969718704826563964069811547199671280636565258874656990129655309018939555406112605505867718895620302545791072884215257030319811022794369446500807943417643733600354539415363782427107647075314929022959571787414279357781436269460707082240000 (BHM 79) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V40 cHM_V40 (by kernel_fact)
  | 80, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 80 0 123 73 25 11 8 10 36 27
      736292612043103561750736662951062340187270230699988093872210939404406075918321883775377882678115353026772268918937233395339704348833146337194865162664503188895423142993643809768089618276552926303350780662075839273284174961737449950570734884559620829482911275372285240165961801103771729977431022943357818403969294513355026031873884160000 (BHM 80) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V42 cHM_V42 (by kernel_fact)
  | 81, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 81 0 123 73 25 11 8 10 36 27
      736106934719874438744195462090381733587214156563811892259599882133059438598552143707339030329122021969718704826563964069811547199671280636565258874656990129655309018939555406112605505867718895620302545791072884215257030319811022794369446500807943417643733600354539415363782427107647075314929022959571787414279357781436269460707082240000 (BHM 81) (kronHM 123 73 55) rfl (by kernel_fact) clHM_V4n cHM_V4n (by kernel_fact)
  | 82, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 82 0 123 73 25 11 8 10 36 27
      747378866027324362269282346632347516430871097780709042810244604121135442631598105301308609723910887571150676249738450284530552628090574769496655679288167309005404726090433173327861321640906023488318862615333636362735220628437969295101345840484711163313485724819137809668133393343384693937154252262775574441401808183518833875615744000000 (BHM 82) (kronHM 123 73 55) rfl (by kernel_fact) clHM_VV4 cHM_VV4 (by kernel_fact)
  | 83, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 83 2 123 73 25 11 8 10 36 27
      873897967811129181131552927350402037275989576069777528753447870510831875264009340214761424731014707046984472250296297585874521991956449521505882268166025439267828286976145772836680969282039558385427241955357404894167498353548996740059909420780803899877288318024866583173205267377074223518707980196549452392440389482350904043592744960000 (BHM 83) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Bm cHM_Bm (by kernel_fact)
  | 84, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 84 0 119 73 25 11 8 10 36 27
      45995081073084006264144606564559527938699228393417533573598176733084600082297792035543621019137988288542448388437039018242641375080835391148527320444728598934811521695529204766241656148397867050973105399534421307647211296478893894771361942651718915100816587580614727384329808619654784155783657233394175857799219043141864941032570880000 (BHM 84) (kronHM 119 73 55) rfl (by kernel_fact) clHM_lamv cHM_lamv (by kernel_fact)
  | 85, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 85 2 119 73 25 11 8 10 36 27
      54618616901390938274581294305444302559099223233783238474989548264758087236948771659047016621118128536760499240657162416616383226320084065937543630370150262752170584675771497880599666687888573603569778134779334071124633688562103550394024441841109651417844868762702616338244747362957480695040070330870911792458864851591120771298099200000 (BHM 85) (kronHM 119 73 55) rfl (by kernel_fact) clHM_EN cHM_EN (by kernel_fact)
  | 86, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 86 0 123 73 25 11 8 10 36 27
      764838273716370965694592319571167006820632106025956748498772505096340788317995272415008978605609029601004836298149963062295597463631027065155070067166555099626287594546357009395590951563275779532581668988778047197409990434434961277899808570103976045894254694204832177568516884327914038502383869707686299520609087865400825455260467200000 (BHM 86) (kronHM 123 73 55) rfl (by kernel_fact) clHM_N0 cHM_N0 (by kernel_fact)
  | 87, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 87 0 124 73 25 11 8 10 36 27
      794882785428063439457600731136520046739062122517695450789995137563358260881379097752378823752816812315888277208954128694895564269918621741256101362144215381765422370092926980210588012826362499222680544373607212031931279386146872745177128187186754566467507418117234987710433517129154919083370885170689568826820856163556891127887953920000 (BHM 87) (kronHM 124 73 55) rfl (by kernel_fact) clHM_N2 cHM_N2 (by kernel_fact)
  | 88, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 88 0 123 73 25 11 8 10 36 27
      764838273716370965694592319571167006820632106025956748498772505096340788317995272415008978605609029601004836298149963062295597463631027065155070067166555099626287594546357009395590951563275779532581668988778047197409990434434961277899808570103976045894254694204832177568516884327914038502383869707686299520609087865400825455260467200000 (BHM 88) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Nn cHM_Nn (by kernel_fact)
  | 89, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 89 0 123 73 25 11 8 10 36 27
      736464611889671868317537751397653227449108162896719354258209619807348798629405620576759436429009515513248129412088575493171248282958020548913899088989983001919219314156583024921650881233581159315280619181123980847207409788087151143475996491507750888512238339328825326788868379741347578515922024887008270910598965577020992757547663360000 (BHM 89) (kronHM 123 73 55) rfl (by kernel_fact) clHM_Fv cHM_Fv (by kernel_fact)
  | 90, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 90 0 119 73 25 11 8 10 36 27
      130689522912555115129665690128827571081777221191232782061411440585846546185422443899232250471988139415552282833329631639818966383427230260076099809631281898684092945670282606854999040290568913791973224913227752957423849279017027602449039341525714355099558087552375912700693702241687515067022742750684856258501241556554023584263045120000 (BHM 90) (kronHM 119 73 55) rfl (by kernel_fact) clHM_YDt cHM_YDt (by kernel_fact)
  | 91, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 91 0 122 73 25 11 8 10 36 27
      908288767338838816780105713000403418384841226230870373803393329859853947806166356856915516711415112444073128493188017004775485844914398374789020153921022308310312044243151524183065623392509868919544918043941308285205602255975073699492929805993422429857957334309743761831496020646934972948386706256822271965326268921137459012776755200000 (BHM 91) (kronHM 122 73 55) rfl (by kernel_fact) clHM_DtF cHM_DtF (by kernel_fact)
  | 92, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 92 3 120 73 25 11 8 10 36 27
      214732322911143430729882085984457720180581626287055751074994521292661951062600092086261380450622636068523615690292513835843229275640898509366390016654592037779541328258442574454832414116388052624171880703540239891252882708519632251273720027492674538173716423744165700724693299188128504444758403991731284846488753436371707123144826880000 (BHM 92) (kronHM 120 73 55) rfl (by kernel_fact) clHM_YnRt cHM_YnRt (by kernel_fact)
  | 93, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 93 3 118 73 25 11 8 10 36 27
      64847942947127064437712252234176447746809825041509984737351844414101017957931569929551320415195550693742963260734660413363805324920406062181162465394842144835168525940014847715473363987061377678170578318516922276095917018613082787867380521672313480173987017097399805798994273775299498664838801584508105620784587355446116939705876480000 (BHM 93) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nRtF cHM_nRtF (by kernel_fact)
  | 94, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 94 2 123 73 25 11 8 10 36 27
      2197659051713900207668891693776307355242597048360502330211191369503452985307266781947867616956530767862401425896122700970366140125924142205921764403469234989250493651732027499537909646297131338578483797877737854573998093962769838641366013380244486859262708053837222447689530401712301082887833336210183201891475571666530078839870648699375 (BHM 94) (kronHM 123 73 55) rfl (by kernel_fact) clHM_YnZt cHM_YnZt (by kernel_fact)
  | 95, _ => center3_fullN hq hc boxHM (l1HM 55) (fun _ => rfl) 95 0 118 73 25 11 8 10 36 27
      67321068532913415754332712555967880126119658556986010339462214735451268707837868402424250202935962802512494530223116235442655719032210266480618723971049217996348051673858984850455596773227644670989876530317842238556090174024322916150773914714466395132965855727964419549983533811448499849148293326370017999555260145011244209128079360000 (BHM 95) (kronHM 118 73 55) rfl (by kernel_fact) clHM_nZtF cHM_nZtF (by kernel_fact)
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
      72 54 24 123 73 25 11 8 10 36 27 11344893698692134882520304660758205021561068270205044035841553825394952282552471355773681794784284403097310257061512097953653871049695341536855976677577674366521774021932148212496122653837984651546558248474433795739649952295446637188691189311001607433597742350360087137426300324114783186876444590348917147096163444446481745088348160000
      (2549 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Vm1 kHM_Vm1 (by kernel_fact)
  have h2 := norm3_fullN hr hq hc hWHM boxHM (l1HM 55) (fun _ => rfl) hn hE trHMN_V2m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 22861527411154873817452851699962277714404158098038463597515466863591872273163063927006297237127336854119028688699361122155396309976230824772183031472353465989744798627697763104393259519795130470345581648870002892826141636685649240080621422160853179432874761706962220265208695824633755736041753255480790347187095359059199577880002560000
      (5137 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V2m1 kHM_V2m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_eta (2, 0, 0)
      144 108 48 237 145 49 13 8 19 72 54 43938283157983102905637935071791136568109583634770961261698944393042597116999684863766306057184361014209596155253363752858384448726704837616314502532852952743177774428250877727845645121151926670923847613297181911786311042843082570031237193789534050202635577472683327735431008610484551021607693720037196708552673706935925600931050439929422932190037045812448701560334861131044832630475946500345211416563207465750111102485214352577878613337650209573360039505638565360562435515282570719045379866220843882079574612322549275818754754590212642191224525320569566376982695520983048153844727858860489341054495873993304991176016233539110202605746257920000000
      (23 / 40000000000000000000000 : ℚ) (kronHM 237 145 109) (by kernel_fact)
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
  have hv := vstep (a := (((2549 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (n2 := (((5137 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((23 / 40000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((12827 / 12500 : ℚ) : ℚ) : ℝ)) (m := (((541 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((102821 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 54 : ℚ) : ℝ))
    hr h1 h2 h3 hEb
    (by exact_mod_cast (show (2549 / 10 ^ 5 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (2549 / 10 ^ 5 : ℚ)) ≤ (12827 / 12500 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (12827 / 12500 : ℚ) ^ 2 * (5137 / 10 ^ 5 : ℚ) ≤ (541 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 51 + EHM 51 ≤ (541 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (541 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (102821 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (102821 / 10 ^ 5 : ℚ) ^ 2 * (1 - (541 / 10 ^ 4 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * (541 / 10 ^ 4 : ℚ) + (2549 / 10 ^ 5 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((12827 / 12500 : ℚ) ^ 2 * (23 / 40000000000000000000000 : ℚ)) ≤ EHM 54 by kernel_fact))
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
      72 54 24 123 73 25 11 8 10 36 27 185637550530338517881757057429286568026502269131355082029054403705837281787471138641094022914209353039530611571339777929285198377914378188821747541332546698324671811088129852739007493353022804732859398522143292901649576148720478027655418380440776030668199064703777214505489193170528822390507225264973689491853091166430404185948160000
      (4171 / 10 ^ 7 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_V4m1 kHM_V4m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaV4 (2, 0, 0)
      144 108 48 231 145 49 13 8 19 72 54 1684786118968709823517069016148624933242077400337229611173844109918638282027366168257653349275487742627402944388458556252592162839923526943150509847747692621411333523878433914752376490311401956472410684498040600639263278891257234015065822562988424718809082919108075555417119101268780560436893016604236011942164740812531061728113670912553963100263112073242398784160787311060496865096112814118753622152383141445860545656717327079106463011311387626317655683154302717914033499783338078063878175066684294710673277851668532571805351465048052645121250156671558254917126192016123222246828786738855436197434078260444758675785047635457532729963315200000000
      (3 / 2000000000000000000000 : ℚ) (kronHM 231 145 109) (by kernel_fact)
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
  have hv := vstep2 (a := (((4171 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (η := (((3 / 2000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (m := (((417 / 500000 : ℚ) : ℚ) : ℝ)) (g := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 81 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (4171 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (4171 / 10 ^ 7 : ℚ)) ≤ (50021 / 50000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 76 + EHM 76 + (50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ) ≤ (417 / 500000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (417 / 500000 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (50021 / 50000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (50021 / 50000 : ℚ) ^ 2 * (1 - (417 / 500000 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * (417 / 500000 : ℚ) + (4171 / 10 ^ 7 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * ((50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ)) ≤ EHM 81 by kernel_fact))
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
      72 54 24 123 73 25 11 8 10 36 27 28916976547026865468278614538214559801444451731276211321201677366987187001230599846311042299401216984325662083157338770413335462337660806778632940050897516669303247417889733135724453188909906717011982596227306275054609690772658961558017487676473404281189292914996539419239946413437492009845353973379485795821583175130986398739333120000
      (6497 / 10 ^ 5 : ℚ) (kronHM 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHM_Nm1 kHM_Nm1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHM boxHM (l1HM 109) (fun _ => rfl) hn hE trHMN_etaN (2, 0, 0)
      144 108 48 240 145 49 13 8 19 72 54 100330269300835475770734428250616768677563544345806232629089648139099740545836297302948825503354165961782934347714641923808030936777307269752149075203221168541995502086683810561175811519038020429652897296315264757214544482861449246666295018151420834621115472827757624563412258572814129998421945042899918092811886103478834249621911984263035383661622744775335230249541193209660700065043195983202457134012017125625540833789940559251425722822073163175209766231125154154287214204705308152855769284489332768280745093261602656976032425367934779859250478267358842723781297622292382968419650878357945001817864572269465926578008002755849308006464104693760000000
      (17 / 10 ^ 22 : ℚ) (kronHM 240 145 109) (by kernel_fact)
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
  have hv := vstep2 (a := (((6497 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((17 / 10 ^ 22 : ℚ) : ℚ) : ℝ))
    (b := (((106949 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (m := (((1229 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((106777 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHM 88 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (6497 / 10 ^ 5 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (6497 / 10 ^ 5 : ℚ)) ≤ (106949 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHM 85 + EHM 85 + (106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ) ≤ (1229 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (1229 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (106777 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (106777 / 10 ^ 5 : ℚ) ^ 2 * (1 - (1229 / 10 ^ 4 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * (1229 / 10 ^ 4 : ℚ) + (6497 / 10 ^ 5 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ)) ≤ EHM 88 by kernel_fact))
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
      144 108 48 236 145 49 13 8 19 72 54 89554169008585783715107240488541653303483446061790305833373459285736464752418125932516638312338665377547589670329710398025646284315301328432352898356904467356073396977725137070415947706329565433212908515439996858046847841136339609794377745820391928121489236698041972546003094059272259793704201157948883499006933387405846757166697847330490714944684217176277572551441757094444316202468155181239048585903133737566669824990605068679907873661401152905923002084462173082635873310192037211377141926548328063444397136409607377872347060512629795239149051507707067238622501389556791048301313298211785429566443652441808228029077878424636246355691438080000000
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
      144 108 48 236 145 49 13 8 19 72 54 52503296927360953848505089797013360817280086225623698730657791519613819824946601063841351039571934416071681230720483590195104501587960136571579500695423561212309665738344640925164807642479711223972082129822967478882079432043987798977711523965411936837341570366324262710058606133187350554124546095013717098670222829676958495875519664613271892256311889743924115915191927719473067203400364432287987992339710571720168516173929588574876200960814093719212622140453160607208981922146277939054847758364518065970133657945086616150530351447636217179129920760938838084061424544084990239852349578034991063072241069484203619962696096549715182295795630080000000
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
      144 108 48 236 145 49 13 8 19 72 54 106467811375128048858316379256880774908432254645160568616579023518212588180527713829682164975026307410561723746423706248208205677363392703229995386455629074300790364718164234870000803977924005831484405119839840775688445626763671435215936645210725028770290238621870357477186380382362967069477950061749600261563101578399653343754706476031339368415659255699708541306272368304032279802956495767110567254446743095208953944139908699617107709112363042766216892228297616496209323000301470610223234320171212958978702969398908573820349559807371678538727690909148642222572489012419994270329674220463555604893452181108243189356205267826653250966131834880000000
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
      144 108 48 232 145 49 13 8 19 72 54 27678259396765917695809877240270923125119364669559859041530591872675754757687632631174260566382111134227977662145756563387277380964510001426069009481888696975940230681379002193563294799959165088338268566457881427817710981045426695584847898522264819511423602020937654429461838571293914726953631470354226820429581343811121768288722350849497625196538813826314460145824685352639722063842330161222442455983105655397582844039675918590204702911357688437014922937607454692745914264452111556443413716382380203024984137626104373682347340684837080520993432055591297486630453871838880498998794768387272303644072615687905032981910295687673773805944176640000000
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
      144 108 48 232 145 49 13 8 19 72 54 16842477799329546319175711075220920191710230059571886806930508482979648780957405558385538323566819471925883199586196534593830431871673041203400340721295741903173959576480377750949768038639349235739573778662054002743751035135668341575494212516672330048188667241382437979206853227402501508476207755886303417609471384462332720377610550634686462927872564716605946583601801980501641417701810518041893456437185595181656616776339047076906795567329756269520748989989627347977417271370731276716151260386468507375004423049176652124432176938882327899970685148116065391726108152325971531399268987879667921088254704554519413915465924941798523962927349760000000
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
      144 108 48 232 145 49 13 8 19 72 54 18441868824808084006349512011807245456321018660182611996576965308005685706734834962813001948092290039713433762519513550094653257781341468664828972641754117506612777603856241223214145334825877950826718198033146994098863863078228669287253361318083778745630444059597113917016016563536280207552949024256846213471509864739841051199062333046144198917589084617181427300611313213150441380141323711275040249969531670885142861149630424443203156462986710343140615097110013197969508566844133270897219137000471104615804578240383599983489864691152537012441158737206670907065773424180616574025696080575995321179995736740104199099709894461664435322287554560000000
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
      144 108 48 232 145 49 13 8 19 72 54 38988724340044645033300987731547986427151597886494031687923498229104490674462282412974113971052224319511836817546219242313164444588905380819380751085268353596699339868860287729620962491164530032263913719851374345323811492246003405839343102451699056854356645577420757502992783144698908588461982931848885406805804992102357903032592729335023962774212260525356347235980925348613456407718667552155046549834889057494100610050070901945669054171039847794020844764533704864277297146908654114976318739856647834076937952702564066030470955095947442567142504436516770952419146026560624152446910491913286405023828126442246834946352044520631286673566597120000000
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
      144 108 48 228 145 49 13 8 19 72 54 3445712609558709874399137445232635488365835428279649413393403430244499711328308000906641362393222579707157699888004656243170571513771985039563447008449122133007192106844140383970827344847151464421613154432998934085588585702472046413399000125179653772040399794229575691740554154384079335656422242240725194407512246982807804837041399892786804869544065231100729892048792962272077802495889398844069040142706167317541028138877803251370668342459024657082764432763014139655347160616278845418786745875680185823475411195885504644401505468402386082305491044609806334804501560310224022071845254407199591202466232941328736295610992207788641740275056640000000
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
      144 108 48 228 145 49 13 8 19 72 54 3103361904965704062464994266825833598611860254789265303320568209911243460792527439657804676548981540494267617304019231927729079376746852200017269870602425247645694507263817264468760556279775418583854569255431814773894519752956555397554773789772950472015260161920880380165454211194557087297840025320603131901138843378912006321865174419699049829127332978262077920943559577107108012042726027118976353710320867382205257423419544325578251029122148598845902868656963730468517121161126962759970569645466428679380979045521298420484288978296346585591991672676436440726956324655205771029435841982501471508482546963169828081033111661590167251813662720000000
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
      144 108 48 228 145 49 13 8 19 72 54 4592072433841412893471799537070867459467066647363066351737907700028483239800362651534464032403168281663297992859114039229351419558500315905444475244689445819880548264596543865157897227209122013470841664499624156222618931801728391537385789780985186565958985744579283558357290689826362918683584584085583461677068094000267044343306540512479755547488629734460282218170279161298016433883903133535005624052158257961957733935762753869088333661802629202054857696614512946672343076203403095905928717063680168093231847249875869376239190825095416005875259867309168149439901255768376451734225485168754999591480108448919113886541686255780220654898380800000000
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
      144 108 48 230 145 49 13 8 19 72 54 10824347080371312751465450813086435925562668100733570029916629179978191803005003040347133556850552687834040178654594703523309691676557433115346735809335486758648909741802986403712286955062490895641221233000326636000870946534991873246091366482763441824038527998818691768655256244188263649779655320118705861600363757274593337176218266990452777754056701224200677185087789325937007011589267820789261798889105282976312351632629029009184445631817414035445905056143649385054385793565387477825827272667463919978249711169833346986162290675623847047027957444794865879217963798153855122979716551304206436384468334536301118082392783273908990014841159680000000
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
      144 108 48 225 145 49 13 8 19 72 54 1326372862279643526435826688390259935233286542501514892998413175960801624244022803727224233702448662832625703058170816527860250197379450354016510922372148383400227793334689237313462789967460632366368637450439065004252954086858927288926673771308525692080148064725971602836933674590879553627275710735941660130006879155165694933285010424523069885552725108766677971444592372899225075371676444493809848214019664915318670012334020155608917653590957077002561770463859278148459592755160112583676196977148935115246752131618119638353762469782624362915158005895003529036499770600145969404160183189202933033598509983202466187776282634952890730917396480000000
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
      144 108 48 226 145 49 13 8 19 72 54 2911794782060778446357957402087001015417024089046180640561738347359528886629073741457926936170362493652348823265809891738436423572782564685695466037241571325238821333116838088435242721407841074004400538742041317583620548392141888042399623449097100210669986460218493473339869968297765512869722252039707132549352187459487938234075978880411392547407136755274862631852164981295399953539645850223377696198663894395233976764250106580720094600825287402739462529192340986050311692095646410372757855407224273899460197986889737726461875931591955623656668597440798197495288530801260276842372474602542510504296511744531077530022422262256564708866785280000000
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
      144 108 48 222 145 49 13 8 19 72 54 549977939240877577877027318770360418981221834455206044198956258458588910727321785858890942463702925250197403290212745485528937649945189525501530018070740663724869597939286242307982907671396648383164988607009494295602892520162212472896457150721901493744155154736143839480521623619565049791928087593333294605987209326312117589394139245978829936483394909629643735839208276725115032579227806357174401007846744006002127583393131340207133589798942307707161741573591056219979041622382092756604985680227212433312297802388601129960485535805071078645055799673677856770836382000381639626016112898178326261297952475518948142078642732139762789866536960000000
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
      144 108 48 224 145 49 13 8 19 72 54 957566475164824014741016863779485810318400545309269830928933822481477665005763886094633333718385465520807247408807388445918066804541738105466286797994594690896932261530277852132788376895374899660411866312098372161871399219468964504590238692071604256198935616011456256557298150686760244189330919104754827780385650977985495844261537916395459786067103735079927418164477230042966075147267514253123682424058459447412958693731195825058785851567449698610254916740522296030237546138825996160326671176688171108471847082379944062900408224012540038850668194110548148188693659424175385746465834033399394212807642699602571943026425185448127403288166400000000
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
      72 56 24 127 73 25 11 8 10 36 28 979948379444271688271206196695616054766082441567516966337191245888006202012778318609158469446526907847828531752348219334142154523268277190750080815857098422344625477529740825506593118437469710471241019252656138544143687374024062601903518511960913413292796179223368769214054597761811257546580713753477989898649600000
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
      72 56 24 124 73 25 11 8 10 36 28 988246645948216332829563234643913308137613252863144407721042957154850503097202150221616634255116119098736610865024628587541407480443917147391213105672527360741909277360592341831722310373190914172754638590736397807677943320553925183249281935420551107989902560836505289181816586660088747928078045879253142706585600000
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
      72 56 24 125 73 25 11 8 10 36 28 2015565476034053522145144186396937133778862438414177382685980031287070152882888721858165063873323090122738969505485947423550218786680504955329785510400540995199703466447856086935589462417751638259052082677714663421561968175438664275031227285295284423434934598785113291645733578291119838122969308303085203546439680000
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
      72 56 24 126 73 25 11 8 10 36 28 252578171470635312839643154607507527492040743969344998232318402058091413003838395220669790273155207455584766970071600597586423266076105162192147206061429803439508471925198194159741593126908974913743308331355030758316896222975035456520998102170728157659806517746059918091582780661646310202826260314757366357688320000
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
      72 56 24 125 73 25 11 8 10 36 28 995795667797656397899823490731377752877190442875019008599334721208668943602557097265028039757183235718168773485751767540886061693722013544015912257976576129139403985164475259653574092668226252347079910078669530328334164333504840711675419019664413393720594694619945807548988513695970411984877323312140907152670720000
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
      72 56 24 121 73 25 11 8 10 36 28 505245597841289647815820270669015702648658760397403246829047579678252747968022293627677048759080889481062373074448029167144121690656785166551754859552623146499395008850907670546651915231842426804796150738624401717391411709244247095902925152705732786634518329167387509793690982684106989452288619953087520062832640000
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
      72 56 24 126 73 25 11 8 10 36 28 987905478243870427250500121319280355095121516193331848441419352182612739174888164704586451657124313998661236989109434890280007654844377758422111403242028527282759564815939596088934117472233147015015009254475987429585041860184232723684606927275367045875665183013177128577576428070112616754977490579424556896747520000
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
      72 56 24 126 73 25 11 8 10 36 28 1017758849029221373569387736048389386251213200518680695383868538375695338407851839716886516229984232989766826602611134447900597825005816032320190621597203953245458636218396773399915427950995344624213375401526917533899057387506092576821104562165111709318182179528225762352808382089468133452846723843464973799915520000
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
      72 56 24 124 73 25 11 8 10 36 28 504951708981426877398470461524410145806030503285935164342305884436531293726757518947522835106375124111494440326789541767357053258253927057737149337480837579323075626896712757200568597158946236385180422735970679779244432589511634584950258083519274547872700651701953172341529751264858195002728103618456513392148480000
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
      72 56 24 126 73 25 11 8 10 36 28 1001563912519455775891366249261226097114581583262547119099442807943636238251293047420694747520732420851753103065493099431532962990374398481418004039886985231982567232233390407552726602034112555994283362998469369821538434399223223602357731056647136061828740774455415909073284677259615287538996270054994088873164800000
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
      72 56 24 124 73 25 11 8 10 36 28 243517293965755314086691459038500047865074763210677611542293550200971592566771646577192815521289883096925335039231979472769946719897801972617362664522941749052697163866853524403506502939605616371893712447218696642123124671151970821846844009837859210323187531883043289235802166504395017498316476252269639777648640000
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
      72 56 24 125 73 25 11 8 10 36 28 998646047862076692987909116004564523003146495053525777566157960398159644515399220930327009193104135815527843342554391126322716264995486786446934428651178459767259763636437264082763512460408111269200433414023987647961545023466838174140274892058821833984770491881333300464260009919926405303186707604369307514961920000
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
      144 108 48 239 145 49 13 8 19 72 54 204047518738155093064162010038097356148560461726906716623825814429851919315496090323543395814898368547459437504198368386792349304611622292801259358746055180323415562329592249427394391143656072869014265826051013878757335316721791753954503900005328483059565041594524034197608065018401804973143444436353265830062505368815328082060568323896590985444950531107405985751780189296561274673104233791398586084255807293536637064736707653216629166768758274079692876882078271625000624962408585954956515296491417182890657353339674694348356556162532133719986876071361555977718207266617016569830110260229963855335103054028047473162240220414593314839540531200000000
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
      144 108 48 240 145 49 13 8 19 72 54 148128989974896219219501243280186900065653474443235194852222974933508188054723856155691133914856728310205098151571318922835528107358195969729233110183776368367985375304315269769402534408648054316378076143113251689811605333814836977684320762513534445799842560182208764326833781870968782345675098670127667764346631894454303872277421211746385759243299685989370509053257950706212224936407748562061258479730552415709489387837875780635959376887698747971864161993747104380910714761608526787691612754589183382481324956947284582550357506090603225182753597264174121982998378360546375352912214227333538652405902850211630282032813092355489051394965504000000000
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
      144 108 48 236 145 49 13 8 19 72 54 82226144901781709049651451464872439708815822973778524474840355889328943503644200864072388221065471198201015702765055833491645186243935809996083849736511904368884491571557534442280221559757855450241830499593649629611519840397585406406987769418115601191374421410302373936920608694693999124729908316073827171033650954267857312789440220243868023690182285977546757916050170601457965421715879909954847934667854916292984903740834183844307338333535265077263628112188095860808831553638815136859356533882787320900864598546632686336526265648108329264789400451828633515639600546084125313271295017762664962002019184549584883422997115075512329012510720000000000
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
      144 108 48 233 145 49 13 8 19 72 54 24275705537824775221579767683283958275201433272224944392499742087552384762643238378158000225017287653857058712644855375555573665669920378774823147914687030749497800010710920356462595752848765423224178033227676955599183098938485695551646843257886007613309894178181020708355765895931623979807541275756055086075959299146050156430642403604092683312898216261946153862781289819144340744190455418908200488649507688181067722154155077030137000778433420725570803464697970607506983163636733510675897542450184873507866985223671489703478565509160081339388785285189701790722124132345589303152727367960205932076728867332418875320809378973936510890955243520000000
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
      144 108 48 242 145 49 13 8 19 72 54 940935104289246637225168594535280203108013485029212852866890237559688531680830227541457218089408401192928966591217155081534307052826993939240865663115443322484978965441084969544321388118489276716072105289689179019970482775487079655111810300114576294090917435947256522707316872615405462450866914136331131528020659793450719707619006157999088186395015471060416971232773011646657139173177629219371431363640507998533517018077273507211655630077329453436851941471261883573937821584107612310145988354455826658873008122656949905951852258740912084199815323099251375717068195232524748129058148664903893920282688279430988921194502284528183698817894318080000000
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
      144 108 48 245 145 49 13 8 19 72 54 2871217126197696523159428903662867917151339450908395928209607000404560624138523408080768956151568120430986760240394568550160802823362238726023698741462336224223031381809307720149996260259468426267263894305956856760815875965857605239341612511128733192730767145640643304607427494661450196554181297915437980981397821088973870089174969015746182880373643238150633946278429606157037782519538016997577183336503106557740671099551476158319697629853876437288932012960098566100990234504743525660352134418764498509369427946484321708487289850316717140657999303822247681436528260353393479758734764307367354194977485034572183313235609554128105815303866286080000000
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
      144 108 48 241 145 49 13 8 19 72 54 529888123725304193418679486914681882796438289723025617808211444366019252966377130065836219544473216380223364767886357394565282897608298859409178124788089196812229189930770619084080575232962264070656215536620523489509033463350455937132610808347200468309494041003880600518739631911062796890867051902434144947954969766995500688099561010111468463965906510047084669532357378250642002811710190178847273730006210666308104959274447549860419866112781655724624358197622561425254157023946530851975366883515099434847888832059296761464865132150487670764097030898897537319694223803371777250779722580905883104157973870278412250993737667271244372712095744000000000
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
      144 108 48 238 145 49 13 8 19 72 54 147308788339824167647677850648146428002004545188133619983447199965979730163798343701088395039254723929944015534096239313883322983750875784657002800730818598005812593696063616273045101853151318240707708513573592987623677813659013999710131562185287782257379227026773981475297782158905345085641380316480061922818401977330131856555560733464172717967090244087836567466136882458952509279717997273046620593631356156295508872676534884810256381084688137883523408000752861887117366647868500111649230378613858338669171709199156175746027617593866505983305689337494092403960442620075111724634275037587709024854667641655419607176514581623095670159766978560000000
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
      144 108 48 244 145 49 13 8 19 72 54 4438577944810187703421897508503076906359280203705470488772964980789576354929789698492627218493292231496030732982894824988711795765284017035280303036473662377201187510098588267623408830972960451285898250179067008336163149628843292653073405642887378616959183772634878024818513903532336873332263467570745626122135998718632621639246858225021120452134671028348374768286211214223001570277338267114447704138678535694738035402525914873794303213860737133230513379390618427107066877063830023719828600771774687120047415018768772610752489021474353176634434290120382062814246881484102213417760160996510889684166924632172718063836137659946439409105318707200000000
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
      144 108 48 243 145 49 13 8 19 72 54 5394741261055328288316622787799582950933186834063069004079377549492866678267860911072717565258939060881603528234736640460253323090513107620972100966457608015735667738168980771570181654537625417780936635753125273850395007036929429684680360353661276675227183687836903445869310072482214513373440890785095120002179961253590174963088944603522243710604407775988489306744779619733831268689525380395258825970104558686970124270602553164499481826843272963042597747155173172188538968739523340828183697622128493795984043343340812733696410072146602719352283550939544304465310845850849329992041908621633189270751929356604932742006384076572100043306549903360000000
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
      144 108 48 244 145 49 13 8 19 72 54 16335446290763460704841180251292250360500032245931535926320987518018014689326709584333407094698542301727603403969937506120506861122363808988868254303353584319899995991363255841198271473476391242405771046681375788633695026060029760506909896699899076027103339340618994160090399687687537733422863016169509140223976837665814379705480419416615162677815266489664323206870019691416535431880010283345929423100694533862955337895478938337821514895296627282576108886233335725255755317172188871352356279855317132014365964394295978528318148373956825035133641967136812812852936008398831528703761673999268655712141852380642073855063248316935816370968330240000000
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
      144 108 48 244 145 49 13 8 19 72 54 177225412063448852602999898036779050478244540867565641053405275444761095846586499102275823710030458206574227884243562179571294664801819977589392176162036974163508529322382704897626748022924975255086206430387528733328147864204615697869854918263966049861018412833494743676982666347040141993117892423490375146286311660027965790395641906580616458833332752162469807776579070637501635144063069584520825533385066713885774071816174492296651209652065786681655330177903758194928291560344347094973365617930866518761881439409638528909855914532103360579175929716171200247269679541949559557332839298460472865602487090444096147445276003732646175184624025600000000
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
      144 108 48 244 145 49 13 8 19 72 54 5316304421668526240317683493640915531315486507707552942219591634241351290467824770693023828106462856693284076855172305575579028051770029629833984661786359729613216827439375854711629877643760996213386292548308044252356494345171759280937389714271652854198121645980844055214815567125141400555239266692154437230535425790298257362333504497875528589746024921577909982682208204609966252254923349819799434964024457662795080068909128416750819985553140875527426767838055956369541924552681993418096513617664049966345098931699059273325643115787644551106829080585038081871812174609744443014786184263542612995911496016888874659681954941890592709209950781440000000
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
      144 108 48 244 145 49 13 8 19 72 54 20304318165585840574528587118354739012892414969309690990446311704050015300152037798549016478185107318696867541426932168930604066035625807400250278049534384494752785451147657653492990727915244372306491288661858848510851876216254818461386778326558312337814935996177951487952448227280399152674724989933618782532354551396294283275484735637708977291284972768116827344020152114485089072037342646092998692412667009628546095284862403755569184218720887557378589579845544001559687368337072951001387965968996041445402635196799693428276783761563894464629941461132691782368876898546218347124390457998895537558104493044876839761141976106914482724389603246080000000
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
      144 108 48 236 145 49 13 8 19 72 54 106467811375128048858316379256880774908432254645160568616579023518212588180527713829682164975026307410561723746423706248208205677363392703229995386455629074300790364718164234870000803977924005831484405119839840775688445626763671435215936645210725028770290238621870357477186380382362967069477950061749600261563101578399653343754706476031339368415659255699708541306272368304032279802956495767110567254446743095208953944139908699617107709112363042766216892228297616496209323000301470610223234320171212958978702969398908573820349559807371678538727690909148642222572489012419994270329674220463555604893452181108243189356205267826653250966131834880000000
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
      144 108 48 239 145 49 13 8 19 72 54 188170470713158111237677996142776816254271556472362514339598320980138749932837267768197639054386971318247882512192760901680149619898486998134704121693698879575907297811915439706512919691264786332080810056691970585077478066866213318523198602217399383568790648297748766634936828136561384411558380913598330892080749369925180247182021231623745913909866449072482494047853139443011244121699091251929184641361747216730115226133427135533108345517321415603932297007701366350774442605898754723282596615980707162298441390539430644526101925372996611747464721843955235914091669836325184878794445540970562506548259992185188393345356731092511704329287106560000000
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
      144 108 48 242 145 49 13 8 19 72 54 2838495706622608119000525287293942933265603565602008607131982001201729655151959755653729174402048443689980784258537282247765202003348241267061521792396713191278039126876775516339927872585784331822528751334648238407716239810379189105311594602013987038932710577671178271293514562298187426323248412164609433093676152043059484839568875010580746718058303616547789079191474183871919198195116481959909730393171030295594369226493049899425093253963737711829058523693581311187940038875312218561541804680018999193141131241618197314022687396786570641676635334604971109873318049446340759259072986830736737700563901740227529841125198922185372356872020951040000000
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
      144 108 48 237 145 49 13 8 19 72 54 217634728014665409293316236385806033750177470370740788607218599496794486721059858512393176317937814223702317855236101719654649668967934877283197178983589085910017590061309951512584626328285055562138370063424071602919994087585915279219514373476840414808842294148504731934908275427920544443172901130556586312046176832345730818861047710303629952012472640806417872270231543090333056280313052983857138165233142908771907795029488251057688465172092549878916170676393200688071568309444272974910753914521871192903883217561155778925044654619060338352796634525973269629018214908716926948944297914808258700335068988909710420846285112978906821567289753600000000
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
      144 108 48 242 145 49 13 8 19 72 54 1327524610020756720858934885897383793694045312573134686424617756276506682947582533960512284875141015523665199409046180221087046214712811241342895856144715445145651601498684421881776024857254269857531516393098924756629780111926288391122051138436428242438105326051152383851155143071075124480867479204675488062176626992679951405900190706507906136636075518481259961397415326784981166684157414569912563522211798666957718660242849090146519212187145409991823358509998792575424940942914815288375596787055217538396281297845130288168336774983275734235187484242475461531603220500891436602044151542613684369437848989113947828364104186439765557854076928000000000
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
      144 108 48 240 145 49 13 8 19 72 54 907028742288734095809568450373146462262901843760097545452129694916143666459874859506021471000011406549596900271130320922377341320753948204722888114544032119230926654231509782709842804229980385052362723658672569894730359717360313959641989725610792889349168773811199802909854705368825254955895802504909936379768703693917235120960198972674692510374154358320141421533785286904833077725714000567286964404493422008288702625169637200534720165302332698268247194038243541648684432424313331453925020355093226544032881616151444381172595531329737160457520002778702896214553579757899281434409579010551039508545647201220221357302439995414368897700242391040000000
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
      144 108 48 246 145 49 13 8 19 72 54 6223445152649756731774698919546055700240926729243088295830068486126470876895130750847637340648182090473420934372707477853774933146050283717089231254648336894428580637097786103409758099673431197496096006622125661042797260291543258793421440099780017173127365861506072956752732769554905551092231989945177040458176617013893667428093174309644347920762973973506949431831534624538522497281577786040382780031216905561331561048001423604689663809718024824236591042884134008038085196284524317183787052682953539058698407295990912292160709943085818061818060633476597685001208619396018723042994104192614361620411202369562226775990473856501727489212505128960000000
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
      144 108 48 239 145 49 13 8 19 72 54 768208912629798735465000276505766248055444130649404894825129094189747469053128490486399886676746780369348935681639805468035851625887583012803007971772148379726604467484267501009510067003494155951388669474836138313259641394851152690310410528083851270348234316263584139055298978396352740321529257138979665606872738275545226903280970894507126033245611264371265389114545197865999885034514379471496004855143482495389634807684095212859125704611159532894054220752203383700027551567805544919190386258090809018559728274104970279805235237575677649653797292022389398604261631835344149726401172133153820593654781042250927259558947375518168871796924743680000000
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
      144 108 48 240 145 49 13 8 19 72 54 1389529432041629679853148445756471908066995341647017820319507099168648772811295238415960613233593805392882168656563901764639792680655862947513353104113680956306793114612653511162388723370987794551342311260188880214278389768219484421760928148912737108811119518830996953659279002149074710125119636661865209385333298012728148199269714523168980164104377761800238640128727443119766664663822059364963009574297182793512650852706864871355867159322218102504363074485816693049117351656037593277351308619520294965746129004142687650850551903324056027147535738811824248123834211745223930163028836974640138047294194859341155612725064988933161154128495247360000000
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
      144 108 48 243 145 49 13 8 19 72 54 12675493001488300063263973570322388436029634022139800768479655076065788801671186943929476989286543619180614687043203886589398985304392034345903238390902602147927235149458821463120829864115209574893043564690086098905583331246129986512223495515527501534522926487339107916479759959457972596775316084397428289430083480368990189854359789130721705266250605408713044262523963080720610628705103992863621203515632855131387028723885214734474403727126666471507204742232932098231916521426529851682962621434754181609987057095325794008835521705283481212750184634047704384582696193719244058975230803600323739607208254021318075856365420943422167356338811699200000000
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
      144 108 48 242 145 49 13 8 19 72 54 354655531231553952257720701496319850260592692982760389807990997643780533567502902223573796613679072041232823271225158715442983210978402798076742266700211413658573218023966030010853480790508965053487385003630204988834402206029674493591939213130924008880143703159289265033530023841459972535706631754239414756353288753191874619231339679744151585177220012048724007876212661015417300691653219341179372699465671394794432707566249013008240358356004576197080102642516943843510702942539993219532761426697487438198465443691564175192520930730237676011425370629963487029755449296922832107477052931095478951469597361854102913278234724444666503250103500800000000
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
      144 108 48 242 145 49 13 8 19 72 54 2155223400039440188861764825317009338116304773160261427382044197058762047553624332287913490621918452643946771251528895267276985864152540388944061458784182840435666628708502028837611432776057077920335215119134097859680029397428853485204389097577185616904312342750464727759395454555524570640650092482632226412983447706554143189853589531647691529483819450468547052119469405143279719076008049859951975084597589185900689555792897916531865814060416512666206002593374570567326949712810962100587699146058135491085296817984785641481855101370906694707233111397344283163109826827438788555696966263065588627716724535221794592796138405107552977785276334080000000
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
      144 108 48 244 145 49 13 8 19 72 54 11818809861691254314341914586610171867853928322139588002243075431472399965988030343275547219153658532963363281557211987354767032532394860839734524168112737821873992770096564263976078403104708520377472656874394494185510478066947498876041694265105818827103270887241875702030233869203809228836649558814635710719728219683128499522980428444515066345135128089573961311280443777423252715539494620868410023872787925944051505784174605755980871455481424917983967324402534876087654702900106607697316367737469098672129361085665690988881168600947578028043883550596859285141468711068287451880324967784239994096770926151579939602370438239092760545265650237440000000
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
      144 108 48 243 145 49 13 8 19 72 54 9316342711946459263218406403453464895937442457515167276678695227845640462784800945328824243302613524021843326801562794880248556158418973340606946840425413242026374926489265935904432624366607628269856963376967091927611460012466932169111181331298693263656669046079720815192362430256564475305806425084529557621904546697605809530578145685248735842034566119660562099428895929523362110169377505577670976509327347930393977588455396010477817933753228628895026244282074047557927710217113905514581419061495846134692035865841020186471776109929781310214781781790236859476328964016259874489071746986422121362365665755305750088117129522770886014182568755200000000
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
      144 108 48 244 145 49 13 8 19 72 54 7246689876914769195053985320235298364580364601290268600069122544112561831649740850894560983748998793205162248288393667327377225008333536382102367432781770507675870463417994574765110622675251542222961301858427250352260566593025252185775540594811814481896204282855246250023340869357613709326452831020742193057715826784864743408213590585619763788554372441609920496690968296988169616915184849551600950699158318700488401932131275728530095903717384464322326951839122671005247783150247963411959315215453628138350863882004372517562913814077079111993132536433078793795358051174325593636024385517754730208281535398925688336701468304604085719932621291520000000
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
      144 108 48 243 145 49 13 8 19 72 54 7717796133583445230399001902607672447488637879762262184920732577029919922831565065743988893309738290071241783212787321102849297755686353431604694112262361906018511604052920697312799491243735187476100491952796640371873310466299177934483111140523971992861392740175758927046801236238155692759598901322265114207809226600762481706248862596521986882588708820426735444985979161217092034714555094988602695851838803299668181370571837890257252129961209038836230840978516384820101483957376046269722755257041718131539088339041461968412843968026194878202099825628068787878898753325424134542793039135450099961390569462866733666386189946735843672381257154560000000
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
      144 108 48 244 145 49 13 8 19 72 54 649882919989920320692077385095870028451793342271402955604677442605015520094996136291590728585423059188840208815239477974343795539715109164327486516558147743398502900590171072884779310427676885386606647811461572350285976725150833700032288867406574698484616148490975553362220186282388403245416999735430491366712301010822444825649928179224849909707135241943315552083586153194746819267926546990283102555387525203199572898438135174958697665539467989196565092968692824639250908659727789891348943325193417495704010931724047067665791330720337558009996244466175381929457009072288469545246771585089722915499467272266067324681402917212029101392527360000000
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
      144 108 48 244 145 49 13 8 19 72 54 1141421660551457869419059058708015924029167575505286600879348548184280385332999790157744938526254804038910218811716916124348883908610242431665687413428663670963538811690034249441873417938590535973305414096506589051466458968803655312997755085932051427073340007556178454676674952967486699501318630330374145922235907715821381430920882453412729562397643369876910269598753909260064834901797643592414624542539003534562278323990012196012410675479893003413883940476984089792278266335528298306788098337098206972123988229051140576281628939735537859412719976642378681786584234077753593406007567261246582448260064172672101224207468563704168273894440960000000
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
      144 108 48 244 145 49 13 8 19 72 54 31273345919712160714533287974812049300730027914755023758151880239340860068441888814543790258094515587219543836415773180556377984160490400450688228588798789598926723176709165481969303279438853771290005991461475845599902533306433683571747405124111027621007164317532467087363545471966689383002899058063964232688810820337736692413532745280663504227626424059854469824002213648494640111078359728620214125555296246355693047489327992183410366357063766291301418038722433804291632795594143308427882158231986796242037481896454212291357830290529773261585103358162580086203544055691801942909985199047016460698417534240417273060879247272605823115471093760000000
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
      144 108 48 240 145 49 13 8 19 72 54 581450256998209685391266797622858254560732807515886188927504911697258464470852701952456659678832046070079513178470738486472026309902537202426231996776192093665379770603284739371504366522454635313502222023101776447655591314956501294125366801181823269737104874835611661076207145309950195724747174789965024550615265650995854653705978638939002660283656425048462513706033837428701506886789982574373986568790046630180694086425242879469932421175789110869976624913803660430006683672426262603803416755792307048949371363494636398791657881002160272323589014346612194104051028317739496193781386326747257319197756716396824312059993867974270918716712550400000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
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
      144 108 48 244 145 49 13 8 19 72 54 65728736867197531790978333663097100652674846059077139041441146783224706004491763100325748100036933318473536006624163732517844837211082764434544371067623874328456897360811885832660961073677880688130917958891147747996444752628681661120998213214768521736609540469951733963928025281746195018329451336998560842444613786277200732518412466673589771595766183282811474277232017253713116693405336585547170795647023002851762836928432824174359889819283824812765832331498515579601896196754425603278392608211592393310609960633945401441152182311504914861285689423730911526307746350879486589520846335446459433588162923234925804886438196457182531470896314449920000000
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
      144 108 48 240 145 49 13 8 19 72 54 19176519788043507102836349276584508028312545789326910810963663022791962314399785119002451672790085055887339351787325616188701967308603468921412462790255497853818374306388979531680818571367551255274339263766195559359738294713476090512393083545004136927725342346099441262280035061033822587038052878595734021863046095918331913008213310516623618251303755870572847811972494653951740599751019046188825529822898061762819920647511650276870792799075912516057019570069657978789268202323132595027794775865001498860267782859025871108823591530380683127968869663773908239558814702687321248907749644542740075055473808815327274848161434161793233443140329799680000000
      (kronHM 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
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
      144 108 48 240 145 49 13 8 19 72 54 1776334066178290191047605168143159091303630205754074098808006490509864583891356983281715297900154090094257890812168435658196060403194492236080948371494636136019391305839023850269623831412819015733622500617349802371002377587288550280789859734077055780823833070979317472538056104510265667769592644302502610827523860857050283133995406442523929506411377354522343039480236267502685198289172023425195844576196601790585769634796926837774027211151394649629804581487678664928943584678080159140665634139602975444258514427522782413980150371834866936092045065882435034079039692589251548302989951134981647052741422595122614075028956170947717360120506613760000000
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
      144 108 48 241 145 49 13 8 19 72 54 719080989632516123336384650563965861008361917591102865042980749255617258165597106195963312281125789746280647057892323320709489557633861628689468527809656217500269812805934206139959290883988033375374355993737206800739114965380058892256009706419135930984865104196486540183497694263337077279808086766991860745077079505579950432120203904986729209291722399910341393416003609862924117111922379790609193123565415165688387832785413104923513397699568805553601453394201300024118051380194100675123410168252240831963345461629213094207803420645602737335690788589009975920793238312565149243079785131367268733316702082194735926627215091635052613975251353600000000
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
      144 108 48 241 145 49 13 8 19 72 54 2662288352639159503098660714192224621279401225103570249100321696155213604544527502215815682059036671326250257922411026574865636422246578986451131210553631095478419231581383943726107501767332425851344860220199946413379254860832661538926136110010089216151488969883029512232756097783389980232309322875540639570358726832451208041662252688220587832169664032289380507476502224393931284707487438243531908789583156341679371486801644163494412706209902966501313621762422649979810874061625212095765159484247093285660148704177307225962130445391882587934525284058861601091927405673099947979361832431108491657349068629377378171935731161510694227641840435200000000
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
      144 108 48 241 145 49 13 8 19 72 54 973026309505031631109997708807447442806664098295172804094497084882741611499254532335796775026011103691023805493133766492936170380379790974524013282078335322032518971270765681438110212806268524836761471477664557374945906593351757030632323398033699662349758786181386822422967190507470610095653665527606957170932258573529760125711908601557179526555658348953526375405227090188297820283135685050134488507935785249230317515119607940203526264933938309720702987315174122172348101688440907024535239863002743993511491540897557129204909595861936475669234975864905690795701048345488472850500288912905570008094912601573660332947503752774824374774613934080000000
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
      144 108 48 245 145 49 13 8 19 72 54 22787826887913343955064840512088509300821383050522460948234721086253297227119932689197500690440017390128159049980183709903112475652188823278079010430341336879398016341073604250630574659664558767188336427912819950368747185599926575709776529609846663994516177378144346336693931964200780582290178574242467036344356215155161775330073201921180619684596151529354309131590055616515607051240400567790439311429088929420862844889404709718080163870216767965643083205394010090934938679699174434187899411209093084475767784020805215472643322695498486492795149400913141427357369720399974777941524937658019603895166077667308972529973241596834000150726621265920000000
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
      144 108 48 244 145 49 13 8 19 72 54 4550062528411810558557607306448268054979876480155652036593793924325193345076823079353171836676721960755649770152648048722635877358011110984641045567890382997838976802378739073151199703433886173533399316120325536158166345725583179027506991637253297418969415599451948357527574450731405473077571864156323727947122903678943386758728150836991225630634479876108175765868578691052171394021944966050340323401914782301451296993665072816028124832526200595563620697001198535351096143874026477075019085413446730203894101754926513188533736308516659904326607870344265988233937507396759429455159821204130860184882331551364864469901173139743769283256291164160000000
      (kronHM 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHM_nZtF kHM_nZtF (by kernel_fact) (relHM_nZtF c))

end PlasmaLean.Design.RationalStellaratorGC
