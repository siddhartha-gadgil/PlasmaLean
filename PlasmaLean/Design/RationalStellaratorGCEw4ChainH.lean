/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCEw4RelH
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH1
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH2
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH3
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH4
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH5
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH6
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH7
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH8
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH9
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH10
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH11
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH12
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH13
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH14
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH15
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH16
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH17
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH18
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH19
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH20
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH21
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH22
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH23
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH24
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH25
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH26
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH27
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH28
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH29
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH30
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH31
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH32
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH33
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH34
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH35
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH36
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH37
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH38
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH39
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH40
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH41
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH42
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH43
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH44
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH45
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH46
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH47
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH48
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH49
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH50
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH51
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH52
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH53
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH54
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH55
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH56
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH57
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH58
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH59
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH60
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH61
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH62
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH63
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH64
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH65
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH66
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH67
public import PlasmaLean.Design.RationalStellaratorGCEw4CheckH68
public import PlasmaLean.Design.RationalStellaratorGCMuCommon
public import PlasmaLean.Design.RationalStellaratorGCEw4LowMemH
public import PlasmaLean.Certificates.KernelFact

/-!
# The high-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the high-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`, built
variable by variable (`ballHE4_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCEw4CheckH*` (`node3_fullN`), the node identities of
`Design/RationalStellaratorGCEw4RelH` and the node step `vstep`.
Generated by `scripts/gc_kam/ew_emit_lean.py`.

Energy-window node 4: gyro-length `ρ_4 = 1/256 + 2⁻³²`, its own family torus `K_4(λ)`; the
fields at `ρ_4` are the nodes `DtJ`, `nRtJ`, `nZtJ`.
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
theorem kderHE4_LRx : KvHE4 221 73 55 6 = famPack 221 73 55 NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 10888383889117653077957113864) ((c0HE4 4 : ℤ) * 158456325028528675187087900672) ddHE4 drHE4 0 (famHE4 4) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `LRx` is the symbol family of `U` (equal Kronecker images). -/
theorem PHE4_der_LRx : PHE4 6 = famPoly NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 10888383889117653077957113864) ((c0HE4 4 : ℤ) * 158456325028528675187087900672) 0 (famHE4 4) := by
  have hk : kron 221 73 (flat 55 (PHE4 6)) = kron 221 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 10888383889117653077957113864) ((c0HE4 4 : ℤ) * 158456325028528675187087900672) 0 (famHE4 4))) := by
    rw [kronHE4, ← famPack_eq 221 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 4)
      fun sd h => ((staticHE4 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_LRx
  have hbox := boxHE4 6
  rw [bx6HE4 6 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 6) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `LRx` is a derivative of the centre `U`. -/
theorem xHE4_der_LRx {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 6 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHE4 c 4) := by
  rw [xHE4_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHE4, PHE4_der_LRx,
    show WtHE4 6 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `LZx` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHE4_LZx : KvHE4 221 73 55 7 = famPack 221 73 55 NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 10888383889117653077957113864) ((c0HE4 5 : ℤ) * 158456325028528675187087900672) ddHE4 drHE4 0 (famHE4 5) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `LZx` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHE4_der_LZx : PHE4 7 = famPoly NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 10888383889117653077957113864) ((c0HE4 5 : ℤ) * 158456325028528675187087900672) 0 (famHE4 5) := by
  have hk : kron 221 73 (flat 55 (PHE4 7)) = kron 221 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 10888383889117653077957113864) ((c0HE4 5 : ℤ) * 158456325028528675187087900672) 0 (famHE4 5))) := by
    rw [kronHE4, ← famPack_eq 221 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 5)
      fun sd h => ((staticHE4 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_LZx
  have hbox := boxHE4 7
  rw [bx6HE4 7 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 221) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 7) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `LZx` is a derivative of the centre `Z`. -/
theorem xHE4_der_LZx {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 7 = dS ((10888383889117653077957113864 : ℤ) : ℂ) ((158456325028528675187087900672 : ℤ) : ℂ) (xHE4 c 5) := by
  rw [xHE4_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHE4, PHE4_der_LZx,
    show WtHE4 7 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thU` and the symbol family of `U` have the same
Kronecker image. -/
theorem kderHE4_thU : KvHE4 125 73 55 8 = famPack 125 73 55 NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 1) ((c0HE4 4 : ℤ) * 0) ddHE4 drHE4 0 (famHE4 4) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thU` is the symbol family of `U` (equal Kronecker images). -/
theorem PHE4_der_thU : PHE4 8 = famPoly NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 1) ((c0HE4 4 : ℤ) * 0) 0 (famHE4 4) := by
  have hk : kron 125 73 (flat 55 (PHE4 8)) = kron 125 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 4 then -1 else 1) 0
    ((c0HE4 4 : ℤ) * 1) ((c0HE4 4 : ℤ) * 0) 0 (famHE4 4))) := by
    rw [kronHE4, ← famPack_eq 125 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 4)
      fun sd h => ((staticHE4 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_thU
  have hbox := boxHE4 8
  rw [bx6HE4 8 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 8) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 4 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thU` is a derivative of the centre `U`. -/
theorem xHE4_der_thU {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 8 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 4) := by
  rw [xHE4_fam hc (i := 4) rfl (p := 0) rfl, dS_famCtr, xHE4, PHE4_der_thU,
    show WtHE4 8 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZ` and the symbol family of `Z` have the same
Kronecker image. -/
theorem kderHE4_thZ : KvHE4 125 73 55 9 = famPack 125 73 55 NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 1) ((c0HE4 5 : ℤ) * 0) ddHE4 drHE4 0 (famHE4 5) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thZ` is the symbol family of `Z` (equal Kronecker images). -/
theorem PHE4_der_thZ : PHE4 9 = famPoly NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 1) ((c0HE4 5 : ℤ) * 0) 0 (famHE4 5) := by
  have hk : kron 125 73 (flat 55 (PHE4 9)) = kron 125 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 5 then -1 else 1) 0
    ((c0HE4 5 : ℤ) * 1) ((c0HE4 5 : ℤ) * 0) 0 (famHE4 5))) := by
    rw [kronHE4, ← famPack_eq 125 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 5)
      fun sd h => ((staticHE4 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_thZ
  have hbox := boxHE4 9
  rw [bx6HE4 9 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 9) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 5 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thZ` is a derivative of the centre `Z`. -/
theorem xHE4_der_thZ {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 9 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 5) := by
  rw [xHE4_fam hc (i := 5) rfl (p := 1) rfl, dS_famCtr, xHE4, PHE4_der_thZ,
    show WtHE4 9 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thUe` and the symbol family of `Ue` have the same
Kronecker image. -/
theorem kderHE4_thUe : KvHE4 125 73 55 12 = famPack 125 73 55 NHE4 MHE4 DHE4 (if oddHE4 10 then -1 else 1) 0
    ((c0HE4 10 : ℤ) * 1) ((c0HE4 10 : ℤ) * 0) ddHE4 drHE4 0 (famHE4 10) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thUe` is the symbol family of `Ue` (equal Kronecker images). -/
theorem PHE4_der_thUe : PHE4 12 = famPoly NHE4 MHE4 DHE4 (if oddHE4 10 then -1 else 1) 0
    ((c0HE4 10 : ℤ) * 1) ((c0HE4 10 : ℤ) * 0) 0 (famHE4 10) := by
  have hk : kron 125 73 (flat 55 (PHE4 12)) = kron 125 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 10 then -1 else 1) 0
    ((c0HE4 10 : ℤ) * 1) ((c0HE4 10 : ℤ) * 0) 0 (famHE4 10))) := by
    rw [kronHE4, ← famPack_eq 125 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 10)
      fun sd h => ((staticHE4 10 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_thUe
  have hbox := boxHE4 12
  rw [bx6HE4 12 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 12) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 10 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thUe` is a derivative of the centre `Ue`. -/
theorem xHE4_der_thUe {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 12 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 10) := by
  rw [xHE4_fam hc (i := 10) rfl (p := 0) rfl, dS_famCtr, xHE4, PHE4_der_thUe,
    show WtHE4 12 = (1, 0, (0 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `thZe` and the symbol family of `Ze` have the same
Kronecker image. -/
theorem kderHE4_thZe : KvHE4 125 73 55 13 = famPack 125 73 55 NHE4 MHE4 DHE4 (if oddHE4 11 then -1 else 1) 0
    ((c0HE4 11 : ℤ) * 1) ((c0HE4 11 : ℤ) * 0) ddHE4 drHE4 0 (famHE4 11) := by
  kernel_fact

set_option maxRecDepth 100000 in
/-- The stored derivative `thZe` is the symbol family of `Ze` (equal Kronecker images). -/
theorem PHE4_der_thZe : PHE4 13 = famPoly NHE4 MHE4 DHE4 (if oddHE4 11 then -1 else 1) 0
    ((c0HE4 11 : ℤ) * 1) ((c0HE4 11 : ℤ) * 0) 0 (famHE4 11) := by
  have hk : kron 125 73 (flat 55 (PHE4 13)) = kron 125 73 (flat 55 (famPoly NHE4 MHE4 DHE4 (if oddHE4 11 then -1 else 1) 0
    ((c0HE4 11 : ℤ) * 1) ((c0HE4 11 : ℤ) * 0) 0 (famHE4 11))) := by
    rw [kronHE4, ← famPack_eq 125 73 55 NHE4 MHE4 DHE4 _ _ _ _ 0 (famHE4 11)
      fun sd h => ((staticHE4 11 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1]
    exact kderHE4_thZe
  have hbox := boxHE4 13
  rw [bx6HE4 13 (by kernel_fact) (by kernel_fact)] at hbox
  refine eq_of_kron_flat (b := 125) (W := 73) (R := 55) (d := 17) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by kernel_fact)) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1HE4 55 13) (l1_flat_famPoly_le 55 NHE4 MHE4 DHE4
    (by kernel_fact) _ _ _ 0 _
    fun sd h => ((staticHE4 11 (by kernel_fact) (by kernel_fact)).2.2.2 sd h).1.2.2.2.2))
    (by kernel_fact)

/-- The centre `thZe` is a derivative of the centre `Ze`. -/
theorem xHE4_der_thZe {c : ℂ} (hc : c ≠ 0) :
    xHE4 c 13 = dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 11) := by
  rw [xHE4_fam hc (i := 11) rfl (p := 1) rfl, dS_famCtr, xHE4, PHE4_der_thZe,
    show WtHE4 13 = (1, 0, (1 + 3) % 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by kernel_fact)

/-- The embedded low-resolution family centre `Ue`. -/
theorem xHE4_embed_Ue {c : ℂ} (hc : c ≠ 0) : xHE4 c 10 = xLM c 4 := by
  rw [xHE4_fam hc (i := 10) rfl (p := 0) rfl, xLM_fam hc (i := 4) rfl (p := 0) rfl]
  exact famCtr_embed SLM NLM MLM 0 (NHE4 - NLM) (MHE4 - MLM) (SHE4 - SLM) _ c 0 (famLM 4)
    (by kernel_fact)

/-- The embedded low-resolution family centre `Ze`. -/
theorem xHE4_embed_Ze {c : ℂ} (hc : c ≠ 0) : xHE4 c 11 = xLM c 5 := by
  rw [xHE4_fam hc (i := 11) rfl (p := 1) rfl, xLM_fam hc (i := 5) rfl (p := 1) rfl]
  exact famCtr_embed SLM NLM MLM 1 (NHE4 - NLM) (MHE4 - MLM) (SHE4 - SLM) _ c 0 (famLM 5)
    (by kernel_fact)

set_option linter.unusedVariables false in
/-- The variable `t` is exact. -/
theorem XHE4_eq_t {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 0 = xHE4 c 0 := by
  rw [xHE4_t (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `V` is exact. -/
theorem XHE4_eq_V {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 1 = xHE4 c 1 := by
  rw [xHE4_V]; rfl

set_option linter.unusedVariables false in
/-- The variable `c` is exact. -/
theorem XHE4_eq_c {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 2 = xHE4 c 2 := by
  rw [xHE4_c, ctr_cPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `s` is exact. -/
theorem XHE4_eq_s {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 3 = xHE4 c 3 := by
  rw [xHE4_s, ctr_sPoly]; rfl

set_option linter.unusedVariables false in
/-- The variable `U` is exact. -/
theorem XHE4_eq_U {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 4 = xHE4 c 4 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Z` is exact. -/
theorem XHE4_eq_Z {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 5 = xHE4 c 5 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `thU` is exact. -/
theorem XHE4_eq_thU {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 8 = xHE4 c 8 := by
  rw [XHE4_spec c (i := 8) rfl, xHE4_der_thU (ne_zero_of_norm_one_mu hc)]
  simp [XHE4spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZ` is exact. -/
theorem XHE4_eq_thZ {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 9 = xHE4 c 9 := by
  rw [XHE4_spec c (i := 9) rfl, xHE4_der_thZ (ne_zero_of_norm_one_mu hc)]
  simp [XHE4spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `Ue` is exact. -/
theorem XHE4_eq_Ue {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 10 = xHE4 c 10 := by
  rw [XHE4_spec c (i := 10) rfl, xHE4_embed_Ue (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `Ze` is exact. -/
theorem XHE4_eq_Ze {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 11 = xHE4 c 11 := by
  rw [XHE4_spec c (i := 11) rfl, xHE4_embed_Ze (ne_zero_of_norm_one_mu hc)]; rfl

set_option linter.unusedVariables false in
/-- The variable `thUe` is exact. -/
theorem XHE4_eq_thUe {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 12 = xHE4 c 12 := by
  rw [XHE4_spec c (i := 12) rfl, xHE4_der_thUe (ne_zero_of_norm_one_mu hc), xHE4_embed_Ue (ne_zero_of_norm_one_mu hc)]
  simp [XHE4spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `thZe` is exact. -/
theorem XHE4_eq_thZe {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 13 = xHE4 c 13 := by
  rw [XHE4_spec c (i := 13) rfl, xHE4_der_thZe (ne_zero_of_norm_one_mu hc), xHE4_embed_Ze (ne_zero_of_norm_one_mu hc)]
  simp [XHE4spec, dTh]

set_option linter.unusedVariables false in
/-- The variable `V0` is exact. -/
theorem XHE4_eq_V0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 52 = xHE4 c 52 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `Dt0` is exact. -/
theorem XHE4_eq_Dt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 68 = xHE4 c 68 := by
  rw [xHE4_zero c (i := 68) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nRt0` is exact. -/
theorem XHE4_eq_nRt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 69 = xHE4 c 69 := by
  rw [xHE4_zero c (i := 69) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `nZt0` is exact. -/
theorem XHE4_eq_nZt0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 70 = xHE4 c 70 := by
  rw [xHE4_zero c (i := 70) rfl]; rfl

set_option linter.unusedVariables false in
/-- The variable `r` is exact. -/
theorem XHE4_eq_r {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 71 = xHE4 c 71 := by
  rw [XHE4_rel c (i := 71) rfl]
  change XLM c (xHE4 c 4) (xHE4 c 5) 114 = _
  rw [XLM_new c _ _ (j := 114) rfl]
  change algebraMap ℂ FA (((63 + 32 * lamF c : ℝ)) : ℂ) = _
  rw [xHE4_r (ne_zero_of_norm_one_mu hc), param_eq_mu hc]

set_option linter.unusedVariables false in
/-- The variable `V40` is exact. -/
theorem XHE4_eq_V40 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 79 = xHE4 c 79 := by
  rfl

set_option linter.unusedVariables false in
/-- The variable `N0` is exact. -/
theorem XHE4_eq_N0 {c : ℂ} (hc : ‖c‖ = 1) :
    XHE4 c 86 = xHE4 c 86 := by
  rfl

set_option maxHeartbeats 400000 in
-- 184 `kernel_fact` side conditions, each a small proof term to elaborate
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- **Norms of the centres.** -/
theorem normHE4 {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 99 → Bd r (xHE4 c i) (BHE4 i)
  | 0, _ => by rw [xHE4_t (ne_zero_of_norm_one_mu hc)]; exact (Bd_one r).le (by norm_num [BHE4, BHE4l])
  | 1, _ => by rw [xHE4_V]; exact (Bd_one r).le (by norm_num [BHE4, BHE4l])
  | 2, _ => by rw [xHE4_c, ctr_cPoly]; exact (Bd_cS_q hq).le (by norm_num [BHE4, BHE4l])
  | 3, _ => by rw [xHE4_s, ctr_sPoly]; exact (Bd_sS_q hq).le (by norm_num [BHE4, BHE4l])
  | 4, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 4 0 119 73 25 11 1 73 36 27
      85868364264719552200618514652470507997826174736940528931829596676050375423010015532841958433558038728298728127706845461316479871646634162426786368847326377121251656517147806352261530170707205129760955127132047841125626909228434750368872302707146417062159979795961481007895685304387344194422743007456986217262462289925665436779172331520 (BHE4 4) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_U cHE4_U (by kernel_fact)
  | 5, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 5 1 119 73 25 11 1 73 36 27
      72209707223930360184110139937769547493645124971436690659895924633115288122201652697814603084667576695940922267895432029707348495811192677122808421214337779332234045752084761338159836642893271407307103544952462471731389907967085148313888175251967726065311417518044814580943958534240495359667992023702516446281017967638026060156675031040 (BHE4 5) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_Z cHE4_Z (by kernel_fact)
  | 6, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 6 3 221 73 25 11 1 73 36 27
      3855256216568686421032289429904844673938210091405237010639967688744887821054178304967781179878493304017591409416294125146074601486094256485732586953693033682613115065853141858850847930408962199129818989954739703027847231978669367789070490761622551783801169514934293063968230903346045705832962734613857381766477932154933508070372530782630591329438445522486852321280 (BHE4 6) (kronHE4 221 73 55) rfl (by kernel_fact) clHE4_LRx cHE4_LRx (by kernel_fact)
  | 7, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 7 0 221 73 25 11 1 73 36 27
      3655661184691556595109980997486854515486538527092847555135376816605142781288992105269611665119137488892424942941522187711322476638308891199937862215206118378394330352397239613692374752450607057860880833812579963101621998246281652229913205399445118521282650115807344791328386958785624333002624013771682216284504136833460129507549903300914451552745990506963617710080 (BHE4 7) (kronHE4 221 73 55) rfl (by kernel_fact) clHE4_LZx cHE4_LZx (by kernel_fact)
  | 8, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 8 3 125 73 25 11 1 73 36 27
      72727999879760574088768843149966350664915368000476965151741608884666569820993874931120061196772238948658930337410869171719559872407238318225975990344992183063346342522894363541492212658139732724436833922028865036522300917633143874158874874072321693777351361527781373237296460009218795235683348808184160021208157437219245622493624401920 (BHE4 8) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_thU cHE4_thU (by kernel_fact)
  | 9, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 9 0 125 73 25 11 1 73 36 27
      71928717022903368730408592956585296546946426804530662562070157822624118713111438962561095704705904378665349855995471604822266866118683201025585388575705573305782047833279262068504555663169153625483583011099703142967076089795003166420596542690347831107177990282005545748552128667988632352871236256101263582517060366202602399897485312000 (BHE4 9) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_thZ cHE4_thZ (by kernel_fact)
  | 10, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 10 0 119 73 25 11 8 10 36 27
      127851892760837724279445547993531155933966158517778688691437555192970059617708139673364712271013175352062085908847818465626513013879417831113051489752313227048297978941561537174552325389892027276649521583864559441751640071163086964626807533984980423021293487351997124183550557436499438510440831293989808899438662653057576820382105600000 (BHE4 10) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_Ue cHE4_Ue (by kernel_fact)
  | 11, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 11 1 119 73 25 11 8 10 36 27
      105418199702671940687587185900788720098161834334999805375289230993403724820309205906660895678677713088485654508690223786103484497935275556223281171961484838763104139598079804303796229103419807096146591202091609902464530056436849945131216286393188296769443395383593532704695932486921421000440168198260720798658834052580974126075740160000 (BHE4 11) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_Ze cHE4_Ze (by kernel_fact)
  | 12, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 12 3 125 73 25 11 8 10 36 27
      105061925581715585637867725836733851934764247322786501268704853420075859413845047658684870262427858377799061962600518822973491286413812958687050190107102563504240947443804445671848068240837614223931504532168351428281009275196873579279959081215351769652061380490355280561253320335762364145585079324282000793341744399149202598264832000000 (BHE4 12) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_thUe cHE4_thUe (by kernel_fact)
  | 13, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 13 0 125 73 25 11 8 10 36 27
      103991936885312502901650488240118186811772515815930252385444932917497140650424973542225328391457849572113936595604722220815190145894224655394095981800653933291694831781578563299569413487489596082207170531903868844746409994524263095447510266924786837887548725821888837966310513936055153855233358548549048376737047825243700732603924480000 (BHE4 13) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_thZe cHE4_thZe (by kernel_fact)
  | 14, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 14 2 115 73 25 11 8 10 36 27
      14124924772857554265042971402560308724477972396197840127845524086523444584499918630319197113062799259114103243961744565693608107955357672760653003692852271620984305431130434479247160267297593556412455330355148818831194426889336739689203942609461759446677539543130687221747750474708659737869581276029988618962742063665072964800348160000 (BHE4 14) (kronHE4 115 73 55) rfl (by kernel_fact) clHE4_m02 cHE4_m02 (by kernel_fact)
  | 15, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 15 1 115 73 25 11 8 10 36 27
      10412665422150572598144202412359472536361316209175916112611086066219549429760438087474709214263655506893408682658193447082682204251672620967018757756373993840470873052791595251870348717212896223038687689857236971096534690241330072002740254704331318694073004951268169115776498695141787911929597675120905542028784340927071915710873600000 (BHE4 15) (kronHE4 115 73 55) rfl (by kernel_fact) clHE4_m11 cHE4_m11 (by kernel_fact)
  | 16, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 16 0 115 73 25 11 8 10 36 27
      20629243644204448079592237270799075555495426704377375212734390878113698046319485580519775060885284972497348717119043324606211673005156311243875018087583982994998739065591238268974325069672392488446527817738083419223519016677494669706823228722041574366838811497594398665997674314690264674521786873730211510331877721017371655751598080000 (BHE4 16) (kronHE4 115 73 55) rfl (by kernel_fact) clHE4_m20 cHE4_m20 (by kernel_fact)
  | 17, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 17 3 112 73 25 11 8 10 36 27
      1887994155731738616431696020719958979109120852740498386724838509398327560910479900711847388938824918171600286294303325953496691258607381801888160759698595218143593881858395010641052607438170682884431028653031538041327450621800845131769840964557955899147416379894090156478599688908501135158545197949004150262541809179773101093683200000 (BHE4 17) (kronHE4 112 73 55) rfl (by kernel_fact) clHE4_m03 cHE4_m03 (by kernel_fact)
  | 18, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 18 2 111 73 25 11 8 10 36 27
      1332961515286915006661889423822019783452943423376030617135561080705975697731392266127717431917026677126561167874009738377920529127729247486361111409111864292534546173704903360273095372491024356855741314101846868425408258141216859896755805969194334826481766211067311279582738956428567958170091481353957656891353143532206098250465280000 (BHE4 18) (kronHE4 111 73 55) rfl (by kernel_fact) clHE4_m12 cHE4_m12 (by kernel_fact)
  | 19, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 19 1 111 73 25 11 8 10 36 27
      1503227960184507111276803654047552042284975584665581118048634910023639032020942268041366312746404413734195040920497099872616835410086270346173768073052886880156875248798122602335055155002890293552936422949161358446427978757733372060969474865561758008089128918499031730977152342069168007525433343113172499876623467439158295999283200000 (BHE4 19) (kronHE4 111 73 55) rfl (by kernel_fact) clHE4_m21 cHE4_m21 (by kernel_fact)
  | 20, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 20 0 113 73 25 11 8 10 36 27
      3300730116695014277542908458284586413533571512925461596453320646747219467892461961959923410248211163940209309417111460046872127556697553510561165333968497127211444388249340761408905883169167774948569094324745024405297988452989382457384222719535577273324944250908423697120891008503535289093224472963793865338874048950750444005621760000 (BHE4 20) (kronHE4 113 73 55) rfl (by kernel_fact) clHE4_m30 cHE4_m30 (by kernel_fact)
  | 21, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 21 3 108 73 25 11 8 10 36 27
      154519500195742803474192020082637042233287471417820206380012790528568513990846501844256436431965746208440285976035306220359836474054591984883219269838386854521275956700951231352614651099875864728406740405415579536405333915597731528167610876698206769614378782987791825413519001714006201080518993652473636199346894427806564498800640000 (BHE4 21) (kronHE4 108 73 55) rfl (by kernel_fact) clHE4_m13 cHE4_m13 (by kernel_fact)
  | 22, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 22 2 107 73 25 11 8 10 36 27
      142975003764713778443666386169551704415015963548871334121558112459544723053629617150233717886881651859665733134944235220752143583237818170103324750111617294074457618090949837344315946231882783417188571722806849128185473353270142233693681830878872113743920579376897294911661032099684075968183891731187468089697671088980801450147840000 (BHE4 22) (kronHE4 107 73 55) rfl (by kernel_fact) clHE4_m22 cHE4_m22 (by kernel_fact)
  | 23, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 23 1 108 73 25 11 8 10 36 27
      217613314334691229439520086224997928847548583526926808277750980665260975959291375249344809914738420798510901860922429093355019287725019473605187892407831191733338564603448709412802636042912298128886878031688215991584590585347784796584654705500285103603141418362125585261961863763821945184935539380185739358002375880693252934860800000 (BHE4 23) (kronHE4 108 73 55) rfl (by kernel_fact) clHE4_m31 cHE4_m31 (by kernel_fact)
  | 24, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 24 0 109 73 25 11 8 10 36 27
      548492858504706879046849556303207410147446836509978100011143552031242554521683768905297909335494113623310613241762428350219604912112408463996423185537102434173297726258142013236563793112379858613212869324183988567300122471860945655904644997863084825513701057873734873980897217718998662752698098680023999641119502566600684423086080000 (BHE4 24) (kronHE4 109 73 55) rfl (by kernel_fact) clHE4_m40 cHE4_m40 (by kernel_fact)
  | 25, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 25 1 105 73 25 11 8 10 36 27
      33104566793737305420554251737924822938776054687282224586819314203769810180893121576430822123871864219705337541560442445440189233562354698633710431557835160917687241300178388621773851043741670591091493074058387960748158389760068726434585934560071441420107316402892796373743292348394224683762246283941394912130576681583437445857280000 (BHE4 25) (kronHE4 105 73 55) rfl (by kernel_fact) clHE4_m41 cHE4_m41 (by kernel_fact)
  | 26, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 26 0 107 73 25 11 8 10 36 27
      90153989970983314068456780819520065243405909031527958549433887558461781390425999205237051778088647475317572966432182583976026463517913526955045251087881098452161905011256400452748301655719712513415641167218373154212591020776160246746717316946962644233905714934968259479340315864782332425342101861843768381873108479255943640514560000 (BHE4 26) (kronHE4 107 73 55) rfl (by kernel_fact) clHE4_m50 cHE4_m50 (by kernel_fact)
  | 27, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 27 1 102 73 25 11 8 10 36 27
      5078316898553388000387283942983382847428382790395585656485981141394623042729130084789798772657551804255889042474550327389402324090436033804679335155579333518194099545302269881936360307679649005221684877167848767511245420148220337105403076580676754112244974386590880153325304621633138164752100158180773872779595179949232247275520000 (BHE4 27) (kronHE4 102 73 55) rfl (by kernel_fact) clHE4_m51 cHE4_m51 (by kernel_fact)
  | 28, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 28 0 104 73 25 11 8 10 36 27
      14879592577611699882493345658755815590375434823907133883569617629098105410423888931764787216672873998504454087657953709110549504636354868724139230581279531388881773975322904911712457551825868496372305728170581725722067172155855380174369813558917493733650151207745078964211751147547749604129520789972544225036290680694611671777280000 (BHE4 28) (kronHE4 104 73 55) rfl (by kernel_fact) clHE4_m60 cHE4_m60 (by kernel_fact)
  | 29, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 29 0 122 73 25 11 8 10 36 27
      908498500536558187896564878236636643486132436022461971302369916093485383798668162299303074844613913479362517752600651546465375770073268665816852769388664162861230189190956706536346722668686777167718528247084830790329548805404298713156828142862168259934005892735097901282585936797319914694135608829242243130478922181304782525866967040000 (BHE4 29) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_Dp cHE4_Dp (by kernel_fact)
  | 30, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 30 3 118 73 25 11 8 10 36 27
      64496777394049522945319431958431673628118061957138261441358939495220691592345194361332971506026765107728686963423573307469231828924680279633649134233923610754110936688294504146617308887914315477264380338753611464091263434318629111067280037956230222934756049208236486661439547165032055048758100260480245651527176304927117415169392640000 (BHE4 30) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nRp cHE4_nRp (by kernel_fact)
  | 31, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 31 0 118 73 25 11 8 10 36 27
      64320071183208444174801620886663676411921854048712891130566875291958641635658707096282508056780187781542491101185682674929620134845016101654368884944488661470273435428829743725623583445524805822085715947876917150975322048228022567499839095753194290607191658128092485843648506306837088804089632331654886512518407701656496267098849280000 (BHE4 31) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nZp cHE4_nZp (by kernel_fact)
  | 32, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 32 0 123 73 25 11 8 10 36 27
      1620055205988613376574943040607305540922854599873255724725286702956565936483928068497418478736022225098686153443929916206705990291248408591248104386748420520578463538723663346327090060294832114563831810924870941791736141725626196325132075670660363042907585409361949045329351336451420796014441127064519645719435589271331070369270333440000 (BHE4 32) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_DuP cHE4_DuP (by kernel_fact)
  | 33, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 33 3 119 73 25 11 8 10 36 27
      133977453316878754456846468463040357412294552417031075692355954723752073544667714379854643638587322230485541476071706822643950563340329967110214014005116063217135278721621331095693385845857217834837985957176267371307731801708571284095470482965391922275225849288656952288647165131793532636271344100235806706306906813784841543598735360000 (BHE4 33) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_DzP cHE4_DzP (by kernel_fact)
  | 34, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 34 1 116 73 25 11 8 10 36 27
      13984929666841412936195713177041587020287217364027903959740537090164049444180095155174230093165679222431634750022380767572373101412001773417201919019457477379264508788722860569576206582931993219555523184932163989601551014391245534472741129642899118998796902877017684479418746499136000625210137549889689187258464201033453002429562880000 (BHE4 34) (kronHE4 116 73 55) rfl (by kernel_fact) clHE4_DphP cHE4_DphP (by kernel_fact)
  | 35, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 35 3 121 73 25 11 8 10 36 27
      650554752700319772710936544503784184167238887265686472907139663377669483107583480065945274114840085660788432325131035045684438783604351486448630459568556290058733678964862300110648318245574266532824991724450900616430412778332571733906095996143622156185140904656527810907749673480091670017627581880813054144581579137488227248468131840000 (BHE4 35) (kronHE4 121 73 55) rfl (by kernel_fact) clHE4_nRuP cHE4_nRuP (by kernel_fact)
  | 36, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 36 0 121 73 25 11 8 10 36 27
      524789673689133872189630890507129824243848921407964821330454350322061754184930635377323869209759593190290343837198177150713318247543812605467763254978141044427166295709200360953793866713288313938018564553904517598088550451146772480944793385502038776990414731133897696997126985753352960603615284494652710596989221661088601357051494400000 (BHE4 36) (kronHE4 121 73 55) rfl (by kernel_fact) clHE4_nRzP cHE4_nRzP (by kernel_fact)
  | 37, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 37 0 119 73 25 11 8 10 36 27
      130656055714132329197230495672247691881791293063536055032453576338293391749785988518087287677251246469344052628323891185330347106909536568531637905487511097650040078425513914127980980404801046765329046575252380581888520118764573525750632571420152226279451785319421972206983650178783465931897286308644147313368371578782746333245603840000 (BHE4 37) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_nRphP cHE4_nRphP (by kernel_fact)
  | 38, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 38 0 121 73 25 11 8 10 36 27
      604384819537336782555337702865061055928528314968280950420272077922064420212437220366892207500261916341189264406323667460841100859910000155141425572071912648984224671591236897754584083783645113305676637325546791796849069263413779034401896516282598143177141178136147604559621746474465738008094792230273053006952814508983262121159557120000 (BHE4 38) (kronHE4 121 73 55) rfl (by kernel_fact) clHE4_nZuP cHE4_nZuP (by kernel_fact)
  | 39, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 39 1 121 73 25 11 8 10 36 27
      571080413180429958031912228985874509086800138994457891568092126554648936030604662713666609718138061895522267903822116845037217360815641043954022673933775513458217524102977838071260703776684140915146321667598699310993706939241921805116336780692517139254533084536592446458323579592885760120958517138983951748287831067115015059821035520000 (BHE4 39) (kronHE4 121 73 55) rfl (by kernel_fact) clHE4_nZzP cHE4_nZzP (by kernel_fact)
  | 40, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 40 3 119 73 25 11 8 10 36 27
      129323664296152893418824784917924954783855919342410625406182517419717136232142223607181373515560423648887590450936941074915564361803721046892403072887832611839821990433770568848021458475594774790285756253338771163590309969198339481482347133882624969771009267651823805904076900875374196372592652573862235063302747877217496959916441600000 (BHE4 40) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_nZphP cHE4_nZphP (by kernel_fact)
  | 41, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 41 0 123 73 25 11 8 10 36 27
      1266582207118296720027564094285810141244483949689637866936807800409129042392927577572072724050081067685074087801129616180589660484815777658219294915055005961800839440127922631527136509933484653781127667085663239753898481281980340292586441330111608732788476851764411237099360128386758087425849932531660798402716752195662562938469744640000 (BHE4 41) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_PuP cHE4_PuP (by kernel_fact)
  | 42, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 42 0 122 73 25 11 8 10 36 27
      988473885420499725949226103472396565219179268453693834178115541855416288314390421450574897413730692767984211130292208816675271863330151969300198185056223204039397085748044104992332987352244991384569323044926793943110850508686845805720278281013527026233028387462197891174943710761906639006977163129216542310306885967939070449544069120000 (BHE4 42) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_RD cHE4_RD (by kernel_fact)
  | 43, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 43 0 123 73 25 11 8 10 36 27
      1699920355878755751015648356394263288378957975850063376632514693637052961726197784263281500083959389991536293739467889992885796735772582789631910271144272347739572330077432338639402516269161065211853584521414627712078813450808896046801108467756272813107448105683816741812241319198795673743698142094847806819845953946569026763227136000000 (BHE4 43) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_RDu cHE4_RDu (by kernel_fact)
  | 44, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 44 3 119 73 25 11 8 10 36 27
      130215060304970752548992724613412798756703387022221154119660956730443383346125603154674650968277596124076693228076278613926166860262816653284618532106593039306454214016716860605324545846030265537113755716447193644587352530874225683324008612016281231354396789269814353095721623933946669273511303640031874040840063791072115331159818240000 (BHE4 44) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_RDz cHE4_RDz (by kernel_fact)
  | 45, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 45 1 116 73 25 11 8 10 36 27
      13432387147981716876767928925023246864245271345757500294645261720378702208176799576072265889349128205259397187931554529321540315357348507729158810389918478996810427012809520588422771585312774016544963698225383797300664227953961284989328661363738159365686153777644620847948567294025627228694236650160734450997922052769908651437588480000 (BHE4 45) (kronHE4 116 73 55) rfl (by kernel_fact) clHE4_RDph cHE4_RDph (by kernel_fact)
  | 46, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 46 2 122 73 25 11 8 10 36 27
      1284085246203108556383023401646177414375178484652032522181096476270031723590472221058759585561218742924622918550855684656820905609997326600768497091116016791458142228848155573745538344508073502523765432402436613840159865338432452607136834189709546912211576659493335788316337565830623427354160748318219064094841963278298128809784770560000 (BHE4 46) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_q cHE4_q (by kernel_fact)
  | 47, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 47 0 125 73 25 11 8 10 36 27
      6835548158328838998588504740855705848870291236591465406493449895595291730081284032096934975083221393794494729043128811273434577699849967842742827004710381342934870614642973687768305650196185453172004255625308404035192313280267773774653502959065595510129933927313761943660612822750235706494136926467669146989282926661301742735751905280000 (BHE4 47) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_qR cHE4_qR (by kernel_fact)
  | 48, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 48 3 120 73 25 11 8 10 36 27
      215984416737307449607112941496358870263676039873056386480408497813613198210955883093676678649856220492003169933502515793176665138609854787710571212753731548000127417675540440104516687613394807670302158335460424005911375950102611707094428162111951065655161177321661559043227841988166029762752263807527297863687586450460241225433743360000 (BHE4 48) (kronHE4 120 73 55) rfl (by kernel_fact) clHE4_qz cHE4_qz (by kernel_fact)
  | 49, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 49 3 116 73 25 11 8 10 36 27
      28584061878926084794995699635534488002461263907165150653962227247184769144814112365244835509259772494503312450237456040023068172569597704531025169086576236443521196563818468977512972770885447653508001180971209426947284555829415329471519416177095728023840159063010475772884125554029192966644653009157473487312208585782397312193003520000 (BHE4 49) (kronHE4 116 73 55) rfl (by kernel_fact) clHE4_qph cHE4_qph (by kernel_fact)
  | 50, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 50 0 123 73 25 11 8 10 36 27
      2168885176035780394970122346227880425620463509241330594263745504907227219670220028191496866195916759895340161280863449866040362992172371164381038877047241476219627203531189346675453124649038328713652370500086362480306947704037095787657189459444899357167998450510709421368032826515102878908251098298493997582870967982739317365753774080000 (BHE4 50) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_P2 cHE4_P2 (by kernel_fact)
  | 51, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 51 2 116 73 25 11 8 10 36 27
      22191293334170583672917993630519363820418099630600336211754492284281352139286899644147703910542153636450343166011549425139872732927499787087036556548102349340529719878055570812814890880276171156590359351166794212421482437781623463000697883173862452071876501293345181393792487179141805342017008612257041530370392713888061577263841280000 (BHE4 51) (kronHE4 116 73 55) rfl (by kernel_fact) clHE4_E cHE4_E (by kernel_fact)
  | 52, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 52 0 123 73 25 11 8 10 36 27
      747266190654142705551579384568015804611038887191784781034490564740319380967884658410757691261538580972424386773285849750915891725474705085551771924212222287085669588024526326979703129314669740437214898249285664820085957758971479047674865026940043838736215924274539782279413047432667129122933435820652845512560638129816137014475489280000 (BHE4 52) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_V0 cHE4_V0 (by kernel_fact)
  | 53, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 53 0 123 73 25 11 8 10 36 27
      758782824144208145981889245269684564817613594700077754977314470140366515881684133590038019401747575558646385328047218717828720500164491952039960340877614444286758659840780084922581656699637454823703231920633279202552250388453514463316952126306632230650515233548243903533908807713195170113498098379005491777690419817324512672072335360000 (BHE4 53) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_V2 cHE4_V2 (by kernel_fact)
  | 54, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 54 0 123 73 25 11 8 10 36 27
      747266190654142705551579384568015804611038887191784781034490564740319380967884658410757691261538580972424386773285849750915891725474705085551771924212222287085669588024526326979703129314669740437214898249285664820085957758971479047674865026940043838736215924274539782279413047432667129122933435820652845512560638129816137014475489280000 (BHE4 54) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_Vn cHE4_Vn (by kernel_fact)
  | 55, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 55 0 123 73 25 11 8 10 36 27
      1285602815333969585046557847894403435189491226224995754794404770854021720365133608483543201708235786046234004729748451317697156231537744782332811311484688273635629007168640543585054550110005602530469756123554018874317629195973030207569324523908717055136169671684389065832195450112898580855636289750849393182866710055884653312480378880000 (BHE4 55) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_W cHE4_W (by kernel_fact)
  | 56, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 56 0 123 73 25 11 8 10 36 27
      2233869450948236495507972494624179162830762937596419413019190279287185147151492858068585280044873639143549009955831060584312484499552600074996572208362360662503207217438097512349440116916781226292586894638405347156560562777191461428787343687811133564891537086648860925585119000445248838625885990861539429014061447590365239338679312687500 (BHE4 56) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_W2 cHE4_W2 (by kernel_fact)
  | 57, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 57 0 123 73 25 11 8 10 36 27
      3861225971609835856918355316548434493383105135004959035226744004096017125205504820067981184026602549075301073259048588099956946210054995736538514254749815127926615107266104731037115429214068801073135521454790035502294860164729574332251149036704953520015572689433010306926869085684634246072429790494960676230668445111543594494011248641250 (BHE4 57) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_W3 cHE4_W3 (by kernel_fact)
  | 58, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 58 0 122 73 25 11 8 10 36 27
      902724487360815305036290808744948944090769482364446718611521426719313103960458857901596572519165197872118731338509900607128379586533005284567764954233886188976788976945244344763510232648823061305370631136900148053821801646793506437111007820340346029533499442109277304053853848623580961117430323365314119561472853044921674140777185280000 (BHE4 58) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_R2 cHE4_R2 (by kernel_fact)
  | 59, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 59 0 122 73 25 11 8 10 36 27
      990255056812998699093059466641691268667088494516369664819242792895659767320828220367940195882959696408563062091666893877769534682317761766664537559725455393118164967089955006604235014642812449974237879733417524154482859147346256817317634610544831846653125765496269990660356475318111632234274114520434395459780477119393117936172400640000 (BHE4 59) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_R3 cHE4_R3 (by kernel_fact)
  | 60, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 60 0 125 73 25 11 8 10 36 27
      7487506062110335180717427703403889989200149928448837613091781050681588744267908964715612646471734432878213405030862771629305186461538668672726779642951425100818016211126567022314857968757086464597477313997409170437200655274210131366317792734157947110071084278152795420719056428080127437498951065782331650645530683004035264396247695360000 (BHE4 60) (kronHE4 125 73 55) rfl (by kernel_fact) clHE4_A1 cHE4_A1 (by kernel_fact)
  | 61, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 61 3 120 73 25 11 8 10 36 27
      227085988292987681228493170358720199796630525449425347844948461663679720396134207928308155525923724855168209725553525380985354545941161588440253606823518426699410955118054939489377139185448331702967086273647212805067473050889775439636988162867883990625698934115121153190401395142166585831716364649194016022170744204766488207713894400000 (BHE4 61) (kronHE4 120 73 55) rfl (by kernel_fact) clHE4_A2 cHE4_A2 (by kernel_fact)
  | 62, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 62 0 119 73 25 11 8 10 36 27
      189092560147769668293383166600419155312825202972249951693344745937980196800469629491686892785371690846804981061710493750428989032566272743445365148674163865074149135647553650518229484264541553431640807827225998863714504648634048381730032701011454616754343726541409559075449169792051214881012527174109965142037333475009605881697402880000 (BHE4 62) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_K1 cHE4_K1 (by kernel_fact)
  | 63, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 63 3 120 73 25 11 8 10 36 27
      277742027536546149854039780004486052964427446327234706130140778864183398226668979390903331386971920799783082225913918376313715420648323278296338570633330752788866988728495604382331452413448057266746754571120978816397969219818655782779554335625976751174947989998232339113520682046768713296781348206021706588851391038865801173721415680000 (BHE4 63) (kronHE4 120 73 55) rfl (by kernel_fact) clHE4_K2 cHE4_K2 (by kernel_fact)
  | 64, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 64 2 123 73 25 11 8 10 36 27
      3626620690872488005249293134610478337153343401430359214139134610160118832503502918235837445942137012531356790308584546413008011306591466964890960901979854293571905024407559238088049292546151630680027614696902304610635812066123616658563906430194786768843013869764748600408955687662508259439886530989116206480147617356141930216717025280000 (BHE4 64) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_K3 cHE4_K3 (by kernel_fact)
  | 65, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 65 0 119 73 25 11 8 10 36 27
      220545593022052663813070133254601186003517529794115979259749037455592524195061330029396731985168256787921339810985111759250130319278911257499216687714524785550529332863457552056150498993769167847495613111695642434240817724638263775961583804657410550060158919890137076927620284957626955249171190979780568198101810791104975397778882560000 (BHE4 65) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_KD cHE4_KD (by kernel_fact)
  | 66, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 66 3 120 73 25 11 8 10 36 27
      337591966170486644614374396846267770213328803216936366734226345677052040881131952458735748006502953172950680847144511428479321807894913882898196084097277223547580713592088548196933202827915485805691353957073270005793252198721686929420478514792487383401666697993633176037830557711000986525685103522004196851941543639533645000500838400000 (BHE4 66) (kronHE4 120 73 55) rfl (by kernel_fact) clHE4_KR cHE4_KR (by kernel_fact)
  | 67, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 67 2 124 73 25 11 8 10 36 27
      4743872285734485755801750514849460926915906481274081832044852842288936692727181875205218891221973311022078437800173102141940645985088811776907090380588403344497716592629152986041443915122234497159094838135799430897972507165387991277338283681086822229049929744329409312571323316161814720088556279122792232225900122240461680513216675840000 (BHE4 67) (kronHE4 124 73 55) rfl (by kernel_fact) clHE4_KZ cHE4_KZ (by kernel_fact)
  | 68, _ => by rw [xHE4_zero c (i := 68) rfl]; exact (Bd_zero r).le (by norm_num [BHE4, BHE4l])
  | 69, _ => by rw [xHE4_zero c (i := 69) rfl]; exact (Bd_zero r).le (by norm_num [BHE4, BHE4l])
  | 70, _ => by rw [xHE4_zero c (i := 70) rfl]; exact (Bd_zero r).le (by norm_num [BHE4, BHE4l])
  | 71, _ => center3_fullN hq hc boxHE4 (l1HE4 28) (fun _ => rfl) 71 0 129 37 14 9 8 5 36 27
      47834884316007366514710390827141909056247197529154234916542103802407984085589703716965365859903507820084146323974520578972347030084068806794468413262517742892203982563350372956891322394333781733012029615515798159953099748338049650562216420357787671704849251083839316479703000964440975522015003522729942892111187804867539538673873715200000 (BHE4 71) (kronHE4 129 37 28) rfl (by kernel_fact) clHE4_r cHE4_r (by kernel_fact)
  | 72, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 72 0 123 73 25 11 8 10 36 27
      1516057004412108922281608719430755331720729130214525990160440772428522868408293286919985336285573571290869628204888537508061621536681692839196019388846499650571720316940715527687533868503606718930368359471239623329703091399373100985957078059256297649184241058138302794996228383619854954970869851785286587124723117411820117651577896960000 (BHE4 72) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_P4P cHE4_P4P (by kernel_fact)
  | 73, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 73 0 122 73 25 11 8 10 36 27
      1081824904814025373290006066140692778806491962353218469712543362964293935021083176874601842365595454158440037481638180689928410827046280105781710443939186564442182227449425605161114086174547038265425480755677485498736816671167932199264181739050731660971901738180732395118332463246957553574474767697735807240068145941565717564190883840000 (BHE4 73) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_R4 cHE4_R4 (by kernel_fact)
  | 74, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 74 0 122 73 25 11 8 10 36 27
      1549419343082738290636670301635136833770701814432474349532854361086095682698431096901642600181738915629770981965887289924183255593769779938687044638800947515800074667709812687070612056418482319349326708661436116162632381162584623249940828468314783517048315654221847341698449140560604597372683353106359899029346490707132356211706429440000 (BHE4 74) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_R8 cHE4_R8 (by kernel_fact)
  | 75, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 75 0 123 73 25 11 8 10 36 27
      3095069366471544819674515825390593940367315039370190777969922524961999363304764639553218244437506611224415367204986291998913178834772782186625339543503072558148099327917165170436487084598890964244987377164514607208749115524958501884913072128850691918155170530945355101478721394159207917487521330483634019927080638562023802590839439360000 (BHE4 75) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_P42 cHE4_P42 (by kernel_fact)
  | 76, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 76 0 108 73 25 11 8 10 36 27
      371155833909157528514340897528589537119767122316754431305909883469823832372215655622491902654106054302796517193781654027746647227883051043189729457723167861111574741296008835404791867233106502984593519802244001905761890860120821285838305340509460517248704995119600790338482852517149135975260375549725791160952192834640456586362880000 (BHE4 76) (kronHE4 108 73 55) rfl (by kernel_fact) clHE4_E4P cHE4_E4P (by kernel_fact)
  | 77, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 77 0 123 73 25 11 8 10 36 27
      2591548014889210311121796757007377929898458357778487201389822116161669931794727433435191749301952203731585160607626749618030126762341384650887243487651408762689463016674461534968096991995514009406509238419963500883933618037375297745974212646877835005871980550249475796641783773827256581750466555410594969714200417336301505190507315200000 (BHE4 77) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_PP4 cHE4_PP4 (by kernel_fact)
  | 78, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 78 2 123 73 25 11 8 10 36 27
      874394076315164379506061849186426630433330336895344241815736656538698214619068310853872051494952483275154895888858069245609085997692708290980675401755459464646848604872234080741257324393684371043227275204414390410708306869675130386109685740461356348316467233765388397216788468365129263163387227334790101377667377752528339956127498240000 (BHE4 78) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_QPP4P cHE4_QPP4P (by kernel_fact)
  | 79, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 79 0 123 73 25 11 8 10 36 27
      736106934709948521189376476430805535456055943420269664810662413315162239340346909989515354117337366403446775473506521781536043567467171749683982810657081057959446305938740729245148303469080631600450600288443748265333208518092502329564435306047190804521635841158522922232623108657994665835801011641751379463002852807758128727845765120000 (BHE4 79) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_V40 cHE4_V40 (by kernel_fact)
  | 80, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 80 0 123 73 25 11 8 10 36 27
      736292612023247738885441734495760877936181855955981629745343748588041647217466699763185562004828663145742862878656686059814039332938342894458923669669858864760468192977035484485591322602600749543047891271151160599449954231138855970618858670035752800343964394752222948909292467657266120237083587746058428086579157547058754729457745920000 (BHE4 80) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_V42 cHE4_V42 (by kernel_fact)
  | 81, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 81 0 123 73 25 11 8 10 36 27
      736106934709948521189376476430805535456055943420269664810662413315162239340346909989515354117337366403446775473506521781536043567467171749683982810657081057959446305938740729245148303469080631600450600288443748265333208518092502329564435306047190804521635841158522922232623108657994665835801011641751379463002852807758128727845765120000 (BHE4 81) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_V4n cHE4_V4n (by kernel_fact)
  | 82, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 82 0 123 73 25 11 8 10 36 27
      747378865806766452729830652665358197486084297310499118640024848549755271266341311252641176590456805880025086366292501029139089403166273043727159519508361706896341972482453253207981955053625266539140488032369407939166516071471980692319912079633972889370170314152791008352333030810833030187160689474159565574417459549677786925178552320000 (BHE4 82) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_VV4 cHE4_VV4 (by kernel_fact)
  | 83, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 83 2 123 73 25 11 8 10 36 27
      873897966495799099581707585353152179719643360065870425205004605136631805038833055136483367274057447401664117357776897146064810506482340831794080992133954723585599717504216480784691464878555301693587362753296751463046385051325191554958139606537354925580142509740024041102132396401647549938598035171362461313377222710363064071440302080000 (BHE4 83) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_Bm cHE4_Bm (by kernel_fact)
  | 84, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 84 0 119 73 25 11 8 10 36 27
      45995081073084006264144606564559527938699228393417533573598176733084600082297792035543621019137988288542448388437039018242641375080835391148527320444728598934811521695529204766241656148397867050973105399534421307647211296478893894771361942651718915100816587580614727384329808619654784155783657233394175857799219043141864941032570880000 (BHE4 84) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_lamv cHE4_lamv (by kernel_fact)
  | 85, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 85 2 119 73 25 11 8 10 36 27
      54618616819182298481247778617712992604898806565480090496045121833426281717708460273267191321704471536879798613880098283396900311414972437605229874464726795768880672683177997804405313227740701661517701337180812038840188265968434919733190607599883530541506849293713708188246841120257207614242171936464485261410158833641461359847669760000 (BHE4 85) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_EN cHE4_EN (by kernel_fact)
  | 86, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 86 0 123 73 25 11 8 10 36 27
      764838273670785111503257442580467262549750249792803541541750729900381426767304119767026651972470203584920158735590176291001771771052153419840701781754413503517816965647838557269268987345510618364231091671349109718488400420783965278610962526752599426760635004553035680505148154194135469125977587688160095975024305366845794354724864000000 (BHE4 86) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_N0 cHE4_N0 (by kernel_fact)
  | 87, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 87 0 124 73 25 11 8 10 36 27
      794882785333642963572965986546309746575654746752880723558994058170664455881564226907846574299964601987392639912948732152912230784966850678789089368166435602485999277169694759057772899352139653291663720042390970490436116496409843078584581819492943099524283741133019130064908227617600624403396319157094980034541660877810055762380062720000 (BHE4 87) (kronHE4 124 73 55) rfl (by kernel_fact) clHE4_N2 cHE4_N2 (by kernel_fact)
  | 88, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 88 0 123 73 25 11 8 10 36 27
      764838273670785111503257442580467262549750249792803541541750729900381426767304119767026651972470203584920158735590176291001771771052153419840701781754413503517816965647838557269268987345510618364231091671349109718488400420783965278610962526752599426760635004553035680505148154194135469125977587688160095975024305366845794354724864000000 (BHE4 88) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_Nn cHE4_Nn (by kernel_fact)
  | 89, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 89 0 123 73 25 11 8 10 36 27
      736464611888085346419929735148114617602985979994281356189772225669119987975817297223870616916211411375039855918324982084415693578310165467133200316373597373201276084794624223511376656138518677423248851361471836556416612927177771641434627173021799391019742500645858087123116290446550285568406001750033367479454238793314233465983467520000 (BHE4 89) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_Fv cHE4_Fv (by kernel_fact)
  | 90, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 90 0 119 73 25 11 8 10 36 27
      130689519908994361854100390487021289361529584596402058973074340568449037338461999858247336254128236851150036455730283895176826228916378775913727665249120498091001470463146250621015654927647751532701916371272190809253132263405738975596696915269467042889971471307990706726406030434323792643156597431326492410401744793647694337424752640000 (BHE4 90) (kronHE4 119 73 55) rfl (by kernel_fact) clHE4_YDt cHE4_YDt (by kernel_fact)
  | 91, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 91 0 122 73 25 11 8 10 36 27
      908288759656819384217797912654724254386444746853665740368934887252101328321737211577066038848677751825091165346902479767295555518706720221427241469034066433348334128069101055836624592869021026720290415745502491433438484420544918375877811567911523911250919095342483543136094818147488582579748726076516002188658697031274408711416709120000 (BHE4 91) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_DtF cHE4_DtF (by kernel_fact)
  | 92, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 92 3 120 73 25 11 8 10 36 27
      214732319139249006303991442520157342193428807895938731016972064942041104414219826382530004002626100304141681136348978570898581705870197275217878355827278511058351223566223269933921486584433245209910981181784312309067167218708722104881074013709867683009362085524024413646552303085418563064268171899593584648571576347833364522145914880000 (BHE4 92) (kronHE4 120 73 55) rfl (by kernel_fact) clHE4_YnRt cHE4_YnRt (by kernel_fact)
  | 93, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 93 3 118 73 25 11 8 10 36 27
      64847942189868534160841940203940486356970552543744390377418926090767515939843834914775568839792836040376134001825042334252681036809336264034696920314381314298307872009300277134001856165100900578419163464687232966303547877032061879085451898550446721723166602898037771921243706388472847453410350187813538976194331911527795076890624000000 (BHE4 93) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nRtF cHE4_nRtF (by kernel_fact)
  | 94, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 94 2 123 73 25 11 8 10 36 27
      2197659024194235823316155654415875685669624359377060214519430572866248226159281652160288574009840450192282259882742170159251485582945886514922044710202682078295951544471837147386473327585357503887250743207829482673220844178870137375463474767167325540491912028391659735973227657581640952834596129875051039397096650970900139557453885819375 (BHE4 94) (kronHE4 123 73 55) rfl (by kernel_fact) clHE4_YnZt cHE4_YnZt (by kernel_fact)
  | 95, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 95 0 118 73 25 11 8 10 36 27
      67321067097635201457382550193641036863792023683606957424410767997069488403219919467709703091058719202371047919501234713313037585116373377571260407975726207505169204519689272583949713115081408889348961037315763359275896416007081364440817038041574560985689993152210761071606768971628668086309593674833023324676847865277695419712798720000 (BHE4 95) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nZtF cHE4_nZtF (by kernel_fact)
  | 96, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 96 0 122 73 25 11 8 10 36 27
      908288759644317853586208906821803932048162201595317528558176226805352028888361367940709796777642109804739931974200239983169525726663501110088850103571309790650296030218582985553096341357445984991518620183169823196096447448160176721741647367998965945081266293855111840738612156094838667449926067795338874048145338894772653446691553280000 (BHE4 96) (kronHE4 122 73 55) rfl (by kernel_fact) clHE4_DtJ cHE4_DtJ (by kernel_fact)
  | 97, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 97 3 118 73 25 11 8 10 36 27
      64847942210799638741917763656837153699102479113312184156756837657118067114668094827776821661435637287509156471427654294184097674315128345138576833495825444293342976276710445651937748559953552079578834758860929115598009360231334509541649759946577243257738738965430189135491701212050261793146923445176438144627400643487195085689323520000 (BHE4 97) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nRtJ cHE4_nRtJ (by kernel_fact)
  | 98, _ => center3_fullN hq hc boxHE4 (l1HE4 55) (fun _ => rfl) 98 2 118 73 25 11 8 10 36 27
      67321067349027209523315831845037984341491266612904580065955678028464282911468172367562809152607064677090421906996520045249293953671466571517065247204557408136875428672411045839184086348146780199307411477210371398646649935173920320784057707871875946755235614977422805678104965925291643739739337207591458194248973799322357297777213440000 (BHE4 98) (kronHE4 118 73 55) rfl (by kernel_fact) clHE4_nZtJ cHE4_nZtJ (by kernel_fact)
  | n + 99, h => absurd h (by omega)

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Vn`. -/
theorem vnodeHE4_Vn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 54 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i)) :
    Bd r (XHE4 c 54 - xHE4 c 54) (EHE4 54) := by
  have hn : ∀ i, i < 54 → Bd r (xHE4 c i) (BHE4 i) := fun i hi => normHE4 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl) hn hE trHE4N_Vm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 11344893484798605325265679535063357591851232897104243856919737010965779651119985842059754955330768355745212558293225459033629724181338827175334797096564704128685240896059050719836630940303867621645211856734923897730577015309176731333073944512541197123150522984704144130136109518190582630394920086346031787773133439546297957954355200000
      (2549 / 10 ^ 5 : ℚ) (kronHE4 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_Vm1 kHE4_Vm1 (by kernel_fact)
  have h2 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl) hn hE trHE4N_V2m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 22861526974864045755575540236732117798425940405397217799743642411012914564919461021340083095539762941967211113054594425946458498871125693663523213761956861329774312712312808662715158325271582008133545528082538280196869644791212146975161043879129589037449832258408265384631869798718623620959582644698678052902915127054673615551201280000
      (5137 / 10 ^ 5 : ℚ) (kronHE4 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_V2m1 kHE4_V2m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl) hn hE trHE4N_eta (2, 0, 0)
      144 108 48 237 145 49 13 8 19 72 54 43931426657619403534989670756051057587463748933176095396543676796899267433931926557254637778301534387563301551710126654303462387955179330009295159014926376619169151475062235809798926961021105864354396443084478616065305371396964684954545918848449916685031826835814470098976075548446127973725485419693355701570332452062055007308897971019803429169280179208271229548083813688159066519397738764713857518988268339146300539911412858566499765053234797846425789001115889398576703780951781604535397604292892771810795723951923791382870054847442882552243726820290680760403789790712227198055056377149070767562697011167373938793441336897019876940196085760000000
      (23 / 40000000000000000000000 : ℚ) (kronHE4 237 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_eta kHE4_eta (by kernel_fact)
  have e1 : Ex.eval (XHE4 c) (toEx trHE4N_Vm1) = xHE4 c 52 - 1 := by
    simp only [trHE4N_Vm1, toEx, Ex.eval, XHE4_eq_V0 hc, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
  have e2 : Ex.eval (XHE4 c) (toEx trHE4N_V2m1) = xHE4 c 52 ^ 2 - 1 := by
    simp only [trHE4N_V2m1, toEx, Ex.eval, XHE4_spec c (i := 53) rfl, XHE4spec, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE4 c) (toEx trHE4N_eta) = xHE4 c 52 ^ 2 * (1 + XHE4 c 51) - 1 := by
    simp only [trHE4N_eta, toEx, Ex.eval, XHE4_spec c (i := 53) rfl, XHE4spec, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hEb : Bd r (XHE4 c 51) ((BHE4 51 + EHE4 51 : ℚ) : ℝ) := by
    have := (hn 51 (by norm_num)).add (hE 51 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep (a := (((2549 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (n2 := (((5137 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((23 / 40000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((12827 / 12500 : ℚ) : ℚ) : ℝ)) (m := (((541 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((102821 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHE4 54 : ℚ) : ℝ))
    hr h1 h2 h3 hEb
    (by exact_mod_cast (show (2549 / 10 ^ 5 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (2549 / 10 ^ 5 : ℚ)) ≤ (12827 / 12500 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (12827 / 12500 : ℚ) ^ 2 * (5137 / 10 ^ 5 : ℚ) ≤ (541 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHE4 51 + EHE4 51 ≤ (541 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (541 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (102821 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (102821 / 10 ^ 5 : ℚ) ^ 2 * (1 - (541 / 10 ^ 4 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * (541 / 10 ^ 4 : ℚ) + (2549 / 10 ^ 5 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (102821 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((12827 / 12500 : ℚ) ^ 2 * (23 / 40000000000000000000000 : ℚ)) ≤ EHE4 54 by kernel_fact))
  have eX : XHE4 c 54 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE4 c 51) := by
    rw [XHE4_rel c (i := 54) rfl, XHE4_rel c (i := 51) rfl]
    change XLM c _ _ 63 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 61)
    rw [XLM_old c _ _ (j := 63) rfl, XLM_old c _ _ (j := 61) rfl]
    simp only [XL, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHE4 c 54 = xHE4 c 52 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `V4n`. -/
theorem vnodeHE4_V4n {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 81 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i)) :
    Bd r (XHE4 c 81 - xHE4 c 81) (EHE4 81) := by
  have hn : ∀ i, i < 81 → Bd r (xHE4 c i) (BHE4 i) := fun i hi => normHE4 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl) hn hE trHE4N_V4m1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 185637540604420963062771397853088436868289125589127633091585585808638023582237420817417811129553786767601258513897489653781566173805491307545683541423475002461958810273452985281805094714758784880913895893007342977827774430200013222644223619688162908570439868687284083346170743518119343262495907444565738215348117488289671324631040000
      (4171 / 10 ^ 7 : ℚ) (kronHE4 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_V4m1 kHE4_V4m1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl) hn hE trHE4N_etaV4 (2, 0, 0)
      144 108 48 231 145 49 13 8 19 72 54 1675688553469833810621257354910640581445403196721974877096853014945217729348954694686088082285108594741541396597433720198510548479434644205999905082719586100748562881573760038328474798583869639618566250038339273825910786905749525842255281239903461210579039603728338574897278403529755239970209547308726344102805195106466230681156406272316513798411377203927506573306244263184818596465056452625270658815585998868544871679282249535603028435760901853863938459553093187439036946186892120432807311554303460956316220271792337584503255061886897626705638528944843051673652536283833832756355690578950392184028487135399866033963110552197562346776821760000000
      (3 / 2000000000000000000000 : ℚ) (kronHE4 231 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_etaV4 kHE4_etaV4 (by kernel_fact)
  have e1 : Ex.eval (XHE4 c) (toEx trHE4N_V4m1) = xHE4 c 79 - 1 := by
    simp only [trHE4N_V4m1, toEx, Ex.eval, XHE4_eq_V40 hc, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE4 c) (toEx trHE4N_etaV4) = xHE4 c 79 ^ 2 * (1 + XHE4 c 76) - 1 := by
    simp only [trHE4N_etaV4, toEx, Ex.eval, XHE4_spec c (i := 80) rfl, XHE4spec, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHE4 c 76) ((BHE4 76 + EHE4 76 : ℚ) : ℝ) := by
    have := (hn 76 (by norm_num)).add (hE 76 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((4171 / 10 ^ 7 : ℚ) : ℚ) : ℝ)) (η := (((3 / 2000000000000000000000 : ℚ) : ℚ) : ℝ))
    (b := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (m := (((417 / 500000 : ℚ) : ℚ) : ℝ)) (g := (((50021 / 50000 : ℚ) : ℚ) : ℝ)) (ε := ((EHE4 81 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (4171 / 10 ^ 7 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (4171 / 10 ^ 7 : ℚ)) ≤ (50021 / 50000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHE4 76 + EHE4 76 + (50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ) ≤ (417 / 500000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (417 / 500000 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (50021 / 50000 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (50021 / 50000 : ℚ) ^ 2 * (1 - (417 / 500000 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * (417 / 500000 : ℚ) + (4171 / 10 ^ 7 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (50021 / 50000 : ℚ) ^ 3 / 2 * ((50021 / 50000 : ℚ) ^ 2 * (3 / 2000000000000000000000 : ℚ)) ≤ EHE4 81 by kernel_fact))
  have eX : XHE4 c 81 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE4 c 76) := by
    rw [XHE4_rel c (i := 81) rfl, XHE4_rel c (i := 76) rfl]
    change XLM c _ _ 124 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 120)
    rw [XLM_new c _ _ (j := 124) rfl, XLM_new c _ _ (j := 120) rfl]
    simp only [XLMnew, eV4, PolyExprS.eval, PolyExprS.eval_ofPoly]
    rfl
  rw [eX, show xHE4 c 81 = xHE4 c 79 from rfl]
  exact hv

set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The node step: the ball of the node `Nn`. -/
theorem vnodeHE4_Nn {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)
    (hE : ∀ i, i < 88 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i)) :
    Bd r (XHE4 c 88 - xHE4 c 88) (EHE4 88) := by
  have hn : ∀ i, i < 88 → Bd r (xHE4 c i) (BHE4 i) := fun i hi => normHE4 hq hc i (by omega)
  have h1 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl) hn hE trHE4N_Nm1 (1, 0, 0)
      72 54 24 123 73 25 11 8 10 36 27 28916976501441011276943737547514815530562595498123004364179902171027825450539447198328715666262390968240984520597551999119509769758787161464264654638755920560832618519371281009402488971144745548661405278798368796133019677121662962269171444325096785147569603263200042355871216279658922633439071953853282250236800676575955298203729920000
      (6497 / 10 ^ 5 : ℚ) (kronHE4 123 73 55) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_Nm1 kHE4_Nm1 (by kernel_fact)
  have h3 := norm3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl) hn hE trHE4N_etaN (2, 0, 0)
      144 108 48 240 145 49 13 8 19 72 54 100330269147533853813036780091831811008120190819033292521634421351940951956411688013476929657862260677844367404453170869564362828116398295965478304162400457071891701302328291579576530117800318665709305554699808673165305833619183141239028191358006696595809172764022333582237431779103254118964952961789473537391676222382692759911985844613058347914327114700596207252583335814816007932522735681788288244806250338516795123195137796921859170930256784833611812396335255341822088555013037758796699901481692815150954909606648829552657628829485181137403529716663015044794159624485879909052440845224501766471161526699766223303995176414660983336568891637760000000
      (17 / 10 ^ 22 : ℚ) (kronHE4 240 145 109) (by kernel_fact)
      (by kernel_fact) (by kernel_fact) lHE4_etaN kHE4_etaN (by kernel_fact)
  have e1 : Ex.eval (XHE4 c) (toEx trHE4N_Nm1) = xHE4 c 86 - 1 := by
    simp only [trHE4N_Nm1, toEx, Ex.eval, XHE4_eq_N0 hc, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
  have e3 : Ex.eval (XHE4 c) (toEx trHE4N_etaN) = xHE4 c 86 ^ 2 * (1 + XHE4 c 85) - 1 := by
    simp only [trHE4N_etaN, toEx, Ex.eval, XHE4_spec c (i := 87) rfl, XHE4spec, XHE4_eq_t hc, xHE4_t (ne_zero_of_norm_one_mu hc)]
    ring
  rw [e1] at h1
  rw [e3] at h3
  have hEb : Bd r (XHE4 c 85) ((BHE4 85 + EHE4 85 : ℚ) : ℝ) := by
    have := (hn 85 (by norm_num)).add (hE 85 (by norm_num))
    rw [add_sub_cancel] at this; push_cast; exact this
  have hv := vstep2 (a := (((6497 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (η := (((17 / 10 ^ 22 : ℚ) : ℚ) : ℝ))
    (b := (((106949 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (m := (((1229 / 10 ^ 4 : ℚ) : ℚ) : ℝ)) (g := (((106777 / 10 ^ 5 : ℚ) : ℚ) : ℝ)) (ε := ((EHE4 88 : ℚ) : ℝ))
    hr h1 h3 hEb
    (by exact_mod_cast (show (6497 / 10 ^ 5 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show 1 / (1 - (6497 / 10 ^ 5 : ℚ)) ≤ (106949 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show BHE4 85 + EHE4 85 + (106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ) ≤ (1229 / 10 ^ 4 : ℚ) by kernel_fact))
    (by exact_mod_cast (show (1229 / 10 ^ 4 : ℚ) < 1 by kernel_fact))
    (by exact_mod_cast (show (0 : ℚ) ≤ (106777 / 10 ^ 5 : ℚ) by kernel_fact))
    (by exact_mod_cast (show 1 ≤ (106777 / 10 ^ 5 : ℚ) ^ 2 * (1 - (1229 / 10 ^ 4 : ℚ)) by kernel_fact))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * (1229 / 10 ^ 4 : ℚ) + (6497 / 10 ^ 5 : ℚ) < 2 by kernel_fact))
    (by exact_mod_cast (show (106777 / 10 ^ 5 : ℚ) ^ 3 / 2 * ((106949 / 10 ^ 5 : ℚ) ^ 2 * (17 / 10 ^ 22 : ℚ)) ≤ EHE4 88 by kernel_fact))
  have eX : XHE4 c 88 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHE4 c 85) := by
    rw [XHE4_rel c (i := 88) rfl, XHE4_rel c (i := 85) rfl]
    change XLM c _ _ 130 = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLM c _ _ 128)
    rw [XLM_new c _ _ (j := 130) rfl, XLM_new c _ _ (j := 128) rfl]
    simp only [XLMnew, eN, PolyExprS.eval]
    rfl
  rw [eX, show xHE4 c 88 = xHE4 c 86 from rfl]
  exact hv

/-- The transport input `LRx`. -/
theorem stepHE4_LRx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHE4 c 6 - xHE4 c 6) (EHE4 6) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHE4 c 4)) ((BHE4 8 : ℚ) : ℝ) := by
    have h := normHE4 hq hc 8 (by norm_num)
    rwa [xHE4_der_thU hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 4) = dTh (xHE4 c 4) by simp [dTh]] at h
  have hana : Ana (xHE4 c 4) := by
    rw [xHE4_fam hc0 (i := 4) rfl (p := 0) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHE4_spec c (i := 6) rfl]
  exact step_Linput hana (by rw [xHE4_der_LRx hc0]; norm_num [KamTorusA.Iq]) hth (by kernel_fact)

/-- The transport input `LZx`. -/
theorem stepHE4_LZx {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHE4 c 7 - xHE4 c 7) (EHE4 7) := by
  have hc0 := ne_zero_of_norm_one_mu hc
  have hth : Bd r (dTh (xHE4 c 5)) ((BHE4 9 : ℚ) : ℝ) := by
    have h := normHE4 hq hc 9 (by norm_num)
    rwa [xHE4_der_thZ hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHE4 c 5) = dTh (xHE4 c 5) by simp [dTh]] at h
  have hana : Ana (xHE4 c 5) := by
    rw [xHE4_fam hc0 (i := 5) rfl (p := 1) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHE4_spec c (i := 7) rfl]
  exact step_Linput hana (by rw [xHE4_der_LZx hc0]; norm_num [KamTorusA.Iq]) hth (by kernel_fact)

set_option linter.unusedVariables false in
/-- The empty chain. -/
theorem ballHE4_0 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 0 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  fun i h => absurd h (Nat.not_lt_zero i)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `t`. -/
theorem ballHE4_1 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 1 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_0 hr hq hc)
    (step_exact (XHE4_eq_t hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V`. -/
theorem ballHE4_2 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 2 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_1 hr hq hc)
    (step_exact (XHE4_eq_V hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `c`. -/
theorem ballHE4_3 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 3 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_2 hr hq hc)
    (step_exact (XHE4_eq_c hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `s`. -/
theorem ballHE4_4 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 4 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_3 hr hq hc)
    (step_exact (XHE4_eq_s hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `U`. -/
theorem ballHE4_5 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 5 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_4 hr hq hc)
    (step_exact (XHE4_eq_U hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Z`. -/
theorem ballHE4_6 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 6 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_5 hr hq hc)
    (step_exact (XHE4_eq_Z hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LRx`. -/
theorem ballHE4_7 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 7 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_6 hr hq hc)
    (stepHE4_LRx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `LZx`. -/
theorem ballHE4_8 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 8 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_7 hr hq hc)
    (stepHE4_LZx hq hc)

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thU`. -/
theorem ballHE4_9 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 9 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_8 hr hq hc)
    (step_exact (XHE4_eq_thU hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZ`. -/
theorem ballHE4_10 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 10 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_9 hr hq hc)
    (step_exact (XHE4_eq_thZ hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ue`. -/
theorem ballHE4_11 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 11 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_10 hr hq hc)
    (step_exact (XHE4_eq_Ue hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Ze`. -/
theorem ballHE4_12 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 12 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_11 hr hq hc)
    (step_exact (XHE4_eq_Ze hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thUe`. -/
theorem ballHE4_13 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 13 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_12 hr hq hc)
    (step_exact (XHE4_eq_thUe hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `thZe`. -/
theorem ballHE4_14 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 14 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_13 hr hq hc)
    (step_exact (XHE4_eq_thZe hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m02`. -/
theorem ballHE4_15 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 15 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_14 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_14 hr hq hc) trHE4N_m02 1 0 2 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 89554648511099266895166682971888625093677602837788328791790611123216563123869930512145277334060224572043632644438019537632355567541167427000030276882034868166745499958335200262850833710208087914850251970071610250820944841914452257870544566059907793971310026480294461736399656532889351165899414384281073559357607432383011498596246830849081353082502205858414814139573391803737279037611975648659009322512040263318161804283127567862531968131622443493521352677078780923852045526545286617895441005568149909458703659806926576063138078421168386012367755928042571949314049722247152947722874760376183647739061282652541427993315019647865801655220961280000000
      (kronHE4 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m02 kHE4_m02 (by kernel_fact) (relHE4_m02 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m11`. -/
theorem ballHE4_16 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 16 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_15 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_15 hr hq hc) trHE4N_m11 1 0 1 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 52504974114484809107360156768661704869183210553217106411414047786933312437373952934638968017909029203010007307784983444599513002351044108516896741045964549074627082736260388381804626171559474733928140361751655669187212058083033579671330435782019084835679664236790347192066176076582543379556155781193025815835386533030639596965591329425452990268449233809529608869323626771917705451248823266347623616256582097710763142283318644857007709579041714829972319953503729879826046438398824719771214386756293918953232302504112015882564608039278751048541878986291121036839733918647805834249179064688063021975955070266692160254454678112776178730648207360000000
      (kronHE4 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m11 kHE4_m11 (by kernel_fact) (relHE4_m11 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m20`. -/
theorem ballHE4_17 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 17 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_16 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_16 hr hq hc) trHE4N_m20 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 106466869164987068801047226549929296514190467965398427977777578163188004946836185849380129653184751975045041564933721984813909578189328269632246754209987843284106107608141375894071225804273768245196314700516492269740037640295710193953446449895928973713229968380067128320269243134193017347810397083845427224198356934414276151151191084144672939622875597829723979795655577084394462933819116332030063672145849273272186547879123170103222677197333710528792995464783356062522077888312120070366076538462005209367922016240737730953884569599073660087363963705258684701366377366369428407264631410542799203162583731129903241097947459678894289920427294720000000
      (kronHE4 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m20 kHE4_m20 (by kernel_fact) (relHE4_m20 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m03`. -/
theorem ballHE4_18 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 18 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_17 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_17 hr hq hc) trHE4N_m03 1 0 3 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 27677234578973337909212524885649616419135682987692734107925326505193492154599885243345329764409307034922264618686901550887673685532879679832613234871984634627175105389625398469544341532472770376352184603806778868443758595185467461534748639801240484501046025122322794331297670657654943003724706337954942714978515567138800213209962663301795777460769500343076436893922197437976599505261110785270344488988567078579290439569443194644952088613423357726393807009585939535890975849279714681431128281741124638747834161908913225391380407706489714837165128808131866588632675507174619440576361074474369900676721571688789780138118635808201024527746990080000000
      (kronHE4 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m03 kHE4_m03 (by kernel_fact) (relHE4_m03 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m12`. -/
theorem ballHE4_19 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 19 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_18 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_18 hr hq hc) trHE4N_m12 1 0 2 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 16842561922341206637443810956963474566800116254763424235389844180867541976202041434476617118206150013752419668597945138619906404564201120977541101763407546016027697509847905802878841787266727556977865522463442558806949850879581421786431012327008451441538620458190387156178042533844898471999014202723069824964141093130201996217635914986872333501347846046625401269443382931261527385318187714283754265462820142262515482586401880072702228318366569041942136259597663241940695758527966275290853313764824494000454467304973918262559527282202750923722377591347815673409330447040292115452080743453735815882605198531974727015202611284756724470670950400000000
      (kronHE4 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m12 kHE4_m12 (by kernel_fact) (relHE4_m12 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m21`. -/
theorem ballHE4_20 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 20 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_19 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_19 hr hq hc) trHE4N_m21 1 0 1 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 18442408153886237167631453075209030210012494829076696837252242509620079079921526897275423338541460765919682060183577597108535605440902111177216951483591844524930010195374132766240311037359229755569259506535879265207613636976825850540995575688503692082039168296011662476192256519163308355242953181629804223614383629237824154278270950493075960890569893492245462302597489137905675295080884771700730906695582988099214500900142338588085008597647122660153290789372971820923251485410059274721396279431138207724042925071651039702383025125526660738967257004467954319879570536310888392410871837657761339924519966457624406561255796110476736080914677760000000
      (kronHE4 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m21 kHE4_m21 (by kernel_fact) (relHE4_m21 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m30`. -/
theorem ballHE4_21 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 21 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_20 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_20 hr hq hc) trHE4N_m30 1 0 0 (1 : ℤ)
      144 108 48 232 145 49 13 8 19 72 54 38991240860401973681193681517976523490202639558303041640675348629251547735842241601561762234645914921181568082534505699845665643244312971962446343831354838405157519433831392939361336290583824540244494151114232655126090947171161547267773848484812684132613979403600762607120274551448842266469716664369540473953277510301604794041684299205967904690762630232524671382185133807403387130439596343585425521882921725060329077936801258108974058535219042741201835729784025648407184220743024079771526893104996285369291584789839198098063942385429746868811639965871204929942427673826945827578993740533565135281073925508166419709385629386324523885747240960000000
      (kronHE4 232 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m30 kHE4_m30 (by kernel_fact) (relHE4_m30 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m13`. -/
theorem ballHE4_22 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 22 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_21 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_21 hr hq hc) trHE4N_m13 1 0 3 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 3445969360348539735951756157805713979073684759027619768538879347964313488716831144844307764709526541926218508519200648817208487453213147797679211168875686354906652746066590748754911343338083515339947042630270795531119722878072430920545890566455336459787245518450658058147888169773117069577753933041706167864601948745938866783244661080429335148066438971398883155716218443596690912044459848461760346396331055333640859334646277235131905944623863562891550377919230080117456963883260878998400795147696416768833865287447586066351612158499815843383364246124137803732340074559242866936978660328486496185020391485238721091111943685106953758839930880000000
      (kronHE4 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m13 kHE4_m13 (by kernel_fact) (relHE4_m13 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m22`. -/
theorem ballHE4_23 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 23 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_22 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_22 hr hq hc) trHE4N_m22 1 0 2 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 3104591964185126351521763559251879819612720569346995520362605304333332108173206753442384451243763053769139976204701788220793048087047551186471886557317708980833775628452099779843740835159098982192205257870061016283889571236583400148369605858907087150404166484705222476761242068159645626821193113528702072621694227728928914184100479654841298993961989382580313694180498515949125400636803117486321166966006760205028610273126351985146861444137073166223350596109238174034134515747957086661543844843995366320047113829424940293612939005958646423954172960547885642238711526157571077129722125333988684403466792323527363711495774282544081548397772800000000
      (kronHE4 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m22 kHE4_m22 (by kernel_fact) (relHE4_m22 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m31`. -/
theorem ballHE4_24 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 24 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_23 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_23 hr hq hc) trHE4N_m31 1 0 1 (1 : ℤ)
      144 108 48 228 145 49 13 8 19 72 54 4592506210533990878475586370889911121839945220011431016532287112507296774169753263580499366574416849653965623761170652563685090362609042573529054676972449030705891465409457016058616828596462735435855820165552313381897151909207613858548042274626463030756919333326250439795247809568048006076610228675119772078018825848919176877776181664348019075180904618779684108875455109039509098111041624542399008658316548979002012765307271902115513299553813073312156651450211492691708457989003813617044748687979768966422344772177556709893802167977948297181620079768887756770177610501664200843093582574099628331565172450602340329746203894606390797061324800000000
      (kronHE4 228 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m31 kHE4_m31 (by kernel_fact) (relHE4_m31 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m40`. -/
theorem ballHE4_25 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 25 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_24 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_24 hr hq hc) trHE4N_m40 1 0 0 (1 : ℤ)
      144 108 48 230 145 49 13 8 19 72 54 10824382361395912185737388564359283372907659214962064200536215335696016074590936007072799195340548613191693898357263651550834677423726232530012548600291850200283524609639558723910210763462218597681515406325023885738284092249294238253663928422952164217470793990565428926170918268941837487061730167147418424057582184919383443071133896419555783807365947065832153186876960299582914040589425635155079299180183551861387251280578074666904822139167619070158693514663534274395185287564832450306679564328705031988110493264805844237962580034548847791673703132411564031797704971198496506732811364807718786986493498328717649497129627970188410442953523200000000
      (kronHE4 230 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m40 kHE4_m40 (by kernel_fact) (relHE4_m40 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m41`. -/
theorem ballHE4_26 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 26 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_25 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_25 hr hq hc) trHE4N_m41 1 0 1 (1 : ℤ)
      144 108 48 225 145 49 13 8 19 72 54 1324877345338953522710376791125997473625447582618831128768741791657130611760061477981938301580963367641494994996433868912041161046884717465628540046108129971064582366548838821974233460909364589756713170251296583273228906946268787454274668597269361159827685488586126828782204263349736555677255876139016855541873433122729840278091124696349778202094233570831066364848107727928811129140943032514541243993147051593542470642130747167709530397354328147693909876595902717531739264237458079102531970964364099126683047750914936346070685256982238906881611879574876237602289433240348008955232309750280088980554514206409567624265629300068749356533022720000000
      (kronHE4 225 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m41 kHE4_m41 (by kernel_fact) (relHE4_m41 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m50`. -/
theorem ballHE4_27 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 27 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_26 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_26 hr hq hc) trHE4N_m50 1 0 0 (1 : ℤ)
      144 108 48 226 145 49 13 8 19 72 54 2910068907613427756605210040499429084713126206858717354737192210373706463137850859509661768161129019764864476652052864928386156968358366464803017477641362047602628012238709862418208940454461479156126934773401720063599300437917729782110172687585619776099538219783105167632176885083351492787534680122696511559056644050667100513450110455744401781595459133882912974071499910101221532111056430280489970913856335992278533233809339949348568217854701129029735118569834114504882305663936952286421067228872486876082885675090068840240514121712832204433497842141863616310812735170519075440515525871937008911157852371549530977293679458883515591614791680000000
      (kronHE4 226 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m50 kHE4_m50 (by kernel_fact) (relHE4_m50 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m51`. -/
theorem ballHE4_28 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 28 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_27 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_27 hr hq hc) trHE4N_m51 1 0 1 (1 : ℤ)
      144 108 48 222 145 49 13 8 19 72 54 548496270571184160123038957718790739039988973568409935124229916336585602893745103885025634400699040059377874801937814040191776274506352127105958240256331101636359871117099690525977207153012496000974487978002812904661366873379090873926888310891748741962164513872661186327467442032279913327646176934339186337969855915514958726909933776052237339317070377038399885508258177263217635067004764444483707775747694907848240295195957483486979108545774823012823729821172119792829723247555707164298587020855170190917564657671779013812659665683139780916641852558779099944907733205038257717770245489899099348173222681251554609953751440806542302615961600000000
      (kronHE4 222 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m51 kHE4_m51 (by kernel_fact) (relHE4_m51 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `m60`. -/
theorem ballHE4_29 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 29 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_28 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_28 hr hq hc) trHE4N_m60 1 0 0 (1 : ℤ)
      144 108 48 224 145 49 13 8 19 72 54 957792592472919161797998098587097135324719390192007840186257885590953789251722869943047809230732125360478778418935383151500714157902119747342935730945164903894105995471514735730559477043436966932628318072869381056540322939621197050373956666909274807521632475127988812504182769822608393976761055270752395384374028954284370466227907340983884568639437486702309582233868616655350567147681018682198744944199840866214248383396760921479616022667302731485343100282514256218032420160345457876490896695022065784072437635071011370397937300455638573817805253627369052477331915076972838837868560946436434946724305583472815155774096192262880688812851200000000
      (kronHE4 224 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_m60 kHE4_m60 (by kernel_fact) (relHE4_m60 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dp`. -/
theorem ballHE4_30 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 30 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_29 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_29 hr hq hc) trHE4N_Dp 0 1 0 (8 : ℤ)
      72 56 24 127 73 25 11 8 10 36 28 980773858914916437689590526298308828791380058844552104645419404550062057145706302408246531176427829388631595970534636757161980282992471689437348092459995738012842648803068106238984848123644676142923580942195497001722672493120991843554585181940796851165033204175756306671787172801221936537480275072700909449379840000
      (kronHE4 127 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_Dp kHE4_Dp (by kernel_fact) (relHE4_Dp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRp`. -/
theorem ballHE4_31 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 31 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_30 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_30 hr hq hc) trHE4N_nRp 0 1 3 (8 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 984233629626928443460312230671113099383217131603449935655896449766322954243452782964074283942015242296839813118642219714643062881137631281581126015350706336346627792600669518795696738459910756058349017530195125627017872719851651129491951708224441694444862965469488347940278023822061825618957744871484893618503680000
      (kronHE4 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRp kHE4_nRp (by kernel_fact) (relHE4_nRp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZp`. -/
theorem ballHE4_32 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 32 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_31 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_31 hr hq hc) trHE4N_nZp 0 1 0 (16 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 2010030939234155768983328319440851210778982961171829668925935888971360161732247409170789826265432995219986266691046762592646556581124722427611764786009153225142941690348696281246078758523592575970037017588459831918421877954372250948836990335102830766265795186956342566744649672077411497235538244255870609260544000000
      (kronHE4 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZp kHE4_nZp (by kernel_fact) (relHE4_nZp c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DuP`. -/
theorem ballHE4_33 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 33 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_32 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_32 hr hq hc) trHE4N_DuP 0 1 0 (2 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 252806517436017566917517803976030601192386665986594889631808342111437444187227244438658185049077263231272615159031461571658028827773657167609980537904527121293334789494514995849267909273853969336588321510910053337839901693877572712387542637050179829963215148158720563085255284781108226034840649827224586645667840000
      (kronHE4 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_DuP kHE4_DuP (by kernel_fact) (relHE4_DuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DzP`. -/
theorem ballHE4_34 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 34 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_33 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_33 hr hq hc) trHE4N_DzP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 1000600583423811396074927157414426537284802545772153844347446607718461163737628081341520850594900371566727242319999240725458102345923338360532516876736787614337331221069669756889793748395012464350828062403373128598464220807940952799000599005707335877490761849840088342253447730231720856901883986035440098769633280000
      (kronHE4 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_DzP kHE4_DzP (by kernel_fact) (relHE4_DzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DphP`. -/
theorem ballHE4_35 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 35 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_34 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_34 hr hq hc) trHE4N_DphP 0 1 1 (4 : ℤ)
      72 56 24 121 73 25 11 8 10 36 28 507382680372405033593062557005826141807451176851028271646823812986449374722055967802056778465383876779595173982963131085488832844151089370680733331183999572275829854281933657814567965353950947317896741379121323308021975441402722322399485256937201703820286069926547575009193720152672364495737120874528147326894080000
      (kronHE4 121 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_DphP kHE4_DphP (by kernel_fact) (relHE4_DphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRuP`. -/
theorem ballHE4_36 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 36 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_35 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_35 hr hq hc) trHE4N_nRuP 0 1 3 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 991189816803471331359884126493006542754560640897970772645307384773346782674002769706620829487813261199900794085671429060651394017286544382242977593810137590810136417460959232446312017380928672608750195355577941635163176742804630313792831291957448368690407187066464075622178296062959495185864456776820627844628480000
      (kronHE4 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRuP kHE4_nRuP (by kernel_fact) (relHE4_nRuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRzP`. -/
theorem ballHE4_37 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 37 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_36 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_36 hr hq hc) trHE4N_nRzP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1011047092091196998012347061965665839547052824463827606001718100756549096808745309154125775950878881000416137499382183715969328488565722213565717913504170193894074129404711229141782075224873243333725647570650088959588555056162059989859712571875717846536450213022124791925337724547269164496614711121920198684180480000
      (kronHE4 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRzP kHE4_nRzP (by kernel_fact) (relHE4_nRzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRphP`. -/
theorem ballHE4_38 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 38 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_37 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_37 hr hq hc) trHE4N_nRphP 0 1 0 (4 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 508516865245252982341977352237257693592065816670262407885792444221877535912185131502823523682699926553824039048632700138481193816467101894063545996678647137636145359643995303562046488771225570106438538230149807703599949157531043542643751575714722704300831502502182688961100713721643868000694215611080085025587200000
      (kronHE4 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRphP kHE4_nRphP (by kernel_fact) (relHE4_nRphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZuP`. -/
theorem ballHE4_39 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 39 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_38 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_38 hr hq hc) trHE4N_nZuP 0 1 0 (8 : ℤ)
      72 56 24 126 73 25 11 8 10 36 28 1000294367994526106717802266742775714130409186054243488121809495455363581365902915443845491151092467197104714853694204055674967041191516735865471846971513999549232245950690908838430830061401425851534637808457940777637274354121779204648517626064838634148027208539655576323070494989760737238579064923043705410027520000
      (kronHE4 126 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZuP kHE4_nZuP (by kernel_fact) (relHE4_nZuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZzP`. -/
theorem ballHE4_40 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 40 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_39 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_39 hr hq hc) trHE4N_nZzP 0 1 1 (2 : ℤ)
      72 56 24 124 73 25 11 8 10 36 28 244417901460936338843603974166925493978278198834746369096988219678261125632767907477360541126243739988653812919646275863105260476362231725559371381035461148094118098998548058892775392312678504059519574056289039056907155169279094749440693217473780848811157899967952326879030432811165010169464545068362116282449920000
      (kronHE4 124 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZzP kHE4_nZzP (by kernel_fact) (relHE4_nZzP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZphP`. -/
theorem ballHE4_41 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 41 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_40 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 57) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_40 hr hq hc) trHE4N_nZphP 0 1 3 (8 : ℤ)
      72 56 24 125 73 25 11 8 10 36 28 1003191002639642868042027054533597316106824797468159350657382808835961159876988485499501562503146291008668521281780147197189225177486540199147325129566790815508207248163203075746663940172015996284020663947680710140251955465215559240745386454780609513799618550802548150799096521898607346308106022530718149807964160000
      (kronHE4 125 73 57) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZphP kHE4_nZphP (by kernel_fact) (relHE4_nZphP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PuP`. -/
theorem ballHE4_42 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 42 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_41 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_41 hr hq hc) trHE4N_PuP 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHE4 124 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_PuP kHE4_PuP (by kernel_fact) (relHE4_PuP c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RD`. -/
theorem ballHE4_43 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 43 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_42 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_42 hr hq hc) trHE4N_RD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 204047172513993362345682551610534309724531498358267965229494232997327122746945051721976857950332776284093328002810367994885223002757705430305806751210261673039758196038204159734849308136159068118653823140930162233443944596778378507700131752203268594834806820010566731157399281960707746277336202626101567284883034357677014282504886777032773740417667358887824357462197374544987256636852190727264881359493209835401009166097500333544684379395174977612377129425908143319697272178117180739680936564509363063117056514339619029740133768641766539726709250938546780344928266079554988792677523723165554491922032959378982618938245894730062194036640317440000000
      (kronHE4 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_RD kHE4_RD (by kernel_fact) (relHE4_RD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDu`. -/
theorem ballHE4_44 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 44 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_43 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_43 hr hq hc) trHE4N_RDu 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 148129122933664293463466123075865968913775244851468922961150661750575078011782234724505107211106386969353469342713603076891886770959249939662119975330744322370558209185130598221113815758049510106065691064166483694653405672027165341023859460786003401094651810580709922615478209546135385521283792050130761774367364924929680937915691872604752885581412819974764221882299386518718951182883837148625196438749110660182669711177939421855407448938720447866871202866358329441034817171088071128584125671827326441151590011546955271941821227679300872380855363473317834535912696759728294290315672377894869661076101488114091795367332763807116573850562723840000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_RDu kHE4_RDu (by kernel_fact) (relHE4_RDu c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDz`. -/
theorem ballHE4_45 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 45 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_44 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_44 hr hq hc) trHE4N_RDz 1 0 3 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 82227180611442224932475078025158070912961773503848671056791577623349078090335378048362176068165073238468603798263919238142913928387276791258980614632567085694490746375848810662367335362941483743909981522463559254280487211843176100712422514163861244932487175996858159245177877732097000881486251918720656442725558079696241287707468608714299326507817183393811686961251204863440212248087425190931271439848360588930090799735302126911917239558228333538243601363163969072678472426028365797474797633036876177665386975407746001960502763030422232593938988219960403430206662304925189616316571124973125975642807273723645335179532433830155944855978639360000000
      (kronHE4 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_RDz kHE4_RDz (by kernel_fact) (relHE4_RDz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `RDph`. -/
theorem ballHE4_46 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 46 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_45 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_45 hr hq hc) trHE4N_RDph 1 0 1 (1 : ℤ)
      144 108 48 233 145 49 13 8 19 72 54 24275600025670072020327417129365780617913479479375192306209454368609482384107360325006260264902039717521599385646566125934853350071991508172327370585432311087244903058926410443534683581778586997625665099155619738441808921329365589033935988667301493545419608772885954493903340530914644619941631695450894578161789278884565758164598815437143421120716672359167480282552125397271315251893020391804109146305113301932222320116461918113601122399647107226481865516068043113178946918903850919325983930690601405363785019884260603883917730683980657713149142661282412689941441045218473767282469008860208908664485822041527193818619794311927700949995356160000000
      (kronHE4 233 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_RDph kHE4_RDph (by kernel_fact) (relHE4_RDph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `q`. -/
theorem ballHE4_47 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 47 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_46 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_46 hr hq hc) trHE4N_q 1 0 2 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 940934179470975033936666678473802268078453603475713967660071318254898489060065239238697906282337881965853835771500979655314459211524150634179583816907418725385200883599545924920011310844720119226661114198742328457936479393297363921938784479497641392417006884511526935134391152392370730234156088454046890676197665085357613568103666685018079637326821637006151583386603575508692678300039196623292260184505744819353937280298531856756370387144072170711243321523947440716987175490844392543862534934352991402253170289498407381479507811326564999889997021429659390311332136655582445437758242763537292922606179776492105767876287847907275271881044787200000000
      (kronHE4 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_q kHE4_q (by kernel_fact) (relHE4_q c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qR`. -/
theorem ballHE4_48 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 48 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_47 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_47 hr hq hc) trHE4N_qR 1 0 0 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 2871215902195755042497690575000591388931920447595419962931315109986020658547354435059179710136002750061197769531066521330388801269875358965546236838465474076672979614884429059570049085611580739679061537140934672316838188832142371592566843618025960743250379153076842901348085035319805640381813601417537540422614990477000685873092090620788341149091171204816568021716228782144403605826352364701211687504517220534884774251746929012750439217015985725781591103573061173882500746842227646520737277523811692312285454339478721447245421764712364197908483721560096282222794065418668723328599449697301934695282195516309653867272352071470187774240652001280000000
      (kronHE4 245 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_qR kHE4_qR (by kernel_fact) (relHE4_qR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qz`. -/
theorem ballHE4_49 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 49 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_48 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_48 hr hq hc) trHE4N_qz 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 529886002540773451230043826772982019941962315502300136643959399775963894929518430143463605902067688115639165633051267039793695490349432077495204867691424795738868931357462272428649268501175101852855041234511184574522049927392194048229517996348502680649097836399595850823930321427470320243749596055619436630632464888274283237168568737747220853645400949170844474481121589006149274836638664862047298894012473386824419825759580954238012145860849250602551361475667417850686527370407563822746976955452694649232405854297386667331746834704924543853513511654001769366821456337003149867691933867626326389501322250431111097334740552084837915824352133120000000
      (kronHE4 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_qz kHE4_qz (by kernel_fact) (relHE4_qz c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `qph`. -/
theorem ballHE4_50 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 50 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_49 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_49 hr hq hc) trHE4N_qph 1 0 3 (1 : ℤ)
      144 108 48 238 145 49 13 8 19 72 54 147305748352117522025290291158264829085719468646690423247080157136969700117008330913342096555775635858426511539838486399257268954780711971713228959258234112496093612011082950910453476856003776077098775063200958414781118774903807089559797298296301556580839356917903256992756368851487998014101417382164965862371024319749878777751844210242057416636555132619259478534964138582354628970289692970754051066715184651189601311688002041935294844590938913695796360955186800884940528160348462361393831966308610799385181810923461007428627332620183496982010523548597925288310670653459169951963230909724159256755758881198595925707744223062832807252580106240000000
      (kronHE4 238 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_qph kHE4_qph (by kernel_fact) (relHE4_qph c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P2`. -/
theorem ballHE4_51 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 51 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_50 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_50 hr hq hc) trHE4N_P2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 4438575827404950045787517243882317842530468169057603010731705741046939266628382959256316009073286659488729450031813969980964294122592954800731474352523772616874428122504990713217635243518438242233180427578499069929067018831472475783650857898819103668729866863587408321331698472893384222259095218753584257562195460932927239455867652736674508046612302515934092504658618408725246673200881854485938055683523459232967934937304156727769688055599920821267704461273984776341010110035410298912643181154984511931816885881869835068662233606216963606346520943218524228146396305792823338862846951253360156830001070717829369520372449123745771306614029025280000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_P2 kHE4_P2 (by kernel_fact) (relHE4_P2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E`. -/
theorem ballHE4_52 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 52 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_51 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_51 hr hq hc) trHE4N_E 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 5394736920741952885173010929426237888037815539962089605107339080757822811461253748509664324604561717667749105879079865949168952589237698203846702193870771869450280073373567224204244051832478093426635010519273842154332290419852352496194319589603422196752887615923672203722398231472667206164239428286990877433776779470696047211553874026564016266011031381271707424964419959012230901648727983128253773487961909623073443520558809213798492691082103456007919134191761366006606440175837083014135310040382760215274832067324123369073011813138275336272057390352965885614381919252348272063340679127659706661212327914082696748093868397090760454555975024640000000
      (kronHE4 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_E kHE4_E (by kernel_fact) (relHE4_E c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V0`. -/
theorem ballHE4_53 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 53 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_52 hr hq hc)
    (step_exact (XHE4_eq_V0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V2`. -/
theorem ballHE4_54 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 54 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_53 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_53 hr hq hc) trHE4N_V2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 16337582831723343901163358603181188304814368856643775602374253505190364813914567263200294741638726545184618902977992772748938360388262066912879935514398679372716850048804749895228463436487753165666769416750827063090263772960016704306564393276604195543705162484387546998373086274229951468690063415082488511140972136004098746975499218737772998539302989916985404175609622742347762335643257206858377549636782577557309790503561043771312078322926929475726116954635325221821139886568950827773065075574205742848850326157140304096823065913931614227322760361835671175665124742043626613338645421295397776111755934732660160123561052644984538911222005760000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_V2 kHE4_V2 (by kernel_fact) (relHE4_V2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Vn`. -/
theorem ballHE4_55 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 55 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_54 hr hq hc)
    (vnodeHE4_Vn hr hq hc (ballHE4_54 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W`. -/
theorem ballHE4_56 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 56 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_55 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_55 hr hq hc) trHE4N_W 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 177228293538678482391773587381668369442828430924553684621700051403875040276072802273498907404191288107792625090731600192415933758875702507727145211319696949803654729950385316425605582086030511793789100929195551461565718881030814455971586239229828236914559635012011407974482359154257053770627213374930143530784681681861959782443296614351936681736049589355084813346698238076435263349911930515299834165869307673299107870577441871227775741998459784827209492668194371751931456342181449647908679342608613270829951842398081726191194144566265371667563285690996241410295307632433565639037500608810303335621670345448538520727467809852090472218346127360000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_W kHE4_W (by kernel_fact) (relHE4_W c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W2`. -/
theorem ballHE4_57 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 57 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_56 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_56 hr hq hc) trHE4N_W2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 5316302226894027128302047922738791598446929730660826413658472462492308641659961664210048760502392617940143636253545702595544687637861427015080800150975193115519374099322592662648387562932232657811052948083308608561664563161450540381254397751009778976884956171295948287111959653067024579681963344885604179059228931989877524573858135481472124906482722980148239363210422413951016485216038512819416330181271207092475447339448096033220719567354607349082092378429911173322862674722387010213634915639176855037084738722677744042753106327067190345370661455801841767727349867272647546817932663690108198791729614388486724166332702436226747093125158666240000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_W2 kHE4_W2 (by kernel_fact) (relHE4_W2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `W3`. -/
theorem ballHE4_58 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 58 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_57 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_57 hr hq hc) trHE4N_W3 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 20304324278908136031608703790452019892231535658521822417011293689168262015487887069535011240007732059220066344954963559396342478822775943772530305372309228669127021072563939748546336980355759614484285061929939536264346375673434272441684395317008371231290972137202588253351318157693832722073063543166505101083426880991084504799230423075762000814292745104028600557033791548022055230189288252537651516246441625530540191698761046962573248625071188912903394776015696652870420972944891076633663250085237301456017977561751985937031834956633630822704555082311404501908627742299034520451290232382321361250825725901633080255842200613653969813722984611840000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_W3 kHE4_W3 (by kernel_fact) (relHE4_W3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R2`. -/
theorem ballHE4_59 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 59 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_58 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_58 hr hq hc) trHE4N_R2 1 0 0 (1 : ℤ)
      144 108 48 236 145 49 13 8 19 72 54 106466869164987068801047226549929296514190467965398427977777578163188004946836185849380129653184751975045041564933721984813909578189328269632246754209987843284106107608141375894071225804273768245196314700516492269740037640295710193953446449895928973713229968380067128320269243134193017347810397083845427224198356934414276151151191084144672939622875597829723979795655577084394462933819116332030063672145849273272186547879123170103222677197333710528792995464783356062522077888312120070366076538462005209367922016240737730953884569599073660087363963705258684701366377366369428407264631410542799203162583731129903241097947459678894289920427294720000000
      (kronHE4 236 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_R2 kHE4_R2 (by kernel_fact) (relHE4_R2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R3`. -/
theorem ballHE4_60 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 60 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_59 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_59 hr hq hc) trHE4N_R3 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 188170268106280706021377569409891965421485812526665902217859732544333235261297861912760596208154989349144205103206359768774068546913771290012739684749646274657534975408927913695381940825646098400540420776494443987953191835647146903625899708377015680663356945169640820729953568694288257031674771918061378824762302493747551175007679184919120584455509930314614424559238156851834658383708671289654603327750552176981976542321032767904344058080573482163453124674538911267583617976127230988640577608504011584980968895659266201269881125676453469534565172336693615625492313174482138284638514862656499792158256113642284090009504998503375528939046830080000000
      (kronHE4 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_R3 kHE4_R3 (by kernel_fact) (relHE4_R3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A1`. -/
theorem ballHE4_61 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 61 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_60 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_60 hr hq hc) trHE4N_A1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 2838497247144043027279536426466440406064753388931394198290278559264239691120611951899245121561122640580375068883139732032539795138726114767210457737761574988266655470851024696643841856703016234594689870848259576390764603254373949720368554855177427063755112307189378475787917960245331942176603074798921252907958841396178188191912527624092559379073315825464824260444152098697004175191714936961163800718485751435088388839379321222416426693875245187440057385849239919447603760267838762012655038174881805622233850874010401012907270515167662162762452995765458104505730979508847024899804865516672202497120757503183028625737813027809865153434794065920000000
      (kronHE4 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_A1 kHE4_A1 (by kernel_fact) (relHE4_A1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `A2`. -/
theorem ballHE4_62 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 62 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_61 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_61 hr hq hc) trHE4N_A2 1 0 3 (1 : ℤ)
      144 108 48 237 145 49 13 8 19 72 54 217634507918421028479360328028019709892866587817050037111133985980481881739793218635313448129022345286570016016841902373135162572089696169173455674056898441996263015068944498438529558997231188552505591719433019855464674823833615311613688474922947514791946794321335245597103036349287772241731328638593099855651328023727442412491698211593850513560185654442797924383674997073997715595931425589447672905195766593257848773054958583809277698594919988725380503878283569920688152090185391372584627725478409021730280435647219721792109566786819145419000965016614678570953397800869079781852914021543663740878254485151524232394691667619455802779694530560000000
      (kronHE4 237 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_A2 kHE4_A2 (by kernel_fact) (relHE4_A2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K1`. -/
theorem ballHE4_63 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 63 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_62 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_62 hr hq hc) trHE4N_K1 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 1327519804880881754156481394095804100078307601017359079066254489374148126249590109820699215232494637622488102262390789652116636944715633028046928653645276084912479003134673746248902170454814254013232548715438606309701898800746330701100412967136596014082422051160416310598063108651433258758253875466008995431506629053576362105676849124018099110632802534043641921455615899741927188385917218693995531720460466097755216085204247813903190530704442861606503811375153782024867531014926886363466402440237636630323830107682283849294613311949590468312653664465515834652384078453982942224879749847550371363841597752302195262043009863932369407422601625600000000
      (kronHE4 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_K1 kHE4_K1 (by kernel_fact) (relHE4_K1 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K2`. -/
theorem ballHE4_64 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 64 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_63 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_63 hr hq hc) trHE4N_K2 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 907026389954976044641942001056881034705716322334694865946897327825804762679318367907614211794428957843478609443239301992579568047263044926166029661804787006558813149093459983802906118725693641155487657625233728500264157047767602611496670364168702895151068434438142436689213637055851748827563136548446783381652407950269714402020595091839113176363286091361142320116776185277985671918896949144796635176131261517422123945726737544203845727460645682471849288830252659575404041461937398721614375568525686984564586590037437810877996611773127457532388920158462114634142922433445618556600824877137217518711361545360225331409239288824185176793599180800000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_K2 kHE4_K2 (by kernel_fact) (relHE4_K2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `K3`. -/
theorem ballHE4_65 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 65 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_64 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_64 hr hq hc) trHE4N_K3 1 0 2 (1 : ℤ)
      144 108 48 246 145 49 13 8 19 72 54 6223442706444742343602633032153696036341949034253308384899932835106991495345045982867673994466183559017839424928878456315934794664064681024653222445928065121359624622611677839979941129399012721063657853407670832361038756040031666706833608033172131317139418783663086999183746874681698403550487649076343244891422583732156174063020977007950905121587062107989148504177046632385965925391332798126617214433118113354232148509230984640160627684857902170533196090065317310744734300971559284877783863170428222755574015893329927960338223291077277077908864059921634441889685354920126275005349500934869849737368685003288755893393894773766100388161530101760000000
      (kronHE4 246 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_K3 kHE4_K3 (by kernel_fact) (relHE4_K3 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KD`. -/
theorem ballHE4_66 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 66 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_65 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_65 hr hq hc) trHE4N_KD 1 0 0 (1 : ℤ)
      144 108 48 239 145 49 13 8 19 72 54 768207573911882928179990360543336872329809246395416241498514377624957841577337298922870607197889172040886170360957008574657113863222926076812711256677357131086569819569911150205974896037398466240689461184338598026140276216641422488759813569987187028295157878591019332799898562281812491084993552038982936911180272234790914551411414552181025803614744484883610121929123299633466527909248380128205291502550862423579455782143701365930199627453228412192412487182724287645418394474710514988126494618728602406702064328122733842282754800412570971746729034021187766710316044719129328641674408727893208239238067666062725417947242579278965212523224104960000000
      (kronHE4 239 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_KD kHE4_KD (by kernel_fact) (relHE4_KD c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KR`. -/
theorem ballHE4_67 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 67 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_66 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_66 hr hq hc) trHE4N_KR 1 0 3 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 1389528520766178345566246009282547329990440665402276240500751212134492775330781335866707111197400754191082950204435250518902221268491188702485717991025668965938045583098790901199458799824233628876142967328865776198283274645810046906849467790702678101827289529878875389825263776726142842371240079102036421550719150560732183287646489947553325046609170828975818371692830461649654816791421581082390034858105799016670852344669016240297042155125402929316369798133970301710006822798562904806477910290438568694493033497179975834324751232987625486398913765244289942469504537654210424640487571327769222305597647494609524994529672843896009736087436001280000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_KR kHE4_KR (by kernel_fact) (relHE4_KR c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `KZ`. -/
theorem ballHE4_68 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 68 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_67 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_67 hr hq hc) trHE4N_KZ 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 12675490624925708153781716844314042582144510575811768027313807550413001298311533167339767936145758446293486536365542507995226966719189179706057842577579039137157425615326171473539342628504035111358692668276554763863539232543423368586524659650165450478964913524384309883744851964178544930702997873476229472608429957648356062940834606475618069924734953736123151098459411149386506805528313982280139239956802921641405111174199446812444527634075464781463666334201553618709694711605945088908329040682713212468091858360730366968763219364487733014377095908689126222338955484614766970480841343136222106574219775852762627865323020316359945800760824954880000000
      (kronHE4 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_KZ kHE4_KZ (by kernel_fact) (relHE4_KZ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Dt0`. -/
theorem ballHE4_69 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 69 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_68 hr hq hc)
    (step_exact (XHE4_eq_Dt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRt0`. -/
theorem ballHE4_70 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 70 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_69 hr hq hc)
    (step_exact (XHE4_eq_nRt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZt0`. -/
theorem ballHE4_71 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 71 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_70 hr hq hc)
    (step_exact (XHE4_eq_nZt0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `r`. -/
theorem ballHE4_72 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 72 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_71 hr hq hc)
    (step_exact (XHE4_eq_r hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P4P`. -/
theorem ballHE4_73 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 73 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_72 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_72 hr hq hc) trHE4N_P4P 0 0 0 (1 : ℤ)
      72 54 24 124 73 25 11 8 10 36 27 0
      (kronHE4 124 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_P4P kHE4_P4P (by kernel_fact) (relHE4_P4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R4`. -/
theorem ballHE4_74 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 74 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_73 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_73 hr hq hc) trHE4N_R4 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 354658601444104392407765894001511147269876566485679832153895877719109007280490340954562365124833507014552417224473942598626160277868031671381029603236519550935411415582538947772798260227333994045664370732649995083019238676724207975869460453446140427829233495729477248692874941731128394828240295000545430958637124718226194637217436549912258398935346945553413978447742885363932391022436638111294887500728162857352634384227615011438370959838048542135941498175450180619008932208462586990817394282288478021550555952618025852087347108162291538943864888834205411713780194510851327918379747293400465965863233826852653166365274914605368946778733281280000000
      (kronHE4 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_R4 kHE4_R4 (by kernel_fact) (relHE4_R4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `R8`. -/
theorem ballHE4_75 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 75 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_74 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_74 hr hq hc) trHE4N_R8 1 0 0 (1 : ℤ)
      144 108 48 242 145 49 13 8 19 72 54 2155224255753658706099138498945790524460693715955199086241626021665535345709814944084391823513712338169139034273915294708377423835493247118075783322864083497876647884190640762837168823057590959893435153684112327245619875848855636759915004466873589947223006275181570347395852533950003006033313575790609559337323785738314213362697451737464615890154137048591605968499035373074185003425186007273717309777878512568541742413008739039740624239441376195712190879253594518317082150454168655757324291937220591427534086249170023499310471148826554753983187940078077632409663249232199635507933124839278187676095379341754691517532625872642181059940376903680000000
      (kronHE4 242 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_R8 kHE4_R8 (by kernel_fact) (relHE4_R8 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `P42`. -/
theorem ballHE4_76 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 76 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_75 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_75 hr hq hc) trHE4N_P42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 11818813739924770075145277615338281895133863986219936425235246584275677542671265656244899165569690722834425261555694007809079227678882456573344047049265150326980156316042221707105108076777378106812197376767120521377610691488244608866946069396133116683781026370745230977053404883014233614814126004169357400345402877054873606925259094567310257976181850385479106943501260375857222496130002255795870597851691548007337798594192904159157567469573685136454138139477539358780378257337238170984253991373277709360561605623487022694024867949837180112244762634090926911966853128265011305534884578426599534339692185484907168078764295535020473192671462031360000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_P42 kHE4_P42 (by kernel_fact) (relHE4_P42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `E4P`. -/
theorem ballHE4_77 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 77 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_76 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_76 hr hq hc) trHE4N_E4P 1 0 0 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 9316338416315234065267836615902197255058275096857413036792357099435975134506261753845423945209003759543395396475455496912492076901633234658585673829004879802587114498488045912717961997612490113795873357066370810713760908045435329110276965250788878490970828031096619133980888579870352585406852938982165877120967924605153362708638994581632702303553554459113766685558170865451379330218850575404810509698715596869135343097503879920705781825901651820646003120446130283353890037203846100971810216121139193293938782789043236266604929001839373441558736852997391002951805285576405901425478522477143115130013718190561144295622729170556882683672888606720000000
      (kronHE4 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_E4P kHE4_E4P (by kernel_fact) (relHE4_E4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `PP4`. -/
theorem ballHE4_78 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 78 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_77 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_77 hr hq hc) trHE4N_PP4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 7246685252065328144288004256235185793178055191227914364266497904828085073649220041687888857301446590833828654711801016045943107592530302053007000051691349708377217927540971620217982181085501260634056386677270637812086859241595929505812269398223281858724757858922031910376172870950252917890575348132193994097163436746395036089200407890953263531710836073026840898122234738651955702695948742418893857893599933286916767383888839337431371367515153027160772363462630030917870934252964727909358735609042848485734714453800003771479387170068785377618423397145906287235794173561087683316479299843766162567452532281813775782253969257319111377988406476800000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_PP4 kHE4_PP4 (by kernel_fact) (relHE4_PP4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `QPP4P`. -/
theorem ballHE4_79 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 79 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_78 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_78 hr hq hc) trHE4N_QPP4P 1 0 2 (1 : ℤ)
      144 108 48 243 145 49 13 8 19 72 54 7717795513575758520620462403300590344163258827560437618917972899770302996357127552483634343036709024887991646424041075737128580637772138497791608999825609648240150273612768655056360939993017574086588456728559568149477175851320703081004201387350955968821933593869550224246826430838266171767096554200569748638570842660218700188629717193438544802589418089036521374281156254420382775230848440861712032828704655845834586076063645026178990852107944674092537823881236024507309792990009865600019542761361764987510017687436501459934590375255934093693299304301632472232757560364279878051623528133333714554561044755501108627295539161839208958342232801280000000
      (kronHE4 243 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_QPP4P kHE4_QPP4P (by kernel_fact) (relHE4_QPP4P c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V40`. -/
theorem ballHE4_80 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 80 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_79 hr hq hc)
    (step_exact (XHE4_eq_V40 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V42`. -/
theorem ballHE4_81 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 81 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_80 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_80 hr hq hc) trHE4N_V42 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 650345719971907360409343632952572442066469192746910458204141098742113965849586316548702793757516347059564892190406094060940064579482621913772668059095874455026066514375047421196243613065704460297383823177678124033048385957655339209673509982895794959864208886711118524581039216583628915608524726248576790844193620200359026073696621351245869647359932333762062330475058963801552437274757504167840434906538890843558399672968191964933357130394968772603699397249387992240734691782563267834428749461381902431049929724217868155814838442166336861091739723823642838626375332051063279929585554970939330385353669477506357546320014557295307500027904000000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_V42 kHE4_V42 (by kernel_fact) (relHE4_V42 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `V4n`. -/
theorem ballHE4_82 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 82 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_81 hr hq hc)
    (vnodeHE4_V4n hr hq hc (ballHE4_81 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `VV4`. -/
theorem ballHE4_83 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 83 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_82 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_82 hr hq hc) trHE4N_VV4 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 1138045520405278942990744118025168274453060911252652247854961257213080734039310647360563459784788040132104486746467027203069706319170854800133556026605830726141972957597790162669802268515512085867764613199661909023624429440983540753990125283689678027679077892751662780790374475219886804367549142114301522210445203001807179140566203191640888314317846876849807937141665388964120227611723969399370708902821942772829423052147685133070771492417219286392990288958523792508460268147506628820157495495280791812097395627330901449184721632762654039181058062464159225466972190668477685862183341401617343622696234413606472157693976313989173395964559360000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_VV4 kHE4_VV4 (by kernel_fact) (relHE4_VV4 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Bm`. -/
theorem ballHE4_84 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 84 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_83 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_83 hr hq hc) trHE4N_Bm 1 0 2 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 31273046481095077121401927616729460870965317676915802643618778075694642399648001396541606570709556946606289362616158281205134933907770143957591853557395763896502082281147773308395259787668633914693015894827209213231272049681653676674049539767939362750930642277986081696135673947638683109679180512360546927301494998857982145215887282268275630289686469799728561207453555778640344175205357829827249335575858899368743289736338548391022858305324869994811704804435521440560773081020989549527192499631365990319188154358300966658898646445701790981027710788431973985415050772352972679899901543519807321768542464474628374259609571552366560663767613440000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_Bm kHE4_Bm (by kernel_fact) (relHE4_Bm c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `lamv`. -/
theorem ballHE4_85 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 85 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_84 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 55) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_84 hr hq hc) trHE4N_lamv 0 0 0 (32 : ℤ)
      72 54 24 130 73 25 11 8 10 36 27 0
      (kronHE4 130 73 55) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_lamv kHE4_lamv (by kernel_fact) (relHE4_lamv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `EN`. -/
theorem ballHE4_86 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 86 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_85 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_85 hr hq hc) trHE4N_EN 1 0 2 (-1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 581447639278894056381531286469811003896094320000623019090920235353130858203725222358604829684008810068406188712533363079260371484053772892490931972605449255814942619610897425298966956819147236298914528921887312349253731406272055397515381413886798889982773730182273059644094847370601312943641520338235286124346586168197173571344102621974030385790217307127993584749837863563492635545340027481473862925678077053597505853327168629617334215445354000291836705398997001044755352468391717210595443351974916052085009562776205161371417269269153930216437646864410847872894362138509885161276397491078794696326652160773860726910573390895320783466937712640000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_EN kHE4_EN (by kernel_fact) (relHE4_EN c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N0`. -/
theorem ballHE4_87 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 87 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_86 hr hq hc)
    (step_exact (XHE4_eq_N0 hc) (by kernel_fact))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `N2`. -/
theorem ballHE4_88 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 88 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_87 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_87 hr hq hc) trHE4N_N2 1 0 0 (1 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 65728738983191892677179302438617994747097660125450615425539358510324471462257606607515143588599229361498733874802259778859699874308257616206056931602517070116686165656571054357739780683618130600676255152420090521111819169826176089063476869732170994446876586487189479373074612536924866725373742463742960345373761562671685768231233041212785944038847711158381006824399324324215946843086674610075833948560736542340350447656144738395706964267341852138354179338206141803214628100677789236040085395944921626806033552569741113379569782218774383766698542724559078838070651846094943489945156579494620009401140388276032323155627827880306416879621363466240000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_N2 kHE4_N2 (by kernel_fact) (relHE4_N2 c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Nn`. -/
theorem ballHE4_89 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 89 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_88 hr hq hc)
    (vnodeHE4_Nn hr hq hc (ballHE4_88 hr hq hc))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `Fv`. -/
theorem ballHE4_90 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 90 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_89 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_89 hr hq hc) trHE4N_Fv 1 0 0 (2 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 19176520023410366493336611417351900527226792467843518513983679291055665251624295622601357361396546876493467157452900199378291225883085742635716006373388451600873231254919907680231164328322122344441376616373872906514132347289459092574091080702962007292794966659161749817999813423249916188086787317168162222693129717232887623020901144151186789501398712676197114802585080548300462060906497660381360103318627977595162546749462456270461513751815318674132258008200463747148018620635055134581887401629468304701113522416140561839328906799647450683489830852423687330687632293690835968520293250313224069733082490523902646073442726858811157014354287656960000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_Fv kHE4_Fv (by kernel_fact) (relHE4_Fv c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YDt`. -/
theorem ballHE4_91 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 91 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_90 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_90 hr hq hc) trHE4N_YDt 1 0 0 (1 : ℤ)
      144 108 48 240 145 49 13 8 19 72 54 1776339088250693973207907492362903644467450499491222725777724280008666620008033559735931717901109894814535022805622030628975643568063161217206491013109015556145174044744468517741894186360441231651087393141731988300543261692296254965741325731179381449677830948935071405586546818686073464333873863857167095529674296183632013803277540050591647134827097829533942009782926169405895751767238346540828328602468303294782826805215859798055574327889690609659371687517215031377532894655849918456988324355203819886898194312030127766246869284710076530415380355053210417602232709505415458152535889292710400504343656889221191678922354674548162356471901716480000000
      (kronHE4 240 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_YDt kHE4_YDt (by kernel_fact) (relHE4_YDt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DtF`. -/
theorem ballHE4_92 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 92 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_91 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_91 hr hq hc) trHE4N_DtF 1 0 0 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 719430236945103038153581153033821682007912810937907212374642469575489841769358194439812114472279022720472335610294658665384417798987256053598219649175828203774473201958694112377627614232754976061001780601574236379108145968557245995216664133010512469974502717181947163809012785266248327965923356724748043301426779288986829488920469608719024391428677120480054749898428761972163848195993740202848362936947722415877868540389825038073218364956926227803607654614242971495493282045421863265716545636520214236234863096816526452531035870808569543952790893996244102524069975624255318625970507850079246284919166501610928934169595728557564584256549683200000000
      (kronHE4 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_DtF kHE4_DtF (by kernel_fact) (relHE4_DtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnRt`. -/
theorem ballHE4_93 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 93 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_92 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_92 hr hq hc) trHE4N_YnRt 1 0 3 (1 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 2662289684980472841242783192989939811670144472663311663549463792595700520108063103420217103709210939526105384516313588662736267673386304869799074298756312037940313886034902154074386565864774768304169511891525823166583315020718361213092426930605715987364873100571169325954912165574586320393651114520143128876282382869538791735531791723443361091797563489816301866798581076649942606231634008440554230450518529479736277431041579846449988350644607054752346113607224684234298677345877486830030581892975726967411914915349893133978170364451682569310476319635049236434709653858583311635011523430504211429665084400065029787166508402179080183310073200640000000
      (kronHE4 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_YnRt kHE4_YnRt (by kernel_fact) (relHE4_YnRt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRtF`. -/
theorem ballHE4_94 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 94 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_93 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_93 hr hq hc) trHE4N_nRtF 1 0 3 (512 : ℤ)
      144 108 48 241 145 49 13 8 19 72 54 973125105075200545604159556755659611725791911095483135384321822793191905249468734490666470546875409327432255178872871046692545993414085673882716190441265396404203114556161924093962864340009525941118087772689590226026718983381630026914625567118732289080554486654488452387012993184522213346636881131802139959081474293630366503227246877897072335723549049966768844402699678901264495193077661811577681151337642975123218846477579925022925249663632138865530651511014082294201016223524461577081474584122169569443216790505392430914783477051283550499906050194592626198307485651430695568167437911071838207525221001804798164152835029464659653905895915520000000
      (kronHE4 241 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRtF kHE4_nRtF (by kernel_fact) (relHE4_nRtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `YnZt`. -/
theorem ballHE4_95 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 95 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_94 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_94 hr hq hc) trHE4N_YnZt 1 0 2 (1 : ℤ)
      144 108 48 245 145 49 13 8 19 72 54 22787828088867750796384007092712541443434819647072325876473132309326664755237248990746800662393645119382034060058493323378063947245624545717064527662826669794195564078660122884960805546412970944292963546398724436184827205607603766075022299928923151332599364567982589773517803399837283649630502634162977037490410598489884366754980437720954150792243295144256551830149364690978792233613130653616273032654767770654703150838643017346245885239128557495655754551806299044093861356387760035791699806452227740318258269494174405423773474719435578790408674751493131901772282614784454830396617448703117843918291449557734566248293764657196191120785397514240000000
      (kronHE4 245 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_YnZt kHE4_YnZt (by kernel_fact) (relHE4_YnZt c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZtF`. -/
theorem ballHE4_96 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 96 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_95 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_95 hr hq hc) trHE4N_nZtF 1 0 0 (512 : ℤ)
      144 108 48 244 145 49 13 8 19 72 54 4551422755376587096198022958714298186561908540802072244878611986302933544137205459925264577446288675907706106813197239287399128955924432436722018302981743140500853096594348442719412029614973184475515751364188875928447783539321428375073287554423525454213408011903645768431888495341543948657777148437286047295661634541971062977303333841427375833427921652535305548886054377612618739369806576519050993294002411699822996354147863159688687228581482727518131650361884156801984158055897277387788915040429699750971462722034419270345050069030119645182401845595263138182510971316784296511707804112077834211050434571029766234719027436110196510580067532800000000
      (kronHE4 244 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZtF kHE4_nZtF (by kernel_fact) (relHE4_nZtF c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `DtJ`. -/
theorem ballHE4_97 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 97 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_96 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_96 hr hq hc) trHE4N_DtJ 1 0 0 (8589934592 : ℤ)
      144 108 48 263 145 49 13 8 19 72 54 602671343362425329765538563938079133162153055697537113618120840360815391924286864350026269128756033612849043360849648872408094344127434795835600633167276908979139108960457075814959419757081142663696866597036725109426616063650990326226560487960710016227261303757946438934529368768513373627292629072778613264053237695527271524540955391250191608407159239334626567127633387383931328674563271625025937311929543893529961664368566649032529059739258096405217435716176658386399282743213637504233934081822881285129779952109328655815299714587729919946524080194319418424607226488174221283961821440426986361233714909748662676971129426378328390043577321070264320000000
      (kronHE4 263 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_DtJ kHE4_DtJ (by kernel_fact) (relHE4_DtJ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nRtJ`. -/
theorem ballHE4_98 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 98 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_97 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_97 hr hq hc) trHE4N_nRtJ 1 0 3 (8589934592 : ℤ)
      144 108 48 259 145 49 13 8 19 72 54 717339319061273568416845342788211424078771812412727330170417824343597894626544663579508547604839350610066604761595474267592300775874875038224304554155896229299076935701702477194356872362710189811738874839816709858525778942958881896756105636527949997827936784636854714856594382760268594961005983244482396306936072787451070047427048759680361121645930873301789594047989267069817049551464500394978634769973965342894023173111235702818103139885248376365067083105531866897747847407183035775499514848265130746867402835475293292290591646705191580615707458865478493904538316670606334383297966346143029077478657620615800199937962153824205434083148812664176640000000
      (kronHE4 259 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nRtJ kHE4_nRtJ (by kernel_fact) (relHE4_nRtJ c))

set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 4096 in
/-- The chain up to the variable `nZtJ`. -/
theorem ballHE4_99 {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 99 → Bd r (XHE4 c i - xHE4 c i) (EHE4 i) :=
  chain_succ (ballHE4_98 hr hq hc)
    (node3_fullN hr hq hc hWHE4 boxHE4 (l1HE4 109) (fun _ => rfl)
      (fun i hi => normHE4 hq hc i (by omega)) (ballHE4_98 hr hq hc) trHE4N_nZtJ 1 0 2 (8589934592 : ℤ)
      144 108 48 259 145 49 13 8 19 72 54 734451257608430302271253182166858808921168882264610828211827850323155731753187241861764523074432271946742188705215512070039260287200588588722470341769971794654933395587425813503236645239892006802080817537227391974151922910763524587912455573209793478002949586522296145475418878564396160618777226061086839744240538784633954129024275063639525876616494450817561777033022785850872230613311662720483732506063256833390523733097936915834352382787223611140677051242370353636363831580679915046454098545730873536390549228992345180031691691159320356643058764675217265560736068700908151183046060539320789100757451064870740251057235806384342555619275760866426880000000
      (kronHE4 259 145 109) (by kernel_fact) (by kernel_fact) (by kernel_fact) (by norm_num) (by kernel_fact)
      lHE4_nZtJ kHE4_nZtJ (by kernel_fact) (relHE4_nZtJ c))

end PlasmaLean.Design.RationalStellaratorGC
