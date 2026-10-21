/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronChebCompute
public import PlasmaLean.Design.RationalStellaratorGCFamDataH1
public import PlasmaLean.Design.RationalStellaratorGCFamDataH2
public import PlasmaLean.Design.RationalStellaratorGCFamDataH3
public import PlasmaLean.Design.RationalStellaratorGCFamDataH4
public import PlasmaLean.Design.RationalStellaratorGCFamDataH5
public import PlasmaLean.Design.RationalStellaratorGCFamDataH6
public import PlasmaLean.Design.RationalStellaratorGCFamDataL

/-!
# The high-resolution layout and Kronecker images of the guiding-centre torus family certificate

Layout `N = 36`, `M = 27`, Chebyshev degree `D = 10`, scale `2^{−107}`; for every variable: the
stored coefficients `famHF i` (with symbol `c0HF i` and parity `oddHF i`), the weight `WtHF i`, the
degree box `BxHF i`, the static `ℓ¹` bound `LHF i`, the minimal widths `bMinHF i`, `wMinHF i` of
the fast images, and the Kronecker image `KvHF b W R i` (fast: `famTB − famO`; generic: `famPack`).
Variables `0, 1, 2, 3` are `t`, `V`, `cos 2φ`, `sin 2φ`; variable `71` is the parameter
`r = 64 + cos ϑ`; the special variables are 0, 1, 2, 3, 68, 69, 70, 71. Light module (kernel checks only).
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Certificates.KronBallCheb

/-- Layout: poloidal half width. -/
def NHF : Nat := 36
/-- Layout: toroidal half width. -/
def MHF : Nat := 27
/-- Layout: Chebyshev degree. -/
def DHF : Nat := 10
/-- Layout: scale exponent. -/
def SHF : Nat := 107
/-- Reading levels of the stored coefficients (`N_j ≤ 2^dd`, `2M_j + 1 ≤ 2^dr`, `2D + 1 ≤ 2^dw`). -/
def ddHF : Nat := 6
/-- Reading levels. -/
def drHF : Nat := 6
/-- Reading levels. -/
def dwHF : Nat := 5

/-- The kinds of the variables: `0` = `t`, `1` = `V`, `2` = `cos 2φ`, `3` = `sin 2φ`, `4` = the
parameter `r`, `5` = zero (dummies and beyond the last variable), `6` = stored family (list). -/
def kindHFl : List Nat :=
  [0, 1, 2, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 5, 5, 5, 4, 6, 6, 6, 6, 6, 6]

/-- The kinds of the variables. -/
def kindHF (i : Nat) : Nat := kindHFl.getD i 5

/-- The stored coefficients of the variables (list). -/
def famHFl : List (List SliceData) :=
  [[], [], [], [], sdHF_U, sdHF_Z, sdHF_LRx, sdHF_LZx, sdHF_thU, sdHF_thZ, sdLF_U, sdLF_Z,
    sdHF_thUe, sdHF_thZe, sdHF_m02, sdHF_m11, sdHF_m20, sdHF_m03, sdHF_m12, sdHF_m21, sdHF_m30,
    sdHF_m13, sdHF_m22, sdHF_m31, sdHF_m40, sdHF_m41, sdHF_m50, sdHF_m51, sdHF_m60, sdHF_Dp,
    sdHF_nRp, sdHF_nZp, sdHF_DuP, sdHF_DzP, sdHF_DphP, sdHF_nRuP, sdHF_nRzP, sdHF_nRphP,
    sdHF_nZuP, sdHF_nZzP, sdHF_nZphP, sdHF_PuP, sdHF_RD, sdHF_RDu, sdHF_RDz, sdHF_RDph, sdHF_q,
    sdHF_qR, sdHF_qz, sdHF_qph, sdHF_P2, sdHF_E, sdHF_V0, sdHF_V2, sdHF_V0, sdHF_W, sdHF_W2,
    sdHF_W3, sdHF_R2, sdHF_R3, sdHF_A1, sdHF_A2, sdHF_K1, sdHF_K2, sdHF_K3, sdHF_KD, sdHF_KR,
    sdHF_KZ, [], [], [], [], sdHF_YDt, sdHF_DtF, sdHF_YnRt, sdHF_nRtF, sdHF_YnZt, sdHF_nZtF]

/-- The stored coefficients of the variables. -/
def famHF (i : Nat) : List SliceData := famHFl.getD i []

/-- The symbols of the stored families (list). -/
def c0HFl : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 140737488355328, 140737488355328, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The symbols of the stored families. -/
def c0HF (i : Nat) : Nat := c0HFl.getD i 1

/-- The parities of the stored families (list). -/
def oddHFl : List Bool :=
  [false, false, false, false, false, true, true, false, true, false, false, true, true, false,
    false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false, false, true, false, false, true, true, true, false, false, false, true, true, false,
    false, false, true, true, false, false, true, true, false, false, false, false, false, false,
    false, false, false, false, false, true, false, true, false, false, true, false, false, false,
    false, false, false, false, true, true, false, false]

/-- The parities of the stored families. -/
def oddHF (i : Nat) : Bool := oddHFl.getD i false

/-- The weights of the variables (list). -/
def WtHFl : List (Nat × Nat × Nat) :=
  [(1, 0, 0), (0, 1, 0), (0, 1, 3), (0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 2), (1, 0, 0),
    (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 2), (1, 0, 0)]

/-- The weights of the variables. -/
def WtHF (i : Nat) : Nat × Nat × Nat := WtHFl.getD i (1, 0, 0)

/-- The degree boxes of the variables (list). -/
def BxHFl : List (Nat × Nat × Nat) :=
  [(36, 27, 10), (0, 1, 0), (0, 2, 0), (0, 2, 0), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (0, 0, 0), (0, 0, 0), (0, 0, 0), (36, 27, 11), (72, 54, 20), (72, 54, 20),
    (72, 54, 20), (72, 54, 20), (72, 54, 20), (72, 54, 20)]

/-- The degree boxes of the variables. -/
def BxHF (i : Nat) : Nat × Nat × Nat := BxHFl.getD i (0, 0, 0)

/-- The static `ℓ¹` bounds of the variables (list). -/
def LHFl : List Nat :=
  [162259276829213363391578010288128, 2, 2, 2, 164142648317675092206307816337571840,
    164142648317823219561220781805404160,
    6502360208223117917386684105337714252302302393439909579723898880,
    6502360208223117917386684105337714252302302393439909579723898880,
    164142648317675092206307816337571840, 164142648317823219561220781805404160,
    164142638571930864166950603660984320, 164142638571930864166950603660984320,
    164142638571930864166950603660984320, 164142638571930864166950603660984320,
    10338440483423860741749959064289280, 10338596113146985817582388044103680,
    10338907370213903883427209868738560, 1312244661573625045122129379983360,
    646181653236985808361650875269120, 646220540890151148963899962818560,
    2564767862345725186673526733537280, 80777577091346994316837247221760,
    40388798035082171203379973816320, 80772723254181241585045687173120,
    161555192214392929555195985920000, 10097199513399557958154951782400,
    40075725593438806902759681146880, 1262074101444350707746832473600,
    5009465708469480552420624481280, 1305491791339287656397417947689123840,
    82070702867680327492684380184248320, 82070700440761744616247334786826240,
    2608433784277870964431789370302791680, 164142648317823219561219704037048320,
    20677192221553896277984234983915520, 654018299959771045335862381127925760,
    652108446069541807045647888296181760, 164141405735360654985368760368496640,
    654018299997691648228621945678069760, 652745895669791960074110065285529600,
    164141405735360654985230806018949120, 2610983582679167840296435950068695040,
    1308036599919542090742357389224181760, 2610983582678575312794835895378247680,
    164142648317675087685819690364436480, 20677192221535379793559233274839040,
    1313126236571243142507274381914275840, 10464272918039305802731644233858416640,
    328282801725125218327269525474508800, 20997157172260536661313820368568320,
    2616103060798199987731352556991938560, 20677193439753263073348810199531520,
    2606043348277210565511398723587932160, 2606202710677254514954054601948528640,
    2606043348277210565511398723587932160, 2610983582679167840296435950068695040,
    2616103060798199987731352556991938560, 2616142901399400677299943742017372160,
    1305491791339287656397417947689123840, 1308036599919542090742357389224181760,
    10505009892565204920040945590017720320, 328285286889754083728171385466388480,
    165417537753247803030466419836846080, 330835075487535304632211214140702720,
    2646640841419092686057186320334192640, 165422517809140166757634959873146880,
    330845035580359728397582066809569280, 5252644270521234145739305319294566400, 0, 0, 0,
    10546852993898868620452570668728320, 164141405735360654985368760368496640,
    1305491791339287656397417947689123840, 328282801763046978464989339147304960,
    82070702867680327492684380184248320, 2616073199839084181484714778448363520,
    82070702867680327492684380184248320]

/-- The static `ℓ¹` bounds of the variables. -/
def LHF (i : Nat) : Nat := LHFl.getD i 0

/-- The minimal widths `b` of the fast images (list). -/
def bMinHFl : List Nat :=
  [0, 0, 0, 0, 106, 106, 201, 201, 106, 106, 106, 106, 106, 106, 102, 102, 102, 99, 98, 98, 100,
    95, 94, 95, 96, 92, 94, 89, 91, 109, 105, 105, 110, 106, 103, 108, 108, 106, 108, 108, 106,
    110, 109, 110, 106, 103, 109, 112, 107, 103, 110, 103, 110, 110, 110, 110, 110, 110, 109, 109,
    112, 107, 106, 107, 110, 106, 107, 111, 0, 0, 0, 0, 106, 109, 107, 105, 110, 105]

/-- The minimal widths `b` of the fast images. -/
def bMinHF (i : Nat) : Nat := bMinHFl.getD i 0

/-- The minimal widths `W` of the fast images (list). -/
def wMinHFl : List Nat :=
  [0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 16, 16, 16, 16, 32, 32, 32, 33, 32, 32, 32, 33, 33, 33, 33,
    32, 32, 32, 32, 33, 32, 33, 32, 32, 33, 33, 32, 33, 33, 32, 33, 33, 33, 33, 33, 33, 34, 34,
    34, 34, 35, 35, 34, 34, 34, 35, 36, 36, 32, 32, 34, 34, 34, 35, 35, 35, 35, 36, 0, 0, 0, 0,
    36, 33, 36, 32, 36, 33]

/-- The minimal widths `W` of the fast images. -/
def wMinHF (i : Nat) : Nat := wMinHFl.getD i 0

/-- **The Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`). -/
def KvHF (b W R : Nat) (i : Nat) : Int :=
  match kindHF i with
  | 0 => ((1 <<< SHF : Nat) : Int) * ((1 <<< (b * (NHF + W * (MHF + R * DHF))) : Nat) : Int)
  | 1 => 2 * ((1 <<< (b * W) : Nat) : Int)
  | 2 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) + 1
  | 4 =>
    ((1 <<< (SHF + 6) : Nat) : Int) * ((1 <<< (b * (NHF + W * (MHF + R * DHF))) : Nat) : Int) +
      ((1 <<< (SHF - 1) : Nat) : Int) * (((1 <<< (b * (NHF + W * (MHF + R * (DHF + 1)))) : Nat) : Int) +
        ((1 <<< (b * (NHF + W * (MHF + R * (DHF - 1)))) : Nat) : Int))
  | 5 => 0
  | _ =>
    if bMinHF i ≤ b ∧ wMinHF i ≤ W then
      ((famTB b W R NHF MHF DHF (c0HF i) (oddHF i) drHF dwHF (famHF i) : Nat) : Int) -
        ((famO b W R NHF MHF DHF dwHF (famHF i) : Nat) : Int)
    else famPack b W R NHF MHF DHF (if oddHF i then -1 else 1) (c0HF i : Int) 0 0 ddHF drHF 0
      (famHF i)

end PlasmaLean.Design.RationalStellaratorGC
