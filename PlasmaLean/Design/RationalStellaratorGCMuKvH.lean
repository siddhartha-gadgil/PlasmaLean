/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronChebCompute
public import PlasmaLean.Design.RationalStellaratorGCMuDataH1
public import PlasmaLean.Design.RationalStellaratorGCMuDataH2
public import PlasmaLean.Design.RationalStellaratorGCMuDataH3
public import PlasmaLean.Design.RationalStellaratorGCMuDataH4
public import PlasmaLean.Design.RationalStellaratorGCMuDataH5
public import PlasmaLean.Design.RationalStellaratorGCMuDataH6
public import PlasmaLean.Design.RationalStellaratorGCMuDataL

/-!
# The high-resolution layout and Kronecker images of the `μ > 0` passing guiding-centre torus family certificate

Layout `N = 36`, `M = 27`, Chebyshev degree `D = 12`, scale `2^{−107}`; for every variable: the
stored coefficients `famHM i` (with symbol `c0HM i` and parity `oddHM i`), the weight `WtHM i`, the
degree box `BxHM i`, the static `ℓ¹` bound `LHM i`, the minimal widths `bMinHM i`, `wMinHM i` of
the fast images, and the Kronecker image `KvHM b W R i` (fast: `famTB − famO`; generic: `famPack`).
Variables `0, 1, 2, 3` are `t`, `V`, `cos 2φ`, `sin 2φ`; variable `71` is the parameter
`r = 64 + cos ϑ = 63 + 8λ`; the special variables are 0, 1, 2, 3, 68, 69, 70, 71. Light module (kernel checks only).
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Certificates.KronBallCheb

/-- Layout: poloidal half width. -/
def NHM : Nat := 36
/-- Layout: toroidal half width. -/
def MHM : Nat := 27
/-- Layout: Chebyshev degree. -/
def DHM : Nat := 12
/-- Layout: scale exponent. -/
def SHM : Nat := 107
/-- Reading levels of the stored coefficients (`N_j ≤ 2^dd`, `2M_j + 1 ≤ 2^dr`, `2D + 1 ≤ 2^dw`). -/
def ddHM : Nat := 6
/-- Reading levels. -/
def drHM : Nat := 6
/-- Reading levels. -/
def dwHM : Nat := 5

/-- The kinds of the variables: `0` = `t`, `1` = `V`, `2` = `cos 2φ`, `3` = `sin 2φ`, `4` = the
parameter `r`, `5` = zero (dummies and beyond the last variable), `6` = stored family (list). -/
def kindHMl : List Nat :=
  [0, 1, 2, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 5, 5, 5, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6]

/-- The kinds of the variables. -/
def kindHM (i : Nat) : Nat := kindHMl.getD i 5

/-- The stored coefficients of the variables (list). -/
def famHMl : List (List SliceData) :=
  [[], [], [], [], sdHM_U, sdHM_Z, sdHM_LRx, sdHM_LZx, sdHM_thU, sdHM_thZ, sdLM_U, sdLM_Z,
    sdHM_thUe, sdHM_thZe, sdHM_m02, sdHM_m11, sdHM_m20, sdHM_m03, sdHM_m12, sdHM_m21, sdHM_m30,
    sdHM_m13, sdHM_m22, sdHM_m31, sdHM_m40, sdHM_m41, sdHM_m50, sdHM_m51, sdHM_m60, sdHM_Dp,
    sdHM_nRp, sdHM_nZp, sdHM_DuP, sdHM_DzP, sdHM_DphP, sdHM_nRuP, sdHM_nRzP, sdHM_nRphP,
    sdHM_nZuP, sdHM_nZzP, sdHM_nZphP, sdHM_PuP, sdHM_RD, sdHM_RDu, sdHM_RDz, sdHM_RDph, sdHM_q,
    sdHM_qR, sdHM_qz, sdHM_qph, sdHM_P2, sdHM_E, sdHM_V0, sdHM_V2, sdHM_V0, sdHM_W, sdHM_W2,
    sdHM_W3, sdHM_R2, sdHM_R3, sdHM_A1, sdHM_A2, sdHM_K1, sdHM_K2, sdHM_K3, sdHM_KD, sdHM_KR,
    sdHM_KZ, [], [], [], [], sdHM_P4P, sdHM_R4, sdHM_R8, sdHM_P42, sdHM_E4P, sdHM_PP4, sdHM_QPP4P,
    sdHM_V40, sdHM_V42, sdHM_V40, sdHM_VV4, sdHM_Bm, sdHM_lamv, sdHM_EN, sdHM_N0, sdHM_N2,
    sdHM_N0, sdHM_Fv, sdHM_YDt, sdHM_DtF, sdHM_YnRt, sdHM_nRtF, sdHM_YnZt, sdHM_nZtF]

/-- The stored coefficients of the variables. -/
def famHM (i : Nat) : List SliceData := famHMl.getD i []

/-- The symbols of the stored families (list). -/
def c0HMl : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 140737488355328, 140737488355328, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The symbols of the stored families. -/
def c0HM (i : Nat) : Nat := c0HMl.getD i 1

/-- The parities of the stored families (list). -/
def oddHMl : List Bool :=
  [false, false, false, false, false, true, true, false, true, false, false, true, true, false,
    false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false, false, true, false, false, true, true, true, false, false, false, true, true, false,
    false, false, true, true, false, false, true, true, false, false, false, false, false, false,
    false, false, false, false, false, true, false, true, false, false, true, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, true, false, false]

/-- The parities of the stored families. -/
def oddHM (i : Nat) : Bool := oddHMl.getD i false

/-- The weights of the variables (list). -/
def WtHMl : List (Nat × Nat × Nat) :=
  [(1, 0, 0), (0, 1, 0), (0, 1, 3), (0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1),
    (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 2), (1, 0, 0),
    (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 2), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 2), (1, 0, 0)]

/-- The weights of the variables. -/
def WtHM (i : Nat) : Nat × Nat × Nat := WtHMl.getD i (1, 0, 0)

/-- The degree boxes of the variables (list). -/
def BxHMl : List (Nat × Nat × Nat) :=
  [(36, 27, 12), (0, 1, 0), (0, 2, 0), (0, 2, 0), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (0, 0, 0), (0, 0, 0), (0, 0, 0), (36, 27, 13), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24)]

/-- The degree boxes of the variables. -/
def BxHM (i : Nat) : Nat × Nat × Nat := BxHMl.getD i (0, 0, 0)

/-- The static `ℓ¹` bounds of the variables (list). -/
def LHMl : List Nat :=
  [162259276829213363391578010288128, 2, 2, 2, 162917768063406064347744076730204160,
    162917768063406064347744076730204160,
    6453837702294380006635820662785623251554060364716195607090298880,
    6453837702294380006635820662785623251554060364716195607090298880,
    162917768063406064347744076730204160, 162917768063406064347744076730204160,
    162917768060998406879955500872499200, 162917768060998406879955500872499200,
    162917768060998406879955500872499200, 162917768060998406879955500872499200,
    10182982098635397953364295805829120, 10182360807478180473016799314575360,
    10185486688093077079580136492236800, 1273185911890478221125005638369280,
    636592918006111151443704964710400, 636592955945230069517273698140160,
    2546371672023287351985492365148160, 79574119493153758698281359114240,
    39811480688881315595695465431040, 79622961377762631191390930862080,
    159245922755669918002813002055680, 9952870172220328898923866357760,
    39811329006469885822825922560000, 1244108771600999596503597056000,
    4976435086114687145952107560960, 1303042030830749609721266720420659200,
    81446458170638102241286860371394560, 81446380509243450197508677246648320,
    2605944260983588659628904871027015680, 162917768063406064347744076730204160,
    20364721614660106236209823230197760, 651521015415374813901609612156600320,
    651496005942333229368276908790251520, 162892916341276204482573720742789120,
    651521020269249590115553845088092160, 651521015415374813901609612156600320,
    162892916341276204482573720742789120, 2606084061661499219442533440841318400,
    1303042040538499180231107690176184320, 2606004536090010703189066896826695680,
    162897886670533935284377440726548480, 20364721614660106200893509746032640,
    1303142088138266925073207978738319360, 10424336324345914044778041034240163840,
    325785522036973800790034708986593280, 20370973376195556775565931902402560,
    2606284176276830104891556046359756800, 20365964197270795906728591611658240,
    2605887753071317994939033160075182080, 2605891520265469373809340719216721920,
    2605887753071317994939033160075182080, 2606084061661499255606438448626401280,
    2606284176276830104891556046359756800, 2606684366676493598234857373465313280,
    1303042030830749609721266720420659200, 1303042040538499180231107690176184320,
    10424341297102090362976700948419706880, 325785522036973800790034708986593280,
    162892916417117998002250830493777920, 325785522036973819154517720752455680,
    2606286662673878710075227660122849280, 162892921270992195598129478049464320,
    325785832834235996013330739358597120, 5212568352591580817161043469758627840, 0, 0, 0,
    10546852993898868620452570668728320, 2606084081076998360480149445793546240,
    1303042661834396471947480594277990400, 1303142088147895204290260867439656960,
    2606684289014506432180310886601195520, 79720047902331440718930646138880,
    2606684287801037738125721193571942400, 2605934004823249766912190494130831360,
    2605884083267055935374672550680330240, 2605884180656945254680602256133324800,
    2605884083267055935374672550680330240, 2605890238235946860339943642213908480,
    2605934004823249775953166746077102080, 162867749117322913504296427827061800,
    162868530663355462877489473509130240, 2646924073452369751129848718169210880,
    2688610461620502727441289476623564800, 2646924073452369751129848718169210880,
    2606681763170090047552214387895828480, 162897886670533935284377440726548480,
    1303042030830749609721266720420659200, 325785522036973800785620169801072640,
    81448943335266967642188720363274240, 2606084081076998360462215380352368640,
    81446458170638102241286860371394560]

/-- The static `ℓ¹` bounds of the variables. -/
def LHM (i : Nat) : Nat := LHMl.getD i 0

/-- The minimal widths `b` of the fast images (list). -/
def bMinHMl : List Nat :=
  [0, 0, 0, 0, 106, 106, 201, 201, 106, 106, 106, 106, 106, 106, 102, 102, 102, 99, 98, 98, 100,
    95, 94, 95, 96, 92, 94, 89, 91, 109, 105, 105, 110, 106, 103, 108, 108, 106, 108, 108, 106,
    110, 109, 110, 106, 103, 109, 112, 107, 103, 110, 103, 110, 110, 110, 110, 110, 110, 109, 109,
    112, 107, 106, 107, 110, 106, 107, 111, 0, 0, 0, 0, 110, 109, 109, 110, 95, 110, 110, 110,
    110, 110, 110, 110, 105, 105, 110, 110, 110, 110, 106, 109, 107, 105, 110, 105]

/-- The minimal widths `b` of the fast images. -/
def bMinHM (i : Nat) : Nat := bMinHMl.getD i 0

/-- The minimal widths `W` of the fast images (list). -/
def wMinHMl : List Nat :=
  [0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 16, 16, 16, 16, 32, 32, 32, 33, 32, 32, 32, 33, 33, 33, 33,
    32, 32, 32, 32, 33, 32, 33, 32, 32, 33, 33, 32, 33, 33, 32, 33, 33, 33, 33, 33, 33, 34, 34,
    34, 34, 35, 35, 34, 34, 34, 35, 36, 36, 32, 32, 34, 34, 34, 35, 35, 35, 35, 36, 0, 0, 0, 0,
    33, 33, 34, 36, 36, 36, 35, 36, 36, 36, 36, 36, 1, 32, 32, 32, 32, 30, 36, 33, 36, 32, 36, 33]

/-- The minimal widths `W` of the fast images. -/
def wMinHM (i : Nat) : Nat := wMinHMl.getD i 0

/-- **The Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`). -/
def KvHM (b W R : Nat) (i : Nat) : Int :=
  match kindHM i with
  | 0 => ((1 <<< SHM : Nat) : Int) * ((1 <<< (b * (NHM + W * (MHM + R * DHM))) : Nat) : Int)
  | 1 => 2 * ((1 <<< (b * W) : Nat) : Int)
  | 2 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) + 1
  | 4 =>
    ((1 <<< (SHM + 6) : Nat) : Int) * ((1 <<< (b * (NHM + W * (MHM + R * DHM))) : Nat) : Int) +
      ((1 <<< (SHM - 1) : Nat) : Int) * (((1 <<< (b * (NHM + W * (MHM + R * (DHM + 1)))) : Nat) : Int) +
        ((1 <<< (b * (NHM + W * (MHM + R * (DHM - 1)))) : Nat) : Int))
  | 5 => 0
  | _ =>
    if bMinHM i ≤ b ∧ wMinHM i ≤ W then
      ((famTB b W R NHM MHM DHM (c0HM i) (oddHM i) drHM dwHM (famHM i) : Nat) : Int) -
        ((famO b W R NHM MHM DHM dwHM (famHM i) : Nat) : Int)
    else famPack b W R NHM MHM DHM (if oddHM i then -1 else 1) (c0HM i : Int) 0 0 ddHM drHM 0
      (famHM i)

end PlasmaLean.Design.RationalStellaratorGC
