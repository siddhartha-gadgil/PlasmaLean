/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronChebCompute
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH1
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH2
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH3
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH4
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH5
public import PlasmaLean.Design.RationalStellaratorGCEw4DataH6
public import PlasmaLean.Design.RationalStellaratorGCMuDataL

/-!
# The high-resolution layout and Kronecker images of the `μ > 0` passing guiding-centre torus family certificate

Layout `N = 36`, `M = 27`, Chebyshev degree `D = 12`, scale `2^{−107}`; for every variable: the
stored coefficients `famHE4 i` (with symbol `c0HE4 i` and parity `oddHE4 i`), the weight `WtHE4 i`, the
degree box `BxHE4 i`, the static `ℓ¹` bound `LHE4 i`, the minimal widths `bMinHE4 i`, `wMinHE4 i` of
the fast images, and the Kronecker image `KvHE4 b W R i` (fast: `famTB − famO`; generic: `famPack`).
Variables `0, 1, 2, 3` are `t`, `V`, `cos 2φ`, `sin 2φ`; variable `71` is the parameter
`r = 64 + cos ϑ = 63 + 8λ`; the special variables are 0, 1, 2, 3, 68, 69, 70, 71. Light module (kernel checks only).

Energy-window node 4: gyro-length `ρ_4 = 1/256 + 2⁻³²`, its own family torus `K_4(λ)`; the
fields at `ρ_4` are the nodes `DtJ`, `nRtJ`, `nZtJ`.
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Certificates.KronBallCheb

/-- Layout: poloidal half width. -/
def NHE4 : Nat := 36
/-- Layout: toroidal half width. -/
def MHE4 : Nat := 27
/-- Layout: Chebyshev degree. -/
def DHE4 : Nat := 12
/-- Layout: scale exponent. -/
def SHE4 : Nat := 107
/-- Reading levels of the stored coefficients (`N_j ≤ 2^dd`, `2M_j + 1 ≤ 2^dr`, `2D + 1 ≤ 2^dw`). -/
def ddHE4 : Nat := 6
/-- Reading levels. -/
def drHE4 : Nat := 6
/-- Reading levels. -/
def dwHE4 : Nat := 5

/-- The kinds of the variables: `0` = `t`, `1` = `V`, `2` = `cos 2φ`, `3` = `sin 2φ`, `4` = the
parameter `r`, `5` = zero (dummies and beyond the last variable), `6` = stored family (list). -/
def kindHE4l : List Nat :=
  [0, 1, 2, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 5, 5, 5, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6]

/-- The kinds of the variables. -/
def kindHE4 (i : Nat) : Nat := kindHE4l.getD i 5

/-- The stored coefficients of the variables (list). -/
def famHE4l : List (List SliceData) :=
  [[], [], [], [], sdHE4_U, sdHE4_Z, sdHE4_LRx, sdHE4_LZx, sdHE4_thU, sdHE4_thZ, sdLM_U, sdLM_Z,
    sdHE4_thUe, sdHE4_thZe, sdHE4_m02, sdHE4_m11, sdHE4_m20, sdHE4_m03, sdHE4_m12, sdHE4_m21, sdHE4_m30,
    sdHE4_m13, sdHE4_m22, sdHE4_m31, sdHE4_m40, sdHE4_m41, sdHE4_m50, sdHE4_m51, sdHE4_m60, sdHE4_Dp,
    sdHE4_nRp, sdHE4_nZp, sdHE4_DuP, sdHE4_DzP, sdHE4_DphP, sdHE4_nRuP, sdHE4_nRzP, sdHE4_nRphP,
    sdHE4_nZuP, sdHE4_nZzP, sdHE4_nZphP, sdHE4_PuP, sdHE4_RD, sdHE4_RDu, sdHE4_RDz, sdHE4_RDph, sdHE4_q,
    sdHE4_qR, sdHE4_qz, sdHE4_qph, sdHE4_P2, sdHE4_E, sdHE4_V0, sdHE4_V2, sdHE4_V0, sdHE4_W, sdHE4_W2,
    sdHE4_W3, sdHE4_R2, sdHE4_R3, sdHE4_A1, sdHE4_A2, sdHE4_K1, sdHE4_K2, sdHE4_K3, sdHE4_KD, sdHE4_KR,
    sdHE4_KZ, [], [], [], [], sdHE4_P4P, sdHE4_R4, sdHE4_R8, sdHE4_P42, sdHE4_E4P, sdHE4_PP4, sdHE4_QPP4P,
    sdHE4_V40, sdHE4_V42, sdHE4_V40, sdHE4_VV4, sdHE4_Bm, sdHE4_lamv, sdHE4_EN, sdHE4_N0, sdHE4_N2,
    sdHE4_N0, sdHE4_Fv, sdHE4_YDt, sdHE4_DtF, sdHE4_YnRt, sdHE4_nRtF, sdHE4_YnZt, sdHE4_nZtF, sdHE4_DtJ,
    sdHE4_nRtJ, sdHE4_nZtJ]

/-- The stored coefficients of the variables. -/
def famHE4 (i : Nat) : List SliceData := famHE4l.getD i []

/-- The symbols of the stored families (list). -/
def c0HE4l : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 140737488355328, 140737488355328, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The symbols of the stored families. -/
def c0HE4 (i : Nat) : Nat := c0HE4l.getD i 1

/-- The parities of the stored families (list). -/
def oddHE4l : List Bool :=
  [false, false, false, false, false, true, true, false, true, false, false, true, true, false,
    false, true, false, true, false, true, false, true, false, true, false, true, false, true,
    false, false, true, false, false, true, true, true, false, false, false, true, true, false,
    false, false, true, true, false, false, true, true, false, false, false, false, false, false,
    false, false, false, false, false, true, false, true, false, false, true, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, true, false, false,
    false, true, false]

/-- The parities of the stored families. -/
def oddHE4 (i : Nat) : Bool := oddHE4l.getD i false

/-- The weights of the variables (list). -/
def WtHE4l : List (Nat × Nat × Nat) :=
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
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 2), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 2)]

/-- The weights of the variables. -/
def WtHE4 (i : Nat) : Nat × Nat × Nat := WtHE4l.getD i (1, 0, 0)

/-- The degree boxes of the variables (list). -/
def BxHE4l : List (Nat × Nat × Nat) :=
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
    (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24), (72, 54, 24),
    (72, 54, 24)]

/-- The degree boxes of the variables. -/
def BxHE4 (i : Nat) : Nat × Nat × Nat := BxHE4l.getD i (0, 0, 0)

/-- The static `ℓ¹` bounds of the variables (list). -/
def LHE4l : List Nat :=
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
    81446458170638102241286860371394560, 1303042030830749609721266720420659200,
    81448943335266967642188720363274240, 81446458170638102241286860371394560]

/-- The static `ℓ¹` bounds of the variables. -/
def LHE4 (i : Nat) : Nat := LHE4l.getD i 0

/-- The minimal widths `b` of the fast images (list). -/
def bMinHE4l : List Nat :=
  [0, 0, 0, 0, 106, 106, 201, 201, 106, 106, 106, 106, 106, 106, 102, 102, 102, 99, 98, 98, 100,
    95, 94, 95, 96, 92, 94, 89, 91, 109, 105, 105, 110, 106, 103, 108, 108, 106, 108, 108, 106,
    110, 109, 110, 106, 103, 109, 112, 107, 103, 110, 103, 110, 110, 110, 110, 110, 110, 109, 109,
    112, 107, 106, 107, 110, 106, 107, 111, 0, 0, 0, 0, 110, 109, 109, 110, 95, 110, 110, 110,
    110, 110, 110, 110, 105, 105, 110, 110, 110, 110, 106, 109, 107, 105, 110, 105, 109, 105, 105]

/-- The minimal widths `b` of the fast images. -/
def bMinHE4 (i : Nat) : Nat := bMinHE4l.getD i 0

/-- The minimal widths `W` of the fast images (list). -/
def wMinHE4l : List Nat :=
  [0, 0, 0, 0, 28, 28, 28, 28, 28, 28, 16, 16, 16, 16, 32, 32, 32, 33, 32, 32, 32, 33, 33, 33, 33,
    32, 32, 32, 32, 33, 32, 33, 32, 32, 33, 33, 32, 33, 33, 32, 33, 33, 33, 33, 33, 33, 34, 34,
    34, 34, 35, 35, 34, 34, 34, 35, 36, 36, 32, 32, 34, 34, 34, 35, 35, 35, 35, 36, 0, 0, 0, 0,
    33, 33, 34, 36, 36, 36, 35, 36, 36, 36, 36, 36, 1, 32, 32, 32, 32, 30, 36, 33, 36, 32, 36, 33,
    33, 32, 33]

/-- The minimal widths `W` of the fast images. -/
def wMinHE4 (i : Nat) : Nat := wMinHE4l.getD i 0

/-- **The Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`). -/
def KvHE4 (b W R : Nat) (i : Nat) : Int :=
  match kindHE4 i with
  | 0 => ((1 <<< SHE4 : Nat) : Int) * ((1 <<< (b * (NHE4 + W * (MHE4 + R * DHE4))) : Nat) : Int)
  | 1 => 2 * ((1 <<< (b * W) : Nat) : Int)
  | 2 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) + 1
  | 4 =>
    ((1 <<< (SHE4 + 6) : Nat) : Int) * ((1 <<< (b * (NHE4 + W * (MHE4 + R * DHE4))) : Nat) : Int) +
      ((1 <<< (SHE4 - 1) : Nat) : Int) * (((1 <<< (b * (NHE4 + W * (MHE4 + R * (DHE4 + 1)))) : Nat) : Int) +
        ((1 <<< (b * (NHE4 + W * (MHE4 + R * (DHE4 - 1)))) : Nat) : Int))
  | 5 => 0
  | _ =>
    if bMinHE4 i ≤ b ∧ wMinHE4 i ≤ W then
      ((famTB b W R NHE4 MHE4 DHE4 (c0HE4 i) (oddHE4 i) drHE4 dwHE4 (famHE4 i) : Nat) : Int) -
        ((famO b W R NHE4 MHE4 DHE4 dwHE4 (famHE4 i) : Nat) : Int)
    else famPack b W R NHE4 MHE4 DHE4 (if oddHE4 i then -1 else 1) (c0HE4 i : Int) 0 0 ddHE4 drHE4 0
      (famHE4 i)

end PlasmaLean.Design.RationalStellaratorGC
