/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronChebCompute
public import PlasmaLean.Design.RationalStellaratorGCFamDataL

/-!
# The low-resolution layout and Kronecker images of the guiding-centre torus family certificate

Layout `N = 16`, `M = 12`, Chebyshev degree `D = 4`, scale `2^{−60}`; for every variable: the
stored coefficients `famLF i` (with symbol `c0LF i` and parity `oddLF i`), the weight `WtLF i`, the
degree box `BxLF i`, the static `ℓ¹` bound `LLF i`, the minimal widths `bMinLF i`, `wMinLF i` of
the fast images, and the Kronecker image `KvLF b W R i` (fast: `famTB − famO`; generic: `famPack`).
Variables `0, 1, 2, 3` are `t`, `V`, `cos 2φ`, `sin 2φ`; variable `114` is the parameter
`r = 64 + cos ϑ`; the special variables are 0, 1, 2, 3, 77, 78, 79, 101, 102, 103, 104, 105, 106, 107, 109, 111, 112, 113, 114. Light module (kernel checks only).
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Certificates.KronBallCheb

/-- Layout: poloidal half width. -/
def NLF : Nat := 16
/-- Layout: toroidal half width. -/
def MLF : Nat := 12
/-- Layout: Chebyshev degree. -/
def DLF : Nat := 4
/-- Layout: scale exponent. -/
def SLF : Nat := 60
/-- Reading levels of the stored coefficients (`N_j ≤ 2^dd`, `2M_j + 1 ≤ 2^dr`, `2D + 1 ≤ 2^dw`). -/
def ddLF : Nat := 5
/-- Reading levels. -/
def drLF : Nat := 5
/-- Reading levels. -/
def dwLF : Nat := 4

/-- The kinds of the variables: `0` = `t`, `1` = `V`, `2` = `cos 2φ`, `3` = `sin 2φ`, `4` = the
parameter `r`, `5` = zero (dummies and beyond the last variable), `6` = stored family (list). -/
def kindLFl : List Nat :=
  [0, 1, 2, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 5, 5, 5, 5, 5, 5, 5, 6, 5, 6, 5, 5, 5, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6]

/-- The kinds of the variables. -/
def kindLF (i : Nat) : Nat := kindLFl.getD i 5

/-- The stored coefficients of the variables (list). -/
def famLFl : List (List SliceData) :=
  [[], [], [], [], sdLF_U, sdLF_Z, sdLF_A, sdLF_B, sdLF_m02, sdLF_m11, sdLF_m20, sdLF_m03,
    sdLF_m12, sdLF_m21, sdLF_m30, sdLF_m13, sdLF_m22, sdLF_m31, sdLF_m40, sdLF_m41, sdLF_m50,
    sdLF_m51, sdLF_m60, sdLF_Dp, sdLF_nRp, sdLF_nZp, sdLF_DuP, sdLF_DzP, sdLF_DphP, sdLF_nRuP,
    sdLF_nRzP, sdLF_nRphP, sdLF_nZuP, sdLF_nZzP, sdLF_nZphP, sdLF_PuP, sdLF_PdP, sdLF_DuuP,
    sdLF_DuzP, sdLF_DzzP, sdLF_DuphP, sdLF_DzphP, sdLF_nRuuP, sdLF_nRuzP, sdLF_nRzzP, sdLF_nRuphP,
    sdLF_nRzphP, sdLF_nZuuP, sdLF_nRzzP, sdLF_nZzzP, sdLF_nZuphP, sdLF_nZzphP, sdLF_RD, sdLF_RDu,
    sdLF_RDz, sdLF_RDph, sdLF_q, sdLF_qR, sdLF_qz, sdLF_qph, sdLF_P2, sdLF_E, sdLF_V0, sdLF_V0,
    sdLF_W, sdLF_W2, sdLF_W3, sdLF_R2, sdLF_R3, sdLF_A1, sdLF_A2, sdLF_K1, sdLF_K2, sdLF_K3,
    sdLF_KD, sdLF_KR, sdLF_KZ, [], [], [], sdLF_qRu, sdLF_qRz, sdLF_qzz, sdLF_qzu, sdLF_qphu,
    sdLF_qphz, sdLF_qR, sdLF_qz, sdLF_Eu, sdLF_Ez, sdLF_V3, sdLF_Wu, sdLF_Wz, sdLF_W3u, sdLF_W3z,
    sdLF_KDu, sdLF_KDz, sdLF_KRu, sdLF_KRz, sdLF_KZu, sdLF_KZz, [], [], [], [], [], [], [],
    sdLF_W0, [], sdLF_W02, [], [], [], [], sdLF_YDt, sdLF_DtF, sdLF_YnRt, sdLF_nRtF, sdLF_YnZt,
    sdLF_nZtF, sdLF_YDtu, sdLF_DtuF, sdLF_YDtz, sdLF_DtzF, sdLF_YnRtu, sdLF_nRtuF, sdLF_YnRtz,
    sdLF_nRtzF, sdLF_YnZtu, sdLF_nZtuF, sdLF_YnZtz, sdLF_nZtzF, sdLF_PtorF, sdLF_Dt3F, sdLF_FF,
    sdLF_qiF, sdLF_YF, sdLF_Uo, sdLF_Zo, sdLF_Ao, sdLF_Bo]

/-- The stored coefficients of the variables. -/
def famLF (i : Nat) : List SliceData := famLFl.getD i []

/-- The symbols of the stored families (list). -/
def c0LFl : List Nat :=
  [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

/-- The symbols of the stored families. -/
def c0LF (i : Nat) : Nat := c0LFl.getD i 1

/-- The parities of the stored families (list). -/
def oddLFl : List Bool :=
  [false, false, false, false, false, true, true, false, false, true, false, true, false, true,
    false, true, false, true, false, true, false, true, false, false, true, false, false, true,
    true, true, false, false, false, true, true, false, false, false, true, false, true, false,
    true, false, true, false, true, false, true, false, true, false, false, false, true, true,
    false, false, true, true, false, false, false, false, false, false, false, false, false,
    false, true, false, true, false, false, true, false, false, false, false, false, true, false,
    true, true, false, false, true, false, true, false, false, true, false, true, false, true,
    true, false, false, true, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, true, false, false, false, false, true,
    true, true, true, false, false, false, false, true, true, false, false, false, false, false,
    false, true, true, false]

/-- The parities of the stored families. -/
def oddLF (i : Nat) : Bool := oddLFl.getD i false

/-- The weights of the variables (list). -/
def WtLFl : List (Nat × Nat × Nat) :=
  [(1, 0, 0), (0, 1, 0), (0, 1, 3), (0, 1, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0),
    (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0),
    (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 1), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 1),
    (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 3),
    (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 0),
    (1, 0, 3), (1, 0, 3), (1, 0, 0), (1, 0, 2), (1, 0, 3), (1, 0, 0), (1, 0, 3), (1, 0, 3),
    (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 2),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 3), (1, 0, 0),
    (1, 0, 0), (1, 0, 2), (1, 0, 0), (1, 0, 3), (1, 0, 1), (1, 0, 0), (1, 0, 0), (1, 0, 0),
    (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0)]

/-- The weights of the variables. -/
def WtLF (i : Nat) : Nat × Nat × Nat := WtLFl.getD i (1, 0, 0)

/-- The degree boxes of the variables (list). -/
def BxLFl : List (Nat × Nat × Nat) :=
  [(16, 12, 4), (0, 1, 0), (0, 2, 0), (0, 2, 0), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (0, 0, 0), (0, 0, 0), (0, 0, 0), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (0, 0, 0), (0, 0, 0), (32, 24, 8), (0, 0, 0), (32, 24, 8), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (16, 12, 5), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8),
    (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8), (32, 24, 8)]

/-- The degree boxes of the variables. -/
def BxLF (i : Nat) : Nat × Nat × Nat := BxLFl.getD i (0, 0, 0)

/-- The static `ℓ¹` bounds of the variables (list). -/
def LLFl : List Nat :=
  [1152921504606846976, 2, 2, 2, 239651423559824179200, 239651423559824179200,
    239651423559824179200, 239651423559824179200, 15094324173786316800, 15094550948059545600,
    15095004495740928000, 1915902890724556800, 943437781362278400, 943494475363123200,
    3744610409014886400, 117936823261593600, 58968425472000000, 117929736565555200,
    235873701779865600, 14742106368000000, 58511333577523200, 1842653433139200, 7313920164249600,
    1906043210844025651200, 119824806456223334400, 119824806456223334400, 3808363693445323161600,
    239651425334958489600, 30189100122714931200, 954879346471757414400, 952090926463057920000,
    239649612912446668800, 954879342931869696000, 953021606308714905600, 239649612912446668800,
    3812086425241780224000, 7639063798964079820800, 7613001032031220531200,
    1902553608327580876800, 3808363691671919014800, 479302850666456678400, 479302850669916979200,
    7624158329822615961600, 479299225821433036800, 1906043210844025651200, 1909755057468447129600,
    1904181852926115840000, 3806505960375897292800, 1906043210844025651200,
    3808360065056951500800, 1909758685856818790400, 1906043212617429811200,
    1909758682310010470400, 3812086419914647142400, 239651427106632499200, 30189100122714931200,
    1917189632349437952000, 15278040459747577036800, 479299232918509977600, 30656256902430720000,
    3819560926644378009600, 30189101896119091200, 3804873637380331929600, 3804873637380331929600,
    3812086432342317465600, 3819560954991162163200, 3819619066009406668800,
    1906043210843160576000, 1909758682310010470400, 15337517058684773990400,
    479302861306881638400, 241512793908864614400, 483025580731033190400, 3864146591412859699200,
    241520057799986380800, 483040101426580684800, 7668961776172321996800, 0, 0, 0,
    61112277947307471667200, 3834379293017977651200, 3819510114936894259200,
    3834379293017977651200, 966036662026607001600, 958598465837019955200, 15278040459747577036800,
    479299232918509977600, 479310111010770124800, 479302854220185600000, 3805107216658622054400,
    7639063798964079820800, 477445119373895270400, 61112975281630268620800,
    1909809533115432960000, 3864204702541833830400, 1917211416936107212800,
    7728409291696531046400, 3864204645626806272000, 61827274330028900352000,
    3834422833872214425600, 0, 0, 0, 0, 0, 0, 0, 30188646574168473600, 0, 239502090259660800, 0,
    0, 0, 74939897799445053440, 239649612912446668800, 1906043210844025651200,
    479299225824893337600, 119824806456223334400, 3819517371706716979200, 119824806456223334400,
    1906043212617429811200, 3808363693445323161600, 1906043210845755801600, 239651425334958489600,
    3819517371727478784000, 954879346471757414400, 3812086432328476262400, 952092740657243750400,
    15248316673818624000000, 954879342931869696000, 3808363705859152281600, 953021606308714905600,
    958008139579392000, 1917189632349437952000, 239530547773440000, 32157066943422350858649600,
    15697888931808804864000, 237790060325162188800, 237790060325162188800, 237790060325162188800,
    237790060325162188800]

/-- The static `ℓ¹` bounds of the variables. -/
def LLF (i : Nat) : Nat := LLFl.getD i 0

/-- The minimal widths `b` of the fast images (list). -/
def bMinLFl : List Nat :=
  [0, 0, 0, 0, 59, 59, 59, 59, 55, 55, 55, 52, 51, 51, 53, 48, 47, 48, 49, 45, 47, 42, 44, 62, 58,
    58, 63, 59, 56, 61, 61, 59, 61, 61, 59, 63, 64, 64, 62, 63, 60, 60, 64, 60, 62, 62, 62, 63,
    62, 63, 62, 62, 62, 63, 59, 56, 62, 65, 60, 56, 63, 56, 63, 63, 63, 63, 63, 62, 62, 65, 60,
    59, 60, 63, 59, 60, 64, 0, 0, 0, 67, 63, 63, 63, 61, 61, 65, 60, 60, 60, 63, 64, 60, 67, 62,
    63, 62, 64, 63, 67, 63, 0, 0, 0, 0, 0, 0, 0, 56, 0, 49, 0, 0, 0, 0, 59, 62, 60, 58, 63, 58,
    62, 63, 62, 59, 63, 61, 63, 61, 65, 61, 63, 61, 51, 62, 49, 76, 65, 59, 59, 59, 59]

/-- The minimal widths `b` of the fast images. -/
def bMinLF (i : Nat) : Nat := bMinLFl.getD i 0

/-- The minimal widths `W` of the fast images (list). -/
def wMinLFl : List Nat :=
  [0, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 0, 0, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 0, 0, 0, 0, 0, 0, 0, 16, 0, 16, 0, 0, 0, 0, 16, 16, 16, 16, 16, 16,
    16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]

/-- The minimal widths `W` of the fast images. -/
def wMinLF (i : Nat) : Nat := wMinLFl.getD i 0

/-- **The Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`). -/
def KvLF (b W R : Nat) (i : Nat) : Int :=
  match kindLF i with
  | 0 => ((1 <<< SLF : Nat) : Int) * ((1 <<< (b * (NLF + W * (MLF + R * DLF))) : Nat) : Int)
  | 1 => 2 * ((1 <<< (b * W) : Nat) : Int)
  | 2 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) + 1
  | 4 =>
    ((1 <<< (SLF + 6) : Nat) : Int) * ((1 <<< (b * (NLF + W * (MLF + R * DLF))) : Nat) : Int) +
      ((1 <<< (SLF - 1) : Nat) : Int) * (((1 <<< (b * (NLF + W * (MLF + R * (DLF + 1)))) : Nat) : Int) +
        ((1 <<< (b * (NLF + W * (MLF + R * (DLF - 1)))) : Nat) : Int))
  | 5 => 0
  | _ =>
    if bMinLF i ≤ b ∧ wMinLF i ≤ W then
      ((famTB b W R NLF MLF DLF (c0LF i) (oddLF i) drLF dwLF (famLF i) : Nat) : Int) -
        ((famO b W R NLF MLF DLF dwLF (famLF i) : Nat) : Int)
    else famPack b W R NLF MLF DLF (if oddLF i then -1 else 1) (c0LF i : Int) 0 0 ddLF drLF 0
      (famLF i)

end PlasmaLean.Design.RationalStellaratorGC
