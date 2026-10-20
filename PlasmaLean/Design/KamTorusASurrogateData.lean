/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.KronExpr

/-!
# Data of the surrogate-torus certificates of torus A (KAM route, final stage)

Untrusted data, produced by `scripts/kam_oracle/surrogate_emit.py`; every property is proved in
`Design/KamTorusASurrogateCheck` and `Design/KamTorusASurrogate`.

* `listQ`: the cosine coefficients (times `2^65`) of a trigonometric polynomial
  `q ≈ 1/(D³ W₀²)` on the surrogate torus of `Design/KamTorusAFrameData`, modes `0 ≤ k ≤ 14`,
  `|m| ≤ 10` (row-major, `k = 0, m < 0` entries zero). Its compact grid `gQc` (centre `(14, 10)`,
  scale `2^66 = σ₁²`) is symmetric under the reflection `(i, j) ↦ (28 − i, 20 − j)`.
* `treeD`, `treeP`: expression trees (Horner form in `r = R − 1`, then `z`) of `8 D` and `128 P`
  (`D = Dp`, `P = Pp` of `Design/KamNewtonField`), homogenized with the scale variables `t`, `V`.
  Variables: `0 r, 1 z, 2 C = cos 2φ, 3 S = sin 2φ, 4 t, 5 V, 6 a = ∂_θ R, 7 b = ∂_θ z`.
* `treeW = a z − b r` (the winding form `W₀`).
* `c0W`, `e0T`: oracle values of the centre coefficient of `Ŵ₀` and of the centre digit of the
  Kronecker image of `(t + r)³ P̂ q̂` (any values are sound: the first is only subtracted, the
  second is checked by the kernel).
-/

@[expose] public section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Certificates.KronExpr

/-- `2^65 ×` the cosine coefficients of `q` (row-major, `0 ≤ k ≤ 14`, `|m| ≤ 10`). -/
def listQ : List ℤ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 156930009624666859110400, 17908548661303295606784,
    -1142836172530749931520, -212581094789978587136, -548707341431949312, 1263719113034527232,
    40645531424658752, -8242026191191536, -188198400955567, 37116963016609, 4328874254028,
    -5379886560433, -22295234079363, 737220886912047, 5141307390361968, -36974448039618256,
    -1324127127628862208, 9700577599522539520, 214302435593570877440, -401396682053644451840,
    -43953433704523553046528, -147903838468500109656064, -3209037830552877006848,
    1684585531933252124672, 107738817660570173440, -7580134092733988864, -1034087301789915136,
    11151412187033888, 5832225857035745, 87267879971254, -42155531998841, -928945320460,
    5911453486826, -63692778619008, -935237063218665, -4868958182157678, 130542854687478400,
    707448025735240960, -10251815342295107584, -187691945592496324608, 2312211696601706004480,
    31029061529670533513216, 39449367428367130820608, -2616225845502792433664,
    -1165033065225339011072, -18352818577280221184, 9725367165118087168, 487746079183178368,
    -48611014378113672, -4261170978000405, 116419877929663, 26021687721590, -50695202666,
    1115493666637, 115279154228976, 1104411277611399, -5822715242053134, -139301769458830784,
    -344383878697381440, 8563617965520753664, 40360192915128524800, -1705424349902467497984,
    -16574173280462536966144, -6780547181834647109632, 4442948293254489047040,
    371398827591835451392, -20984590032484159488, -6409581172716095488, -60516311713139144,
    50260999482032808, 1964667267589572, -273533281500898, -12901808960560, 881425749030,
    -13181979468735, -125821513354247, -13726074381724, 15714201417924872, 133640003374274400,
    420122206820502528, -13456557348165396480, -27200982996255506432, 1917592139113852829696,
    5547349042466849292288, 333914512581914656768, -1797616432352207306752, -63452939394831523840,
    33008489232474636288, 2238063614873824256, -152486543579398208, -31197824326294120,
    47192733943545, 208796276704328, 6372563721915, -1342523160435, 13609159378377,
    54418224720725, -1201759102763733, -11678921311558948, -86286853015764048, 72193202344902528,
    13070474618805602304, -65713199035205959680, -1179184029973652701184, -1290990604272801415168,
    307994821971176718336, 441165145511489241088, -21532904033962700800, -16648222836571998208,
    -365963207010502656, 204976602376010944, 10339295436363568, -1008351068152376,
    -127852973512889, 1892752052006, 793437418622, -11160249562813, 27234468775540,
    1779130194996636, 9717140119677044, -19965803941453792, -649021602675533440,
    -2188100305413810688, 71614621242615537664, 506389186384170188800, 214113812006891847680,
    -221597096244614791168, -73848742174065065984, 40748672771406168064, 4496594006634708992,
    -237748555223082784, -103313635176081232, -1364293241669956, 1082866283839552, 41452131154304,
    -5803618657074, -429367120124, 4418848517285, -86995041023115, -937928295352645,
    185998333330258, -27842300771707316, 474600028607014528, 1217309582751825152,
    -63915343695942197248, -150435247044286808064, -456741974920365952, 74461729156858970112,
    5068191205301828608, -15096146964472352768, -743367139742423040, 408632394339414656,
    29083278501914720, -1984789507975264, -526921619553462, -1528549245398, 4843964622148,
    144170311573, -576423498135, 137247235450872, 132315982864715, 720805711234032,
    19328393185061816, -439642075717268992, 1749991447843257600, 34020307719615094784,
    32176618037657706496, -16357963199438716928, -17287942978858766336, 2427151349775856128,
    3597611828301761536, -127776271080441216, -169351321550529024, -4641975291815980,
    2913060453659373, 141907331929921, -14207818269232, -2297872833835, 20242202033, 467246678794,
    -59907327757696, -445807306389793, -1947251043100696, 24855084678885544, 135939602487229440,
    -2336134788513584640, -12722869764029431808, -4552597695499203072, 8334699997847581696,
    2944835491143975424, -2175222717978636288, -609788440194556160, 320152159776026944,
    41323756194126696, -1960674510812759, -1177492033675561, -20126135938411, 17081223163067,
    585856436720, -89221351591, 7105764016853, 40588623415819, -121159358602542, 2112451867504414,
    -13996736415043866, -57916491056882704, 1784737313896791040, 3536218959238533632,
    -486913797374678784, -2469199466922859520, -76193296058068704, 714926843254506496,
    50001520727192968, -110667449114120224, -6684550424891365, 4067951665750202, 291647366613002,
    -19108245637397, -6468729573091, -48744356404, 84634350575, -7648199373175, -3426123218614,
    10362062805725, -1026522403707496, 13179370896296776, -46610972177813624, -851136709127585792,
    -714377464812502784, 600655390498058752, 529465239292857344, -171274512555851456,
    -166070261452191808, 16667984792357714, 26326996730690324, -590544344973312,
    -1422171989442517, -46687096060259, 33828175551407, 1532621642827, -153147557209,
    -29723987292, 344243000306, 372044914113, 178116828517349, -597574929586054,
    -6205567123151378, 67022377311972288, 291489311496561152, 76562873352415872,
    -249838694811683488, -81203051637277712, 94015179190968736, 28899645432741588,
    -18926334906487576, -4583377333098139, 2345525688439786, 328740938778096, -12607630535855,
    -10903514251218, -238551922691, 224628859296, 6632558968, -1333869120902, 7522805189652,
    -93472226376688, 374631990417708, 2014427872224270, -44816003667665504, -77419513862738016,
    25028354674550120, 69460935768936968, -3343786286224762, -27247803156784248, -903930574703847,
    5909860563283712, 431690351758490, -761939650640967, -52827226413694, 36255013727924,
    2545965181119, -143324656917, -63050703964, -863133672, -24400312534, 1948154646023,
    36389643942713, -408839424532936, 1316861413861524, 19607164719450032, 14564412383419248,
    -18242440616766096, -14167521957308202, 7312466137452640, 5886274795064347, -1505580929225387,
    -1383781568892536, 104336043607747, 183872827152927, -1366036324768, -10584684422721,
    -407739975054, 350905334757, 14604540485, -1302383731]

/-- Half-window lookup of `listQ` on the compact `q` grid (`14 ≤ i ≤ 28`, `j ≤ 20`). -/
def hQ (i j : ℕ) : ℤ := if 14 ≤ i ∧ i ≤ 28 ∧ j ≤ 20 then listQ.getD ((i - 14) * 21 + j) 0 else 0

/-- The compact grid of `q̂ = σ₁² u^{14} v^{10} q` (cosine symmetrization of `hQ`). -/
def gQc (i j : ℕ) : ℤ := hQ i j + hQ (28 - i) (20 - j)

/-- Coefficient of `r^0` in the Horner form of `8 D` (homogenized). -/
def treeD0 : Ex :=
  (.mul (.mul (.add (.mul (.mul (.add (.mul (.mul (.cst (4)) (.var 2)) (.var 1)) (.mul (.mul
    (.cst (4)) (.var 3)) (.var 4))) (.var 1)) (.var 1)) (.mul (.mul (.mul (.mul (.cst (8)) (.var
    5)) (.var 4)) (.var 4)) (.var 4))) (.var 4)) (.var 4))

/-- Coefficient of `r^1` in the Horner form of `8 D` (homogenized). -/
def treeD1 : Ex :=
  (.mul (.mul (.mul (.add (.mul (.mul (.cst (8)) (.var 2)) (.var 1)) (.mul (.mul (.cst (16))
    (.var 5)) (.var 4))) (.var 4)) (.var 4)) (.var 4))

/-- Coefficient of `r^2` in the Horner form of `8 D` (homogenized). -/
def treeD2 : Ex :=
  (.mul (.mul (.mul (.add (.mul (.cst (-4)) (.var 3)) (.mul (.cst (8)) (.var 5))) (.var 4)) (.var
    4)) (.var 4))

/-- Coefficient of `r^3` in the Horner form of `8 D` (homogenized). -/
def treeD3 : Ex :=
  (.mul (.add (.mul (.mul (.cst (-4)) (.var 2)) (.var 1)) (.mul (.mul (.cst (-4)) (.var 3)) (.var
    4))) (.var 4))

/-- Coefficient of `r^4` in the Horner form of `8 D` (homogenized). -/
def treeD4 : Ex :=
  (.add (.mul (.mul (.cst (-1)) (.var 2)) (.var 1)) (.mul (.mul (.cst (-1)) (.var 3)) (.var 4)))

/-- The tree of `8 D` (Horner form in `r`). -/
def treeD : Ex :=
  (.add (.mul (.add (.mul (.add (.mul (.add (.mul treeD4 (.var 0)) treeD3) (.var 0)) treeD2)
    (.var 0)) treeD1) (.var 0)) treeD0)

/-- Coefficient of `r^0` in the Horner form of `128 P` (homogenized). -/
def treeP0 : Ex :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.mul
    (.mul (.cst (-32)) (.var 2)) (.var 3)) (.var 1)) (.mul (.mul (.mul (.cst (64)) (.var 2))
    (.var 2)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.cst (128)) (.var 2)) (.var 3)) (.var
    4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.mul (.mul (.cst (64)) (.var 3)) (.var 3))
    (.mul (.mul (.cst (128)) (.var 3)) (.var 5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul
    (.mul (.mul (.mul (.mul (.mul (.cst (-64)) (.var 2)) (.var 5)) (.var 4)) (.var 4)) (.var 4))
    (.var 4))) (.var 1)) (.var 1)) (.var 1)) (.var 4)) (.var 4)) (.var 4)) (.var 4))

/-- Coefficient of `r^1` in the Horner form of `128 P` (homogenized). -/
def treeP1 : Ex :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul
    (.mul (.cst (32)) (.var 2)) (.var 2)) (.mul (.mul (.cst (32)) (.var 3)) (.var 3))) (.var 1))
    (.mul (.mul (.mul (.cst (-96)) (.var 2)) (.var 3)) (.var 4))) (.var 1)) (.mul (.mul (.add
    (.add (.mul (.mul (.cst (256)) (.var 2)) (.var 2)) (.mul (.mul (.cst (-48)) (.var 3)) (.var
    3))) (.mul (.mul (.cst (320)) (.var 3)) (.var 5))) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul
    (.mul (.add (.mul (.mul (.cst (256)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-128)) (.var 2))
    (.var 5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.mul (.mul (.cst
    (224)) (.var 3)) (.var 5)) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.var 1)) (.var
    4)) (.var 4)) (.var 4)) (.var 4))

/-- Coefficient of `r^2` in the Horner form of `128 P` (homogenized). -/
def treeP2 : Ex :=
  (.mul (.mul (.mul (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst
    (-112)) (.var 2)) (.var 3)) (.var 1)) (.mul (.add (.mul (.mul (.cst (288)) (.var 2)) (.var
    2)) (.mul (.mul (.cst (256)) (.var 3)) (.var 5))) (.var 4))) (.var 1)) (.mul (.mul (.add
    (.mul (.mul (.cst (-80)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-64)) (.var 2)) (.var 5)))
    (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.add (.mul (.mul (.cst (256)) (.var
    2)) (.var 2)) (.mul (.mul (.cst (-128)) (.var 3)) (.var 3))) (.mul (.mul (.cst (832)) (.var
    3)) (.var 5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.mul (.mul
    (.cst (-32)) (.var 2)) (.var 5)) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.var 4))
    (.var 4)) (.var 4)) (.var 4))

/-- Coefficient of `r^3` in the Horner form of `128 P` (homogenized). -/
def treeP3 : Ex :=
  (.mul (.mul (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (64))
    (.var 2)) (.var 3)) (.var 1)) (.mul (.add (.add (.mul (.mul (.cst (16)) (.var 2)) (.var 2))
    (.mul (.mul (.cst (128)) (.var 3)) (.var 3))) (.mul (.mul (.cst (64)) (.var 3)) (.var 5)))
    (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.cst (-320)) (.var 2)) (.var 3)) (.var 4))
    (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.add (.mul (.mul (.cst (288)) (.var 2)) (.var
    2)) (.mul (.mul (.cst (-112)) (.var 3)) (.var 3))) (.mul (.mul (.cst (1376)) (.var 3)) (.var
    5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.add (.mul (.mul (.cst
    (-256)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-192)) (.var 2)) (.var 5))) (.var 4)) (.var
    4)) (.var 4)) (.var 4))) (.var 1)) (.var 4)) (.var 4)) (.var 4))

/-- Coefficient of `r^4` in the Horner form of `128 P` (homogenized). -/
def treeP4 : Ex :=
  (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (96))
    (.var 2)) (.var 3)) (.var 1)) (.mul (.add (.mul (.mul (.cst (-96)) (.var 2)) (.var 2)) (.mul
    (.mul (.cst (96)) (.var 3)) (.var 3))) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.cst
    (248)) (.var 2)) (.var 3)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.add (.mul
    (.mul (.cst (-256)) (.var 2)) (.var 2)) (.mul (.mul (.cst (64)) (.var 3)) (.var 3))) (.mul
    (.mul (.cst (1344)) (.var 3)) (.var 5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul
    (.mul (.mul (.add (.mul (.mul (.cst (-464)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-400))
    (.var 2)) (.var 5))) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul
    (.mul (.mul (.add (.mul (.mul (.cst (64)) (.var 3)) (.var 3)) (.mul (.mul (.cst (-64)) (.var
    3)) (.var 5))) (.var 4)) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 4)) (.var 4))

/-- Coefficient of `r^5` in the Horner form of `128 P` (homogenized). -/
def treeP5 : Ex :=
  (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (32)) (.var
    2)) (.var 3)) (.var 1)) (.mul (.add (.mul (.mul (.cst (-32)) (.var 2)) (.var 2)) (.mul (.mul
    (.cst (32)) (.var 3)) (.var 3))) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.cst (528))
    (.var 2)) (.var 3)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.add (.mul (.mul
    (.cst (-592)) (.var 2)) (.var 2)) (.mul (.mul (.cst (48)) (.var 3)) (.var 3))) (.mul (.mul
    (.cst (816)) (.var 3)) (.var 5))) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul
    (.mul (.add (.mul (.mul (.cst (-224)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-384)) (.var 2))
    (.var 5))) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.mul
    (.add (.mul (.mul (.cst (160)) (.var 3)) (.var 3)) (.mul (.mul (.cst (-280)) (.var 3)) (.var
    5))) (.var 4)) (.var 4)) (.var 4)) (.var 4)) (.var 4))) (.var 4))

/-- Coefficient of `r^6` in the Horner form of `128 P` (homogenized). -/
def treeP6 : Ex :=
  (.mul (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (284)) (.var 2)) (.var 3))
    (.var 1)) (.mul (.add (.add (.mul (.mul (.cst (-400)) (.var 2)) (.var 2)) (.mul (.mul (.cst
    (-40)) (.var 3)) (.var 3))) (.mul (.mul (.cst (288)) (.var 3)) (.var 5))) (.var 4))) (.var
    1)) (.mul (.mul (.add (.mul (.mul (.cst (-20)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-176))
    (.var 2)) (.var 5))) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.mul (.mul (.cst
    (160)) (.var 3)) (.var 3)) (.mul (.mul (.cst (-480)) (.var 3)) (.var 5))) (.var 4)) (.var 4))
    (.var 4))) (.var 4)) (.var 4))

/-- Coefficient of `r^7` in the Horner form of `128 P` (homogenized). -/
def treeP7 : Ex :=
  (.mul (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (56)) (.var 2)) (.var 3)) (.var 1))
    (.mul (.add (.add (.mul (.mul (.cst (-124)) (.var 2)) (.var 2)) (.mul (.mul (.cst (-44))
    (.var 3)) (.var 3))) (.mul (.mul (.cst (48)) (.var 3)) (.var 5))) (.var 4))) (.var 1)) (.mul
    (.mul (.add (.mul (.mul (.cst (-40)) (.var 2)) (.var 3)) (.mul (.mul (.cst (-32)) (.var 2))
    (.var 5))) (.var 4)) (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.mul (.mul (.cst (100))
    (.var 3)) (.var 3)) (.mul (.mul (.cst (-400)) (.var 3)) (.var 5))) (.var 4)) (.var 4)) (.var
    4))) (.var 4))

/-- Coefficient of `r^8` in the Horner form of `128 P` (homogenized). -/
def treeP8 : Ex :=
  (.add (.mul (.add (.mul (.add (.mul (.mul (.mul (.cst (2)) (.var 2)) (.var 3)) (.var 1)) (.mul
    (.add (.mul (.mul (.cst (-20)) (.var 2)) (.var 2)) (.mul (.mul (.cst (-16)) (.var 3)) (.var
    3))) (.var 4))) (.var 1)) (.mul (.mul (.mul (.mul (.cst (-50)) (.var 2)) (.var 3)) (.var 4))
    (.var 4))) (.var 1)) (.mul (.mul (.mul (.add (.mul (.mul (.cst (56)) (.var 3)) (.var 3))
    (.mul (.mul (.cst (-160)) (.var 3)) (.var 5))) (.var 4)) (.var 4)) (.var 4)))

/-- Coefficient of `r^9` in the Horner form of `128 P` (homogenized). -/
def treeP9 : Ex :=
  (.add (.mul (.add (.mul (.add (.mul (.mul (.cst (-2)) (.var 2)) (.var 2)) (.mul (.mul (.cst
    (-2)) (.var 3)) (.var 3))) (.var 1)) (.mul (.mul (.mul (.cst (-18)) (.var 2)) (.var 3)) (.var
    4))) (.var 1)) (.mul (.mul (.add (.mul (.mul (.cst (27)) (.var 3)) (.var 3)) (.mul (.mul
    (.cst (-24)) (.var 3)) (.var 5))) (.var 4)) (.var 4)))

/-- Coefficient of `r^10` in the Horner form of `128 P` (homogenized). -/
def treeP10 : Ex :=
  (.add (.mul (.mul (.mul (.cst (-2)) (.var 2)) (.var 3)) (.var 1)) (.mul (.mul (.mul (.cst (8))
    (.var 3)) (.var 3)) (.var 4)))

/-- Coefficient of `r^11` in the Horner form of `128 P` (homogenized). -/
def treeP11 : Ex :=
  (.mul (.mul (.cst (1)) (.var 3)) (.var 3))

/-- The tree of `128 P` (Horner form in `r`). -/
def treeP : Ex :=
  (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul (.add (.mul
    (.add (.mul (.add (.mul (.add (.mul treeP11 (.var 0)) treeP10) (.var 0)) treeP9) (.var 0))
    treeP8) (.var 0)) treeP7) (.var 0)) treeP6) (.var 0)) treeP5) (.var 0)) treeP4) (.var 0))
    treeP3) (.var 0)) treeP2) (.var 0)) treeP1) (.var 0)) treeP0)

/-- The tree of `W₀ = a z − b r`. -/
def treeW : Ex := .sub (.mul (.var 6) (.var 1)) (.mul (.var 7) (.var 0))

/-- Oracle value of the centre coefficient of `Ŵ₀` (scale `σ₁²`). -/
def c0W : ℤ := -1338131791472789936

set_option linter.style.longLine false in
/-- Oracle value of the centre digit (`b = 560`, offset `2^559`) of the Kronecker image of
`(t + r)³ P̂ q̂`. -/
def e0T : ℕ := 1886981391755373307968748102015919540083491070014512220155913053753060110354885925691996294271414379503690287773831574845255652167977682543047992797596684860296499455162

end PlasmaLean.Design.KamNewton
