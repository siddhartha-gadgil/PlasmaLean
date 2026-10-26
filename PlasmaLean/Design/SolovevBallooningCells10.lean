/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 10

52 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (evaluation certificate `ballooning_box`: one kernel leaf per ball
operation) and refers to its corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(2816/NT, 14336/NS)`. -/
theorem cn10_0 : cornerOK gdata (2816) (14336)
    [379567245, 367200151, 509288344, 187968945, 162929058, 23063064, 16146092] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 14336/NS)`. -/
theorem cn10_1 : cornerOK gdata (3072) (14336)
    [379567245, 367200151, 509288344, 187968945, 162929058, 23063064, 16146092] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 16384/NS)`. -/
theorem cn10_2 : cornerOK gdata (2816) (16384)
    [379567245, 367200151, 509288344, 187968945, 162929058, 23063064, 16146092] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 16384/NS)`. -/
theorem cn10_3 : cornerOK gdata (3072) (16384)
    [379567245, 367200151, 509288344, 187968945, 162929058, 23063064, 16146092] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 12288/NS)`. -/
theorem cn10_4 : cornerOK gdata (3072) (12288)
    [314524516, 258489827, 418644410, 132007217, 136059318, 16159357, 13585514] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 12288/NS)`. -/
theorem cn10_5 : cornerOK gdata (3328) (12288)
    [314524516, 258489827, 418644410, 132007217, 136059318, 16159357, 13585514] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 14336/NS)`. -/
theorem cn10_6 : cornerOK gdata (3328) (14336)
    [317309072, 278837904, 447349054, 144716986, 147754775, 17809666, 14977850] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 16384/NS)`. -/
theorem cn10_7 : cornerOK gdata (3328) (16384)
    [317309072, 278837904, 447349054, 144716986, 147754775, 17809666, 14977850] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 12288/NS)`. -/
theorem cn10_8 : cornerOK gdata (3584) (12288)
    [530549698, 197199680, 781289473, 107152190, 294894862, 12367010, 31975547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 14336/NS)`. -/
theorem cn10_9 : cornerOK gdata (3584) (14336)
    [268640960, 204808690, 393747373, 107592106, 133848992, 13257080, 13808615] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 16384/NS)`. -/
theorem cn10_10 : cornerOK gdata (3584) (16384)
    [530549698, 204808690, 781289473, 107592106, 294894862, 13257080, 31975547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3712/NT, 12288/NS)`. -/
theorem cn10_11 : cornerOK gdata (3712) (12288)
    [530549698, 197199680, 781289473, 107152190, 294894862, 12367010, 31975547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3712/NT, 16384/NS)`. -/
theorem cn10_12 : cornerOK gdata (3712) (16384)
    [530549698, 197199680, 781289473, 107152190, 294894862, 12367010, 31975547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 12288/NS)`. -/
theorem cn10_13 : cornerOK gdata (3840) (12288)
    [518997925, 155902705, 770916557, 84939234, 293186780, 9874612, 31897519] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 16384/NS)`. -/
theorem cn10_14 : cornerOK gdata (3840) (16384)
    [518997925, 155902705, 770916557, 84939234, 293186780, 9874612, 31897519] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3968/NT, 12288/NS)`. -/
theorem cn10_15 : cornerOK gdata (3968) (12288)
    [508392708, 115992552, 760161452, 63378464, 290750983, 7472214, 31716306] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3968/NT, 16384/NS)`. -/
theorem cn10_16 : cornerOK gdata (3968) (16384)
    [508392708, 115992552, 760161452, 63378464, 290750983, 7472214, 31716306] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 12288/NS)`. -/
theorem cn10_17 : cornerOK gdata (4096) (12288)
    [498218222, 77922940, 748464764, 42602037, 287563850, 5155710, 31434069] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 16384/NS)`. -/
theorem cn10_18 : cornerOK gdata (4096) (16384)
    [498218222, 77922940, 748464764, 42602037, 287563850, 5155710, 31434069] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 16384/NS)`. -/
theorem cn10_19 : cornerOK gdata (-4096) (16384)
    [3678306019, 254133439, 1782944349, 90397577, 351438843, 11129714, 19810352] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 16384/NS)`. -/
theorem cn10_20 : cornerOK gdata (-3968) (16384)
    [3757851095, 380932355, 1822378633, 135512730, 357565643, 16735454, 20012687] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 18432/NS)`. -/
theorem cn10_21 : cornerOK gdata (-4096) (18432)
    [5777181591, 369541083, 2660862089, 127315728, 494574726, 15705428, 24733484] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 18432/NS)`. -/
theorem cn10_22 : cornerOK gdata (-3968) (18432)
    [5910137410, 563470263, 2724378564, 193920007, 503918448, 24016945, 24998964] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 20480/NS)`. -/
theorem cn10_23 : cornerOK gdata (-4096) (20480)
    [5777181591, 369541083, 2660862089, 127315728, 494574726, 15705428, 24733484] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 20480/NS)`. -/
theorem cn10_24 : cornerOK gdata (-3968) (20480)
    [5910137410, 563470263, 2724378564, 193920007, 503918448, 24016945, 24998964] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 16384/NS)`. -/
theorem cn10_25 : cornerOK gdata (-3840) (16384)
    [3835399584, 511362257, 1860115701, 182537082, 362706450, 22464485, 20091547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 18432/NS)`. -/
theorem cn10_26 : cornerOK gdata (-3840) (18432)
    [6038089661, 763258164, 2785082350, 262910348, 511768254, 32482386, 25090929] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 20480/NS)`. -/
theorem cn10_27 : cornerOK gdata (-3840) (20480)
    [6038089661, 763258164, 2785082350, 262910348, 511768254, 32482386, 25090929] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3712/NT, 16384/NS)`. -/
theorem cn10_28 : cornerOK gdata (-3712) (16384)
    [3907316352, 642608502, 1894471300, 230146689, 366546152, 28163073, 20091547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3712/NT, 18432/NS)`. -/
theorem cn10_29 : cornerOK gdata (-3712) (18432)
    [6156974589, 964232905, 2841232296, 332426405, 517823351, 40874088, 25090929] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3712/NT, 20480/NS)`. -/
theorem cn10_30 : cornerOK gdata (-3712) (20480)
    [6156974589, 964232905, 2841232296, 332426405, 517823351, 40874088, 25090929] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 16384/NS)`. -/
theorem cn10_31 : cornerOK gdata (-3584) (16384)
    [3907316352, 642608502, 1894471300, 230146689, 366546152, 28163073, 20029712] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 18432/NS)`. -/
theorem cn10_32 : cornerOK gdata (-3584) (18432)
    [6156974589, 1310669353, 2841232296, 472277581, 517823351, 55170853, 24996959] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 20480/NS)`. -/
theorem cn10_33 : cornerOK gdata (-3584) (20480)
    [6156974589, 1645745364, 2841232296, 577860402, 517823351, 67605915, 24996959] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 16384/NS)`. -/
theorem cn10_34 : cornerOK gdata (-3584) (16384)
    [2595422864, 850247492, 1310172608, 321243077, 238159133, 37380750, 11471305] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 16384/NS)`. -/
theorem cn10_35 : cornerOK gdata (-3328) (16384)
    [2595422864, 850247492, 1310172608, 321243077, 238159133, 37380750, 11745264] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 17408/NS)`. -/
theorem cn10_36 : cornerOK gdata (-3584) (17408)
    [3308760652, 1052675364, 1633583626, 388141639, 286395978, 45290482, 13008071] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 17408/NS)`. -/
theorem cn10_37 : cornerOK gdata (-3328) (17408)
    [3308760652, 1052675364, 1633583626, 388141639, 286395978, 45290482, 13008071] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 18432/NS)`. -/
theorem cn10_38 : cornerOK gdata (-3328) (18432)
    [4246136216, 1310669353, 2052922518, 472277581, 347486933, 55170853, 14800538] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 19456/NS)`. -/
theorem cn10_39 : cornerOK gdata (-3584) (19456)
    [5488507908, 1645745364, 2600602286, 577860402, 425687882, 67605915, 16902104] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 19456/NS)`. -/
theorem cn10_40 : cornerOK gdata (-3328) (19456)
    [5488507908, 1645745364, 2600602286, 577860402, 425687882, 67605915, 16902104] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 20480/NS)`. -/
theorem cn10_41 : cornerOK gdata (-3328) (20480)
    [5488507908, 1645745364, 2600602286, 577860402, 425687882, 67605915, 16902104] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 16384/NS)`. -/
theorem cn10_42 : cornerOK gdata (-3264) (16384)
    [2438935053, 546033312, 1126234795, 184651647, 220334652, 22592244, 11745264] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 18432/NS)`. -/
theorem cn10_43 : cornerOK gdata (-3264) (18432)
    [3739062979, 799024449, 1642978526, 259245597, 303570994, 32163307, 14253024] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 20480/NS)`. -/
theorem cn10_44 : cornerOK gdata (-3264) (20480)
    [3739062979, 799024449, 1642978526, 259245597, 303570994, 32163307, 14253024] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 16384/NS)`. -/
theorem cn10_45 : cornerOK gdata (-3200) (16384)
    [2426566169, 573062213, 1120008849, 192993779, 217936856, 23496007, 11482068] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 18432/NS)`. -/
theorem cn10_46 : cornerOK gdata (-3200) (18432)
    [3718985007, 837013814, 1634699394, 270075083, 300339350, 33365828, 13915823] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 20480/NS)`. -/
theorem cn10_47 : cornerOK gdata (-3200) (20480)
    [3718985007, 837013814, 1634699394, 270075083, 300339350, 33365828, 13915823] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 16384/NS)`. -/
theorem cn10_48 : cornerOK gdata (-3136) (16384)
    [2410457550, 597382361, 1112245228, 200317541, 215203866, 24256500, 11197799] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 18432/NS)`. -/
theorem cn10_49 : cornerOK gdata (-3136) (18432)
    [3690477948, 870695693, 1622888710, 279304765, 296448371, 34349380, 13545410] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 20480/NS)`. -/
theorem cn10_50 : cornerOK gdata (-3136) (20480)
    [3690477948, 870695693, 1622888710, 279304765, 296448371, 34349380, 13545410] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 16384/NS)`. -/
theorem cn10_51 : cornerOK gdata (-3072) (16384)
    [2389080344, 618835688, 1102264234, 206566170, 212032517, 24868303, 10888892] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 18432/NS)`. -/
theorem cn10_52 : cornerOK gdata (-3072) (18432)
    [3653344187, 899997545, 1607646801, 286931363, 291923488, 35111822, 13145658] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 20480/NS)`. -/
theorem cn10_53 : cornerOK gdata (-3072) (20480)
    [3653344187, 899997545, 1607646801, 286931363, 291923488, 35111822, 13145658] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 16384/NS)`. -/
theorem cn10_54 : cornerOK gdata (-3008) (16384)
    [2362584962, 637069149, 1090162802, 211645304, 208446356, 25319419, 10559606] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 18432/NS)`. -/
theorem cn10_55 : cornerOK gdata (-3008) (18432)
    [3608073749, 924220332, 1589290300, 292746445, 286827620, 35631367, 12722441] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 20480/NS)`. -/
theorem cn10_56 : cornerOK gdata (-3008) (20480)
    [3608073749, 924220332, 1589290300, 292746445, 286827620, 35631367, 12722441] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 16384/NS)`. -/
theorem cn10_57 : cornerOK gdata (-2944) (16384)
    [2330081254, 651991616, 1075709802, 215536470, 204390244, 25615065, 10209795] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 18432/NS)`. -/
theorem cn10_58 : cornerOK gdata (-2944) (18432)
    [3552340009, 943289777, 1566803916, 296750577, 281031880, 35908627, 12274081] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 20480/NS)`. -/
theorem cn10_59 : cornerOK gdata (-2944) (20480)
    [3552340009, 943289777, 1566803916, 296750577, 281031880, 35908627, 12274081] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 16384/NS)`. -/
theorem cn10_60 : cornerOK gdata (-2880) (16384)
    [2292195988, 663399053, 1059187675, 218221221, 199941238, 25742530, 9844756] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 18432/NS)`. -/
theorem cn10_61 : cornerOK gdata (-2880) (18432)
    [3486412129, 956771510, 1540474023, 298922433, 274642840, 35947045, 11804613] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 20480/NS)`. -/
theorem cn10_62 : cornerOK gdata (-2880) (20480)
    [3486412129, 956771510, 1540474023, 298922433, 274642840, 35947045, 11804613] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 16384/NS)`. -/
theorem cn10_63 : cornerOK gdata (-2816) (16384)
    [2247734482, 663399053, 1040027240, 218221221, 195022930, 25742530, 9461394] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 18432/NS)`. -/
theorem cn10_64 : cornerOK gdata (-2816) (18432)
    [3410407167, 964722412, 1510465275, 299292218, 267614752, 35947045, 11317376] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 20480/NS)`. -/
theorem cn10_65 : cornerOK gdata (-2816) (20480)
    [3410407167, 964722412, 1510465275, 299292218, 267614752, 35947045, 11317376] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 16384/NS)`. -/
theorem cn10_66 : cornerOK gdata (-2688) (16384)
    [775407367, 323513494, 378142161, 111984635, 68579920, 12517333, 3208123] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 17408/NS)`. -/
theorem cn10_67 : cornerOK gdata (-2816) (17408)
    [964326816, 370258065, 456318672, 126136547, 81012703, 14405878, 3549315] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 17408/NS)`. -/
theorem cn10_68 : cornerOK gdata (-2688) (17408)
    [964326816, 387326228, 458204735, 131036615, 81012703, 14760969, 3549315] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 18432/NS)`. -/
theorem cn10_69 : cornerOK gdata (-2688) (18432)
    [3226976510, 966656488, 1438185471, 297795278, 251637082, 35311724, 10297928] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 18432/NS)`. -/
theorem cn10_70 : cornerOK gdata (-2752) (18432)
    [3324196311, 966656488, 1476506272, 299292218, 259959587, 35748889, 10814962] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 20480/NS)`. -/
theorem cn10_71 : cornerOK gdata (-2752) (20480)
    [3324196311, 966656488, 1476506272, 299292218, 259959587, 35748889, 10814962] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 20480/NS)`. -/
theorem cn10_72 : cornerOK gdata (-2688) (20480)
    [3226976510, 966656488, 1438185471, 297795278, 251637082, 35311724, 10297928] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 16384/NS)`. -/
theorem cn10_73 : cornerOK gdata (-2560) (16384)
    [767859583, 333530494, 378142161, 114424849, 68323188, 12631339, 3096338] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 17408/NS)`. -/
theorem cn10_74 : cornerOK gdata (-2560) (17408)
    [953118785, 396813611, 458204735, 133497608, 80593362, 14826592, 3421994] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 18432/NS)`. -/
theorem cn10_75 : cornerOK gdata (-2560) (18432)
    [1189209687, 478325337, 559483585, 156364010, 95723192, 17468799, 3790274] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 19456/NS)`. -/
theorem cn10_76 : cornerOK gdata (-2688) (19456)
    [1490929406, 568705220, 687099252, 182571508, 114461942, 20743645, 4205536] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 19456/NS)`. -/
theorem cn10_77 : cornerOK gdata (-2560) (19456)
    [1490929406, 579373064, 687099252, 184490171, 114461942, 20743645, 4205536] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 20480/NS)`. -/
theorem cn10_78 : cornerOK gdata (-2560) (20480)
    [1490929406, 579373064, 687099252, 184490171, 114461942, 20743645, 4205536] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 16384/NS)`. -/
theorem cn10_79 : cornerOK gdata (-2432) (16384)
    [751643295, 337393160, 376683496, 114716970, 67525753, 12631339, 2973716] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 17408/NS)`. -/
theorem cn10_80 : cornerOK gdata (-2432) (17408)
    [930207589, 400334403, 455325283, 133497608, 79473683, 14826592, 3283162] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 18432/NS)`. -/
theorem cn10_81 : cornerOK gdata (-2432) (18432)
    [1156259794, 479088574, 554682461, 156364010, 94105620, 17463852, 3631564] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 19456/NS)`. -/
theorem cn10_82 : cornerOK gdata (-2432) (19456)
    [1444684992, 579373064, 679701990, 184490171, 112210241, 20644261, 4025704] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 20480/NS)`. -/
theorem cn10_83 : cornerOK gdata (-2432) (20480)
    [1444684992, 579373064, 679701990, 184490171, 112210241, 20644261, 4025704] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 16384/NS)`. -/
theorem cn10_84 : cornerOK gdata (-2304) (16384)
    [727365942, 337393160, 371224912, 114716970, 66099003, 12606840, 2841945] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 17408/NS)`. -/
theorem cn10_85 : cornerOK gdata (-2304) (17408)
    [897171722, 400334403, 447755900, 133434111, 77571930, 14642764, 3132822] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 18432/NS)`. -/
theorem cn10_86 : cornerOK gdata (-2304) (18432)
    [1110968548, 479088574, 543352358, 155688410, 91544109, 17113859, 3458063] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 19456/NS)`. -/
theorem cn10_87 : cornerOK gdata (-2304) (19456)
    [1110968548, 479088574, 543352358, 155688410, 91544109, 17113859, 3458063] = true := by
  bl_cert

/-- Kernel-checked box `[2816, 3072]/NT × [14336, 16384]/NS`. -/
theorem cov516 : Cover gdata (2816) (3072) (14336) (16384) := by
  ballooning_box "Q:cn10_0,cn10_1,cn10_2,cn10_3"

/-- Kernel-checked box `[3072, 3328]/NT × [12288, 14336]/NS`. -/
theorem cov517 : Cover gdata (3072) (3328) (12288) (14336) := by
  ballooning_box "Q:cn10_4,cn10_5,cn10_1,cn10_6"

/-- Kernel-checked box `[3072, 3328]/NT × [14336, 16384]/NS`. -/
theorem cov518 : Cover gdata (3072) (3328) (14336) (16384) := by
  ballooning_box "Q:cn10_1,cn10_6,cn10_3,cn10_7"

/-- Kernel-checked box `[3328, 3584]/NT × [12288, 14336]/NS`. -/
theorem cov519 : Cover gdata (3328) (3584) (12288) (14336) := by
  ballooning_box "Q:cn10_5,cn10_8,cn10_6,cn10_9"

/-- Kernel-checked box `[3328, 3584]/NT × [14336, 16384]/NS`. -/
theorem cov520 : Cover gdata (3328) (3584) (14336) (16384) := by
  ballooning_box "Q:cn10_6,cn10_9,cn10_7,cn10_10"

/-- Kernel-checked box `[3584, 3712]/NT × [12288, 16384]/NS`. -/
theorem cov521 : Cover gdata (3584) (3712) (12288) (16384) := by
  ballooning_box "Q:cn10_8,cn10_11,cn10_10,cn10_12"

/-- Kernel-checked box `[3712, 3840]/NT × [12288, 16384]/NS`. -/
theorem cov522 : Cover gdata (3712) (3840) (12288) (16384) := by
  ballooning_box "Q:cn10_11,cn10_13,cn10_12,cn10_14"

/-- Kernel-checked box `[3840, 3968]/NT × [12288, 16384]/NS`. -/
theorem cov523 : Cover gdata (3840) (3968) (12288) (16384) := by
  ballooning_box "Q:cn10_13,cn10_15,cn10_14,cn10_16"

/-- Kernel-checked box `[3968, 4096]/NT × [12288, 16384]/NS`. -/
theorem cov524 : Cover gdata (3968) (4096) (12288) (16384) := by
  ballooning_box "Q:cn10_15,cn10_17,cn10_16,cn10_18"

/-- Kernel-checked box `[-4096, -3968]/NT × [16384, 18432]/NS`. -/
theorem cov525 : Cover gdata (-4096) (-3968) (16384) (18432) := by
  ballooning_box "Q:cn10_19,cn10_20,cn10_21,cn10_22"

/-- Kernel-checked box `[-4096, -3968]/NT × [18432, 20480]/NS`. -/
theorem cov526 : Cover gdata (-4096) (-3968) (18432) (20480) := by
  ballooning_box "Q:cn10_21,cn10_22,cn10_23,cn10_24"

/-- Kernel-checked box `[-3968, -3840]/NT × [16384, 18432]/NS`. -/
theorem cov527 : Cover gdata (-3968) (-3840) (16384) (18432) := by
  ballooning_box "Q:cn10_20,cn10_25,cn10_22,cn10_26"

/-- Kernel-checked box `[-3968, -3840]/NT × [18432, 20480]/NS`. -/
theorem cov528 : Cover gdata (-3968) (-3840) (18432) (20480) := by
  ballooning_box "Q:cn10_22,cn10_26,cn10_24,cn10_27"

/-- Kernel-checked box `[-3840, -3712]/NT × [16384, 18432]/NS`. -/
theorem cov529 : Cover gdata (-3840) (-3712) (16384) (18432) := by
  ballooning_box "Q:cn10_25,cn10_28,cn10_26,cn10_29"

/-- Kernel-checked box `[-3840, -3712]/NT × [18432, 20480]/NS`. -/
theorem cov530 : Cover gdata (-3840) (-3712) (18432) (20480) := by
  ballooning_box "Q:cn10_26,cn10_29,cn10_27,cn10_30"

/-- Kernel-checked box `[-3712, -3584]/NT × [16384, 18432]/NS`. -/
theorem cov531 : Cover gdata (-3712) (-3584) (16384) (18432) := by
  ballooning_box "Q:cn10_28,cn10_31,cn10_29,cn10_32"

/-- Kernel-checked box `[-3712, -3584]/NT × [18432, 20480]/NS`. -/
theorem cov532 : Cover gdata (-3712) (-3584) (18432) (20480) := by
  ballooning_box "Q:cn10_29,cn10_32,cn10_30,cn10_33"

/-- Kernel-checked box `[-3584, -3328]/NT × [16384, 17408]/NS`. -/
theorem cov533 : Cover gdata (-3584) (-3328) (16384) (17408) := by
  ballooning_box "Q:cn10_34,cn10_35,cn10_36,cn10_37"

/-- Kernel-checked box `[-3584, -3328]/NT × [17408, 18432]/NS`. -/
theorem cov534 : Cover gdata (-3584) (-3328) (17408) (18432) := by
  ballooning_box "Q:cn10_36,cn10_37,cn10_32,cn10_38"

/-- Kernel-checked box `[-3584, -3328]/NT × [18432, 19456]/NS`. -/
theorem cov535 : Cover gdata (-3584) (-3328) (18432) (19456) := by
  ballooning_box "Q:cn10_32,cn10_38,cn10_39,cn10_40"

/-- Kernel-checked box `[-3584, -3328]/NT × [19456, 20480]/NS`. -/
theorem cov536 : Cover gdata (-3584) (-3328) (19456) (20480) := by
  ballooning_box "Q:cn10_39,cn10_40,cn10_33,cn10_41"

/-- Kernel-checked box `[-3328, -3264]/NT × [16384, 18432]/NS`. -/
theorem cov537 : Cover gdata (-3328) (-3264) (16384) (18432) := by
  ballooning_box "Q:cn10_35,cn10_42,cn10_38,cn10_43"

/-- Kernel-checked box `[-3328, -3264]/NT × [18432, 20480]/NS`. -/
theorem cov538 : Cover gdata (-3328) (-3264) (18432) (20480) := by
  ballooning_box "Q:cn10_38,cn10_43,cn10_41,cn10_44"

/-- Kernel-checked box `[-3264, -3200]/NT × [16384, 18432]/NS`. -/
theorem cov539 : Cover gdata (-3264) (-3200) (16384) (18432) := by
  ballooning_box "Q:cn10_42,cn10_45,cn10_43,cn10_46"

/-- Kernel-checked box `[-3264, -3200]/NT × [18432, 20480]/NS`. -/
theorem cov540 : Cover gdata (-3264) (-3200) (18432) (20480) := by
  ballooning_box "Q:cn10_43,cn10_46,cn10_44,cn10_47"

/-- Kernel-checked box `[-3200, -3136]/NT × [16384, 18432]/NS`. -/
theorem cov541 : Cover gdata (-3200) (-3136) (16384) (18432) := by
  ballooning_box "Q:cn10_45,cn10_48,cn10_46,cn10_49"

/-- Kernel-checked box `[-3200, -3136]/NT × [18432, 20480]/NS`. -/
theorem cov542 : Cover gdata (-3200) (-3136) (18432) (20480) := by
  ballooning_box "Q:cn10_46,cn10_49,cn10_47,cn10_50"

/-- Kernel-checked box `[-3136, -3072]/NT × [16384, 18432]/NS`. -/
theorem cov543 : Cover gdata (-3136) (-3072) (16384) (18432) := by
  ballooning_box "Q:cn10_48,cn10_51,cn10_49,cn10_52"

/-- Kernel-checked box `[-3136, -3072]/NT × [18432, 20480]/NS`. -/
theorem cov544 : Cover gdata (-3136) (-3072) (18432) (20480) := by
  ballooning_box "Q:cn10_49,cn10_52,cn10_50,cn10_53"

/-- Kernel-checked box `[-3072, -3008]/NT × [16384, 18432]/NS`. -/
theorem cov545 : Cover gdata (-3072) (-3008) (16384) (18432) := by
  ballooning_box "Q:cn10_51,cn10_54,cn10_52,cn10_55"

/-- Kernel-checked box `[-3072, -3008]/NT × [18432, 20480]/NS`. -/
theorem cov546 : Cover gdata (-3072) (-3008) (18432) (20480) := by
  ballooning_box "Q:cn10_52,cn10_55,cn10_53,cn10_56"

/-- Kernel-checked box `[-3008, -2944]/NT × [16384, 18432]/NS`. -/
theorem cov547 : Cover gdata (-3008) (-2944) (16384) (18432) := by
  ballooning_box "Q:cn10_54,cn10_57,cn10_55,cn10_58"

/-- Kernel-checked box `[-3008, -2944]/NT × [18432, 20480]/NS`. -/
theorem cov548 : Cover gdata (-3008) (-2944) (18432) (20480) := by
  ballooning_box "Q:cn10_55,cn10_58,cn10_56,cn10_59"

/-- Kernel-checked box `[-2944, -2880]/NT × [16384, 18432]/NS`. -/
theorem cov549 : Cover gdata (-2944) (-2880) (16384) (18432) := by
  ballooning_box "Q:cn10_57,cn10_60,cn10_58,cn10_61"

/-- Kernel-checked box `[-2944, -2880]/NT × [18432, 20480]/NS`. -/
theorem cov550 : Cover gdata (-2944) (-2880) (18432) (20480) := by
  ballooning_box "Q:cn10_58,cn10_61,cn10_59,cn10_62"

/-- Kernel-checked box `[-2880, -2816]/NT × [16384, 18432]/NS`. -/
theorem cov551 : Cover gdata (-2880) (-2816) (16384) (18432) := by
  ballooning_box "Q:cn10_60,cn10_63,cn10_61,cn10_64"

/-- Kernel-checked box `[-2880, -2816]/NT × [18432, 20480]/NS`. -/
theorem cov552 : Cover gdata (-2880) (-2816) (18432) (20480) := by
  ballooning_box "Q:cn10_61,cn10_64,cn10_62,cn10_65"

/-- Kernel-checked box `[-2816, -2688]/NT × [16384, 17408]/NS`. -/
theorem cov553 : Cover gdata (-2816) (-2688) (16384) (17408) := by
  ballooning_box "Q:cn10_63,cn10_66,cn10_67,cn10_68"

/-- Kernel-checked box `[-2816, -2688]/NT × [17408, 18432]/NS`. -/
theorem cov554 : Cover gdata (-2816) (-2688) (17408) (18432) := by
  ballooning_box "Q:cn10_67,cn10_68,cn10_64,cn10_69"

/-- Kernel-checked box `[-2816, -2752]/NT × [18432, 20480]/NS`. -/
theorem cov555 : Cover gdata (-2816) (-2752) (18432) (20480) := by
  ballooning_box "Q:cn10_64,cn10_70,cn10_65,cn10_71"

/-- Kernel-checked box `[-2752, -2688]/NT × [18432, 20480]/NS`. -/
theorem cov556 : Cover gdata (-2752) (-2688) (18432) (20480) := by
  ballooning_box "Q:cn10_70,cn10_69,cn10_71,cn10_72"

/-- Kernel-checked box `[-2688, -2560]/NT × [16384, 17408]/NS`. -/
theorem cov557 : Cover gdata (-2688) (-2560) (16384) (17408) := by
  ballooning_box "Q:cn10_66,cn10_73,cn10_68,cn10_74"

/-- Kernel-checked box `[-2688, -2560]/NT × [17408, 18432]/NS`. -/
theorem cov558 : Cover gdata (-2688) (-2560) (17408) (18432) := by
  ballooning_box "Q:cn10_68,cn10_74,cn10_69,cn10_75"

/-- Kernel-checked box `[-2688, -2560]/NT × [18432, 19456]/NS`. -/
theorem cov559 : Cover gdata (-2688) (-2560) (18432) (19456) := by
  ballooning_box "Q:cn10_69,cn10_75,cn10_76,cn10_77"

/-- Kernel-checked box `[-2688, -2560]/NT × [19456, 20480]/NS`. -/
theorem cov560 : Cover gdata (-2688) (-2560) (19456) (20480) := by
  ballooning_box "Q:cn10_76,cn10_77,cn10_72,cn10_78"

/-- Kernel-checked box `[-2560, -2432]/NT × [16384, 17408]/NS`. -/
theorem cov561 : Cover gdata (-2560) (-2432) (16384) (17408) := by
  ballooning_box "Q:cn10_73,cn10_79,cn10_74,cn10_80"

/-- Kernel-checked box `[-2560, -2432]/NT × [17408, 18432]/NS`. -/
theorem cov562 : Cover gdata (-2560) (-2432) (17408) (18432) := by
  ballooning_box "Q:cn10_74,cn10_80,cn10_75,cn10_81"

/-- Kernel-checked box `[-2560, -2432]/NT × [18432, 19456]/NS`. -/
theorem cov563 : Cover gdata (-2560) (-2432) (18432) (19456) := by
  ballooning_box "Q:cn10_75,cn10_81,cn10_77,cn10_82"

/-- Kernel-checked box `[-2560, -2432]/NT × [19456, 20480]/NS`. -/
theorem cov564 : Cover gdata (-2560) (-2432) (19456) (20480) := by
  ballooning_box "Q:cn10_77,cn10_82,cn10_78,cn10_83"

/-- Kernel-checked box `[-2432, -2304]/NT × [16384, 17408]/NS`. -/
theorem cov565 : Cover gdata (-2432) (-2304) (16384) (17408) := by
  ballooning_box "Q:cn10_79,cn10_84,cn10_80,cn10_85"

/-- Kernel-checked box `[-2432, -2304]/NT × [17408, 18432]/NS`. -/
theorem cov566 : Cover gdata (-2432) (-2304) (17408) (18432) := by
  ballooning_box "Q:cn10_80,cn10_85,cn10_81,cn10_86"

/-- Kernel-checked box `[-2432, -2304]/NT × [18432, 19456]/NS`. -/
theorem cov567 : Cover gdata (-2432) (-2304) (18432) (19456) := by
  ballooning_box "Q:cn10_81,cn10_86,cn10_82,cn10_87"

end PlasmaLean.Design.SolovevBallooning
