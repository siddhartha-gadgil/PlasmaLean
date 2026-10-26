/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningEvalCert

/-!
# Ballooning certificate: kernel-checked cells, part 11

51 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(-2432/NT, 19456/NS)`. -/
theorem cn11_0 : cornerOK gdata (-2432) (19456)
    [1382026976, 578383056, 663673870, 182723186, 108755254, 20123114, 3828406] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 19456/NS)`. -/
theorem cn11_1 : cornerOK gdata (-2304) (19456)
    [1382026976, 578383056, 663673870, 182723186, 108755254, 20123114, 3828406] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 20480/NS)`. -/
theorem cn11_2 : cornerOK gdata (-2432) (20480)
    [1382026976, 578383056, 663673870, 182723186, 108755254, 20123114, 3828406] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 20480/NS)`. -/
theorem cn11_3 : cornerOK gdata (-2304) (20480)
    [1382026976, 578383056, 663673870, 182723186, 108755254, 20123114, 3828406] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 16384/NS)`. -/
theorem cn11_4 : cornerOK gdata (-2304) (16384)
    [703587201, 334558152, 361807405, 112925223, 64085843, 12353238, 2695262] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 16384/NS)`. -/
theorem cn11_5 : cornerOK gdata (-2176) (16384)
    [1399138655, 555863421, 680372886, 172624868, 118856094, 19126197, 5030517] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 17408/NS)`. -/
theorem cn11_6 : cornerOK gdata (-2304) (17408)
    [863747083, 396174030, 436082132, 130986869, 75075322, 14288217, 2970691] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 17408/NS)`. -/
theorem cn11_7 : cornerOK gdata (-2176) (17408)
    [863747083, 396174030, 436082132, 130986869, 75075322, 14288217, 2970691] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 18432/NS)`. -/
theorem cn11_8 : cornerOK gdata (-2304) (18432)
    [1064503317, 470465099, 527769856, 152321115, 88408749, 16585894, 3278170] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 18432/NS)`. -/
theorem cn11_9 : cornerOK gdata (-2176) (18432)
    [1399138655, 555863421, 680372886, 172624868, 118856094, 19126197, 5030517] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 19456/NS)`. -/
theorem cn11_10 : cornerOK gdata (-2176) (19456)
    [1317254692, 566033106, 643249637, 177942846, 104689756, 19326249, 3622404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 20480/NS)`. -/
theorem cn11_11 : cornerOK gdata (-2176) (20480)
    [1317254692, 566033106, 643249637, 177942846, 104689756, 19326249, 3622404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 16384/NS)`. -/
theorem cn11_12 : cornerOK gdata (-2112) (16384)
    [1399138655, 555863421, 680372886, 172624868, 118856094, 19126197, 5030517] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 18432/NS)`. -/
theorem cn11_13 : cornerOK gdata (-2112) (18432)
    [1399138655, 555863421, 680372886, 172624868, 118856094, 19126197, 5030517] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 16384/NS)`. -/
theorem cn11_14 : cornerOK gdata (-2048) (16384)
    [1304015227, 528552321, 639040560, 163714349, 110905130, 18142634, 4661588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 18432/NS)`. -/
theorem cn11_15 : cornerOK gdata (-2048) (18432)
    [1304015227, 528552321, 639040560, 163714349, 110905130, 18142634, 4661588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 19456/NS)`. -/
theorem cn11_16 : cornerOK gdata (-2048) (19456)
    [1253818865, 543323844, 613668868, 171543054, 99400212, 18750557, 3399269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 20480/NS)`. -/
theorem cn11_17 : cornerOK gdata (-2048) (20480)
    [1253818865, 543323844, 613668868, 171543054, 99400212, 18750557, 3399269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 16384/NS)`. -/
theorem cn11_18 : cornerOK gdata (-1984) (16384)
    [1208807475, 499882793, 597374506, 154656720, 102993322, 17173759, 4303816] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 18432/NS)`. -/
theorem cn11_19 : cornerOK gdata (-1984) (18432)
    [1208807475, 499882793, 597374506, 154656720, 102993322, 17173759, 4303816] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 16384/NS)`. -/
theorem cn11_20 : cornerOK gdata (-1920) (16384)
    [1115008784, 470098291, 556062330, 145454705, 95224314, 16193604, 3962267] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 18432/NS)`. -/
theorem cn11_21 : cornerOK gdata (-1920) (18432)
    [1417648397, 571635054, 696985104, 169142681, 112699257, 18876975, 4108212] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 19456/NS)`. -/
theorem cn11_22 : cornerOK gdata (-1920) (19456)
    [1175580497, 516952920, 577179408, 165103118, 93042684, 18316284, 3161197] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 20480/NS)`. -/
theorem cn11_23 : cornerOK gdata (-1920) (20480)
    [1417648397, 571635054, 696985104, 169142681, 112699257, 18876975, 4108212] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 16384/NS)`. -/
theorem cn11_24 : cornerOK gdata (-1856) (16384)
    [1022495727, 439141055, 515031416, 136091468, 87578116, 15201057, 3632600] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 18432/NS)`. -/
theorem cn11_25 : cornerOK gdata (-1856) (18432)
    [1417648397, 571635054, 696985104, 169142681, 112699257, 18876975, 4108212] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 20480/NS)`. -/
theorem cn11_26 : cornerOK gdata (-1856) (20480)
    [1417648397, 571635054, 696985104, 169142681, 112699257, 18876975, 4108212] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 16384/NS)`. -/
theorem cn11_27 : cornerOK gdata (-1792) (16384)
    [932602913, 407474568, 475068326, 126748869, 80157103, 14212259, 3319108] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 18432/NS)`. -/
theorem cn11_28 : cornerOK gdata (-1792) (18432)
    [1280680805, 525778222, 637229462, 156458011, 102380119, 17518189, 3736966] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 20480/NS)`. -/
theorem cn11_29 : cornerOK gdata (-1792) (20480)
    [1280680805, 525778222, 637229462, 156458011, 102380119, 17518189, 3736966] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 16384/NS)`. -/
theorem cn11_30 : cornerOK gdata (-1728) (16384)
    [846167969, 375667694, 436241486, 117581179, 73027201, 13238711, 3022739] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 18432/NS)`. -/
theorem cn11_31 : cornerOK gdata (-1728) (18432)
    [1151217613, 480539095, 580497310, 144109231, 92585650, 16192838, 3387293] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 20480/NS)`. -/
theorem cn11_32 : cornerOK gdata (-1728) (20480)
    [1151217613, 480539095, 580497310, 144109231, 92585650, 16192838, 3387293] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 16384/NS)`. -/
theorem cn11_33 : cornerOK gdata (-1664) (16384)
    [1557954673, 708742796, 841180387, 255385645, 136776841, 28297668, 5331055] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 18432/NS)`. -/
theorem cn11_34 : cornerOK gdata (-1664) (18432)
    [1557954673, 708742796, 841180387, 255385645, 136776841, 28297668, 5331055] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 20480/NS)`. -/
theorem cn11_35 : cornerOK gdata (-1664) (20480)
    [1028948366, 436024594, 526253755, 132350493, 83278801, 14917491, 3060092] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 16384/NS)`. -/
theorem cn11_36 : cornerOK gdata (-1536) (16384)
    [1557954673, 708742796, 841180387, 255385645, 136776841, 28297668, 5331055] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 18432/NS)`. -/
theorem cn11_37 : cornerOK gdata (-1536) (18432)
    [1557954673, 708742796, 841180387, 255385645, 136776841, 28297668, 5331055] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 18432/NS)`. -/
theorem cn11_38 : cornerOK gdata (-1600) (18432)
    [914490478, 393130314, 474756828, 121491023, 74523082, 13722000, 2756675] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 20480/NS)`. -/
theorem cn11_39 : cornerOK gdata (-1600) (20480)
    [914490478, 393130314, 474756828, 121491023, 74523082, 13722000, 2756675] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 20480/NS)`. -/
theorem cn11_40 : cornerOK gdata (-1536) (20480)
    [809470679, 351780661, 426585478, 111089935, 66395152, 12572360, 2478374] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 16384/NS)`. -/
theorem cn11_41 : cornerOK gdata (-1408) (16384)
    [1306625186, 599855907, 717115551, 224291393, 115520153, 24762153, 4491220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 18432/NS)`. -/
theorem cn11_42 : cornerOK gdata (-1408) (18432)
    [1448539259, 646172510, 789703044, 239966388, 123047039, 26329210, 4491220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 18432/NS)`. -/
theorem cn11_43 : cornerOK gdata (-1472) (18432)
    [712829818, 312087318, 381354706, 101165634, 58827123, 11475894, 2221466] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 20480/NS)`. -/
theorem cn11_44 : cornerOK gdata (-1472) (20480)
    [712829818, 312087318, 381354706, 101165634, 58827123, 11475894, 2221466] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 20480/NS)`. -/
theorem cn11_45 : cornerOK gdata (-1408) (20480)
    [1448539259, 646172510, 789703044, 239966388, 123047039, 26329210, 4401226] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 16384/NS)`. -/
theorem cn11_46 : cornerOK gdata (-1280) (16384)
    [2278190248, 965146615, 1244707130, 350412523, 196979191, 38188244, 7440889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 18432/NS)`. -/
theorem cn11_47 : cornerOK gdata (-1280) (18432)
    [1448539259, 646172510, 789703044, 239966388, 123047039, 26329210, 4401226] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 20480/NS)`. -/
theorem cn11_48 : cornerOK gdata (-1280) (20480)
    [2278190248, 965146615, 1244707130, 350412523, 196979191, 38188244, 7440889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 16384/NS)`. -/
theorem cn11_49 : cornerOK gdata (-1216) (16384)
    [2278190248, 965146615, 1244707130, 350412523, 196979191, 38188244, 7440889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 20480/NS)`. -/
theorem cn11_50 : cornerOK gdata (-1216) (20480)
    [2278190248, 965146615, 1244707130, 350412523, 196979191, 38188244, 7440889] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 16384/NS)`. -/
theorem cn11_51 : cornerOK gdata (-1152) (16384)
    [1971257855, 822613019, 1062668861, 304765551, 170465851, 33267837, 6398302] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 20480/NS)`. -/
theorem cn11_52 : cornerOK gdata (-1152) (20480)
    [1971257855, 822613019, 1062668861, 304765551, 170465851, 33267837, 6398302] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 16384/NS)`. -/
theorem cn11_53 : cornerOK gdata (-1088) (16384)
    [1697341212, 699904618, 912678268, 263998009, 146930455, 28871685, 5478095] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 20480/NS)`. -/
theorem cn11_54 : cornerOK gdata (-1088) (20480)
    [1697341212, 699904618, 912678268, 263998009, 146930455, 28871685, 5478095] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 16384/NS)`. -/
theorem cn11_55 : cornerOK gdata (-1024) (16384)
    [2399192353, 1060532725, 1320428833, 404104520, 210292871, 42755465, 7764445] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 20480/NS)`. -/
theorem cn11_56 : cornerOK gdata (-1024) (20480)
    [2399192353, 1060532725, 1320428833, 404104520, 210292871, 42755465, 7764445] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 16384/NS)`. -/
theorem cn11_57 : cornerOK gdata (-896) (16384)
    [2399192353, 1060532725, 1320428833, 404104520, 210292871, 42755465, 7764445] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 20480/NS)`. -/
theorem cn11_58 : cornerOK gdata (-896) (20480)
    [2399192353, 1060532725, 1320428833, 404104520, 210292871, 42755465, 7764445] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 16384/NS)`. -/
theorem cn11_59 : cornerOK gdata (-768) (16384)
    [1790371089, 835353863, 993247450, 303982177, 160121604, 32101734, 5947982] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 20480/NS)`. -/
theorem cn11_60 : cornerOK gdata (-768) (20480)
    [1790371089, 835353863, 993247450, 303982177, 160121604, 32101734, 5947982] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 16384/NS)`. -/
theorem cn11_61 : cornerOK gdata (-640) (16384)
    [1320529208, 652799329, 743091581, 227427702, 121695306, 23862664, 4557654] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 20480/NS)`. -/
theorem cn11_62 : cornerOK gdata (-640) (20480)
    [1320529208, 652799329, 743091581, 227427702, 121695306, 23862664, 4557654] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 16384/NS)`. -/
theorem cn11_63 : cornerOK gdata (-512) (16384)
    [969057181, 517451111, 560413128, 176405542, 92397014, 18188407, 3636719] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 20480/NS)`. -/
theorem cn11_64 : cornerOK gdata (-512) (20480)
    [969057181, 517451111, 560413128, 176405542, 92397014, 18188407, 3636719] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 16384/NS)`. -/
theorem cn11_65 : cornerOK gdata (-384) (16384)
    [710507253, 404723298, 425816748, 136270276, 70523217, 13568395, 2956577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 20480/NS)`. -/
theorem cn11_66 : cornerOK gdata (-384) (20480)
    [710507253, 404723298, 425816748, 136270276, 70523217, 13568395, 2956577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 16384/NS)`. -/
theorem cn11_67 : cornerOK gdata (-256) (16384)
    [520986199, 317307697, 328049264, 108317294, 54929222, 10204759, 2488907] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 20480/NS)`. -/
theorem cn11_68 : cornerOK gdata (-256) (20480)
    [520986199, 317307697, 328049264, 108317294, 54929222, 10204759, 2488907] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-128/NT, 16384/NS)`. -/
theorem cn11_69 : cornerOK gdata (-128) (16384)
    [396347794, 247052698, 257446686, 89017352, 44100923, 8209955, 2163489] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-128/NT, 20480/NS)`. -/
theorem cn11_70 : cornerOK gdata (-128) (20480)
    [396347794, 247052698, 257446686, 89017352, 44100923, 8209955, 2163489] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 16384/NS)`. -/
theorem cn11_71 : cornerOK gdata (0) (16384)
    [304861336, 190176935, 207212134, 75487650, 36960145, 7488973, 1947919] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 20480/NS)`. -/
theorem cn11_72 : cornerOK gdata (0) (20480)
    [304861336, 190176935, 207212134, 75487650, 36960145, 7488973, 1947919] = true := by
  bl_cert

/-- Kernel-checked corner test at `(128/NT, 16384/NS)`. -/
theorem cn11_73 : cornerOK gdata (128) (16384)
    [306674721, 220549754, 223355223, 91160276, 43333706, 9139761, 2263747] = true := by
  bl_cert

/-- Kernel-checked corner test at `(128/NT, 20480/NS)`. -/
theorem cn11_74 : cornerOK gdata (128) (20480)
    [306674721, 220549754, 223355223, 91160276, 43333706, 9139761, 2263747] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 16384/NS)`. -/
theorem cn11_75 : cornerOK gdata (256) (16384)
    [337703711, 261848455, 255235432, 108396351, 51843783, 10932156, 2806246] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 20480/NS)`. -/
theorem cn11_76 : cornerOK gdata (256) (20480)
    [337703711, 261848455, 255235432, 108396351, 51843783, 10932156, 2806246] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 16384/NS)`. -/
theorem cn11_77 : cornerOK gdata (384) (16384)
    [379405374, 305627627, 291834351, 126182935, 62009222, 12789824, 3620772] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 20480/NS)`. -/
theorem cn11_78 : cornerOK gdata (384) (20480)
    [379405374, 305627627, 291834351, 126182935, 62009222, 12789824, 3620772] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 16384/NS)`. -/
theorem cn11_79 : cornerOK gdata (512) (16384)
    [428088015, 349682913, 331871490, 143947144, 73492543, 14637858, 4635914] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 20480/NS)`. -/
theorem cn11_80 : cornerOK gdata (512) (20480)
    [428088015, 349682913, 331871490, 143947144, 73492543, 14637858, 4635914] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 16384/NS)`. -/
theorem cn11_81 : cornerOK gdata (640) (16384)
    [475328673, 393133442, 375409299, 161671406, 86327002, 16518375, 5791610] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 20480/NS)`. -/
theorem cn11_82 : cornerOK gdata (640) (20480)
    [475328673, 393133442, 375409299, 161671406, 86327002, 16518375, 5791610] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 16384/NS)`. -/
theorem cn11_83 : cornerOK gdata (768) (16384)
    [518841882, 434487291, 425214780, 178878074, 100253817, 18531316, 7088780] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 20480/NS)`. -/
theorem cn11_84 : cornerOK gdata (768) (20480)
    [518841882, 434487291, 425214780, 178878074, 100253817, 18531316, 7088780] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 16384/NS)`. -/
theorem cn11_85 : cornerOK gdata (896) (16384)
    [556505536, 472145076, 475190949, 197863487, 114666140, 20837775, 8460198] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 20480/NS)`. -/
theorem cn11_86 : cornerOK gdata (896) (20480)
    [556505536, 472145076, 475190949, 197863487, 114666140, 20837775, 8460198] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 16384/NS)`. -/
theorem cn11_87 : cornerOK gdata (1024) (16384)
    [587804892, 505139014, 523521084, 218410629, 129236957, 23145825, 9878993] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 20480/NS)`. -/
theorem cn11_88 : cornerOK gdata (1024) (20480)
    [587804892, 505139014, 523521084, 218410629, 129236957, 23145825, 9878993] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 16384/NS)`. -/
theorem cn11_89 : cornerOK gdata (1152) (16384)
    [612248773, 532376857, 569422570, 237422852, 143929795, 25327865, 11349655] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 20480/NS)`. -/
theorem cn11_90 : cornerOK gdata (1152) (20480)
    [612248773, 532376857, 569422570, 237422852, 143929795, 25327865, 11349655] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 16384/NS)`. -/
theorem cn11_91 : cornerOK gdata (1280) (16384)
    [612248773, 532376857, 569422570, 237422852, 143929795, 25327865, 11349655] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 20480/NS)`. -/
theorem cn11_92 : cornerOK gdata (1280) (20480)
    [612248773, 532376857, 569422570, 237422852, 143929795, 25327865, 11349655] = true := by
  bl_cert

/-- Kernel-checked box `[-2432, -2304]/NT × [19456, 20480]/NS`. -/
theorem cov568 : Cover gdata (-2432) (-2304) (19456) (20480) := by
  ballooning_cover "Q:cn11_0,cn11_1,cn11_2,cn11_3"

/-- Kernel-checked box `[-2304, -2176]/NT × [16384, 17408]/NS`. -/
theorem cov569 : Cover gdata (-2304) (-2176) (16384) (17408) := by
  ballooning_cover "Q:cn11_4,cn11_5,cn11_6,cn11_7"

/-- Kernel-checked box `[-2304, -2176]/NT × [17408, 18432]/NS`. -/
theorem cov570 : Cover gdata (-2304) (-2176) (17408) (18432) := by
  ballooning_cover "Q:cn11_6,cn11_7,cn11_8,cn11_9"

/-- Kernel-checked box `[-2304, -2176]/NT × [18432, 19456]/NS`. -/
theorem cov571 : Cover gdata (-2304) (-2176) (18432) (19456) := by
  ballooning_cover "Q:cn11_8,cn11_9,cn11_1,cn11_10"

/-- Kernel-checked box `[-2304, -2176]/NT × [19456, 20480]/NS`. -/
theorem cov572 : Cover gdata (-2304) (-2176) (19456) (20480) := by
  ballooning_cover "Q:cn11_1,cn11_10,cn11_3,cn11_11"

/-- Kernel-checked box `[-2176, -2112]/NT × [16384, 18432]/NS`. -/
theorem cov573 : Cover gdata (-2176) (-2112) (16384) (18432) := by
  ballooning_cover "Q:cn11_5,cn11_12,cn11_9,cn11_13"

/-- Kernel-checked box `[-2112, -2048]/NT × [16384, 18432]/NS`. -/
theorem cov574 : Cover gdata (-2112) (-2048) (16384) (18432) := by
  ballooning_cover "Q:cn11_12,cn11_14,cn11_13,cn11_15"

/-- Kernel-checked box `[-2176, -2048]/NT × [18432, 19456]/NS`. -/
theorem cov575 : Cover gdata (-2176) (-2048) (18432) (19456) := by
  ballooning_cover "Q:cn11_9,cn11_15,cn11_10,cn11_16"

/-- Kernel-checked box `[-2176, -2048]/NT × [19456, 20480]/NS`. -/
theorem cov576 : Cover gdata (-2176) (-2048) (19456) (20480) := by
  ballooning_cover "Q:cn11_10,cn11_16,cn11_11,cn11_17"

/-- Kernel-checked box `[-2048, -1984]/NT × [16384, 18432]/NS`. -/
theorem cov577 : Cover gdata (-2048) (-1984) (16384) (18432) := by
  ballooning_cover "Q:cn11_14,cn11_18,cn11_15,cn11_19"

/-- Kernel-checked box `[-1984, -1920]/NT × [16384, 18432]/NS`. -/
theorem cov578 : Cover gdata (-1984) (-1920) (16384) (18432) := by
  ballooning_cover "Q:cn11_18,cn11_20,cn11_19,cn11_21"

/-- Kernel-checked box `[-2048, -1920]/NT × [18432, 19456]/NS`. -/
theorem cov579 : Cover gdata (-2048) (-1920) (18432) (19456) := by
  ballooning_cover "Q:cn11_15,cn11_21,cn11_16,cn11_22"

/-- Kernel-checked box `[-2048, -1920]/NT × [19456, 20480]/NS`. -/
theorem cov580 : Cover gdata (-2048) (-1920) (19456) (20480) := by
  ballooning_cover "Q:cn11_16,cn11_22,cn11_17,cn11_23"

/-- Kernel-checked box `[-1920, -1856]/NT × [16384, 18432]/NS`. -/
theorem cov581 : Cover gdata (-1920) (-1856) (16384) (18432) := by
  ballooning_cover "Q:cn11_20,cn11_24,cn11_21,cn11_25"

/-- Kernel-checked box `[-1920, -1856]/NT × [18432, 20480]/NS`. -/
theorem cov582 : Cover gdata (-1920) (-1856) (18432) (20480) := by
  ballooning_cover "Q:cn11_21,cn11_25,cn11_23,cn11_26"

/-- Kernel-checked box `[-1856, -1792]/NT × [16384, 18432]/NS`. -/
theorem cov583 : Cover gdata (-1856) (-1792) (16384) (18432) := by
  ballooning_cover "Q:cn11_24,cn11_27,cn11_25,cn11_28"

/-- Kernel-checked box `[-1856, -1792]/NT × [18432, 20480]/NS`. -/
theorem cov584 : Cover gdata (-1856) (-1792) (18432) (20480) := by
  ballooning_cover "Q:cn11_25,cn11_28,cn11_26,cn11_29"

/-- Kernel-checked box `[-1792, -1728]/NT × [16384, 18432]/NS`. -/
theorem cov585 : Cover gdata (-1792) (-1728) (16384) (18432) := by
  ballooning_cover "Q:cn11_27,cn11_30,cn11_28,cn11_31"

/-- Kernel-checked box `[-1792, -1728]/NT × [18432, 20480]/NS`. -/
theorem cov586 : Cover gdata (-1792) (-1728) (18432) (20480) := by
  ballooning_cover "Q:cn11_28,cn11_31,cn11_29,cn11_32"

/-- Kernel-checked box `[-1728, -1664]/NT × [16384, 18432]/NS`. -/
theorem cov587 : Cover gdata (-1728) (-1664) (16384) (18432) := by
  ballooning_cover "Q:cn11_30,cn11_33,cn11_31,cn11_34"

/-- Kernel-checked box `[-1728, -1664]/NT × [18432, 20480]/NS`. -/
theorem cov588 : Cover gdata (-1728) (-1664) (18432) (20480) := by
  ballooning_cover "Q:cn11_31,cn11_34,cn11_32,cn11_35"

/-- Kernel-checked box `[-1664, -1536]/NT × [16384, 18432]/NS`. -/
theorem cov589 : Cover gdata (-1664) (-1536) (16384) (18432) := by
  ballooning_cover "Q:cn11_33,cn11_36,cn11_34,cn11_37"

/-- Kernel-checked box `[-1664, -1600]/NT × [18432, 20480]/NS`. -/
theorem cov590 : Cover gdata (-1664) (-1600) (18432) (20480) := by
  ballooning_cover "Q:cn11_34,cn11_38,cn11_35,cn11_39"

/-- Kernel-checked box `[-1600, -1536]/NT × [18432, 20480]/NS`. -/
theorem cov591 : Cover gdata (-1600) (-1536) (18432) (20480) := by
  ballooning_cover "Q:cn11_38,cn11_37,cn11_39,cn11_40"

/-- Kernel-checked box `[-1536, -1408]/NT × [16384, 18432]/NS`. -/
theorem cov592 : Cover gdata (-1536) (-1408) (16384) (18432) := by
  ballooning_cover "Q:cn11_36,cn11_41,cn11_37,cn11_42"

/-- Kernel-checked box `[-1536, -1472]/NT × [18432, 20480]/NS`. -/
theorem cov593 : Cover gdata (-1536) (-1472) (18432) (20480) := by
  ballooning_cover "Q:cn11_37,cn11_43,cn11_40,cn11_44"

/-- Kernel-checked box `[-1472, -1408]/NT × [18432, 20480]/NS`. -/
theorem cov594 : Cover gdata (-1472) (-1408) (18432) (20480) := by
  ballooning_cover "Q:cn11_43,cn11_42,cn11_44,cn11_45"

/-- Kernel-checked box `[-1408, -1280]/NT × [16384, 18432]/NS`. -/
theorem cov595 : Cover gdata (-1408) (-1280) (16384) (18432) := by
  ballooning_cover "Q:cn11_41,cn11_46,cn11_42,cn11_47"

/-- Kernel-checked box `[-1408, -1280]/NT × [18432, 20480]/NS`. -/
theorem cov596 : Cover gdata (-1408) (-1280) (18432) (20480) := by
  ballooning_cover "Q:cn11_42,cn11_47,cn11_45,cn11_48"

/-- Kernel-checked box `[-1280, -1216]/NT × [16384, 20480]/NS`. -/
theorem cov597 : Cover gdata (-1280) (-1216) (16384) (20480) := by
  ballooning_cover "Q:cn11_46,cn11_49,cn11_48,cn11_50"

/-- Kernel-checked box `[-1216, -1152]/NT × [16384, 20480]/NS`. -/
theorem cov598 : Cover gdata (-1216) (-1152) (16384) (20480) := by
  ballooning_cover "Q:cn11_49,cn11_51,cn11_50,cn11_52"

/-- Kernel-checked box `[-1152, -1088]/NT × [16384, 20480]/NS`. -/
theorem cov599 : Cover gdata (-1152) (-1088) (16384) (20480) := by
  ballooning_cover "Q:cn11_51,cn11_53,cn11_52,cn11_54"

/-- Kernel-checked box `[-1088, -1024]/NT × [16384, 20480]/NS`. -/
theorem cov600 : Cover gdata (-1088) (-1024) (16384) (20480) := by
  ballooning_cover "Q:cn11_53,cn11_55,cn11_54,cn11_56"

/-- Kernel-checked box `[-1024, -896]/NT × [16384, 20480]/NS`. -/
theorem cov601 : Cover gdata (-1024) (-896) (16384) (20480) := by
  ballooning_cover "Q:cn11_55,cn11_57,cn11_56,cn11_58"

/-- Kernel-checked box `[-896, -768]/NT × [16384, 20480]/NS`. -/
theorem cov602 : Cover gdata (-896) (-768) (16384) (20480) := by
  ballooning_cover "Q:cn11_57,cn11_59,cn11_58,cn11_60"

/-- Kernel-checked box `[-768, -640]/NT × [16384, 20480]/NS`. -/
theorem cov603 : Cover gdata (-768) (-640) (16384) (20480) := by
  ballooning_cover "Q:cn11_59,cn11_61,cn11_60,cn11_62"

/-- Kernel-checked box `[-640, -512]/NT × [16384, 20480]/NS`. -/
theorem cov604 : Cover gdata (-640) (-512) (16384) (20480) := by
  ballooning_cover "Q:cn11_61,cn11_63,cn11_62,cn11_64"

/-- Kernel-checked box `[-512, -384]/NT × [16384, 20480]/NS`. -/
theorem cov605 : Cover gdata (-512) (-384) (16384) (20480) := by
  ballooning_cover "Q:cn11_63,cn11_65,cn11_64,cn11_66"

/-- Kernel-checked box `[-384, -256]/NT × [16384, 20480]/NS`. -/
theorem cov606 : Cover gdata (-384) (-256) (16384) (20480) := by
  ballooning_cover "Q:cn11_65,cn11_67,cn11_66,cn11_68"

/-- Kernel-checked box `[-256, -128]/NT × [16384, 20480]/NS`. -/
theorem cov607 : Cover gdata (-256) (-128) (16384) (20480) := by
  ballooning_cover "Q:cn11_67,cn11_69,cn11_68,cn11_70"

/-- Kernel-checked box `[-128, 0]/NT × [16384, 20480]/NS`. -/
theorem cov608 : Cover gdata (-128) (0) (16384) (20480) := by
  ballooning_cover "Q:cn11_69,cn11_71,cn11_70,cn11_72"

/-- Kernel-checked box `[0, 128]/NT × [16384, 20480]/NS`. -/
theorem cov609 : Cover gdata (0) (128) (16384) (20480) := by
  ballooning_cover "Q:cn11_71,cn11_73,cn11_72,cn11_74"

/-- Kernel-checked box `[128, 256]/NT × [16384, 20480]/NS`. -/
theorem cov610 : Cover gdata (128) (256) (16384) (20480) := by
  ballooning_cover "Q:cn11_73,cn11_75,cn11_74,cn11_76"

/-- Kernel-checked box `[256, 384]/NT × [16384, 20480]/NS`. -/
theorem cov611 : Cover gdata (256) (384) (16384) (20480) := by
  ballooning_cover "Q:cn11_75,cn11_77,cn11_76,cn11_78"

/-- Kernel-checked box `[384, 512]/NT × [16384, 20480]/NS`. -/
theorem cov612 : Cover gdata (384) (512) (16384) (20480) := by
  ballooning_cover "Q:cn11_77,cn11_79,cn11_78,cn11_80"

/-- Kernel-checked box `[512, 640]/NT × [16384, 20480]/NS`. -/
theorem cov613 : Cover gdata (512) (640) (16384) (20480) := by
  ballooning_cover "Q:cn11_79,cn11_81,cn11_80,cn11_82"

/-- Kernel-checked box `[640, 768]/NT × [16384, 20480]/NS`. -/
theorem cov614 : Cover gdata (640) (768) (16384) (20480) := by
  ballooning_cover "Q:cn11_81,cn11_83,cn11_82,cn11_84"

/-- Kernel-checked box `[768, 896]/NT × [16384, 20480]/NS`. -/
theorem cov615 : Cover gdata (768) (896) (16384) (20480) := by
  ballooning_cover "Q:cn11_83,cn11_85,cn11_84,cn11_86"

/-- Kernel-checked box `[896, 1024]/NT × [16384, 20480]/NS`. -/
theorem cov616 : Cover gdata (896) (1024) (16384) (20480) := by
  ballooning_cover "Q:cn11_85,cn11_87,cn11_86,cn11_88"

/-- Kernel-checked box `[1024, 1152]/NT × [16384, 20480]/NS`. -/
theorem cov617 : Cover gdata (1024) (1152) (16384) (20480) := by
  ballooning_cover "Q:cn11_87,cn11_89,cn11_88,cn11_90"

/-- Kernel-checked box `[1152, 1280]/NT × [16384, 20480]/NS`. -/
theorem cov618 : Cover gdata (1152) (1280) (16384) (20480) := by
  ballooning_cover "Q:cn11_89,cn11_91,cn11_90,cn11_92"

end PlasmaLean.Design.SolovevBallooning
