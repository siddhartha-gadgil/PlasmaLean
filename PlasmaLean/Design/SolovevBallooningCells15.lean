/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningData

/-!
# Ballooning certificate: kernel-checked cells, part 15

51 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(-128/NT, 20480/NS)`. -/
theorem cn15_0 : cornerOK gdata (-128) (20480)
    [578725855, 371457680, 391766773, 151851333, 69948311, 13899495, 3542146] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(0/NT, 20480/NS)`. -/
theorem cn15_1 : cornerOK gdata (0) (20480)
    [578725855, 371457680, 391766773, 151851333, 69948311, 14196460, 3558904] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-128/NT, 25600/NS)`. -/
theorem cn15_2 : cornerOK gdata (-128) (25600)
    [578725855, 371457680, 391766773, 151851333, 69948311, 13899495, 3542146] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(0/NT, 25600/NS)`. -/
theorem cn15_3 : cornerOK gdata (0) (25600)
    [578725855, 371457680, 391766773, 151851333, 69948311, 14196460, 3558904] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(128/NT, 20480/NS)`. -/
theorem cn15_4 : cornerOK gdata (128) (20480)
    [562981215, 415865626, 408261973, 176062473, 80332908, 17026965, 4150539] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(128/NT, 25600/NS)`. -/
theorem cn15_5 : cornerOK gdata (128) (25600)
    [562981215, 415865626, 408261973, 176062473, 80332908, 17026965, 4150539] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(256/NT, 20480/NS)`. -/
theorem cn15_6 : cornerOK gdata (256) (20480)
    [614241284, 489684488, 466705168, 207020969, 96450738, 20282202, 5156258] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(256/NT, 25600/NS)`. -/
theorem cn15_7 : cornerOK gdata (256) (25600)
    [614241284, 489684488, 466705168, 207020969, 96450738, 20282202, 5156258] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(384/NT, 20480/NS)`. -/
theorem cn15_8 : cornerOK gdata (384) (20480)
    [669450032, 567045494, 533724462, 238810000, 115648540, 23703719, 6691810] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(384/NT, 25600/NS)`. -/
theorem cn15_9 : cornerOK gdata (384) (25600)
    [669450032, 567045494, 533724462, 238810000, 115648540, 23703719, 6691810] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(512/NT, 20480/NS)`. -/
theorem cn15_10 : cornerOK gdata (512) (20480)
    [749623803, 645680197, 607878460, 271072099, 137497470, 27195977, 8630192] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(512/NT, 25600/NS)`. -/
theorem cn15_11 : cornerOK gdata (512) (25600)
    [749623803, 645680197, 607878460, 271072099, 137497470, 27195977, 8630192] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(640/NT, 20480/NS)`. -/
theorem cn15_12 : cornerOK gdata (640) (20480)
    [827696106, 723967584, 690741811, 303890498, 162029928, 30821579, 10853139] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(640/NT, 25600/NS)`. -/
theorem cn15_13 : cornerOK gdata (640) (25600)
    [827696106, 723967584, 690741811, 303890498, 162029928, 30821579, 10853139] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(768/NT, 20480/NS)`. -/
theorem cn15_14 : cornerOK gdata (768) (20480)
    [827696106, 723967584, 690741811, 303890498, 162029928, 30821579, 10853139] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(768/NT, 25600/NS)`. -/
theorem cn15_15 : cornerOK gdata (768) (25600)
    [827696106, 723967584, 690741811, 303890498, 162029928, 30821579, 10853139] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(832/NT, 20480/NS)`. -/
theorem cn15_16 : cornerOK gdata (832) (20480)
    [414874365, 365211370, 375603821, 151973767, 96354149, 15298212, 6558646] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(832/NT, 25600/NS)`. -/
theorem cn15_17 : cornerOK gdata (832) (25600)
    [414874365, 365211370, 375603821, 151973767, 96354149, 15298212, 6558646] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(896/NT, 20480/NS)`. -/
theorem cn15_18 : cornerOK gdata (896) (20480)
    [436200339, 385416480, 402862467, 159993691, 104443286, 16314159, 7298729] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(896/NT, 25600/NS)`. -/
theorem cn15_19 : cornerOK gdata (896) (25600)
    [436200339, 385416480, 402862467, 159993691, 104443286, 16314159, 7298729] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(960/NT, 20480/NS)`. -/
theorem cn15_20 : cornerOK gdata (960) (20480)
    [456533867, 404937736, 430708525, 168070004, 112775847, 17354187, 8070444] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(960/NT, 25600/NS)`. -/
theorem cn15_21 : cornerOK gdata (960) (25600)
    [456533867, 404937736, 430708525, 168070004, 112775847, 17354187, 8070444] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1024/NT, 20480/NS)`. -/
theorem cn15_22 : cornerOK gdata (1024) (20480)
    [475917125, 423902955, 459100144, 179127589, 121333488, 18422727, 8872417] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1024/NT, 25600/NS)`. -/
theorem cn15_23 : cornerOK gdata (1024) (25600)
    [475917125, 423902955, 459100144, 179127589, 121333488, 18422727, 8872417] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1088/NT, 20480/NS)`. -/
theorem cn15_24 : cornerOK gdata (1088) (20480)
    [493260851, 441598793, 486918372, 191508868, 129858261, 19500822, 9681126] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1088/NT, 25600/NS)`. -/
theorem cn15_25 : cornerOK gdata (1088) (25600)
    [493260851, 441598793, 486918372, 191508868, 129858261, 19500822, 9681126] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1152/NT, 20480/NS)`. -/
theorem cn15_26 : cornerOK gdata (1152) (20480)
    [509574634, 458691384, 514920752, 203655343, 138540004, 20611359, 10515217] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1152/NT, 25600/NS)`. -/
theorem cn15_27 : cornerOK gdata (1152) (25600)
    [509574634, 458691384, 514920752, 203655343, 138540004, 20611359, 10515217] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1216/NT, 20480/NS)`. -/
theorem cn15_28 : cornerOK gdata (1216) (20480)
    [524372902, 474576318, 542627543, 216090157, 147225820, 21713960, 11361947] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1216/NT, 25600/NS)`. -/
theorem cn15_29 : cornerOK gdata (1216) (25600)
    [524372902, 474576318, 542627543, 216090157, 147225820, 21713960, 11361947] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1280/NT, 20480/NS)`. -/
theorem cn15_30 : cornerOK gdata (1280) (20480)
    [536152694, 488635127, 568148529, 228304850, 155418523, 22926202, 12168251] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1280/NT, 25600/NS)`. -/
theorem cn15_31 : cornerOK gdata (1280) (25600)
    [536152694, 488635127, 568148529, 228304850, 155418523, 22926202, 12168251] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1344/NT, 20480/NS)`. -/
theorem cn15_32 : cornerOK gdata (1344) (20480)
    [548638954, 503024698, 594931463, 240191916, 163961521, 24225093, 12999149] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1344/NT, 25600/NS)`. -/
theorem cn15_33 : cornerOK gdata (1344) (25600)
    [548638954, 503024698, 594931463, 240191916, 163961521, 24225093, 12999149] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 20480/NS)`. -/
theorem cn15_34 : cornerOK gdata (1408) (20480)
    [548638954, 503024698, 594931463, 240191916, 163961521, 24225093, 12999149] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 25600/NS)`. -/
theorem cn15_35 : cornerOK gdata (1408) (25600)
    [548638954, 503024698, 594931463, 240191916, 163961521, 24225093, 12999149] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 20480/NS)`. -/
theorem cn15_36 : cornerOK gdata (1536) (20480)
    [271706512, 259658564, 303645324, 129323884, 83595637, 14651017, 7250198] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 23040/NS)`. -/
theorem cn15_37 : cornerOK gdata (1408) (23040)
    [284741696, 283571822, 327748529, 138935548, 91027848, 15754000, 7874028] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 23040/NS)`. -/
theorem cn15_38 : cornerOK gdata (1536) (23040)
    [284741696, 283571822, 330482417, 142013589, 93146727, 16183292, 8142986] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 25600/NS)`. -/
theorem cn15_39 : cornerOK gdata (1536) (25600)
    [284741696, 283571822, 330482417, 142013589, 93146727, 16183292, 8142986] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 20480/NS)`. -/
theorem cn15_40 : cornerOK gdata (1664) (20480)
    [262159559, 257951956, 304595946, 130786365, 85263970, 14915094, 7737539] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 23040/NS)`. -/
theorem cn15_41 : cornerOK gdata (1664) (23040)
    [272076619, 279739182, 330482417, 142753186, 94343947, 16365326, 8600506] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 25600/NS)`. -/
theorem cn15_42 : cornerOK gdata (1664) (25600)
    [272076619, 279739182, 330482417, 142753186, 94343947, 16365326, 8600506] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 20480/NS)`. -/
theorem cn15_43 : cornerOK gdata (1792) (20480)
    [250822390, 252776499, 304595946, 130786365, 86641280, 14941166, 8193609] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 23040/NS)`. -/
theorem cn15_44 : cornerOK gdata (1792) (23040)
    [258784616, 272656987, 330062369, 142753186, 94491267, 16365326, 9027201] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 25600/NS)`. -/
theorem cn15_45 : cornerOK gdata (1792) (25600)
    [258784616, 272656987, 330062369, 142753186, 94491267, 16365326, 9027201] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 20480/NS)`. -/
theorem cn15_46 : cornerOK gdata (1920) (20480)
    [238681234, 244862724, 302907577, 130179543, 87233793, 14941166, 8603965] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 23040/NS)`. -/
theorem cn15_47 : cornerOK gdata (1920) (23040)
    [244259769, 262698168, 326241067, 141258320, 94491267, 16317575, 9408628] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 25600/NS)`. -/
theorem cn15_48 : cornerOK gdata (1920) (25600)
    [244259769, 262698168, 326241067, 141258320, 94491267, 16317575, 9408628] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 20480/NS)`. -/
theorem cn15_49 : cornerOK gdata (2048) (20480)
    [225944573, 234835230, 298946703, 127719469, 89515222, 14715647, 8992695] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 23040/NS)`. -/
theorem cn15_50 : cornerOK gdata (2048) (23040)
    [229415111, 250289395, 319774578, 137812956, 95750831, 16018231, 9741346] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 25600/NS)`. -/
theorem cn15_51 : cornerOK gdata (2048) (25600)
    [229415111, 250289395, 319774578, 137812956, 95750831, 16018231, 9741346] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 20480/NS)`. -/
theorem cn15_52 : cornerOK gdata (2176) (20480)
    [212769191, 222545061, 292658636, 123741394, 91633396, 14274154, 9410202] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 23040/NS)`. -/
theorem cn15_53 : cornerOK gdata (2176) (23040)
    [214738178, 235992505, 311470265, 132688383, 97691401, 15503709, 10173610] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 25600/NS)`. -/
theorem cn15_54 : cornerOK gdata (2176) (25600)
    [214738178, 235992505, 311470265, 132688383, 97691401, 15503709, 10173610] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 20480/NS)`. -/
theorem cn15_55 : cornerOK gdata (2304) (20480)
    [200210272, 208963482, 285103828, 118325938, 93199144, 13648795, 9778591] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 23040/NS)`. -/
theorem cn15_56 : cornerOK gdata (2304) (23040)
    [200491708, 220024466, 301157035, 126223380, 99097088, 14823389, 10552020] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 25600/NS)`. -/
theorem cn15_57 : cornerOK gdata (2304) (25600)
    [200491708, 220024466, 301157035, 126223380, 99097088, 14823389, 10552020] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 20480/NS)`. -/
theorem cn15_58 : cornerOK gdata (2432) (20480)
    [188146377, 194354493, 276609812, 111718019, 94491711, 12917251, 10108298] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 23040/NS)`. -/
theorem cn15_59 : cornerOK gdata (2432) (23040)
    [188146377, 203231237, 289816262, 118666584, 100025109, 14025831, 10857960] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 25600/NS)`. -/
theorem cn15_60 : cornerOK gdata (2432) (25600)
    [186746799, 203231237, 289816262, 118666584, 100025109, 14025831, 10857960] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 20480/NS)`. -/
theorem cn15_61 : cornerOK gdata (2560) (20480)
    [176625206, 179373315, 267642224, 104565040, 95260921, 12117236, 10364890] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 23040/NS)`. -/
theorem cn15_62 : cornerOK gdata (2560) (23040)
    [176625206, 186843406, 278589398, 110605516, 100658284, 13163944, 11097576] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 25600/NS)`. -/
theorem cn15_63 : cornerOK gdata (2560) (25600)
    [174066827, 186843406, 278589398, 110605516, 100658284, 13163944, 11097576] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 20480/NS)`. -/
theorem cn15_64 : cornerOK gdata (2688) (20480)
    [165697990, 164835518, 259830153, 96875532, 95894738, 11243544, 10575393] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 23040/NS)`. -/
theorem cn15_65 : cornerOK gdata (2688) (23040)
    [165697990, 170388186, 269656737, 102288367, 101017918, 12224069, 11286880] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 25600/NS)`. -/
theorem cn15_66 : cornerOK gdata (2688) (25600)
    [161981993, 170388186, 269656737, 102288367, 101017918, 12224069, 11286880] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 20480/NS)`. -/
theorem cn15_67 : cornerOK gdata (2816) (20480)
    [155691438, 150325565, 255714992, 89110228, 96000905, 10330165, 10712990] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 23040/NS)`. -/
theorem cn15_68 : cornerOK gdata (2816) (23040)
    [155691438, 153801842, 264255962, 93652883, 101017918, 11223014, 11401193] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 25600/NS)`. -/
theorem cn15_69 : cornerOK gdata (2816) (25600)
    [150482337, 153801842, 264255962, 93652883, 101017918, 11223014, 11401193] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 20480/NS)`. -/
theorem cn15_70 : cornerOK gdata (2944) (20480)
    [502590174, 390173947, 902624271, 233442947, 361234695, 25601584, 41112663] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 23040/NS)`. -/
theorem cn15_71 : cornerOK gdata (2944) (23040)
    [145911881, 138260754, 258511921, 84862516, 100862923, 10216929, 11401193] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 25600/NS)`. -/
theorem cn15_72 : cornerOK gdata (2944) (25600)
    [502590174, 390173947, 902624271, 233442947, 361234695, 25601584, 41112663] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3008/NT, 20480/NS)`. -/
theorem cn15_73 : cornerOK gdata (3008) (20480)
    [502590174, 390173947, 902624271, 233442947, 361234695, 25601584, 41112663] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3008/NT, 25600/NS)`. -/
theorem cn15_74 : cornerOK gdata (3008) (25600)
    [502590174, 390173947, 909919133, 233442947, 366677734, 25601584, 41830773] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3008/NT, 20480/NS)`. -/
theorem cn15_75 : cornerOK gdata (3008) (20480)
    [499895576, 372591385, 909919133, 223014745, 366677734, 24514818, 41830773] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 20480/NS)`. -/
theorem cn15_76 : cornerOK gdata (3072) (20480)
    [499895576, 372591385, 909919133, 223014745, 366677734, 24514818, 41830773] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 25600/NS)`. -/
theorem cn15_77 : cornerOK gdata (3072) (25600)
    [499895576, 490148249, 909919133, 278781735, 366677734, 34587799, 41830773] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 20480/NS)`. -/
theorem cn15_78 : cornerOK gdata (3072) (20480)
    [467839407, 457159696, 770382393, 252809884, 270210349, 31004511, 28412540] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 20480/NS)`. -/
theorem cn15_79 : cornerOK gdata (3328) (20480)
    [467839407, 457159696, 770382393, 252809884, 270210349, 31004511, 28412540] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 23040/NS)`. -/
theorem cn15_80 : cornerOK gdata (3072) (23040)
    [475998766, 490148249, 829510500, 278781735, 296494294, 34587799, 31452151] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 23040/NS)`. -/
theorem cn15_81 : cornerOK gdata (3328) (23040)
    [475998766, 490148249, 829510500, 278781735, 296494294, 34587799, 31452151] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 25600/NS)`. -/
theorem cn15_82 : cornerOK gdata (3328) (25600)
    [475998766, 490148249, 829510500, 278781735, 296494294, 34587799, 31452151] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 20480/NS)`. -/
theorem cn15_83 : cornerOK gdata (3584) (20480)
    [392983205, 332239252, 674940137, 185326094, 242739247, 22808143, 26020858] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 23040/NS)`. -/
theorem cn15_84 : cornerOK gdata (3584) (23040)
    [394932400, 353975790, 719582017, 202978429, 263757902, 25275884, 28519602] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 25600/NS)`. -/
theorem cn15_85 : cornerOK gdata (3584) (25600)
    [394932400, 353975790, 719582017, 202978429, 263757902, 25275884, 28519602] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 20480/NS)`. -/
theorem cn15_86 : cornerOK gdata (3840) (20480)
    [334988166, 229005301, 594252742, 129460515, 218665908, 16004216, 23807529] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 23040/NS)`. -/
theorem cn15_87 : cornerOK gdata (3840) (23040)
    [334988166, 243150345, 627637881, 141297674, 235352129, 17686410, 25847934] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 25600/NS)`. -/
theorem cn15_88 : cornerOK gdata (3840) (25600)
    [333293544, 243150345, 627637881, 141297674, 235352129, 17686410, 25847934] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 20480/NS)`. -/
theorem cn15_89 : cornerOK gdata (4096) (20480)
    [290006128, 146178319, 526292101, 85744809, 197645274, 10790555, 21779059] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 23040/NS)`. -/
theorem cn15_90 : cornerOK gdata (4096) (23040)
    [290006128, 155232925, 551518507, 93804452, 211160594, 11885393, 23476117] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 25600/NS)`. -/
theorem cn15_91 : cornerOK gdata (4096) (25600)
    [286064113, 155232925, 551518507, 93804452, 211160594, 11885393, 23476117] = true := by
  decide +kernel

/-- Kernel-checked box `[-128, 0]/NT × [20480, 25600]/NS`. -/
theorem cov774 : Cover gdata (-128) (0) (20480) (25600) := by
  ballooning_cover "Q:cn15_0,cn15_1,cn15_2,cn15_3"

/-- Kernel-checked box `[0, 128]/NT × [20480, 25600]/NS`. -/
theorem cov775 : Cover gdata (0) (128) (20480) (25600) := by
  ballooning_cover "Q:cn15_1,cn15_4,cn15_3,cn15_5"

/-- Kernel-checked box `[128, 256]/NT × [20480, 25600]/NS`. -/
theorem cov776 : Cover gdata (128) (256) (20480) (25600) := by
  ballooning_cover "Q:cn15_4,cn15_6,cn15_5,cn15_7"

/-- Kernel-checked box `[256, 384]/NT × [20480, 25600]/NS`. -/
theorem cov777 : Cover gdata (256) (384) (20480) (25600) := by
  ballooning_cover "Q:cn15_6,cn15_8,cn15_7,cn15_9"

/-- Kernel-checked box `[384, 512]/NT × [20480, 25600]/NS`. -/
theorem cov778 : Cover gdata (384) (512) (20480) (25600) := by
  ballooning_cover "Q:cn15_8,cn15_10,cn15_9,cn15_11"

/-- Kernel-checked box `[512, 640]/NT × [20480, 25600]/NS`. -/
theorem cov779 : Cover gdata (512) (640) (20480) (25600) := by
  ballooning_cover "Q:cn15_10,cn15_12,cn15_11,cn15_13"

/-- Kernel-checked box `[640, 768]/NT × [20480, 25600]/NS`. -/
theorem cov780 : Cover gdata (640) (768) (20480) (25600) := by
  ballooning_cover "Q:cn15_12,cn15_14,cn15_13,cn15_15"

/-- Kernel-checked box `[768, 832]/NT × [20480, 25600]/NS`. -/
theorem cov781 : Cover gdata (768) (832) (20480) (25600) := by
  ballooning_cover "Q:cn15_14,cn15_16,cn15_15,cn15_17"

/-- Kernel-checked box `[832, 896]/NT × [20480, 25600]/NS`. -/
theorem cov782 : Cover gdata (832) (896) (20480) (25600) := by
  ballooning_cover "Q:cn15_16,cn15_18,cn15_17,cn15_19"

/-- Kernel-checked box `[896, 960]/NT × [20480, 25600]/NS`. -/
theorem cov783 : Cover gdata (896) (960) (20480) (25600) := by
  ballooning_cover "Q:cn15_18,cn15_20,cn15_19,cn15_21"

/-- Kernel-checked box `[960, 1024]/NT × [20480, 25600]/NS`. -/
theorem cov784 : Cover gdata (960) (1024) (20480) (25600) := by
  ballooning_cover "Q:cn15_20,cn15_22,cn15_21,cn15_23"

/-- Kernel-checked box `[1024, 1088]/NT × [20480, 25600]/NS`. -/
theorem cov785 : Cover gdata (1024) (1088) (20480) (25600) := by
  ballooning_cover "Q:cn15_22,cn15_24,cn15_23,cn15_25"

/-- Kernel-checked box `[1088, 1152]/NT × [20480, 25600]/NS`. -/
theorem cov786 : Cover gdata (1088) (1152) (20480) (25600) := by
  ballooning_cover "Q:cn15_24,cn15_26,cn15_25,cn15_27"

/-- Kernel-checked box `[1152, 1216]/NT × [20480, 25600]/NS`. -/
theorem cov787 : Cover gdata (1152) (1216) (20480) (25600) := by
  ballooning_cover "Q:cn15_26,cn15_28,cn15_27,cn15_29"

/-- Kernel-checked box `[1216, 1280]/NT × [20480, 25600]/NS`. -/
theorem cov788 : Cover gdata (1216) (1280) (20480) (25600) := by
  ballooning_cover "Q:cn15_28,cn15_30,cn15_29,cn15_31"

/-- Kernel-checked box `[1280, 1344]/NT × [20480, 25600]/NS`. -/
theorem cov789 : Cover gdata (1280) (1344) (20480) (25600) := by
  ballooning_cover "Q:cn15_30,cn15_32,cn15_31,cn15_33"

/-- Kernel-checked box `[1344, 1408]/NT × [20480, 25600]/NS`. -/
theorem cov790 : Cover gdata (1344) (1408) (20480) (25600) := by
  ballooning_cover "Q:cn15_32,cn15_34,cn15_33,cn15_35"

/-- Kernel-checked box `[1408, 1536]/NT × [20480, 23040]/NS`. -/
theorem cov791 : Cover gdata (1408) (1536) (20480) (23040) := by
  ballooning_cover "Q:cn15_34,cn15_36,cn15_37,cn15_38"

/-- Kernel-checked box `[1408, 1536]/NT × [23040, 25600]/NS`. -/
theorem cov792 : Cover gdata (1408) (1536) (23040) (25600) := by
  ballooning_cover "Q:cn15_37,cn15_38,cn15_35,cn15_39"

/-- Kernel-checked box `[1536, 1664]/NT × [20480, 23040]/NS`. -/
theorem cov793 : Cover gdata (1536) (1664) (20480) (23040) := by
  ballooning_cover "Q:cn15_36,cn15_40,cn15_38,cn15_41"

/-- Kernel-checked box `[1536, 1664]/NT × [23040, 25600]/NS`. -/
theorem cov794 : Cover gdata (1536) (1664) (23040) (25600) := by
  ballooning_cover "Q:cn15_38,cn15_41,cn15_39,cn15_42"

/-- Kernel-checked box `[1664, 1792]/NT × [20480, 23040]/NS`. -/
theorem cov795 : Cover gdata (1664) (1792) (20480) (23040) := by
  ballooning_cover "Q:cn15_40,cn15_43,cn15_41,cn15_44"

/-- Kernel-checked box `[1664, 1792]/NT × [23040, 25600]/NS`. -/
theorem cov796 : Cover gdata (1664) (1792) (23040) (25600) := by
  ballooning_cover "Q:cn15_41,cn15_44,cn15_42,cn15_45"

/-- Kernel-checked box `[1792, 1920]/NT × [20480, 23040]/NS`. -/
theorem cov797 : Cover gdata (1792) (1920) (20480) (23040) := by
  ballooning_cover "Q:cn15_43,cn15_46,cn15_44,cn15_47"

/-- Kernel-checked box `[1792, 1920]/NT × [23040, 25600]/NS`. -/
theorem cov798 : Cover gdata (1792) (1920) (23040) (25600) := by
  ballooning_cover "Q:cn15_44,cn15_47,cn15_45,cn15_48"

/-- Kernel-checked box `[1920, 2048]/NT × [20480, 23040]/NS`. -/
theorem cov799 : Cover gdata (1920) (2048) (20480) (23040) := by
  ballooning_cover "Q:cn15_46,cn15_49,cn15_47,cn15_50"

/-- Kernel-checked box `[1920, 2048]/NT × [23040, 25600]/NS`. -/
theorem cov800 : Cover gdata (1920) (2048) (23040) (25600) := by
  ballooning_cover "Q:cn15_47,cn15_50,cn15_48,cn15_51"

/-- Kernel-checked box `[2048, 2176]/NT × [20480, 23040]/NS`. -/
theorem cov801 : Cover gdata (2048) (2176) (20480) (23040) := by
  ballooning_cover "Q:cn15_49,cn15_52,cn15_50,cn15_53"

/-- Kernel-checked box `[2048, 2176]/NT × [23040, 25600]/NS`. -/
theorem cov802 : Cover gdata (2048) (2176) (23040) (25600) := by
  ballooning_cover "Q:cn15_50,cn15_53,cn15_51,cn15_54"

/-- Kernel-checked box `[2176, 2304]/NT × [20480, 23040]/NS`. -/
theorem cov803 : Cover gdata (2176) (2304) (20480) (23040) := by
  ballooning_cover "Q:cn15_52,cn15_55,cn15_53,cn15_56"

/-- Kernel-checked box `[2176, 2304]/NT × [23040, 25600]/NS`. -/
theorem cov804 : Cover gdata (2176) (2304) (23040) (25600) := by
  ballooning_cover "Q:cn15_53,cn15_56,cn15_54,cn15_57"

/-- Kernel-checked box `[2304, 2432]/NT × [20480, 23040]/NS`. -/
theorem cov805 : Cover gdata (2304) (2432) (20480) (23040) := by
  ballooning_cover "Q:cn15_55,cn15_58,cn15_56,cn15_59"

/-- Kernel-checked box `[2304, 2432]/NT × [23040, 25600]/NS`. -/
theorem cov806 : Cover gdata (2304) (2432) (23040) (25600) := by
  ballooning_cover "Q:cn15_56,cn15_59,cn15_57,cn15_60"

/-- Kernel-checked box `[2432, 2560]/NT × [20480, 23040]/NS`. -/
theorem cov807 : Cover gdata (2432) (2560) (20480) (23040) := by
  ballooning_cover "Q:cn15_58,cn15_61,cn15_59,cn15_62"

/-- Kernel-checked box `[2432, 2560]/NT × [23040, 25600]/NS`. -/
theorem cov808 : Cover gdata (2432) (2560) (23040) (25600) := by
  ballooning_cover "Q:cn15_59,cn15_62,cn15_60,cn15_63"

/-- Kernel-checked box `[2560, 2688]/NT × [20480, 23040]/NS`. -/
theorem cov809 : Cover gdata (2560) (2688) (20480) (23040) := by
  ballooning_cover "Q:cn15_61,cn15_64,cn15_62,cn15_65"

/-- Kernel-checked box `[2560, 2688]/NT × [23040, 25600]/NS`. -/
theorem cov810 : Cover gdata (2560) (2688) (23040) (25600) := by
  ballooning_cover "Q:cn15_62,cn15_65,cn15_63,cn15_66"

/-- Kernel-checked box `[2688, 2816]/NT × [20480, 23040]/NS`. -/
theorem cov811 : Cover gdata (2688) (2816) (20480) (23040) := by
  ballooning_cover "Q:cn15_64,cn15_67,cn15_65,cn15_68"

/-- Kernel-checked box `[2688, 2816]/NT × [23040, 25600]/NS`. -/
theorem cov812 : Cover gdata (2688) (2816) (23040) (25600) := by
  ballooning_cover "Q:cn15_65,cn15_68,cn15_66,cn15_69"

/-- Kernel-checked box `[2816, 2944]/NT × [20480, 23040]/NS`. -/
theorem cov813 : Cover gdata (2816) (2944) (20480) (23040) := by
  ballooning_cover "Q:cn15_67,cn15_70,cn15_68,cn15_71"

/-- Kernel-checked box `[2816, 2944]/NT × [23040, 25600]/NS`. -/
theorem cov814 : Cover gdata (2816) (2944) (23040) (25600) := by
  ballooning_cover "Q:cn15_68,cn15_71,cn15_69,cn15_72"

/-- Kernel-checked box `[2944, 3008]/NT × [20480, 25600]/NS`. -/
theorem cov815 : Cover gdata (2944) (3008) (20480) (25600) := by
  ballooning_cover "Q:cn15_70,cn15_73,cn15_72,cn15_74"

/-- Kernel-checked box `[3008, 3072]/NT × [20480, 25600]/NS`. -/
theorem cov816 : Cover gdata (3008) (3072) (20480) (25600) := by
  ballooning_cover "Q:cn15_75,cn15_76,cn15_74,cn15_77"

/-- Kernel-checked box `[3072, 3328]/NT × [20480, 23040]/NS`. -/
theorem cov817 : Cover gdata (3072) (3328) (20480) (23040) := by
  ballooning_cover "Q:cn15_78,cn15_79,cn15_80,cn15_81"

/-- Kernel-checked box `[3072, 3328]/NT × [23040, 25600]/NS`. -/
theorem cov818 : Cover gdata (3072) (3328) (23040) (25600) := by
  ballooning_cover "Q:cn15_80,cn15_81,cn15_77,cn15_82"

/-- Kernel-checked box `[3328, 3584]/NT × [20480, 23040]/NS`. -/
theorem cov819 : Cover gdata (3328) (3584) (20480) (23040) := by
  ballooning_cover "Q:cn15_79,cn15_83,cn15_81,cn15_84"

/-- Kernel-checked box `[3328, 3584]/NT × [23040, 25600]/NS`. -/
theorem cov820 : Cover gdata (3328) (3584) (23040) (25600) := by
  ballooning_cover "Q:cn15_81,cn15_84,cn15_82,cn15_85"

/-- Kernel-checked box `[3584, 3840]/NT × [20480, 23040]/NS`. -/
theorem cov821 : Cover gdata (3584) (3840) (20480) (23040) := by
  ballooning_cover "Q:cn15_83,cn15_86,cn15_84,cn15_87"

/-- Kernel-checked box `[3584, 3840]/NT × [23040, 25600]/NS`. -/
theorem cov822 : Cover gdata (3584) (3840) (23040) (25600) := by
  ballooning_cover "Q:cn15_84,cn15_87,cn15_85,cn15_88"

/-- Kernel-checked box `[3840, 4096]/NT × [20480, 23040]/NS`. -/
theorem cov823 : Cover gdata (3840) (4096) (20480) (23040) := by
  ballooning_cover "Q:cn15_86,cn15_89,cn15_87,cn15_90"

/-- Kernel-checked box `[3840, 4096]/NT × [23040, 25600]/NS`. -/
theorem cov824 : Cover gdata (3840) (4096) (23040) (25600) := by
  ballooning_cover "Q:cn15_87,cn15_90,cn15_88,cn15_91"

end PlasmaLean.Design.SolovevBallooning
