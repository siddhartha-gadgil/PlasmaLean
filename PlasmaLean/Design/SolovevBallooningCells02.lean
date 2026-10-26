/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningEvalCert

/-!
# Ballooning certificate: kernel-checked cells, part 2

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

/-- Kernel-checked corner test at `(-2560/NT, 1024/NS)`. -/
theorem cn02_0 : cornerOK gdata (-2560) (1024)
    [46143705, 31013146, 35021230, 14200319, 9224223, 1660490, 792429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 1024/NS)`. -/
theorem cn02_1 : cornerOK gdata (-2432) (1024)
    [46379925, 32031628, 35021230, 14565942, 9224223, 1698845, 792429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 2048/NS)`. -/
theorem cn02_2 : cornerOK gdata (-2560) (2048)
    [46143705, 31013146, 35021230, 14200319, 9224223, 1660490, 792429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 2048/NS)`. -/
theorem cn02_3 : cornerOK gdata (-2432) (2048)
    [46379925, 32031628, 35021230, 14565942, 9224223, 1698845, 792429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 1024/NS)`. -/
theorem cn02_4 : cornerOK gdata (-2304) (1024)
    [46414723, 32651478, 34904961, 14750144, 8919682, 1714086, 747579] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 2048/NS)`. -/
theorem cn02_5 : cornerOK gdata (-2304) (2048)
    [46414723, 32651478, 34904961, 14750144, 8919682, 1714086, 747579] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 1024/NS)`. -/
theorem cn02_6 : cornerOK gdata (-2176) (1024)
    [46414723, 32787107, 34630659, 14750144, 8576152, 1714086, 699444] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 2048/NS)`. -/
theorem cn02_7 : cornerOK gdata (-2176) (2048)
    [46414723, 32787107, 34630659, 14750144, 8576152, 1714086, 699444] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 1024/NS)`. -/
theorem cn02_8 : cornerOK gdata (-2048) (1024)
    [46150976, 32787107, 34129320, 14718846, 8220314, 1701843, 648469] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 2048/NS)`. -/
theorem cn02_9 : cornerOK gdata (-2048) (2048)
    [46150976, 32787107, 34129320, 14718846, 8220314, 1701843, 648469] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 1024/NS)`. -/
theorem cn02_10 : cornerOK gdata (-1920) (1024)
    [45518819, 32399694, 33358069, 14462177, 7955226, 1660716, 594990] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 2048/NS)`. -/
theorem cn02_11 : cornerOK gdata (-1920) (2048)
    [45518819, 32399694, 33358069, 14462177, 7955226, 1660716, 594990] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 1024/NS)`. -/
theorem cn02_12 : cornerOK gdata (-1792) (1024)
    [44499324, 31492534, 32310877, 13988718, 7623632, 1592029, 547476] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 2048/NS)`. -/
theorem cn02_13 : cornerOK gdata (-1792) (2048)
    [44499324, 31492534, 32310877, 13988718, 7623632, 1592029, 547476] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 1024/NS)`. -/
theorem cn02_14 : cornerOK gdata (-1664) (1024)
    [43049992, 30266380, 30971205, 13327880, 7224788, 1499326, 511661] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 2048/NS)`. -/
theorem cn02_15 : cornerOK gdata (-1664) (2048)
    [43049992, 30266380, 30971205, 13327880, 7224788, 1499326, 511661] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 1024/NS)`. -/
theorem cn02_16 : cornerOK gdata (-1536) (1024)
    [41198634, 29726473, 29464197, 12824917, 6784495, 1421293, 472811] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 2048/NS)`. -/
theorem cn02_17 : cornerOK gdata (-1536) (2048)
    [41198634, 29726473, 29464197, 12824917, 6784495, 1421293, 472811] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 1024/NS)`. -/
theorem cn02_18 : cornerOK gdata (-1408) (1024)
    [39440773, 28910942, 27986241, 12197988, 6344937, 1356590, 435588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 2048/NS)`. -/
theorem cn02_19 : cornerOK gdata (-1408) (2048)
    [39440773, 28910942, 27986241, 12197988, 6344937, 1356590, 435588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 1024/NS)`. -/
theorem cn02_20 : cornerOK gdata (-1280) (1024)
    [37406991, 27785960, 26364343, 11459744, 5892511, 1285020, 401020] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 2048/NS)`. -/
theorem cn02_21 : cornerOK gdata (-1280) (2048)
    [37406991, 27785960, 26364343, 11459744, 5892511, 1285020, 401020] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 1024/NS)`. -/
theorem cn02_22 : cornerOK gdata (-1152) (1024)
    [34989220, 26316280, 24495850, 10611656, 5396536, 1199888, 365156] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 2048/NS)`. -/
theorem cn02_23 : cornerOK gdata (-1152) (2048)
    [34989220, 26316280, 24495850, 10611656, 5396536, 1199888, 365156] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 1024/NS)`. -/
theorem cn02_24 : cornerOK gdata (-1024) (1024)
    [32237703, 24523204, 22418453, 9676945, 4867506, 1102619, 328431] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 2048/NS)`. -/
theorem cn02_25 : cornerOK gdata (-1024) (2048)
    [32237703, 24523204, 22418453, 9676945, 4867506, 1102619, 328431] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 1024/NS)`. -/
theorem cn02_26 : cornerOK gdata (-896) (1024)
    [29523576, 22434565, 20197555, 8670429, 4322169, 994621, 291616] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 2048/NS)`. -/
theorem cn02_27 : cornerOK gdata (-896) (2048)
    [29523576, 22434565, 20197555, 8670429, 4322169, 994621, 291616] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 1024/NS)`. -/
theorem cn02_28 : cornerOK gdata (-768) (1024)
    [26742976, 20103391, 17916213, 7616845, 3800412, 877847, 255414] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 2048/NS)`. -/
theorem cn02_29 : cornerOK gdata (-768) (2048)
    [26742976, 20103391, 17916213, 7616845, 3800412, 877847, 255414] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 1024/NS)`. -/
theorem cn02_30 : cornerOK gdata (-640) (1024)
    [24167177, 17569383, 15811560, 6540030, 3373621, 754606, 220542] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 2048/NS)`. -/
theorem cn02_31 : cornerOK gdata (-640) (2048)
    [24167177, 17569383, 15811560, 6540030, 3373621, 754606, 220542] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 1024/NS)`. -/
theorem cn02_32 : cornerOK gdata (-512) (1024)
    [90561427, 55151774, 58625249, 22881302, 12283822, 2731832, 755318] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 2048/NS)`. -/
theorem cn02_33 : cornerOK gdata (-512) (2048)
    [90561427, 55151774, 58625249, 22881302, 12283822, 2731832, 755318] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 1024/NS)`. -/
theorem cn02_34 : cornerOK gdata (-256) (1024)
    [90561427, 55151774, 58625249, 22881302, 12283822, 2731832, 755318] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 2048/NS)`. -/
theorem cn02_35 : cornerOK gdata (-256) (2048)
    [90561427, 55151774, 58625249, 22881302, 12283822, 2731832, 755318] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 1024/NS)`. -/
theorem cn02_36 : cornerOK gdata (0) (1024)
    [71022966, 36424919, 45815824, 15205047, 9546459, 1694993, 594751] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 2048/NS)`. -/
theorem cn02_37 : cornerOK gdata (0) (2048)
    [71022966, 36424919, 45815824, 15205047, 9546459, 1694993, 594751] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 1024/NS)`. -/
theorem cn02_38 : cornerOK gdata (256) (1024)
    [71022966, 36424919, 45815824, 15205047, 9546459, 1694993, 594751] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 2048/NS)`. -/
theorem cn02_39 : cornerOK gdata (256) (2048)
    [71022966, 36424919, 45815824, 15205047, 9546459, 1694993, 594751] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 1024/NS)`. -/
theorem cn02_40 : cornerOK gdata (384) (1024)
    [19029922, 11058790, 11785795, 4369922, 2467198, 496628, 148394] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 2048/NS)`. -/
theorem cn02_41 : cornerOK gdata (384) (2048)
    [19029922, 11058790, 11785795, 4369922, 2467198, 496628, 148394] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 1024/NS)`. -/
theorem cn02_42 : cornerOK gdata (512) (1024)
    [20721321, 12968547, 13134520, 5113963, 2753269, 594870, 171397] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 2048/NS)`. -/
theorem cn02_43 : cornerOK gdata (512) (2048)
    [20721321, 12968547, 13134520, 5113963, 2753269, 594870, 171397] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 1024/NS)`. -/
theorem cn02_44 : cornerOK gdata (640) (1024)
    [22558181, 14681842, 14578659, 5855975, 3071970, 704572, 196507] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 2048/NS)`. -/
theorem cn02_45 : cornerOK gdata (640) (2048)
    [22558181, 14681842, 14578659, 5855975, 3071970, 704572, 196507] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 1024/NS)`. -/
theorem cn02_46 : cornerOK gdata (768) (1024)
    [24329528, 16149657, 16039673, 6659640, 3465550, 808103, 223113] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 2048/NS)`. -/
theorem cn02_47 : cornerOK gdata (768) (2048)
    [24329528, 16149657, 16039673, 6659640, 3465550, 808103, 223113] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 1024/NS)`. -/
theorem cn02_48 : cornerOK gdata (896) (1024)
    [25986268, 17370531, 17708280, 7419905, 3879450, 903224, 252338] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 2048/NS)`. -/
theorem cn02_49 : cornerOK gdata (896) (2048)
    [25986268, 17370531, 17708280, 7419905, 3879450, 903224, 252338] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 1024/NS)`. -/
theorem cn02_50 : cornerOK gdata (1024) (1024)
    [27491034, 18557826, 19276366, 8154476, 4283633, 987935, 284040] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 2048/NS)`. -/
theorem cn02_51 : cornerOK gdata (1024) (2048)
    [27491034, 18557826, 19276366, 8154476, 4283633, 987935, 284040] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 1024/NS)`. -/
theorem cn02_52 : cornerOK gdata (1152) (1024)
    [28815758, 19528687, 20681838, 8804306, 4672523, 1060836, 316079] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 2048/NS)`. -/
theorem cn02_53 : cornerOK gdata (1152) (2048)
    [28815758, 19528687, 20681838, 8804306, 4672523, 1060836, 316079] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 1024/NS)`. -/
theorem cn02_54 : cornerOK gdata (1280) (1024)
    [29924550, 20258378, 21883708, 9351762, 5037463, 1120446, 351220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 2048/NS)`. -/
theorem cn02_55 : cornerOK gdata (1280) (2048)
    [29924550, 20258378, 21883708, 9351762, 5037463, 1120446, 351220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 1024/NS)`. -/
theorem cn02_56 : cornerOK gdata (1408) (1024)
    [31167155, 20776182, 23051470, 9798037, 5409131, 1167428, 391495] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 2048/NS)`. -/
theorem cn02_57 : cornerOK gdata (1408) (2048)
    [31167155, 20776182, 23051470, 9798037, 5409131, 1167428, 391495] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 1024/NS)`. -/
theorem cn02_58 : cornerOK gdata (1536) (1024)
    [32380720, 21321636, 24168778, 10143929, 5806647, 1202762, 437587] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 2048/NS)`. -/
theorem cn02_59 : cornerOK gdata (1536) (2048)
    [32380720, 21321636, 24168778, 10143929, 5806647, 1202762, 437587] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 1024/NS)`. -/
theorem cn02_60 : cornerOK gdata (1664) (1024)
    [33324994, 22048958, 25353433, 10536465, 6188356, 1248523, 482905] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 2048/NS)`. -/
theorem cn02_61 : cornerOK gdata (1664) (2048)
    [33324994, 22048958, 25353433, 10536465, 6188356, 1248523, 482905] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 1024/NS)`. -/
theorem cn02_62 : cornerOK gdata (1792) (1024)
    [34015439, 22719819, 26480421, 10902611, 6534992, 1299791, 526251] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 2048/NS)`. -/
theorem cn02_63 : cornerOK gdata (1792) (2048)
    [34015439, 22719819, 26480421, 10902611, 6534992, 1299791, 526251] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 1024/NS)`. -/
theorem cn02_64 : cornerOK gdata (1920) (1024)
    [34453655, 23024879, 27408490, 11100404, 6840886, 1329433, 567360] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 2048/NS)`. -/
theorem cn02_65 : cornerOK gdata (1920) (2048)
    [34453655, 23024879, 27408490, 11100404, 6840886, 1329433, 567360] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 1024/NS)`. -/
theorem cn02_66 : cornerOK gdata (2048) (1024)
    [34663503, 23024879, 28145304, 11126551, 7101886, 1337130, 605400] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 2048/NS)`. -/
theorem cn02_67 : cornerOK gdata (2048) (2048)
    [34663503, 23024879, 28145304, 11126551, 7101886, 1337130, 605400] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 1024/NS)`. -/
theorem cn02_68 : cornerOK gdata (2176) (1024)
    [34670883, 22961876, 28702662, 11126551, 7317783, 1337130, 639878] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 2048/NS)`. -/
theorem cn02_69 : cornerOK gdata (2176) (2048)
    [34670883, 22961876, 28702662, 11126551, 7317783, 1337130, 639878] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 1024/NS)`. -/
theorem cn02_70 : cornerOK gdata (2304) (1024)
    [34670883, 22555094, 29104941, 10988490, 7517275, 1323862, 670718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 2048/NS)`. -/
theorem cn02_71 : cornerOK gdata (2304) (2048)
    [34670883, 22555094, 29104941, 10988490, 7517275, 1323862, 670718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 1024/NS)`. -/
theorem cn02_72 : cornerOK gdata (2432) (1024)
    [34529099, 21860225, 29394392, 10708524, 7687538, 1292374, 698325] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 2048/NS)`. -/
theorem cn02_73 : cornerOK gdata (2432) (2048)
    [34529099, 21860225, 29394392, 10708524, 7687538, 1292374, 698325] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 1024/NS)`. -/
theorem cn02_74 : cornerOK gdata (2560) (1024)
    [34387062, 20948256, 29557757, 10320840, 7826523, 1247045, 721600] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 2048/NS)`. -/
theorem cn02_75 : cornerOK gdata (2560) (2048)
    [34387062, 20948256, 29557757, 10320840, 7826523, 1247045, 721600] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 1024/NS)`. -/
theorem cn02_76 : cornerOK gdata (2688) (1024)
    [34096497, 19813451, 29608205, 9815355, 7938764, 1186788, 740855] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 2048/NS)`. -/
theorem cn02_77 : cornerOK gdata (2688) (2048)
    [34096497, 19813451, 29608205, 9815355, 7938764, 1186788, 740855] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 1024/NS)`. -/
theorem cn02_78 : cornerOK gdata (2816) (1024)
    [33673692, 18489479, 29608205, 9210361, 8010817, 1114275, 756602] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 2048/NS)`. -/
theorem cn02_79 : cornerOK gdata (2816) (2048)
    [33673692, 18489479, 29608205, 9210361, 8010817, 1114275, 756602] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 1024/NS)`. -/
theorem cn02_80 : cornerOK gdata (2944) (1024)
    [33150505, 17018780, 29584927, 8524851, 8047249, 1031930, 768074] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 2048/NS)`. -/
theorem cn02_81 : cornerOK gdata (2944) (2048)
    [33150505, 17018780, 29584927, 8524851, 8047249, 1031930, 768074] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 1024/NS)`. -/
theorem cn02_82 : cornerOK gdata (3072) (1024)
    [88996238, 49426338, 80613668, 23837729, 22251869, 2930435, 2017730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 2048/NS)`. -/
theorem cn02_83 : cornerOK gdata (3072) (2048)
    [88996238, 49426338, 80613668, 23837729, 22251869, 2930435, 2017730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 1024/NS)`. -/
theorem cn02_84 : cornerOK gdata (3328) (1024)
    [88996238, 49426338, 80613668, 23837729, 22251869, 2930435, 2017730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 2048/NS)`. -/
theorem cn02_85 : cornerOK gdata (3328) (2048)
    [88996238, 49426338, 80613668, 23837729, 22251869, 2930435, 2017730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 1024/NS)`. -/
theorem cn02_86 : cornerOK gdata (3584) (1024)
    [79224258, 37752567, 73401923, 18429575, 20600291, 2269636, 1904677] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 2048/NS)`. -/
theorem cn02_87 : cornerOK gdata (3584) (2048)
    [79224258, 37752567, 73401923, 18429575, 20600291, 2269636, 1904677] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 1024/NS)`. -/
theorem cn02_88 : cornerOK gdata (3840) (1024)
    [70549763, 28470827, 66588882, 14084611, 18935508, 1735674, 1779569] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 2048/NS)`. -/
theorem cn02_89 : cornerOK gdata (3840) (2048)
    [70549763, 28470827, 66588882, 14084611, 18935508, 1735674, 1779569] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 1024/NS)`. -/
theorem cn02_90 : cornerOK gdata (4096) (1024)
    [63018955, 20503004, 60288420, 10156003, 17311183, 1258787, 1649554] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 2048/NS)`. -/
theorem cn02_91 : cornerOK gdata (4096) (2048)
    [63018955, 20503004, 60288420, 10156003, 17311183, 1258787, 1649554] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 2048/NS)`. -/
theorem cn02_92 : cornerOK gdata (-4096) (2048)
    [100736308, 30526003, 83720607, 14378293, 23618968, 1806004, 2116703] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 2048/NS)`. -/
theorem cn02_93 : cornerOK gdata (-3840) (2048)
    [112777482, 44307007, 93155296, 20560812, 25789073, 2526830, 2268677] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 3072/NS)`. -/
theorem cn02_94 : cornerOK gdata (-4096) (3072)
    [123229718, 36949083, 98960341, 17056082, 26830977, 2137115, 2322705] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 3072/NS)`. -/
theorem cn02_95 : cornerOK gdata (-3840) (3072)
    [138538878, 53876176, 110647825, 24566781, 29491295, 3005815, 2502184] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 4096/NS)`. -/
theorem cn02_96 : cornerOK gdata (-4096) (4096)
    [123229718, 36949083, 98960341, 17056082, 26830977, 2137115, 2322705] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 4096/NS)`. -/
theorem cn02_97 : cornerOK gdata (-3840) (4096)
    [138538878, 53876176, 110647825, 24566781, 29491295, 3005815, 2502184] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 2048/NS)`. -/
theorem cn02_98 : cornerOK gdata (-3584) (2048)
    [126570810, 60198504, 103371629, 27335697, 27953196, 3384136, 2406868] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 3072/NS)`. -/
theorem cn02_99 : cornerOK gdata (-3584) (3072)
    [156126304, 73845753, 123401953, 32885189, 32177866, 4052746, 2669551] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 4096/NS)`. -/
theorem cn02_100 : cornerOK gdata (-3584) (4096)
    [156126304, 73845753, 123401953, 32885189, 32177866, 4052746, 2669551] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 2048/NS)`. -/
theorem cn02_101 : cornerOK gdata (-3328) (2048)
    [126570810, 60198504, 103371629, 27335697, 27953196, 3384136, 2406868] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 3072/NS)`. -/
theorem cn02_102 : cornerOK gdata (-3328) (3072)
    [156126304, 73845753, 123401953, 32885189, 32177866, 4052746, 2669551] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 4096/NS)`. -/
theorem cn02_103 : cornerOK gdata (-3328) (4096)
    [156126304, 73845753, 123401953, 32885189, 32177866, 4052746, 2669551] = true := by
  bl_cert

/-- Kernel-checked box `[-2560, -2432]/NT × [1024, 2048]/NS`. -/
theorem cov104 : Cover gdata (-2560) (-2432) (1024) (2048) := by
  ballooning_cover "Q:cn02_0,cn02_1,cn02_2,cn02_3"

/-- Kernel-checked box `[-2432, -2304]/NT × [1024, 2048]/NS`. -/
theorem cov105 : Cover gdata (-2432) (-2304) (1024) (2048) := by
  ballooning_cover "Q:cn02_1,cn02_4,cn02_3,cn02_5"

/-- Kernel-checked box `[-2304, -2176]/NT × [1024, 2048]/NS`. -/
theorem cov106 : Cover gdata (-2304) (-2176) (1024) (2048) := by
  ballooning_cover "Q:cn02_4,cn02_6,cn02_5,cn02_7"

/-- Kernel-checked box `[-2176, -2048]/NT × [1024, 2048]/NS`. -/
theorem cov107 : Cover gdata (-2176) (-2048) (1024) (2048) := by
  ballooning_cover "Q:cn02_6,cn02_8,cn02_7,cn02_9"

/-- Kernel-checked box `[-2048, -1920]/NT × [1024, 2048]/NS`. -/
theorem cov108 : Cover gdata (-2048) (-1920) (1024) (2048) := by
  ballooning_cover "Q:cn02_8,cn02_10,cn02_9,cn02_11"

/-- Kernel-checked box `[-1920, -1792]/NT × [1024, 2048]/NS`. -/
theorem cov109 : Cover gdata (-1920) (-1792) (1024) (2048) := by
  ballooning_cover "Q:cn02_10,cn02_12,cn02_11,cn02_13"

/-- Kernel-checked box `[-1792, -1664]/NT × [1024, 2048]/NS`. -/
theorem cov110 : Cover gdata (-1792) (-1664) (1024) (2048) := by
  ballooning_cover "Q:cn02_12,cn02_14,cn02_13,cn02_15"

/-- Kernel-checked box `[-1664, -1536]/NT × [1024, 2048]/NS`. -/
theorem cov111 : Cover gdata (-1664) (-1536) (1024) (2048) := by
  ballooning_cover "Q:cn02_14,cn02_16,cn02_15,cn02_17"

/-- Kernel-checked box `[-1536, -1408]/NT × [1024, 2048]/NS`. -/
theorem cov112 : Cover gdata (-1536) (-1408) (1024) (2048) := by
  ballooning_cover "Q:cn02_16,cn02_18,cn02_17,cn02_19"

/-- Kernel-checked box `[-1408, -1280]/NT × [1024, 2048]/NS`. -/
theorem cov113 : Cover gdata (-1408) (-1280) (1024) (2048) := by
  ballooning_cover "Q:cn02_18,cn02_20,cn02_19,cn02_21"

/-- Kernel-checked box `[-1280, -1152]/NT × [1024, 2048]/NS`. -/
theorem cov114 : Cover gdata (-1280) (-1152) (1024) (2048) := by
  ballooning_cover "Q:cn02_20,cn02_22,cn02_21,cn02_23"

/-- Kernel-checked box `[-1152, -1024]/NT × [1024, 2048]/NS`. -/
theorem cov115 : Cover gdata (-1152) (-1024) (1024) (2048) := by
  ballooning_cover "Q:cn02_22,cn02_24,cn02_23,cn02_25"

/-- Kernel-checked box `[-1024, -896]/NT × [1024, 2048]/NS`. -/
theorem cov116 : Cover gdata (-1024) (-896) (1024) (2048) := by
  ballooning_cover "Q:cn02_24,cn02_26,cn02_25,cn02_27"

/-- Kernel-checked box `[-896, -768]/NT × [1024, 2048]/NS`. -/
theorem cov117 : Cover gdata (-896) (-768) (1024) (2048) := by
  ballooning_cover "Q:cn02_26,cn02_28,cn02_27,cn02_29"

/-- Kernel-checked box `[-768, -640]/NT × [1024, 2048]/NS`. -/
theorem cov118 : Cover gdata (-768) (-640) (1024) (2048) := by
  ballooning_cover "Q:cn02_28,cn02_30,cn02_29,cn02_31"

/-- Kernel-checked box `[-640, -512]/NT × [1024, 2048]/NS`. -/
theorem cov119 : Cover gdata (-640) (-512) (1024) (2048) := by
  ballooning_cover "Q:cn02_30,cn02_32,cn02_31,cn02_33"

/-- Kernel-checked box `[-512, -256]/NT × [1024, 2048]/NS`. -/
theorem cov120 : Cover gdata (-512) (-256) (1024) (2048) := by
  ballooning_cover "Q:cn02_32,cn02_34,cn02_33,cn02_35"

/-- Kernel-checked box `[-256, 0]/NT × [1024, 2048]/NS`. -/
theorem cov121 : Cover gdata (-256) (0) (1024) (2048) := by
  ballooning_cover "Q:cn02_34,cn02_36,cn02_35,cn02_37"

/-- Kernel-checked box `[0, 256]/NT × [1024, 2048]/NS`. -/
theorem cov122 : Cover gdata (0) (256) (1024) (2048) := by
  ballooning_cover "Q:cn02_36,cn02_38,cn02_37,cn02_39"

/-- Kernel-checked box `[256, 384]/NT × [1024, 2048]/NS`. -/
theorem cov123 : Cover gdata (256) (384) (1024) (2048) := by
  ballooning_cover "Q:cn02_38,cn02_40,cn02_39,cn02_41"

/-- Kernel-checked box `[384, 512]/NT × [1024, 2048]/NS`. -/
theorem cov124 : Cover gdata (384) (512) (1024) (2048) := by
  ballooning_cover "Q:cn02_40,cn02_42,cn02_41,cn02_43"

/-- Kernel-checked box `[512, 640]/NT × [1024, 2048]/NS`. -/
theorem cov125 : Cover gdata (512) (640) (1024) (2048) := by
  ballooning_cover "Q:cn02_42,cn02_44,cn02_43,cn02_45"

/-- Kernel-checked box `[640, 768]/NT × [1024, 2048]/NS`. -/
theorem cov126 : Cover gdata (640) (768) (1024) (2048) := by
  ballooning_cover "Q:cn02_44,cn02_46,cn02_45,cn02_47"

/-- Kernel-checked box `[768, 896]/NT × [1024, 2048]/NS`. -/
theorem cov127 : Cover gdata (768) (896) (1024) (2048) := by
  ballooning_cover "Q:cn02_46,cn02_48,cn02_47,cn02_49"

/-- Kernel-checked box `[896, 1024]/NT × [1024, 2048]/NS`. -/
theorem cov128 : Cover gdata (896) (1024) (1024) (2048) := by
  ballooning_cover "Q:cn02_48,cn02_50,cn02_49,cn02_51"

/-- Kernel-checked box `[1024, 1152]/NT × [1024, 2048]/NS`. -/
theorem cov129 : Cover gdata (1024) (1152) (1024) (2048) := by
  ballooning_cover "Q:cn02_50,cn02_52,cn02_51,cn02_53"

/-- Kernel-checked box `[1152, 1280]/NT × [1024, 2048]/NS`. -/
theorem cov130 : Cover gdata (1152) (1280) (1024) (2048) := by
  ballooning_cover "Q:cn02_52,cn02_54,cn02_53,cn02_55"

/-- Kernel-checked box `[1280, 1408]/NT × [1024, 2048]/NS`. -/
theorem cov131 : Cover gdata (1280) (1408) (1024) (2048) := by
  ballooning_cover "Q:cn02_54,cn02_56,cn02_55,cn02_57"

/-- Kernel-checked box `[1408, 1536]/NT × [1024, 2048]/NS`. -/
theorem cov132 : Cover gdata (1408) (1536) (1024) (2048) := by
  ballooning_cover "Q:cn02_56,cn02_58,cn02_57,cn02_59"

/-- Kernel-checked box `[1536, 1664]/NT × [1024, 2048]/NS`. -/
theorem cov133 : Cover gdata (1536) (1664) (1024) (2048) := by
  ballooning_cover "Q:cn02_58,cn02_60,cn02_59,cn02_61"

/-- Kernel-checked box `[1664, 1792]/NT × [1024, 2048]/NS`. -/
theorem cov134 : Cover gdata (1664) (1792) (1024) (2048) := by
  ballooning_cover "Q:cn02_60,cn02_62,cn02_61,cn02_63"

/-- Kernel-checked box `[1792, 1920]/NT × [1024, 2048]/NS`. -/
theorem cov135 : Cover gdata (1792) (1920) (1024) (2048) := by
  ballooning_cover "Q:cn02_62,cn02_64,cn02_63,cn02_65"

/-- Kernel-checked box `[1920, 2048]/NT × [1024, 2048]/NS`. -/
theorem cov136 : Cover gdata (1920) (2048) (1024) (2048) := by
  ballooning_cover "Q:cn02_64,cn02_66,cn02_65,cn02_67"

/-- Kernel-checked box `[2048, 2176]/NT × [1024, 2048]/NS`. -/
theorem cov137 : Cover gdata (2048) (2176) (1024) (2048) := by
  ballooning_cover "Q:cn02_66,cn02_68,cn02_67,cn02_69"

/-- Kernel-checked box `[2176, 2304]/NT × [1024, 2048]/NS`. -/
theorem cov138 : Cover gdata (2176) (2304) (1024) (2048) := by
  ballooning_cover "Q:cn02_68,cn02_70,cn02_69,cn02_71"

/-- Kernel-checked box `[2304, 2432]/NT × [1024, 2048]/NS`. -/
theorem cov139 : Cover gdata (2304) (2432) (1024) (2048) := by
  ballooning_cover "Q:cn02_70,cn02_72,cn02_71,cn02_73"

/-- Kernel-checked box `[2432, 2560]/NT × [1024, 2048]/NS`. -/
theorem cov140 : Cover gdata (2432) (2560) (1024) (2048) := by
  ballooning_cover "Q:cn02_72,cn02_74,cn02_73,cn02_75"

/-- Kernel-checked box `[2560, 2688]/NT × [1024, 2048]/NS`. -/
theorem cov141 : Cover gdata (2560) (2688) (1024) (2048) := by
  ballooning_cover "Q:cn02_74,cn02_76,cn02_75,cn02_77"

/-- Kernel-checked box `[2688, 2816]/NT × [1024, 2048]/NS`. -/
theorem cov142 : Cover gdata (2688) (2816) (1024) (2048) := by
  ballooning_cover "Q:cn02_76,cn02_78,cn02_77,cn02_79"

/-- Kernel-checked box `[2816, 2944]/NT × [1024, 2048]/NS`. -/
theorem cov143 : Cover gdata (2816) (2944) (1024) (2048) := by
  ballooning_cover "Q:cn02_78,cn02_80,cn02_79,cn02_81"

/-- Kernel-checked box `[2944, 3072]/NT × [1024, 2048]/NS`. -/
theorem cov144 : Cover gdata (2944) (3072) (1024) (2048) := by
  ballooning_cover "Q:cn02_80,cn02_82,cn02_81,cn02_83"

/-- Kernel-checked box `[3072, 3328]/NT × [1024, 2048]/NS`. -/
theorem cov145 : Cover gdata (3072) (3328) (1024) (2048) := by
  ballooning_cover "Q:cn02_82,cn02_84,cn02_83,cn02_85"

/-- Kernel-checked box `[3328, 3584]/NT × [1024, 2048]/NS`. -/
theorem cov146 : Cover gdata (3328) (3584) (1024) (2048) := by
  ballooning_cover "Q:cn02_84,cn02_86,cn02_85,cn02_87"

/-- Kernel-checked box `[3584, 3840]/NT × [1024, 2048]/NS`. -/
theorem cov147 : Cover gdata (3584) (3840) (1024) (2048) := by
  ballooning_cover "Q:cn02_86,cn02_88,cn02_87,cn02_89"

/-- Kernel-checked box `[3840, 4096]/NT × [1024, 2048]/NS`. -/
theorem cov148 : Cover gdata (3840) (4096) (1024) (2048) := by
  ballooning_cover "Q:cn02_88,cn02_90,cn02_89,cn02_91"

/-- Kernel-checked box `[-4096, -3840]/NT × [2048, 3072]/NS`. -/
theorem cov149 : Cover gdata (-4096) (-3840) (2048) (3072) := by
  ballooning_cover "Q:cn02_92,cn02_93,cn02_94,cn02_95"

/-- Kernel-checked box `[-4096, -3840]/NT × [3072, 4096]/NS`. -/
theorem cov150 : Cover gdata (-4096) (-3840) (3072) (4096) := by
  ballooning_cover "Q:cn02_94,cn02_95,cn02_96,cn02_97"

/-- Kernel-checked box `[-3840, -3584]/NT × [2048, 3072]/NS`. -/
theorem cov151 : Cover gdata (-3840) (-3584) (2048) (3072) := by
  ballooning_cover "Q:cn02_93,cn02_98,cn02_95,cn02_99"

/-- Kernel-checked box `[-3840, -3584]/NT × [3072, 4096]/NS`. -/
theorem cov152 : Cover gdata (-3840) (-3584) (3072) (4096) := by
  ballooning_cover "Q:cn02_95,cn02_99,cn02_97,cn02_100"

/-- Kernel-checked box `[-3584, -3328]/NT × [2048, 3072]/NS`. -/
theorem cov153 : Cover gdata (-3584) (-3328) (2048) (3072) := by
  ballooning_cover "Q:cn02_98,cn02_101,cn02_99,cn02_102"

/-- Kernel-checked box `[-3584, -3328]/NT × [3072, 4096]/NS`. -/
theorem cov154 : Cover gdata (-3584) (-3328) (3072) (4096) := by
  ballooning_cover "Q:cn02_99,cn02_102,cn02_100,cn02_103"

end PlasmaLean.Design.SolovevBallooning
