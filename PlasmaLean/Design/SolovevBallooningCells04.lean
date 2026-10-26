/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 4

51 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (evaluation certificate `ballooning_box`: one kernel leaf per ball
operation) and refers to its corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(2944/NT, 2048/NS)`. -/
theorem cn04_0 : cornerOK gdata (2944) (2048)
    [152797895, 74274883, 149192879, 37705734, 42807938, 4464915, 4203194] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 2048/NS)`. -/
theorem cn04_1 : cornerOK gdata (3072) (2048)
    [152797895, 74274883, 149745786, 37705734, 43382958, 4464915, 4302996] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 4096/NS)`. -/
theorem cn04_2 : cornerOK gdata (2944) (4096)
    [152797895, 74274883, 149192879, 37705734, 42807938, 4464915, 4203194] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 4096/NS)`. -/
theorem cn04_3 : cornerOK gdata (3072) (4096)
    [152797895, 74274883, 149745786, 37705734, 43382958, 4464915, 4302996] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3200/NT, 2048/NS)`. -/
theorem cn04_4 : cornerOK gdata (3200) (2048)
    [151109810, 67264055, 149844267, 34288351, 43769004, 4065498, 4379849] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3200/NT, 4096/NS)`. -/
theorem cn04_5 : cornerOK gdata (3200) (4096)
    [151109810, 67264055, 149844267, 34288351, 43769004, 4065498, 4379849] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 2048/NS)`. -/
theorem cn04_6 : cornerOK gdata (3328) (2048)
    [149231172, 59895037, 149844267, 30648713, 43961642, 3639948, 4432891] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 4096/NS)`. -/
theorem cn04_7 : cornerOK gdata (3328) (4096)
    [149231172, 59895037, 149844267, 30648713, 43961642, 3639948, 4432891] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3456/NT, 2048/NS)`. -/
theorem cn04_8 : cornerOK gdata (3456) (2048)
    [147099055, 52547807, 149442015, 26968315, 43974228, 3208819, 4463336] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3456/NT, 4096/NS)`. -/
theorem cn04_9 : cornerOK gdata (3456) (4096)
    [147099055, 52547807, 149442015, 26968315, 43974228, 3208819, 4463336] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 2048/NS)`. -/
theorem cn04_10 : cornerOK gdata (3584) (2048)
    [144831274, 45221030, 148607873, 23265472, 43974228, 2775737, 4476240] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 4096/NS)`. -/
theorem cn04_11 : cornerOK gdata (3584) (4096)
    [144831274, 45221030, 148607873, 23265472, 43974228, 2775737, 4476240] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3712/NT, 2048/NS)`. -/
theorem cn04_12 : cornerOK gdata (3712) (2048)
    [142466875, 37897724, 147375097, 19535307, 43856851, 2339477, 4476240] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3712/NT, 4096/NS)`. -/
theorem cn04_13 : cornerOK gdata (3712) (4096)
    [142466875, 37897724, 147375097, 19535307, 43856851, 2339477, 4476240] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 2048/NS)`. -/
theorem cn04_14 : cornerOK gdata (3840) (2048)
    [140095564, 30655529, 145855923, 15822020, 43566181, 1905175, 4467220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 4096/NS)`. -/
theorem cn04_15 : cornerOK gdata (3840) (4096)
    [140095564, 30655529, 145855923, 15822020, 43566181, 1905175, 4467220] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3968/NT, 2048/NS)`. -/
theorem cn04_16 : cornerOK gdata (3968) (2048)
    [137739844, 23654575, 144078814, 12175355, 43165776, 1479834, 4442809] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3968/NT, 4096/NS)`. -/
theorem cn04_17 : cornerOK gdata (3968) (4096)
    [137739844, 23654575, 144078814, 12175355, 43165776, 1479834, 4442809] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 2048/NS)`. -/
theorem cn04_18 : cornerOK gdata (4096) (2048)
    [135365651, 16928408, 142034747, 8635571, 42642759, 1071484, 4402015] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 4096/NS)`. -/
theorem cn04_19 : cornerOK gdata (4096) (4096)
    [135365651, 16928408, 142034747, 8635571, 42642759, 1071484, 4402015] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 4096/NS)`. -/
theorem cn04_20 : cornerOK gdata (-4096) (4096)
    [150669385, 44472039, 116571459, 20127447, 30520628, 2508265, 2552154] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 4096/NS)`. -/
theorem cn04_21 : cornerOK gdata (-3840) (4096)
    [170011084, 65051864, 130914367, 29216494, 33741277, 3550392, 2761307] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 5120/NS)`. -/
theorem cn04_22 : cornerOK gdata (-4096) (5120)
    [184129082, 53275570, 136976686, 23735596, 34747538, 2927087, 2808106] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 5120/NS)`. -/
theorem cn04_23 : cornerOK gdata (-3840) (5120)
    [208489938, 78112617, 154494142, 34617560, 38623494, 4173878, 3050690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 6144/NS)`. -/
theorem cn04_24 : cornerOK gdata (-4096) (6144)
    [184129082, 53275570, 136976686, 23735596, 34747538, 2927087, 2808106] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 6144/NS)`. -/
theorem cn04_25 : cornerOK gdata (-3840) (6144)
    [208489938, 78112617, 154494142, 34617560, 38623494, 4173878, 3050690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 4096/NS)`. -/
theorem cn04_26 : cornerOK gdata (-3584) (4096)
    [192291150, 89859691, 146715370, 39406752, 37035659, 4812936, 2960777] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 5120/NS)`. -/
theorem cn04_27 : cornerOK gdata (-3584) (5120)
    [236642787, 108624445, 174011003, 47072440, 42650073, 5684369, 3285295] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 6144/NS)`. -/
theorem cn04_28 : cornerOK gdata (-3584) (6144)
    [236642787, 108624445, 174011003, 47072440, 42650073, 5684369, 3285295] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 4096/NS)`. -/
theorem cn04_29 : cornerOK gdata (-3328) (4096)
    [217120412, 121986206, 163825229, 52750684, 40348592, 6457442, 3139049] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 5120/NS)`. -/
theorem cn04_30 : cornerOK gdata (-3328) (5120)
    [267974514, 148137197, 195279519, 63412036, 46775597, 7665187, 3499796] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 6144/NS)`. -/
theorem cn04_31 : cornerOK gdata (-3328) (6144)
    [267974514, 148137197, 195279519, 63412036, 46775597, 7665187, 3499796] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 4096/NS)`. -/
theorem cn04_32 : cornerOK gdata (-3072) (4096)
    [243423182, 155828436, 181238641, 66623072, 43374928, 8166476, 3279763] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 5120/NS)`. -/
theorem cn04_33 : cornerOK gdata (-3072) (5120)
    [301316466, 189622392, 217287821, 80306466, 50653149, 9713069, 3677952] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 6144/NS)`. -/
theorem cn04_34 : cornerOK gdata (-3072) (6144)
    [301316466, 189622392, 217287821, 80306466, 50653149, 9713069, 3677952] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 4096/NS)`. -/
theorem cn04_35 : cornerOK gdata (-2816) (4096)
    [269953193, 187737802, 197427236, 79518562, 45811924, 9746661, 3366568] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 5120/NS)`. -/
theorem cn04_36 : cornerOK gdata (-2816) (5120)
    [334456228, 228940563, 237987987, 96032364, 53859381, 11612971, 3797718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 6144/NS)`. -/
theorem cn04_37 : cornerOK gdata (-2816) (6144)
    [334456228, 228940563, 237987987, 96032364, 53859381, 11612971, 3797718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 4096/NS)`. -/
theorem cn04_38 : cornerOK gdata (-2560) (4096)
    [393498786, 223919427, 269079934, 94846488, 63480357, 10800480, 4948048] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 5120/NS)`. -/
theorem cn04_39 : cornerOK gdata (-2560) (5120)
    [334456228, 228940563, 237987987, 96032364, 53859381, 11612971, 3797718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 6144/NS)`. -/
theorem cn04_40 : cornerOK gdata (-2560) (6144)
    [393498786, 228940563, 269079934, 96032364, 63480357, 11612971, 4948048] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 4096/NS)`. -/
theorem cn04_41 : cornerOK gdata (-2432) (4096)
    [393498786, 226118783, 269079934, 95036281, 63480357, 10804055, 4948048] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 6144/NS)`. -/
theorem cn04_42 : cornerOK gdata (-2432) (6144)
    [393498786, 226118783, 269079934, 95036281, 63480357, 10804055, 4948048] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 4096/NS)`. -/
theorem cn04_43 : cornerOK gdata (-2304) (4096)
    [383725007, 226118783, 260342616, 95036281, 60563866, 10804055, 4582638] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 6144/NS)`. -/
theorem cn04_44 : cornerOK gdata (-2304) (6144)
    [383725007, 226118783, 260342616, 95036281, 60563866, 10804055, 4582638] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 4096/NS)`. -/
theorem cn04_45 : cornerOK gdata (-2176) (4096)
    [371279054, 224912864, 250064584, 93774582, 57320858, 10639938, 4203002] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 6144/NS)`. -/
theorem cn04_46 : cornerOK gdata (-2176) (6144)
    [371279054, 224912864, 250064584, 93774582, 57320858, 10639938, 4203002] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 4096/NS)`. -/
theorem cn04_47 : cornerOK gdata (-2048) (4096)
    [355735414, 220028594, 237988281, 91001675, 53722421, 10302012, 3811436] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 6144/NS)`. -/
theorem cn04_48 : cornerOK gdata (-2048) (6144)
    [355735414, 220028594, 237988281, 91001675, 53722421, 10302012, 3811436] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 4096/NS)`. -/
theorem cn04_49 : cornerOK gdata (-1920) (4096)
    [337272780, 211552758, 224267984, 86811082, 49829276, 9800144, 3414966] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 6144/NS)`. -/
theorem cn04_50 : cornerOK gdata (-1920) (6144)
    [337272780, 211552758, 224267984, 86811082, 49829276, 9800144, 3414966] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 4096/NS)`. -/
theorem cn04_51 : cornerOK gdata (-1792) (4096)
    [316003941, 199744915, 208937175, 81602475, 45671093, 9153762, 3019838] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 6144/NS)`. -/
theorem cn04_52 : cornerOK gdata (-1792) (6144)
    [316003941, 199744915, 208937175, 81602475, 45671093, 9153762, 3019838] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 4096/NS)`. -/
theorem cn04_53 : cornerOK gdata (-1664) (4096)
    [292971440, 186857317, 192794785, 76133825, 41431944, 8470567, 2634540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 6144/NS)`. -/
theorem cn04_54 : cornerOK gdata (-1664) (6144)
    [292971440, 186857317, 192794785, 76133825, 41431944, 8470567, 2634540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 4096/NS)`. -/
theorem cn04_55 : cornerOK gdata (-1536) (4096)
    [269147488, 174478441, 176666978, 70359807, 37294527, 7761153, 2315225] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 6144/NS)`. -/
theorem cn04_56 : cornerOK gdata (-1536) (6144)
    [269147488, 174478441, 176666978, 70359807, 37294527, 7761153, 2315225] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 4096/NS)`. -/
theorem cn04_57 : cornerOK gdata (-1408) (4096)
    [243893735, 161103061, 159993720, 64128560, 33169576, 7077662, 2017698] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 6144/NS)`. -/
theorem cn04_58 : cornerOK gdata (-1408) (6144)
    [243893735, 161103061, 159993720, 64128560, 33169576, 7077662, 2017698] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 4096/NS)`. -/
theorem cn04_59 : cornerOK gdata (-1280) (4096)
    [217765673, 146636045, 142876320, 57636325, 29099657, 6370541, 1742040] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 6144/NS)`. -/
theorem cn04_60 : cornerOK gdata (-1280) (6144)
    [217765673, 146636045, 142876320, 57636325, 29099657, 6370541, 1742040] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 4096/NS)`. -/
theorem cn04_61 : cornerOK gdata (-1152) (4096)
    [191569081, 131318860, 125719623, 51016121, 25165746, 5652166, 1490313] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 6144/NS)`. -/
theorem cn04_62 : cornerOK gdata (-1152) (6144)
    [191569081, 131318860, 125719623, 51016121, 25165746, 5652166, 1490313] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 4096/NS)`. -/
theorem cn04_63 : cornerOK gdata (-1024) (4096)
    [165808005, 115573200, 108794892, 44393096, 21412351, 4932872, 1261321] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 6144/NS)`. -/
theorem cn04_64 : cornerOK gdata (-1024) (6144)
    [165808005, 115573200, 108794892, 44393096, 21412351, 4932872, 1261321] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 4096/NS)`. -/
theorem cn04_65 : cornerOK gdata (-896) (4096)
    [143252664, 99910484, 92625986, 37945903, 17924032, 4226611, 1055898] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 6144/NS)`. -/
theorem cn04_66 : cornerOK gdata (-896) (6144)
    [143252664, 99910484, 92625986, 37945903, 17924032, 4226611, 1055898] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 4096/NS)`. -/
theorem cn04_67 : cornerOK gdata (-768) (4096)
    [386989482, 263730786, 244439171, 103400638, 47672954, 11826574, 2618260] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 6144/NS)`. -/
theorem cn04_68 : cornerOK gdata (-768) (6144)
    [386989482, 263730786, 244439171, 103400638, 47672954, 11826574, 2618260] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 4096/NS)`. -/
theorem cn04_69 : cornerOK gdata (-512) (4096)
    [386989482, 263730786, 244439171, 103400638, 47672954, 11826574, 2618260] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 6144/NS)`. -/
theorem cn04_70 : cornerOK gdata (-512) (6144)
    [386989482, 263730786, 244439171, 103400638, 47672954, 11826574, 2618260] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 4096/NS)`. -/
theorem cn04_71 : cornerOK gdata (-256) (4096)
    [278048765, 173104804, 175243469, 68044483, 34463176, 7665535, 1901730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 6144/NS)`. -/
theorem cn04_72 : cornerOK gdata (-256) (6144)
    [278048765, 173104804, 175243469, 68044483, 34463176, 7665535, 1901730] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 4096/NS)`. -/
theorem cn04_73 : cornerOK gdata (0) (4096)
    [203571543, 121396147, 132371563, 48557187, 26362990, 5326664, 1509719] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 6144/NS)`. -/
theorem cn04_74 : cornerOK gdata (0) (6144)
    [203571543, 121396147, 132371563, 48557187, 26362990, 5326664, 1509719] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 4096/NS)`. -/
theorem cn04_75 : cornerOK gdata (256) (4096)
    [257197720, 181652478, 176301404, 71982422, 35789051, 8171827, 2140297] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 6144/NS)`. -/
theorem cn04_76 : cornerOK gdata (256) (6144)
    [257197720, 181652478, 176301404, 71982422, 35789051, 8171827, 2140297] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 4096/NS)`. -/
theorem cn04_77 : cornerOK gdata (512) (4096)
    [257197720, 181652478, 176301404, 71982422, 35789051, 8171827, 2140297] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 6144/NS)`. -/
theorem cn04_78 : cornerOK gdata (512) (6144)
    [257197720, 181652478, 176301404, 71982422, 35789051, 8171827, 2140297] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 4096/NS)`. -/
theorem cn04_79 : cornerOK gdata (640) (4096)
    [81309580, 55938801, 53159720, 21785233, 10954544, 2528540, 726101] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 6144/NS)`. -/
theorem cn04_80 : cornerOK gdata (640) (6144)
    [81309580, 55938801, 53159720, 21785233, 10954544, 2528540, 726101] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 4096/NS)`. -/
theorem cn04_81 : cornerOK gdata (768) (4096)
    [89933170, 62537603, 60188962, 25412545, 12927754, 2949563, 877050] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 6144/NS)`. -/
theorem cn04_82 : cornerOK gdata (768) (6144)
    [89933170, 62537603, 60188962, 25412545, 12927754, 2949563, 877050] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 4096/NS)`. -/
theorem cn04_83 : cornerOK gdata (896) (4096)
    [98264593, 69191340, 68448492, 29038944, 15045685, 3364029, 1039610] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 6144/NS)`. -/
theorem cn04_84 : cornerOK gdata (896) (6144)
    [98264593, 69191340, 68448492, 29038944, 15045685, 3364029, 1039610] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 4096/NS)`. -/
theorem cn04_85 : cornerOK gdata (1024) (4096)
    [106282849, 75364056, 76624639, 32577303, 17221298, 3763697, 1212902] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 6144/NS)`. -/
theorem cn04_86 : cornerOK gdata (1024) (6144)
    [106282849, 75364056, 76624639, 32577303, 17221298, 3763697, 1212902] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 4096/NS)`. -/
theorem cn04_87 : cornerOK gdata (1152) (4096)
    [113860585, 80889060, 84514038, 35932167, 19427840, 4139638, 1395847] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 6144/NS)`. -/
theorem cn04_88 : cornerOK gdata (1152) (6144)
    [113860585, 80889060, 84514038, 35932167, 19427840, 4139638, 1395847] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 4096/NS)`. -/
theorem cn04_89 : cornerOK gdata (1280) (4096)
    [121269261, 85714854, 92579229, 39033635, 21682626, 4484014, 1589508] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 6144/NS)`. -/
theorem cn04_90 : cornerOK gdata (1280) (6144)
    [121269261, 85714854, 92579229, 39033635, 21682626, 4484014, 1589508] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 4096/NS)`. -/
theorem cn04_91 : cornerOK gdata (1408) (4096)
    [127938394, 89882989, 100562118, 41886206, 24024163, 4801618, 1820141] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 6144/NS)`. -/
theorem cn04_92 : cornerOK gdata (1408) (6144)
    [127938394, 89882989, 100562118, 41886206, 24024163, 4801618, 1820141] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 4096/NS)`. -/
theorem cn04_93 : cornerOK gdata (1536) (4096)
    [133583076, 94118047, 108053760, 44534311, 26340520, 5123779, 2081350] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 6144/NS)`. -/
theorem cn04_94 : cornerOK gdata (1536) (6144)
    [133583076, 94118047, 108053760, 44534311, 26340520, 5123779, 2081350] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 4096/NS)`. -/
theorem cn04_95 : cornerOK gdata (1664) (4096)
    [138091894, 98822390, 115093669, 47181803, 28641773, 5476948, 2346710] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 6144/NS)`. -/
theorem cn04_96 : cornerOK gdata (1664) (6144)
    [138091894, 98822390, 115093669, 47181803, 28641773, 5476948, 2346710] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 4096/NS)`. -/
theorem cn04_97 : cornerOK gdata (1792) (4096)
    [141513082, 102167325, 121374811, 49241452, 30959202, 5749730, 2613004] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 6144/NS)`. -/
theorem cn04_98 : cornerOK gdata (1792) (6144)
    [141513082, 102167325, 121374811, 49241452, 30959202, 5749730, 2613004] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 4096/NS)`. -/
theorem cn04_99 : cornerOK gdata (1920) (4096)
    [141513082, 102167325, 121374811, 49241452, 30959202, 5749730, 2613004] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 6144/NS)`. -/
theorem cn04_100 : cornerOK gdata (1920) (6144)
    [141513082, 102167325, 121374811, 49241452, 30959202, 5749730, 2613004] = true := by
  bl_cert

/-- Kernel-checked box `[2944, 3072]/NT × [2048, 4096]/NS`. -/
theorem cov207 : Cover gdata (2944) (3072) (2048) (4096) := by
  ballooning_box "Q:cn04_0,cn04_1,cn04_2,cn04_3"

/-- Kernel-checked box `[3072, 3200]/NT × [2048, 4096]/NS`. -/
theorem cov208 : Cover gdata (3072) (3200) (2048) (4096) := by
  ballooning_box "Q:cn04_1,cn04_4,cn04_3,cn04_5"

/-- Kernel-checked box `[3200, 3328]/NT × [2048, 4096]/NS`. -/
theorem cov209 : Cover gdata (3200) (3328) (2048) (4096) := by
  ballooning_box "Q:cn04_4,cn04_6,cn04_5,cn04_7"

/-- Kernel-checked box `[3328, 3456]/NT × [2048, 4096]/NS`. -/
theorem cov210 : Cover gdata (3328) (3456) (2048) (4096) := by
  ballooning_box "Q:cn04_6,cn04_8,cn04_7,cn04_9"

/-- Kernel-checked box `[3456, 3584]/NT × [2048, 4096]/NS`. -/
theorem cov211 : Cover gdata (3456) (3584) (2048) (4096) := by
  ballooning_box "Q:cn04_8,cn04_10,cn04_9,cn04_11"

/-- Kernel-checked box `[3584, 3712]/NT × [2048, 4096]/NS`. -/
theorem cov212 : Cover gdata (3584) (3712) (2048) (4096) := by
  ballooning_box "Q:cn04_10,cn04_12,cn04_11,cn04_13"

/-- Kernel-checked box `[3712, 3840]/NT × [2048, 4096]/NS`. -/
theorem cov213 : Cover gdata (3712) (3840) (2048) (4096) := by
  ballooning_box "Q:cn04_12,cn04_14,cn04_13,cn04_15"

/-- Kernel-checked box `[3840, 3968]/NT × [2048, 4096]/NS`. -/
theorem cov214 : Cover gdata (3840) (3968) (2048) (4096) := by
  ballooning_box "Q:cn04_14,cn04_16,cn04_15,cn04_17"

/-- Kernel-checked box `[3968, 4096]/NT × [2048, 4096]/NS`. -/
theorem cov215 : Cover gdata (3968) (4096) (2048) (4096) := by
  ballooning_box "Q:cn04_16,cn04_18,cn04_17,cn04_19"

/-- Kernel-checked box `[-4096, -3840]/NT × [4096, 5120]/NS`. -/
theorem cov216 : Cover gdata (-4096) (-3840) (4096) (5120) := by
  ballooning_box "Q:cn04_20,cn04_21,cn04_22,cn04_23"

/-- Kernel-checked box `[-4096, -3840]/NT × [5120, 6144]/NS`. -/
theorem cov217 : Cover gdata (-4096) (-3840) (5120) (6144) := by
  ballooning_box "Q:cn04_22,cn04_23,cn04_24,cn04_25"

/-- Kernel-checked box `[-3840, -3584]/NT × [4096, 5120]/NS`. -/
theorem cov218 : Cover gdata (-3840) (-3584) (4096) (5120) := by
  ballooning_box "Q:cn04_21,cn04_26,cn04_23,cn04_27"

/-- Kernel-checked box `[-3840, -3584]/NT × [5120, 6144]/NS`. -/
theorem cov219 : Cover gdata (-3840) (-3584) (5120) (6144) := by
  ballooning_box "Q:cn04_23,cn04_27,cn04_25,cn04_28"

/-- Kernel-checked box `[-3584, -3328]/NT × [4096, 5120]/NS`. -/
theorem cov220 : Cover gdata (-3584) (-3328) (4096) (5120) := by
  ballooning_box "Q:cn04_26,cn04_29,cn04_27,cn04_30"

/-- Kernel-checked box `[-3584, -3328]/NT × [5120, 6144]/NS`. -/
theorem cov221 : Cover gdata (-3584) (-3328) (5120) (6144) := by
  ballooning_box "Q:cn04_27,cn04_30,cn04_28,cn04_31"

/-- Kernel-checked box `[-3328, -3072]/NT × [4096, 5120]/NS`. -/
theorem cov222 : Cover gdata (-3328) (-3072) (4096) (5120) := by
  ballooning_box "Q:cn04_29,cn04_32,cn04_30,cn04_33"

/-- Kernel-checked box `[-3328, -3072]/NT × [5120, 6144]/NS`. -/
theorem cov223 : Cover gdata (-3328) (-3072) (5120) (6144) := by
  ballooning_box "Q:cn04_30,cn04_33,cn04_31,cn04_34"

/-- Kernel-checked box `[-3072, -2816]/NT × [4096, 5120]/NS`. -/
theorem cov224 : Cover gdata (-3072) (-2816) (4096) (5120) := by
  ballooning_box "Q:cn04_32,cn04_35,cn04_33,cn04_36"

/-- Kernel-checked box `[-3072, -2816]/NT × [5120, 6144]/NS`. -/
theorem cov225 : Cover gdata (-3072) (-2816) (5120) (6144) := by
  ballooning_box "Q:cn04_33,cn04_36,cn04_34,cn04_37"

/-- Kernel-checked box `[-2816, -2560]/NT × [4096, 5120]/NS`. -/
theorem cov226 : Cover gdata (-2816) (-2560) (4096) (5120) := by
  ballooning_box "Q:cn04_35,cn04_38,cn04_36,cn04_39"

/-- Kernel-checked box `[-2816, -2560]/NT × [5120, 6144]/NS`. -/
theorem cov227 : Cover gdata (-2816) (-2560) (5120) (6144) := by
  ballooning_box "Q:cn04_36,cn04_39,cn04_37,cn04_40"

/-- Kernel-checked box `[-2560, -2432]/NT × [4096, 6144]/NS`. -/
theorem cov228 : Cover gdata (-2560) (-2432) (4096) (6144) := by
  ballooning_box "Q:cn04_38,cn04_41,cn04_40,cn04_42"

/-- Kernel-checked box `[-2432, -2304]/NT × [4096, 6144]/NS`. -/
theorem cov229 : Cover gdata (-2432) (-2304) (4096) (6144) := by
  ballooning_box "Q:cn04_41,cn04_43,cn04_42,cn04_44"

/-- Kernel-checked box `[-2304, -2176]/NT × [4096, 6144]/NS`. -/
theorem cov230 : Cover gdata (-2304) (-2176) (4096) (6144) := by
  ballooning_box "Q:cn04_43,cn04_45,cn04_44,cn04_46"

/-- Kernel-checked box `[-2176, -2048]/NT × [4096, 6144]/NS`. -/
theorem cov231 : Cover gdata (-2176) (-2048) (4096) (6144) := by
  ballooning_box "Q:cn04_45,cn04_47,cn04_46,cn04_48"

/-- Kernel-checked box `[-2048, -1920]/NT × [4096, 6144]/NS`. -/
theorem cov232 : Cover gdata (-2048) (-1920) (4096) (6144) := by
  ballooning_box "Q:cn04_47,cn04_49,cn04_48,cn04_50"

/-- Kernel-checked box `[-1920, -1792]/NT × [4096, 6144]/NS`. -/
theorem cov233 : Cover gdata (-1920) (-1792) (4096) (6144) := by
  ballooning_box "Q:cn04_49,cn04_51,cn04_50,cn04_52"

/-- Kernel-checked box `[-1792, -1664]/NT × [4096, 6144]/NS`. -/
theorem cov234 : Cover gdata (-1792) (-1664) (4096) (6144) := by
  ballooning_box "Q:cn04_51,cn04_53,cn04_52,cn04_54"

/-- Kernel-checked box `[-1664, -1536]/NT × [4096, 6144]/NS`. -/
theorem cov235 : Cover gdata (-1664) (-1536) (4096) (6144) := by
  ballooning_box "Q:cn04_53,cn04_55,cn04_54,cn04_56"

/-- Kernel-checked box `[-1536, -1408]/NT × [4096, 6144]/NS`. -/
theorem cov236 : Cover gdata (-1536) (-1408) (4096) (6144) := by
  ballooning_box "Q:cn04_55,cn04_57,cn04_56,cn04_58"

/-- Kernel-checked box `[-1408, -1280]/NT × [4096, 6144]/NS`. -/
theorem cov237 : Cover gdata (-1408) (-1280) (4096) (6144) := by
  ballooning_box "Q:cn04_57,cn04_59,cn04_58,cn04_60"

/-- Kernel-checked box `[-1280, -1152]/NT × [4096, 6144]/NS`. -/
theorem cov238 : Cover gdata (-1280) (-1152) (4096) (6144) := by
  ballooning_box "Q:cn04_59,cn04_61,cn04_60,cn04_62"

/-- Kernel-checked box `[-1152, -1024]/NT × [4096, 6144]/NS`. -/
theorem cov239 : Cover gdata (-1152) (-1024) (4096) (6144) := by
  ballooning_box "Q:cn04_61,cn04_63,cn04_62,cn04_64"

/-- Kernel-checked box `[-1024, -896]/NT × [4096, 6144]/NS`. -/
theorem cov240 : Cover gdata (-1024) (-896) (4096) (6144) := by
  ballooning_box "Q:cn04_63,cn04_65,cn04_64,cn04_66"

/-- Kernel-checked box `[-896, -768]/NT × [4096, 6144]/NS`. -/
theorem cov241 : Cover gdata (-896) (-768) (4096) (6144) := by
  ballooning_box "Q:cn04_65,cn04_67,cn04_66,cn04_68"

/-- Kernel-checked box `[-768, -512]/NT × [4096, 6144]/NS`. -/
theorem cov242 : Cover gdata (-768) (-512) (4096) (6144) := by
  ballooning_box "Q:cn04_67,cn04_69,cn04_68,cn04_70"

/-- Kernel-checked box `[-512, -256]/NT × [4096, 6144]/NS`. -/
theorem cov243 : Cover gdata (-512) (-256) (4096) (6144) := by
  ballooning_box "Q:cn04_69,cn04_71,cn04_70,cn04_72"

/-- Kernel-checked box `[-256, 0]/NT × [4096, 6144]/NS`. -/
theorem cov244 : Cover gdata (-256) (0) (4096) (6144) := by
  ballooning_box "Q:cn04_71,cn04_73,cn04_72,cn04_74"

/-- Kernel-checked box `[0, 256]/NT × [4096, 6144]/NS`. -/
theorem cov245 : Cover gdata (0) (256) (4096) (6144) := by
  ballooning_box "Q:cn04_73,cn04_75,cn04_74,cn04_76"

/-- Kernel-checked box `[256, 512]/NT × [4096, 6144]/NS`. -/
theorem cov246 : Cover gdata (256) (512) (4096) (6144) := by
  ballooning_box "Q:cn04_75,cn04_77,cn04_76,cn04_78"

/-- Kernel-checked box `[512, 640]/NT × [4096, 6144]/NS`. -/
theorem cov247 : Cover gdata (512) (640) (4096) (6144) := by
  ballooning_box "Q:cn04_77,cn04_79,cn04_78,cn04_80"

/-- Kernel-checked box `[640, 768]/NT × [4096, 6144]/NS`. -/
theorem cov248 : Cover gdata (640) (768) (4096) (6144) := by
  ballooning_box "Q:cn04_79,cn04_81,cn04_80,cn04_82"

/-- Kernel-checked box `[768, 896]/NT × [4096, 6144]/NS`. -/
theorem cov249 : Cover gdata (768) (896) (4096) (6144) := by
  ballooning_box "Q:cn04_81,cn04_83,cn04_82,cn04_84"

/-- Kernel-checked box `[896, 1024]/NT × [4096, 6144]/NS`. -/
theorem cov250 : Cover gdata (896) (1024) (4096) (6144) := by
  ballooning_box "Q:cn04_83,cn04_85,cn04_84,cn04_86"

/-- Kernel-checked box `[1024, 1152]/NT × [4096, 6144]/NS`. -/
theorem cov251 : Cover gdata (1024) (1152) (4096) (6144) := by
  ballooning_box "Q:cn04_85,cn04_87,cn04_86,cn04_88"

/-- Kernel-checked box `[1152, 1280]/NT × [4096, 6144]/NS`. -/
theorem cov252 : Cover gdata (1152) (1280) (4096) (6144) := by
  ballooning_box "Q:cn04_87,cn04_89,cn04_88,cn04_90"

/-- Kernel-checked box `[1280, 1408]/NT × [4096, 6144]/NS`. -/
theorem cov253 : Cover gdata (1280) (1408) (4096) (6144) := by
  ballooning_box "Q:cn04_89,cn04_91,cn04_90,cn04_92"

/-- Kernel-checked box `[1408, 1536]/NT × [4096, 6144]/NS`. -/
theorem cov254 : Cover gdata (1408) (1536) (4096) (6144) := by
  ballooning_box "Q:cn04_91,cn04_93,cn04_92,cn04_94"

/-- Kernel-checked box `[1536, 1664]/NT × [4096, 6144]/NS`. -/
theorem cov255 : Cover gdata (1536) (1664) (4096) (6144) := by
  ballooning_box "Q:cn04_93,cn04_95,cn04_94,cn04_96"

/-- Kernel-checked box `[1664, 1792]/NT × [4096, 6144]/NS`. -/
theorem cov256 : Cover gdata (1664) (1792) (4096) (6144) := by
  ballooning_box "Q:cn04_95,cn04_97,cn04_96,cn04_98"

/-- Kernel-checked box `[1792, 1920]/NT × [4096, 6144]/NS`. -/
theorem cov257 : Cover gdata (1792) (1920) (4096) (6144) := by
  ballooning_box "Q:cn04_97,cn04_99,cn04_98,cn04_100"

end PlasmaLean.Design.SolovevBallooning
