/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningData

/-!
# Ballooning certificate: kernel-checked cells, part 12

52 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(1280/NT, 16384/NS)`. -/
theorem cn12_0 : cornerOK gdata (1280) (16384)
    [630434498, 558198652, 612532186, 257655448, 158552655, 27682501, 12824830] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 16384/NS)`. -/
theorem cn12_1 : cornerOK gdata (1408) (16384)
    [644083217, 579276700, 652418429, 276524837, 172917497, 30039476, 14264027] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1280/NT, 20480/NS)`. -/
theorem cn12_2 : cornerOK gdata (1280) (20480)
    [630434498, 558198652, 612532186, 257655448, 158552655, 27682501, 12824830] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 20480/NS)`. -/
theorem cn12_3 : cornerOK gdata (1408) (20480)
    [644083217, 579276700, 652418429, 276524837, 172917497, 30039476, 14264027] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 16384/NS)`. -/
theorem cn12_4 : cornerOK gdata (1536) (16384)
    [651619090, 595540093, 688493783, 292286205, 186466588, 31982299, 15779935] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 20480/NS)`. -/
theorem cn12_5 : cornerOK gdata (1536) (20480)
    [651619090, 595540093, 688493783, 292286205, 186466588, 31982299, 15779935] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 16384/NS)`. -/
theorem cn12_6 : cornerOK gdata (1664) (16384)
    [652444146, 604169455, 717914371, 304139990, 198588155, 33499187, 17669006] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 20480/NS)`. -/
theorem cn12_7 : cornerOK gdata (1664) (20480)
    [652444146, 604169455, 717914371, 304139990, 198588155, 33499187, 17669006] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 16384/NS)`. -/
theorem cn12_8 : cornerOK gdata (1792) (16384)
    [652444146, 605476966, 742398651, 311650767, 209695627, 34520342, 19544760] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 20480/NS)`. -/
theorem cn12_9 : cornerOK gdata (1792) (20480)
    [652444146, 605476966, 742398651, 311650767, 209695627, 34520342, 19544760] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 16384/NS)`. -/
theorem cn12_10 : cornerOK gdata (1920) (16384)
    [649267950, 605476966, 761059204, 314538643, 219479291, 34980764, 21340926] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 20480/NS)`. -/
theorem cn12_11 : cornerOK gdata (1920) (20480)
    [649267950, 605476966, 761059204, 314538643, 219479291, 34980764, 21340926] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 16384/NS)`. -/
theorem cn12_12 : cornerOK gdata (2048) (16384)
    [641153056, 599770836, 776394340, 314538643, 233642498, 34980764, 23113177] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 20480/NS)`. -/
theorem cn12_13 : cornerOK gdata (2048) (20480)
    [641153056, 599770836, 776394340, 314538643, 233642498, 34980764, 23113177] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 16384/NS)`. -/
theorem cn12_14 : cornerOK gdata (2176) (16384)
    [630579427, 591120121, 785030294, 313734624, 245992576, 34959971, 24771043] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 20480/NS)`. -/
theorem cn12_15 : cornerOK gdata (2176) (20480)
    [630579427, 591120121, 785030294, 313734624, 245992576, 34959971, 24771043] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 16384/NS)`. -/
theorem cn12_16 : cornerOK gdata (2304) (16384)
    [615865493, 574495857, 790573580, 308146889, 256996013, 34396189, 26291403] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 20480/NS)`. -/
theorem cn12_17 : cornerOK gdata (2304) (20480)
    [615865493, 574495857, 790573580, 308146889, 256996013, 34396189, 26291403] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 16384/NS)`. -/
theorem cn12_18 : cornerOK gdata (2432) (16384)
    [600219086, 552165813, 791102619, 298844663, 266474332, 33398217, 27647008] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 20480/NS)`. -/
theorem cn12_19 : cornerOK gdata (2432) (20480)
    [600219086, 552165813, 791102619, 298844663, 266474332, 33398217, 27647008] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 16384/NS)`. -/
theorem cn12_20 : cornerOK gdata (2560) (16384)
    [582395428, 524661911, 791102619, 286194903, 274533234, 32026718, 28873658] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 20480/NS)`. -/
theorem cn12_21 : cornerOK gdata (2560) (20480)
    [582395428, 524661911, 791102619, 286194903, 274533234, 32026718, 28873658] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 16384/NS)`. -/
theorem cn12_22 : cornerOK gdata (2688) (16384)
    [564279568, 493123305, 790721038, 270840061, 281743896, 30403323, 30030222] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 20480/NS)`. -/
theorem cn12_23 : cornerOK gdata (2688) (20480)
    [564279568, 493123305, 790721038, 270840061, 281743896, 30403323, 30030222] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 16384/NS)`. -/
theorem cn12_24 : cornerOK gdata (2816) (16384)
    [543617887, 458527520, 784348569, 253415062, 286880757, 28593740, 30905143] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 20480/NS)`. -/
theorem cn12_25 : cornerOK gdata (2816) (20480)
    [543617887, 458527520, 784348569, 253415062, 286880757, 28593740, 30905143] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 16384/NS)`. -/
theorem cn12_26 : cornerOK gdata (2944) (16384)
    [525571892, 422282965, 782838681, 234294367, 290737449, 26517137, 31602936] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 20480/NS)`. -/
theorem cn12_27 : cornerOK gdata (2944) (20480)
    [525571892, 422282965, 782838681, 234294367, 290737449, 26517137, 31602936] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 16384/NS)`. -/
theorem cn12_28 : cornerOK gdata (3072) (16384)
    [508116143, 383974024, 780313912, 213785137, 293453219, 24258940, 32130998] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 20480/NS)`. -/
theorem cn12_29 : cornerOK gdata (3072) (20480)
    [508116143, 383974024, 780313912, 213785137, 293453219, 24258940, 32130998] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3200/NT, 16384/NS)`. -/
theorem cn12_30 : cornerOK gdata (3200) (16384)
    [491257468, 344536466, 775868132, 192561199, 295362053, 21886562, 32542827] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3200/NT, 20480/NS)`. -/
theorem cn12_31 : cornerOK gdata (3200) (20480)
    [491257468, 344536466, 775868132, 192561199, 295362053, 21886562, 32542827] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 16384/NS)`. -/
theorem cn12_32 : cornerOK gdata (3328) (16384)
    [474899766, 304207903, 770285595, 170722110, 295731761, 19441722, 32762325] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 20480/NS)`. -/
theorem cn12_33 : cornerOK gdata (3328) (20480)
    [474899766, 304207903, 770285595, 170722110, 295731761, 19441722, 32762325] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3456/NT, 16384/NS)`. -/
theorem cn12_34 : cornerOK gdata (3456) (16384)
    [459681796, 263481549, 762236389, 148286708, 295731761, 16937993, 32859362] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3456/NT, 20480/NS)`. -/
theorem cn12_35 : cornerOK gdata (3456) (20480)
    [459681796, 263481549, 762236389, 148286708, 295731761, 16937993, 32859362] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 16384/NS)`. -/
theorem cn12_36 : cornerOK gdata (3584) (16384)
    [446126142, 223110895, 753264534, 125867795, 295246731, 14435262, 32859362] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 20480/NS)`. -/
theorem cn12_37 : cornerOK gdata (3584) (20480)
    [446126142, 223110895, 753264534, 125867795, 295246731, 14435262, 32859362] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3712/NT, 16384/NS)`. -/
theorem cn12_38 : cornerOK gdata (3712) (16384)
    [434180858, 183463502, 743092309, 103692403, 293822455, 11963416, 32828254] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3712/NT, 20480/NS)`. -/
theorem cn12_39 : cornerOK gdata (3712) (20480)
    [434180858, 183463502, 743092309, 103692403, 293822455, 11963416, 32828254] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 16384/NS)`. -/
theorem cn12_40 : cornerOK gdata (3840) (16384)
    [423075779, 144996282, 732007188, 82312082, 291575125, 9587169, 32679238] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 20480/NS)`. -/
theorem cn12_41 : cornerOK gdata (3840) (20480)
    [423075779, 144996282, 732007188, 82312082, 291575125, 9587169, 32679238] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3968/NT, 16384/NS)`. -/
theorem cn12_42 : cornerOK gdata (3968) (16384)
    [412982209, 108121484, 720472962, 61651610, 288669272, 7308013, 32435649] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3968/NT, 20480/NS)`. -/
theorem cn12_43 : cornerOK gdata (3968) (20480)
    [412982209, 108121484, 720472962, 61651610, 288669272, 7308013, 32435649] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 16384/NS)`. -/
theorem cn12_44 : cornerOK gdata (4096) (16384)
    [403917581, 73304178, 708675624, 41857608, 285198018, 5124976, 32108357] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 20480/NS)`. -/
theorem cn12_45 : cornerOK gdata (4096) (20480)
    [403917581, 73304178, 708675624, 41857608, 285198018, 5124976, 32108357] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 20480/NS)`. -/
theorem cn12_46 : cornerOK gdata (-4096) (20480)
    [7730328136, 1137522201, 3577053948, 387509301, 593443504, 45520649, 24134487] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 20480/NS)`. -/
theorem cn12_47 : cornerOK gdata (-3840) (20480)
    [8939512817, 1903879387, 4146272791, 644234862, 674383731, 76357111, 26300673] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 21760/NS)`. -/
theorem cn12_48 : cornerOK gdata (-4096) (21760)
    [10858398502, 1507617367, 4906875366, 500826291, 784802151, 58877558, 28830274] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 21760/NS)`. -/
theorem cn12_49 : cornerOK gdata (-3840) (21760)
    [12608026630, 2572277595, 5713753358, 844535863, 895956942, 100228873, 31461437] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 23040/NS)`. -/
theorem cn12_50 : cornerOK gdata (-4096) (23040)
    [15509340866, 2025600255, 6858023076, 656378795, 1059750942, 77251967, 34765010] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 23040/NS)`. -/
theorem cn12_51 : cornerOK gdata (-3840) (23040)
    [18085065296, 3523803344, 8023391354, 1123003417, 1215797650, 133479492, 37988785] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 24320/NS)`. -/
theorem cn12_52 : cornerOK gdata (-4096) (24320)
    [22579298667, 2764972831, 9790537730, 874344916, 1464974895, 103045354, 42379907] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 24320/NS)`. -/
theorem cn12_53 : cornerOK gdata (-3840) (24320)
    [26447369129, 4904941877, 11510474846, 1518208418, 1689570450, 180728898, 46371336] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 25600/NS)`. -/
theorem cn12_54 : cornerOK gdata (-4096) (25600)
    [22579298667, 2764972831, 9790537730, 874344916, 1464974895, 103045354, 42379907] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 25600/NS)`. -/
theorem cn12_55 : cornerOK gdata (-3840) (25600)
    [26447369129, 4904941877, 11510474846, 1518208418, 1689570450, 180728898, 46371336] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 20480/NS)`. -/
theorem cn12_56 : cornerOK gdata (-3584) (20480)
    [8939512817, 1903879387, 4146272791, 644234862, 674383731, 76357111, 26300673] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 21760/NS)`. -/
theorem cn12_57 : cornerOK gdata (-3584) (21760)
    [12608026630, 2572277595, 5713753358, 844535863, 895956942, 100228873, 31461437] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 23040/NS)`. -/
theorem cn12_58 : cornerOK gdata (-3584) (23040)
    [18085065296, 3523803344, 8023391354, 1123003417, 1215797650, 133479492, 37988785] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 24320/NS)`. -/
theorem cn12_59 : cornerOK gdata (-3584) (24320)
    [26447369129, 4904941877, 11510474846, 1518208418, 1689570450, 180728898, 46371336] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 25600/NS)`. -/
theorem cn12_60 : cornerOK gdata (-3584) (25600)
    [26447369129, 4904941877, 11510474846, 1518208418, 1689570450, 180728898, 46371336] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 20480/NS)`. -/
theorem cn12_61 : cornerOK gdata (-3456) (20480)
    [2945631088, 641229252, 1276785714, 209857060, 220113036, 25762239, 9182739] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 21760/NS)`. -/
theorem cn12_62 : cornerOK gdata (-3456) (21760)
    [4022607923, 852807721, 1701026167, 269495570, 282909519, 33188414, 10690576] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 23040/NS)`. -/
theorem cn12_63 : cornerOK gdata (-3456) (23040)
    [5571987003, 1148219243, 2303019844, 349913199, 370192080, 43234466, 12539656] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 24320/NS)`. -/
theorem cn12_64 : cornerOK gdata (-3456) (24320)
    [7840333954, 1566988050, 3173787608, 460070278, 494661642, 57025962, 14830805] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 25600/NS)`. -/
theorem cn12_65 : cornerOK gdata (-3456) (25600)
    [7840333954, 1566988050, 3173787608, 460070278, 494661642, 57025962, 14830805] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 20480/NS)`. -/
theorem cn12_66 : cornerOK gdata (-3328) (20480)
    [3007855489, 732625573, 1306520011, 239008975, 222393091, 29081961, 9080579] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 21760/NS)`. -/
theorem cn12_67 : cornerOK gdata (-3328) (21760)
    [4108266141, 968169759, 1741990855, 306275034, 286020228, 37394610, 10558871] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 23040/NS)`. -/
theorem cn12_68 : cornerOK gdata (-3328) (23040)
    [5688847664, 1302538770, 2359128939, 396558941, 375192722, 48593996, 12368216] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 24320/NS)`. -/
theorem cn12_69 : cornerOK gdata (-3328) (24320)
    [8002270516, 1775978224, 3251897875, 519810611, 501886023, 63922308, 14604338] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 25600/NS)`. -/
theorem cn12_70 : cornerOK gdata (-3328) (25600)
    [8002270516, 1775978224, 3251897875, 519810611, 501886023, 63922308, 14604338] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 20480/NS)`. -/
theorem cn12_71 : cornerOK gdata (-3200) (20480)
    [3050642021, 818449930, 1329227150, 265076842, 223320070, 31941240, 8904871] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 21760/NS)`. -/
theorem cn12_72 : cornerOK gdata (-3200) (21760)
    [4163321222, 1078660877, 1772070277, 338544861, 288021235, 40940984, 10339168] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 23040/NS)`. -/
theorem cn12_73 : cornerOK gdata (-3200) (23040)
    [5759649509, 1439963406, 2399270598, 436755957, 377879288, 53020580, 12086724] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 24320/NS)`. -/
theorem cn12_74 : cornerOK gdata (-3200) (24320)
    [8090303214, 1951122698, 3304625914, 570074162, 505186580, 69467906, 14243879] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 25600/NS)`. -/
theorem cn12_75 : cornerOK gdata (-3200) (25600)
    [8090303214, 1951122698, 3304625914, 570074162, 505186580, 69467906, 14243879] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 20480/NS)`. -/
theorem cn12_76 : cornerOK gdata (-3072) (20480)
    [3066352774, 892310149, 1342075594, 286786961, 223378239, 34191150, 8657223] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 21760/NS)`. -/
theorem cn12_77 : cornerOK gdata (-3072) (21760)
    [4177659041, 1172777592, 1787567471, 364792829, 288021235, 43648812, 10030701] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 23040/NS)`. -/
theorem cn12_78 : cornerOK gdata (-3072) (23040)
    [5767270268, 1560675150, 2417004464, 468483504, 377879288, 56275253, 11700935] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 24320/NS)`. -/
theorem cn12_79 : cornerOK gdata (-3072) (24320)
    [8090303214, 2105782281, 3323187795, 608424640, 505186580, 73372510, 13753818] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 25600/NS)`. -/
theorem cn12_80 : cornerOK gdata (-3072) (25600)
    [8090303214, 2105782281, 3323187795, 608424640, 505186580, 73372510, 13753818] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 20480/NS)`. -/
theorem cn12_81 : cornerOK gdata (-2944) (20480)
    [3066352774, 951287965, 1342924595, 303246744, 223378239, 35731054, 8340278] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 21760/NS)`. -/
theorem cn12_82 : cornerOK gdata (-2944) (21760)
    [4177659041, 1244798661, 1787567471, 383905907, 287867729, 45396361, 9639737] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 23040/NS)`. -/
theorem cn12_83 : cornerOK gdata (-2944) (23040)
    [5767270268, 1560675150, 2417004464, 468483504, 377205836, 56275253, 11214464] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 24320/NS)`. -/
theorem cn12_84 : cornerOK gdata (-2944) (24320)
    [8080819502, 2105782281, 3323187795, 608424640, 503504002, 73372510, 13143831] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 25600/NS)`. -/
theorem cn12_85 : cornerOK gdata (-2944) (25600)
    [8080819502, 2105782281, 3323187795, 608424640, 503504002, 73372510, 13143831] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2816/NT, 20480/NS)`. -/
theorem cn12_86 : cornerOK gdata (-2816) (20480)
    [3048491211, 951287965, 1342924595, 303246744, 221589210, 35731054, 7994144] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2816/NT, 21760/NS)`. -/
theorem cn12_87 : cornerOK gdata (-2816) (21760)
    [4142119817, 1244798661, 1785077695, 383905907, 285053830, 45396361, 9211500] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2816/NT, 23040/NS)`. -/
theorem cn12_88 : cornerOK gdata (-2816) (23040)
    [4142119817, 1244798661, 1785077695, 383905907, 285053830, 45396361, 9211500] = true := by
  decide +kernel

/-- Kernel-checked box `[1280, 1408]/NT × [16384, 20480]/NS`. -/
theorem cov619 : Cover gdata (1280) (1408) (16384) (20480) := by
  ballooning_cover "Q:cn12_0,cn12_1,cn12_2,cn12_3"

/-- Kernel-checked box `[1408, 1536]/NT × [16384, 20480]/NS`. -/
theorem cov620 : Cover gdata (1408) (1536) (16384) (20480) := by
  ballooning_cover "Q:cn12_1,cn12_4,cn12_3,cn12_5"

/-- Kernel-checked box `[1536, 1664]/NT × [16384, 20480]/NS`. -/
theorem cov621 : Cover gdata (1536) (1664) (16384) (20480) := by
  ballooning_cover "Q:cn12_4,cn12_6,cn12_5,cn12_7"

/-- Kernel-checked box `[1664, 1792]/NT × [16384, 20480]/NS`. -/
theorem cov622 : Cover gdata (1664) (1792) (16384) (20480) := by
  ballooning_cover "Q:cn12_6,cn12_8,cn12_7,cn12_9"

/-- Kernel-checked box `[1792, 1920]/NT × [16384, 20480]/NS`. -/
theorem cov623 : Cover gdata (1792) (1920) (16384) (20480) := by
  ballooning_cover "Q:cn12_8,cn12_10,cn12_9,cn12_11"

/-- Kernel-checked box `[1920, 2048]/NT × [16384, 20480]/NS`. -/
theorem cov624 : Cover gdata (1920) (2048) (16384) (20480) := by
  ballooning_cover "Q:cn12_10,cn12_12,cn12_11,cn12_13"

/-- Kernel-checked box `[2048, 2176]/NT × [16384, 20480]/NS`. -/
theorem cov625 : Cover gdata (2048) (2176) (16384) (20480) := by
  ballooning_cover "Q:cn12_12,cn12_14,cn12_13,cn12_15"

/-- Kernel-checked box `[2176, 2304]/NT × [16384, 20480]/NS`. -/
theorem cov626 : Cover gdata (2176) (2304) (16384) (20480) := by
  ballooning_cover "Q:cn12_14,cn12_16,cn12_15,cn12_17"

/-- Kernel-checked box `[2304, 2432]/NT × [16384, 20480]/NS`. -/
theorem cov627 : Cover gdata (2304) (2432) (16384) (20480) := by
  ballooning_cover "Q:cn12_16,cn12_18,cn12_17,cn12_19"

/-- Kernel-checked box `[2432, 2560]/NT × [16384, 20480]/NS`. -/
theorem cov628 : Cover gdata (2432) (2560) (16384) (20480) := by
  ballooning_cover "Q:cn12_18,cn12_20,cn12_19,cn12_21"

/-- Kernel-checked box `[2560, 2688]/NT × [16384, 20480]/NS`. -/
theorem cov629 : Cover gdata (2560) (2688) (16384) (20480) := by
  ballooning_cover "Q:cn12_20,cn12_22,cn12_21,cn12_23"

/-- Kernel-checked box `[2688, 2816]/NT × [16384, 20480]/NS`. -/
theorem cov630 : Cover gdata (2688) (2816) (16384) (20480) := by
  ballooning_cover "Q:cn12_22,cn12_24,cn12_23,cn12_25"

/-- Kernel-checked box `[2816, 2944]/NT × [16384, 20480]/NS`. -/
theorem cov631 : Cover gdata (2816) (2944) (16384) (20480) := by
  ballooning_cover "Q:cn12_24,cn12_26,cn12_25,cn12_27"

/-- Kernel-checked box `[2944, 3072]/NT × [16384, 20480]/NS`. -/
theorem cov632 : Cover gdata (2944) (3072) (16384) (20480) := by
  ballooning_cover "Q:cn12_26,cn12_28,cn12_27,cn12_29"

/-- Kernel-checked box `[3072, 3200]/NT × [16384, 20480]/NS`. -/
theorem cov633 : Cover gdata (3072) (3200) (16384) (20480) := by
  ballooning_cover "Q:cn12_28,cn12_30,cn12_29,cn12_31"

/-- Kernel-checked box `[3200, 3328]/NT × [16384, 20480]/NS`. -/
theorem cov634 : Cover gdata (3200) (3328) (16384) (20480) := by
  ballooning_cover "Q:cn12_30,cn12_32,cn12_31,cn12_33"

/-- Kernel-checked box `[3328, 3456]/NT × [16384, 20480]/NS`. -/
theorem cov635 : Cover gdata (3328) (3456) (16384) (20480) := by
  ballooning_cover "Q:cn12_32,cn12_34,cn12_33,cn12_35"

/-- Kernel-checked box `[3456, 3584]/NT × [16384, 20480]/NS`. -/
theorem cov636 : Cover gdata (3456) (3584) (16384) (20480) := by
  ballooning_cover "Q:cn12_34,cn12_36,cn12_35,cn12_37"

/-- Kernel-checked box `[3584, 3712]/NT × [16384, 20480]/NS`. -/
theorem cov637 : Cover gdata (3584) (3712) (16384) (20480) := by
  ballooning_cover "Q:cn12_36,cn12_38,cn12_37,cn12_39"

/-- Kernel-checked box `[3712, 3840]/NT × [16384, 20480]/NS`. -/
theorem cov638 : Cover gdata (3712) (3840) (16384) (20480) := by
  ballooning_cover "Q:cn12_38,cn12_40,cn12_39,cn12_41"

/-- Kernel-checked box `[3840, 3968]/NT × [16384, 20480]/NS`. -/
theorem cov639 : Cover gdata (3840) (3968) (16384) (20480) := by
  ballooning_cover "Q:cn12_40,cn12_42,cn12_41,cn12_43"

/-- Kernel-checked box `[3968, 4096]/NT × [16384, 20480]/NS`. -/
theorem cov640 : Cover gdata (3968) (4096) (16384) (20480) := by
  ballooning_cover "Q:cn12_42,cn12_44,cn12_43,cn12_45"

/-- Kernel-checked box `[-4096, -3840]/NT × [20480, 21760]/NS`. -/
theorem cov641 : Cover gdata (-4096) (-3840) (20480) (21760) := by
  ballooning_cover "Q:cn12_46,cn12_47,cn12_48,cn12_49"

/-- Kernel-checked box `[-4096, -3840]/NT × [21760, 23040]/NS`. -/
theorem cov642 : Cover gdata (-4096) (-3840) (21760) (23040) := by
  ballooning_cover "Q:cn12_48,cn12_49,cn12_50,cn12_51"

/-- Kernel-checked box `[-4096, -3840]/NT × [23040, 24320]/NS`. -/
theorem cov643 : Cover gdata (-4096) (-3840) (23040) (24320) := by
  ballooning_cover "Q:cn12_50,cn12_51,cn12_52,cn12_53"

/-- Kernel-checked box `[-4096, -3840]/NT × [24320, 25600]/NS`. -/
theorem cov644 : Cover gdata (-4096) (-3840) (24320) (25600) := by
  ballooning_cover "Q:cn12_52,cn12_53,cn12_54,cn12_55"

/-- Kernel-checked box `[-3840, -3584]/NT × [20480, 21760]/NS`. -/
theorem cov645 : Cover gdata (-3840) (-3584) (20480) (21760) := by
  ballooning_cover "Q:cn12_47,cn12_56,cn12_49,cn12_57"

/-- Kernel-checked box `[-3840, -3584]/NT × [21760, 23040]/NS`. -/
theorem cov646 : Cover gdata (-3840) (-3584) (21760) (23040) := by
  ballooning_cover "Q:cn12_49,cn12_57,cn12_51,cn12_58"

/-- Kernel-checked box `[-3840, -3584]/NT × [23040, 24320]/NS`. -/
theorem cov647 : Cover gdata (-3840) (-3584) (23040) (24320) := by
  ballooning_cover "Q:cn12_51,cn12_58,cn12_53,cn12_59"

/-- Kernel-checked box `[-3840, -3584]/NT × [24320, 25600]/NS`. -/
theorem cov648 : Cover gdata (-3840) (-3584) (24320) (25600) := by
  ballooning_cover "Q:cn12_53,cn12_59,cn12_55,cn12_60"

/-- Kernel-checked box `[-3584, -3456]/NT × [20480, 21760]/NS`. -/
theorem cov649 : Cover gdata (-3584) (-3456) (20480) (21760) := by
  ballooning_cover "Q:cn12_56,cn12_61,cn12_57,cn12_62"

/-- Kernel-checked box `[-3584, -3456]/NT × [21760, 23040]/NS`. -/
theorem cov650 : Cover gdata (-3584) (-3456) (21760) (23040) := by
  ballooning_cover "Q:cn12_57,cn12_62,cn12_58,cn12_63"

/-- Kernel-checked box `[-3584, -3456]/NT × [23040, 24320]/NS`. -/
theorem cov651 : Cover gdata (-3584) (-3456) (23040) (24320) := by
  ballooning_cover "Q:cn12_58,cn12_63,cn12_59,cn12_64"

/-- Kernel-checked box `[-3584, -3456]/NT × [24320, 25600]/NS`. -/
theorem cov652 : Cover gdata (-3584) (-3456) (24320) (25600) := by
  ballooning_cover "Q:cn12_59,cn12_64,cn12_60,cn12_65"

/-- Kernel-checked box `[-3456, -3328]/NT × [20480, 21760]/NS`. -/
theorem cov653 : Cover gdata (-3456) (-3328) (20480) (21760) := by
  ballooning_cover "Q:cn12_61,cn12_66,cn12_62,cn12_67"

/-- Kernel-checked box `[-3456, -3328]/NT × [21760, 23040]/NS`. -/
theorem cov654 : Cover gdata (-3456) (-3328) (21760) (23040) := by
  ballooning_cover "Q:cn12_62,cn12_67,cn12_63,cn12_68"

/-- Kernel-checked box `[-3456, -3328]/NT × [23040, 24320]/NS`. -/
theorem cov655 : Cover gdata (-3456) (-3328) (23040) (24320) := by
  ballooning_cover "Q:cn12_63,cn12_68,cn12_64,cn12_69"

/-- Kernel-checked box `[-3456, -3328]/NT × [24320, 25600]/NS`. -/
theorem cov656 : Cover gdata (-3456) (-3328) (24320) (25600) := by
  ballooning_cover "Q:cn12_64,cn12_69,cn12_65,cn12_70"

/-- Kernel-checked box `[-3328, -3200]/NT × [20480, 21760]/NS`. -/
theorem cov657 : Cover gdata (-3328) (-3200) (20480) (21760) := by
  ballooning_cover "Q:cn12_66,cn12_71,cn12_67,cn12_72"

/-- Kernel-checked box `[-3328, -3200]/NT × [21760, 23040]/NS`. -/
theorem cov658 : Cover gdata (-3328) (-3200) (21760) (23040) := by
  ballooning_cover "Q:cn12_67,cn12_72,cn12_68,cn12_73"

/-- Kernel-checked box `[-3328, -3200]/NT × [23040, 24320]/NS`. -/
theorem cov659 : Cover gdata (-3328) (-3200) (23040) (24320) := by
  ballooning_cover "Q:cn12_68,cn12_73,cn12_69,cn12_74"

/-- Kernel-checked box `[-3328, -3200]/NT × [24320, 25600]/NS`. -/
theorem cov660 : Cover gdata (-3328) (-3200) (24320) (25600) := by
  ballooning_cover "Q:cn12_69,cn12_74,cn12_70,cn12_75"

/-- Kernel-checked box `[-3200, -3072]/NT × [20480, 21760]/NS`. -/
theorem cov661 : Cover gdata (-3200) (-3072) (20480) (21760) := by
  ballooning_cover "Q:cn12_71,cn12_76,cn12_72,cn12_77"

/-- Kernel-checked box `[-3200, -3072]/NT × [21760, 23040]/NS`. -/
theorem cov662 : Cover gdata (-3200) (-3072) (21760) (23040) := by
  ballooning_cover "Q:cn12_72,cn12_77,cn12_73,cn12_78"

/-- Kernel-checked box `[-3200, -3072]/NT × [23040, 24320]/NS`. -/
theorem cov663 : Cover gdata (-3200) (-3072) (23040) (24320) := by
  ballooning_cover "Q:cn12_73,cn12_78,cn12_74,cn12_79"

/-- Kernel-checked box `[-3200, -3072]/NT × [24320, 25600]/NS`. -/
theorem cov664 : Cover gdata (-3200) (-3072) (24320) (25600) := by
  ballooning_cover "Q:cn12_74,cn12_79,cn12_75,cn12_80"

/-- Kernel-checked box `[-3072, -2944]/NT × [20480, 21760]/NS`. -/
theorem cov665 : Cover gdata (-3072) (-2944) (20480) (21760) := by
  ballooning_cover "Q:cn12_76,cn12_81,cn12_77,cn12_82"

/-- Kernel-checked box `[-3072, -2944]/NT × [21760, 23040]/NS`. -/
theorem cov666 : Cover gdata (-3072) (-2944) (21760) (23040) := by
  ballooning_cover "Q:cn12_77,cn12_82,cn12_78,cn12_83"

/-- Kernel-checked box `[-3072, -2944]/NT × [23040, 24320]/NS`. -/
theorem cov667 : Cover gdata (-3072) (-2944) (23040) (24320) := by
  ballooning_cover "Q:cn12_78,cn12_83,cn12_79,cn12_84"

/-- Kernel-checked box `[-3072, -2944]/NT × [24320, 25600]/NS`. -/
theorem cov668 : Cover gdata (-3072) (-2944) (24320) (25600) := by
  ballooning_cover "Q:cn12_79,cn12_84,cn12_80,cn12_85"

/-- Kernel-checked box `[-2944, -2816]/NT × [20480, 21760]/NS`. -/
theorem cov669 : Cover gdata (-2944) (-2816) (20480) (21760) := by
  ballooning_cover "Q:cn12_81,cn12_86,cn12_82,cn12_87"

/-- Kernel-checked box `[-2944, -2816]/NT × [21760, 23040]/NS`. -/
theorem cov670 : Cover gdata (-2944) (-2816) (21760) (23040) := by
  ballooning_cover "Q:cn12_82,cn12_87,cn12_83,cn12_88"

end PlasmaLean.Design.SolovevBallooning
