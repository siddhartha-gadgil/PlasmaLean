/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 7

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

/-- Kernel-checked corner test at `(-2176/NT, 8192/NS)`. -/
theorem cn07_0 : cornerOK gdata (-2176) (8192)
    [667335885, 362385633, 400818539, 141754262, 83299538, 15946852, 5089851] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 8192/NS)`. -/
theorem cn07_1 : cornerOK gdata (-2048) (8192)
    [667335885, 362385633, 400818539, 141754262, 83299538, 15946852, 5089851] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 10240/NS)`. -/
theorem cn07_2 : cornerOK gdata (-2176) (10240)
    [926429569, 467377804, 529939441, 178972584, 105212308, 20045346, 5904635] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 10240/NS)`. -/
theorem cn07_3 : cornerOK gdata (-2048) (10240)
    [926429569, 467377804, 529939441, 178972584, 105212308, 20045346, 5904635] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 12288/NS)`. -/
theorem cn07_4 : cornerOK gdata (-2176) (12288)
    [926429569, 467377804, 529939441, 178972584, 105212308, 20045346, 5904635] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 12288/NS)`. -/
theorem cn07_5 : cornerOK gdata (-2048) (12288)
    [926429569, 467377804, 529939441, 178972584, 105212308, 20045346, 5904635] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 8192/NS)`. -/
theorem cn07_6 : cornerOK gdata (-1920) (8192)
    [621940462, 343429803, 373915856, 133516854, 76503092, 14996306, 4553925] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 10240/NS)`. -/
theorem cn07_7 : cornerOK gdata (-1920) (10240)
    [856315311, 440166426, 492084685, 167485158, 96222192, 18721644, 5269106] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 12288/NS)`. -/
theorem cn07_8 : cornerOK gdata (-1920) (12288)
    [856315311, 440166426, 492084685, 167485158, 96222192, 18721644, 5269106] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 8192/NS)`. -/
theorem cn07_9 : cornerOK gdata (-1792) (8192)
    [573796008, 321537933, 345957169, 124380352, 69576567, 13937234, 4027947] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 10240/NS)`. -/
theorem cn07_10 : cornerOK gdata (-1792) (10240)
    [782071505, 410077477, 452621322, 155543370, 87101048, 17352019, 4657566] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 12288/NS)`. -/
theorem cn07_11 : cornerOK gdata (-1792) (12288)
    [782071505, 410077477, 452621322, 155543370, 87101048, 17352019, 4657566] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 8192/NS)`. -/
theorem cn07_12 : cornerOK gdata (-1664) (8192)
    [522766575, 297093656, 317246364, 115350639, 62667194, 12822953, 3528611] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 10240/NS)`. -/
theorem cn07_13 : cornerOK gdata (-1664) (10240)
    [704322492, 375579672, 411353636, 143244985, 77967287, 15954640, 4070733] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 12288/NS)`. -/
theorem cn07_14 : cornerOK gdata (-1664) (12288)
    [704322492, 375579672, 411353636, 143244985, 77967287, 15954640, 4070733] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 8192/NS)`. -/
theorem cn07_15 : cornerOK gdata (-1536) (8192)
    [469784225, 270350306, 287549229, 105871124, 55800717, 11761320, 3053693] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 10240/NS)`. -/
theorem cn07_16 : cornerOK gdata (-1536) (10240)
    [624646237, 337469689, 369141172, 130717108, 68864398, 14538421, 3514320] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 12288/NS)`. -/
theorem cn07_17 : cornerOK gdata (-1536) (12288)
    [624646237, 337469689, 369141172, 130717108, 68864398, 14538421, 3514320] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 8192/NS)`. -/
theorem cn07_18 : cornerOK gdata (-1408) (8192)
    [1254068367, 695287913, 751408159, 255404137, 133913584, 27957133, 7052934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 10240/NS)`. -/
theorem cn07_19 : cornerOK gdata (-1408) (10240)
    [545957551, 302667442, 327250081, 117827964, 59988854, 13098623, 2996292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 12288/NS)`. -/
theorem cn07_20 : cornerOK gdata (-1408) (12288)
    [1254068367, 695287913, 751408159, 255404137, 133913584, 27957133, 7052934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 8192/NS)`. -/
theorem cn07_21 : cornerOK gdata (-1344) (8192)
    [1254068367, 695287913, 751408159, 255404137, 133913584, 27957133, 7052934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 12288/NS)`. -/
theorem cn07_22 : cornerOK gdata (-1344) (12288)
    [1254068367, 695287913, 751408159, 255404137, 133913584, 27957133, 7052934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 8192/NS)`. -/
theorem cn07_23 : cornerOK gdata (-1280) (8192)
    [1117969531, 626987997, 672075497, 230283063, 119163519, 25194394, 6174375] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 12288/NS)`. -/
theorem cn07_24 : cornerOK gdata (-1280) (12288)
    [1117969531, 626987997, 672075497, 230283063, 119163519, 25194394, 6174375] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 8192/NS)`. -/
theorem cn07_25 : cornerOK gdata (-1216) (8192)
    [1002962644, 562102374, 598062115, 206655716, 105620362, 22595601, 5370425] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 12288/NS)`. -/
theorem cn07_26 : cornerOK gdata (-1216) (12288)
    [1002962644, 562102374, 598062115, 206655716, 105620362, 22595601, 5370425] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 8192/NS)`. -/
theorem cn07_27 : cornerOK gdata (-1152) (8192)
    [896778427, 501367341, 530105437, 184699753, 93229195, 20175336, 4642763] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 12288/NS)`. -/
theorem cn07_28 : cornerOK gdata (-1152) (12288)
    [896778427, 501367341, 530105437, 184699753, 93229195, 20175336, 4642763] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 8192/NS)`. -/
theorem cn07_29 : cornerOK gdata (-1088) (8192)
    [797970314, 444513053, 467612073, 164308018, 81912976, 17932409, 4017007] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 12288/NS)`. -/
theorem cn07_30 : cornerOK gdata (-1088) (12288)
    [797970314, 444513053, 467612073, 164308018, 81912976, 17932409, 4017007] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 8192/NS)`. -/
theorem cn07_31 : cornerOK gdata (-1024) (8192)
    [1064404033, 590357437, 625625239, 227770335, 108263640, 24319074, 5176614] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 12288/NS)`. -/
theorem cn07_32 : cornerOK gdata (-1024) (12288)
    [1064404033, 590357437, 625625239, 227770335, 108263640, 24319074, 5176614] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 8192/NS)`. -/
theorem cn07_33 : cornerOK gdata (-896) (8192)
    [1064404033, 590357437, 625625239, 227770335, 108263640, 24319074, 5176614] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 12288/NS)`. -/
theorem cn07_34 : cornerOK gdata (-896) (12288)
    [1064404033, 590357437, 625625239, 227770335, 108263640, 24319074, 5176614] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 8192/NS)`. -/
theorem cn07_35 : cornerOK gdata (-768) (8192)
    [833302538, 459108508, 485007998, 177907436, 83399826, 18916051, 4020386] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 12288/NS)`. -/
theorem cn07_36 : cornerOK gdata (-768) (12288)
    [833302538, 459108508, 485007998, 177907436, 83399826, 18916051, 4020386] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 8192/NS)`. -/
theorem cn07_37 : cornerOK gdata (-640) (8192)
    [644541209, 349402437, 371032311, 136088682, 64086889, 14398330, 3144798] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 12288/NS)`. -/
theorem cn07_38 : cornerOK gdata (-640) (12288)
    [644541209, 349402437, 371032311, 136088682, 64086889, 14398330, 3144798] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 8192/NS)`. -/
theorem cn07_39 : cornerOK gdata (-512) (8192)
    [493547486, 268920534, 284419388, 101646913, 48953039, 10681046, 2473359] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 12288/NS)`. -/
theorem cn07_40 : cornerOK gdata (-512) (12288)
    [493547486, 268920534, 284419388, 101646913, 48953039, 10681046, 2473359] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 8192/NS)`. -/
theorem cn07_41 : cornerOK gdata (-384) (8192)
    [381415607, 206508802, 221159816, 74187192, 37772301, 7700599, 1976208] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 12288/NS)`. -/
theorem cn07_42 : cornerOK gdata (-384) (12288)
    [381415607, 206508802, 221159816, 74187192, 37772301, 7700599, 1976208] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 8192/NS)`. -/
theorem cn07_43 : cornerOK gdata (-256) (8192)
    [749972648, 420678420, 469918238, 164139987, 85117402, 16202706, 4554409] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 12288/NS)`. -/
theorem cn07_44 : cornerOK gdata (-256) (12288)
    [749972648, 420678420, 469918238, 164139987, 85117402, 16202706, 4554409] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 8192/NS)`. -/
theorem cn07_45 : cornerOK gdata (0) (8192)
    [749972648, 444090416, 469918238, 175727816, 87945107, 18666011, 4900448] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 12288/NS)`. -/
theorem cn07_46 : cornerOK gdata (0) (12288)
    [749972648, 444090416, 469918238, 175727816, 87945107, 18666011, 4900448] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 8192/NS)`. -/
theorem cn07_47 : cornerOK gdata (256) (8192)
    [692940419, 444090416, 462449437, 175727816, 87945107, 18666011, 4900448] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 12288/NS)`. -/
theorem cn07_48 : cornerOK gdata (256) (12288)
    [692940419, 444090416, 462449437, 175727816, 87945107, 18666011, 4900448] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 8192/NS)`. -/
theorem cn07_49 : cornerOK gdata (384) (8192)
    [269942710, 189120664, 182788265, 74345284, 36164081, 7342350, 2108047] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 12288/NS)`. -/
theorem cn07_50 : cornerOK gdata (384) (12288)
    [269942710, 189120664, 182788265, 74345284, 36164081, 7342350, 2108047] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 8192/NS)`. -/
theorem cn07_51 : cornerOK gdata (512) (8192)
    [313936447, 225836908, 216055567, 89109555, 44484047, 8975505, 2763030] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 12288/NS)`. -/
theorem cn07_52 : cornerOK gdata (512) (12288)
    [313936447, 225836908, 216055567, 89109555, 44484047, 8975505, 2763030] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 8192/NS)`. -/
theorem cn07_53 : cornerOK gdata (640) (8192)
    [362884966, 265003206, 254825461, 104925769, 54378848, 11055030, 3561310] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 12288/NS)`. -/
theorem cn07_54 : cornerOK gdata (640) (12288)
    [362884966, 265003206, 254825461, 104925769, 54378848, 11055030, 3561310] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 8192/NS)`. -/
theorem cn07_55 : cornerOK gdata (768) (8192)
    [413239390, 305214604, 298807512, 124417478, 65761402, 13297130, 4476941] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 12288/NS)`. -/
theorem cn07_56 : cornerOK gdata (768) (12288)
    [413239390, 305214604, 298807512, 124417478, 65761402, 13297130, 4476941] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 8192/NS)`. -/
theorem cn07_57 : cornerOK gdata (896) (8192)
    [464132937, 346473607, 347366423, 145623584, 78448836, 15666211, 5511858] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 12288/NS)`. -/
theorem cn07_58 : cornerOK gdata (896) (12288)
    [464132937, 346473607, 347366423, 145623584, 78448836, 15666211, 5511858] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 8192/NS)`. -/
theorem cn07_59 : cornerOK gdata (1024) (8192)
    [513893368, 386822507, 397990189, 167310729, 92065230, 18104216, 6659627] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 12288/NS)`. -/
theorem cn07_60 : cornerOK gdata (1024) (12288)
    [513893368, 386822507, 397990189, 167310729, 92065230, 18104216, 6659627] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 8192/NS)`. -/
theorem cn07_61 : cornerOK gdata (1152) (8192)
    [560461443, 425046925, 449063345, 188866475, 106319271, 20539104, 7907795] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 12288/NS)`. -/
theorem cn07_62 : cornerOK gdata (1152) (12288)
    [560461443, 425046925, 449063345, 188866475, 106319271, 20539104, 7907795] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 8192/NS)`. -/
theorem cn07_63 : cornerOK gdata (1280) (8192)
    [603817860, 460756557, 500772610, 209837141, 121381534, 22931206, 9280477] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 12288/NS)`. -/
theorem cn07_64 : cornerOK gdata (1280) (12288)
    [603817860, 460756557, 500772610, 209837141, 121381534, 22931206, 9280477] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 8192/NS)`. -/
theorem cn07_65 : cornerOK gdata (1408) (8192)
    [644327628, 496302310, 552709975, 231219845, 136966784, 25388617, 10736101] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 12288/NS)`. -/
theorem cn07_66 : cornerOK gdata (1408) (12288)
    [644327628, 496302310, 552709975, 231219845, 136966784, 25388617, 10736101] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 8192/NS)`. -/
theorem cn07_67 : cornerOK gdata (1536) (8192)
    [679109400, 529415374, 602368212, 251324246, 152665338, 27821110, 12459352] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 12288/NS)`. -/
theorem cn07_68 : cornerOK gdata (1536) (12288)
    [679109400, 529415374, 602368212, 251324246, 152665338, 27821110, 12459352] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 8192/NS)`. -/
theorem cn07_69 : cornerOK gdata (1664) (8192)
    [708356930, 558303545, 649472907, 268820591, 168228278, 29955407, 14306379] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 12288/NS)`. -/
theorem cn07_70 : cornerOK gdata (1664) (12288)
    [708356930, 558303545, 649472907, 268820591, 168228278, 29955407, 14306379] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 8192/NS)`. -/
theorem cn07_71 : cornerOK gdata (1792) (8192)
    [708356930, 558303545, 649472907, 268820591, 168228278, 29955407, 14306379] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 12288/NS)`. -/
theorem cn07_72 : cornerOK gdata (1792) (12288)
    [708356930, 587137632, 649472907, 274077760, 168228278, 32724016, 14306379] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 8192/NS)`. -/
theorem cn07_73 : cornerOK gdata (2048) (8192)
    [566795923, 506839904, 532278234, 234834554, 138326377, 27927290, 11859433] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 10240/NS)`. -/
theorem cn07_74 : cornerOK gdata (1792) (10240)
    [624664948, 587137632, 613991377, 274077760, 161962878, 32724016, 13573778] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 10240/NS)`. -/
theorem cn07_75 : cornerOK gdata (2048) (10240)
    [624664948, 587137632, 613991377, 274077760, 161962878, 32724016, 13835011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 12288/NS)`. -/
theorem cn07_76 : cornerOK gdata (2048) (12288)
    [624664948, 587137632, 613991377, 274077760, 161962878, 32724016, 13835011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 8192/NS)`. -/
theorem cn07_77 : cornerOK gdata (2304) (8192)
    [516004047, 470486612, 508599269, 221254630, 138105956, 26589185, 12036120] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 10240/NS)`. -/
theorem cn07_78 : cornerOK gdata (2304) (10240)
    [556500891, 535654833, 576076930, 254307660, 159154921, 30683626, 13835011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 12288/NS)`. -/
theorem cn07_79 : cornerOK gdata (2304) (12288)
    [556500891, 535654833, 576076930, 254307660, 159154921, 30683626, 13835011] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 8192/NS)`. -/
theorem cn07_80 : cornerOK gdata (2560) (8192)
    [459995642, 415588674, 474300550, 198286015, 134455060, 23957920, 12036120] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 10240/NS)`. -/
theorem cn07_81 : cornerOK gdata (2560) (10240)
    [486306166, 465930643, 527752133, 224710841, 152626959, 27248800, 13832846] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 12288/NS)`. -/
theorem cn07_82 : cornerOK gdata (2560) (12288)
    [486306166, 465930643, 527752133, 224710841, 152626959, 27248800, 13832846] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 8192/NS)`. -/
theorem cn07_83 : cornerOK gdata (2816) (8192)
    [406776665, 352053773, 439032316, 170354001, 128913205, 20645610, 11968690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 10240/NS)`. -/
theorem cn07_84 : cornerOK gdata (2816) (10240)
    [421536929, 388998829, 480852905, 190405187, 143946577, 23153106, 13530904] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 12288/NS)`. -/
theorem cn07_85 : cornerOK gdata (2816) (12288)
    [421536929, 388998829, 480852905, 190405187, 143946577, 23153106, 13530904] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 8192/NS)`. -/
theorem cn07_86 : cornerOK gdata (3072) (8192)
    [357358255, 285207816, 404067668, 139953046, 122571373, 16992452, 11679369] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 10240/NS)`. -/
theorem cn07_87 : cornerOK gdata (3072) (10240)
    [363564937, 311268587, 436085960, 154536327, 134870450, 18820713, 13016652] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 12288/NS)`. -/
theorem cn07_88 : cornerOK gdata (3072) (12288)
    [363564937, 311268587, 436085960, 154536327, 134870450, 18820713, 13016652] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 8192/NS)`. -/
theorem cn07_89 : cornerOK gdata (3328) (8192)
    [313716218, 220883530, 369353639, 109937974, 115453134, 13370488, 11246819] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 10240/NS)`. -/
theorem cn07_90 : cornerOK gdata (3328) (10240)
    [313716218, 239280139, 392942779, 120512272, 125438630, 14698186, 12364638] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3328/NT, 12288/NS)`. -/
theorem cn07_91 : cornerOK gdata (3328) (12288)
    [313517331, 239280139, 392942779, 120512272, 125438630, 14698186, 12364638] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 8192/NS)`. -/
theorem cn07_92 : cornerOK gdata (3584) (8192)
    [276237697, 166553034, 336704455, 84115121, 108046359, 10227413, 10718521] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 10240/NS)`. -/
theorem cn07_93 : cornerOK gdata (3584) (10240)
    [276237697, 178586661, 353846912, 91285889, 116062935, 11129335, 11642671] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 12288/NS)`. -/
theorem cn07_94 : cornerOK gdata (3584) (12288)
    [271925710, 178586661, 353846912, 91285889, 116062935, 11129335, 11642671] = true := by
  bl_cert

/-- Kernel-checked box `[-2176, -2048]/NT × [8192, 10240]/NS`. -/
theorem cov361 : Cover gdata (-2176) (-2048) (8192) (10240) := by
  ballooning_box "Q:cn07_0,cn07_1,cn07_2,cn07_3"

/-- Kernel-checked box `[-2176, -2048]/NT × [10240, 12288]/NS`. -/
theorem cov362 : Cover gdata (-2176) (-2048) (10240) (12288) := by
  ballooning_box "Q:cn07_2,cn07_3,cn07_4,cn07_5"

/-- Kernel-checked box `[-2048, -1920]/NT × [8192, 10240]/NS`. -/
theorem cov363 : Cover gdata (-2048) (-1920) (8192) (10240) := by
  ballooning_box "Q:cn07_1,cn07_6,cn07_3,cn07_7"

/-- Kernel-checked box `[-2048, -1920]/NT × [10240, 12288]/NS`. -/
theorem cov364 : Cover gdata (-2048) (-1920) (10240) (12288) := by
  ballooning_box "Q:cn07_3,cn07_7,cn07_5,cn07_8"

/-- Kernel-checked box `[-1920, -1792]/NT × [8192, 10240]/NS`. -/
theorem cov365 : Cover gdata (-1920) (-1792) (8192) (10240) := by
  ballooning_box "Q:cn07_6,cn07_9,cn07_7,cn07_10"

/-- Kernel-checked box `[-1920, -1792]/NT × [10240, 12288]/NS`. -/
theorem cov366 : Cover gdata (-1920) (-1792) (10240) (12288) := by
  ballooning_box "Q:cn07_7,cn07_10,cn07_8,cn07_11"

/-- Kernel-checked box `[-1792, -1664]/NT × [8192, 10240]/NS`. -/
theorem cov367 : Cover gdata (-1792) (-1664) (8192) (10240) := by
  ballooning_box "Q:cn07_9,cn07_12,cn07_10,cn07_13"

/-- Kernel-checked box `[-1792, -1664]/NT × [10240, 12288]/NS`. -/
theorem cov368 : Cover gdata (-1792) (-1664) (10240) (12288) := by
  ballooning_box "Q:cn07_10,cn07_13,cn07_11,cn07_14"

/-- Kernel-checked box `[-1664, -1536]/NT × [8192, 10240]/NS`. -/
theorem cov369 : Cover gdata (-1664) (-1536) (8192) (10240) := by
  ballooning_box "Q:cn07_12,cn07_15,cn07_13,cn07_16"

/-- Kernel-checked box `[-1664, -1536]/NT × [10240, 12288]/NS`. -/
theorem cov370 : Cover gdata (-1664) (-1536) (10240) (12288) := by
  ballooning_box "Q:cn07_13,cn07_16,cn07_14,cn07_17"

/-- Kernel-checked box `[-1536, -1408]/NT × [8192, 10240]/NS`. -/
theorem cov371 : Cover gdata (-1536) (-1408) (8192) (10240) := by
  ballooning_box "Q:cn07_15,cn07_18,cn07_16,cn07_19"

/-- Kernel-checked box `[-1536, -1408]/NT × [10240, 12288]/NS`. -/
theorem cov372 : Cover gdata (-1536) (-1408) (10240) (12288) := by
  ballooning_box "Q:cn07_16,cn07_19,cn07_17,cn07_20"

/-- Kernel-checked box `[-1408, -1344]/NT × [8192, 12288]/NS`. -/
theorem cov373 : Cover gdata (-1408) (-1344) (8192) (12288) := by
  ballooning_box "Q:cn07_18,cn07_21,cn07_20,cn07_22"

/-- Kernel-checked box `[-1344, -1280]/NT × [8192, 12288]/NS`. -/
theorem cov374 : Cover gdata (-1344) (-1280) (8192) (12288) := by
  ballooning_box "Q:cn07_21,cn07_23,cn07_22,cn07_24"

/-- Kernel-checked box `[-1280, -1216]/NT × [8192, 12288]/NS`. -/
theorem cov375 : Cover gdata (-1280) (-1216) (8192) (12288) := by
  ballooning_box "Q:cn07_23,cn07_25,cn07_24,cn07_26"

/-- Kernel-checked box `[-1216, -1152]/NT × [8192, 12288]/NS`. -/
theorem cov376 : Cover gdata (-1216) (-1152) (8192) (12288) := by
  ballooning_box "Q:cn07_25,cn07_27,cn07_26,cn07_28"

/-- Kernel-checked box `[-1152, -1088]/NT × [8192, 12288]/NS`. -/
theorem cov377 : Cover gdata (-1152) (-1088) (8192) (12288) := by
  ballooning_box "Q:cn07_27,cn07_29,cn07_28,cn07_30"

/-- Kernel-checked box `[-1088, -1024]/NT × [8192, 12288]/NS`. -/
theorem cov378 : Cover gdata (-1088) (-1024) (8192) (12288) := by
  ballooning_box "Q:cn07_29,cn07_31,cn07_30,cn07_32"

/-- Kernel-checked box `[-1024, -896]/NT × [8192, 12288]/NS`. -/
theorem cov379 : Cover gdata (-1024) (-896) (8192) (12288) := by
  ballooning_box "Q:cn07_31,cn07_33,cn07_32,cn07_34"

/-- Kernel-checked box `[-896, -768]/NT × [8192, 12288]/NS`. -/
theorem cov380 : Cover gdata (-896) (-768) (8192) (12288) := by
  ballooning_box "Q:cn07_33,cn07_35,cn07_34,cn07_36"

/-- Kernel-checked box `[-768, -640]/NT × [8192, 12288]/NS`. -/
theorem cov381 : Cover gdata (-768) (-640) (8192) (12288) := by
  ballooning_box "Q:cn07_35,cn07_37,cn07_36,cn07_38"

/-- Kernel-checked box `[-640, -512]/NT × [8192, 12288]/NS`. -/
theorem cov382 : Cover gdata (-640) (-512) (8192) (12288) := by
  ballooning_box "Q:cn07_37,cn07_39,cn07_38,cn07_40"

/-- Kernel-checked box `[-512, -384]/NT × [8192, 12288]/NS`. -/
theorem cov383 : Cover gdata (-512) (-384) (8192) (12288) := by
  ballooning_box "Q:cn07_39,cn07_41,cn07_40,cn07_42"

/-- Kernel-checked box `[-384, -256]/NT × [8192, 12288]/NS`. -/
theorem cov384 : Cover gdata (-384) (-256) (8192) (12288) := by
  ballooning_box "Q:cn07_41,cn07_43,cn07_42,cn07_44"

/-- Kernel-checked box `[-256, 0]/NT × [8192, 12288]/NS`. -/
theorem cov385 : Cover gdata (-256) (0) (8192) (12288) := by
  ballooning_box "Q:cn07_43,cn07_45,cn07_44,cn07_46"

/-- Kernel-checked box `[0, 256]/NT × [8192, 12288]/NS`. -/
theorem cov386 : Cover gdata (0) (256) (8192) (12288) := by
  ballooning_box "Q:cn07_45,cn07_47,cn07_46,cn07_48"

/-- Kernel-checked box `[256, 384]/NT × [8192, 12288]/NS`. -/
theorem cov387 : Cover gdata (256) (384) (8192) (12288) := by
  ballooning_box "Q:cn07_47,cn07_49,cn07_48,cn07_50"

/-- Kernel-checked box `[384, 512]/NT × [8192, 12288]/NS`. -/
theorem cov388 : Cover gdata (384) (512) (8192) (12288) := by
  ballooning_box "Q:cn07_49,cn07_51,cn07_50,cn07_52"

/-- Kernel-checked box `[512, 640]/NT × [8192, 12288]/NS`. -/
theorem cov389 : Cover gdata (512) (640) (8192) (12288) := by
  ballooning_box "Q:cn07_51,cn07_53,cn07_52,cn07_54"

/-- Kernel-checked box `[640, 768]/NT × [8192, 12288]/NS`. -/
theorem cov390 : Cover gdata (640) (768) (8192) (12288) := by
  ballooning_box "Q:cn07_53,cn07_55,cn07_54,cn07_56"

/-- Kernel-checked box `[768, 896]/NT × [8192, 12288]/NS`. -/
theorem cov391 : Cover gdata (768) (896) (8192) (12288) := by
  ballooning_box "Q:cn07_55,cn07_57,cn07_56,cn07_58"

/-- Kernel-checked box `[896, 1024]/NT × [8192, 12288]/NS`. -/
theorem cov392 : Cover gdata (896) (1024) (8192) (12288) := by
  ballooning_box "Q:cn07_57,cn07_59,cn07_58,cn07_60"

/-- Kernel-checked box `[1024, 1152]/NT × [8192, 12288]/NS`. -/
theorem cov393 : Cover gdata (1024) (1152) (8192) (12288) := by
  ballooning_box "Q:cn07_59,cn07_61,cn07_60,cn07_62"

/-- Kernel-checked box `[1152, 1280]/NT × [8192, 12288]/NS`. -/
theorem cov394 : Cover gdata (1152) (1280) (8192) (12288) := by
  ballooning_box "Q:cn07_61,cn07_63,cn07_62,cn07_64"

/-- Kernel-checked box `[1280, 1408]/NT × [8192, 12288]/NS`. -/
theorem cov395 : Cover gdata (1280) (1408) (8192) (12288) := by
  ballooning_box "Q:cn07_63,cn07_65,cn07_64,cn07_66"

/-- Kernel-checked box `[1408, 1536]/NT × [8192, 12288]/NS`. -/
theorem cov396 : Cover gdata (1408) (1536) (8192) (12288) := by
  ballooning_box "Q:cn07_65,cn07_67,cn07_66,cn07_68"

/-- Kernel-checked box `[1536, 1664]/NT × [8192, 12288]/NS`. -/
theorem cov397 : Cover gdata (1536) (1664) (8192) (12288) := by
  ballooning_box "Q:cn07_67,cn07_69,cn07_68,cn07_70"

/-- Kernel-checked box `[1664, 1792]/NT × [8192, 12288]/NS`. -/
theorem cov398 : Cover gdata (1664) (1792) (8192) (12288) := by
  ballooning_box "Q:cn07_69,cn07_71,cn07_70,cn07_72"

/-- Kernel-checked box `[1792, 2048]/NT × [8192, 10240]/NS`. -/
theorem cov399 : Cover gdata (1792) (2048) (8192) (10240) := by
  ballooning_box "Q:cn07_71,cn07_73,cn07_74,cn07_75"

/-- Kernel-checked box `[1792, 2048]/NT × [10240, 12288]/NS`. -/
theorem cov400 : Cover gdata (1792) (2048) (10240) (12288) := by
  ballooning_box "Q:cn07_74,cn07_75,cn07_72,cn07_76"

/-- Kernel-checked box `[2048, 2304]/NT × [8192, 10240]/NS`. -/
theorem cov401 : Cover gdata (2048) (2304) (8192) (10240) := by
  ballooning_box "Q:cn07_73,cn07_77,cn07_75,cn07_78"

/-- Kernel-checked box `[2048, 2304]/NT × [10240, 12288]/NS`. -/
theorem cov402 : Cover gdata (2048) (2304) (10240) (12288) := by
  ballooning_box "Q:cn07_75,cn07_78,cn07_76,cn07_79"

/-- Kernel-checked box `[2304, 2560]/NT × [8192, 10240]/NS`. -/
theorem cov403 : Cover gdata (2304) (2560) (8192) (10240) := by
  ballooning_box "Q:cn07_77,cn07_80,cn07_78,cn07_81"

/-- Kernel-checked box `[2304, 2560]/NT × [10240, 12288]/NS`. -/
theorem cov404 : Cover gdata (2304) (2560) (10240) (12288) := by
  ballooning_box "Q:cn07_78,cn07_81,cn07_79,cn07_82"

/-- Kernel-checked box `[2560, 2816]/NT × [8192, 10240]/NS`. -/
theorem cov405 : Cover gdata (2560) (2816) (8192) (10240) := by
  ballooning_box "Q:cn07_80,cn07_83,cn07_81,cn07_84"

/-- Kernel-checked box `[2560, 2816]/NT × [10240, 12288]/NS`. -/
theorem cov406 : Cover gdata (2560) (2816) (10240) (12288) := by
  ballooning_box "Q:cn07_81,cn07_84,cn07_82,cn07_85"

/-- Kernel-checked box `[2816, 3072]/NT × [8192, 10240]/NS`. -/
theorem cov407 : Cover gdata (2816) (3072) (8192) (10240) := by
  ballooning_box "Q:cn07_83,cn07_86,cn07_84,cn07_87"

/-- Kernel-checked box `[2816, 3072]/NT × [10240, 12288]/NS`. -/
theorem cov408 : Cover gdata (2816) (3072) (10240) (12288) := by
  ballooning_box "Q:cn07_84,cn07_87,cn07_85,cn07_88"

/-- Kernel-checked box `[3072, 3328]/NT × [8192, 10240]/NS`. -/
theorem cov409 : Cover gdata (3072) (3328) (8192) (10240) := by
  ballooning_box "Q:cn07_86,cn07_89,cn07_87,cn07_90"

/-- Kernel-checked box `[3072, 3328]/NT × [10240, 12288]/NS`. -/
theorem cov410 : Cover gdata (3072) (3328) (10240) (12288) := by
  ballooning_box "Q:cn07_87,cn07_90,cn07_88,cn07_91"

/-- Kernel-checked box `[3328, 3584]/NT × [8192, 10240]/NS`. -/
theorem cov411 : Cover gdata (3328) (3584) (8192) (10240) := by
  ballooning_box "Q:cn07_89,cn07_92,cn07_90,cn07_93"

/-- Kernel-checked box `[3328, 3584]/NT × [10240, 12288]/NS`. -/
theorem cov412 : Cover gdata (3328) (3584) (10240) (12288) := by
  ballooning_box "Q:cn07_90,cn07_93,cn07_91,cn07_94"

end PlasmaLean.Design.SolovevBallooning
