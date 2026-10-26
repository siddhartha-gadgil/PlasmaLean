/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 9

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

/-- Kernel-checked corner test at `(-2176/NT, 12288/NS)`. -/
theorem cn09_0 : cornerOK gdata (-2176) (12288)
    [711386825, 321856681, 371417987, 110734425, 72442112, 12321554, 3855972] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 12288/NS)`. -/
theorem cn09_1 : cornerOK gdata (-2112) (12288)
    [711386825, 321856681, 371417987, 110734425, 72442112, 12321554, 3855972] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 14336/NS)`. -/
theorem cn09_2 : cornerOK gdata (-2176) (14336)
    [990582681, 420408008, 498216949, 137316479, 91907327, 15238905, 4390632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 14336/NS)`. -/
theorem cn09_3 : cornerOK gdata (-2112) (14336)
    [990582681, 420408008, 498216949, 137316479, 91907327, 15238905, 4390632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 16384/NS)`. -/
theorem cn09_4 : cornerOK gdata (-2176) (16384)
    [990582681, 420408008, 498216949, 137316479, 91907327, 15238905, 4390632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 16384/NS)`. -/
theorem cn09_5 : cornerOK gdata (-2112) (16384)
    [990582681, 420408008, 498216949, 137316479, 91907327, 15238905, 4390632] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 12288/NS)`. -/
theorem cn09_6 : cornerOK gdata (-2048) (12288)
    [1194579348, 578557517, 660485547, 212675277, 122645688, 23623930, 6118733] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 14336/NS)`. -/
theorem cn09_7 : cornerOK gdata (-2048) (14336)
    [1194579348, 578557517, 660485547, 212675277, 122645688, 23623930, 6118733] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 16384/NS)`. -/
theorem cn09_8 : cornerOK gdata (-2048) (16384)
    [930087212, 402199527, 470565070, 130942597, 86217259, 14539533, 4085670] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 12288/NS)`. -/
theorem cn09_9 : cornerOK gdata (-1920) (12288)
    [1194579348, 578557517, 660485547, 212675277, 122645688, 23623930, 6118733] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 14336/NS)`. -/
theorem cn09_10 : cornerOK gdata (-1920) (14336)
    [1504111586, 702687880, 811709805, 249947538, 141276289, 27732766, 6250407] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 14336/NS)`. -/
theorem cn09_11 : cornerOK gdata (-1984) (14336)
    [868381411, 382692919, 442336714, 124364410, 80478630, 13821822, 3788330] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 16384/NS)`. -/
theorem cn09_12 : cornerOK gdata (-1984) (16384)
    [868381411, 382692919, 442336714, 124364410, 80478630, 13821822, 3788330] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 16384/NS)`. -/
theorem cn09_13 : cornerOK gdata (-1920) (16384)
    [1504111586, 702687880, 811709805, 249947538, 141276289, 27732766, 6250407] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 12288/NS)`. -/
theorem cn09_14 : cornerOK gdata (-1792) (12288)
    [1077987662, 531990425, 601359111, 196237269, 110222529, 21801311, 5389947] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 14336/NS)`. -/
theorem cn09_15 : cornerOK gdata (-1792) (14336)
    [1504111586, 702687880, 811709805, 249947538, 141276289, 27732766, 6250407] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 16384/NS)`. -/
theorem cn09_16 : cornerOK gdata (-1792) (16384)
    [1504111586, 702687880, 811709805, 249947538, 141276289, 27732766, 6250407] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 12288/NS)`. -/
theorem cn09_17 : cornerOK gdata (-1664) (12288)
    [958054102, 479366465, 540267839, 179094182, 97857869, 19969267, 4693408] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 14336/NS)`. -/
theorem cn09_18 : cornerOK gdata (-1664) (14336)
    [1318667191, 626170136, 721127839, 225907699, 124205055, 25158339, 5415058] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 16384/NS)`. -/
theorem cn09_19 : cornerOK gdata (-1664) (16384)
    [1318667191, 626170136, 721127839, 225907699, 124205055, 25158339, 5415058] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 12288/NS)`. -/
theorem cn09_20 : cornerOK gdata (-1536) (12288)
    [838083390, 425039547, 479180506, 162309905, 85682399, 18053201, 4037210] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 14336/NS)`. -/
theorem cn09_21 : cornerOK gdata (-1536) (14336)
    [1137771511, 546462171, 631463744, 202998624, 107667043, 22538457, 4636935] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 16384/NS)`. -/
theorem cn09_22 : cornerOK gdata (-1536) (16384)
    [1137771511, 546462171, 631463744, 202998624, 107667043, 22538457, 4636935] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 12288/NS)`. -/
theorem cn09_23 : cornerOK gdata (-1408) (12288)
    [1921496693, 936104090, 1096822057, 338165889, 184330799, 37054021, 8408875] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 14336/NS)`. -/
theorem cn09_24 : cornerOK gdata (-1408) (14336)
    [967118990, 470393806, 544997741, 180053164, 91976995, 19949029, 3925202] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 16384/NS)`. -/
theorem cn09_25 : cornerOK gdata (-1408) (16384)
    [1921496693, 936104090, 1096822057, 338165889, 184330799, 37054021, 8408875] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 12288/NS)`. -/
theorem cn09_26 : cornerOK gdata (-1344) (12288)
    [1921496693, 936104090, 1096822057, 338165889, 184330799, 37054021, 8408875] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 16384/NS)`. -/
theorem cn09_27 : cornerOK gdata (-1344) (16384)
    [1921496693, 936104090, 1096822057, 338165889, 184330799, 37054021, 8408875] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 12288/NS)`. -/
theorem cn09_28 : cornerOK gdata (-1280) (12288)
    [1702747078, 829693101, 967662019, 301209163, 162763657, 32998998, 7332357] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 16384/NS)`. -/
theorem cn09_29 : cornerOK gdata (-1280) (16384)
    [1702747078, 829693101, 967662019, 301209163, 162763657, 32998998, 7332357] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 12288/NS)`. -/
theorem cn09_30 : cornerOK gdata (-1216) (12288)
    [1504592917, 730455201, 850299557, 266955138, 142995889, 29254210, 6355759] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 16384/NS)`. -/
theorem cn09_31 : cornerOK gdata (-1216) (16384)
    [1504592917, 730455201, 850299557, 266955138, 142995889, 29254210, 6355759] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 12288/NS)`. -/
theorem cn09_32 : cornerOK gdata (-1152) (12288)
    [1324010595, 639366433, 744361523, 235615374, 125216984, 25836829, 5487478] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 16384/NS)`. -/
theorem cn09_33 : cornerOK gdata (-1152) (16384)
    [1324010595, 639366433, 744361523, 235615374, 125216984, 25836829, 5487478] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 12288/NS)`. -/
theorem cn09_34 : cornerOK gdata (-1088) (12288)
    [1160150444, 555767366, 648832418, 207013323, 109200478, 22720375, 4714924] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 16384/NS)`. -/
theorem cn09_35 : cornerOK gdata (-1088) (16384)
    [1160150444, 555767366, 648832418, 207013323, 109200478, 22720375, 4714924] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 12288/NS)`. -/
theorem cn09_36 : cornerOK gdata (-1024) (12288)
    [1585262115, 774736854, 900452672, 301973966, 149704998, 32239874, 6260294] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 16384/NS)`. -/
theorem cn09_37 : cornerOK gdata (-1024) (16384)
    [1585262115, 774736854, 900452672, 301973966, 149704998, 32239874, 6260294] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 12288/NS)`. -/
theorem cn09_38 : cornerOK gdata (-896) (12288)
    [1585262115, 774736854, 900452672, 301973966, 149704998, 32239874, 6260294] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 16384/NS)`. -/
theorem cn09_39 : cornerOK gdata (-896) (16384)
    [1585262115, 774736854, 900452672, 301973966, 149704998, 32239874, 6260294] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 12288/NS)`. -/
theorem cn09_40 : cornerOK gdata (-768) (12288)
    [1205918237, 600592762, 685756868, 231409185, 114676709, 24675300, 4767231] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 16384/NS)`. -/
theorem cn09_41 : cornerOK gdata (-768) (16384)
    [1205918237, 600592762, 685756868, 231409185, 114676709, 24675300, 4767231] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 12288/NS)`. -/
theorem cn09_42 : cornerOK gdata (-640) (12288)
    [913970233, 473906991, 520896574, 174327557, 88070578, 18560682, 3739611] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 16384/NS)`. -/
theorem cn09_43 : cornerOK gdata (-640) (16384)
    [913970233, 473906991, 520896574, 174327557, 88070578, 18560682, 3739611] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 12288/NS)`. -/
theorem cn09_44 : cornerOK gdata (-512) (12288)
    [688422210, 367337657, 397146991, 128580596, 67390993, 13644089, 2963574] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 16384/NS)`. -/
theorem cn09_45 : cornerOK gdata (-512) (16384)
    [688422210, 367337657, 397146991, 128580596, 67390993, 13644089, 2963574] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 12288/NS)`. -/
theorem cn09_46 : cornerOK gdata (-384) (12288)
    [517436195, 288582249, 306261232, 98419675, 51923806, 10235018, 2391429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 16384/NS)`. -/
theorem cn09_47 : cornerOK gdata (-384) (16384)
    [517436195, 288582249, 306261232, 98419675, 51923806, 10235018, 2391429] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 12288/NS)`. -/
theorem cn09_48 : cornerOK gdata (-256) (12288)
    [1131369402, 672742418, 724312693, 261780956, 130912369, 26308514, 6904535] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 16384/NS)`. -/
theorem cn09_49 : cornerOK gdata (-256) (16384)
    [1131369402, 672742418, 724312693, 261780956, 130912369, 26308514, 6904535] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 12288/NS)`. -/
theorem cn09_50 : cornerOK gdata (0) (12288)
    [1131369402, 672742418, 724312693, 261780956, 130912369, 26308514, 6904535] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 16384/NS)`. -/
theorem cn09_51 : cornerOK gdata (0) (16384)
    [1131369402, 672742418, 724312693, 261780956, 130912369, 26308514, 6904535] = true := by
  bl_cert

/-- Kernel-checked corner test at `(128/NT, 12288/NS)`. -/
theorem cn09_52 : cornerOK gdata (128) (12288)
    [236002292, 166095208, 170781215, 66578116, 32359635, 6656392, 1669735] = true := by
  bl_cert

/-- Kernel-checked corner test at `(128/NT, 16384/NS)`. -/
theorem cn09_53 : cornerOK gdata (128) (16384)
    [236002292, 166095208, 170781215, 66578116, 32359635, 6656392, 1669735] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 12288/NS)`. -/
theorem cn09_54 : cornerOK gdata (256) (12288)
    [273864148, 202405569, 199017509, 81439272, 39325779, 8159167, 2118536] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 16384/NS)`. -/
theorem cn09_55 : cornerOK gdata (256) (16384)
    [273864148, 202405569, 199017509, 81439272, 39325779, 8159167, 2118536] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 12288/NS)`. -/
theorem cn09_56 : cornerOK gdata (384) (12288)
    [317945631, 241250431, 231659732, 97149583, 47771415, 9749314, 2772881] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 16384/NS)`. -/
theorem cn09_57 : cornerOK gdata (384) (16384)
    [317945631, 241250431, 231659732, 97149583, 47771415, 9749314, 2772881] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 12288/NS)`. -/
theorem cn09_58 : cornerOK gdata (512) (12288)
    [364251263, 281695604, 267839842, 113256992, 57458800, 11373281, 3591404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 16384/NS)`. -/
theorem cn09_59 : cornerOK gdata (512) (16384)
    [364251263, 281695604, 267839842, 113256992, 57458800, 11373281, 3591404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 12288/NS)`. -/
theorem cn09_60 : cornerOK gdata (640) (12288)
    [413546148, 323663484, 309096266, 130077546, 68813070, 13346133, 4568056] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 16384/NS)`. -/
theorem cn09_61 : cornerOK gdata (640) (16384)
    [413546148, 323663484, 309096266, 130077546, 68813070, 13346133, 4568056] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 12288/NS)`. -/
theorem cn09_62 : cornerOK gdata (768) (12288)
    [461987023, 365186424, 356256525, 148083887, 81316470, 15663765, 5662722] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 16384/NS)`. -/
theorem cn09_63 : cornerOK gdata (768) (16384)
    [461987023, 365186424, 356256525, 148083887, 81316470, 15663765, 5662722] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 12288/NS)`. -/
theorem cn09_64 : cornerOK gdata (896) (12288)
    [506928742, 404564707, 405663290, 169591209, 94908307, 18035730, 6852300] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 16384/NS)`. -/
theorem cn09_65 : cornerOK gdata (896) (16384)
    [506928742, 404564707, 405663290, 169591209, 94908307, 18035730, 6852300] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 12288/NS)`. -/
theorem cn09_66 : cornerOK gdata (1024) (12288)
    [548021477, 441073738, 455421418, 190891332, 109159093, 20407508, 8133303] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 16384/NS)`. -/
theorem cn09_67 : cornerOK gdata (1024) (16384)
    [548021477, 441073738, 455421418, 190891332, 109159093, 20407508, 8133303] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 12288/NS)`. -/
theorem cn09_68 : cornerOK gdata (1152) (12288)
    [583896129, 473773920, 504267537, 211491245, 123799464, 22731928, 9494918] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 16384/NS)`. -/
theorem cn09_69 : cornerOK gdata (1152) (16384)
    [583896129, 473773920, 504267537, 211491245, 123799464, 22731928, 9494918] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 12288/NS)`. -/
theorem cn09_70 : cornerOK gdata (1280) (12288)
    [614121990, 502334211, 551296887, 231394777, 138611236, 24959686, 10917200] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 16384/NS)`. -/
theorem cn09_71 : cornerOK gdata (1280) (16384)
    [614121990, 502334211, 551296887, 231394777, 138611236, 24959686, 10917200] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 12288/NS)`. -/
theorem cn09_72 : cornerOK gdata (1408) (12288)
    [640704847, 531604442, 597411028, 251968900, 153612852, 27442642, 12376037] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 16384/NS)`. -/
theorem cn09_73 : cornerOK gdata (1408) (16384)
    [640704847, 531604442, 597411028, 251968900, 153612852, 27442642, 12376037] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 12288/NS)`. -/
theorem cn09_74 : cornerOK gdata (1536) (12288)
    [661473678, 557702741, 640396881, 270024388, 168386713, 29658367, 14031223] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 16384/NS)`. -/
theorem cn09_75 : cornerOK gdata (1536) (16384)
    [661473678, 557702741, 640396881, 270024388, 168386713, 29658367, 14031223] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 12288/NS)`. -/
theorem cn09_76 : cornerOK gdata (1664) (12288)
    [675393889, 577948689, 678520216, 284547960, 182281546, 31477428, 15903542] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 16384/NS)`. -/
theorem cn09_77 : cornerOK gdata (1664) (16384)
    [675393889, 577948689, 678520216, 284547960, 182281546, 31477428, 15903542] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 12288/NS)`. -/
theorem cn09_78 : cornerOK gdata (1792) (12288)
    [683254210, 590701371, 711220220, 295325422, 195132241, 32852348, 17805272] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 16384/NS)`. -/
theorem cn09_79 : cornerOK gdata (1792) (16384)
    [683254210, 590701371, 711220220, 295325422, 195132241, 32852348, 17805272] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 12288/NS)`. -/
theorem cn09_80 : cornerOK gdata (1920) (12288)
    [686175440, 594723079, 738982696, 301425505, 208244032, 33694483, 19638202] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 16384/NS)`. -/
theorem cn09_81 : cornerOK gdata (1920) (16384)
    [686175440, 594723079, 738982696, 301425505, 208244032, 33694483, 19638202] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 12288/NS)`. -/
theorem cn09_82 : cornerOK gdata (2048) (12288)
    [686175440, 594723079, 762530129, 303573563, 223007249, 34044878, 21435482] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 16384/NS)`. -/
theorem cn09_83 : cornerOK gdata (2048) (16384)
    [686175440, 594723079, 762530129, 303573563, 223007249, 34044878, 21435482] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 12288/NS)`. -/
theorem cn09_84 : cornerOK gdata (2176) (12288)
    [684646084, 592365431, 781060581, 303573563, 236383162, 34044878, 23136607] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 16384/NS)`. -/
theorem cn09_85 : cornerOK gdata (2176) (16384)
    [684646084, 592365431, 781060581, 303573563, 236383162, 34044878, 23136607] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 12288/NS)`. -/
theorem cn09_86 : cornerOK gdata (2304) (12288)
    [678717499, 582440962, 781060581, 301249505, 236383162, 33867298, 23136607] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 16384/NS)`. -/
theorem cn09_87 : cornerOK gdata (2304) (16384)
    [678717499, 582440962, 781060581, 301249505, 236383162, 34910707, 23136607] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 12288/NS)`. -/
theorem cn09_88 : cornerOK gdata (2560) (12288)
    [513946356, 519164099, 586707030, 253801345, 172787408, 30888150, 15849308] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 14336/NS)`. -/
theorem cn09_89 : cornerOK gdata (2304) (14336)
    [542924463, 575426064, 651903297, 286092302, 195332075, 34910707, 18121402] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 14336/NS)`. -/
theorem cn09_90 : cornerOK gdata (2560) (14336)
    [542924463, 575426064, 651903297, 286092302, 195332075, 34910707, 18121402] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 16384/NS)`. -/
theorem cn09_91 : cornerOK gdata (2560) (16384)
    [542924463, 575426064, 651903297, 286092302, 195332075, 34910707, 18121402] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 12288/NS)`. -/
theorem cn09_92 : cornerOK gdata (2816) (12288)
    [437482398, 427757586, 526648229, 212341936, 160741815, 25915603, 15281611] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 14336/NS)`. -/
theorem cn09_93 : cornerOK gdata (2816) (14336)
    [455195655, 468528393, 577638029, 236585053, 179407831, 28961933, 17237976] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 16384/NS)`. -/
theorem cn09_94 : cornerOK gdata (2816) (16384)
    [455195655, 468528393, 577638029, 236585053, 179407831, 28961933, 17237976] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 12288/NS)`. -/
theorem cn09_95 : cornerOK gdata (3072) (12288)
    [370700641, 338441296, 470758127, 170408209, 148099181, 20826558, 14488807] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3072/NT, 14336/NS)`. -/
theorem cn09_96 : cornerOK gdata (3072) (14336)
    [370700641, 338441296, 470758127, 170408209, 148099181, 20826558, 14488807] = true := by
  bl_cert

/-- Kernel-checked box `[-2176, -2112]/NT × [12288, 14336]/NS`. -/
theorem cov465 : Cover gdata (-2176) (-2112) (12288) (14336) := by
  ballooning_box "Q:cn09_0,cn09_1,cn09_2,cn09_3"

/-- Kernel-checked box `[-2176, -2112]/NT × [14336, 16384]/NS`. -/
theorem cov466 : Cover gdata (-2176) (-2112) (14336) (16384) := by
  ballooning_box "Q:cn09_2,cn09_3,cn09_4,cn09_5"

/-- Kernel-checked box `[-2112, -2048]/NT × [12288, 14336]/NS`. -/
theorem cov467 : Cover gdata (-2112) (-2048) (12288) (14336) := by
  ballooning_box "Q:cn09_1,cn09_6,cn09_3,cn09_7"

/-- Kernel-checked box `[-2112, -2048]/NT × [14336, 16384]/NS`. -/
theorem cov468 : Cover gdata (-2112) (-2048) (14336) (16384) := by
  ballooning_box "Q:cn09_3,cn09_7,cn09_5,cn09_8"

/-- Kernel-checked box `[-2048, -1920]/NT × [12288, 14336]/NS`. -/
theorem cov469 : Cover gdata (-2048) (-1920) (12288) (14336) := by
  ballooning_box "Q:cn09_6,cn09_9,cn09_7,cn09_10"

/-- Kernel-checked box `[-2048, -1984]/NT × [14336, 16384]/NS`. -/
theorem cov470 : Cover gdata (-2048) (-1984) (14336) (16384) := by
  ballooning_box "Q:cn09_7,cn09_11,cn09_8,cn09_12"

/-- Kernel-checked box `[-1984, -1920]/NT × [14336, 16384]/NS`. -/
theorem cov471 : Cover gdata (-1984) (-1920) (14336) (16384) := by
  ballooning_box "Q:cn09_11,cn09_10,cn09_12,cn09_13"

/-- Kernel-checked box `[-1920, -1792]/NT × [12288, 14336]/NS`. -/
theorem cov472 : Cover gdata (-1920) (-1792) (12288) (14336) := by
  ballooning_box "Q:cn09_9,cn09_14,cn09_10,cn09_15"

/-- Kernel-checked box `[-1920, -1792]/NT × [14336, 16384]/NS`. -/
theorem cov473 : Cover gdata (-1920) (-1792) (14336) (16384) := by
  ballooning_box "Q:cn09_10,cn09_15,cn09_13,cn09_16"

/-- Kernel-checked box `[-1792, -1664]/NT × [12288, 14336]/NS`. -/
theorem cov474 : Cover gdata (-1792) (-1664) (12288) (14336) := by
  ballooning_box "Q:cn09_14,cn09_17,cn09_15,cn09_18"

/-- Kernel-checked box `[-1792, -1664]/NT × [14336, 16384]/NS`. -/
theorem cov475 : Cover gdata (-1792) (-1664) (14336) (16384) := by
  ballooning_box "Q:cn09_15,cn09_18,cn09_16,cn09_19"

/-- Kernel-checked box `[-1664, -1536]/NT × [12288, 14336]/NS`. -/
theorem cov476 : Cover gdata (-1664) (-1536) (12288) (14336) := by
  ballooning_box "Q:cn09_17,cn09_20,cn09_18,cn09_21"

/-- Kernel-checked box `[-1664, -1536]/NT × [14336, 16384]/NS`. -/
theorem cov477 : Cover gdata (-1664) (-1536) (14336) (16384) := by
  ballooning_box "Q:cn09_18,cn09_21,cn09_19,cn09_22"

/-- Kernel-checked box `[-1536, -1408]/NT × [12288, 14336]/NS`. -/
theorem cov478 : Cover gdata (-1536) (-1408) (12288) (14336) := by
  ballooning_box "Q:cn09_20,cn09_23,cn09_21,cn09_24"

/-- Kernel-checked box `[-1536, -1408]/NT × [14336, 16384]/NS`. -/
theorem cov479 : Cover gdata (-1536) (-1408) (14336) (16384) := by
  ballooning_box "Q:cn09_21,cn09_24,cn09_22,cn09_25"

/-- Kernel-checked box `[-1408, -1344]/NT × [12288, 16384]/NS`. -/
theorem cov480 : Cover gdata (-1408) (-1344) (12288) (16384) := by
  ballooning_box "Q:cn09_23,cn09_26,cn09_25,cn09_27"

/-- Kernel-checked box `[-1344, -1280]/NT × [12288, 16384]/NS`. -/
theorem cov481 : Cover gdata (-1344) (-1280) (12288) (16384) := by
  ballooning_box "Q:cn09_26,cn09_28,cn09_27,cn09_29"

/-- Kernel-checked box `[-1280, -1216]/NT × [12288, 16384]/NS`. -/
theorem cov482 : Cover gdata (-1280) (-1216) (12288) (16384) := by
  ballooning_box "Q:cn09_28,cn09_30,cn09_29,cn09_31"

/-- Kernel-checked box `[-1216, -1152]/NT × [12288, 16384]/NS`. -/
theorem cov483 : Cover gdata (-1216) (-1152) (12288) (16384) := by
  ballooning_box "Q:cn09_30,cn09_32,cn09_31,cn09_33"

/-- Kernel-checked box `[-1152, -1088]/NT × [12288, 16384]/NS`. -/
theorem cov484 : Cover gdata (-1152) (-1088) (12288) (16384) := by
  ballooning_box "Q:cn09_32,cn09_34,cn09_33,cn09_35"

/-- Kernel-checked box `[-1088, -1024]/NT × [12288, 16384]/NS`. -/
theorem cov485 : Cover gdata (-1088) (-1024) (12288) (16384) := by
  ballooning_box "Q:cn09_34,cn09_36,cn09_35,cn09_37"

/-- Kernel-checked box `[-1024, -896]/NT × [12288, 16384]/NS`. -/
theorem cov486 : Cover gdata (-1024) (-896) (12288) (16384) := by
  ballooning_box "Q:cn09_36,cn09_38,cn09_37,cn09_39"

/-- Kernel-checked box `[-896, -768]/NT × [12288, 16384]/NS`. -/
theorem cov487 : Cover gdata (-896) (-768) (12288) (16384) := by
  ballooning_box "Q:cn09_38,cn09_40,cn09_39,cn09_41"

/-- Kernel-checked box `[-768, -640]/NT × [12288, 16384]/NS`. -/
theorem cov488 : Cover gdata (-768) (-640) (12288) (16384) := by
  ballooning_box "Q:cn09_40,cn09_42,cn09_41,cn09_43"

/-- Kernel-checked box `[-640, -512]/NT × [12288, 16384]/NS`. -/
theorem cov489 : Cover gdata (-640) (-512) (12288) (16384) := by
  ballooning_box "Q:cn09_42,cn09_44,cn09_43,cn09_45"

/-- Kernel-checked box `[-512, -384]/NT × [12288, 16384]/NS`. -/
theorem cov490 : Cover gdata (-512) (-384) (12288) (16384) := by
  ballooning_box "Q:cn09_44,cn09_46,cn09_45,cn09_47"

/-- Kernel-checked box `[-384, -256]/NT × [12288, 16384]/NS`. -/
theorem cov491 : Cover gdata (-384) (-256) (12288) (16384) := by
  ballooning_box "Q:cn09_46,cn09_48,cn09_47,cn09_49"

/-- Kernel-checked box `[-256, 0]/NT × [12288, 16384]/NS`. -/
theorem cov492 : Cover gdata (-256) (0) (12288) (16384) := by
  ballooning_box "Q:cn09_48,cn09_50,cn09_49,cn09_51"

/-- Kernel-checked box `[0, 128]/NT × [12288, 16384]/NS`. -/
theorem cov493 : Cover gdata (0) (128) (12288) (16384) := by
  ballooning_box "Q:cn09_50,cn09_52,cn09_51,cn09_53"

/-- Kernel-checked box `[128, 256]/NT × [12288, 16384]/NS`. -/
theorem cov494 : Cover gdata (128) (256) (12288) (16384) := by
  ballooning_box "Q:cn09_52,cn09_54,cn09_53,cn09_55"

/-- Kernel-checked box `[256, 384]/NT × [12288, 16384]/NS`. -/
theorem cov495 : Cover gdata (256) (384) (12288) (16384) := by
  ballooning_box "Q:cn09_54,cn09_56,cn09_55,cn09_57"

/-- Kernel-checked box `[384, 512]/NT × [12288, 16384]/NS`. -/
theorem cov496 : Cover gdata (384) (512) (12288) (16384) := by
  ballooning_box "Q:cn09_56,cn09_58,cn09_57,cn09_59"

/-- Kernel-checked box `[512, 640]/NT × [12288, 16384]/NS`. -/
theorem cov497 : Cover gdata (512) (640) (12288) (16384) := by
  ballooning_box "Q:cn09_58,cn09_60,cn09_59,cn09_61"

/-- Kernel-checked box `[640, 768]/NT × [12288, 16384]/NS`. -/
theorem cov498 : Cover gdata (640) (768) (12288) (16384) := by
  ballooning_box "Q:cn09_60,cn09_62,cn09_61,cn09_63"

/-- Kernel-checked box `[768, 896]/NT × [12288, 16384]/NS`. -/
theorem cov499 : Cover gdata (768) (896) (12288) (16384) := by
  ballooning_box "Q:cn09_62,cn09_64,cn09_63,cn09_65"

/-- Kernel-checked box `[896, 1024]/NT × [12288, 16384]/NS`. -/
theorem cov500 : Cover gdata (896) (1024) (12288) (16384) := by
  ballooning_box "Q:cn09_64,cn09_66,cn09_65,cn09_67"

/-- Kernel-checked box `[1024, 1152]/NT × [12288, 16384]/NS`. -/
theorem cov501 : Cover gdata (1024) (1152) (12288) (16384) := by
  ballooning_box "Q:cn09_66,cn09_68,cn09_67,cn09_69"

/-- Kernel-checked box `[1152, 1280]/NT × [12288, 16384]/NS`. -/
theorem cov502 : Cover gdata (1152) (1280) (12288) (16384) := by
  ballooning_box "Q:cn09_68,cn09_70,cn09_69,cn09_71"

/-- Kernel-checked box `[1280, 1408]/NT × [12288, 16384]/NS`. -/
theorem cov503 : Cover gdata (1280) (1408) (12288) (16384) := by
  ballooning_box "Q:cn09_70,cn09_72,cn09_71,cn09_73"

/-- Kernel-checked box `[1408, 1536]/NT × [12288, 16384]/NS`. -/
theorem cov504 : Cover gdata (1408) (1536) (12288) (16384) := by
  ballooning_box "Q:cn09_72,cn09_74,cn09_73,cn09_75"

/-- Kernel-checked box `[1536, 1664]/NT × [12288, 16384]/NS`. -/
theorem cov505 : Cover gdata (1536) (1664) (12288) (16384) := by
  ballooning_box "Q:cn09_74,cn09_76,cn09_75,cn09_77"

/-- Kernel-checked box `[1664, 1792]/NT × [12288, 16384]/NS`. -/
theorem cov506 : Cover gdata (1664) (1792) (12288) (16384) := by
  ballooning_box "Q:cn09_76,cn09_78,cn09_77,cn09_79"

/-- Kernel-checked box `[1792, 1920]/NT × [12288, 16384]/NS`. -/
theorem cov507 : Cover gdata (1792) (1920) (12288) (16384) := by
  ballooning_box "Q:cn09_78,cn09_80,cn09_79,cn09_81"

/-- Kernel-checked box `[1920, 2048]/NT × [12288, 16384]/NS`. -/
theorem cov508 : Cover gdata (1920) (2048) (12288) (16384) := by
  ballooning_box "Q:cn09_80,cn09_82,cn09_81,cn09_83"

/-- Kernel-checked box `[2048, 2176]/NT × [12288, 16384]/NS`. -/
theorem cov509 : Cover gdata (2048) (2176) (12288) (16384) := by
  ballooning_box "Q:cn09_82,cn09_84,cn09_83,cn09_85"

/-- Kernel-checked box `[2176, 2304]/NT × [12288, 16384]/NS`. -/
theorem cov510 : Cover gdata (2176) (2304) (12288) (16384) := by
  ballooning_box "Q:cn09_84,cn09_86,cn09_85,cn09_87"

/-- Kernel-checked box `[2304, 2560]/NT × [12288, 14336]/NS`. -/
theorem cov511 : Cover gdata (2304) (2560) (12288) (14336) := by
  ballooning_box "Q:cn09_86,cn09_88,cn09_89,cn09_90"

/-- Kernel-checked box `[2304, 2560]/NT × [14336, 16384]/NS`. -/
theorem cov512 : Cover gdata (2304) (2560) (14336) (16384) := by
  ballooning_box "Q:cn09_89,cn09_90,cn09_87,cn09_91"

/-- Kernel-checked box `[2560, 2816]/NT × [12288, 14336]/NS`. -/
theorem cov513 : Cover gdata (2560) (2816) (12288) (14336) := by
  ballooning_box "Q:cn09_88,cn09_92,cn09_90,cn09_93"

/-- Kernel-checked box `[2560, 2816]/NT × [14336, 16384]/NS`. -/
theorem cov514 : Cover gdata (2560) (2816) (14336) (16384) := by
  ballooning_box "Q:cn09_90,cn09_93,cn09_91,cn09_94"

/-- Kernel-checked box `[2816, 3072]/NT × [12288, 14336]/NS`. -/
theorem cov515 : Cover gdata (2816) (3072) (12288) (14336) := by
  ballooning_box "Q:cn09_92,cn09_95,cn09_93,cn09_96"

end PlasmaLean.Design.SolovevBallooning
