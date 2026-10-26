/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 3

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

/-- Kernel-checked corner test at `(-3328/NT, 2048/NS)`. -/
theorem cn03_0 : cornerOK gdata (-3328) (2048)
    [50030841, 21948896, 38586125, 10062508, 11074510, 1195433, 1028511] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 2048/NS)`. -/
theorem cn03_1 : cornerOK gdata (-3200) (2048)
    [51062187, 24913534, 39193314, 11341590, 11074510, 1348299, 1028511] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 3072/NS)`. -/
theorem cn03_2 : cornerOK gdata (-3328) (3072)
    [175670111, 99675477, 137064897, 43703691, 34834993, 5404388, 2814269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 3072/NS)`. -/
theorem cn03_3 : cornerOK gdata (-3200) (3072)
    [51062187, 24913534, 39193314, 11341590, 11074510, 1348299, 1028511] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 2048/NS)`. -/
theorem cn03_4 : cornerOK gdata (-3072) (2048)
    [51990278, 27764360, 39670694, 12547427, 11059171, 1493170, 1014248] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 3072/NS)`. -/
theorem cn03_5 : cornerOK gdata (-3072) (3072)
    [196395862, 127053888, 150845656, 55052191, 37229139, 6819240, 2922871] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 4096/NS)`. -/
theorem cn03_6 : cornerOK gdata (-3328) (4096)
    [175670111, 99675477, 137064897, 43703691, 34834993, 5404388, 2814269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 4096/NS)`. -/
theorem cn03_7 : cornerOK gdata (-3072) (4096)
    [196395862, 127053888, 150845656, 55052191, 37229139, 6819240, 2922871] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 2048/NS)`. -/
theorem cn03_8 : cornerOK gdata (-2944) (2048)
    [52825363, 30433685, 40029411, 13650623, 10990634, 1626217, 994044] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 3072/NS)`. -/
theorem cn03_9 : cornerOK gdata (-2944) (3072)
    [52825363, 30433685, 40029411, 13650623, 10990634, 1626217, 994044] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 2048/NS)`. -/
theorem cn03_10 : cornerOK gdata (-2816) (2048)
    [53592571, 32842743, 40234223, 14618647, 10866318, 1743242, 967900] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 3072/NS)`. -/
theorem cn03_11 : cornerOK gdata (-2816) (3072)
    [217586302, 152758495, 163439068, 65581797, 39089565, 8122082, 2979295] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 4096/NS)`. -/
theorem cn03_12 : cornerOK gdata (-2816) (4096)
    [217586302, 152758495, 163439068, 65581797, 39089565, 8122082, 2979295] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 2048/NS)`. -/
theorem cn03_13 : cornerOK gdata (-2688) (2048)
    [54320735, 34905584, 40244237, 15417539, 10682287, 1839815, 935760] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 3072/NS)`. -/
theorem cn03_14 : cornerOK gdata (-2688) (3072)
    [54320735, 34905584, 40244237, 15417539, 10682287, 1839815, 935760] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 2048/NS)`. -/
theorem cn03_15 : cornerOK gdata (-2560) (2048)
    [54839342, 36554711, 40298745, 16022907, 10464188, 1911927, 897784] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 3072/NS)`. -/
theorem cn03_16 : cornerOK gdata (-2560) (3072)
    [239401179, 173939063, 175882865, 74223177, 41187434, 9153506, 2985129] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 4096/NS)`. -/
theorem cn03_17 : cornerOK gdata (-2560) (4096)
    [239401179, 173939063, 175882865, 74223177, 41187434, 9153506, 2985129] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 2048/NS)`. -/
theorem cn03_18 : cornerOK gdata (-2432) (2048)
    [55102538, 37722473, 40298745, 16434756, 10247892, 1957214, 854848] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 3072/NS)`. -/
theorem cn03_19 : cornerOK gdata (-2432) (3072)
    [55102538, 37722473, 40298745, 16434756, 10247892, 1957214, 854848] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 2048/NS)`. -/
theorem cn03_20 : cornerOK gdata (-2304) (2048)
    [55102637, 38382707, 40227789, 16657932, 9979323, 1974199, 810574] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 3072/NS)`. -/
theorem cn03_21 : cornerOK gdata (-2304) (3072)
    [256925632, 187117585, 186301514, 79757487, 42617299, 9746597, 2985129] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 4096/NS)`. -/
theorem cn03_22 : cornerOK gdata (-2304) (4096)
    [256925632, 187117585, 186301514, 79757487, 42617299, 9746597, 2985129] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 2048/NS)`. -/
theorem cn03_23 : cornerOK gdata (-2176) (2048)
    [55102637, 38431979, 39970302, 16657932, 9662010, 1974199, 762496] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 3072/NS)`. -/
theorem cn03_24 : cornerOK gdata (-2176) (3072)
    [55102637, 38431979, 39970302, 16657932, 9662010, 1974199, 762496] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 2048/NS)`. -/
theorem cn03_25 : cornerOK gdata (-2048) (2048)
    [211417110, 152431150, 154573963, 67149082, 35234589, 7989449, 2411119] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 3072/NS)`. -/
theorem cn03_26 : cornerOK gdata (-2048) (3072)
    [265524576, 188434037, 190148830, 81471613, 42617299, 9746597, 2938400] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 4096/NS)`. -/
theorem cn03_27 : cornerOK gdata (-2048) (4096)
    [265524576, 188434037, 190148830, 81471613, 42617299, 9746597, 2938400] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 2048/NS)`. -/
theorem cn03_28 : cornerOK gdata (-1792) (2048)
    [221747247, 152431150, 154573963, 67149082, 35234589, 7989449, 2411119] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 3072/NS)`. -/
theorem cn03_29 : cornerOK gdata (-1792) (3072)
    [265524576, 188434037, 190148830, 81471613, 42553983, 9700608, 2798660] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 4096/NS)`. -/
theorem cn03_30 : cornerOK gdata (-1792) (4096)
    [265524576, 188434037, 190148830, 81471613, 42553983, 9700608, 2798660] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 2048/NS)`. -/
theorem cn03_31 : cornerOK gdata (-1664) (2048)
    [221747247, 148412476, 152552624, 62336535, 34093241, 6894838, 2320901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 4096/NS)`. -/
theorem cn03_32 : cornerOK gdata (-1664) (4096)
    [221747247, 148412476, 152552624, 62336535, 34093241, 6894838, 2320901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 2048/NS)`. -/
theorem cn03_33 : cornerOK gdata (-1536) (2048)
    [205078757, 139407559, 139976884, 57684869, 30753953, 6316537, 2049366] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 4096/NS)`. -/
theorem cn03_34 : cornerOK gdata (-1536) (4096)
    [205078757, 139407559, 139976884, 57684869, 30753953, 6316537, 2049366] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 2048/NS)`. -/
theorem cn03_35 : cornerOK gdata (-1408) (2048)
    [187849082, 129427247, 127395293, 52659171, 27519011, 5757758, 1800791] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 4096/NS)`. -/
theorem cn03_36 : cornerOK gdata (-1408) (4096)
    [187849082, 129427247, 127395293, 52659171, 27519011, 5757758, 1800791] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 2048/NS)`. -/
theorem cn03_37 : cornerOK gdata (-1280) (2048)
    [169656800, 118564606, 114426140, 47410900, 24319382, 5182969, 1569404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 4096/NS)`. -/
theorem cn03_38 : cornerOK gdata (-1280) (4096)
    [169656800, 118564606, 114426140, 47410900, 24319382, 5182969, 1569404] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 2048/NS)`. -/
theorem cn03_39 : cornerOK gdata (-1152) (2048)
    [150815993, 106900241, 101216516, 42034346, 21170924, 4591393, 1352574] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 4096/NS)`. -/
theorem cn03_40 : cornerOK gdata (-1152) (4096)
    [150815993, 106900241, 101216516, 42034346, 21170924, 4591393, 1352574] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 2048/NS)`. -/
theorem cn03_41 : cornerOK gdata (-1024) (2048)
    [132050072, 94828645, 88217540, 36685607, 18167718, 3999822, 1154196] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 4096/NS)`. -/
theorem cn03_42 : cornerOK gdata (-1024) (4096)
    [132050072, 94828645, 88217540, 36685607, 18167718, 3999822, 1154196] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 2048/NS)`. -/
theorem cn03_43 : cornerOK gdata (-896) (2048)
    [114317283, 82636017, 75638360, 31458255, 15346022, 3418851, 973690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 4096/NS)`. -/
theorem cn03_44 : cornerOK gdata (-896) (4096)
    [114317283, 82636017, 75638360, 31458255, 15346022, 3418851, 973690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 2048/NS)`. -/
theorem cn03_45 : cornerOK gdata (-768) (2048)
    [97798980, 70657614, 63863862, 26471328, 12805467, 2860073, 812580] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 4096/NS)`. -/
theorem cn03_46 : cornerOK gdata (-768) (4096)
    [97798980, 70657614, 63863862, 26471328, 12805467, 2860073, 812580] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 2048/NS)`. -/
theorem cn03_47 : cornerOK gdata (-640) (2048)
    [84750724, 59033214, 53256766, 21772893, 10706665, 2330836, 670080] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 4096/NS)`. -/
theorem cn03_48 : cornerOK gdata (-640) (4096)
    [84750724, 59033214, 53256766, 21772893, 10706665, 2330836, 670080] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 2048/NS)`. -/
theorem cn03_49 : cornerOK gdata (-512) (2048)
    [72939250, 47995496, 44295632, 17488745, 8895679, 1838816, 554564] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 4096/NS)`. -/
theorem cn03_50 : cornerOK gdata (-512) (4096)
    [72939250, 47995496, 44295632, 17488745, 8895679, 1838816, 554564] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 2048/NS)`. -/
theorem cn03_51 : cornerOK gdata (-384) (2048)
    [62782771, 37756829, 36697906, 13681031, 7396933, 1394155, 458253] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 4096/NS)`. -/
theorem cn03_52 : cornerOK gdata (-384) (4096)
    [62782771, 37756829, 36697906, 13681031, 7396933, 1394155, 458253] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 2048/NS)`. -/
theorem cn03_53 : cornerOK gdata (-256) (2048)
    [157802996, 74480590, 96349307, 30632017, 19331469, 3373557, 1122621] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 4096/NS)`. -/
theorem cn03_54 : cornerOK gdata (-256) (4096)
    [157802996, 74480590, 96349307, 30632017, 19331469, 3373557, 1122621] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 2048/NS)`. -/
theorem cn03_55 : cornerOK gdata (0) (2048)
    [157802996, 84659426, 98693412, 34345350, 19773759, 3724085, 1147165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 4096/NS)`. -/
theorem cn03_56 : cornerOK gdata (0) (4096)
    [157802996, 84659426, 98693412, 34345350, 19773759, 3724085, 1147165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 2048/NS)`. -/
theorem cn03_57 : cornerOK gdata (256) (2048)
    [157563233, 84659426, 98693412, 34345350, 19773759, 3724085, 1147165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(256/NT, 4096/NS)`. -/
theorem cn03_58 : cornerOK gdata (256) (4096)
    [157563233, 84659426, 98693412, 34345350, 19773759, 3724085, 1147165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 2048/NS)`. -/
theorem cn03_59 : cornerOK gdata (384) (2048)
    [57008038, 33310545, 33740273, 13019818, 6873448, 1374219, 399436] = true := by
  bl_cert

/-- Kernel-checked corner test at `(384/NT, 4096/NS)`. -/
theorem cn03_60 : cornerOK gdata (384) (4096)
    [57008038, 33310545, 33740273, 13019818, 6873448, 1374219, 399436] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 2048/NS)`. -/
theorem cn03_61 : cornerOK gdata (512) (2048)
    [64108316, 39918210, 39348809, 15546818, 8030115, 1700046, 491814] = true := by
  bl_cert

/-- Kernel-checked corner test at `(512/NT, 4096/NS)`. -/
theorem cn03_62 : cornerOK gdata (512) (4096)
    [64108316, 39918210, 39348809, 15546818, 8030115, 1700046, 491814] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 2048/NS)`. -/
theorem cn03_63 : cornerOK gdata (640) (2048)
    [72065501, 46434945, 45738163, 18327093, 9407066, 2089676, 599577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(640/NT, 4096/NS)`. -/
theorem cn03_64 : cornerOK gdata (640) (4096)
    [72065501, 46434945, 45738163, 18327093, 9407066, 2089676, 599577] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 2048/NS)`. -/
theorem cn03_65 : cornerOK gdata (768) (2048)
    [80342638, 52694545, 52673454, 21631265, 11084596, 2491482, 721595] = true := by
  bl_cert

/-- Kernel-checked corner test at `(768/NT, 4096/NS)`. -/
theorem cn03_66 : cornerOK gdata (768) (4096)
    [80342638, 52694545, 52673454, 21631265, 11084596, 2491482, 721595] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 2048/NS)`. -/
theorem cn03_67 : cornerOK gdata (896) (2048)
    [88708466, 58991769, 60455663, 25083839, 12936792, 2898614, 862876] = true := by
  bl_cert

/-- Kernel-checked corner test at `(896/NT, 4096/NS)`. -/
theorem cn03_68 : cornerOK gdata (896) (4096)
    [88708466, 58991769, 60455663, 25083839, 12936792, 2898614, 862876] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 2048/NS)`. -/
theorem cn03_69 : cornerOK gdata (1024) (2048)
    [97105850, 65374081, 68348468, 28544867, 14921149, 3302738, 1018380] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1024/NT, 4096/NS)`. -/
theorem cn03_70 : cornerOK gdata (1024) (4096)
    [97105850, 65374081, 68348468, 28544867, 14921149, 3302738, 1018380] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 2048/NS)`. -/
theorem cn03_71 : cornerOK gdata (1152) (2048)
    [105274843, 71366800, 76142266, 31916303, 17005001, 3693697, 1187602] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1152/NT, 4096/NS)`. -/
theorem cn03_72 : cornerOK gdata (1152) (4096)
    [105274843, 71366800, 76142266, 31916303, 17005001, 3693697, 1187602] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 2048/NS)`. -/
theorem cn03_73 : cornerOK gdata (1280) (2048)
    [113410049, 76851290, 83776952, 35116784, 19171060, 4062439, 1369340] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1280/NT, 4096/NS)`. -/
theorem cn03_74 : cornerOK gdata (1280) (4096)
    [113410049, 76851290, 83776952, 35116784, 19171060, 4062439, 1369340] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 2048/NS)`. -/
theorem cn03_75 : cornerOK gdata (1408) (2048)
    [121680055, 81855582, 91484760, 38129047, 21495634, 4407579, 1600304] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1408/NT, 4096/NS)`. -/
theorem cn03_76 : cornerOK gdata (1408) (4096)
    [121680055, 81855582, 91484760, 38129047, 21495634, 4407579, 1600304] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 2048/NS)`. -/
theorem cn03_77 : cornerOK gdata (1536) (2048)
    [129121155, 86537078, 99163892, 40838931, 23867516, 4718305, 1849051] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1536/NT, 4096/NS)`. -/
theorem cn03_78 : cornerOK gdata (1536) (4096)
    [129121155, 86537078, 99163892, 40838931, 23867516, 4718305, 1849051] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 2048/NS)`. -/
theorem cn03_79 : cornerOK gdata (1664) (2048)
    [135682988, 91607758, 107097561, 43647349, 26285267, 5065421, 2106934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1664/NT, 4096/NS)`. -/
theorem cn03_80 : cornerOK gdata (1664) (4096)
    [135682988, 91607758, 107097561, 43647349, 26285267, 5065421, 2106934] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 2048/NS)`. -/
theorem cn03_81 : cornerOK gdata (1792) (2048)
    [141295263, 95649958, 114504114, 45957276, 28629099, 5357683, 2366641] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1792/NT, 4096/NS)`. -/
theorem cn03_82 : cornerOK gdata (1792) (4096)
    [141295263, 95649958, 114504114, 45957276, 28629099, 5357683, 2366641] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 2048/NS)`. -/
theorem cn03_83 : cornerOK gdata (1920) (2048)
    [145876895, 98333415, 121221597, 47625570, 30883300, 5571646, 2626270] = true := by
  bl_cert

/-- Kernel-checked corner test at `(1920/NT, 4096/NS)`. -/
theorem cn03_84 : cornerOK gdata (1920) (4096)
    [145876895, 98333415, 121221597, 47625570, 30883300, 5571646, 2626270] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 2048/NS)`. -/
theorem cn03_85 : cornerOK gdata (2048) (2048)
    [149403450, 99558708, 127162012, 48585433, 32993035, 5699646, 2879189] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2048/NT, 4096/NS)`. -/
theorem cn03_86 : cornerOK gdata (2048) (4096)
    [149403450, 99558708, 127162012, 48585433, 32993035, 5699646, 2879189] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 2048/NS)`. -/
theorem cn03_87 : cornerOK gdata (2176) (2048)
    [152028957, 99558708, 132375799, 48838075, 34936717, 5741586, 3121222] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2176/NT, 4096/NS)`. -/
theorem cn03_88 : cornerOK gdata (2176) (4096)
    [152028957, 99558708, 132375799, 48838075, 34936717, 5741586, 3121222] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 2048/NS)`. -/
theorem cn03_89 : cornerOK gdata (2304) (2048)
    [153725001, 99371942, 136796692, 48838075, 36706053, 5741586, 3349836] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2304/NT, 4096/NS)`. -/
theorem cn03_90 : cornerOK gdata (2304) (4096)
    [153725001, 99371942, 136796692, 48838075, 36706053, 5741586, 3349836] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 2048/NS)`. -/
theorem cn03_91 : cornerOK gdata (2432) (2048)
    [154869606, 97819251, 140605328, 48399552, 38322646, 5700256, 3562946] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2432/NT, 4096/NS)`. -/
theorem cn03_92 : cornerOK gdata (2432) (4096)
    [154869606, 97819251, 140605328, 48399552, 38322646, 5700256, 3562946] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 2048/NS)`. -/
theorem cn03_93 : cornerOK gdata (2560) (2048)
    [155282224, 95148529, 143726183, 47360611, 39760725, 5585373, 3756788] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2560/NT, 4096/NS)`. -/
theorem cn03_94 : cornerOK gdata (2560) (4096)
    [155282224, 95148529, 143726183, 47360611, 39760725, 5585373, 3756788] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 2048/NS)`. -/
theorem cn03_95 : cornerOK gdata (2688) (2048)
    [155282224, 91348978, 146270501, 45712994, 41003664, 5396814, 3929313] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2688/NT, 4096/NS)`. -/
theorem cn03_96 : cornerOK gdata (2688) (4096)
    [155282224, 91348978, 146270501, 45712994, 41003664, 5396814, 3929313] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 2048/NS)`. -/
theorem cn03_97 : cornerOK gdata (2816) (2048)
    [155041416, 86498648, 148056893, 43503171, 42009280, 5141194, 4077805] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2816/NT, 4096/NS)`. -/
theorem cn03_98 : cornerOK gdata (2816) (4096)
    [155041416, 86498648, 148056893, 43503171, 42009280, 5141194, 4077805] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 2048/NS)`. -/
theorem cn03_99 : cornerOK gdata (2944) (2048)
    [154142774, 80735645, 148056893, 40802127, 42009280, 4826428, 4077805] = true := by
  bl_cert

/-- Kernel-checked corner test at `(2944/NT, 4096/NS)`. -/
theorem cn03_100 : cornerOK gdata (2944) (4096)
    [154142774, 80735645, 148056893, 40802127, 42009280, 4826428, 4077805] = true := by
  bl_cert

/-- Kernel-checked box `[-3328, -3200]/NT × [2048, 3072]/NS`. -/
theorem cov155 : Cover gdata (-3328) (-3200) (2048) (3072) := by
  ballooning_box "Q:cn03_0,cn03_1,cn03_2,cn03_3"

/-- Kernel-checked box `[-3200, -3072]/NT × [2048, 3072]/NS`. -/
theorem cov156 : Cover gdata (-3200) (-3072) (2048) (3072) := by
  ballooning_box "Q:cn03_1,cn03_4,cn03_3,cn03_5"

/-- Kernel-checked box `[-3328, -3072]/NT × [3072, 4096]/NS`. -/
theorem cov157 : Cover gdata (-3328) (-3072) (3072) (4096) := by
  ballooning_box "Q:cn03_2,cn03_5,cn03_6,cn03_7"

/-- Kernel-checked box `[-3072, -2944]/NT × [2048, 3072]/NS`. -/
theorem cov158 : Cover gdata (-3072) (-2944) (2048) (3072) := by
  ballooning_box "Q:cn03_4,cn03_8,cn03_5,cn03_9"

/-- Kernel-checked box `[-2944, -2816]/NT × [2048, 3072]/NS`. -/
theorem cov159 : Cover gdata (-2944) (-2816) (2048) (3072) := by
  ballooning_box "Q:cn03_8,cn03_10,cn03_9,cn03_11"

/-- Kernel-checked box `[-3072, -2816]/NT × [3072, 4096]/NS`. -/
theorem cov160 : Cover gdata (-3072) (-2816) (3072) (4096) := by
  ballooning_box "Q:cn03_5,cn03_11,cn03_7,cn03_12"

/-- Kernel-checked box `[-2816, -2688]/NT × [2048, 3072]/NS`. -/
theorem cov161 : Cover gdata (-2816) (-2688) (2048) (3072) := by
  ballooning_box "Q:cn03_10,cn03_13,cn03_11,cn03_14"

/-- Kernel-checked box `[-2688, -2560]/NT × [2048, 3072]/NS`. -/
theorem cov162 : Cover gdata (-2688) (-2560) (2048) (3072) := by
  ballooning_box "Q:cn03_13,cn03_15,cn03_14,cn03_16"

/-- Kernel-checked box `[-2816, -2560]/NT × [3072, 4096]/NS`. -/
theorem cov163 : Cover gdata (-2816) (-2560) (3072) (4096) := by
  ballooning_box "Q:cn03_11,cn03_16,cn03_12,cn03_17"

/-- Kernel-checked box `[-2560, -2432]/NT × [2048, 3072]/NS`. -/
theorem cov164 : Cover gdata (-2560) (-2432) (2048) (3072) := by
  ballooning_box "Q:cn03_15,cn03_18,cn03_16,cn03_19"

/-- Kernel-checked box `[-2432, -2304]/NT × [2048, 3072]/NS`. -/
theorem cov165 : Cover gdata (-2432) (-2304) (2048) (3072) := by
  ballooning_box "Q:cn03_18,cn03_20,cn03_19,cn03_21"

/-- Kernel-checked box `[-2560, -2304]/NT × [3072, 4096]/NS`. -/
theorem cov166 : Cover gdata (-2560) (-2304) (3072) (4096) := by
  ballooning_box "Q:cn03_16,cn03_21,cn03_17,cn03_22"

/-- Kernel-checked box `[-2304, -2176]/NT × [2048, 3072]/NS`. -/
theorem cov167 : Cover gdata (-2304) (-2176) (2048) (3072) := by
  ballooning_box "Q:cn03_20,cn03_23,cn03_21,cn03_24"

/-- Kernel-checked box `[-2176, -2048]/NT × [2048, 3072]/NS`. -/
theorem cov168 : Cover gdata (-2176) (-2048) (2048) (3072) := by
  ballooning_box "Q:cn03_23,cn03_25,cn03_24,cn03_26"

/-- Kernel-checked box `[-2304, -2048]/NT × [3072, 4096]/NS`. -/
theorem cov169 : Cover gdata (-2304) (-2048) (3072) (4096) := by
  ballooning_box "Q:cn03_21,cn03_26,cn03_22,cn03_27"

/-- Kernel-checked box `[-2048, -1792]/NT × [2048, 3072]/NS`. -/
theorem cov170 : Cover gdata (-2048) (-1792) (2048) (3072) := by
  ballooning_box "Q:cn03_25,cn03_28,cn03_26,cn03_29"

/-- Kernel-checked box `[-2048, -1792]/NT × [3072, 4096]/NS`. -/
theorem cov171 : Cover gdata (-2048) (-1792) (3072) (4096) := by
  ballooning_box "Q:cn03_26,cn03_29,cn03_27,cn03_30"

/-- Kernel-checked box `[-1792, -1664]/NT × [2048, 4096]/NS`. -/
theorem cov172 : Cover gdata (-1792) (-1664) (2048) (4096) := by
  ballooning_box "Q:cn03_28,cn03_31,cn03_30,cn03_32"

/-- Kernel-checked box `[-1664, -1536]/NT × [2048, 4096]/NS`. -/
theorem cov173 : Cover gdata (-1664) (-1536) (2048) (4096) := by
  ballooning_box "Q:cn03_31,cn03_33,cn03_32,cn03_34"

/-- Kernel-checked box `[-1536, -1408]/NT × [2048, 4096]/NS`. -/
theorem cov174 : Cover gdata (-1536) (-1408) (2048) (4096) := by
  ballooning_box "Q:cn03_33,cn03_35,cn03_34,cn03_36"

/-- Kernel-checked box `[-1408, -1280]/NT × [2048, 4096]/NS`. -/
theorem cov175 : Cover gdata (-1408) (-1280) (2048) (4096) := by
  ballooning_box "Q:cn03_35,cn03_37,cn03_36,cn03_38"

/-- Kernel-checked box `[-1280, -1152]/NT × [2048, 4096]/NS`. -/
theorem cov176 : Cover gdata (-1280) (-1152) (2048) (4096) := by
  ballooning_box "Q:cn03_37,cn03_39,cn03_38,cn03_40"

/-- Kernel-checked box `[-1152, -1024]/NT × [2048, 4096]/NS`. -/
theorem cov177 : Cover gdata (-1152) (-1024) (2048) (4096) := by
  ballooning_box "Q:cn03_39,cn03_41,cn03_40,cn03_42"

/-- Kernel-checked box `[-1024, -896]/NT × [2048, 4096]/NS`. -/
theorem cov178 : Cover gdata (-1024) (-896) (2048) (4096) := by
  ballooning_box "Q:cn03_41,cn03_43,cn03_42,cn03_44"

/-- Kernel-checked box `[-896, -768]/NT × [2048, 4096]/NS`. -/
theorem cov179 : Cover gdata (-896) (-768) (2048) (4096) := by
  ballooning_box "Q:cn03_43,cn03_45,cn03_44,cn03_46"

/-- Kernel-checked box `[-768, -640]/NT × [2048, 4096]/NS`. -/
theorem cov180 : Cover gdata (-768) (-640) (2048) (4096) := by
  ballooning_box "Q:cn03_45,cn03_47,cn03_46,cn03_48"

/-- Kernel-checked box `[-640, -512]/NT × [2048, 4096]/NS`. -/
theorem cov181 : Cover gdata (-640) (-512) (2048) (4096) := by
  ballooning_box "Q:cn03_47,cn03_49,cn03_48,cn03_50"

/-- Kernel-checked box `[-512, -384]/NT × [2048, 4096]/NS`. -/
theorem cov182 : Cover gdata (-512) (-384) (2048) (4096) := by
  ballooning_box "Q:cn03_49,cn03_51,cn03_50,cn03_52"

/-- Kernel-checked box `[-384, -256]/NT × [2048, 4096]/NS`. -/
theorem cov183 : Cover gdata (-384) (-256) (2048) (4096) := by
  ballooning_box "Q:cn03_51,cn03_53,cn03_52,cn03_54"

/-- Kernel-checked box `[-256, 0]/NT × [2048, 4096]/NS`. -/
theorem cov184 : Cover gdata (-256) (0) (2048) (4096) := by
  ballooning_box "Q:cn03_53,cn03_55,cn03_54,cn03_56"

/-- Kernel-checked box `[0, 256]/NT × [2048, 4096]/NS`. -/
theorem cov185 : Cover gdata (0) (256) (2048) (4096) := by
  ballooning_box "Q:cn03_55,cn03_57,cn03_56,cn03_58"

/-- Kernel-checked box `[256, 384]/NT × [2048, 4096]/NS`. -/
theorem cov186 : Cover gdata (256) (384) (2048) (4096) := by
  ballooning_box "Q:cn03_57,cn03_59,cn03_58,cn03_60"

/-- Kernel-checked box `[384, 512]/NT × [2048, 4096]/NS`. -/
theorem cov187 : Cover gdata (384) (512) (2048) (4096) := by
  ballooning_box "Q:cn03_59,cn03_61,cn03_60,cn03_62"

/-- Kernel-checked box `[512, 640]/NT × [2048, 4096]/NS`. -/
theorem cov188 : Cover gdata (512) (640) (2048) (4096) := by
  ballooning_box "Q:cn03_61,cn03_63,cn03_62,cn03_64"

/-- Kernel-checked box `[640, 768]/NT × [2048, 4096]/NS`. -/
theorem cov189 : Cover gdata (640) (768) (2048) (4096) := by
  ballooning_box "Q:cn03_63,cn03_65,cn03_64,cn03_66"

/-- Kernel-checked box `[768, 896]/NT × [2048, 4096]/NS`. -/
theorem cov190 : Cover gdata (768) (896) (2048) (4096) := by
  ballooning_box "Q:cn03_65,cn03_67,cn03_66,cn03_68"

/-- Kernel-checked box `[896, 1024]/NT × [2048, 4096]/NS`. -/
theorem cov191 : Cover gdata (896) (1024) (2048) (4096) := by
  ballooning_box "Q:cn03_67,cn03_69,cn03_68,cn03_70"

/-- Kernel-checked box `[1024, 1152]/NT × [2048, 4096]/NS`. -/
theorem cov192 : Cover gdata (1024) (1152) (2048) (4096) := by
  ballooning_box "Q:cn03_69,cn03_71,cn03_70,cn03_72"

/-- Kernel-checked box `[1152, 1280]/NT × [2048, 4096]/NS`. -/
theorem cov193 : Cover gdata (1152) (1280) (2048) (4096) := by
  ballooning_box "Q:cn03_71,cn03_73,cn03_72,cn03_74"

/-- Kernel-checked box `[1280, 1408]/NT × [2048, 4096]/NS`. -/
theorem cov194 : Cover gdata (1280) (1408) (2048) (4096) := by
  ballooning_box "Q:cn03_73,cn03_75,cn03_74,cn03_76"

/-- Kernel-checked box `[1408, 1536]/NT × [2048, 4096]/NS`. -/
theorem cov195 : Cover gdata (1408) (1536) (2048) (4096) := by
  ballooning_box "Q:cn03_75,cn03_77,cn03_76,cn03_78"

/-- Kernel-checked box `[1536, 1664]/NT × [2048, 4096]/NS`. -/
theorem cov196 : Cover gdata (1536) (1664) (2048) (4096) := by
  ballooning_box "Q:cn03_77,cn03_79,cn03_78,cn03_80"

/-- Kernel-checked box `[1664, 1792]/NT × [2048, 4096]/NS`. -/
theorem cov197 : Cover gdata (1664) (1792) (2048) (4096) := by
  ballooning_box "Q:cn03_79,cn03_81,cn03_80,cn03_82"

/-- Kernel-checked box `[1792, 1920]/NT × [2048, 4096]/NS`. -/
theorem cov198 : Cover gdata (1792) (1920) (2048) (4096) := by
  ballooning_box "Q:cn03_81,cn03_83,cn03_82,cn03_84"

/-- Kernel-checked box `[1920, 2048]/NT × [2048, 4096]/NS`. -/
theorem cov199 : Cover gdata (1920) (2048) (2048) (4096) := by
  ballooning_box "Q:cn03_83,cn03_85,cn03_84,cn03_86"

/-- Kernel-checked box `[2048, 2176]/NT × [2048, 4096]/NS`. -/
theorem cov200 : Cover gdata (2048) (2176) (2048) (4096) := by
  ballooning_box "Q:cn03_85,cn03_87,cn03_86,cn03_88"

/-- Kernel-checked box `[2176, 2304]/NT × [2048, 4096]/NS`. -/
theorem cov201 : Cover gdata (2176) (2304) (2048) (4096) := by
  ballooning_box "Q:cn03_87,cn03_89,cn03_88,cn03_90"

/-- Kernel-checked box `[2304, 2432]/NT × [2048, 4096]/NS`. -/
theorem cov202 : Cover gdata (2304) (2432) (2048) (4096) := by
  ballooning_box "Q:cn03_89,cn03_91,cn03_90,cn03_92"

/-- Kernel-checked box `[2432, 2560]/NT × [2048, 4096]/NS`. -/
theorem cov203 : Cover gdata (2432) (2560) (2048) (4096) := by
  ballooning_box "Q:cn03_91,cn03_93,cn03_92,cn03_94"

/-- Kernel-checked box `[2560, 2688]/NT × [2048, 4096]/NS`. -/
theorem cov204 : Cover gdata (2560) (2688) (2048) (4096) := by
  ballooning_box "Q:cn03_93,cn03_95,cn03_94,cn03_96"

/-- Kernel-checked box `[2688, 2816]/NT × [2048, 4096]/NS`. -/
theorem cov205 : Cover gdata (2688) (2816) (2048) (4096) := by
  ballooning_box "Q:cn03_95,cn03_97,cn03_96,cn03_98"

/-- Kernel-checked box `[2816, 2944]/NT × [2048, 4096]/NS`. -/
theorem cov206 : Cover gdata (2816) (2944) (2048) (4096) := by
  ballooning_box "Q:cn03_97,cn03_99,cn03_98,cn03_100"

end PlasmaLean.Design.SolovevBallooning
