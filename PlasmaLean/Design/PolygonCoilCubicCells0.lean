/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicLines00
public import PlasmaLean.Design.PolygonCoilCubicLines01
public import PlasmaLean.Design.PolygonCoilCubicLines02
public import PlasmaLean.Design.PolygonCoilCubicLines03
public import PlasmaLean.Design.PolygonCoilCubicFrontier

/-!
# Cubic frontier certificate: the cells and the cover of face 0

* `rowCF_i`: kernel evaluation (`decide +kernel`) of `cellsRow4` on the records of the grid lines
  `i, …, i+3` of face `F` (one evaluation per row keeps the kernel memory small);
* `cellsCF`: all cells of the face pass (`cellsAll4`, assembled from the rows);
* `linesC_F`, `rowsC_F`: the facts certified by the line checks `lCF_k` (`lineOut4_sound`);
* `coverC_F`, `faceCovC_F`: the certified bound on the face (`face_sound`).
-/

public section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator Set Real

/-- The line records of face 0. -/
@[expose]
def dataC0 : List (List CRec) := [dC0_0, dC0_1, dC0_2, dC0_3, dC0_4, dC0_5, dC0_6, dC0_7, dC0_8,
    dC0_9, dC0_10, dC0_11, dC0_12, dC0_13, dC0_14, dC0_15, dC0_16, dC0_17, dC0_18, dC0_19, dC0_20,
    dC0_21, dC0_22, dC0_23, dC0_24, dC0_25, dC0_26, dC0_27, dC0_28, dC0_29, dC0_30, dC0_31, dC0_32,
    dC0_33, dC0_34, dC0_35, dC0_36, dC0_37, dC0_38, dC0_39, dC0_40, dC0_41, dC0_42, dC0_43, dC0_44,
    dC0_45, dC0_46, dC0_47, dC0_48, dC0_49, dC0_50, dC0_51, dC0_52, dC0_53, dC0_54, dC0_55, dC0_56,
    dC0_57, dC0_58, dC0_59, dC0_60, dC0_61, dC0_62, dC0_63, dC0_64, dC0_65, dC0_66, dC0_67, dC0_68,
    dC0_69, dC0_70, dC0_71, dC0_72, dC0_73, dC0_74, dC0_75, dC0_76, dC0_77, dC0_78, dC0_79, dC0_80,
    dC0_81, dC0_82, dC0_83, dC0_84, dC0_85, dC0_86, dC0_87, dC0_88, dC0_89, dC0_90, dC0_91, dC0_92,
    dC0_93, dC0_94, dC0_95, dC0_96, dC0_97, dC0_98, dC0_99, dC0_100, dC0_101, dC0_102, dC0_103,
    dC0_104, dC0_105, dC0_106, dC0_107, dC0_108, dC0_109, dC0_110, dC0_111, dC0_112, dC0_113,
    dC0_114, dC0_115, dC0_116, dC0_117, dC0_118, dC0_119, dC0_120, dC0_121, dC0_122, dC0_123,
    dC0_124, dC0_125, dC0_126, dC0_127, dC0_128, dC0_129, dC0_130, dC0_131, dC0_132, dC0_133,
    dC0_134, dC0_135, dC0_136, dC0_137, dC0_138, dC0_139, dC0_140, dC0_141, dC0_142, dC0_143,
    dC0_144, dC0_145, dC0_146, dC0_147, dC0_148, dC0_149, dC0_150, dC0_151, dC0_152, dC0_153,
    dC0_154, dC0_155, dC0_156, dC0_157]

/-- The cells of row 0 of face 0 pass. -/
theorem rowC0_0 : cellsRow4 faceC0 etaC (-1727) (-1705) (-1683) (-1661) dC0_0 dC0_1 dC0_2 dC0_3
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 1 of face 0 pass. -/
theorem rowC0_1 : cellsRow4 faceC0 etaC (-1705) (-1683) (-1661) (-1639) dC0_1 dC0_2 dC0_3 dC0_4
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 2 of face 0 pass. -/
theorem rowC0_2 : cellsRow4 faceC0 etaC (-1683) (-1661) (-1639) (-1617) dC0_2 dC0_3 dC0_4 dC0_5
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 3 of face 0 pass. -/
theorem rowC0_3 : cellsRow4 faceC0 etaC (-1661) (-1639) (-1617) (-1595) dC0_3 dC0_4 dC0_5 dC0_6
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 4 of face 0 pass. -/
theorem rowC0_4 : cellsRow4 faceC0 etaC (-1639) (-1617) (-1595) (-1573) dC0_4 dC0_5 dC0_6 dC0_7
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 5 of face 0 pass. -/
theorem rowC0_5 : cellsRow4 faceC0 etaC (-1617) (-1595) (-1573) (-1551) dC0_5 dC0_6 dC0_7 dC0_8
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 6 of face 0 pass. -/
theorem rowC0_6 : cellsRow4 faceC0 etaC (-1595) (-1573) (-1551) (-1529) dC0_6 dC0_7 dC0_8 dC0_9
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 7 of face 0 pass. -/
theorem rowC0_7 : cellsRow4 faceC0 etaC (-1573) (-1551) (-1529) (-1507) dC0_7 dC0_8 dC0_9 dC0_10
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 8 of face 0 pass. -/
theorem rowC0_8 : cellsRow4 faceC0 etaC (-1551) (-1529) (-1507) (-1485) dC0_8 dC0_9 dC0_10 dC0_11
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 9 of face 0 pass. -/
theorem rowC0_9 : cellsRow4 faceC0 etaC (-1529) (-1507) (-1485) (-1463) dC0_9 dC0_10 dC0_11 dC0_12
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 10 of face 0 pass. -/
theorem rowC0_10 : cellsRow4 faceC0 etaC (-1507) (-1485) (-1463) (-1441) dC0_10 dC0_11 dC0_12 dC0_13
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 11 of face 0 pass. -/
theorem rowC0_11 : cellsRow4 faceC0 etaC (-1485) (-1463) (-1441) (-1419) dC0_11 dC0_12 dC0_13 dC0_14
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 12 of face 0 pass. -/
theorem rowC0_12 : cellsRow4 faceC0 etaC (-1463) (-1441) (-1419) (-1397) dC0_12 dC0_13 dC0_14 dC0_15
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 13 of face 0 pass. -/
theorem rowC0_13 : cellsRow4 faceC0 etaC (-1441) (-1419) (-1397) (-1375) dC0_13 dC0_14 dC0_15 dC0_16
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 14 of face 0 pass. -/
theorem rowC0_14 : cellsRow4 faceC0 etaC (-1419) (-1397) (-1375) (-1353) dC0_14 dC0_15 dC0_16 dC0_17
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 15 of face 0 pass. -/
theorem rowC0_15 : cellsRow4 faceC0 etaC (-1397) (-1375) (-1353) (-1331) dC0_15 dC0_16 dC0_17 dC0_18
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 16 of face 0 pass. -/
theorem rowC0_16 : cellsRow4 faceC0 etaC (-1375) (-1353) (-1331) (-1309) dC0_16 dC0_17 dC0_18 dC0_19
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 17 of face 0 pass. -/
theorem rowC0_17 : cellsRow4 faceC0 etaC (-1353) (-1331) (-1309) (-1287) dC0_17 dC0_18 dC0_19 dC0_20
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 18 of face 0 pass. -/
theorem rowC0_18 : cellsRow4 faceC0 etaC (-1331) (-1309) (-1287) (-1265) dC0_18 dC0_19 dC0_20 dC0_21
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 19 of face 0 pass. -/
theorem rowC0_19 : cellsRow4 faceC0 etaC (-1309) (-1287) (-1265) (-1243) dC0_19 dC0_20 dC0_21 dC0_22
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 20 of face 0 pass. -/
theorem rowC0_20 : cellsRow4 faceC0 etaC (-1287) (-1265) (-1243) (-1221) dC0_20 dC0_21 dC0_22 dC0_23
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 21 of face 0 pass. -/
theorem rowC0_21 : cellsRow4 faceC0 etaC (-1265) (-1243) (-1221) (-1199) dC0_21 dC0_22 dC0_23 dC0_24
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 22 of face 0 pass. -/
theorem rowC0_22 : cellsRow4 faceC0 etaC (-1243) (-1221) (-1199) (-1177) dC0_22 dC0_23 dC0_24 dC0_25
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 23 of face 0 pass. -/
theorem rowC0_23 : cellsRow4 faceC0 etaC (-1221) (-1199) (-1177) (-1155) dC0_23 dC0_24 dC0_25 dC0_26
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 24 of face 0 pass. -/
theorem rowC0_24 : cellsRow4 faceC0 etaC (-1199) (-1177) (-1155) (-1133) dC0_24 dC0_25 dC0_26 dC0_27
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 25 of face 0 pass. -/
theorem rowC0_25 : cellsRow4 faceC0 etaC (-1177) (-1155) (-1133) (-1111) dC0_25 dC0_26 dC0_27 dC0_28
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 26 of face 0 pass. -/
theorem rowC0_26 : cellsRow4 faceC0 etaC (-1155) (-1133) (-1111) (-1089) dC0_26 dC0_27 dC0_28 dC0_29
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 27 of face 0 pass. -/
theorem rowC0_27 : cellsRow4 faceC0 etaC (-1133) (-1111) (-1089) (-1067) dC0_27 dC0_28 dC0_29 dC0_30
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 28 of face 0 pass. -/
theorem rowC0_28 : cellsRow4 faceC0 etaC (-1111) (-1089) (-1067) (-1045) dC0_28 dC0_29 dC0_30 dC0_31
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 29 of face 0 pass. -/
theorem rowC0_29 : cellsRow4 faceC0 etaC (-1089) (-1067) (-1045) (-1023) dC0_29 dC0_30 dC0_31 dC0_32
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 30 of face 0 pass. -/
theorem rowC0_30 : cellsRow4 faceC0 etaC (-1067) (-1045) (-1023) (-1001) dC0_30 dC0_31 dC0_32 dC0_33
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 31 of face 0 pass. -/
theorem rowC0_31 : cellsRow4 faceC0 etaC (-1045) (-1023) (-1001) (-979) dC0_31 dC0_32 dC0_33 dC0_34
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 32 of face 0 pass. -/
theorem rowC0_32 : cellsRow4 faceC0 etaC (-1023) (-1001) (-979) (-957) dC0_32 dC0_33 dC0_34 dC0_35
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 33 of face 0 pass. -/
theorem rowC0_33 : cellsRow4 faceC0 etaC (-1001) (-979) (-957) (-935) dC0_33 dC0_34 dC0_35 dC0_36
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 34 of face 0 pass. -/
theorem rowC0_34 : cellsRow4 faceC0 etaC (-979) (-957) (-935) (-913) dC0_34 dC0_35 dC0_36 dC0_37
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 35 of face 0 pass. -/
theorem rowC0_35 : cellsRow4 faceC0 etaC (-957) (-935) (-913) (-891) dC0_35 dC0_36 dC0_37 dC0_38
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 36 of face 0 pass. -/
theorem rowC0_36 : cellsRow4 faceC0 etaC (-935) (-913) (-891) (-869) dC0_36 dC0_37 dC0_38 dC0_39
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 37 of face 0 pass. -/
theorem rowC0_37 : cellsRow4 faceC0 etaC (-913) (-891) (-869) (-847) dC0_37 dC0_38 dC0_39 dC0_40
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 38 of face 0 pass. -/
theorem rowC0_38 : cellsRow4 faceC0 etaC (-891) (-869) (-847) (-825) dC0_38 dC0_39 dC0_40 dC0_41
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 39 of face 0 pass. -/
theorem rowC0_39 : cellsRow4 faceC0 etaC (-869) (-847) (-825) (-803) dC0_39 dC0_40 dC0_41 dC0_42
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 40 of face 0 pass. -/
theorem rowC0_40 : cellsRow4 faceC0 etaC (-847) (-825) (-803) (-781) dC0_40 dC0_41 dC0_42 dC0_43
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 41 of face 0 pass. -/
theorem rowC0_41 : cellsRow4 faceC0 etaC (-825) (-803) (-781) (-759) dC0_41 dC0_42 dC0_43 dC0_44
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 42 of face 0 pass. -/
theorem rowC0_42 : cellsRow4 faceC0 etaC (-803) (-781) (-759) (-737) dC0_42 dC0_43 dC0_44 dC0_45
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 43 of face 0 pass. -/
theorem rowC0_43 : cellsRow4 faceC0 etaC (-781) (-759) (-737) (-715) dC0_43 dC0_44 dC0_45 dC0_46
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 44 of face 0 pass. -/
theorem rowC0_44 : cellsRow4 faceC0 etaC (-759) (-737) (-715) (-693) dC0_44 dC0_45 dC0_46 dC0_47
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 45 of face 0 pass. -/
theorem rowC0_45 : cellsRow4 faceC0 etaC (-737) (-715) (-693) (-671) dC0_45 dC0_46 dC0_47 dC0_48
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 46 of face 0 pass. -/
theorem rowC0_46 : cellsRow4 faceC0 etaC (-715) (-693) (-671) (-649) dC0_46 dC0_47 dC0_48 dC0_49
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 47 of face 0 pass. -/
theorem rowC0_47 : cellsRow4 faceC0 etaC (-693) (-671) (-649) (-627) dC0_47 dC0_48 dC0_49 dC0_50
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 48 of face 0 pass. -/
theorem rowC0_48 : cellsRow4 faceC0 etaC (-671) (-649) (-627) (-605) dC0_48 dC0_49 dC0_50 dC0_51
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 49 of face 0 pass. -/
theorem rowC0_49 : cellsRow4 faceC0 etaC (-649) (-627) (-605) (-583) dC0_49 dC0_50 dC0_51 dC0_52
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 50 of face 0 pass. -/
theorem rowC0_50 : cellsRow4 faceC0 etaC (-627) (-605) (-583) (-561) dC0_50 dC0_51 dC0_52 dC0_53
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 51 of face 0 pass. -/
theorem rowC0_51 : cellsRow4 faceC0 etaC (-605) (-583) (-561) (-539) dC0_51 dC0_52 dC0_53 dC0_54
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 52 of face 0 pass. -/
theorem rowC0_52 : cellsRow4 faceC0 etaC (-583) (-561) (-539) (-517) dC0_52 dC0_53 dC0_54 dC0_55
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 53 of face 0 pass. -/
theorem rowC0_53 : cellsRow4 faceC0 etaC (-561) (-539) (-517) (-495) dC0_53 dC0_54 dC0_55 dC0_56
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 54 of face 0 pass. -/
theorem rowC0_54 : cellsRow4 faceC0 etaC (-539) (-517) (-495) (-473) dC0_54 dC0_55 dC0_56 dC0_57
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 55 of face 0 pass. -/
theorem rowC0_55 : cellsRow4 faceC0 etaC (-517) (-495) (-473) (-451) dC0_55 dC0_56 dC0_57 dC0_58
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 56 of face 0 pass. -/
theorem rowC0_56 : cellsRow4 faceC0 etaC (-495) (-473) (-451) (-429) dC0_56 dC0_57 dC0_58 dC0_59
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 57 of face 0 pass. -/
theorem rowC0_57 : cellsRow4 faceC0 etaC (-473) (-451) (-429) (-407) dC0_57 dC0_58 dC0_59 dC0_60
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 58 of face 0 pass. -/
theorem rowC0_58 : cellsRow4 faceC0 etaC (-451) (-429) (-407) (-385) dC0_58 dC0_59 dC0_60 dC0_61
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 59 of face 0 pass. -/
theorem rowC0_59 : cellsRow4 faceC0 etaC (-429) (-407) (-385) (-363) dC0_59 dC0_60 dC0_61 dC0_62
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 60 of face 0 pass. -/
theorem rowC0_60 : cellsRow4 faceC0 etaC (-407) (-385) (-363) (-341) dC0_60 dC0_61 dC0_62 dC0_63
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 61 of face 0 pass. -/
theorem rowC0_61 : cellsRow4 faceC0 etaC (-385) (-363) (-341) (-319) dC0_61 dC0_62 dC0_63 dC0_64
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 62 of face 0 pass. -/
theorem rowC0_62 : cellsRow4 faceC0 etaC (-363) (-341) (-319) (-297) dC0_62 dC0_63 dC0_64 dC0_65
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 63 of face 0 pass. -/
theorem rowC0_63 : cellsRow4 faceC0 etaC (-341) (-319) (-297) (-275) dC0_63 dC0_64 dC0_65 dC0_66
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 64 of face 0 pass. -/
theorem rowC0_64 : cellsRow4 faceC0 etaC (-319) (-297) (-275) (-253) dC0_64 dC0_65 dC0_66 dC0_67
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 65 of face 0 pass. -/
theorem rowC0_65 : cellsRow4 faceC0 etaC (-297) (-275) (-253) (-231) dC0_65 dC0_66 dC0_67 dC0_68
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 66 of face 0 pass. -/
theorem rowC0_66 : cellsRow4 faceC0 etaC (-275) (-253) (-231) (-209) dC0_66 dC0_67 dC0_68 dC0_69
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 67 of face 0 pass. -/
theorem rowC0_67 : cellsRow4 faceC0 etaC (-253) (-231) (-209) (-187) dC0_67 dC0_68 dC0_69 dC0_70
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 68 of face 0 pass. -/
theorem rowC0_68 : cellsRow4 faceC0 etaC (-231) (-209) (-187) (-165) dC0_68 dC0_69 dC0_70 dC0_71
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 69 of face 0 pass. -/
theorem rowC0_69 : cellsRow4 faceC0 etaC (-209) (-187) (-165) (-143) dC0_69 dC0_70 dC0_71 dC0_72
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 70 of face 0 pass. -/
theorem rowC0_70 : cellsRow4 faceC0 etaC (-187) (-165) (-143) (-121) dC0_70 dC0_71 dC0_72 dC0_73
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 71 of face 0 pass. -/
theorem rowC0_71 : cellsRow4 faceC0 etaC (-165) (-143) (-121) (-99) dC0_71 dC0_72 dC0_73 dC0_74
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 72 of face 0 pass. -/
theorem rowC0_72 : cellsRow4 faceC0 etaC (-143) (-121) (-99) (-77) dC0_72 dC0_73 dC0_74 dC0_75
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 73 of face 0 pass. -/
theorem rowC0_73 : cellsRow4 faceC0 etaC (-121) (-99) (-77) (-55) dC0_73 dC0_74 dC0_75 dC0_76
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 74 of face 0 pass. -/
theorem rowC0_74 : cellsRow4 faceC0 etaC (-99) (-77) (-55) (-33) dC0_74 dC0_75 dC0_76 dC0_77
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 75 of face 0 pass. -/
theorem rowC0_75 : cellsRow4 faceC0 etaC (-77) (-55) (-33) (-11) dC0_75 dC0_76 dC0_77 dC0_78
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 76 of face 0 pass. -/
theorem rowC0_76 : cellsRow4 faceC0 etaC (-55) (-33) (-11) (11) dC0_76 dC0_77 dC0_78 dC0_79
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 77 of face 0 pass. -/
theorem rowC0_77 : cellsRow4 faceC0 etaC (-33) (-11) (11) (33) dC0_77 dC0_78 dC0_79 dC0_80 faceC0.wn
    = true := by
  decide +kernel

/-- The cells of row 78 of face 0 pass. -/
theorem rowC0_78 : cellsRow4 faceC0 etaC (-11) (11) (33) (55) dC0_78 dC0_79 dC0_80 dC0_81 faceC0.wn
    = true := by
  decide +kernel

/-- The cells of row 79 of face 0 pass. -/
theorem rowC0_79 : cellsRow4 faceC0 etaC (11) (33) (55) (77) dC0_79 dC0_80 dC0_81 dC0_82 faceC0.wn =
    true := by
  decide +kernel

/-- The cells of row 80 of face 0 pass. -/
theorem rowC0_80 : cellsRow4 faceC0 etaC (33) (55) (77) (99) dC0_80 dC0_81 dC0_82 dC0_83 faceC0.wn =
    true := by
  decide +kernel

/-- The cells of row 81 of face 0 pass. -/
theorem rowC0_81 : cellsRow4 faceC0 etaC (55) (77) (99) (121) dC0_81 dC0_82 dC0_83 dC0_84 faceC0.wn
    = true := by
  decide +kernel

/-- The cells of row 82 of face 0 pass. -/
theorem rowC0_82 : cellsRow4 faceC0 etaC (77) (99) (121) (143) dC0_82 dC0_83 dC0_84 dC0_85 faceC0.wn
    = true := by
  decide +kernel

/-- The cells of row 83 of face 0 pass. -/
theorem rowC0_83 : cellsRow4 faceC0 etaC (99) (121) (143) (165) dC0_83 dC0_84 dC0_85 dC0_86
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 84 of face 0 pass. -/
theorem rowC0_84 : cellsRow4 faceC0 etaC (121) (143) (165) (187) dC0_84 dC0_85 dC0_86 dC0_87
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 85 of face 0 pass. -/
theorem rowC0_85 : cellsRow4 faceC0 etaC (143) (165) (187) (209) dC0_85 dC0_86 dC0_87 dC0_88
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 86 of face 0 pass. -/
theorem rowC0_86 : cellsRow4 faceC0 etaC (165) (187) (209) (231) dC0_86 dC0_87 dC0_88 dC0_89
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 87 of face 0 pass. -/
theorem rowC0_87 : cellsRow4 faceC0 etaC (187) (209) (231) (253) dC0_87 dC0_88 dC0_89 dC0_90
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 88 of face 0 pass. -/
theorem rowC0_88 : cellsRow4 faceC0 etaC (209) (231) (253) (275) dC0_88 dC0_89 dC0_90 dC0_91
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 89 of face 0 pass. -/
theorem rowC0_89 : cellsRow4 faceC0 etaC (231) (253) (275) (297) dC0_89 dC0_90 dC0_91 dC0_92
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 90 of face 0 pass. -/
theorem rowC0_90 : cellsRow4 faceC0 etaC (253) (275) (297) (319) dC0_90 dC0_91 dC0_92 dC0_93
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 91 of face 0 pass. -/
theorem rowC0_91 : cellsRow4 faceC0 etaC (275) (297) (319) (341) dC0_91 dC0_92 dC0_93 dC0_94
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 92 of face 0 pass. -/
theorem rowC0_92 : cellsRow4 faceC0 etaC (297) (319) (341) (363) dC0_92 dC0_93 dC0_94 dC0_95
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 93 of face 0 pass. -/
theorem rowC0_93 : cellsRow4 faceC0 etaC (319) (341) (363) (385) dC0_93 dC0_94 dC0_95 dC0_96
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 94 of face 0 pass. -/
theorem rowC0_94 : cellsRow4 faceC0 etaC (341) (363) (385) (407) dC0_94 dC0_95 dC0_96 dC0_97
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 95 of face 0 pass. -/
theorem rowC0_95 : cellsRow4 faceC0 etaC (363) (385) (407) (429) dC0_95 dC0_96 dC0_97 dC0_98
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 96 of face 0 pass. -/
theorem rowC0_96 : cellsRow4 faceC0 etaC (385) (407) (429) (451) dC0_96 dC0_97 dC0_98 dC0_99
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 97 of face 0 pass. -/
theorem rowC0_97 : cellsRow4 faceC0 etaC (407) (429) (451) (473) dC0_97 dC0_98 dC0_99 dC0_100
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 98 of face 0 pass. -/
theorem rowC0_98 : cellsRow4 faceC0 etaC (429) (451) (473) (495) dC0_98 dC0_99 dC0_100 dC0_101
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 99 of face 0 pass. -/
theorem rowC0_99 : cellsRow4 faceC0 etaC (451) (473) (495) (517) dC0_99 dC0_100 dC0_101 dC0_102
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 100 of face 0 pass. -/
theorem rowC0_100 : cellsRow4 faceC0 etaC (473) (495) (517) (539) dC0_100 dC0_101 dC0_102 dC0_103
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 101 of face 0 pass. -/
theorem rowC0_101 : cellsRow4 faceC0 etaC (495) (517) (539) (561) dC0_101 dC0_102 dC0_103 dC0_104
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 102 of face 0 pass. -/
theorem rowC0_102 : cellsRow4 faceC0 etaC (517) (539) (561) (583) dC0_102 dC0_103 dC0_104 dC0_105
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 103 of face 0 pass. -/
theorem rowC0_103 : cellsRow4 faceC0 etaC (539) (561) (583) (605) dC0_103 dC0_104 dC0_105 dC0_106
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 104 of face 0 pass. -/
theorem rowC0_104 : cellsRow4 faceC0 etaC (561) (583) (605) (627) dC0_104 dC0_105 dC0_106 dC0_107
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 105 of face 0 pass. -/
theorem rowC0_105 : cellsRow4 faceC0 etaC (583) (605) (627) (649) dC0_105 dC0_106 dC0_107 dC0_108
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 106 of face 0 pass. -/
theorem rowC0_106 : cellsRow4 faceC0 etaC (605) (627) (649) (671) dC0_106 dC0_107 dC0_108 dC0_109
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 107 of face 0 pass. -/
theorem rowC0_107 : cellsRow4 faceC0 etaC (627) (649) (671) (693) dC0_107 dC0_108 dC0_109 dC0_110
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 108 of face 0 pass. -/
theorem rowC0_108 : cellsRow4 faceC0 etaC (649) (671) (693) (715) dC0_108 dC0_109 dC0_110 dC0_111
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 109 of face 0 pass. -/
theorem rowC0_109 : cellsRow4 faceC0 etaC (671) (693) (715) (737) dC0_109 dC0_110 dC0_111 dC0_112
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 110 of face 0 pass. -/
theorem rowC0_110 : cellsRow4 faceC0 etaC (693) (715) (737) (759) dC0_110 dC0_111 dC0_112 dC0_113
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 111 of face 0 pass. -/
theorem rowC0_111 : cellsRow4 faceC0 etaC (715) (737) (759) (781) dC0_111 dC0_112 dC0_113 dC0_114
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 112 of face 0 pass. -/
theorem rowC0_112 : cellsRow4 faceC0 etaC (737) (759) (781) (803) dC0_112 dC0_113 dC0_114 dC0_115
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 113 of face 0 pass. -/
theorem rowC0_113 : cellsRow4 faceC0 etaC (759) (781) (803) (825) dC0_113 dC0_114 dC0_115 dC0_116
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 114 of face 0 pass. -/
theorem rowC0_114 : cellsRow4 faceC0 etaC (781) (803) (825) (847) dC0_114 dC0_115 dC0_116 dC0_117
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 115 of face 0 pass. -/
theorem rowC0_115 : cellsRow4 faceC0 etaC (803) (825) (847) (869) dC0_115 dC0_116 dC0_117 dC0_118
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 116 of face 0 pass. -/
theorem rowC0_116 : cellsRow4 faceC0 etaC (825) (847) (869) (891) dC0_116 dC0_117 dC0_118 dC0_119
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 117 of face 0 pass. -/
theorem rowC0_117 : cellsRow4 faceC0 etaC (847) (869) (891) (913) dC0_117 dC0_118 dC0_119 dC0_120
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 118 of face 0 pass. -/
theorem rowC0_118 : cellsRow4 faceC0 etaC (869) (891) (913) (935) dC0_118 dC0_119 dC0_120 dC0_121
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 119 of face 0 pass. -/
theorem rowC0_119 : cellsRow4 faceC0 etaC (891) (913) (935) (957) dC0_119 dC0_120 dC0_121 dC0_122
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 120 of face 0 pass. -/
theorem rowC0_120 : cellsRow4 faceC0 etaC (913) (935) (957) (979) dC0_120 dC0_121 dC0_122 dC0_123
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 121 of face 0 pass. -/
theorem rowC0_121 : cellsRow4 faceC0 etaC (935) (957) (979) (1001) dC0_121 dC0_122 dC0_123 dC0_124
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 122 of face 0 pass. -/
theorem rowC0_122 : cellsRow4 faceC0 etaC (957) (979) (1001) (1023) dC0_122 dC0_123 dC0_124 dC0_125
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 123 of face 0 pass. -/
theorem rowC0_123 : cellsRow4 faceC0 etaC (979) (1001) (1023) (1045) dC0_123 dC0_124 dC0_125 dC0_126
    faceC0.wn = true := by
  decide +kernel

/-- The cells of row 124 of face 0 pass. -/
theorem rowC0_124 : cellsRow4 faceC0 etaC (1001) (1023) (1045) (1067) dC0_124 dC0_125 dC0_126
    dC0_127 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 125 of face 0 pass. -/
theorem rowC0_125 : cellsRow4 faceC0 etaC (1023) (1045) (1067) (1089) dC0_125 dC0_126 dC0_127
    dC0_128 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 126 of face 0 pass. -/
theorem rowC0_126 : cellsRow4 faceC0 etaC (1045) (1067) (1089) (1111) dC0_126 dC0_127 dC0_128
    dC0_129 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 127 of face 0 pass. -/
theorem rowC0_127 : cellsRow4 faceC0 etaC (1067) (1089) (1111) (1133) dC0_127 dC0_128 dC0_129
    dC0_130 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 128 of face 0 pass. -/
theorem rowC0_128 : cellsRow4 faceC0 etaC (1089) (1111) (1133) (1155) dC0_128 dC0_129 dC0_130
    dC0_131 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 129 of face 0 pass. -/
theorem rowC0_129 : cellsRow4 faceC0 etaC (1111) (1133) (1155) (1177) dC0_129 dC0_130 dC0_131
    dC0_132 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 130 of face 0 pass. -/
theorem rowC0_130 : cellsRow4 faceC0 etaC (1133) (1155) (1177) (1199) dC0_130 dC0_131 dC0_132
    dC0_133 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 131 of face 0 pass. -/
theorem rowC0_131 : cellsRow4 faceC0 etaC (1155) (1177) (1199) (1221) dC0_131 dC0_132 dC0_133
    dC0_134 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 132 of face 0 pass. -/
theorem rowC0_132 : cellsRow4 faceC0 etaC (1177) (1199) (1221) (1243) dC0_132 dC0_133 dC0_134
    dC0_135 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 133 of face 0 pass. -/
theorem rowC0_133 : cellsRow4 faceC0 etaC (1199) (1221) (1243) (1265) dC0_133 dC0_134 dC0_135
    dC0_136 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 134 of face 0 pass. -/
theorem rowC0_134 : cellsRow4 faceC0 etaC (1221) (1243) (1265) (1287) dC0_134 dC0_135 dC0_136
    dC0_137 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 135 of face 0 pass. -/
theorem rowC0_135 : cellsRow4 faceC0 etaC (1243) (1265) (1287) (1309) dC0_135 dC0_136 dC0_137
    dC0_138 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 136 of face 0 pass. -/
theorem rowC0_136 : cellsRow4 faceC0 etaC (1265) (1287) (1309) (1331) dC0_136 dC0_137 dC0_138
    dC0_139 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 137 of face 0 pass. -/
theorem rowC0_137 : cellsRow4 faceC0 etaC (1287) (1309) (1331) (1353) dC0_137 dC0_138 dC0_139
    dC0_140 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 138 of face 0 pass. -/
theorem rowC0_138 : cellsRow4 faceC0 etaC (1309) (1331) (1353) (1375) dC0_138 dC0_139 dC0_140
    dC0_141 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 139 of face 0 pass. -/
theorem rowC0_139 : cellsRow4 faceC0 etaC (1331) (1353) (1375) (1397) dC0_139 dC0_140 dC0_141
    dC0_142 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 140 of face 0 pass. -/
theorem rowC0_140 : cellsRow4 faceC0 etaC (1353) (1375) (1397) (1419) dC0_140 dC0_141 dC0_142
    dC0_143 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 141 of face 0 pass. -/
theorem rowC0_141 : cellsRow4 faceC0 etaC (1375) (1397) (1419) (1441) dC0_141 dC0_142 dC0_143
    dC0_144 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 142 of face 0 pass. -/
theorem rowC0_142 : cellsRow4 faceC0 etaC (1397) (1419) (1441) (1463) dC0_142 dC0_143 dC0_144
    dC0_145 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 143 of face 0 pass. -/
theorem rowC0_143 : cellsRow4 faceC0 etaC (1419) (1441) (1463) (1485) dC0_143 dC0_144 dC0_145
    dC0_146 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 144 of face 0 pass. -/
theorem rowC0_144 : cellsRow4 faceC0 etaC (1441) (1463) (1485) (1507) dC0_144 dC0_145 dC0_146
    dC0_147 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 145 of face 0 pass. -/
theorem rowC0_145 : cellsRow4 faceC0 etaC (1463) (1485) (1507) (1529) dC0_145 dC0_146 dC0_147
    dC0_148 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 146 of face 0 pass. -/
theorem rowC0_146 : cellsRow4 faceC0 etaC (1485) (1507) (1529) (1551) dC0_146 dC0_147 dC0_148
    dC0_149 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 147 of face 0 pass. -/
theorem rowC0_147 : cellsRow4 faceC0 etaC (1507) (1529) (1551) (1573) dC0_147 dC0_148 dC0_149
    dC0_150 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 148 of face 0 pass. -/
theorem rowC0_148 : cellsRow4 faceC0 etaC (1529) (1551) (1573) (1595) dC0_148 dC0_149 dC0_150
    dC0_151 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 149 of face 0 pass. -/
theorem rowC0_149 : cellsRow4 faceC0 etaC (1551) (1573) (1595) (1617) dC0_149 dC0_150 dC0_151
    dC0_152 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 150 of face 0 pass. -/
theorem rowC0_150 : cellsRow4 faceC0 etaC (1573) (1595) (1617) (1639) dC0_150 dC0_151 dC0_152
    dC0_153 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 151 of face 0 pass. -/
theorem rowC0_151 : cellsRow4 faceC0 etaC (1595) (1617) (1639) (1661) dC0_151 dC0_152 dC0_153
    dC0_154 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 152 of face 0 pass. -/
theorem rowC0_152 : cellsRow4 faceC0 etaC (1617) (1639) (1661) (1683) dC0_152 dC0_153 dC0_154
    dC0_155 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 153 of face 0 pass. -/
theorem rowC0_153 : cellsRow4 faceC0 etaC (1639) (1661) (1683) (1705) dC0_153 dC0_154 dC0_155
    dC0_156 faceC0.wn = true := by
  decide +kernel

/-- The cells of row 154 of face 0 pass. -/
theorem rowC0_154 : cellsRow4 faceC0 etaC (1661) (1683) (1705) (1727) dC0_154 dC0_155 dC0_156
    dC0_157 faceC0.wn = true := by
  decide +kernel

/-- **All cells of face 0 pass** (`η = 3540573·2⁻⁴⁰`). -/
theorem cellsC0 : cellsAll4 etaC faceC0 gridC0 dataC0 = true :=
cellsAll4_cons rowC0_0 <| cellsAll4_cons rowC0_1 <| cellsAll4_cons rowC0_2 <| cellsAll4_cons rowC0_3
    <| cellsAll4_cons rowC0_4 <| cellsAll4_cons rowC0_5 <| cellsAll4_cons rowC0_6 <| cellsAll4_cons
    rowC0_7 <| cellsAll4_cons rowC0_8 <| cellsAll4_cons rowC0_9 <| cellsAll4_cons rowC0_10 <|
    cellsAll4_cons rowC0_11 <| cellsAll4_cons rowC0_12 <| cellsAll4_cons rowC0_13 <| cellsAll4_cons
    rowC0_14 <| cellsAll4_cons rowC0_15 <| cellsAll4_cons rowC0_16 <| cellsAll4_cons rowC0_17 <|
    cellsAll4_cons rowC0_18 <| cellsAll4_cons rowC0_19 <| cellsAll4_cons rowC0_20 <| cellsAll4_cons
    rowC0_21 <| cellsAll4_cons rowC0_22 <| cellsAll4_cons rowC0_23 <| cellsAll4_cons rowC0_24 <|
    cellsAll4_cons rowC0_25 <| cellsAll4_cons rowC0_26 <| cellsAll4_cons rowC0_27 <| cellsAll4_cons
    rowC0_28 <| cellsAll4_cons rowC0_29 <| cellsAll4_cons rowC0_30 <| cellsAll4_cons rowC0_31 <|
    cellsAll4_cons rowC0_32 <| cellsAll4_cons rowC0_33 <| cellsAll4_cons rowC0_34 <| cellsAll4_cons
    rowC0_35 <| cellsAll4_cons rowC0_36 <| cellsAll4_cons rowC0_37 <| cellsAll4_cons rowC0_38 <|
    cellsAll4_cons rowC0_39 <| cellsAll4_cons rowC0_40 <| cellsAll4_cons rowC0_41 <| cellsAll4_cons
    rowC0_42 <| cellsAll4_cons rowC0_43 <| cellsAll4_cons rowC0_44 <| cellsAll4_cons rowC0_45 <|
    cellsAll4_cons rowC0_46 <| cellsAll4_cons rowC0_47 <| cellsAll4_cons rowC0_48 <| cellsAll4_cons
    rowC0_49 <| cellsAll4_cons rowC0_50 <| cellsAll4_cons rowC0_51 <| cellsAll4_cons rowC0_52 <|
    cellsAll4_cons rowC0_53 <| cellsAll4_cons rowC0_54 <| cellsAll4_cons rowC0_55 <| cellsAll4_cons
    rowC0_56 <| cellsAll4_cons rowC0_57 <| cellsAll4_cons rowC0_58 <| cellsAll4_cons rowC0_59 <|
    cellsAll4_cons rowC0_60 <| cellsAll4_cons rowC0_61 <| cellsAll4_cons rowC0_62 <| cellsAll4_cons
    rowC0_63 <| cellsAll4_cons rowC0_64 <| cellsAll4_cons rowC0_65 <| cellsAll4_cons rowC0_66 <|
    cellsAll4_cons rowC0_67 <| cellsAll4_cons rowC0_68 <| cellsAll4_cons rowC0_69 <| cellsAll4_cons
    rowC0_70 <| cellsAll4_cons rowC0_71 <| cellsAll4_cons rowC0_72 <| cellsAll4_cons rowC0_73 <|
    cellsAll4_cons rowC0_74 <| cellsAll4_cons rowC0_75 <| cellsAll4_cons rowC0_76 <| cellsAll4_cons
    rowC0_77 <| cellsAll4_cons rowC0_78 <| cellsAll4_cons rowC0_79 <| cellsAll4_cons rowC0_80 <|
    cellsAll4_cons rowC0_81 <| cellsAll4_cons rowC0_82 <| cellsAll4_cons rowC0_83 <| cellsAll4_cons
    rowC0_84 <| cellsAll4_cons rowC0_85 <| cellsAll4_cons rowC0_86 <| cellsAll4_cons rowC0_87 <|
    cellsAll4_cons rowC0_88 <| cellsAll4_cons rowC0_89 <| cellsAll4_cons rowC0_90 <| cellsAll4_cons
    rowC0_91 <| cellsAll4_cons rowC0_92 <| cellsAll4_cons rowC0_93 <| cellsAll4_cons rowC0_94 <|
    cellsAll4_cons rowC0_95 <| cellsAll4_cons rowC0_96 <| cellsAll4_cons rowC0_97 <| cellsAll4_cons
    rowC0_98 <| cellsAll4_cons rowC0_99 <| cellsAll4_cons rowC0_100 <| cellsAll4_cons rowC0_101 <|
    cellsAll4_cons rowC0_102 <| cellsAll4_cons rowC0_103 <| cellsAll4_cons rowC0_104 <|
    cellsAll4_cons rowC0_105 <| cellsAll4_cons rowC0_106 <| cellsAll4_cons rowC0_107 <|
    cellsAll4_cons rowC0_108 <| cellsAll4_cons rowC0_109 <| cellsAll4_cons rowC0_110 <|
    cellsAll4_cons rowC0_111 <| cellsAll4_cons rowC0_112 <| cellsAll4_cons rowC0_113 <|
    cellsAll4_cons rowC0_114 <| cellsAll4_cons rowC0_115 <| cellsAll4_cons rowC0_116 <|
    cellsAll4_cons rowC0_117 <| cellsAll4_cons rowC0_118 <| cellsAll4_cons rowC0_119 <|
    cellsAll4_cons rowC0_120 <| cellsAll4_cons rowC0_121 <| cellsAll4_cons rowC0_122 <|
    cellsAll4_cons rowC0_123 <| cellsAll4_cons rowC0_124 <| cellsAll4_cons rowC0_125 <|
    cellsAll4_cons rowC0_126 <| cellsAll4_cons rowC0_127 <| cellsAll4_cons rowC0_128 <|
    cellsAll4_cons rowC0_129 <| cellsAll4_cons rowC0_130 <| cellsAll4_cons rowC0_131 <|
    cellsAll4_cons rowC0_132 <| cellsAll4_cons rowC0_133 <| cellsAll4_cons rowC0_134 <|
    cellsAll4_cons rowC0_135 <| cellsAll4_cons rowC0_136 <| cellsAll4_cons rowC0_137 <|
    cellsAll4_cons rowC0_138 <| cellsAll4_cons rowC0_139 <| cellsAll4_cons rowC0_140 <|
    cellsAll4_cons rowC0_141 <| cellsAll4_cons rowC0_142 <| cellsAll4_cons rowC0_143 <|
    cellsAll4_cons rowC0_144 <| cellsAll4_cons rowC0_145 <| cellsAll4_cons rowC0_146 <|
    cellsAll4_cons rowC0_147 <| cellsAll4_cons rowC0_148 <| cellsAll4_cons rowC0_149 <|
    cellsAll4_cons rowC0_150 <| cellsAll4_cons rowC0_151 <| cellsAll4_cons rowC0_152 <|
    cellsAll4_cons rowC0_153 <| cellsAll4_cons rowC0_154 <| cellsAll4_end

/-- Face 0 carries the proved `hel` constants. -/
theorem face4OK_0 : Face4OK faceC0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [faceC0] <;> norm_num

/-- The line facts of face 0. -/
theorem linesC_0 : List.Forall₂ (fun m L => List.Forall₂ (LVal filsC faceC0 m) faceC0.wn L ∧
    QuadP (LW filsC faceC0 m) faceC0.wn L) gridC0 dataC0 :=
.cons (line_facts face4OK_0 lC0_0).1 <| .cons (line_facts face4OK_0 lC0_1).1 <| .cons (line_facts
    face4OK_0 lC0_2).1 <| .cons (line_facts face4OK_0 lC0_3).1 <| .cons (line_facts face4OK_0
    lC0_4).1 <| .cons (line_facts face4OK_0 lC0_5).1 <| .cons (line_facts face4OK_0 lC0_6).1 <|
    .cons (line_facts face4OK_0 lC0_7).1 <| .cons (line_facts face4OK_0 lC0_8).1 <| .cons
    (line_facts face4OK_0 lC0_9).1 <| .cons (line_facts face4OK_0 lC0_10).1 <| .cons (line_facts
    face4OK_0 lC0_11).1 <| .cons (line_facts face4OK_0 lC0_12).1 <| .cons (line_facts face4OK_0
    lC0_13).1 <| .cons (line_facts face4OK_0 lC0_14).1 <| .cons (line_facts face4OK_0 lC0_15).1 <|
    .cons (line_facts face4OK_0 lC0_16).1 <| .cons (line_facts face4OK_0 lC0_17).1 <| .cons
    (line_facts face4OK_0 lC0_18).1 <| .cons (line_facts face4OK_0 lC0_19).1 <| .cons (line_facts
    face4OK_0 lC0_20).1 <| .cons (line_facts face4OK_0 lC0_21).1 <| .cons (line_facts face4OK_0
    lC0_22).1 <| .cons (line_facts face4OK_0 lC0_23).1 <| .cons (line_facts face4OK_0 lC0_24).1 <|
    .cons (line_facts face4OK_0 lC0_25).1 <| .cons (line_facts face4OK_0 lC0_26).1 <| .cons
    (line_facts face4OK_0 lC0_27).1 <| .cons (line_facts face4OK_0 lC0_28).1 <| .cons (line_facts
    face4OK_0 lC0_29).1 <| .cons (line_facts face4OK_0 lC0_30).1 <| .cons (line_facts face4OK_0
    lC0_31).1 <| .cons (line_facts face4OK_0 lC0_32).1 <| .cons (line_facts face4OK_0 lC0_33).1 <|
    .cons (line_facts face4OK_0 lC0_34).1 <| .cons (line_facts face4OK_0 lC0_35).1 <| .cons
    (line_facts face4OK_0 lC0_36).1 <| .cons (line_facts face4OK_0 lC0_37).1 <| .cons (line_facts
    face4OK_0 lC0_38).1 <| .cons (line_facts face4OK_0 lC0_39).1 <| .cons (line_facts face4OK_0
    lC0_40).1 <| .cons (line_facts face4OK_0 lC0_41).1 <| .cons (line_facts face4OK_0 lC0_42).1 <|
    .cons (line_facts face4OK_0 lC0_43).1 <| .cons (line_facts face4OK_0 lC0_44).1 <| .cons
    (line_facts face4OK_0 lC0_45).1 <| .cons (line_facts face4OK_0 lC0_46).1 <| .cons (line_facts
    face4OK_0 lC0_47).1 <| .cons (line_facts face4OK_0 lC0_48).1 <| .cons (line_facts face4OK_0
    lC0_49).1 <| .cons (line_facts face4OK_0 lC0_50).1 <| .cons (line_facts face4OK_0 lC0_51).1 <|
    .cons (line_facts face4OK_0 lC0_52).1 <| .cons (line_facts face4OK_0 lC0_53).1 <| .cons
    (line_facts face4OK_0 lC0_54).1 <| .cons (line_facts face4OK_0 lC0_55).1 <| .cons (line_facts
    face4OK_0 lC0_56).1 <| .cons (line_facts face4OK_0 lC0_57).1 <| .cons (line_facts face4OK_0
    lC0_58).1 <| .cons (line_facts face4OK_0 lC0_59).1 <| .cons (line_facts face4OK_0 lC0_60).1 <|
    .cons (line_facts face4OK_0 lC0_61).1 <| .cons (line_facts face4OK_0 lC0_62).1 <| .cons
    (line_facts face4OK_0 lC0_63).1 <| .cons (line_facts face4OK_0 lC0_64).1 <| .cons (line_facts
    face4OK_0 lC0_65).1 <| .cons (line_facts face4OK_0 lC0_66).1 <| .cons (line_facts face4OK_0
    lC0_67).1 <| .cons (line_facts face4OK_0 lC0_68).1 <| .cons (line_facts face4OK_0 lC0_69).1 <|
    .cons (line_facts face4OK_0 lC0_70).1 <| .cons (line_facts face4OK_0 lC0_71).1 <| .cons
    (line_facts face4OK_0 lC0_72).1 <| .cons (line_facts face4OK_0 lC0_73).1 <| .cons (line_facts
    face4OK_0 lC0_74).1 <| .cons (line_facts face4OK_0 lC0_75).1 <| .cons (line_facts face4OK_0
    lC0_76).1 <| .cons (line_facts face4OK_0 lC0_77).1 <| .cons (line_facts face4OK_0 lC0_78).1 <|
    .cons (line_facts face4OK_0 lC0_79).1 <| .cons (line_facts face4OK_0 lC0_80).1 <| .cons
    (line_facts face4OK_0 lC0_81).1 <| .cons (line_facts face4OK_0 lC0_82).1 <| .cons (line_facts
    face4OK_0 lC0_83).1 <| .cons (line_facts face4OK_0 lC0_84).1 <| .cons (line_facts face4OK_0
    lC0_85).1 <| .cons (line_facts face4OK_0 lC0_86).1 <| .cons (line_facts face4OK_0 lC0_87).1 <|
    .cons (line_facts face4OK_0 lC0_88).1 <| .cons (line_facts face4OK_0 lC0_89).1 <| .cons
    (line_facts face4OK_0 lC0_90).1 <| .cons (line_facts face4OK_0 lC0_91).1 <| .cons (line_facts
    face4OK_0 lC0_92).1 <| .cons (line_facts face4OK_0 lC0_93).1 <| .cons (line_facts face4OK_0
    lC0_94).1 <| .cons (line_facts face4OK_0 lC0_95).1 <| .cons (line_facts face4OK_0 lC0_96).1 <|
    .cons (line_facts face4OK_0 lC0_97).1 <| .cons (line_facts face4OK_0 lC0_98).1 <| .cons
    (line_facts face4OK_0 lC0_99).1 <| .cons (line_facts face4OK_0 lC0_100).1 <| .cons (line_facts
    face4OK_0 lC0_101).1 <| .cons (line_facts face4OK_0 lC0_102).1 <| .cons (line_facts face4OK_0
    lC0_103).1 <| .cons (line_facts face4OK_0 lC0_104).1 <| .cons (line_facts face4OK_0 lC0_105).1
    <| .cons (line_facts face4OK_0 lC0_106).1 <| .cons (line_facts face4OK_0 lC0_107).1 <| .cons
    (line_facts face4OK_0 lC0_108).1 <| .cons (line_facts face4OK_0 lC0_109).1 <| .cons (line_facts
    face4OK_0 lC0_110).1 <| .cons (line_facts face4OK_0 lC0_111).1 <| .cons (line_facts face4OK_0
    lC0_112).1 <| .cons (line_facts face4OK_0 lC0_113).1 <| .cons (line_facts face4OK_0 lC0_114).1
    <| .cons (line_facts face4OK_0 lC0_115).1 <| .cons (line_facts face4OK_0 lC0_116).1 <| .cons
    (line_facts face4OK_0 lC0_117).1 <| .cons (line_facts face4OK_0 lC0_118).1 <| .cons (line_facts
    face4OK_0 lC0_119).1 <| .cons (line_facts face4OK_0 lC0_120).1 <| .cons (line_facts face4OK_0
    lC0_121).1 <| .cons (line_facts face4OK_0 lC0_122).1 <| .cons (line_facts face4OK_0 lC0_123).1
    <| .cons (line_facts face4OK_0 lC0_124).1 <| .cons (line_facts face4OK_0 lC0_125).1 <| .cons
    (line_facts face4OK_0 lC0_126).1 <| .cons (line_facts face4OK_0 lC0_127).1 <| .cons (line_facts
    face4OK_0 lC0_128).1 <| .cons (line_facts face4OK_0 lC0_129).1 <| .cons (line_facts face4OK_0
    lC0_130).1 <| .cons (line_facts face4OK_0 lC0_131).1 <| .cons (line_facts face4OK_0 lC0_132).1
    <| .cons (line_facts face4OK_0 lC0_133).1 <| .cons (line_facts face4OK_0 lC0_134).1 <| .cons
    (line_facts face4OK_0 lC0_135).1 <| .cons (line_facts face4OK_0 lC0_136).1 <| .cons (line_facts
    face4OK_0 lC0_137).1 <| .cons (line_facts face4OK_0 lC0_138).1 <| .cons (line_facts face4OK_0
    lC0_139).1 <| .cons (line_facts face4OK_0 lC0_140).1 <| .cons (line_facts face4OK_0 lC0_141).1
    <| .cons (line_facts face4OK_0 lC0_142).1 <| .cons (line_facts face4OK_0 lC0_143).1 <| .cons
    (line_facts face4OK_0 lC0_144).1 <| .cons (line_facts face4OK_0 lC0_145).1 <| .cons (line_facts
    face4OK_0 lC0_146).1 <| .cons (line_facts face4OK_0 lC0_147).1 <| .cons (line_facts face4OK_0
    lC0_148).1 <| .cons (line_facts face4OK_0 lC0_149).1 <| .cons (line_facts face4OK_0 lC0_150).1
    <| .cons (line_facts face4OK_0 lC0_151).1 <| .cons (line_facts face4OK_0 lC0_152).1 <| .cons
    (line_facts face4OK_0 lC0_153).1 <| .cons (line_facts face4OK_0 lC0_154).1 <| .cons (line_facts
    face4OK_0 lC0_155).1 <| .cons (line_facts face4OK_0 lC0_156).1 <| .cons (line_facts face4OK_0
    lC0_157).1 <| .nil

/-- The strip facts of face 0. -/
theorem rowsC_0 : RowsT filsC faceC0 gridC0 dataC0 :=
rowsT_cons (line_facts face4OK_0 lC0_1).2 <| rowsT_cons (line_facts face4OK_0 lC0_2).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_3).2 <| rowsT_cons (line_facts face4OK_0 lC0_4).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_5).2 <| rowsT_cons (line_facts face4OK_0 lC0_6).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_7).2 <| rowsT_cons (line_facts face4OK_0 lC0_8).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_9).2 <| rowsT_cons (line_facts face4OK_0 lC0_10).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_11).2 <| rowsT_cons (line_facts face4OK_0 lC0_12).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_13).2 <| rowsT_cons (line_facts face4OK_0 lC0_14).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_15).2 <| rowsT_cons (line_facts face4OK_0 lC0_16).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_17).2 <| rowsT_cons (line_facts face4OK_0 lC0_18).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_19).2 <| rowsT_cons (line_facts face4OK_0 lC0_20).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_21).2 <| rowsT_cons (line_facts face4OK_0 lC0_22).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_23).2 <| rowsT_cons (line_facts face4OK_0 lC0_24).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_25).2 <| rowsT_cons (line_facts face4OK_0 lC0_26).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_27).2 <| rowsT_cons (line_facts face4OK_0 lC0_28).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_29).2 <| rowsT_cons (line_facts face4OK_0 lC0_30).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_31).2 <| rowsT_cons (line_facts face4OK_0 lC0_32).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_33).2 <| rowsT_cons (line_facts face4OK_0 lC0_34).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_35).2 <| rowsT_cons (line_facts face4OK_0 lC0_36).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_37).2 <| rowsT_cons (line_facts face4OK_0 lC0_38).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_39).2 <| rowsT_cons (line_facts face4OK_0 lC0_40).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_41).2 <| rowsT_cons (line_facts face4OK_0 lC0_42).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_43).2 <| rowsT_cons (line_facts face4OK_0 lC0_44).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_45).2 <| rowsT_cons (line_facts face4OK_0 lC0_46).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_47).2 <| rowsT_cons (line_facts face4OK_0 lC0_48).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_49).2 <| rowsT_cons (line_facts face4OK_0 lC0_50).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_51).2 <| rowsT_cons (line_facts face4OK_0 lC0_52).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_53).2 <| rowsT_cons (line_facts face4OK_0 lC0_54).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_55).2 <| rowsT_cons (line_facts face4OK_0 lC0_56).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_57).2 <| rowsT_cons (line_facts face4OK_0 lC0_58).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_59).2 <| rowsT_cons (line_facts face4OK_0 lC0_60).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_61).2 <| rowsT_cons (line_facts face4OK_0 lC0_62).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_63).2 <| rowsT_cons (line_facts face4OK_0 lC0_64).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_65).2 <| rowsT_cons (line_facts face4OK_0 lC0_66).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_67).2 <| rowsT_cons (line_facts face4OK_0 lC0_68).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_69).2 <| rowsT_cons (line_facts face4OK_0 lC0_70).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_71).2 <| rowsT_cons (line_facts face4OK_0 lC0_72).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_73).2 <| rowsT_cons (line_facts face4OK_0 lC0_74).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_75).2 <| rowsT_cons (line_facts face4OK_0 lC0_76).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_77).2 <| rowsT_cons (line_facts face4OK_0 lC0_78).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_79).2 <| rowsT_cons (line_facts face4OK_0 lC0_80).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_81).2 <| rowsT_cons (line_facts face4OK_0 lC0_82).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_83).2 <| rowsT_cons (line_facts face4OK_0 lC0_84).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_85).2 <| rowsT_cons (line_facts face4OK_0 lC0_86).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_87).2 <| rowsT_cons (line_facts face4OK_0 lC0_88).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_89).2 <| rowsT_cons (line_facts face4OK_0 lC0_90).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_91).2 <| rowsT_cons (line_facts face4OK_0 lC0_92).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_93).2 <| rowsT_cons (line_facts face4OK_0 lC0_94).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_95).2 <| rowsT_cons (line_facts face4OK_0 lC0_96).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_97).2 <| rowsT_cons (line_facts face4OK_0 lC0_98).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_99).2 <| rowsT_cons (line_facts face4OK_0 lC0_100).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_101).2 <| rowsT_cons (line_facts face4OK_0 lC0_102).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_103).2 <| rowsT_cons (line_facts face4OK_0 lC0_104).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_105).2 <| rowsT_cons (line_facts face4OK_0 lC0_106).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_107).2 <| rowsT_cons (line_facts face4OK_0 lC0_108).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_109).2 <| rowsT_cons (line_facts face4OK_0 lC0_110).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_111).2 <| rowsT_cons (line_facts face4OK_0 lC0_112).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_113).2 <| rowsT_cons (line_facts face4OK_0 lC0_114).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_115).2 <| rowsT_cons (line_facts face4OK_0 lC0_116).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_117).2 <| rowsT_cons (line_facts face4OK_0 lC0_118).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_119).2 <| rowsT_cons (line_facts face4OK_0 lC0_120).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_121).2 <| rowsT_cons (line_facts face4OK_0 lC0_122).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_123).2 <| rowsT_cons (line_facts face4OK_0 lC0_124).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_125).2 <| rowsT_cons (line_facts face4OK_0 lC0_126).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_127).2 <| rowsT_cons (line_facts face4OK_0 lC0_128).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_129).2 <| rowsT_cons (line_facts face4OK_0 lC0_130).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_131).2 <| rowsT_cons (line_facts face4OK_0 lC0_132).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_133).2 <| rowsT_cons (line_facts face4OK_0 lC0_134).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_135).2 <| rowsT_cons (line_facts face4OK_0 lC0_136).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_137).2 <| rowsT_cons (line_facts face4OK_0 lC0_138).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_139).2 <| rowsT_cons (line_facts face4OK_0 lC0_140).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_141).2 <| rowsT_cons (line_facts face4OK_0 lC0_142).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_143).2 <| rowsT_cons (line_facts face4OK_0 lC0_144).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_145).2 <| rowsT_cons (line_facts face4OK_0 lC0_146).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_147).2 <| rowsT_cons (line_facts face4OK_0 lC0_148).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_149).2 <| rowsT_cons (line_facts face4OK_0 lC0_150).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_151).2 <| rowsT_cons (line_facts face4OK_0 lC0_152).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_153).2 <| rowsT_cons (line_facts face4OK_0 lC0_154).2 <| rowsT_cons
    (line_facts face4OK_0 lC0_155).2 <| rowsT_end

set_option maxRecDepth 20000 in
/-- **The certified bound on face 0.** -/
theorem coverC_0 : RectGood filsC 0 etaC (((-1705 : ℤ) : ℝ) / 4096) (((1705 : ℤ) : ℝ) / 4096)
    (((-75240 : ℤ) : ℝ) / ((720742 : ℕ) : ℝ)) (((75240 : ℤ) : ℝ) / ((720742 : ℕ) : ℝ)) := by
  have h := face_sound filsC faceC0 face4OK_0 etaC (by decide) gridC0 dataC0 linesC_0
    rowsC_0 cellsC0 (by decide)
  rw [show gridC0.length = 158 by decide +kernel, show faceC0.wn.length = 25 by decide +kernel] at h
  rwa [show gridC0.getD 1 0 = -1705 by decide +kernel,
    show gridC0.getD 156 0 = 1705 by decide +kernel,
    show faceC0.wn.getD 1 0 = -75240 by decide +kernel,
    show faceC0.wn.getD 23 0 = 75240 by decide +kernel,
    show faceC0.wd = 720742 from rfl, show faceC0.kind = 0 from rfl] at h

/-- **The cover of face 0.** -/
theorem faceCovC_0 : FaceCovC 0 :=
  ⟨_, _, _, _, coverC_0, by norm_num, by norm_num, by norm_num [faceLoC, aF],
    by norm_num [faceHiC, aF]⟩

end PlasmaLean.Design.PolygonCoil
