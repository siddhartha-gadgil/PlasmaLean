/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicLines09
public import PlasmaLean.Design.PolygonCoilCubicLines10
public import PlasmaLean.Design.PolygonCoilCubicLines11
public import PlasmaLean.Design.PolygonCoilCubicLines12
public import PlasmaLean.Design.PolygonCoilCubicLines13
public import PlasmaLean.Design.PolygonCoilCubicLines14
public import PlasmaLean.Design.PolygonCoilCubicFrontier

/-!
# Cubic frontier certificate: the cells and the cover of face 2

* `rowCF_i`: kernel evaluation (`decide +kernel`) of `cellsRow4` on the records of the grid lines
  `i, …, i+3` of face `F` (one evaluation per row keeps the kernel memory small);
* `cellsCF`: all cells of the face pass (`cellsAll4`, assembled from the rows);
* `linesC_F`, `rowsC_F`: the facts certified by the line checks `lCF_k` (`lineOut4_sound`);
* `coverC_F`, `faceCovC_F`: the certified bound on the face (`face_sound`).
-/

public section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator Set Real

/-- The line records of face 2. -/
@[expose]
def dataC2 : List (List CRec) := [dC2_0, dC2_1, dC2_2, dC2_3, dC2_4, dC2_5, dC2_6, dC2_7, dC2_8,
    dC2_9, dC2_10, dC2_11, dC2_12, dC2_13, dC2_14, dC2_15, dC2_16, dC2_17, dC2_18, dC2_19, dC2_20,
    dC2_21, dC2_22, dC2_23, dC2_24, dC2_25, dC2_26, dC2_27, dC2_28, dC2_29, dC2_30, dC2_31, dC2_32,
    dC2_33, dC2_34, dC2_35, dC2_36, dC2_37, dC2_38, dC2_39, dC2_40, dC2_41, dC2_42, dC2_43, dC2_44,
    dC2_45, dC2_46, dC2_47, dC2_48, dC2_49, dC2_50, dC2_51, dC2_52, dC2_53, dC2_54, dC2_55, dC2_56,
    dC2_57, dC2_58, dC2_59, dC2_60, dC2_61, dC2_62, dC2_63, dC2_64, dC2_65, dC2_66, dC2_67, dC2_68,
    dC2_69, dC2_70, dC2_71, dC2_72, dC2_73, dC2_74, dC2_75, dC2_76, dC2_77, dC2_78, dC2_79, dC2_80,
    dC2_81, dC2_82, dC2_83, dC2_84, dC2_85, dC2_86, dC2_87, dC2_88, dC2_89, dC2_90, dC2_91, dC2_92,
    dC2_93, dC2_94, dC2_95, dC2_96, dC2_97, dC2_98, dC2_99, dC2_100, dC2_101, dC2_102, dC2_103,
    dC2_104, dC2_105, dC2_106, dC2_107, dC2_108, dC2_109, dC2_110, dC2_111, dC2_112, dC2_113,
    dC2_114, dC2_115, dC2_116, dC2_117, dC2_118, dC2_119, dC2_120, dC2_121, dC2_122, dC2_123,
    dC2_124, dC2_125, dC2_126, dC2_127, dC2_128, dC2_129, dC2_130, dC2_131, dC2_132, dC2_133,
    dC2_134, dC2_135, dC2_136, dC2_137, dC2_138, dC2_139, dC2_140, dC2_141, dC2_142, dC2_143,
    dC2_144, dC2_145, dC2_146, dC2_147, dC2_148, dC2_149, dC2_150, dC2_151, dC2_152, dC2_153,
    dC2_154, dC2_155, dC2_156, dC2_157, dC2_158, dC2_159, dC2_160, dC2_161, dC2_162, dC2_163,
    dC2_164, dC2_165, dC2_166, dC2_167, dC2_168, dC2_169, dC2_170, dC2_171, dC2_172]

/-- The cells of row 0 of face 2 pass. -/
theorem rowC2_0 : cellsRow4 faceC2 etaC (-1720) (-1700) (-1680) (-1660) dC2_0 dC2_1 dC2_2 dC2_3
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 1 of face 2 pass. -/
theorem rowC2_1 : cellsRow4 faceC2 etaC (-1700) (-1680) (-1660) (-1640) dC2_1 dC2_2 dC2_3 dC2_4
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 2 of face 2 pass. -/
theorem rowC2_2 : cellsRow4 faceC2 etaC (-1680) (-1660) (-1640) (-1620) dC2_2 dC2_3 dC2_4 dC2_5
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 3 of face 2 pass. -/
theorem rowC2_3 : cellsRow4 faceC2 etaC (-1660) (-1640) (-1620) (-1600) dC2_3 dC2_4 dC2_5 dC2_6
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 4 of face 2 pass. -/
theorem rowC2_4 : cellsRow4 faceC2 etaC (-1640) (-1620) (-1600) (-1580) dC2_4 dC2_5 dC2_6 dC2_7
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 5 of face 2 pass. -/
theorem rowC2_5 : cellsRow4 faceC2 etaC (-1620) (-1600) (-1580) (-1560) dC2_5 dC2_6 dC2_7 dC2_8
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 6 of face 2 pass. -/
theorem rowC2_6 : cellsRow4 faceC2 etaC (-1600) (-1580) (-1560) (-1540) dC2_6 dC2_7 dC2_8 dC2_9
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 7 of face 2 pass. -/
theorem rowC2_7 : cellsRow4 faceC2 etaC (-1580) (-1560) (-1540) (-1520) dC2_7 dC2_8 dC2_9 dC2_10
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 8 of face 2 pass. -/
theorem rowC2_8 : cellsRow4 faceC2 etaC (-1560) (-1540) (-1520) (-1500) dC2_8 dC2_9 dC2_10 dC2_11
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 9 of face 2 pass. -/
theorem rowC2_9 : cellsRow4 faceC2 etaC (-1540) (-1520) (-1500) (-1480) dC2_9 dC2_10 dC2_11 dC2_12
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 10 of face 2 pass. -/
theorem rowC2_10 : cellsRow4 faceC2 etaC (-1520) (-1500) (-1480) (-1460) dC2_10 dC2_11 dC2_12 dC2_13
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 11 of face 2 pass. -/
theorem rowC2_11 : cellsRow4 faceC2 etaC (-1500) (-1480) (-1460) (-1440) dC2_11 dC2_12 dC2_13 dC2_14
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 12 of face 2 pass. -/
theorem rowC2_12 : cellsRow4 faceC2 etaC (-1480) (-1460) (-1440) (-1420) dC2_12 dC2_13 dC2_14 dC2_15
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 13 of face 2 pass. -/
theorem rowC2_13 : cellsRow4 faceC2 etaC (-1460) (-1440) (-1420) (-1400) dC2_13 dC2_14 dC2_15 dC2_16
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 14 of face 2 pass. -/
theorem rowC2_14 : cellsRow4 faceC2 etaC (-1440) (-1420) (-1400) (-1380) dC2_14 dC2_15 dC2_16 dC2_17
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 15 of face 2 pass. -/
theorem rowC2_15 : cellsRow4 faceC2 etaC (-1420) (-1400) (-1380) (-1360) dC2_15 dC2_16 dC2_17 dC2_18
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 16 of face 2 pass. -/
theorem rowC2_16 : cellsRow4 faceC2 etaC (-1400) (-1380) (-1360) (-1340) dC2_16 dC2_17 dC2_18 dC2_19
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 17 of face 2 pass. -/
theorem rowC2_17 : cellsRow4 faceC2 etaC (-1380) (-1360) (-1340) (-1320) dC2_17 dC2_18 dC2_19 dC2_20
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 18 of face 2 pass. -/
theorem rowC2_18 : cellsRow4 faceC2 etaC (-1360) (-1340) (-1320) (-1300) dC2_18 dC2_19 dC2_20 dC2_21
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 19 of face 2 pass. -/
theorem rowC2_19 : cellsRow4 faceC2 etaC (-1340) (-1320) (-1300) (-1280) dC2_19 dC2_20 dC2_21 dC2_22
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 20 of face 2 pass. -/
theorem rowC2_20 : cellsRow4 faceC2 etaC (-1320) (-1300) (-1280) (-1260) dC2_20 dC2_21 dC2_22 dC2_23
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 21 of face 2 pass. -/
theorem rowC2_21 : cellsRow4 faceC2 etaC (-1300) (-1280) (-1260) (-1240) dC2_21 dC2_22 dC2_23 dC2_24
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 22 of face 2 pass. -/
theorem rowC2_22 : cellsRow4 faceC2 etaC (-1280) (-1260) (-1240) (-1220) dC2_22 dC2_23 dC2_24 dC2_25
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 23 of face 2 pass. -/
theorem rowC2_23 : cellsRow4 faceC2 etaC (-1260) (-1240) (-1220) (-1200) dC2_23 dC2_24 dC2_25 dC2_26
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 24 of face 2 pass. -/
theorem rowC2_24 : cellsRow4 faceC2 etaC (-1240) (-1220) (-1200) (-1180) dC2_24 dC2_25 dC2_26 dC2_27
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 25 of face 2 pass. -/
theorem rowC2_25 : cellsRow4 faceC2 etaC (-1220) (-1200) (-1180) (-1160) dC2_25 dC2_26 dC2_27 dC2_28
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 26 of face 2 pass. -/
theorem rowC2_26 : cellsRow4 faceC2 etaC (-1200) (-1180) (-1160) (-1140) dC2_26 dC2_27 dC2_28 dC2_29
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 27 of face 2 pass. -/
theorem rowC2_27 : cellsRow4 faceC2 etaC (-1180) (-1160) (-1140) (-1120) dC2_27 dC2_28 dC2_29 dC2_30
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 28 of face 2 pass. -/
theorem rowC2_28 : cellsRow4 faceC2 etaC (-1160) (-1140) (-1120) (-1100) dC2_28 dC2_29 dC2_30 dC2_31
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 29 of face 2 pass. -/
theorem rowC2_29 : cellsRow4 faceC2 etaC (-1140) (-1120) (-1100) (-1080) dC2_29 dC2_30 dC2_31 dC2_32
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 30 of face 2 pass. -/
theorem rowC2_30 : cellsRow4 faceC2 etaC (-1120) (-1100) (-1080) (-1060) dC2_30 dC2_31 dC2_32 dC2_33
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 31 of face 2 pass. -/
theorem rowC2_31 : cellsRow4 faceC2 etaC (-1100) (-1080) (-1060) (-1040) dC2_31 dC2_32 dC2_33 dC2_34
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 32 of face 2 pass. -/
theorem rowC2_32 : cellsRow4 faceC2 etaC (-1080) (-1060) (-1040) (-1020) dC2_32 dC2_33 dC2_34 dC2_35
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 33 of face 2 pass. -/
theorem rowC2_33 : cellsRow4 faceC2 etaC (-1060) (-1040) (-1020) (-1000) dC2_33 dC2_34 dC2_35 dC2_36
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 34 of face 2 pass. -/
theorem rowC2_34 : cellsRow4 faceC2 etaC (-1040) (-1020) (-1000) (-980) dC2_34 dC2_35 dC2_36 dC2_37
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 35 of face 2 pass. -/
theorem rowC2_35 : cellsRow4 faceC2 etaC (-1020) (-1000) (-980) (-960) dC2_35 dC2_36 dC2_37 dC2_38
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 36 of face 2 pass. -/
theorem rowC2_36 : cellsRow4 faceC2 etaC (-1000) (-980) (-960) (-940) dC2_36 dC2_37 dC2_38 dC2_39
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 37 of face 2 pass. -/
theorem rowC2_37 : cellsRow4 faceC2 etaC (-980) (-960) (-940) (-920) dC2_37 dC2_38 dC2_39 dC2_40
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 38 of face 2 pass. -/
theorem rowC2_38 : cellsRow4 faceC2 etaC (-960) (-940) (-920) (-900) dC2_38 dC2_39 dC2_40 dC2_41
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 39 of face 2 pass. -/
theorem rowC2_39 : cellsRow4 faceC2 etaC (-940) (-920) (-900) (-880) dC2_39 dC2_40 dC2_41 dC2_42
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 40 of face 2 pass. -/
theorem rowC2_40 : cellsRow4 faceC2 etaC (-920) (-900) (-880) (-860) dC2_40 dC2_41 dC2_42 dC2_43
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 41 of face 2 pass. -/
theorem rowC2_41 : cellsRow4 faceC2 etaC (-900) (-880) (-860) (-840) dC2_41 dC2_42 dC2_43 dC2_44
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 42 of face 2 pass. -/
theorem rowC2_42 : cellsRow4 faceC2 etaC (-880) (-860) (-840) (-820) dC2_42 dC2_43 dC2_44 dC2_45
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 43 of face 2 pass. -/
theorem rowC2_43 : cellsRow4 faceC2 etaC (-860) (-840) (-820) (-800) dC2_43 dC2_44 dC2_45 dC2_46
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 44 of face 2 pass. -/
theorem rowC2_44 : cellsRow4 faceC2 etaC (-840) (-820) (-800) (-780) dC2_44 dC2_45 dC2_46 dC2_47
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 45 of face 2 pass. -/
theorem rowC2_45 : cellsRow4 faceC2 etaC (-820) (-800) (-780) (-760) dC2_45 dC2_46 dC2_47 dC2_48
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 46 of face 2 pass. -/
theorem rowC2_46 : cellsRow4 faceC2 etaC (-800) (-780) (-760) (-740) dC2_46 dC2_47 dC2_48 dC2_49
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 47 of face 2 pass. -/
theorem rowC2_47 : cellsRow4 faceC2 etaC (-780) (-760) (-740) (-720) dC2_47 dC2_48 dC2_49 dC2_50
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 48 of face 2 pass. -/
theorem rowC2_48 : cellsRow4 faceC2 etaC (-760) (-740) (-720) (-700) dC2_48 dC2_49 dC2_50 dC2_51
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 49 of face 2 pass. -/
theorem rowC2_49 : cellsRow4 faceC2 etaC (-740) (-720) (-700) (-680) dC2_49 dC2_50 dC2_51 dC2_52
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 50 of face 2 pass. -/
theorem rowC2_50 : cellsRow4 faceC2 etaC (-720) (-700) (-680) (-660) dC2_50 dC2_51 dC2_52 dC2_53
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 51 of face 2 pass. -/
theorem rowC2_51 : cellsRow4 faceC2 etaC (-700) (-680) (-660) (-640) dC2_51 dC2_52 dC2_53 dC2_54
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 52 of face 2 pass. -/
theorem rowC2_52 : cellsRow4 faceC2 etaC (-680) (-660) (-640) (-620) dC2_52 dC2_53 dC2_54 dC2_55
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 53 of face 2 pass. -/
theorem rowC2_53 : cellsRow4 faceC2 etaC (-660) (-640) (-620) (-600) dC2_53 dC2_54 dC2_55 dC2_56
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 54 of face 2 pass. -/
theorem rowC2_54 : cellsRow4 faceC2 etaC (-640) (-620) (-600) (-580) dC2_54 dC2_55 dC2_56 dC2_57
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 55 of face 2 pass. -/
theorem rowC2_55 : cellsRow4 faceC2 etaC (-620) (-600) (-580) (-560) dC2_55 dC2_56 dC2_57 dC2_58
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 56 of face 2 pass. -/
theorem rowC2_56 : cellsRow4 faceC2 etaC (-600) (-580) (-560) (-540) dC2_56 dC2_57 dC2_58 dC2_59
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 57 of face 2 pass. -/
theorem rowC2_57 : cellsRow4 faceC2 etaC (-580) (-560) (-540) (-520) dC2_57 dC2_58 dC2_59 dC2_60
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 58 of face 2 pass. -/
theorem rowC2_58 : cellsRow4 faceC2 etaC (-560) (-540) (-520) (-500) dC2_58 dC2_59 dC2_60 dC2_61
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 59 of face 2 pass. -/
theorem rowC2_59 : cellsRow4 faceC2 etaC (-540) (-520) (-500) (-480) dC2_59 dC2_60 dC2_61 dC2_62
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 60 of face 2 pass. -/
theorem rowC2_60 : cellsRow4 faceC2 etaC (-520) (-500) (-480) (-460) dC2_60 dC2_61 dC2_62 dC2_63
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 61 of face 2 pass. -/
theorem rowC2_61 : cellsRow4 faceC2 etaC (-500) (-480) (-460) (-440) dC2_61 dC2_62 dC2_63 dC2_64
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 62 of face 2 pass. -/
theorem rowC2_62 : cellsRow4 faceC2 etaC (-480) (-460) (-440) (-420) dC2_62 dC2_63 dC2_64 dC2_65
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 63 of face 2 pass. -/
theorem rowC2_63 : cellsRow4 faceC2 etaC (-460) (-440) (-420) (-400) dC2_63 dC2_64 dC2_65 dC2_66
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 64 of face 2 pass. -/
theorem rowC2_64 : cellsRow4 faceC2 etaC (-440) (-420) (-400) (-380) dC2_64 dC2_65 dC2_66 dC2_67
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 65 of face 2 pass. -/
theorem rowC2_65 : cellsRow4 faceC2 etaC (-420) (-400) (-380) (-360) dC2_65 dC2_66 dC2_67 dC2_68
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 66 of face 2 pass. -/
theorem rowC2_66 : cellsRow4 faceC2 etaC (-400) (-380) (-360) (-340) dC2_66 dC2_67 dC2_68 dC2_69
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 67 of face 2 pass. -/
theorem rowC2_67 : cellsRow4 faceC2 etaC (-380) (-360) (-340) (-320) dC2_67 dC2_68 dC2_69 dC2_70
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 68 of face 2 pass. -/
theorem rowC2_68 : cellsRow4 faceC2 etaC (-360) (-340) (-320) (-300) dC2_68 dC2_69 dC2_70 dC2_71
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 69 of face 2 pass. -/
theorem rowC2_69 : cellsRow4 faceC2 etaC (-340) (-320) (-300) (-280) dC2_69 dC2_70 dC2_71 dC2_72
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 70 of face 2 pass. -/
theorem rowC2_70 : cellsRow4 faceC2 etaC (-320) (-300) (-280) (-260) dC2_70 dC2_71 dC2_72 dC2_73
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 71 of face 2 pass. -/
theorem rowC2_71 : cellsRow4 faceC2 etaC (-300) (-280) (-260) (-240) dC2_71 dC2_72 dC2_73 dC2_74
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 72 of face 2 pass. -/
theorem rowC2_72 : cellsRow4 faceC2 etaC (-280) (-260) (-240) (-220) dC2_72 dC2_73 dC2_74 dC2_75
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 73 of face 2 pass. -/
theorem rowC2_73 : cellsRow4 faceC2 etaC (-260) (-240) (-220) (-200) dC2_73 dC2_74 dC2_75 dC2_76
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 74 of face 2 pass. -/
theorem rowC2_74 : cellsRow4 faceC2 etaC (-240) (-220) (-200) (-180) dC2_74 dC2_75 dC2_76 dC2_77
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 75 of face 2 pass. -/
theorem rowC2_75 : cellsRow4 faceC2 etaC (-220) (-200) (-180) (-160) dC2_75 dC2_76 dC2_77 dC2_78
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 76 of face 2 pass. -/
theorem rowC2_76 : cellsRow4 faceC2 etaC (-200) (-180) (-160) (-140) dC2_76 dC2_77 dC2_78 dC2_79
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 77 of face 2 pass. -/
theorem rowC2_77 : cellsRow4 faceC2 etaC (-180) (-160) (-140) (-120) dC2_77 dC2_78 dC2_79 dC2_80
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 78 of face 2 pass. -/
theorem rowC2_78 : cellsRow4 faceC2 etaC (-160) (-140) (-120) (-100) dC2_78 dC2_79 dC2_80 dC2_81
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 79 of face 2 pass. -/
theorem rowC2_79 : cellsRow4 faceC2 etaC (-140) (-120) (-100) (-80) dC2_79 dC2_80 dC2_81 dC2_82
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 80 of face 2 pass. -/
theorem rowC2_80 : cellsRow4 faceC2 etaC (-120) (-100) (-80) (-60) dC2_80 dC2_81 dC2_82 dC2_83
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 81 of face 2 pass. -/
theorem rowC2_81 : cellsRow4 faceC2 etaC (-100) (-80) (-60) (-40) dC2_81 dC2_82 dC2_83 dC2_84
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 82 of face 2 pass. -/
theorem rowC2_82 : cellsRow4 faceC2 etaC (-80) (-60) (-40) (-20) dC2_82 dC2_83 dC2_84 dC2_85
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 83 of face 2 pass. -/
theorem rowC2_83 : cellsRow4 faceC2 etaC (-60) (-40) (-20) (0) dC2_83 dC2_84 dC2_85 dC2_86 faceC2.wn
    = true := by
  decide +kernel

/-- The cells of row 84 of face 2 pass. -/
theorem rowC2_84 : cellsRow4 faceC2 etaC (-40) (-20) (0) (20) dC2_84 dC2_85 dC2_86 dC2_87 faceC2.wn
    = true := by
  decide +kernel

/-- The cells of row 85 of face 2 pass. -/
theorem rowC2_85 : cellsRow4 faceC2 etaC (-20) (0) (20) (40) dC2_85 dC2_86 dC2_87 dC2_88 faceC2.wn =
    true := by
  decide +kernel

/-- The cells of row 86 of face 2 pass. -/
theorem rowC2_86 : cellsRow4 faceC2 etaC (0) (20) (40) (60) dC2_86 dC2_87 dC2_88 dC2_89 faceC2.wn =
    true := by
  decide +kernel

/-- The cells of row 87 of face 2 pass. -/
theorem rowC2_87 : cellsRow4 faceC2 etaC (20) (40) (60) (80) dC2_87 dC2_88 dC2_89 dC2_90 faceC2.wn =
    true := by
  decide +kernel

/-- The cells of row 88 of face 2 pass. -/
theorem rowC2_88 : cellsRow4 faceC2 etaC (40) (60) (80) (100) dC2_88 dC2_89 dC2_90 dC2_91 faceC2.wn
    = true := by
  decide +kernel

/-- The cells of row 89 of face 2 pass. -/
theorem rowC2_89 : cellsRow4 faceC2 etaC (60) (80) (100) (120) dC2_89 dC2_90 dC2_91 dC2_92 faceC2.wn
    = true := by
  decide +kernel

/-- The cells of row 90 of face 2 pass. -/
theorem rowC2_90 : cellsRow4 faceC2 etaC (80) (100) (120) (140) dC2_90 dC2_91 dC2_92 dC2_93
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 91 of face 2 pass. -/
theorem rowC2_91 : cellsRow4 faceC2 etaC (100) (120) (140) (160) dC2_91 dC2_92 dC2_93 dC2_94
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 92 of face 2 pass. -/
theorem rowC2_92 : cellsRow4 faceC2 etaC (120) (140) (160) (180) dC2_92 dC2_93 dC2_94 dC2_95
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 93 of face 2 pass. -/
theorem rowC2_93 : cellsRow4 faceC2 etaC (140) (160) (180) (200) dC2_93 dC2_94 dC2_95 dC2_96
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 94 of face 2 pass. -/
theorem rowC2_94 : cellsRow4 faceC2 etaC (160) (180) (200) (220) dC2_94 dC2_95 dC2_96 dC2_97
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 95 of face 2 pass. -/
theorem rowC2_95 : cellsRow4 faceC2 etaC (180) (200) (220) (240) dC2_95 dC2_96 dC2_97 dC2_98
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 96 of face 2 pass. -/
theorem rowC2_96 : cellsRow4 faceC2 etaC (200) (220) (240) (260) dC2_96 dC2_97 dC2_98 dC2_99
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 97 of face 2 pass. -/
theorem rowC2_97 : cellsRow4 faceC2 etaC (220) (240) (260) (280) dC2_97 dC2_98 dC2_99 dC2_100
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 98 of face 2 pass. -/
theorem rowC2_98 : cellsRow4 faceC2 etaC (240) (260) (280) (300) dC2_98 dC2_99 dC2_100 dC2_101
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 99 of face 2 pass. -/
theorem rowC2_99 : cellsRow4 faceC2 etaC (260) (280) (300) (320) dC2_99 dC2_100 dC2_101 dC2_102
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 100 of face 2 pass. -/
theorem rowC2_100 : cellsRow4 faceC2 etaC (280) (300) (320) (340) dC2_100 dC2_101 dC2_102 dC2_103
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 101 of face 2 pass. -/
theorem rowC2_101 : cellsRow4 faceC2 etaC (300) (320) (340) (360) dC2_101 dC2_102 dC2_103 dC2_104
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 102 of face 2 pass. -/
theorem rowC2_102 : cellsRow4 faceC2 etaC (320) (340) (360) (380) dC2_102 dC2_103 dC2_104 dC2_105
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 103 of face 2 pass. -/
theorem rowC2_103 : cellsRow4 faceC2 etaC (340) (360) (380) (400) dC2_103 dC2_104 dC2_105 dC2_106
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 104 of face 2 pass. -/
theorem rowC2_104 : cellsRow4 faceC2 etaC (360) (380) (400) (420) dC2_104 dC2_105 dC2_106 dC2_107
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 105 of face 2 pass. -/
theorem rowC2_105 : cellsRow4 faceC2 etaC (380) (400) (420) (440) dC2_105 dC2_106 dC2_107 dC2_108
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 106 of face 2 pass. -/
theorem rowC2_106 : cellsRow4 faceC2 etaC (400) (420) (440) (460) dC2_106 dC2_107 dC2_108 dC2_109
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 107 of face 2 pass. -/
theorem rowC2_107 : cellsRow4 faceC2 etaC (420) (440) (460) (480) dC2_107 dC2_108 dC2_109 dC2_110
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 108 of face 2 pass. -/
theorem rowC2_108 : cellsRow4 faceC2 etaC (440) (460) (480) (500) dC2_108 dC2_109 dC2_110 dC2_111
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 109 of face 2 pass. -/
theorem rowC2_109 : cellsRow4 faceC2 etaC (460) (480) (500) (520) dC2_109 dC2_110 dC2_111 dC2_112
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 110 of face 2 pass. -/
theorem rowC2_110 : cellsRow4 faceC2 etaC (480) (500) (520) (540) dC2_110 dC2_111 dC2_112 dC2_113
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 111 of face 2 pass. -/
theorem rowC2_111 : cellsRow4 faceC2 etaC (500) (520) (540) (560) dC2_111 dC2_112 dC2_113 dC2_114
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 112 of face 2 pass. -/
theorem rowC2_112 : cellsRow4 faceC2 etaC (520) (540) (560) (580) dC2_112 dC2_113 dC2_114 dC2_115
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 113 of face 2 pass. -/
theorem rowC2_113 : cellsRow4 faceC2 etaC (540) (560) (580) (600) dC2_113 dC2_114 dC2_115 dC2_116
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 114 of face 2 pass. -/
theorem rowC2_114 : cellsRow4 faceC2 etaC (560) (580) (600) (620) dC2_114 dC2_115 dC2_116 dC2_117
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 115 of face 2 pass. -/
theorem rowC2_115 : cellsRow4 faceC2 etaC (580) (600) (620) (640) dC2_115 dC2_116 dC2_117 dC2_118
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 116 of face 2 pass. -/
theorem rowC2_116 : cellsRow4 faceC2 etaC (600) (620) (640) (660) dC2_116 dC2_117 dC2_118 dC2_119
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 117 of face 2 pass. -/
theorem rowC2_117 : cellsRow4 faceC2 etaC (620) (640) (660) (680) dC2_117 dC2_118 dC2_119 dC2_120
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 118 of face 2 pass. -/
theorem rowC2_118 : cellsRow4 faceC2 etaC (640) (660) (680) (700) dC2_118 dC2_119 dC2_120 dC2_121
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 119 of face 2 pass. -/
theorem rowC2_119 : cellsRow4 faceC2 etaC (660) (680) (700) (720) dC2_119 dC2_120 dC2_121 dC2_122
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 120 of face 2 pass. -/
theorem rowC2_120 : cellsRow4 faceC2 etaC (680) (700) (720) (740) dC2_120 dC2_121 dC2_122 dC2_123
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 121 of face 2 pass. -/
theorem rowC2_121 : cellsRow4 faceC2 etaC (700) (720) (740) (760) dC2_121 dC2_122 dC2_123 dC2_124
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 122 of face 2 pass. -/
theorem rowC2_122 : cellsRow4 faceC2 etaC (720) (740) (760) (780) dC2_122 dC2_123 dC2_124 dC2_125
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 123 of face 2 pass. -/
theorem rowC2_123 : cellsRow4 faceC2 etaC (740) (760) (780) (800) dC2_123 dC2_124 dC2_125 dC2_126
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 124 of face 2 pass. -/
theorem rowC2_124 : cellsRow4 faceC2 etaC (760) (780) (800) (820) dC2_124 dC2_125 dC2_126 dC2_127
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 125 of face 2 pass. -/
theorem rowC2_125 : cellsRow4 faceC2 etaC (780) (800) (820) (840) dC2_125 dC2_126 dC2_127 dC2_128
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 126 of face 2 pass. -/
theorem rowC2_126 : cellsRow4 faceC2 etaC (800) (820) (840) (860) dC2_126 dC2_127 dC2_128 dC2_129
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 127 of face 2 pass. -/
theorem rowC2_127 : cellsRow4 faceC2 etaC (820) (840) (860) (880) dC2_127 dC2_128 dC2_129 dC2_130
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 128 of face 2 pass. -/
theorem rowC2_128 : cellsRow4 faceC2 etaC (840) (860) (880) (900) dC2_128 dC2_129 dC2_130 dC2_131
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 129 of face 2 pass. -/
theorem rowC2_129 : cellsRow4 faceC2 etaC (860) (880) (900) (920) dC2_129 dC2_130 dC2_131 dC2_132
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 130 of face 2 pass. -/
theorem rowC2_130 : cellsRow4 faceC2 etaC (880) (900) (920) (940) dC2_130 dC2_131 dC2_132 dC2_133
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 131 of face 2 pass. -/
theorem rowC2_131 : cellsRow4 faceC2 etaC (900) (920) (940) (960) dC2_131 dC2_132 dC2_133 dC2_134
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 132 of face 2 pass. -/
theorem rowC2_132 : cellsRow4 faceC2 etaC (920) (940) (960) (980) dC2_132 dC2_133 dC2_134 dC2_135
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 133 of face 2 pass. -/
theorem rowC2_133 : cellsRow4 faceC2 etaC (940) (960) (980) (1000) dC2_133 dC2_134 dC2_135 dC2_136
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 134 of face 2 pass. -/
theorem rowC2_134 : cellsRow4 faceC2 etaC (960) (980) (1000) (1020) dC2_134 dC2_135 dC2_136 dC2_137
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 135 of face 2 pass. -/
theorem rowC2_135 : cellsRow4 faceC2 etaC (980) (1000) (1020) (1040) dC2_135 dC2_136 dC2_137 dC2_138
    faceC2.wn = true := by
  decide +kernel

/-- The cells of row 136 of face 2 pass. -/
theorem rowC2_136 : cellsRow4 faceC2 etaC (1000) (1020) (1040) (1060) dC2_136 dC2_137 dC2_138
    dC2_139 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 137 of face 2 pass. -/
theorem rowC2_137 : cellsRow4 faceC2 etaC (1020) (1040) (1060) (1080) dC2_137 dC2_138 dC2_139
    dC2_140 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 138 of face 2 pass. -/
theorem rowC2_138 : cellsRow4 faceC2 etaC (1040) (1060) (1080) (1100) dC2_138 dC2_139 dC2_140
    dC2_141 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 139 of face 2 pass. -/
theorem rowC2_139 : cellsRow4 faceC2 etaC (1060) (1080) (1100) (1120) dC2_139 dC2_140 dC2_141
    dC2_142 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 140 of face 2 pass. -/
theorem rowC2_140 : cellsRow4 faceC2 etaC (1080) (1100) (1120) (1140) dC2_140 dC2_141 dC2_142
    dC2_143 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 141 of face 2 pass. -/
theorem rowC2_141 : cellsRow4 faceC2 etaC (1100) (1120) (1140) (1160) dC2_141 dC2_142 dC2_143
    dC2_144 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 142 of face 2 pass. -/
theorem rowC2_142 : cellsRow4 faceC2 etaC (1120) (1140) (1160) (1180) dC2_142 dC2_143 dC2_144
    dC2_145 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 143 of face 2 pass. -/
theorem rowC2_143 : cellsRow4 faceC2 etaC (1140) (1160) (1180) (1200) dC2_143 dC2_144 dC2_145
    dC2_146 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 144 of face 2 pass. -/
theorem rowC2_144 : cellsRow4 faceC2 etaC (1160) (1180) (1200) (1220) dC2_144 dC2_145 dC2_146
    dC2_147 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 145 of face 2 pass. -/
theorem rowC2_145 : cellsRow4 faceC2 etaC (1180) (1200) (1220) (1240) dC2_145 dC2_146 dC2_147
    dC2_148 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 146 of face 2 pass. -/
theorem rowC2_146 : cellsRow4 faceC2 etaC (1200) (1220) (1240) (1260) dC2_146 dC2_147 dC2_148
    dC2_149 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 147 of face 2 pass. -/
theorem rowC2_147 : cellsRow4 faceC2 etaC (1220) (1240) (1260) (1280) dC2_147 dC2_148 dC2_149
    dC2_150 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 148 of face 2 pass. -/
theorem rowC2_148 : cellsRow4 faceC2 etaC (1240) (1260) (1280) (1300) dC2_148 dC2_149 dC2_150
    dC2_151 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 149 of face 2 pass. -/
theorem rowC2_149 : cellsRow4 faceC2 etaC (1260) (1280) (1300) (1320) dC2_149 dC2_150 dC2_151
    dC2_152 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 150 of face 2 pass. -/
theorem rowC2_150 : cellsRow4 faceC2 etaC (1280) (1300) (1320) (1340) dC2_150 dC2_151 dC2_152
    dC2_153 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 151 of face 2 pass. -/
theorem rowC2_151 : cellsRow4 faceC2 etaC (1300) (1320) (1340) (1360) dC2_151 dC2_152 dC2_153
    dC2_154 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 152 of face 2 pass. -/
theorem rowC2_152 : cellsRow4 faceC2 etaC (1320) (1340) (1360) (1380) dC2_152 dC2_153 dC2_154
    dC2_155 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 153 of face 2 pass. -/
theorem rowC2_153 : cellsRow4 faceC2 etaC (1340) (1360) (1380) (1400) dC2_153 dC2_154 dC2_155
    dC2_156 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 154 of face 2 pass. -/
theorem rowC2_154 : cellsRow4 faceC2 etaC (1360) (1380) (1400) (1420) dC2_154 dC2_155 dC2_156
    dC2_157 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 155 of face 2 pass. -/
theorem rowC2_155 : cellsRow4 faceC2 etaC (1380) (1400) (1420) (1440) dC2_155 dC2_156 dC2_157
    dC2_158 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 156 of face 2 pass. -/
theorem rowC2_156 : cellsRow4 faceC2 etaC (1400) (1420) (1440) (1460) dC2_156 dC2_157 dC2_158
    dC2_159 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 157 of face 2 pass. -/
theorem rowC2_157 : cellsRow4 faceC2 etaC (1420) (1440) (1460) (1480) dC2_157 dC2_158 dC2_159
    dC2_160 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 158 of face 2 pass. -/
theorem rowC2_158 : cellsRow4 faceC2 etaC (1440) (1460) (1480) (1500) dC2_158 dC2_159 dC2_160
    dC2_161 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 159 of face 2 pass. -/
theorem rowC2_159 : cellsRow4 faceC2 etaC (1460) (1480) (1500) (1520) dC2_159 dC2_160 dC2_161
    dC2_162 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 160 of face 2 pass. -/
theorem rowC2_160 : cellsRow4 faceC2 etaC (1480) (1500) (1520) (1540) dC2_160 dC2_161 dC2_162
    dC2_163 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 161 of face 2 pass. -/
theorem rowC2_161 : cellsRow4 faceC2 etaC (1500) (1520) (1540) (1560) dC2_161 dC2_162 dC2_163
    dC2_164 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 162 of face 2 pass. -/
theorem rowC2_162 : cellsRow4 faceC2 etaC (1520) (1540) (1560) (1580) dC2_162 dC2_163 dC2_164
    dC2_165 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 163 of face 2 pass. -/
theorem rowC2_163 : cellsRow4 faceC2 etaC (1540) (1560) (1580) (1600) dC2_163 dC2_164 dC2_165
    dC2_166 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 164 of face 2 pass. -/
theorem rowC2_164 : cellsRow4 faceC2 etaC (1560) (1580) (1600) (1620) dC2_164 dC2_165 dC2_166
    dC2_167 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 165 of face 2 pass. -/
theorem rowC2_165 : cellsRow4 faceC2 etaC (1580) (1600) (1620) (1640) dC2_165 dC2_166 dC2_167
    dC2_168 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 166 of face 2 pass. -/
theorem rowC2_166 : cellsRow4 faceC2 etaC (1600) (1620) (1640) (1660) dC2_166 dC2_167 dC2_168
    dC2_169 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 167 of face 2 pass. -/
theorem rowC2_167 : cellsRow4 faceC2 etaC (1620) (1640) (1660) (1680) dC2_167 dC2_168 dC2_169
    dC2_170 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 168 of face 2 pass. -/
theorem rowC2_168 : cellsRow4 faceC2 etaC (1640) (1660) (1680) (1700) dC2_168 dC2_169 dC2_170
    dC2_171 faceC2.wn = true := by
  decide +kernel

/-- The cells of row 169 of face 2 pass. -/
theorem rowC2_169 : cellsRow4 faceC2 etaC (1660) (1680) (1700) (1720) dC2_169 dC2_170 dC2_171
    dC2_172 faceC2.wn = true := by
  decide +kernel

/-- **All cells of face 2 pass** (`η = 3540573·2⁻⁴⁰`). -/
theorem cellsC2 : cellsAll4 etaC faceC2 gridC2 dataC2 = true :=
cellsAll4_cons rowC2_0 <| cellsAll4_cons rowC2_1 <| cellsAll4_cons rowC2_2 <| cellsAll4_cons rowC2_3
    <| cellsAll4_cons rowC2_4 <| cellsAll4_cons rowC2_5 <| cellsAll4_cons rowC2_6 <| cellsAll4_cons
    rowC2_7 <| cellsAll4_cons rowC2_8 <| cellsAll4_cons rowC2_9 <| cellsAll4_cons rowC2_10 <|
    cellsAll4_cons rowC2_11 <| cellsAll4_cons rowC2_12 <| cellsAll4_cons rowC2_13 <| cellsAll4_cons
    rowC2_14 <| cellsAll4_cons rowC2_15 <| cellsAll4_cons rowC2_16 <| cellsAll4_cons rowC2_17 <|
    cellsAll4_cons rowC2_18 <| cellsAll4_cons rowC2_19 <| cellsAll4_cons rowC2_20 <| cellsAll4_cons
    rowC2_21 <| cellsAll4_cons rowC2_22 <| cellsAll4_cons rowC2_23 <| cellsAll4_cons rowC2_24 <|
    cellsAll4_cons rowC2_25 <| cellsAll4_cons rowC2_26 <| cellsAll4_cons rowC2_27 <| cellsAll4_cons
    rowC2_28 <| cellsAll4_cons rowC2_29 <| cellsAll4_cons rowC2_30 <| cellsAll4_cons rowC2_31 <|
    cellsAll4_cons rowC2_32 <| cellsAll4_cons rowC2_33 <| cellsAll4_cons rowC2_34 <| cellsAll4_cons
    rowC2_35 <| cellsAll4_cons rowC2_36 <| cellsAll4_cons rowC2_37 <| cellsAll4_cons rowC2_38 <|
    cellsAll4_cons rowC2_39 <| cellsAll4_cons rowC2_40 <| cellsAll4_cons rowC2_41 <| cellsAll4_cons
    rowC2_42 <| cellsAll4_cons rowC2_43 <| cellsAll4_cons rowC2_44 <| cellsAll4_cons rowC2_45 <|
    cellsAll4_cons rowC2_46 <| cellsAll4_cons rowC2_47 <| cellsAll4_cons rowC2_48 <| cellsAll4_cons
    rowC2_49 <| cellsAll4_cons rowC2_50 <| cellsAll4_cons rowC2_51 <| cellsAll4_cons rowC2_52 <|
    cellsAll4_cons rowC2_53 <| cellsAll4_cons rowC2_54 <| cellsAll4_cons rowC2_55 <| cellsAll4_cons
    rowC2_56 <| cellsAll4_cons rowC2_57 <| cellsAll4_cons rowC2_58 <| cellsAll4_cons rowC2_59 <|
    cellsAll4_cons rowC2_60 <| cellsAll4_cons rowC2_61 <| cellsAll4_cons rowC2_62 <| cellsAll4_cons
    rowC2_63 <| cellsAll4_cons rowC2_64 <| cellsAll4_cons rowC2_65 <| cellsAll4_cons rowC2_66 <|
    cellsAll4_cons rowC2_67 <| cellsAll4_cons rowC2_68 <| cellsAll4_cons rowC2_69 <| cellsAll4_cons
    rowC2_70 <| cellsAll4_cons rowC2_71 <| cellsAll4_cons rowC2_72 <| cellsAll4_cons rowC2_73 <|
    cellsAll4_cons rowC2_74 <| cellsAll4_cons rowC2_75 <| cellsAll4_cons rowC2_76 <| cellsAll4_cons
    rowC2_77 <| cellsAll4_cons rowC2_78 <| cellsAll4_cons rowC2_79 <| cellsAll4_cons rowC2_80 <|
    cellsAll4_cons rowC2_81 <| cellsAll4_cons rowC2_82 <| cellsAll4_cons rowC2_83 <| cellsAll4_cons
    rowC2_84 <| cellsAll4_cons rowC2_85 <| cellsAll4_cons rowC2_86 <| cellsAll4_cons rowC2_87 <|
    cellsAll4_cons rowC2_88 <| cellsAll4_cons rowC2_89 <| cellsAll4_cons rowC2_90 <| cellsAll4_cons
    rowC2_91 <| cellsAll4_cons rowC2_92 <| cellsAll4_cons rowC2_93 <| cellsAll4_cons rowC2_94 <|
    cellsAll4_cons rowC2_95 <| cellsAll4_cons rowC2_96 <| cellsAll4_cons rowC2_97 <| cellsAll4_cons
    rowC2_98 <| cellsAll4_cons rowC2_99 <| cellsAll4_cons rowC2_100 <| cellsAll4_cons rowC2_101 <|
    cellsAll4_cons rowC2_102 <| cellsAll4_cons rowC2_103 <| cellsAll4_cons rowC2_104 <|
    cellsAll4_cons rowC2_105 <| cellsAll4_cons rowC2_106 <| cellsAll4_cons rowC2_107 <|
    cellsAll4_cons rowC2_108 <| cellsAll4_cons rowC2_109 <| cellsAll4_cons rowC2_110 <|
    cellsAll4_cons rowC2_111 <| cellsAll4_cons rowC2_112 <| cellsAll4_cons rowC2_113 <|
    cellsAll4_cons rowC2_114 <| cellsAll4_cons rowC2_115 <| cellsAll4_cons rowC2_116 <|
    cellsAll4_cons rowC2_117 <| cellsAll4_cons rowC2_118 <| cellsAll4_cons rowC2_119 <|
    cellsAll4_cons rowC2_120 <| cellsAll4_cons rowC2_121 <| cellsAll4_cons rowC2_122 <|
    cellsAll4_cons rowC2_123 <| cellsAll4_cons rowC2_124 <| cellsAll4_cons rowC2_125 <|
    cellsAll4_cons rowC2_126 <| cellsAll4_cons rowC2_127 <| cellsAll4_cons rowC2_128 <|
    cellsAll4_cons rowC2_129 <| cellsAll4_cons rowC2_130 <| cellsAll4_cons rowC2_131 <|
    cellsAll4_cons rowC2_132 <| cellsAll4_cons rowC2_133 <| cellsAll4_cons rowC2_134 <|
    cellsAll4_cons rowC2_135 <| cellsAll4_cons rowC2_136 <| cellsAll4_cons rowC2_137 <|
    cellsAll4_cons rowC2_138 <| cellsAll4_cons rowC2_139 <| cellsAll4_cons rowC2_140 <|
    cellsAll4_cons rowC2_141 <| cellsAll4_cons rowC2_142 <| cellsAll4_cons rowC2_143 <|
    cellsAll4_cons rowC2_144 <| cellsAll4_cons rowC2_145 <| cellsAll4_cons rowC2_146 <|
    cellsAll4_cons rowC2_147 <| cellsAll4_cons rowC2_148 <| cellsAll4_cons rowC2_149 <|
    cellsAll4_cons rowC2_150 <| cellsAll4_cons rowC2_151 <| cellsAll4_cons rowC2_152 <|
    cellsAll4_cons rowC2_153 <| cellsAll4_cons rowC2_154 <| cellsAll4_cons rowC2_155 <|
    cellsAll4_cons rowC2_156 <| cellsAll4_cons rowC2_157 <| cellsAll4_cons rowC2_158 <|
    cellsAll4_cons rowC2_159 <| cellsAll4_cons rowC2_160 <| cellsAll4_cons rowC2_161 <|
    cellsAll4_cons rowC2_162 <| cellsAll4_cons rowC2_163 <| cellsAll4_cons rowC2_164 <|
    cellsAll4_cons rowC2_165 <| cellsAll4_cons rowC2_166 <| cellsAll4_cons rowC2_167 <|
    cellsAll4_cons rowC2_168 <| cellsAll4_cons rowC2_169 <| cellsAll4_end

/-- Face 2 carries the proved `hel` constants. -/
theorem face4OK_2 : Face4OK faceC2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [faceC2] <;> norm_num

/-- The line facts of face 2. -/
theorem linesC_2 : List.Forall₂ (fun m L => List.Forall₂ (LVal filsC faceC2 m) faceC2.wn L ∧
    QuadP (LW filsC faceC2 m) faceC2.wn L) gridC2 dataC2 :=
.cons (line_facts face4OK_2 lC2_0).1 <| .cons (line_facts face4OK_2 lC2_1).1 <| .cons (line_facts
    face4OK_2 lC2_2).1 <| .cons (line_facts face4OK_2 lC2_3).1 <| .cons (line_facts face4OK_2
    lC2_4).1 <| .cons (line_facts face4OK_2 lC2_5).1 <| .cons (line_facts face4OK_2 lC2_6).1 <|
    .cons (line_facts face4OK_2 lC2_7).1 <| .cons (line_facts face4OK_2 lC2_8).1 <| .cons
    (line_facts face4OK_2 lC2_9).1 <| .cons (line_facts face4OK_2 lC2_10).1 <| .cons (line_facts
    face4OK_2 lC2_11).1 <| .cons (line_facts face4OK_2 lC2_12).1 <| .cons (line_facts face4OK_2
    lC2_13).1 <| .cons (line_facts face4OK_2 lC2_14).1 <| .cons (line_facts face4OK_2 lC2_15).1 <|
    .cons (line_facts face4OK_2 lC2_16).1 <| .cons (line_facts face4OK_2 lC2_17).1 <| .cons
    (line_facts face4OK_2 lC2_18).1 <| .cons (line_facts face4OK_2 lC2_19).1 <| .cons (line_facts
    face4OK_2 lC2_20).1 <| .cons (line_facts face4OK_2 lC2_21).1 <| .cons (line_facts face4OK_2
    lC2_22).1 <| .cons (line_facts face4OK_2 lC2_23).1 <| .cons (line_facts face4OK_2 lC2_24).1 <|
    .cons (line_facts face4OK_2 lC2_25).1 <| .cons (line_facts face4OK_2 lC2_26).1 <| .cons
    (line_facts face4OK_2 lC2_27).1 <| .cons (line_facts face4OK_2 lC2_28).1 <| .cons (line_facts
    face4OK_2 lC2_29).1 <| .cons (line_facts face4OK_2 lC2_30).1 <| .cons (line_facts face4OK_2
    lC2_31).1 <| .cons (line_facts face4OK_2 lC2_32).1 <| .cons (line_facts face4OK_2 lC2_33).1 <|
    .cons (line_facts face4OK_2 lC2_34).1 <| .cons (line_facts face4OK_2 lC2_35).1 <| .cons
    (line_facts face4OK_2 lC2_36).1 <| .cons (line_facts face4OK_2 lC2_37).1 <| .cons (line_facts
    face4OK_2 lC2_38).1 <| .cons (line_facts face4OK_2 lC2_39).1 <| .cons (line_facts face4OK_2
    lC2_40).1 <| .cons (line_facts face4OK_2 lC2_41).1 <| .cons (line_facts face4OK_2 lC2_42).1 <|
    .cons (line_facts face4OK_2 lC2_43).1 <| .cons (line_facts face4OK_2 lC2_44).1 <| .cons
    (line_facts face4OK_2 lC2_45).1 <| .cons (line_facts face4OK_2 lC2_46).1 <| .cons (line_facts
    face4OK_2 lC2_47).1 <| .cons (line_facts face4OK_2 lC2_48).1 <| .cons (line_facts face4OK_2
    lC2_49).1 <| .cons (line_facts face4OK_2 lC2_50).1 <| .cons (line_facts face4OK_2 lC2_51).1 <|
    .cons (line_facts face4OK_2 lC2_52).1 <| .cons (line_facts face4OK_2 lC2_53).1 <| .cons
    (line_facts face4OK_2 lC2_54).1 <| .cons (line_facts face4OK_2 lC2_55).1 <| .cons (line_facts
    face4OK_2 lC2_56).1 <| .cons (line_facts face4OK_2 lC2_57).1 <| .cons (line_facts face4OK_2
    lC2_58).1 <| .cons (line_facts face4OK_2 lC2_59).1 <| .cons (line_facts face4OK_2 lC2_60).1 <|
    .cons (line_facts face4OK_2 lC2_61).1 <| .cons (line_facts face4OK_2 lC2_62).1 <| .cons
    (line_facts face4OK_2 lC2_63).1 <| .cons (line_facts face4OK_2 lC2_64).1 <| .cons (line_facts
    face4OK_2 lC2_65).1 <| .cons (line_facts face4OK_2 lC2_66).1 <| .cons (line_facts face4OK_2
    lC2_67).1 <| .cons (line_facts face4OK_2 lC2_68).1 <| .cons (line_facts face4OK_2 lC2_69).1 <|
    .cons (line_facts face4OK_2 lC2_70).1 <| .cons (line_facts face4OK_2 lC2_71).1 <| .cons
    (line_facts face4OK_2 lC2_72).1 <| .cons (line_facts face4OK_2 lC2_73).1 <| .cons (line_facts
    face4OK_2 lC2_74).1 <| .cons (line_facts face4OK_2 lC2_75).1 <| .cons (line_facts face4OK_2
    lC2_76).1 <| .cons (line_facts face4OK_2 lC2_77).1 <| .cons (line_facts face4OK_2 lC2_78).1 <|
    .cons (line_facts face4OK_2 lC2_79).1 <| .cons (line_facts face4OK_2 lC2_80).1 <| .cons
    (line_facts face4OK_2 lC2_81).1 <| .cons (line_facts face4OK_2 lC2_82).1 <| .cons (line_facts
    face4OK_2 lC2_83).1 <| .cons (line_facts face4OK_2 lC2_84).1 <| .cons (line_facts face4OK_2
    lC2_85).1 <| .cons (line_facts face4OK_2 lC2_86).1 <| .cons (line_facts face4OK_2 lC2_87).1 <|
    .cons (line_facts face4OK_2 lC2_88).1 <| .cons (line_facts face4OK_2 lC2_89).1 <| .cons
    (line_facts face4OK_2 lC2_90).1 <| .cons (line_facts face4OK_2 lC2_91).1 <| .cons (line_facts
    face4OK_2 lC2_92).1 <| .cons (line_facts face4OK_2 lC2_93).1 <| .cons (line_facts face4OK_2
    lC2_94).1 <| .cons (line_facts face4OK_2 lC2_95).1 <| .cons (line_facts face4OK_2 lC2_96).1 <|
    .cons (line_facts face4OK_2 lC2_97).1 <| .cons (line_facts face4OK_2 lC2_98).1 <| .cons
    (line_facts face4OK_2 lC2_99).1 <| .cons (line_facts face4OK_2 lC2_100).1 <| .cons (line_facts
    face4OK_2 lC2_101).1 <| .cons (line_facts face4OK_2 lC2_102).1 <| .cons (line_facts face4OK_2
    lC2_103).1 <| .cons (line_facts face4OK_2 lC2_104).1 <| .cons (line_facts face4OK_2 lC2_105).1
    <| .cons (line_facts face4OK_2 lC2_106).1 <| .cons (line_facts face4OK_2 lC2_107).1 <| .cons
    (line_facts face4OK_2 lC2_108).1 <| .cons (line_facts face4OK_2 lC2_109).1 <| .cons (line_facts
    face4OK_2 lC2_110).1 <| .cons (line_facts face4OK_2 lC2_111).1 <| .cons (line_facts face4OK_2
    lC2_112).1 <| .cons (line_facts face4OK_2 lC2_113).1 <| .cons (line_facts face4OK_2 lC2_114).1
    <| .cons (line_facts face4OK_2 lC2_115).1 <| .cons (line_facts face4OK_2 lC2_116).1 <| .cons
    (line_facts face4OK_2 lC2_117).1 <| .cons (line_facts face4OK_2 lC2_118).1 <| .cons (line_facts
    face4OK_2 lC2_119).1 <| .cons (line_facts face4OK_2 lC2_120).1 <| .cons (line_facts face4OK_2
    lC2_121).1 <| .cons (line_facts face4OK_2 lC2_122).1 <| .cons (line_facts face4OK_2 lC2_123).1
    <| .cons (line_facts face4OK_2 lC2_124).1 <| .cons (line_facts face4OK_2 lC2_125).1 <| .cons
    (line_facts face4OK_2 lC2_126).1 <| .cons (line_facts face4OK_2 lC2_127).1 <| .cons (line_facts
    face4OK_2 lC2_128).1 <| .cons (line_facts face4OK_2 lC2_129).1 <| .cons (line_facts face4OK_2
    lC2_130).1 <| .cons (line_facts face4OK_2 lC2_131).1 <| .cons (line_facts face4OK_2 lC2_132).1
    <| .cons (line_facts face4OK_2 lC2_133).1 <| .cons (line_facts face4OK_2 lC2_134).1 <| .cons
    (line_facts face4OK_2 lC2_135).1 <| .cons (line_facts face4OK_2 lC2_136).1 <| .cons (line_facts
    face4OK_2 lC2_137).1 <| .cons (line_facts face4OK_2 lC2_138).1 <| .cons (line_facts face4OK_2
    lC2_139).1 <| .cons (line_facts face4OK_2 lC2_140).1 <| .cons (line_facts face4OK_2 lC2_141).1
    <| .cons (line_facts face4OK_2 lC2_142).1 <| .cons (line_facts face4OK_2 lC2_143).1 <| .cons
    (line_facts face4OK_2 lC2_144).1 <| .cons (line_facts face4OK_2 lC2_145).1 <| .cons (line_facts
    face4OK_2 lC2_146).1 <| .cons (line_facts face4OK_2 lC2_147).1 <| .cons (line_facts face4OK_2
    lC2_148).1 <| .cons (line_facts face4OK_2 lC2_149).1 <| .cons (line_facts face4OK_2 lC2_150).1
    <| .cons (line_facts face4OK_2 lC2_151).1 <| .cons (line_facts face4OK_2 lC2_152).1 <| .cons
    (line_facts face4OK_2 lC2_153).1 <| .cons (line_facts face4OK_2 lC2_154).1 <| .cons (line_facts
    face4OK_2 lC2_155).1 <| .cons (line_facts face4OK_2 lC2_156).1 <| .cons (line_facts face4OK_2
    lC2_157).1 <| .cons (line_facts face4OK_2 lC2_158).1 <| .cons (line_facts face4OK_2 lC2_159).1
    <| .cons (line_facts face4OK_2 lC2_160).1 <| .cons (line_facts face4OK_2 lC2_161).1 <| .cons
    (line_facts face4OK_2 lC2_162).1 <| .cons (line_facts face4OK_2 lC2_163).1 <| .cons (line_facts
    face4OK_2 lC2_164).1 <| .cons (line_facts face4OK_2 lC2_165).1 <| .cons (line_facts face4OK_2
    lC2_166).1 <| .cons (line_facts face4OK_2 lC2_167).1 <| .cons (line_facts face4OK_2 lC2_168).1
    <| .cons (line_facts face4OK_2 lC2_169).1 <| .cons (line_facts face4OK_2 lC2_170).1 <| .cons
    (line_facts face4OK_2 lC2_171).1 <| .cons (line_facts face4OK_2 lC2_172).1 <| .nil

/-- The strip facts of face 2. -/
theorem rowsC_2 : RowsT filsC faceC2 gridC2 dataC2 :=
rowsT_cons (line_facts face4OK_2 lC2_1).2 <| rowsT_cons (line_facts face4OK_2 lC2_2).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_3).2 <| rowsT_cons (line_facts face4OK_2 lC2_4).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_5).2 <| rowsT_cons (line_facts face4OK_2 lC2_6).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_7).2 <| rowsT_cons (line_facts face4OK_2 lC2_8).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_9).2 <| rowsT_cons (line_facts face4OK_2 lC2_10).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_11).2 <| rowsT_cons (line_facts face4OK_2 lC2_12).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_13).2 <| rowsT_cons (line_facts face4OK_2 lC2_14).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_15).2 <| rowsT_cons (line_facts face4OK_2 lC2_16).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_17).2 <| rowsT_cons (line_facts face4OK_2 lC2_18).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_19).2 <| rowsT_cons (line_facts face4OK_2 lC2_20).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_21).2 <| rowsT_cons (line_facts face4OK_2 lC2_22).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_23).2 <| rowsT_cons (line_facts face4OK_2 lC2_24).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_25).2 <| rowsT_cons (line_facts face4OK_2 lC2_26).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_27).2 <| rowsT_cons (line_facts face4OK_2 lC2_28).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_29).2 <| rowsT_cons (line_facts face4OK_2 lC2_30).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_31).2 <| rowsT_cons (line_facts face4OK_2 lC2_32).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_33).2 <| rowsT_cons (line_facts face4OK_2 lC2_34).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_35).2 <| rowsT_cons (line_facts face4OK_2 lC2_36).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_37).2 <| rowsT_cons (line_facts face4OK_2 lC2_38).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_39).2 <| rowsT_cons (line_facts face4OK_2 lC2_40).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_41).2 <| rowsT_cons (line_facts face4OK_2 lC2_42).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_43).2 <| rowsT_cons (line_facts face4OK_2 lC2_44).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_45).2 <| rowsT_cons (line_facts face4OK_2 lC2_46).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_47).2 <| rowsT_cons (line_facts face4OK_2 lC2_48).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_49).2 <| rowsT_cons (line_facts face4OK_2 lC2_50).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_51).2 <| rowsT_cons (line_facts face4OK_2 lC2_52).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_53).2 <| rowsT_cons (line_facts face4OK_2 lC2_54).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_55).2 <| rowsT_cons (line_facts face4OK_2 lC2_56).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_57).2 <| rowsT_cons (line_facts face4OK_2 lC2_58).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_59).2 <| rowsT_cons (line_facts face4OK_2 lC2_60).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_61).2 <| rowsT_cons (line_facts face4OK_2 lC2_62).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_63).2 <| rowsT_cons (line_facts face4OK_2 lC2_64).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_65).2 <| rowsT_cons (line_facts face4OK_2 lC2_66).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_67).2 <| rowsT_cons (line_facts face4OK_2 lC2_68).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_69).2 <| rowsT_cons (line_facts face4OK_2 lC2_70).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_71).2 <| rowsT_cons (line_facts face4OK_2 lC2_72).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_73).2 <| rowsT_cons (line_facts face4OK_2 lC2_74).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_75).2 <| rowsT_cons (line_facts face4OK_2 lC2_76).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_77).2 <| rowsT_cons (line_facts face4OK_2 lC2_78).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_79).2 <| rowsT_cons (line_facts face4OK_2 lC2_80).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_81).2 <| rowsT_cons (line_facts face4OK_2 lC2_82).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_83).2 <| rowsT_cons (line_facts face4OK_2 lC2_84).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_85).2 <| rowsT_cons (line_facts face4OK_2 lC2_86).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_87).2 <| rowsT_cons (line_facts face4OK_2 lC2_88).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_89).2 <| rowsT_cons (line_facts face4OK_2 lC2_90).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_91).2 <| rowsT_cons (line_facts face4OK_2 lC2_92).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_93).2 <| rowsT_cons (line_facts face4OK_2 lC2_94).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_95).2 <| rowsT_cons (line_facts face4OK_2 lC2_96).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_97).2 <| rowsT_cons (line_facts face4OK_2 lC2_98).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_99).2 <| rowsT_cons (line_facts face4OK_2 lC2_100).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_101).2 <| rowsT_cons (line_facts face4OK_2 lC2_102).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_103).2 <| rowsT_cons (line_facts face4OK_2 lC2_104).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_105).2 <| rowsT_cons (line_facts face4OK_2 lC2_106).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_107).2 <| rowsT_cons (line_facts face4OK_2 lC2_108).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_109).2 <| rowsT_cons (line_facts face4OK_2 lC2_110).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_111).2 <| rowsT_cons (line_facts face4OK_2 lC2_112).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_113).2 <| rowsT_cons (line_facts face4OK_2 lC2_114).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_115).2 <| rowsT_cons (line_facts face4OK_2 lC2_116).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_117).2 <| rowsT_cons (line_facts face4OK_2 lC2_118).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_119).2 <| rowsT_cons (line_facts face4OK_2 lC2_120).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_121).2 <| rowsT_cons (line_facts face4OK_2 lC2_122).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_123).2 <| rowsT_cons (line_facts face4OK_2 lC2_124).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_125).2 <| rowsT_cons (line_facts face4OK_2 lC2_126).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_127).2 <| rowsT_cons (line_facts face4OK_2 lC2_128).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_129).2 <| rowsT_cons (line_facts face4OK_2 lC2_130).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_131).2 <| rowsT_cons (line_facts face4OK_2 lC2_132).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_133).2 <| rowsT_cons (line_facts face4OK_2 lC2_134).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_135).2 <| rowsT_cons (line_facts face4OK_2 lC2_136).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_137).2 <| rowsT_cons (line_facts face4OK_2 lC2_138).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_139).2 <| rowsT_cons (line_facts face4OK_2 lC2_140).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_141).2 <| rowsT_cons (line_facts face4OK_2 lC2_142).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_143).2 <| rowsT_cons (line_facts face4OK_2 lC2_144).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_145).2 <| rowsT_cons (line_facts face4OK_2 lC2_146).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_147).2 <| rowsT_cons (line_facts face4OK_2 lC2_148).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_149).2 <| rowsT_cons (line_facts face4OK_2 lC2_150).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_151).2 <| rowsT_cons (line_facts face4OK_2 lC2_152).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_153).2 <| rowsT_cons (line_facts face4OK_2 lC2_154).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_155).2 <| rowsT_cons (line_facts face4OK_2 lC2_156).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_157).2 <| rowsT_cons (line_facts face4OK_2 lC2_158).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_159).2 <| rowsT_cons (line_facts face4OK_2 lC2_160).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_161).2 <| rowsT_cons (line_facts face4OK_2 lC2_162).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_163).2 <| rowsT_cons (line_facts face4OK_2 lC2_164).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_165).2 <| rowsT_cons (line_facts face4OK_2 lC2_166).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_167).2 <| rowsT_cons (line_facts face4OK_2 lC2_168).2 <| rowsT_cons
    (line_facts face4OK_2 lC2_169).2 <| rowsT_cons (line_facts face4OK_2 lC2_170).2 <| rowsT_end

set_option maxRecDepth 20000 in
/-- **The certified bound on face 2.** -/
theorem coverC_2 : RectGood filsC 2 etaC (((-1700 : ℤ) : ℝ) / 4096) (((1700 : ℤ) : ℝ) / 4096)
    (((4508 : ℤ) : ℝ) / ((5068 : ℕ) : ℝ)) (((5572 : ℤ) : ℝ) / ((5068 : ℕ) : ℝ)) := by
  have h := face_sound filsC faceC2 face4OK_2 etaC (by decide) gridC2 dataC2 linesC_2
    rowsC_2 cellsC2 (by decide)
  rw [show gridC2.length = 173 by decide +kernel, show faceC2.wn.length = 31 by decide +kernel] at h
  rwa [show gridC2.getD 1 0 = -1700 by decide +kernel,
    show gridC2.getD 171 0 = 1700 by decide +kernel,
    show faceC2.wn.getD 1 0 = 4508 by decide +kernel,
    show faceC2.wn.getD 29 0 = 5572 by decide +kernel,
    show faceC2.wd = 5068 from rfl, show faceC2.kind = 2 from rfl] at h

/-- **The cover of face 2.** -/
theorem faceCovC_2 : FaceCovC 2 :=
  ⟨_, _, _, _, coverC_2, by norm_num, by norm_num, by norm_num [faceLoC, aF],
    by norm_num [faceHiC, aF]⟩

end PlasmaLean.Design.PolygonCoil
