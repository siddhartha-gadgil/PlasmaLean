/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicLines03
public import PlasmaLean.Design.PolygonCoilCubicLines04
public import PlasmaLean.Design.PolygonCoilCubicLines05
public import PlasmaLean.Design.PolygonCoilCubicLines06
public import PlasmaLean.Design.PolygonCoilCubicLines07
public import PlasmaLean.Design.PolygonCoilCubicLines08
public import PlasmaLean.Design.PolygonCoilCubicLines09
public import PlasmaLean.Design.PolygonCoilCubicFrontier

/-!
# Cubic frontier certificate: the cells and the cover of face 1

* `rowCF_i`: kernel evaluation (`decide +kernel`) of `cellsRow4` on the records of the grid lines
  `i, …, i+3` of face `F` (one evaluation per row keeps the kernel memory small);
* `cellsCF`: all cells of the face pass (`cellsAll4`, assembled from the rows);
* `linesC_F`, `rowsC_F`: the facts certified by the line checks `lCF_k` (`lineOut4_sound`);
* `coverC_F`, `faceCovC_F`: the certified bound on the face (`face_sound`).
-/

public section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator Set Real

/-- The line records of face 1. -/
@[expose]
def dataC1 : List (List CRec) := [dC1_0, dC1_1, dC1_2, dC1_3, dC1_4, dC1_5, dC1_6, dC1_7, dC1_8,
    dC1_9, dC1_10, dC1_11, dC1_12, dC1_13, dC1_14, dC1_15, dC1_16, dC1_17, dC1_18, dC1_19, dC1_20,
    dC1_21, dC1_22, dC1_23, dC1_24, dC1_25, dC1_26, dC1_27, dC1_28, dC1_29, dC1_30, dC1_31, dC1_32,
    dC1_33, dC1_34, dC1_35, dC1_36, dC1_37, dC1_38, dC1_39, dC1_40, dC1_41, dC1_42, dC1_43, dC1_44,
    dC1_45, dC1_46, dC1_47, dC1_48, dC1_49, dC1_50, dC1_51, dC1_52, dC1_53, dC1_54, dC1_55, dC1_56,
    dC1_57, dC1_58, dC1_59, dC1_60, dC1_61, dC1_62, dC1_63, dC1_64, dC1_65, dC1_66, dC1_67, dC1_68,
    dC1_69, dC1_70, dC1_71, dC1_72, dC1_73, dC1_74, dC1_75, dC1_76, dC1_77, dC1_78, dC1_79, dC1_80,
    dC1_81, dC1_82, dC1_83, dC1_84, dC1_85, dC1_86, dC1_87, dC1_88, dC1_89, dC1_90, dC1_91, dC1_92,
    dC1_93, dC1_94, dC1_95, dC1_96, dC1_97, dC1_98, dC1_99, dC1_100, dC1_101, dC1_102, dC1_103,
    dC1_104, dC1_105, dC1_106, dC1_107, dC1_108, dC1_109, dC1_110, dC1_111, dC1_112, dC1_113,
    dC1_114, dC1_115, dC1_116, dC1_117, dC1_118, dC1_119, dC1_120, dC1_121, dC1_122, dC1_123,
    dC1_124, dC1_125, dC1_126, dC1_127, dC1_128, dC1_129, dC1_130, dC1_131, dC1_132, dC1_133,
    dC1_134, dC1_135, dC1_136, dC1_137, dC1_138, dC1_139, dC1_140, dC1_141, dC1_142, dC1_143,
    dC1_144, dC1_145, dC1_146, dC1_147, dC1_148, dC1_149, dC1_150, dC1_151, dC1_152, dC1_153,
    dC1_154, dC1_155, dC1_156, dC1_157, dC1_158, dC1_159, dC1_160, dC1_161, dC1_162, dC1_163,
    dC1_164, dC1_165, dC1_166, dC1_167, dC1_168, dC1_169, dC1_170, dC1_171, dC1_172]

/-- The cells of row 0 of face 1 pass. -/
theorem rowC1_0 : cellsRow4 faceC1 etaC (-1720) (-1700) (-1680) (-1660) dC1_0 dC1_1 dC1_2 dC1_3
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 1 of face 1 pass. -/
theorem rowC1_1 : cellsRow4 faceC1 etaC (-1700) (-1680) (-1660) (-1640) dC1_1 dC1_2 dC1_3 dC1_4
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 2 of face 1 pass. -/
theorem rowC1_2 : cellsRow4 faceC1 etaC (-1680) (-1660) (-1640) (-1620) dC1_2 dC1_3 dC1_4 dC1_5
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 3 of face 1 pass. -/
theorem rowC1_3 : cellsRow4 faceC1 etaC (-1660) (-1640) (-1620) (-1600) dC1_3 dC1_4 dC1_5 dC1_6
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 4 of face 1 pass. -/
theorem rowC1_4 : cellsRow4 faceC1 etaC (-1640) (-1620) (-1600) (-1580) dC1_4 dC1_5 dC1_6 dC1_7
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 5 of face 1 pass. -/
theorem rowC1_5 : cellsRow4 faceC1 etaC (-1620) (-1600) (-1580) (-1560) dC1_5 dC1_6 dC1_7 dC1_8
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 6 of face 1 pass. -/
theorem rowC1_6 : cellsRow4 faceC1 etaC (-1600) (-1580) (-1560) (-1540) dC1_6 dC1_7 dC1_8 dC1_9
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 7 of face 1 pass. -/
theorem rowC1_7 : cellsRow4 faceC1 etaC (-1580) (-1560) (-1540) (-1520) dC1_7 dC1_8 dC1_9 dC1_10
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 8 of face 1 pass. -/
theorem rowC1_8 : cellsRow4 faceC1 etaC (-1560) (-1540) (-1520) (-1500) dC1_8 dC1_9 dC1_10 dC1_11
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 9 of face 1 pass. -/
theorem rowC1_9 : cellsRow4 faceC1 etaC (-1540) (-1520) (-1500) (-1480) dC1_9 dC1_10 dC1_11 dC1_12
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 10 of face 1 pass. -/
theorem rowC1_10 : cellsRow4 faceC1 etaC (-1520) (-1500) (-1480) (-1460) dC1_10 dC1_11 dC1_12 dC1_13
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 11 of face 1 pass. -/
theorem rowC1_11 : cellsRow4 faceC1 etaC (-1500) (-1480) (-1460) (-1440) dC1_11 dC1_12 dC1_13 dC1_14
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 12 of face 1 pass. -/
theorem rowC1_12 : cellsRow4 faceC1 etaC (-1480) (-1460) (-1440) (-1420) dC1_12 dC1_13 dC1_14 dC1_15
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 13 of face 1 pass. -/
theorem rowC1_13 : cellsRow4 faceC1 etaC (-1460) (-1440) (-1420) (-1400) dC1_13 dC1_14 dC1_15 dC1_16
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 14 of face 1 pass. -/
theorem rowC1_14 : cellsRow4 faceC1 etaC (-1440) (-1420) (-1400) (-1380) dC1_14 dC1_15 dC1_16 dC1_17
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 15 of face 1 pass. -/
theorem rowC1_15 : cellsRow4 faceC1 etaC (-1420) (-1400) (-1380) (-1360) dC1_15 dC1_16 dC1_17 dC1_18
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 16 of face 1 pass. -/
theorem rowC1_16 : cellsRow4 faceC1 etaC (-1400) (-1380) (-1360) (-1340) dC1_16 dC1_17 dC1_18 dC1_19
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 17 of face 1 pass. -/
theorem rowC1_17 : cellsRow4 faceC1 etaC (-1380) (-1360) (-1340) (-1320) dC1_17 dC1_18 dC1_19 dC1_20
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 18 of face 1 pass. -/
theorem rowC1_18 : cellsRow4 faceC1 etaC (-1360) (-1340) (-1320) (-1300) dC1_18 dC1_19 dC1_20 dC1_21
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 19 of face 1 pass. -/
theorem rowC1_19 : cellsRow4 faceC1 etaC (-1340) (-1320) (-1300) (-1280) dC1_19 dC1_20 dC1_21 dC1_22
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 20 of face 1 pass. -/
theorem rowC1_20 : cellsRow4 faceC1 etaC (-1320) (-1300) (-1280) (-1260) dC1_20 dC1_21 dC1_22 dC1_23
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 21 of face 1 pass. -/
theorem rowC1_21 : cellsRow4 faceC1 etaC (-1300) (-1280) (-1260) (-1240) dC1_21 dC1_22 dC1_23 dC1_24
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 22 of face 1 pass. -/
theorem rowC1_22 : cellsRow4 faceC1 etaC (-1280) (-1260) (-1240) (-1220) dC1_22 dC1_23 dC1_24 dC1_25
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 23 of face 1 pass. -/
theorem rowC1_23 : cellsRow4 faceC1 etaC (-1260) (-1240) (-1220) (-1200) dC1_23 dC1_24 dC1_25 dC1_26
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 24 of face 1 pass. -/
theorem rowC1_24 : cellsRow4 faceC1 etaC (-1240) (-1220) (-1200) (-1180) dC1_24 dC1_25 dC1_26 dC1_27
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 25 of face 1 pass. -/
theorem rowC1_25 : cellsRow4 faceC1 etaC (-1220) (-1200) (-1180) (-1160) dC1_25 dC1_26 dC1_27 dC1_28
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 26 of face 1 pass. -/
theorem rowC1_26 : cellsRow4 faceC1 etaC (-1200) (-1180) (-1160) (-1140) dC1_26 dC1_27 dC1_28 dC1_29
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 27 of face 1 pass. -/
theorem rowC1_27 : cellsRow4 faceC1 etaC (-1180) (-1160) (-1140) (-1120) dC1_27 dC1_28 dC1_29 dC1_30
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 28 of face 1 pass. -/
theorem rowC1_28 : cellsRow4 faceC1 etaC (-1160) (-1140) (-1120) (-1100) dC1_28 dC1_29 dC1_30 dC1_31
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 29 of face 1 pass. -/
theorem rowC1_29 : cellsRow4 faceC1 etaC (-1140) (-1120) (-1100) (-1080) dC1_29 dC1_30 dC1_31 dC1_32
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 30 of face 1 pass. -/
theorem rowC1_30 : cellsRow4 faceC1 etaC (-1120) (-1100) (-1080) (-1060) dC1_30 dC1_31 dC1_32 dC1_33
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 31 of face 1 pass. -/
theorem rowC1_31 : cellsRow4 faceC1 etaC (-1100) (-1080) (-1060) (-1040) dC1_31 dC1_32 dC1_33 dC1_34
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 32 of face 1 pass. -/
theorem rowC1_32 : cellsRow4 faceC1 etaC (-1080) (-1060) (-1040) (-1020) dC1_32 dC1_33 dC1_34 dC1_35
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 33 of face 1 pass. -/
theorem rowC1_33 : cellsRow4 faceC1 etaC (-1060) (-1040) (-1020) (-1000) dC1_33 dC1_34 dC1_35 dC1_36
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 34 of face 1 pass. -/
theorem rowC1_34 : cellsRow4 faceC1 etaC (-1040) (-1020) (-1000) (-980) dC1_34 dC1_35 dC1_36 dC1_37
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 35 of face 1 pass. -/
theorem rowC1_35 : cellsRow4 faceC1 etaC (-1020) (-1000) (-980) (-960) dC1_35 dC1_36 dC1_37 dC1_38
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 36 of face 1 pass. -/
theorem rowC1_36 : cellsRow4 faceC1 etaC (-1000) (-980) (-960) (-940) dC1_36 dC1_37 dC1_38 dC1_39
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 37 of face 1 pass. -/
theorem rowC1_37 : cellsRow4 faceC1 etaC (-980) (-960) (-940) (-920) dC1_37 dC1_38 dC1_39 dC1_40
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 38 of face 1 pass. -/
theorem rowC1_38 : cellsRow4 faceC1 etaC (-960) (-940) (-920) (-900) dC1_38 dC1_39 dC1_40 dC1_41
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 39 of face 1 pass. -/
theorem rowC1_39 : cellsRow4 faceC1 etaC (-940) (-920) (-900) (-880) dC1_39 dC1_40 dC1_41 dC1_42
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 40 of face 1 pass. -/
theorem rowC1_40 : cellsRow4 faceC1 etaC (-920) (-900) (-880) (-860) dC1_40 dC1_41 dC1_42 dC1_43
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 41 of face 1 pass. -/
theorem rowC1_41 : cellsRow4 faceC1 etaC (-900) (-880) (-860) (-840) dC1_41 dC1_42 dC1_43 dC1_44
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 42 of face 1 pass. -/
theorem rowC1_42 : cellsRow4 faceC1 etaC (-880) (-860) (-840) (-820) dC1_42 dC1_43 dC1_44 dC1_45
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 43 of face 1 pass. -/
theorem rowC1_43 : cellsRow4 faceC1 etaC (-860) (-840) (-820) (-800) dC1_43 dC1_44 dC1_45 dC1_46
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 44 of face 1 pass. -/
theorem rowC1_44 : cellsRow4 faceC1 etaC (-840) (-820) (-800) (-780) dC1_44 dC1_45 dC1_46 dC1_47
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 45 of face 1 pass. -/
theorem rowC1_45 : cellsRow4 faceC1 etaC (-820) (-800) (-780) (-760) dC1_45 dC1_46 dC1_47 dC1_48
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 46 of face 1 pass. -/
theorem rowC1_46 : cellsRow4 faceC1 etaC (-800) (-780) (-760) (-740) dC1_46 dC1_47 dC1_48 dC1_49
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 47 of face 1 pass. -/
theorem rowC1_47 : cellsRow4 faceC1 etaC (-780) (-760) (-740) (-720) dC1_47 dC1_48 dC1_49 dC1_50
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 48 of face 1 pass. -/
theorem rowC1_48 : cellsRow4 faceC1 etaC (-760) (-740) (-720) (-700) dC1_48 dC1_49 dC1_50 dC1_51
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 49 of face 1 pass. -/
theorem rowC1_49 : cellsRow4 faceC1 etaC (-740) (-720) (-700) (-680) dC1_49 dC1_50 dC1_51 dC1_52
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 50 of face 1 pass. -/
theorem rowC1_50 : cellsRow4 faceC1 etaC (-720) (-700) (-680) (-660) dC1_50 dC1_51 dC1_52 dC1_53
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 51 of face 1 pass. -/
theorem rowC1_51 : cellsRow4 faceC1 etaC (-700) (-680) (-660) (-640) dC1_51 dC1_52 dC1_53 dC1_54
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 52 of face 1 pass. -/
theorem rowC1_52 : cellsRow4 faceC1 etaC (-680) (-660) (-640) (-620) dC1_52 dC1_53 dC1_54 dC1_55
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 53 of face 1 pass. -/
theorem rowC1_53 : cellsRow4 faceC1 etaC (-660) (-640) (-620) (-600) dC1_53 dC1_54 dC1_55 dC1_56
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 54 of face 1 pass. -/
theorem rowC1_54 : cellsRow4 faceC1 etaC (-640) (-620) (-600) (-580) dC1_54 dC1_55 dC1_56 dC1_57
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 55 of face 1 pass. -/
theorem rowC1_55 : cellsRow4 faceC1 etaC (-620) (-600) (-580) (-560) dC1_55 dC1_56 dC1_57 dC1_58
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 56 of face 1 pass. -/
theorem rowC1_56 : cellsRow4 faceC1 etaC (-600) (-580) (-560) (-540) dC1_56 dC1_57 dC1_58 dC1_59
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 57 of face 1 pass. -/
theorem rowC1_57 : cellsRow4 faceC1 etaC (-580) (-560) (-540) (-520) dC1_57 dC1_58 dC1_59 dC1_60
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 58 of face 1 pass. -/
theorem rowC1_58 : cellsRow4 faceC1 etaC (-560) (-540) (-520) (-500) dC1_58 dC1_59 dC1_60 dC1_61
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 59 of face 1 pass. -/
theorem rowC1_59 : cellsRow4 faceC1 etaC (-540) (-520) (-500) (-480) dC1_59 dC1_60 dC1_61 dC1_62
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 60 of face 1 pass. -/
theorem rowC1_60 : cellsRow4 faceC1 etaC (-520) (-500) (-480) (-460) dC1_60 dC1_61 dC1_62 dC1_63
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 61 of face 1 pass. -/
theorem rowC1_61 : cellsRow4 faceC1 etaC (-500) (-480) (-460) (-440) dC1_61 dC1_62 dC1_63 dC1_64
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 62 of face 1 pass. -/
theorem rowC1_62 : cellsRow4 faceC1 etaC (-480) (-460) (-440) (-420) dC1_62 dC1_63 dC1_64 dC1_65
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 63 of face 1 pass. -/
theorem rowC1_63 : cellsRow4 faceC1 etaC (-460) (-440) (-420) (-400) dC1_63 dC1_64 dC1_65 dC1_66
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 64 of face 1 pass. -/
theorem rowC1_64 : cellsRow4 faceC1 etaC (-440) (-420) (-400) (-380) dC1_64 dC1_65 dC1_66 dC1_67
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 65 of face 1 pass. -/
theorem rowC1_65 : cellsRow4 faceC1 etaC (-420) (-400) (-380) (-360) dC1_65 dC1_66 dC1_67 dC1_68
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 66 of face 1 pass. -/
theorem rowC1_66 : cellsRow4 faceC1 etaC (-400) (-380) (-360) (-340) dC1_66 dC1_67 dC1_68 dC1_69
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 67 of face 1 pass. -/
theorem rowC1_67 : cellsRow4 faceC1 etaC (-380) (-360) (-340) (-320) dC1_67 dC1_68 dC1_69 dC1_70
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 68 of face 1 pass. -/
theorem rowC1_68 : cellsRow4 faceC1 etaC (-360) (-340) (-320) (-300) dC1_68 dC1_69 dC1_70 dC1_71
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 69 of face 1 pass. -/
theorem rowC1_69 : cellsRow4 faceC1 etaC (-340) (-320) (-300) (-280) dC1_69 dC1_70 dC1_71 dC1_72
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 70 of face 1 pass. -/
theorem rowC1_70 : cellsRow4 faceC1 etaC (-320) (-300) (-280) (-260) dC1_70 dC1_71 dC1_72 dC1_73
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 71 of face 1 pass. -/
theorem rowC1_71 : cellsRow4 faceC1 etaC (-300) (-280) (-260) (-240) dC1_71 dC1_72 dC1_73 dC1_74
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 72 of face 1 pass. -/
theorem rowC1_72 : cellsRow4 faceC1 etaC (-280) (-260) (-240) (-220) dC1_72 dC1_73 dC1_74 dC1_75
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 73 of face 1 pass. -/
theorem rowC1_73 : cellsRow4 faceC1 etaC (-260) (-240) (-220) (-200) dC1_73 dC1_74 dC1_75 dC1_76
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 74 of face 1 pass. -/
theorem rowC1_74 : cellsRow4 faceC1 etaC (-240) (-220) (-200) (-180) dC1_74 dC1_75 dC1_76 dC1_77
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 75 of face 1 pass. -/
theorem rowC1_75 : cellsRow4 faceC1 etaC (-220) (-200) (-180) (-160) dC1_75 dC1_76 dC1_77 dC1_78
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 76 of face 1 pass. -/
theorem rowC1_76 : cellsRow4 faceC1 etaC (-200) (-180) (-160) (-140) dC1_76 dC1_77 dC1_78 dC1_79
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 77 of face 1 pass. -/
theorem rowC1_77 : cellsRow4 faceC1 etaC (-180) (-160) (-140) (-120) dC1_77 dC1_78 dC1_79 dC1_80
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 78 of face 1 pass. -/
theorem rowC1_78 : cellsRow4 faceC1 etaC (-160) (-140) (-120) (-100) dC1_78 dC1_79 dC1_80 dC1_81
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 79 of face 1 pass. -/
theorem rowC1_79 : cellsRow4 faceC1 etaC (-140) (-120) (-100) (-80) dC1_79 dC1_80 dC1_81 dC1_82
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 80 of face 1 pass. -/
theorem rowC1_80 : cellsRow4 faceC1 etaC (-120) (-100) (-80) (-60) dC1_80 dC1_81 dC1_82 dC1_83
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 81 of face 1 pass. -/
theorem rowC1_81 : cellsRow4 faceC1 etaC (-100) (-80) (-60) (-40) dC1_81 dC1_82 dC1_83 dC1_84
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 82 of face 1 pass. -/
theorem rowC1_82 : cellsRow4 faceC1 etaC (-80) (-60) (-40) (-20) dC1_82 dC1_83 dC1_84 dC1_85
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 83 of face 1 pass. -/
theorem rowC1_83 : cellsRow4 faceC1 etaC (-60) (-40) (-20) (0) dC1_83 dC1_84 dC1_85 dC1_86 faceC1.wn
    = true := by
  decide +kernel

/-- The cells of row 84 of face 1 pass. -/
theorem rowC1_84 : cellsRow4 faceC1 etaC (-40) (-20) (0) (20) dC1_84 dC1_85 dC1_86 dC1_87 faceC1.wn
    = true := by
  decide +kernel

/-- The cells of row 85 of face 1 pass. -/
theorem rowC1_85 : cellsRow4 faceC1 etaC (-20) (0) (20) (40) dC1_85 dC1_86 dC1_87 dC1_88 faceC1.wn =
    true := by
  decide +kernel

/-- The cells of row 86 of face 1 pass. -/
theorem rowC1_86 : cellsRow4 faceC1 etaC (0) (20) (40) (60) dC1_86 dC1_87 dC1_88 dC1_89 faceC1.wn =
    true := by
  decide +kernel

/-- The cells of row 87 of face 1 pass. -/
theorem rowC1_87 : cellsRow4 faceC1 etaC (20) (40) (60) (80) dC1_87 dC1_88 dC1_89 dC1_90 faceC1.wn =
    true := by
  decide +kernel

/-- The cells of row 88 of face 1 pass. -/
theorem rowC1_88 : cellsRow4 faceC1 etaC (40) (60) (80) (100) dC1_88 dC1_89 dC1_90 dC1_91 faceC1.wn
    = true := by
  decide +kernel

/-- The cells of row 89 of face 1 pass. -/
theorem rowC1_89 : cellsRow4 faceC1 etaC (60) (80) (100) (120) dC1_89 dC1_90 dC1_91 dC1_92 faceC1.wn
    = true := by
  decide +kernel

/-- The cells of row 90 of face 1 pass. -/
theorem rowC1_90 : cellsRow4 faceC1 etaC (80) (100) (120) (140) dC1_90 dC1_91 dC1_92 dC1_93
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 91 of face 1 pass. -/
theorem rowC1_91 : cellsRow4 faceC1 etaC (100) (120) (140) (160) dC1_91 dC1_92 dC1_93 dC1_94
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 92 of face 1 pass. -/
theorem rowC1_92 : cellsRow4 faceC1 etaC (120) (140) (160) (180) dC1_92 dC1_93 dC1_94 dC1_95
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 93 of face 1 pass. -/
theorem rowC1_93 : cellsRow4 faceC1 etaC (140) (160) (180) (200) dC1_93 dC1_94 dC1_95 dC1_96
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 94 of face 1 pass. -/
theorem rowC1_94 : cellsRow4 faceC1 etaC (160) (180) (200) (220) dC1_94 dC1_95 dC1_96 dC1_97
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 95 of face 1 pass. -/
theorem rowC1_95 : cellsRow4 faceC1 etaC (180) (200) (220) (240) dC1_95 dC1_96 dC1_97 dC1_98
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 96 of face 1 pass. -/
theorem rowC1_96 : cellsRow4 faceC1 etaC (200) (220) (240) (260) dC1_96 dC1_97 dC1_98 dC1_99
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 97 of face 1 pass. -/
theorem rowC1_97 : cellsRow4 faceC1 etaC (220) (240) (260) (280) dC1_97 dC1_98 dC1_99 dC1_100
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 98 of face 1 pass. -/
theorem rowC1_98 : cellsRow4 faceC1 etaC (240) (260) (280) (300) dC1_98 dC1_99 dC1_100 dC1_101
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 99 of face 1 pass. -/
theorem rowC1_99 : cellsRow4 faceC1 etaC (260) (280) (300) (320) dC1_99 dC1_100 dC1_101 dC1_102
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 100 of face 1 pass. -/
theorem rowC1_100 : cellsRow4 faceC1 etaC (280) (300) (320) (340) dC1_100 dC1_101 dC1_102 dC1_103
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 101 of face 1 pass. -/
theorem rowC1_101 : cellsRow4 faceC1 etaC (300) (320) (340) (360) dC1_101 dC1_102 dC1_103 dC1_104
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 102 of face 1 pass. -/
theorem rowC1_102 : cellsRow4 faceC1 etaC (320) (340) (360) (380) dC1_102 dC1_103 dC1_104 dC1_105
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 103 of face 1 pass. -/
theorem rowC1_103 : cellsRow4 faceC1 etaC (340) (360) (380) (400) dC1_103 dC1_104 dC1_105 dC1_106
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 104 of face 1 pass. -/
theorem rowC1_104 : cellsRow4 faceC1 etaC (360) (380) (400) (420) dC1_104 dC1_105 dC1_106 dC1_107
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 105 of face 1 pass. -/
theorem rowC1_105 : cellsRow4 faceC1 etaC (380) (400) (420) (440) dC1_105 dC1_106 dC1_107 dC1_108
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 106 of face 1 pass. -/
theorem rowC1_106 : cellsRow4 faceC1 etaC (400) (420) (440) (460) dC1_106 dC1_107 dC1_108 dC1_109
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 107 of face 1 pass. -/
theorem rowC1_107 : cellsRow4 faceC1 etaC (420) (440) (460) (480) dC1_107 dC1_108 dC1_109 dC1_110
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 108 of face 1 pass. -/
theorem rowC1_108 : cellsRow4 faceC1 etaC (440) (460) (480) (500) dC1_108 dC1_109 dC1_110 dC1_111
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 109 of face 1 pass. -/
theorem rowC1_109 : cellsRow4 faceC1 etaC (460) (480) (500) (520) dC1_109 dC1_110 dC1_111 dC1_112
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 110 of face 1 pass. -/
theorem rowC1_110 : cellsRow4 faceC1 etaC (480) (500) (520) (540) dC1_110 dC1_111 dC1_112 dC1_113
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 111 of face 1 pass. -/
theorem rowC1_111 : cellsRow4 faceC1 etaC (500) (520) (540) (560) dC1_111 dC1_112 dC1_113 dC1_114
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 112 of face 1 pass. -/
theorem rowC1_112 : cellsRow4 faceC1 etaC (520) (540) (560) (580) dC1_112 dC1_113 dC1_114 dC1_115
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 113 of face 1 pass. -/
theorem rowC1_113 : cellsRow4 faceC1 etaC (540) (560) (580) (600) dC1_113 dC1_114 dC1_115 dC1_116
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 114 of face 1 pass. -/
theorem rowC1_114 : cellsRow4 faceC1 etaC (560) (580) (600) (620) dC1_114 dC1_115 dC1_116 dC1_117
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 115 of face 1 pass. -/
theorem rowC1_115 : cellsRow4 faceC1 etaC (580) (600) (620) (640) dC1_115 dC1_116 dC1_117 dC1_118
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 116 of face 1 pass. -/
theorem rowC1_116 : cellsRow4 faceC1 etaC (600) (620) (640) (660) dC1_116 dC1_117 dC1_118 dC1_119
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 117 of face 1 pass. -/
theorem rowC1_117 : cellsRow4 faceC1 etaC (620) (640) (660) (680) dC1_117 dC1_118 dC1_119 dC1_120
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 118 of face 1 pass. -/
theorem rowC1_118 : cellsRow4 faceC1 etaC (640) (660) (680) (700) dC1_118 dC1_119 dC1_120 dC1_121
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 119 of face 1 pass. -/
theorem rowC1_119 : cellsRow4 faceC1 etaC (660) (680) (700) (720) dC1_119 dC1_120 dC1_121 dC1_122
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 120 of face 1 pass. -/
theorem rowC1_120 : cellsRow4 faceC1 etaC (680) (700) (720) (740) dC1_120 dC1_121 dC1_122 dC1_123
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 121 of face 1 pass. -/
theorem rowC1_121 : cellsRow4 faceC1 etaC (700) (720) (740) (760) dC1_121 dC1_122 dC1_123 dC1_124
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 122 of face 1 pass. -/
theorem rowC1_122 : cellsRow4 faceC1 etaC (720) (740) (760) (780) dC1_122 dC1_123 dC1_124 dC1_125
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 123 of face 1 pass. -/
theorem rowC1_123 : cellsRow4 faceC1 etaC (740) (760) (780) (800) dC1_123 dC1_124 dC1_125 dC1_126
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 124 of face 1 pass. -/
theorem rowC1_124 : cellsRow4 faceC1 etaC (760) (780) (800) (820) dC1_124 dC1_125 dC1_126 dC1_127
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 125 of face 1 pass. -/
theorem rowC1_125 : cellsRow4 faceC1 etaC (780) (800) (820) (840) dC1_125 dC1_126 dC1_127 dC1_128
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 126 of face 1 pass. -/
theorem rowC1_126 : cellsRow4 faceC1 etaC (800) (820) (840) (860) dC1_126 dC1_127 dC1_128 dC1_129
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 127 of face 1 pass. -/
theorem rowC1_127 : cellsRow4 faceC1 etaC (820) (840) (860) (880) dC1_127 dC1_128 dC1_129 dC1_130
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 128 of face 1 pass. -/
theorem rowC1_128 : cellsRow4 faceC1 etaC (840) (860) (880) (900) dC1_128 dC1_129 dC1_130 dC1_131
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 129 of face 1 pass. -/
theorem rowC1_129 : cellsRow4 faceC1 etaC (860) (880) (900) (920) dC1_129 dC1_130 dC1_131 dC1_132
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 130 of face 1 pass. -/
theorem rowC1_130 : cellsRow4 faceC1 etaC (880) (900) (920) (940) dC1_130 dC1_131 dC1_132 dC1_133
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 131 of face 1 pass. -/
theorem rowC1_131 : cellsRow4 faceC1 etaC (900) (920) (940) (960) dC1_131 dC1_132 dC1_133 dC1_134
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 132 of face 1 pass. -/
theorem rowC1_132 : cellsRow4 faceC1 etaC (920) (940) (960) (980) dC1_132 dC1_133 dC1_134 dC1_135
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 133 of face 1 pass. -/
theorem rowC1_133 : cellsRow4 faceC1 etaC (940) (960) (980) (1000) dC1_133 dC1_134 dC1_135 dC1_136
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 134 of face 1 pass. -/
theorem rowC1_134 : cellsRow4 faceC1 etaC (960) (980) (1000) (1020) dC1_134 dC1_135 dC1_136 dC1_137
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 135 of face 1 pass. -/
theorem rowC1_135 : cellsRow4 faceC1 etaC (980) (1000) (1020) (1040) dC1_135 dC1_136 dC1_137 dC1_138
    faceC1.wn = true := by
  decide +kernel

/-- The cells of row 136 of face 1 pass. -/
theorem rowC1_136 : cellsRow4 faceC1 etaC (1000) (1020) (1040) (1060) dC1_136 dC1_137 dC1_138
    dC1_139 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 137 of face 1 pass. -/
theorem rowC1_137 : cellsRow4 faceC1 etaC (1020) (1040) (1060) (1080) dC1_137 dC1_138 dC1_139
    dC1_140 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 138 of face 1 pass. -/
theorem rowC1_138 : cellsRow4 faceC1 etaC (1040) (1060) (1080) (1100) dC1_138 dC1_139 dC1_140
    dC1_141 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 139 of face 1 pass. -/
theorem rowC1_139 : cellsRow4 faceC1 etaC (1060) (1080) (1100) (1120) dC1_139 dC1_140 dC1_141
    dC1_142 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 140 of face 1 pass. -/
theorem rowC1_140 : cellsRow4 faceC1 etaC (1080) (1100) (1120) (1140) dC1_140 dC1_141 dC1_142
    dC1_143 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 141 of face 1 pass. -/
theorem rowC1_141 : cellsRow4 faceC1 etaC (1100) (1120) (1140) (1160) dC1_141 dC1_142 dC1_143
    dC1_144 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 142 of face 1 pass. -/
theorem rowC1_142 : cellsRow4 faceC1 etaC (1120) (1140) (1160) (1180) dC1_142 dC1_143 dC1_144
    dC1_145 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 143 of face 1 pass. -/
theorem rowC1_143 : cellsRow4 faceC1 etaC (1140) (1160) (1180) (1200) dC1_143 dC1_144 dC1_145
    dC1_146 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 144 of face 1 pass. -/
theorem rowC1_144 : cellsRow4 faceC1 etaC (1160) (1180) (1200) (1220) dC1_144 dC1_145 dC1_146
    dC1_147 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 145 of face 1 pass. -/
theorem rowC1_145 : cellsRow4 faceC1 etaC (1180) (1200) (1220) (1240) dC1_145 dC1_146 dC1_147
    dC1_148 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 146 of face 1 pass. -/
theorem rowC1_146 : cellsRow4 faceC1 etaC (1200) (1220) (1240) (1260) dC1_146 dC1_147 dC1_148
    dC1_149 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 147 of face 1 pass. -/
theorem rowC1_147 : cellsRow4 faceC1 etaC (1220) (1240) (1260) (1280) dC1_147 dC1_148 dC1_149
    dC1_150 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 148 of face 1 pass. -/
theorem rowC1_148 : cellsRow4 faceC1 etaC (1240) (1260) (1280) (1300) dC1_148 dC1_149 dC1_150
    dC1_151 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 149 of face 1 pass. -/
theorem rowC1_149 : cellsRow4 faceC1 etaC (1260) (1280) (1300) (1320) dC1_149 dC1_150 dC1_151
    dC1_152 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 150 of face 1 pass. -/
theorem rowC1_150 : cellsRow4 faceC1 etaC (1280) (1300) (1320) (1340) dC1_150 dC1_151 dC1_152
    dC1_153 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 151 of face 1 pass. -/
theorem rowC1_151 : cellsRow4 faceC1 etaC (1300) (1320) (1340) (1360) dC1_151 dC1_152 dC1_153
    dC1_154 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 152 of face 1 pass. -/
theorem rowC1_152 : cellsRow4 faceC1 etaC (1320) (1340) (1360) (1380) dC1_152 dC1_153 dC1_154
    dC1_155 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 153 of face 1 pass. -/
theorem rowC1_153 : cellsRow4 faceC1 etaC (1340) (1360) (1380) (1400) dC1_153 dC1_154 dC1_155
    dC1_156 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 154 of face 1 pass. -/
theorem rowC1_154 : cellsRow4 faceC1 etaC (1360) (1380) (1400) (1420) dC1_154 dC1_155 dC1_156
    dC1_157 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 155 of face 1 pass. -/
theorem rowC1_155 : cellsRow4 faceC1 etaC (1380) (1400) (1420) (1440) dC1_155 dC1_156 dC1_157
    dC1_158 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 156 of face 1 pass. -/
theorem rowC1_156 : cellsRow4 faceC1 etaC (1400) (1420) (1440) (1460) dC1_156 dC1_157 dC1_158
    dC1_159 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 157 of face 1 pass. -/
theorem rowC1_157 : cellsRow4 faceC1 etaC (1420) (1440) (1460) (1480) dC1_157 dC1_158 dC1_159
    dC1_160 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 158 of face 1 pass. -/
theorem rowC1_158 : cellsRow4 faceC1 etaC (1440) (1460) (1480) (1500) dC1_158 dC1_159 dC1_160
    dC1_161 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 159 of face 1 pass. -/
theorem rowC1_159 : cellsRow4 faceC1 etaC (1460) (1480) (1500) (1520) dC1_159 dC1_160 dC1_161
    dC1_162 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 160 of face 1 pass. -/
theorem rowC1_160 : cellsRow4 faceC1 etaC (1480) (1500) (1520) (1540) dC1_160 dC1_161 dC1_162
    dC1_163 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 161 of face 1 pass. -/
theorem rowC1_161 : cellsRow4 faceC1 etaC (1500) (1520) (1540) (1560) dC1_161 dC1_162 dC1_163
    dC1_164 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 162 of face 1 pass. -/
theorem rowC1_162 : cellsRow4 faceC1 etaC (1520) (1540) (1560) (1580) dC1_162 dC1_163 dC1_164
    dC1_165 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 163 of face 1 pass. -/
theorem rowC1_163 : cellsRow4 faceC1 etaC (1540) (1560) (1580) (1600) dC1_163 dC1_164 dC1_165
    dC1_166 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 164 of face 1 pass. -/
theorem rowC1_164 : cellsRow4 faceC1 etaC (1560) (1580) (1600) (1620) dC1_164 dC1_165 dC1_166
    dC1_167 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 165 of face 1 pass. -/
theorem rowC1_165 : cellsRow4 faceC1 etaC (1580) (1600) (1620) (1640) dC1_165 dC1_166 dC1_167
    dC1_168 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 166 of face 1 pass. -/
theorem rowC1_166 : cellsRow4 faceC1 etaC (1600) (1620) (1640) (1660) dC1_166 dC1_167 dC1_168
    dC1_169 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 167 of face 1 pass. -/
theorem rowC1_167 : cellsRow4 faceC1 etaC (1620) (1640) (1660) (1680) dC1_167 dC1_168 dC1_169
    dC1_170 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 168 of face 1 pass. -/
theorem rowC1_168 : cellsRow4 faceC1 etaC (1640) (1660) (1680) (1700) dC1_168 dC1_169 dC1_170
    dC1_171 faceC1.wn = true := by
  decide +kernel

/-- The cells of row 169 of face 1 pass. -/
theorem rowC1_169 : cellsRow4 faceC1 etaC (1660) (1680) (1700) (1720) dC1_169 dC1_170 dC1_171
    dC1_172 faceC1.wn = true := by
  decide +kernel

/-- **All cells of face 1 pass** (`η = 3540573·2⁻⁴⁰`). -/
theorem cellsC1 : cellsAll4 etaC faceC1 gridC1 dataC1 = true :=
cellsAll4_cons rowC1_0 <| cellsAll4_cons rowC1_1 <| cellsAll4_cons rowC1_2 <| cellsAll4_cons rowC1_3
    <| cellsAll4_cons rowC1_4 <| cellsAll4_cons rowC1_5 <| cellsAll4_cons rowC1_6 <| cellsAll4_cons
    rowC1_7 <| cellsAll4_cons rowC1_8 <| cellsAll4_cons rowC1_9 <| cellsAll4_cons rowC1_10 <|
    cellsAll4_cons rowC1_11 <| cellsAll4_cons rowC1_12 <| cellsAll4_cons rowC1_13 <| cellsAll4_cons
    rowC1_14 <| cellsAll4_cons rowC1_15 <| cellsAll4_cons rowC1_16 <| cellsAll4_cons rowC1_17 <|
    cellsAll4_cons rowC1_18 <| cellsAll4_cons rowC1_19 <| cellsAll4_cons rowC1_20 <| cellsAll4_cons
    rowC1_21 <| cellsAll4_cons rowC1_22 <| cellsAll4_cons rowC1_23 <| cellsAll4_cons rowC1_24 <|
    cellsAll4_cons rowC1_25 <| cellsAll4_cons rowC1_26 <| cellsAll4_cons rowC1_27 <| cellsAll4_cons
    rowC1_28 <| cellsAll4_cons rowC1_29 <| cellsAll4_cons rowC1_30 <| cellsAll4_cons rowC1_31 <|
    cellsAll4_cons rowC1_32 <| cellsAll4_cons rowC1_33 <| cellsAll4_cons rowC1_34 <| cellsAll4_cons
    rowC1_35 <| cellsAll4_cons rowC1_36 <| cellsAll4_cons rowC1_37 <| cellsAll4_cons rowC1_38 <|
    cellsAll4_cons rowC1_39 <| cellsAll4_cons rowC1_40 <| cellsAll4_cons rowC1_41 <| cellsAll4_cons
    rowC1_42 <| cellsAll4_cons rowC1_43 <| cellsAll4_cons rowC1_44 <| cellsAll4_cons rowC1_45 <|
    cellsAll4_cons rowC1_46 <| cellsAll4_cons rowC1_47 <| cellsAll4_cons rowC1_48 <| cellsAll4_cons
    rowC1_49 <| cellsAll4_cons rowC1_50 <| cellsAll4_cons rowC1_51 <| cellsAll4_cons rowC1_52 <|
    cellsAll4_cons rowC1_53 <| cellsAll4_cons rowC1_54 <| cellsAll4_cons rowC1_55 <| cellsAll4_cons
    rowC1_56 <| cellsAll4_cons rowC1_57 <| cellsAll4_cons rowC1_58 <| cellsAll4_cons rowC1_59 <|
    cellsAll4_cons rowC1_60 <| cellsAll4_cons rowC1_61 <| cellsAll4_cons rowC1_62 <| cellsAll4_cons
    rowC1_63 <| cellsAll4_cons rowC1_64 <| cellsAll4_cons rowC1_65 <| cellsAll4_cons rowC1_66 <|
    cellsAll4_cons rowC1_67 <| cellsAll4_cons rowC1_68 <| cellsAll4_cons rowC1_69 <| cellsAll4_cons
    rowC1_70 <| cellsAll4_cons rowC1_71 <| cellsAll4_cons rowC1_72 <| cellsAll4_cons rowC1_73 <|
    cellsAll4_cons rowC1_74 <| cellsAll4_cons rowC1_75 <| cellsAll4_cons rowC1_76 <| cellsAll4_cons
    rowC1_77 <| cellsAll4_cons rowC1_78 <| cellsAll4_cons rowC1_79 <| cellsAll4_cons rowC1_80 <|
    cellsAll4_cons rowC1_81 <| cellsAll4_cons rowC1_82 <| cellsAll4_cons rowC1_83 <| cellsAll4_cons
    rowC1_84 <| cellsAll4_cons rowC1_85 <| cellsAll4_cons rowC1_86 <| cellsAll4_cons rowC1_87 <|
    cellsAll4_cons rowC1_88 <| cellsAll4_cons rowC1_89 <| cellsAll4_cons rowC1_90 <| cellsAll4_cons
    rowC1_91 <| cellsAll4_cons rowC1_92 <| cellsAll4_cons rowC1_93 <| cellsAll4_cons rowC1_94 <|
    cellsAll4_cons rowC1_95 <| cellsAll4_cons rowC1_96 <| cellsAll4_cons rowC1_97 <| cellsAll4_cons
    rowC1_98 <| cellsAll4_cons rowC1_99 <| cellsAll4_cons rowC1_100 <| cellsAll4_cons rowC1_101 <|
    cellsAll4_cons rowC1_102 <| cellsAll4_cons rowC1_103 <| cellsAll4_cons rowC1_104 <|
    cellsAll4_cons rowC1_105 <| cellsAll4_cons rowC1_106 <| cellsAll4_cons rowC1_107 <|
    cellsAll4_cons rowC1_108 <| cellsAll4_cons rowC1_109 <| cellsAll4_cons rowC1_110 <|
    cellsAll4_cons rowC1_111 <| cellsAll4_cons rowC1_112 <| cellsAll4_cons rowC1_113 <|
    cellsAll4_cons rowC1_114 <| cellsAll4_cons rowC1_115 <| cellsAll4_cons rowC1_116 <|
    cellsAll4_cons rowC1_117 <| cellsAll4_cons rowC1_118 <| cellsAll4_cons rowC1_119 <|
    cellsAll4_cons rowC1_120 <| cellsAll4_cons rowC1_121 <| cellsAll4_cons rowC1_122 <|
    cellsAll4_cons rowC1_123 <| cellsAll4_cons rowC1_124 <| cellsAll4_cons rowC1_125 <|
    cellsAll4_cons rowC1_126 <| cellsAll4_cons rowC1_127 <| cellsAll4_cons rowC1_128 <|
    cellsAll4_cons rowC1_129 <| cellsAll4_cons rowC1_130 <| cellsAll4_cons rowC1_131 <|
    cellsAll4_cons rowC1_132 <| cellsAll4_cons rowC1_133 <| cellsAll4_cons rowC1_134 <|
    cellsAll4_cons rowC1_135 <| cellsAll4_cons rowC1_136 <| cellsAll4_cons rowC1_137 <|
    cellsAll4_cons rowC1_138 <| cellsAll4_cons rowC1_139 <| cellsAll4_cons rowC1_140 <|
    cellsAll4_cons rowC1_141 <| cellsAll4_cons rowC1_142 <| cellsAll4_cons rowC1_143 <|
    cellsAll4_cons rowC1_144 <| cellsAll4_cons rowC1_145 <| cellsAll4_cons rowC1_146 <|
    cellsAll4_cons rowC1_147 <| cellsAll4_cons rowC1_148 <| cellsAll4_cons rowC1_149 <|
    cellsAll4_cons rowC1_150 <| cellsAll4_cons rowC1_151 <| cellsAll4_cons rowC1_152 <|
    cellsAll4_cons rowC1_153 <| cellsAll4_cons rowC1_154 <| cellsAll4_cons rowC1_155 <|
    cellsAll4_cons rowC1_156 <| cellsAll4_cons rowC1_157 <| cellsAll4_cons rowC1_158 <|
    cellsAll4_cons rowC1_159 <| cellsAll4_cons rowC1_160 <| cellsAll4_cons rowC1_161 <|
    cellsAll4_cons rowC1_162 <| cellsAll4_cons rowC1_163 <| cellsAll4_cons rowC1_164 <|
    cellsAll4_cons rowC1_165 <| cellsAll4_cons rowC1_166 <| cellsAll4_cons rowC1_167 <|
    cellsAll4_cons rowC1_168 <| cellsAll4_cons rowC1_169 <| cellsAll4_end

/-- Face 1 carries the proved `hel` constants. -/
theorem face4OK_1 : Face4OK faceC1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [faceC1] <;> norm_num

/-- The line facts of face 1. -/
theorem linesC_1 : List.Forall₂ (fun m L => List.Forall₂ (LVal filsC faceC1 m) faceC1.wn L ∧
    QuadP (LW filsC faceC1 m) faceC1.wn L) gridC1 dataC1 :=
.cons (line_facts face4OK_1 lC1_0).1 <| .cons (line_facts face4OK_1 lC1_1).1 <| .cons (line_facts
    face4OK_1 lC1_2).1 <| .cons (line_facts face4OK_1 lC1_3).1 <| .cons (line_facts face4OK_1
    lC1_4).1 <| .cons (line_facts face4OK_1 lC1_5).1 <| .cons (line_facts face4OK_1 lC1_6).1 <|
    .cons (line_facts face4OK_1 lC1_7).1 <| .cons (line_facts face4OK_1 lC1_8).1 <| .cons
    (line_facts face4OK_1 lC1_9).1 <| .cons (line_facts face4OK_1 lC1_10).1 <| .cons (line_facts
    face4OK_1 lC1_11).1 <| .cons (line_facts face4OK_1 lC1_12).1 <| .cons (line_facts face4OK_1
    lC1_13).1 <| .cons (line_facts face4OK_1 lC1_14).1 <| .cons (line_facts face4OK_1 lC1_15).1 <|
    .cons (line_facts face4OK_1 lC1_16).1 <| .cons (line_facts face4OK_1 lC1_17).1 <| .cons
    (line_facts face4OK_1 lC1_18).1 <| .cons (line_facts face4OK_1 lC1_19).1 <| .cons (line_facts
    face4OK_1 lC1_20).1 <| .cons (line_facts face4OK_1 lC1_21).1 <| .cons (line_facts face4OK_1
    lC1_22).1 <| .cons (line_facts face4OK_1 lC1_23).1 <| .cons (line_facts face4OK_1 lC1_24).1 <|
    .cons (line_facts face4OK_1 lC1_25).1 <| .cons (line_facts face4OK_1 lC1_26).1 <| .cons
    (line_facts face4OK_1 lC1_27).1 <| .cons (line_facts face4OK_1 lC1_28).1 <| .cons (line_facts
    face4OK_1 lC1_29).1 <| .cons (line_facts face4OK_1 lC1_30).1 <| .cons (line_facts face4OK_1
    lC1_31).1 <| .cons (line_facts face4OK_1 lC1_32).1 <| .cons (line_facts face4OK_1 lC1_33).1 <|
    .cons (line_facts face4OK_1 lC1_34).1 <| .cons (line_facts face4OK_1 lC1_35).1 <| .cons
    (line_facts face4OK_1 lC1_36).1 <| .cons (line_facts face4OK_1 lC1_37).1 <| .cons (line_facts
    face4OK_1 lC1_38).1 <| .cons (line_facts face4OK_1 lC1_39).1 <| .cons (line_facts face4OK_1
    lC1_40).1 <| .cons (line_facts face4OK_1 lC1_41).1 <| .cons (line_facts face4OK_1 lC1_42).1 <|
    .cons (line_facts face4OK_1 lC1_43).1 <| .cons (line_facts face4OK_1 lC1_44).1 <| .cons
    (line_facts face4OK_1 lC1_45).1 <| .cons (line_facts face4OK_1 lC1_46).1 <| .cons (line_facts
    face4OK_1 lC1_47).1 <| .cons (line_facts face4OK_1 lC1_48).1 <| .cons (line_facts face4OK_1
    lC1_49).1 <| .cons (line_facts face4OK_1 lC1_50).1 <| .cons (line_facts face4OK_1 lC1_51).1 <|
    .cons (line_facts face4OK_1 lC1_52).1 <| .cons (line_facts face4OK_1 lC1_53).1 <| .cons
    (line_facts face4OK_1 lC1_54).1 <| .cons (line_facts face4OK_1 lC1_55).1 <| .cons (line_facts
    face4OK_1 lC1_56).1 <| .cons (line_facts face4OK_1 lC1_57).1 <| .cons (line_facts face4OK_1
    lC1_58).1 <| .cons (line_facts face4OK_1 lC1_59).1 <| .cons (line_facts face4OK_1 lC1_60).1 <|
    .cons (line_facts face4OK_1 lC1_61).1 <| .cons (line_facts face4OK_1 lC1_62).1 <| .cons
    (line_facts face4OK_1 lC1_63).1 <| .cons (line_facts face4OK_1 lC1_64).1 <| .cons (line_facts
    face4OK_1 lC1_65).1 <| .cons (line_facts face4OK_1 lC1_66).1 <| .cons (line_facts face4OK_1
    lC1_67).1 <| .cons (line_facts face4OK_1 lC1_68).1 <| .cons (line_facts face4OK_1 lC1_69).1 <|
    .cons (line_facts face4OK_1 lC1_70).1 <| .cons (line_facts face4OK_1 lC1_71).1 <| .cons
    (line_facts face4OK_1 lC1_72).1 <| .cons (line_facts face4OK_1 lC1_73).1 <| .cons (line_facts
    face4OK_1 lC1_74).1 <| .cons (line_facts face4OK_1 lC1_75).1 <| .cons (line_facts face4OK_1
    lC1_76).1 <| .cons (line_facts face4OK_1 lC1_77).1 <| .cons (line_facts face4OK_1 lC1_78).1 <|
    .cons (line_facts face4OK_1 lC1_79).1 <| .cons (line_facts face4OK_1 lC1_80).1 <| .cons
    (line_facts face4OK_1 lC1_81).1 <| .cons (line_facts face4OK_1 lC1_82).1 <| .cons (line_facts
    face4OK_1 lC1_83).1 <| .cons (line_facts face4OK_1 lC1_84).1 <| .cons (line_facts face4OK_1
    lC1_85).1 <| .cons (line_facts face4OK_1 lC1_86).1 <| .cons (line_facts face4OK_1 lC1_87).1 <|
    .cons (line_facts face4OK_1 lC1_88).1 <| .cons (line_facts face4OK_1 lC1_89).1 <| .cons
    (line_facts face4OK_1 lC1_90).1 <| .cons (line_facts face4OK_1 lC1_91).1 <| .cons (line_facts
    face4OK_1 lC1_92).1 <| .cons (line_facts face4OK_1 lC1_93).1 <| .cons (line_facts face4OK_1
    lC1_94).1 <| .cons (line_facts face4OK_1 lC1_95).1 <| .cons (line_facts face4OK_1 lC1_96).1 <|
    .cons (line_facts face4OK_1 lC1_97).1 <| .cons (line_facts face4OK_1 lC1_98).1 <| .cons
    (line_facts face4OK_1 lC1_99).1 <| .cons (line_facts face4OK_1 lC1_100).1 <| .cons (line_facts
    face4OK_1 lC1_101).1 <| .cons (line_facts face4OK_1 lC1_102).1 <| .cons (line_facts face4OK_1
    lC1_103).1 <| .cons (line_facts face4OK_1 lC1_104).1 <| .cons (line_facts face4OK_1 lC1_105).1
    <| .cons (line_facts face4OK_1 lC1_106).1 <| .cons (line_facts face4OK_1 lC1_107).1 <| .cons
    (line_facts face4OK_1 lC1_108).1 <| .cons (line_facts face4OK_1 lC1_109).1 <| .cons (line_facts
    face4OK_1 lC1_110).1 <| .cons (line_facts face4OK_1 lC1_111).1 <| .cons (line_facts face4OK_1
    lC1_112).1 <| .cons (line_facts face4OK_1 lC1_113).1 <| .cons (line_facts face4OK_1 lC1_114).1
    <| .cons (line_facts face4OK_1 lC1_115).1 <| .cons (line_facts face4OK_1 lC1_116).1 <| .cons
    (line_facts face4OK_1 lC1_117).1 <| .cons (line_facts face4OK_1 lC1_118).1 <| .cons (line_facts
    face4OK_1 lC1_119).1 <| .cons (line_facts face4OK_1 lC1_120).1 <| .cons (line_facts face4OK_1
    lC1_121).1 <| .cons (line_facts face4OK_1 lC1_122).1 <| .cons (line_facts face4OK_1 lC1_123).1
    <| .cons (line_facts face4OK_1 lC1_124).1 <| .cons (line_facts face4OK_1 lC1_125).1 <| .cons
    (line_facts face4OK_1 lC1_126).1 <| .cons (line_facts face4OK_1 lC1_127).1 <| .cons (line_facts
    face4OK_1 lC1_128).1 <| .cons (line_facts face4OK_1 lC1_129).1 <| .cons (line_facts face4OK_1
    lC1_130).1 <| .cons (line_facts face4OK_1 lC1_131).1 <| .cons (line_facts face4OK_1 lC1_132).1
    <| .cons (line_facts face4OK_1 lC1_133).1 <| .cons (line_facts face4OK_1 lC1_134).1 <| .cons
    (line_facts face4OK_1 lC1_135).1 <| .cons (line_facts face4OK_1 lC1_136).1 <| .cons (line_facts
    face4OK_1 lC1_137).1 <| .cons (line_facts face4OK_1 lC1_138).1 <| .cons (line_facts face4OK_1
    lC1_139).1 <| .cons (line_facts face4OK_1 lC1_140).1 <| .cons (line_facts face4OK_1 lC1_141).1
    <| .cons (line_facts face4OK_1 lC1_142).1 <| .cons (line_facts face4OK_1 lC1_143).1 <| .cons
    (line_facts face4OK_1 lC1_144).1 <| .cons (line_facts face4OK_1 lC1_145).1 <| .cons (line_facts
    face4OK_1 lC1_146).1 <| .cons (line_facts face4OK_1 lC1_147).1 <| .cons (line_facts face4OK_1
    lC1_148).1 <| .cons (line_facts face4OK_1 lC1_149).1 <| .cons (line_facts face4OK_1 lC1_150).1
    <| .cons (line_facts face4OK_1 lC1_151).1 <| .cons (line_facts face4OK_1 lC1_152).1 <| .cons
    (line_facts face4OK_1 lC1_153).1 <| .cons (line_facts face4OK_1 lC1_154).1 <| .cons (line_facts
    face4OK_1 lC1_155).1 <| .cons (line_facts face4OK_1 lC1_156).1 <| .cons (line_facts face4OK_1
    lC1_157).1 <| .cons (line_facts face4OK_1 lC1_158).1 <| .cons (line_facts face4OK_1 lC1_159).1
    <| .cons (line_facts face4OK_1 lC1_160).1 <| .cons (line_facts face4OK_1 lC1_161).1 <| .cons
    (line_facts face4OK_1 lC1_162).1 <| .cons (line_facts face4OK_1 lC1_163).1 <| .cons (line_facts
    face4OK_1 lC1_164).1 <| .cons (line_facts face4OK_1 lC1_165).1 <| .cons (line_facts face4OK_1
    lC1_166).1 <| .cons (line_facts face4OK_1 lC1_167).1 <| .cons (line_facts face4OK_1 lC1_168).1
    <| .cons (line_facts face4OK_1 lC1_169).1 <| .cons (line_facts face4OK_1 lC1_170).1 <| .cons
    (line_facts face4OK_1 lC1_171).1 <| .cons (line_facts face4OK_1 lC1_172).1 <| .nil

/-- The strip facts of face 1. -/
theorem rowsC_1 : RowsT filsC faceC1 gridC1 dataC1 :=
rowsT_cons (line_facts face4OK_1 lC1_1).2 <| rowsT_cons (line_facts face4OK_1 lC1_2).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_3).2 <| rowsT_cons (line_facts face4OK_1 lC1_4).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_5).2 <| rowsT_cons (line_facts face4OK_1 lC1_6).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_7).2 <| rowsT_cons (line_facts face4OK_1 lC1_8).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_9).2 <| rowsT_cons (line_facts face4OK_1 lC1_10).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_11).2 <| rowsT_cons (line_facts face4OK_1 lC1_12).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_13).2 <| rowsT_cons (line_facts face4OK_1 lC1_14).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_15).2 <| rowsT_cons (line_facts face4OK_1 lC1_16).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_17).2 <| rowsT_cons (line_facts face4OK_1 lC1_18).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_19).2 <| rowsT_cons (line_facts face4OK_1 lC1_20).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_21).2 <| rowsT_cons (line_facts face4OK_1 lC1_22).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_23).2 <| rowsT_cons (line_facts face4OK_1 lC1_24).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_25).2 <| rowsT_cons (line_facts face4OK_1 lC1_26).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_27).2 <| rowsT_cons (line_facts face4OK_1 lC1_28).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_29).2 <| rowsT_cons (line_facts face4OK_1 lC1_30).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_31).2 <| rowsT_cons (line_facts face4OK_1 lC1_32).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_33).2 <| rowsT_cons (line_facts face4OK_1 lC1_34).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_35).2 <| rowsT_cons (line_facts face4OK_1 lC1_36).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_37).2 <| rowsT_cons (line_facts face4OK_1 lC1_38).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_39).2 <| rowsT_cons (line_facts face4OK_1 lC1_40).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_41).2 <| rowsT_cons (line_facts face4OK_1 lC1_42).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_43).2 <| rowsT_cons (line_facts face4OK_1 lC1_44).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_45).2 <| rowsT_cons (line_facts face4OK_1 lC1_46).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_47).2 <| rowsT_cons (line_facts face4OK_1 lC1_48).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_49).2 <| rowsT_cons (line_facts face4OK_1 lC1_50).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_51).2 <| rowsT_cons (line_facts face4OK_1 lC1_52).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_53).2 <| rowsT_cons (line_facts face4OK_1 lC1_54).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_55).2 <| rowsT_cons (line_facts face4OK_1 lC1_56).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_57).2 <| rowsT_cons (line_facts face4OK_1 lC1_58).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_59).2 <| rowsT_cons (line_facts face4OK_1 lC1_60).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_61).2 <| rowsT_cons (line_facts face4OK_1 lC1_62).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_63).2 <| rowsT_cons (line_facts face4OK_1 lC1_64).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_65).2 <| rowsT_cons (line_facts face4OK_1 lC1_66).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_67).2 <| rowsT_cons (line_facts face4OK_1 lC1_68).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_69).2 <| rowsT_cons (line_facts face4OK_1 lC1_70).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_71).2 <| rowsT_cons (line_facts face4OK_1 lC1_72).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_73).2 <| rowsT_cons (line_facts face4OK_1 lC1_74).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_75).2 <| rowsT_cons (line_facts face4OK_1 lC1_76).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_77).2 <| rowsT_cons (line_facts face4OK_1 lC1_78).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_79).2 <| rowsT_cons (line_facts face4OK_1 lC1_80).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_81).2 <| rowsT_cons (line_facts face4OK_1 lC1_82).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_83).2 <| rowsT_cons (line_facts face4OK_1 lC1_84).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_85).2 <| rowsT_cons (line_facts face4OK_1 lC1_86).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_87).2 <| rowsT_cons (line_facts face4OK_1 lC1_88).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_89).2 <| rowsT_cons (line_facts face4OK_1 lC1_90).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_91).2 <| rowsT_cons (line_facts face4OK_1 lC1_92).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_93).2 <| rowsT_cons (line_facts face4OK_1 lC1_94).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_95).2 <| rowsT_cons (line_facts face4OK_1 lC1_96).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_97).2 <| rowsT_cons (line_facts face4OK_1 lC1_98).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_99).2 <| rowsT_cons (line_facts face4OK_1 lC1_100).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_101).2 <| rowsT_cons (line_facts face4OK_1 lC1_102).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_103).2 <| rowsT_cons (line_facts face4OK_1 lC1_104).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_105).2 <| rowsT_cons (line_facts face4OK_1 lC1_106).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_107).2 <| rowsT_cons (line_facts face4OK_1 lC1_108).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_109).2 <| rowsT_cons (line_facts face4OK_1 lC1_110).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_111).2 <| rowsT_cons (line_facts face4OK_1 lC1_112).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_113).2 <| rowsT_cons (line_facts face4OK_1 lC1_114).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_115).2 <| rowsT_cons (line_facts face4OK_1 lC1_116).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_117).2 <| rowsT_cons (line_facts face4OK_1 lC1_118).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_119).2 <| rowsT_cons (line_facts face4OK_1 lC1_120).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_121).2 <| rowsT_cons (line_facts face4OK_1 lC1_122).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_123).2 <| rowsT_cons (line_facts face4OK_1 lC1_124).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_125).2 <| rowsT_cons (line_facts face4OK_1 lC1_126).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_127).2 <| rowsT_cons (line_facts face4OK_1 lC1_128).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_129).2 <| rowsT_cons (line_facts face4OK_1 lC1_130).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_131).2 <| rowsT_cons (line_facts face4OK_1 lC1_132).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_133).2 <| rowsT_cons (line_facts face4OK_1 lC1_134).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_135).2 <| rowsT_cons (line_facts face4OK_1 lC1_136).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_137).2 <| rowsT_cons (line_facts face4OK_1 lC1_138).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_139).2 <| rowsT_cons (line_facts face4OK_1 lC1_140).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_141).2 <| rowsT_cons (line_facts face4OK_1 lC1_142).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_143).2 <| rowsT_cons (line_facts face4OK_1 lC1_144).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_145).2 <| rowsT_cons (line_facts face4OK_1 lC1_146).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_147).2 <| rowsT_cons (line_facts face4OK_1 lC1_148).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_149).2 <| rowsT_cons (line_facts face4OK_1 lC1_150).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_151).2 <| rowsT_cons (line_facts face4OK_1 lC1_152).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_153).2 <| rowsT_cons (line_facts face4OK_1 lC1_154).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_155).2 <| rowsT_cons (line_facts face4OK_1 lC1_156).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_157).2 <| rowsT_cons (line_facts face4OK_1 lC1_158).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_159).2 <| rowsT_cons (line_facts face4OK_1 lC1_160).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_161).2 <| rowsT_cons (line_facts face4OK_1 lC1_162).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_163).2 <| rowsT_cons (line_facts face4OK_1 lC1_164).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_165).2 <| rowsT_cons (line_facts face4OK_1 lC1_166).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_167).2 <| rowsT_cons (line_facts face4OK_1 lC1_168).2 <| rowsT_cons
    (line_facts face4OK_1 lC1_169).2 <| rowsT_cons (line_facts face4OK_1 lC1_170).2 <| rowsT_end

set_option maxRecDepth 20000 in
/-- **The certified bound on face 1.** -/
theorem coverC_1 : RectGood filsC 1 etaC (((-1700 : ℤ) : ℝ) / 4096) (((1700 : ℤ) : ℝ) / 4096)
    (((-95760 : ℤ) : ℝ) / ((917308 : ℕ) : ℝ)) (((95760 : ℤ) : ℝ) / ((917308 : ℕ) : ℝ)) := by
  have h := face_sound filsC faceC1 face4OK_1 etaC (by decide) gridC1 dataC1 linesC_1
    rowsC_1 cellsC1 (by decide)
  rw [show gridC1.length = 173 by decide +kernel, show faceC1.wn.length = 31 by decide +kernel] at h
  rwa [show gridC1.getD 1 0 = -1700 by decide +kernel,
    show gridC1.getD 171 0 = 1700 by decide +kernel,
    show faceC1.wn.getD 1 0 = -95760 by decide +kernel,
    show faceC1.wn.getD 29 0 = 95760 by decide +kernel,
    show faceC1.wd = 917308 from rfl, show faceC1.kind = 1 from rfl] at h

/-- **The cover of face 1.** -/
theorem faceCovC_1 : FaceCovC 1 :=
  ⟨_, _, _, _, coverC_1, by norm_num, by norm_num, by norm_num [faceLoC, aF],
    by norm_num [faceHiC, aF]⟩

end PlasmaLean.Design.PolygonCoil
