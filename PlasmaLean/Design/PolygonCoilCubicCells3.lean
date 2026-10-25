/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCubicLines14
public import PlasmaLean.Design.PolygonCoilCubicLines15
public import PlasmaLean.Design.PolygonCoilCubicLines16
public import PlasmaLean.Design.PolygonCoilCubicLines17
public import PlasmaLean.Design.PolygonCoilCubicLines18
public import PlasmaLean.Design.PolygonCoilCubicLines19
public import PlasmaLean.Design.PolygonCoilCubicFrontier
public import PlasmaLean.Certificates.BoolCert
public import PlasmaLean.Certificates.KernelFact

/-!
# Cubic frontier certificate: the cells and the cover of face 3

* `rowCF_i`: `cellsRow4` on the records of the grid lines `i, …, i+3` of face `F`, by an explicit
  `BCert` certificate (`bool_cert`, `Certificates/BoolCert`): one `&&` step per cell, and per cell
  its geometric conditions and its error bound `Nat.ble … η` as kernel-checked comparison leaves;
* `cellsCF`: all cells of the face pass (`cellsAll4`, assembled from the rows);
* `linesC_F`, `rowsC_F`: the facts certified by the line checks `lCF_k` (`lineOut4_sound`);
* `coverC_F`, `faceCovC_F`: the certified bound on the face (`face_sound`).
-/

public section

namespace PlasmaLean.Design.PolygonCoil

open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator Set Real
  PlasmaLean.Certificates.BoolCert

/-- The line records of face 3. -/
@[expose]
def dataC3 : List (List CRec) := [dC3_0, dC3_1, dC3_2, dC3_3, dC3_4, dC3_5, dC3_6, dC3_7, dC3_8,
    dC3_9, dC3_10, dC3_11, dC3_12, dC3_13, dC3_14, dC3_15, dC3_16, dC3_17, dC3_18, dC3_19, dC3_20,
    dC3_21, dC3_22, dC3_23, dC3_24, dC3_25, dC3_26, dC3_27, dC3_28, dC3_29, dC3_30, dC3_31, dC3_32,
    dC3_33, dC3_34, dC3_35, dC3_36, dC3_37, dC3_38, dC3_39, dC3_40, dC3_41, dC3_42, dC3_43, dC3_44,
    dC3_45, dC3_46, dC3_47, dC3_48, dC3_49, dC3_50, dC3_51, dC3_52, dC3_53, dC3_54, dC3_55, dC3_56,
    dC3_57, dC3_58, dC3_59, dC3_60, dC3_61, dC3_62, dC3_63, dC3_64, dC3_65, dC3_66, dC3_67, dC3_68,
    dC3_69, dC3_70, dC3_71, dC3_72, dC3_73, dC3_74, dC3_75, dC3_76, dC3_77, dC3_78, dC3_79, dC3_80,
    dC3_81, dC3_82, dC3_83, dC3_84, dC3_85, dC3_86, dC3_87, dC3_88, dC3_89, dC3_90, dC3_91, dC3_92,
    dC3_93, dC3_94, dC3_95, dC3_96, dC3_97, dC3_98, dC3_99, dC3_100, dC3_101, dC3_102, dC3_103,
    dC3_104, dC3_105, dC3_106, dC3_107, dC3_108, dC3_109, dC3_110, dC3_111, dC3_112, dC3_113,
    dC3_114, dC3_115, dC3_116, dC3_117, dC3_118, dC3_119, dC3_120, dC3_121, dC3_122, dC3_123,
    dC3_124, dC3_125, dC3_126, dC3_127, dC3_128, dC3_129, dC3_130, dC3_131, dC3_132, dC3_133,
    dC3_134, dC3_135, dC3_136, dC3_137, dC3_138, dC3_139, dC3_140, dC3_141, dC3_142, dC3_143,
    dC3_144, dC3_145, dC3_146, dC3_147, dC3_148, dC3_149, dC3_150, dC3_151, dC3_152, dC3_153,
    dC3_154, dC3_155, dC3_156, dC3_157, dC3_158, dC3_159, dC3_160, dC3_161, dC3_162, dC3_163,
    dC3_164, dC3_165, dC3_166, dC3_167, dC3_168, dC3_169, dC3_170, dC3_171, dC3_172]

/-- The cells of row 0 of face 3 pass. -/
theorem rowC3_0 : cellsRow4 faceC3 etaC (-1720) (-1700) (-1680) (-1660) dC3_0 dC3_1 dC3_2 dC3_3
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 1 of face 3 pass. -/
theorem rowC3_1 : cellsRow4 faceC3 etaC (-1700) (-1680) (-1660) (-1640) dC3_1 dC3_2 dC3_3 dC3_4
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 2 of face 3 pass. -/
theorem rowC3_2 : cellsRow4 faceC3 etaC (-1680) (-1660) (-1640) (-1620) dC3_2 dC3_3 dC3_4 dC3_5
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 3 of face 3 pass. -/
theorem rowC3_3 : cellsRow4 faceC3 etaC (-1660) (-1640) (-1620) (-1600) dC3_3 dC3_4 dC3_5 dC3_6
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 4 of face 3 pass. -/
theorem rowC3_4 : cellsRow4 faceC3 etaC (-1640) (-1620) (-1600) (-1580) dC3_4 dC3_5 dC3_6 dC3_7
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 5 of face 3 pass. -/
theorem rowC3_5 : cellsRow4 faceC3 etaC (-1620) (-1600) (-1580) (-1560) dC3_5 dC3_6 dC3_7 dC3_8
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 6 of face 3 pass. -/
theorem rowC3_6 : cellsRow4 faceC3 etaC (-1600) (-1580) (-1560) (-1540) dC3_6 dC3_7 dC3_8 dC3_9
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 7 of face 3 pass. -/
theorem rowC3_7 : cellsRow4 faceC3 etaC (-1580) (-1560) (-1540) (-1520) dC3_7 dC3_8 dC3_9 dC3_10
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 8 of face 3 pass. -/
theorem rowC3_8 : cellsRow4 faceC3 etaC (-1560) (-1540) (-1520) (-1500) dC3_8 dC3_9 dC3_10 dC3_11
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 9 of face 3 pass. -/
theorem rowC3_9 : cellsRow4 faceC3 etaC (-1540) (-1520) (-1500) (-1480) dC3_9 dC3_10 dC3_11 dC3_12
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 10 of face 3 pass. -/
theorem rowC3_10 : cellsRow4 faceC3 etaC (-1520) (-1500) (-1480) (-1460) dC3_10 dC3_11 dC3_12 dC3_13
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 11 of face 3 pass. -/
theorem rowC3_11 : cellsRow4 faceC3 etaC (-1500) (-1480) (-1460) (-1440) dC3_11 dC3_12 dC3_13 dC3_14
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 12 of face 3 pass. -/
theorem rowC3_12 : cellsRow4 faceC3 etaC (-1480) (-1460) (-1440) (-1420) dC3_12 dC3_13 dC3_14 dC3_15
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 13 of face 3 pass. -/
theorem rowC3_13 : cellsRow4 faceC3 etaC (-1460) (-1440) (-1420) (-1400) dC3_13 dC3_14 dC3_15 dC3_16
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 14 of face 3 pass. -/
theorem rowC3_14 : cellsRow4 faceC3 etaC (-1440) (-1420) (-1400) (-1380) dC3_14 dC3_15 dC3_16 dC3_17
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 15 of face 3 pass. -/
theorem rowC3_15 : cellsRow4 faceC3 etaC (-1420) (-1400) (-1380) (-1360) dC3_15 dC3_16 dC3_17 dC3_18
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 16 of face 3 pass. -/
theorem rowC3_16 : cellsRow4 faceC3 etaC (-1400) (-1380) (-1360) (-1340) dC3_16 dC3_17 dC3_18 dC3_19
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 17 of face 3 pass. -/
theorem rowC3_17 : cellsRow4 faceC3 etaC (-1380) (-1360) (-1340) (-1320) dC3_17 dC3_18 dC3_19 dC3_20
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 18 of face 3 pass. -/
theorem rowC3_18 : cellsRow4 faceC3 etaC (-1360) (-1340) (-1320) (-1300) dC3_18 dC3_19 dC3_20 dC3_21
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 19 of face 3 pass. -/
theorem rowC3_19 : cellsRow4 faceC3 etaC (-1340) (-1320) (-1300) (-1280) dC3_19 dC3_20 dC3_21 dC3_22
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 20 of face 3 pass. -/
theorem rowC3_20 : cellsRow4 faceC3 etaC (-1320) (-1300) (-1280) (-1260) dC3_20 dC3_21 dC3_22 dC3_23
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 21 of face 3 pass. -/
theorem rowC3_21 : cellsRow4 faceC3 etaC (-1300) (-1280) (-1260) (-1240) dC3_21 dC3_22 dC3_23 dC3_24
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 22 of face 3 pass. -/
theorem rowC3_22 : cellsRow4 faceC3 etaC (-1280) (-1260) (-1240) (-1220) dC3_22 dC3_23 dC3_24 dC3_25
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 23 of face 3 pass. -/
theorem rowC3_23 : cellsRow4 faceC3 etaC (-1260) (-1240) (-1220) (-1200) dC3_23 dC3_24 dC3_25 dC3_26
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 24 of face 3 pass. -/
theorem rowC3_24 : cellsRow4 faceC3 etaC (-1240) (-1220) (-1200) (-1180) dC3_24 dC3_25 dC3_26 dC3_27
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 25 of face 3 pass. -/
theorem rowC3_25 : cellsRow4 faceC3 etaC (-1220) (-1200) (-1180) (-1160) dC3_25 dC3_26 dC3_27 dC3_28
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 26 of face 3 pass. -/
theorem rowC3_26 : cellsRow4 faceC3 etaC (-1200) (-1180) (-1160) (-1140) dC3_26 dC3_27 dC3_28 dC3_29
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 27 of face 3 pass. -/
theorem rowC3_27 : cellsRow4 faceC3 etaC (-1180) (-1160) (-1140) (-1120) dC3_27 dC3_28 dC3_29 dC3_30
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 28 of face 3 pass. -/
theorem rowC3_28 : cellsRow4 faceC3 etaC (-1160) (-1140) (-1120) (-1100) dC3_28 dC3_29 dC3_30 dC3_31
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 29 of face 3 pass. -/
theorem rowC3_29 : cellsRow4 faceC3 etaC (-1140) (-1120) (-1100) (-1080) dC3_29 dC3_30 dC3_31 dC3_32
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 30 of face 3 pass. -/
theorem rowC3_30 : cellsRow4 faceC3 etaC (-1120) (-1100) (-1080) (-1060) dC3_30 dC3_31 dC3_32 dC3_33
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 31 of face 3 pass. -/
theorem rowC3_31 : cellsRow4 faceC3 etaC (-1100) (-1080) (-1060) (-1040) dC3_31 dC3_32 dC3_33 dC3_34
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 32 of face 3 pass. -/
theorem rowC3_32 : cellsRow4 faceC3 etaC (-1080) (-1060) (-1040) (-1020) dC3_32 dC3_33 dC3_34 dC3_35
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 33 of face 3 pass. -/
theorem rowC3_33 : cellsRow4 faceC3 etaC (-1060) (-1040) (-1020) (-1000) dC3_33 dC3_34 dC3_35 dC3_36
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 34 of face 3 pass. -/
theorem rowC3_34 : cellsRow4 faceC3 etaC (-1040) (-1020) (-1000) (-980) dC3_34 dC3_35 dC3_36 dC3_37
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 35 of face 3 pass. -/
theorem rowC3_35 : cellsRow4 faceC3 etaC (-1020) (-1000) (-980) (-960) dC3_35 dC3_36 dC3_37 dC3_38
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 36 of face 3 pass. -/
theorem rowC3_36 : cellsRow4 faceC3 etaC (-1000) (-980) (-960) (-940) dC3_36 dC3_37 dC3_38 dC3_39
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 37 of face 3 pass. -/
theorem rowC3_37 : cellsRow4 faceC3 etaC (-980) (-960) (-940) (-920) dC3_37 dC3_38 dC3_39 dC3_40
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 38 of face 3 pass. -/
theorem rowC3_38 : cellsRow4 faceC3 etaC (-960) (-940) (-920) (-900) dC3_38 dC3_39 dC3_40 dC3_41
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 39 of face 3 pass. -/
theorem rowC3_39 : cellsRow4 faceC3 etaC (-940) (-920) (-900) (-880) dC3_39 dC3_40 dC3_41 dC3_42
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 40 of face 3 pass. -/
theorem rowC3_40 : cellsRow4 faceC3 etaC (-920) (-900) (-880) (-860) dC3_40 dC3_41 dC3_42 dC3_43
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 41 of face 3 pass. -/
theorem rowC3_41 : cellsRow4 faceC3 etaC (-900) (-880) (-860) (-840) dC3_41 dC3_42 dC3_43 dC3_44
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 42 of face 3 pass. -/
theorem rowC3_42 : cellsRow4 faceC3 etaC (-880) (-860) (-840) (-820) dC3_42 dC3_43 dC3_44 dC3_45
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 43 of face 3 pass. -/
theorem rowC3_43 : cellsRow4 faceC3 etaC (-860) (-840) (-820) (-800) dC3_43 dC3_44 dC3_45 dC3_46
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 44 of face 3 pass. -/
theorem rowC3_44 : cellsRow4 faceC3 etaC (-840) (-820) (-800) (-780) dC3_44 dC3_45 dC3_46 dC3_47
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 45 of face 3 pass. -/
theorem rowC3_45 : cellsRow4 faceC3 etaC (-820) (-800) (-780) (-760) dC3_45 dC3_46 dC3_47 dC3_48
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 46 of face 3 pass. -/
theorem rowC3_46 : cellsRow4 faceC3 etaC (-800) (-780) (-760) (-740) dC3_46 dC3_47 dC3_48 dC3_49
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 47 of face 3 pass. -/
theorem rowC3_47 : cellsRow4 faceC3 etaC (-780) (-760) (-740) (-720) dC3_47 dC3_48 dC3_49 dC3_50
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 48 of face 3 pass. -/
theorem rowC3_48 : cellsRow4 faceC3 etaC (-760) (-740) (-720) (-700) dC3_48 dC3_49 dC3_50 dC3_51
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 49 of face 3 pass. -/
theorem rowC3_49 : cellsRow4 faceC3 etaC (-740) (-720) (-700) (-680) dC3_49 dC3_50 dC3_51 dC3_52
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 50 of face 3 pass. -/
theorem rowC3_50 : cellsRow4 faceC3 etaC (-720) (-700) (-680) (-660) dC3_50 dC3_51 dC3_52 dC3_53
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 51 of face 3 pass. -/
theorem rowC3_51 : cellsRow4 faceC3 etaC (-700) (-680) (-660) (-640) dC3_51 dC3_52 dC3_53 dC3_54
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 52 of face 3 pass. -/
theorem rowC3_52 : cellsRow4 faceC3 etaC (-680) (-660) (-640) (-620) dC3_52 dC3_53 dC3_54 dC3_55
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 53 of face 3 pass. -/
theorem rowC3_53 : cellsRow4 faceC3 etaC (-660) (-640) (-620) (-600) dC3_53 dC3_54 dC3_55 dC3_56
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 54 of face 3 pass. -/
theorem rowC3_54 : cellsRow4 faceC3 etaC (-640) (-620) (-600) (-580) dC3_54 dC3_55 dC3_56 dC3_57
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 55 of face 3 pass. -/
theorem rowC3_55 : cellsRow4 faceC3 etaC (-620) (-600) (-580) (-560) dC3_55 dC3_56 dC3_57 dC3_58
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 56 of face 3 pass. -/
theorem rowC3_56 : cellsRow4 faceC3 etaC (-600) (-580) (-560) (-540) dC3_56 dC3_57 dC3_58 dC3_59
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 57 of face 3 pass. -/
theorem rowC3_57 : cellsRow4 faceC3 etaC (-580) (-560) (-540) (-520) dC3_57 dC3_58 dC3_59 dC3_60
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 58 of face 3 pass. -/
theorem rowC3_58 : cellsRow4 faceC3 etaC (-560) (-540) (-520) (-500) dC3_58 dC3_59 dC3_60 dC3_61
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 59 of face 3 pass. -/
theorem rowC3_59 : cellsRow4 faceC3 etaC (-540) (-520) (-500) (-480) dC3_59 dC3_60 dC3_61 dC3_62
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 60 of face 3 pass. -/
theorem rowC3_60 : cellsRow4 faceC3 etaC (-520) (-500) (-480) (-460) dC3_60 dC3_61 dC3_62 dC3_63
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 61 of face 3 pass. -/
theorem rowC3_61 : cellsRow4 faceC3 etaC (-500) (-480) (-460) (-440) dC3_61 dC3_62 dC3_63 dC3_64
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 62 of face 3 pass. -/
theorem rowC3_62 : cellsRow4 faceC3 etaC (-480) (-460) (-440) (-420) dC3_62 dC3_63 dC3_64 dC3_65
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 63 of face 3 pass. -/
theorem rowC3_63 : cellsRow4 faceC3 etaC (-460) (-440) (-420) (-400) dC3_63 dC3_64 dC3_65 dC3_66
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 64 of face 3 pass. -/
theorem rowC3_64 : cellsRow4 faceC3 etaC (-440) (-420) (-400) (-380) dC3_64 dC3_65 dC3_66 dC3_67
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 65 of face 3 pass. -/
theorem rowC3_65 : cellsRow4 faceC3 etaC (-420) (-400) (-380) (-360) dC3_65 dC3_66 dC3_67 dC3_68
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 66 of face 3 pass. -/
theorem rowC3_66 : cellsRow4 faceC3 etaC (-400) (-380) (-360) (-340) dC3_66 dC3_67 dC3_68 dC3_69
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 67 of face 3 pass. -/
theorem rowC3_67 : cellsRow4 faceC3 etaC (-380) (-360) (-340) (-320) dC3_67 dC3_68 dC3_69 dC3_70
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 68 of face 3 pass. -/
theorem rowC3_68 : cellsRow4 faceC3 etaC (-360) (-340) (-320) (-300) dC3_68 dC3_69 dC3_70 dC3_71
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 69 of face 3 pass. -/
theorem rowC3_69 : cellsRow4 faceC3 etaC (-340) (-320) (-300) (-280) dC3_69 dC3_70 dC3_71 dC3_72
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 70 of face 3 pass. -/
theorem rowC3_70 : cellsRow4 faceC3 etaC (-320) (-300) (-280) (-260) dC3_70 dC3_71 dC3_72 dC3_73
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 71 of face 3 pass. -/
theorem rowC3_71 : cellsRow4 faceC3 etaC (-300) (-280) (-260) (-240) dC3_71 dC3_72 dC3_73 dC3_74
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 72 of face 3 pass. -/
theorem rowC3_72 : cellsRow4 faceC3 etaC (-280) (-260) (-240) (-220) dC3_72 dC3_73 dC3_74 dC3_75
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 73 of face 3 pass. -/
theorem rowC3_73 : cellsRow4 faceC3 etaC (-260) (-240) (-220) (-200) dC3_73 dC3_74 dC3_75 dC3_76
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 74 of face 3 pass. -/
theorem rowC3_74 : cellsRow4 faceC3 etaC (-240) (-220) (-200) (-180) dC3_74 dC3_75 dC3_76 dC3_77
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 75 of face 3 pass. -/
theorem rowC3_75 : cellsRow4 faceC3 etaC (-220) (-200) (-180) (-160) dC3_75 dC3_76 dC3_77 dC3_78
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 76 of face 3 pass. -/
theorem rowC3_76 : cellsRow4 faceC3 etaC (-200) (-180) (-160) (-140) dC3_76 dC3_77 dC3_78 dC3_79
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 77 of face 3 pass. -/
theorem rowC3_77 : cellsRow4 faceC3 etaC (-180) (-160) (-140) (-120) dC3_77 dC3_78 dC3_79 dC3_80
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 78 of face 3 pass. -/
theorem rowC3_78 : cellsRow4 faceC3 etaC (-160) (-140) (-120) (-100) dC3_78 dC3_79 dC3_80 dC3_81
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 79 of face 3 pass. -/
theorem rowC3_79 : cellsRow4 faceC3 etaC (-140) (-120) (-100) (-80) dC3_79 dC3_80 dC3_81 dC3_82
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 80 of face 3 pass. -/
theorem rowC3_80 : cellsRow4 faceC3 etaC (-120) (-100) (-80) (-60) dC3_80 dC3_81 dC3_82 dC3_83
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 81 of face 3 pass. -/
theorem rowC3_81 : cellsRow4 faceC3 etaC (-100) (-80) (-60) (-40) dC3_81 dC3_82 dC3_83 dC3_84
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 82 of face 3 pass. -/
theorem rowC3_82 : cellsRow4 faceC3 etaC (-80) (-60) (-40) (-20) dC3_82 dC3_83 dC3_84 dC3_85
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 83 of face 3 pass. -/
theorem rowC3_83 : cellsRow4 faceC3 etaC (-60) (-40) (-20) (0) dC3_83 dC3_84 dC3_85 dC3_86 faceC3.wn
    = true := by
  bool_cert

/-- The cells of row 84 of face 3 pass. -/
theorem rowC3_84 : cellsRow4 faceC3 etaC (-40) (-20) (0) (20) dC3_84 dC3_85 dC3_86 dC3_87 faceC3.wn
    = true := by
  bool_cert

/-- The cells of row 85 of face 3 pass. -/
theorem rowC3_85 : cellsRow4 faceC3 etaC (-20) (0) (20) (40) dC3_85 dC3_86 dC3_87 dC3_88 faceC3.wn =
    true := by
  bool_cert

/-- The cells of row 86 of face 3 pass. -/
theorem rowC3_86 : cellsRow4 faceC3 etaC (0) (20) (40) (60) dC3_86 dC3_87 dC3_88 dC3_89 faceC3.wn =
    true := by
  bool_cert

/-- The cells of row 87 of face 3 pass. -/
theorem rowC3_87 : cellsRow4 faceC3 etaC (20) (40) (60) (80) dC3_87 dC3_88 dC3_89 dC3_90 faceC3.wn =
    true := by
  bool_cert

/-- The cells of row 88 of face 3 pass. -/
theorem rowC3_88 : cellsRow4 faceC3 etaC (40) (60) (80) (100) dC3_88 dC3_89 dC3_90 dC3_91 faceC3.wn
    = true := by
  bool_cert

/-- The cells of row 89 of face 3 pass. -/
theorem rowC3_89 : cellsRow4 faceC3 etaC (60) (80) (100) (120) dC3_89 dC3_90 dC3_91 dC3_92 faceC3.wn
    = true := by
  bool_cert

/-- The cells of row 90 of face 3 pass. -/
theorem rowC3_90 : cellsRow4 faceC3 etaC (80) (100) (120) (140) dC3_90 dC3_91 dC3_92 dC3_93
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 91 of face 3 pass. -/
theorem rowC3_91 : cellsRow4 faceC3 etaC (100) (120) (140) (160) dC3_91 dC3_92 dC3_93 dC3_94
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 92 of face 3 pass. -/
theorem rowC3_92 : cellsRow4 faceC3 etaC (120) (140) (160) (180) dC3_92 dC3_93 dC3_94 dC3_95
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 93 of face 3 pass. -/
theorem rowC3_93 : cellsRow4 faceC3 etaC (140) (160) (180) (200) dC3_93 dC3_94 dC3_95 dC3_96
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 94 of face 3 pass. -/
theorem rowC3_94 : cellsRow4 faceC3 etaC (160) (180) (200) (220) dC3_94 dC3_95 dC3_96 dC3_97
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 95 of face 3 pass. -/
theorem rowC3_95 : cellsRow4 faceC3 etaC (180) (200) (220) (240) dC3_95 dC3_96 dC3_97 dC3_98
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 96 of face 3 pass. -/
theorem rowC3_96 : cellsRow4 faceC3 etaC (200) (220) (240) (260) dC3_96 dC3_97 dC3_98 dC3_99
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 97 of face 3 pass. -/
theorem rowC3_97 : cellsRow4 faceC3 etaC (220) (240) (260) (280) dC3_97 dC3_98 dC3_99 dC3_100
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 98 of face 3 pass. -/
theorem rowC3_98 : cellsRow4 faceC3 etaC (240) (260) (280) (300) dC3_98 dC3_99 dC3_100 dC3_101
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 99 of face 3 pass. -/
theorem rowC3_99 : cellsRow4 faceC3 etaC (260) (280) (300) (320) dC3_99 dC3_100 dC3_101 dC3_102
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 100 of face 3 pass. -/
theorem rowC3_100 : cellsRow4 faceC3 etaC (280) (300) (320) (340) dC3_100 dC3_101 dC3_102 dC3_103
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 101 of face 3 pass. -/
theorem rowC3_101 : cellsRow4 faceC3 etaC (300) (320) (340) (360) dC3_101 dC3_102 dC3_103 dC3_104
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 102 of face 3 pass. -/
theorem rowC3_102 : cellsRow4 faceC3 etaC (320) (340) (360) (380) dC3_102 dC3_103 dC3_104 dC3_105
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 103 of face 3 pass. -/
theorem rowC3_103 : cellsRow4 faceC3 etaC (340) (360) (380) (400) dC3_103 dC3_104 dC3_105 dC3_106
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 104 of face 3 pass. -/
theorem rowC3_104 : cellsRow4 faceC3 etaC (360) (380) (400) (420) dC3_104 dC3_105 dC3_106 dC3_107
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 105 of face 3 pass. -/
theorem rowC3_105 : cellsRow4 faceC3 etaC (380) (400) (420) (440) dC3_105 dC3_106 dC3_107 dC3_108
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 106 of face 3 pass. -/
theorem rowC3_106 : cellsRow4 faceC3 etaC (400) (420) (440) (460) dC3_106 dC3_107 dC3_108 dC3_109
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 107 of face 3 pass. -/
theorem rowC3_107 : cellsRow4 faceC3 etaC (420) (440) (460) (480) dC3_107 dC3_108 dC3_109 dC3_110
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 108 of face 3 pass. -/
theorem rowC3_108 : cellsRow4 faceC3 etaC (440) (460) (480) (500) dC3_108 dC3_109 dC3_110 dC3_111
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 109 of face 3 pass. -/
theorem rowC3_109 : cellsRow4 faceC3 etaC (460) (480) (500) (520) dC3_109 dC3_110 dC3_111 dC3_112
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 110 of face 3 pass. -/
theorem rowC3_110 : cellsRow4 faceC3 etaC (480) (500) (520) (540) dC3_110 dC3_111 dC3_112 dC3_113
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 111 of face 3 pass. -/
theorem rowC3_111 : cellsRow4 faceC3 etaC (500) (520) (540) (560) dC3_111 dC3_112 dC3_113 dC3_114
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 112 of face 3 pass. -/
theorem rowC3_112 : cellsRow4 faceC3 etaC (520) (540) (560) (580) dC3_112 dC3_113 dC3_114 dC3_115
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 113 of face 3 pass. -/
theorem rowC3_113 : cellsRow4 faceC3 etaC (540) (560) (580) (600) dC3_113 dC3_114 dC3_115 dC3_116
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 114 of face 3 pass. -/
theorem rowC3_114 : cellsRow4 faceC3 etaC (560) (580) (600) (620) dC3_114 dC3_115 dC3_116 dC3_117
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 115 of face 3 pass. -/
theorem rowC3_115 : cellsRow4 faceC3 etaC (580) (600) (620) (640) dC3_115 dC3_116 dC3_117 dC3_118
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 116 of face 3 pass. -/
theorem rowC3_116 : cellsRow4 faceC3 etaC (600) (620) (640) (660) dC3_116 dC3_117 dC3_118 dC3_119
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 117 of face 3 pass. -/
theorem rowC3_117 : cellsRow4 faceC3 etaC (620) (640) (660) (680) dC3_117 dC3_118 dC3_119 dC3_120
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 118 of face 3 pass. -/
theorem rowC3_118 : cellsRow4 faceC3 etaC (640) (660) (680) (700) dC3_118 dC3_119 dC3_120 dC3_121
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 119 of face 3 pass. -/
theorem rowC3_119 : cellsRow4 faceC3 etaC (660) (680) (700) (720) dC3_119 dC3_120 dC3_121 dC3_122
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 120 of face 3 pass. -/
theorem rowC3_120 : cellsRow4 faceC3 etaC (680) (700) (720) (740) dC3_120 dC3_121 dC3_122 dC3_123
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 121 of face 3 pass. -/
theorem rowC3_121 : cellsRow4 faceC3 etaC (700) (720) (740) (760) dC3_121 dC3_122 dC3_123 dC3_124
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 122 of face 3 pass. -/
theorem rowC3_122 : cellsRow4 faceC3 etaC (720) (740) (760) (780) dC3_122 dC3_123 dC3_124 dC3_125
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 123 of face 3 pass. -/
theorem rowC3_123 : cellsRow4 faceC3 etaC (740) (760) (780) (800) dC3_123 dC3_124 dC3_125 dC3_126
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 124 of face 3 pass. -/
theorem rowC3_124 : cellsRow4 faceC3 etaC (760) (780) (800) (820) dC3_124 dC3_125 dC3_126 dC3_127
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 125 of face 3 pass. -/
theorem rowC3_125 : cellsRow4 faceC3 etaC (780) (800) (820) (840) dC3_125 dC3_126 dC3_127 dC3_128
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 126 of face 3 pass. -/
theorem rowC3_126 : cellsRow4 faceC3 etaC (800) (820) (840) (860) dC3_126 dC3_127 dC3_128 dC3_129
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 127 of face 3 pass. -/
theorem rowC3_127 : cellsRow4 faceC3 etaC (820) (840) (860) (880) dC3_127 dC3_128 dC3_129 dC3_130
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 128 of face 3 pass. -/
theorem rowC3_128 : cellsRow4 faceC3 etaC (840) (860) (880) (900) dC3_128 dC3_129 dC3_130 dC3_131
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 129 of face 3 pass. -/
theorem rowC3_129 : cellsRow4 faceC3 etaC (860) (880) (900) (920) dC3_129 dC3_130 dC3_131 dC3_132
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 130 of face 3 pass. -/
theorem rowC3_130 : cellsRow4 faceC3 etaC (880) (900) (920) (940) dC3_130 dC3_131 dC3_132 dC3_133
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 131 of face 3 pass. -/
theorem rowC3_131 : cellsRow4 faceC3 etaC (900) (920) (940) (960) dC3_131 dC3_132 dC3_133 dC3_134
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 132 of face 3 pass. -/
theorem rowC3_132 : cellsRow4 faceC3 etaC (920) (940) (960) (980) dC3_132 dC3_133 dC3_134 dC3_135
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 133 of face 3 pass. -/
theorem rowC3_133 : cellsRow4 faceC3 etaC (940) (960) (980) (1000) dC3_133 dC3_134 dC3_135 dC3_136
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 134 of face 3 pass. -/
theorem rowC3_134 : cellsRow4 faceC3 etaC (960) (980) (1000) (1020) dC3_134 dC3_135 dC3_136 dC3_137
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 135 of face 3 pass. -/
theorem rowC3_135 : cellsRow4 faceC3 etaC (980) (1000) (1020) (1040) dC3_135 dC3_136 dC3_137 dC3_138
    faceC3.wn = true := by
  bool_cert

/-- The cells of row 136 of face 3 pass. -/
theorem rowC3_136 : cellsRow4 faceC3 etaC (1000) (1020) (1040) (1060) dC3_136 dC3_137 dC3_138
    dC3_139 faceC3.wn = true := by
  bool_cert

/-- The cells of row 137 of face 3 pass. -/
theorem rowC3_137 : cellsRow4 faceC3 etaC (1020) (1040) (1060) (1080) dC3_137 dC3_138 dC3_139
    dC3_140 faceC3.wn = true := by
  bool_cert

/-- The cells of row 138 of face 3 pass. -/
theorem rowC3_138 : cellsRow4 faceC3 etaC (1040) (1060) (1080) (1100) dC3_138 dC3_139 dC3_140
    dC3_141 faceC3.wn = true := by
  bool_cert

/-- The cells of row 139 of face 3 pass. -/
theorem rowC3_139 : cellsRow4 faceC3 etaC (1060) (1080) (1100) (1120) dC3_139 dC3_140 dC3_141
    dC3_142 faceC3.wn = true := by
  bool_cert

/-- The cells of row 140 of face 3 pass. -/
theorem rowC3_140 : cellsRow4 faceC3 etaC (1080) (1100) (1120) (1140) dC3_140 dC3_141 dC3_142
    dC3_143 faceC3.wn = true := by
  bool_cert

/-- The cells of row 141 of face 3 pass. -/
theorem rowC3_141 : cellsRow4 faceC3 etaC (1100) (1120) (1140) (1160) dC3_141 dC3_142 dC3_143
    dC3_144 faceC3.wn = true := by
  bool_cert

/-- The cells of row 142 of face 3 pass. -/
theorem rowC3_142 : cellsRow4 faceC3 etaC (1120) (1140) (1160) (1180) dC3_142 dC3_143 dC3_144
    dC3_145 faceC3.wn = true := by
  bool_cert

/-- The cells of row 143 of face 3 pass. -/
theorem rowC3_143 : cellsRow4 faceC3 etaC (1140) (1160) (1180) (1200) dC3_143 dC3_144 dC3_145
    dC3_146 faceC3.wn = true := by
  bool_cert

/-- The cells of row 144 of face 3 pass. -/
theorem rowC3_144 : cellsRow4 faceC3 etaC (1160) (1180) (1200) (1220) dC3_144 dC3_145 dC3_146
    dC3_147 faceC3.wn = true := by
  bool_cert

/-- The cells of row 145 of face 3 pass. -/
theorem rowC3_145 : cellsRow4 faceC3 etaC (1180) (1200) (1220) (1240) dC3_145 dC3_146 dC3_147
    dC3_148 faceC3.wn = true := by
  bool_cert

/-- The cells of row 146 of face 3 pass. -/
theorem rowC3_146 : cellsRow4 faceC3 etaC (1200) (1220) (1240) (1260) dC3_146 dC3_147 dC3_148
    dC3_149 faceC3.wn = true := by
  bool_cert

/-- The cells of row 147 of face 3 pass. -/
theorem rowC3_147 : cellsRow4 faceC3 etaC (1220) (1240) (1260) (1280) dC3_147 dC3_148 dC3_149
    dC3_150 faceC3.wn = true := by
  bool_cert

/-- The cells of row 148 of face 3 pass. -/
theorem rowC3_148 : cellsRow4 faceC3 etaC (1240) (1260) (1280) (1300) dC3_148 dC3_149 dC3_150
    dC3_151 faceC3.wn = true := by
  bool_cert

/-- The cells of row 149 of face 3 pass. -/
theorem rowC3_149 : cellsRow4 faceC3 etaC (1260) (1280) (1300) (1320) dC3_149 dC3_150 dC3_151
    dC3_152 faceC3.wn = true := by
  bool_cert

/-- The cells of row 150 of face 3 pass. -/
theorem rowC3_150 : cellsRow4 faceC3 etaC (1280) (1300) (1320) (1340) dC3_150 dC3_151 dC3_152
    dC3_153 faceC3.wn = true := by
  bool_cert

/-- The cells of row 151 of face 3 pass. -/
theorem rowC3_151 : cellsRow4 faceC3 etaC (1300) (1320) (1340) (1360) dC3_151 dC3_152 dC3_153
    dC3_154 faceC3.wn = true := by
  bool_cert

/-- The cells of row 152 of face 3 pass. -/
theorem rowC3_152 : cellsRow4 faceC3 etaC (1320) (1340) (1360) (1380) dC3_152 dC3_153 dC3_154
    dC3_155 faceC3.wn = true := by
  bool_cert

/-- The cells of row 153 of face 3 pass. -/
theorem rowC3_153 : cellsRow4 faceC3 etaC (1340) (1360) (1380) (1400) dC3_153 dC3_154 dC3_155
    dC3_156 faceC3.wn = true := by
  bool_cert

/-- The cells of row 154 of face 3 pass. -/
theorem rowC3_154 : cellsRow4 faceC3 etaC (1360) (1380) (1400) (1420) dC3_154 dC3_155 dC3_156
    dC3_157 faceC3.wn = true := by
  bool_cert

/-- The cells of row 155 of face 3 pass. -/
theorem rowC3_155 : cellsRow4 faceC3 etaC (1380) (1400) (1420) (1440) dC3_155 dC3_156 dC3_157
    dC3_158 faceC3.wn = true := by
  bool_cert

/-- The cells of row 156 of face 3 pass. -/
theorem rowC3_156 : cellsRow4 faceC3 etaC (1400) (1420) (1440) (1460) dC3_156 dC3_157 dC3_158
    dC3_159 faceC3.wn = true := by
  bool_cert

/-- The cells of row 157 of face 3 pass. -/
theorem rowC3_157 : cellsRow4 faceC3 etaC (1420) (1440) (1460) (1480) dC3_157 dC3_158 dC3_159
    dC3_160 faceC3.wn = true := by
  bool_cert

/-- The cells of row 158 of face 3 pass. -/
theorem rowC3_158 : cellsRow4 faceC3 etaC (1440) (1460) (1480) (1500) dC3_158 dC3_159 dC3_160
    dC3_161 faceC3.wn = true := by
  bool_cert

/-- The cells of row 159 of face 3 pass. -/
theorem rowC3_159 : cellsRow4 faceC3 etaC (1460) (1480) (1500) (1520) dC3_159 dC3_160 dC3_161
    dC3_162 faceC3.wn = true := by
  bool_cert

/-- The cells of row 160 of face 3 pass. -/
theorem rowC3_160 : cellsRow4 faceC3 etaC (1480) (1500) (1520) (1540) dC3_160 dC3_161 dC3_162
    dC3_163 faceC3.wn = true := by
  bool_cert

/-- The cells of row 161 of face 3 pass. -/
theorem rowC3_161 : cellsRow4 faceC3 etaC (1500) (1520) (1540) (1560) dC3_161 dC3_162 dC3_163
    dC3_164 faceC3.wn = true := by
  bool_cert

/-- The cells of row 162 of face 3 pass. -/
theorem rowC3_162 : cellsRow4 faceC3 etaC (1520) (1540) (1560) (1580) dC3_162 dC3_163 dC3_164
    dC3_165 faceC3.wn = true := by
  bool_cert

/-- The cells of row 163 of face 3 pass. -/
theorem rowC3_163 : cellsRow4 faceC3 etaC (1540) (1560) (1580) (1600) dC3_163 dC3_164 dC3_165
    dC3_166 faceC3.wn = true := by
  bool_cert

/-- The cells of row 164 of face 3 pass. -/
theorem rowC3_164 : cellsRow4 faceC3 etaC (1560) (1580) (1600) (1620) dC3_164 dC3_165 dC3_166
    dC3_167 faceC3.wn = true := by
  bool_cert

/-- The cells of row 165 of face 3 pass. -/
theorem rowC3_165 : cellsRow4 faceC3 etaC (1580) (1600) (1620) (1640) dC3_165 dC3_166 dC3_167
    dC3_168 faceC3.wn = true := by
  bool_cert

/-- The cells of row 166 of face 3 pass. -/
theorem rowC3_166 : cellsRow4 faceC3 etaC (1600) (1620) (1640) (1660) dC3_166 dC3_167 dC3_168
    dC3_169 faceC3.wn = true := by
  bool_cert

/-- The cells of row 167 of face 3 pass. -/
theorem rowC3_167 : cellsRow4 faceC3 etaC (1620) (1640) (1660) (1680) dC3_167 dC3_168 dC3_169
    dC3_170 faceC3.wn = true := by
  bool_cert

/-- The cells of row 168 of face 3 pass. -/
theorem rowC3_168 : cellsRow4 faceC3 etaC (1640) (1660) (1680) (1700) dC3_168 dC3_169 dC3_170
    dC3_171 faceC3.wn = true := by
  bool_cert

/-- The cells of row 169 of face 3 pass. -/
theorem rowC3_169 : cellsRow4 faceC3 etaC (1660) (1680) (1700) (1720) dC3_169 dC3_170 dC3_171
    dC3_172 faceC3.wn = true := by
  bool_cert

/-- **All cells of face 3 pass** (`η = 3540573·2⁻⁴⁰`). -/
theorem cellsC3 : cellsAll4 etaC faceC3 gridC3 dataC3 = true :=
cellsAll4_cons rowC3_0 <| cellsAll4_cons rowC3_1 <| cellsAll4_cons rowC3_2 <| cellsAll4_cons rowC3_3
    <| cellsAll4_cons rowC3_4 <| cellsAll4_cons rowC3_5 <| cellsAll4_cons rowC3_6 <| cellsAll4_cons
    rowC3_7 <| cellsAll4_cons rowC3_8 <| cellsAll4_cons rowC3_9 <| cellsAll4_cons rowC3_10 <|
    cellsAll4_cons rowC3_11 <| cellsAll4_cons rowC3_12 <| cellsAll4_cons rowC3_13 <| cellsAll4_cons
    rowC3_14 <| cellsAll4_cons rowC3_15 <| cellsAll4_cons rowC3_16 <| cellsAll4_cons rowC3_17 <|
    cellsAll4_cons rowC3_18 <| cellsAll4_cons rowC3_19 <| cellsAll4_cons rowC3_20 <| cellsAll4_cons
    rowC3_21 <| cellsAll4_cons rowC3_22 <| cellsAll4_cons rowC3_23 <| cellsAll4_cons rowC3_24 <|
    cellsAll4_cons rowC3_25 <| cellsAll4_cons rowC3_26 <| cellsAll4_cons rowC3_27 <| cellsAll4_cons
    rowC3_28 <| cellsAll4_cons rowC3_29 <| cellsAll4_cons rowC3_30 <| cellsAll4_cons rowC3_31 <|
    cellsAll4_cons rowC3_32 <| cellsAll4_cons rowC3_33 <| cellsAll4_cons rowC3_34 <| cellsAll4_cons
    rowC3_35 <| cellsAll4_cons rowC3_36 <| cellsAll4_cons rowC3_37 <| cellsAll4_cons rowC3_38 <|
    cellsAll4_cons rowC3_39 <| cellsAll4_cons rowC3_40 <| cellsAll4_cons rowC3_41 <| cellsAll4_cons
    rowC3_42 <| cellsAll4_cons rowC3_43 <| cellsAll4_cons rowC3_44 <| cellsAll4_cons rowC3_45 <|
    cellsAll4_cons rowC3_46 <| cellsAll4_cons rowC3_47 <| cellsAll4_cons rowC3_48 <| cellsAll4_cons
    rowC3_49 <| cellsAll4_cons rowC3_50 <| cellsAll4_cons rowC3_51 <| cellsAll4_cons rowC3_52 <|
    cellsAll4_cons rowC3_53 <| cellsAll4_cons rowC3_54 <| cellsAll4_cons rowC3_55 <| cellsAll4_cons
    rowC3_56 <| cellsAll4_cons rowC3_57 <| cellsAll4_cons rowC3_58 <| cellsAll4_cons rowC3_59 <|
    cellsAll4_cons rowC3_60 <| cellsAll4_cons rowC3_61 <| cellsAll4_cons rowC3_62 <| cellsAll4_cons
    rowC3_63 <| cellsAll4_cons rowC3_64 <| cellsAll4_cons rowC3_65 <| cellsAll4_cons rowC3_66 <|
    cellsAll4_cons rowC3_67 <| cellsAll4_cons rowC3_68 <| cellsAll4_cons rowC3_69 <| cellsAll4_cons
    rowC3_70 <| cellsAll4_cons rowC3_71 <| cellsAll4_cons rowC3_72 <| cellsAll4_cons rowC3_73 <|
    cellsAll4_cons rowC3_74 <| cellsAll4_cons rowC3_75 <| cellsAll4_cons rowC3_76 <| cellsAll4_cons
    rowC3_77 <| cellsAll4_cons rowC3_78 <| cellsAll4_cons rowC3_79 <| cellsAll4_cons rowC3_80 <|
    cellsAll4_cons rowC3_81 <| cellsAll4_cons rowC3_82 <| cellsAll4_cons rowC3_83 <| cellsAll4_cons
    rowC3_84 <| cellsAll4_cons rowC3_85 <| cellsAll4_cons rowC3_86 <| cellsAll4_cons rowC3_87 <|
    cellsAll4_cons rowC3_88 <| cellsAll4_cons rowC3_89 <| cellsAll4_cons rowC3_90 <| cellsAll4_cons
    rowC3_91 <| cellsAll4_cons rowC3_92 <| cellsAll4_cons rowC3_93 <| cellsAll4_cons rowC3_94 <|
    cellsAll4_cons rowC3_95 <| cellsAll4_cons rowC3_96 <| cellsAll4_cons rowC3_97 <| cellsAll4_cons
    rowC3_98 <| cellsAll4_cons rowC3_99 <| cellsAll4_cons rowC3_100 <| cellsAll4_cons rowC3_101 <|
    cellsAll4_cons rowC3_102 <| cellsAll4_cons rowC3_103 <| cellsAll4_cons rowC3_104 <|
    cellsAll4_cons rowC3_105 <| cellsAll4_cons rowC3_106 <| cellsAll4_cons rowC3_107 <|
    cellsAll4_cons rowC3_108 <| cellsAll4_cons rowC3_109 <| cellsAll4_cons rowC3_110 <|
    cellsAll4_cons rowC3_111 <| cellsAll4_cons rowC3_112 <| cellsAll4_cons rowC3_113 <|
    cellsAll4_cons rowC3_114 <| cellsAll4_cons rowC3_115 <| cellsAll4_cons rowC3_116 <|
    cellsAll4_cons rowC3_117 <| cellsAll4_cons rowC3_118 <| cellsAll4_cons rowC3_119 <|
    cellsAll4_cons rowC3_120 <| cellsAll4_cons rowC3_121 <| cellsAll4_cons rowC3_122 <|
    cellsAll4_cons rowC3_123 <| cellsAll4_cons rowC3_124 <| cellsAll4_cons rowC3_125 <|
    cellsAll4_cons rowC3_126 <| cellsAll4_cons rowC3_127 <| cellsAll4_cons rowC3_128 <|
    cellsAll4_cons rowC3_129 <| cellsAll4_cons rowC3_130 <| cellsAll4_cons rowC3_131 <|
    cellsAll4_cons rowC3_132 <| cellsAll4_cons rowC3_133 <| cellsAll4_cons rowC3_134 <|
    cellsAll4_cons rowC3_135 <| cellsAll4_cons rowC3_136 <| cellsAll4_cons rowC3_137 <|
    cellsAll4_cons rowC3_138 <| cellsAll4_cons rowC3_139 <| cellsAll4_cons rowC3_140 <|
    cellsAll4_cons rowC3_141 <| cellsAll4_cons rowC3_142 <| cellsAll4_cons rowC3_143 <|
    cellsAll4_cons rowC3_144 <| cellsAll4_cons rowC3_145 <| cellsAll4_cons rowC3_146 <|
    cellsAll4_cons rowC3_147 <| cellsAll4_cons rowC3_148 <| cellsAll4_cons rowC3_149 <|
    cellsAll4_cons rowC3_150 <| cellsAll4_cons rowC3_151 <| cellsAll4_cons rowC3_152 <|
    cellsAll4_cons rowC3_153 <| cellsAll4_cons rowC3_154 <| cellsAll4_cons rowC3_155 <|
    cellsAll4_cons rowC3_156 <| cellsAll4_cons rowC3_157 <| cellsAll4_cons rowC3_158 <|
    cellsAll4_cons rowC3_159 <| cellsAll4_cons rowC3_160 <| cellsAll4_cons rowC3_161 <|
    cellsAll4_cons rowC3_162 <| cellsAll4_cons rowC3_163 <| cellsAll4_cons rowC3_164 <|
    cellsAll4_cons rowC3_165 <| cellsAll4_cons rowC3_166 <| cellsAll4_cons rowC3_167 <|
    cellsAll4_cons rowC3_168 <| cellsAll4_cons rowC3_169 <| cellsAll4_end

/-- Face 3 carries the proved `hel` constants. -/
theorem face4OK_3 : Face4OK faceC3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [faceC3] <;> norm_num

/-- The line facts of face 3. -/
theorem linesC_3 : List.Forall₂ (fun m L => List.Forall₂ (LVal filsC faceC3 m) faceC3.wn L ∧
    QuadP (LW filsC faceC3 m) faceC3.wn L) gridC3 dataC3 :=
.cons (line_facts face4OK_3 lC3_0).1 <| .cons (line_facts face4OK_3 lC3_1).1 <| .cons (line_facts
    face4OK_3 lC3_2).1 <| .cons (line_facts face4OK_3 lC3_3).1 <| .cons (line_facts face4OK_3
    lC3_4).1 <| .cons (line_facts face4OK_3 lC3_5).1 <| .cons (line_facts face4OK_3 lC3_6).1 <|
    .cons (line_facts face4OK_3 lC3_7).1 <| .cons (line_facts face4OK_3 lC3_8).1 <| .cons
    (line_facts face4OK_3 lC3_9).1 <| .cons (line_facts face4OK_3 lC3_10).1 <| .cons (line_facts
    face4OK_3 lC3_11).1 <| .cons (line_facts face4OK_3 lC3_12).1 <| .cons (line_facts face4OK_3
    lC3_13).1 <| .cons (line_facts face4OK_3 lC3_14).1 <| .cons (line_facts face4OK_3 lC3_15).1 <|
    .cons (line_facts face4OK_3 lC3_16).1 <| .cons (line_facts face4OK_3 lC3_17).1 <| .cons
    (line_facts face4OK_3 lC3_18).1 <| .cons (line_facts face4OK_3 lC3_19).1 <| .cons (line_facts
    face4OK_3 lC3_20).1 <| .cons (line_facts face4OK_3 lC3_21).1 <| .cons (line_facts face4OK_3
    lC3_22).1 <| .cons (line_facts face4OK_3 lC3_23).1 <| .cons (line_facts face4OK_3 lC3_24).1 <|
    .cons (line_facts face4OK_3 lC3_25).1 <| .cons (line_facts face4OK_3 lC3_26).1 <| .cons
    (line_facts face4OK_3 lC3_27).1 <| .cons (line_facts face4OK_3 lC3_28).1 <| .cons (line_facts
    face4OK_3 lC3_29).1 <| .cons (line_facts face4OK_3 lC3_30).1 <| .cons (line_facts face4OK_3
    lC3_31).1 <| .cons (line_facts face4OK_3 lC3_32).1 <| .cons (line_facts face4OK_3 lC3_33).1 <|
    .cons (line_facts face4OK_3 lC3_34).1 <| .cons (line_facts face4OK_3 lC3_35).1 <| .cons
    (line_facts face4OK_3 lC3_36).1 <| .cons (line_facts face4OK_3 lC3_37).1 <| .cons (line_facts
    face4OK_3 lC3_38).1 <| .cons (line_facts face4OK_3 lC3_39).1 <| .cons (line_facts face4OK_3
    lC3_40).1 <| .cons (line_facts face4OK_3 lC3_41).1 <| .cons (line_facts face4OK_3 lC3_42).1 <|
    .cons (line_facts face4OK_3 lC3_43).1 <| .cons (line_facts face4OK_3 lC3_44).1 <| .cons
    (line_facts face4OK_3 lC3_45).1 <| .cons (line_facts face4OK_3 lC3_46).1 <| .cons (line_facts
    face4OK_3 lC3_47).1 <| .cons (line_facts face4OK_3 lC3_48).1 <| .cons (line_facts face4OK_3
    lC3_49).1 <| .cons (line_facts face4OK_3 lC3_50).1 <| .cons (line_facts face4OK_3 lC3_51).1 <|
    .cons (line_facts face4OK_3 lC3_52).1 <| .cons (line_facts face4OK_3 lC3_53).1 <| .cons
    (line_facts face4OK_3 lC3_54).1 <| .cons (line_facts face4OK_3 lC3_55).1 <| .cons (line_facts
    face4OK_3 lC3_56).1 <| .cons (line_facts face4OK_3 lC3_57).1 <| .cons (line_facts face4OK_3
    lC3_58).1 <| .cons (line_facts face4OK_3 lC3_59).1 <| .cons (line_facts face4OK_3 lC3_60).1 <|
    .cons (line_facts face4OK_3 lC3_61).1 <| .cons (line_facts face4OK_3 lC3_62).1 <| .cons
    (line_facts face4OK_3 lC3_63).1 <| .cons (line_facts face4OK_3 lC3_64).1 <| .cons (line_facts
    face4OK_3 lC3_65).1 <| .cons (line_facts face4OK_3 lC3_66).1 <| .cons (line_facts face4OK_3
    lC3_67).1 <| .cons (line_facts face4OK_3 lC3_68).1 <| .cons (line_facts face4OK_3 lC3_69).1 <|
    .cons (line_facts face4OK_3 lC3_70).1 <| .cons (line_facts face4OK_3 lC3_71).1 <| .cons
    (line_facts face4OK_3 lC3_72).1 <| .cons (line_facts face4OK_3 lC3_73).1 <| .cons (line_facts
    face4OK_3 lC3_74).1 <| .cons (line_facts face4OK_3 lC3_75).1 <| .cons (line_facts face4OK_3
    lC3_76).1 <| .cons (line_facts face4OK_3 lC3_77).1 <| .cons (line_facts face4OK_3 lC3_78).1 <|
    .cons (line_facts face4OK_3 lC3_79).1 <| .cons (line_facts face4OK_3 lC3_80).1 <| .cons
    (line_facts face4OK_3 lC3_81).1 <| .cons (line_facts face4OK_3 lC3_82).1 <| .cons (line_facts
    face4OK_3 lC3_83).1 <| .cons (line_facts face4OK_3 lC3_84).1 <| .cons (line_facts face4OK_3
    lC3_85).1 <| .cons (line_facts face4OK_3 lC3_86).1 <| .cons (line_facts face4OK_3 lC3_87).1 <|
    .cons (line_facts face4OK_3 lC3_88).1 <| .cons (line_facts face4OK_3 lC3_89).1 <| .cons
    (line_facts face4OK_3 lC3_90).1 <| .cons (line_facts face4OK_3 lC3_91).1 <| .cons (line_facts
    face4OK_3 lC3_92).1 <| .cons (line_facts face4OK_3 lC3_93).1 <| .cons (line_facts face4OK_3
    lC3_94).1 <| .cons (line_facts face4OK_3 lC3_95).1 <| .cons (line_facts face4OK_3 lC3_96).1 <|
    .cons (line_facts face4OK_3 lC3_97).1 <| .cons (line_facts face4OK_3 lC3_98).1 <| .cons
    (line_facts face4OK_3 lC3_99).1 <| .cons (line_facts face4OK_3 lC3_100).1 <| .cons (line_facts
    face4OK_3 lC3_101).1 <| .cons (line_facts face4OK_3 lC3_102).1 <| .cons (line_facts face4OK_3
    lC3_103).1 <| .cons (line_facts face4OK_3 lC3_104).1 <| .cons (line_facts face4OK_3 lC3_105).1
    <| .cons (line_facts face4OK_3 lC3_106).1 <| .cons (line_facts face4OK_3 lC3_107).1 <| .cons
    (line_facts face4OK_3 lC3_108).1 <| .cons (line_facts face4OK_3 lC3_109).1 <| .cons (line_facts
    face4OK_3 lC3_110).1 <| .cons (line_facts face4OK_3 lC3_111).1 <| .cons (line_facts face4OK_3
    lC3_112).1 <| .cons (line_facts face4OK_3 lC3_113).1 <| .cons (line_facts face4OK_3 lC3_114).1
    <| .cons (line_facts face4OK_3 lC3_115).1 <| .cons (line_facts face4OK_3 lC3_116).1 <| .cons
    (line_facts face4OK_3 lC3_117).1 <| .cons (line_facts face4OK_3 lC3_118).1 <| .cons (line_facts
    face4OK_3 lC3_119).1 <| .cons (line_facts face4OK_3 lC3_120).1 <| .cons (line_facts face4OK_3
    lC3_121).1 <| .cons (line_facts face4OK_3 lC3_122).1 <| .cons (line_facts face4OK_3 lC3_123).1
    <| .cons (line_facts face4OK_3 lC3_124).1 <| .cons (line_facts face4OK_3 lC3_125).1 <| .cons
    (line_facts face4OK_3 lC3_126).1 <| .cons (line_facts face4OK_3 lC3_127).1 <| .cons (line_facts
    face4OK_3 lC3_128).1 <| .cons (line_facts face4OK_3 lC3_129).1 <| .cons (line_facts face4OK_3
    lC3_130).1 <| .cons (line_facts face4OK_3 lC3_131).1 <| .cons (line_facts face4OK_3 lC3_132).1
    <| .cons (line_facts face4OK_3 lC3_133).1 <| .cons (line_facts face4OK_3 lC3_134).1 <| .cons
    (line_facts face4OK_3 lC3_135).1 <| .cons (line_facts face4OK_3 lC3_136).1 <| .cons (line_facts
    face4OK_3 lC3_137).1 <| .cons (line_facts face4OK_3 lC3_138).1 <| .cons (line_facts face4OK_3
    lC3_139).1 <| .cons (line_facts face4OK_3 lC3_140).1 <| .cons (line_facts face4OK_3 lC3_141).1
    <| .cons (line_facts face4OK_3 lC3_142).1 <| .cons (line_facts face4OK_3 lC3_143).1 <| .cons
    (line_facts face4OK_3 lC3_144).1 <| .cons (line_facts face4OK_3 lC3_145).1 <| .cons (line_facts
    face4OK_3 lC3_146).1 <| .cons (line_facts face4OK_3 lC3_147).1 <| .cons (line_facts face4OK_3
    lC3_148).1 <| .cons (line_facts face4OK_3 lC3_149).1 <| .cons (line_facts face4OK_3 lC3_150).1
    <| .cons (line_facts face4OK_3 lC3_151).1 <| .cons (line_facts face4OK_3 lC3_152).1 <| .cons
    (line_facts face4OK_3 lC3_153).1 <| .cons (line_facts face4OK_3 lC3_154).1 <| .cons (line_facts
    face4OK_3 lC3_155).1 <| .cons (line_facts face4OK_3 lC3_156).1 <| .cons (line_facts face4OK_3
    lC3_157).1 <| .cons (line_facts face4OK_3 lC3_158).1 <| .cons (line_facts face4OK_3 lC3_159).1
    <| .cons (line_facts face4OK_3 lC3_160).1 <| .cons (line_facts face4OK_3 lC3_161).1 <| .cons
    (line_facts face4OK_3 lC3_162).1 <| .cons (line_facts face4OK_3 lC3_163).1 <| .cons (line_facts
    face4OK_3 lC3_164).1 <| .cons (line_facts face4OK_3 lC3_165).1 <| .cons (line_facts face4OK_3
    lC3_166).1 <| .cons (line_facts face4OK_3 lC3_167).1 <| .cons (line_facts face4OK_3 lC3_168).1
    <| .cons (line_facts face4OK_3 lC3_169).1 <| .cons (line_facts face4OK_3 lC3_170).1 <| .cons
    (line_facts face4OK_3 lC3_171).1 <| .cons (line_facts face4OK_3 lC3_172).1 <| .nil

/-- The strip facts of face 3. -/
theorem rowsC_3 : RowsT filsC faceC3 gridC3 dataC3 :=
rowsT_cons (line_facts face4OK_3 lC3_1).2 <| rowsT_cons (line_facts face4OK_3 lC3_2).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_3).2 <| rowsT_cons (line_facts face4OK_3 lC3_4).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_5).2 <| rowsT_cons (line_facts face4OK_3 lC3_6).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_7).2 <| rowsT_cons (line_facts face4OK_3 lC3_8).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_9).2 <| rowsT_cons (line_facts face4OK_3 lC3_10).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_11).2 <| rowsT_cons (line_facts face4OK_3 lC3_12).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_13).2 <| rowsT_cons (line_facts face4OK_3 lC3_14).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_15).2 <| rowsT_cons (line_facts face4OK_3 lC3_16).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_17).2 <| rowsT_cons (line_facts face4OK_3 lC3_18).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_19).2 <| rowsT_cons (line_facts face4OK_3 lC3_20).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_21).2 <| rowsT_cons (line_facts face4OK_3 lC3_22).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_23).2 <| rowsT_cons (line_facts face4OK_3 lC3_24).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_25).2 <| rowsT_cons (line_facts face4OK_3 lC3_26).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_27).2 <| rowsT_cons (line_facts face4OK_3 lC3_28).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_29).2 <| rowsT_cons (line_facts face4OK_3 lC3_30).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_31).2 <| rowsT_cons (line_facts face4OK_3 lC3_32).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_33).2 <| rowsT_cons (line_facts face4OK_3 lC3_34).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_35).2 <| rowsT_cons (line_facts face4OK_3 lC3_36).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_37).2 <| rowsT_cons (line_facts face4OK_3 lC3_38).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_39).2 <| rowsT_cons (line_facts face4OK_3 lC3_40).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_41).2 <| rowsT_cons (line_facts face4OK_3 lC3_42).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_43).2 <| rowsT_cons (line_facts face4OK_3 lC3_44).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_45).2 <| rowsT_cons (line_facts face4OK_3 lC3_46).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_47).2 <| rowsT_cons (line_facts face4OK_3 lC3_48).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_49).2 <| rowsT_cons (line_facts face4OK_3 lC3_50).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_51).2 <| rowsT_cons (line_facts face4OK_3 lC3_52).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_53).2 <| rowsT_cons (line_facts face4OK_3 lC3_54).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_55).2 <| rowsT_cons (line_facts face4OK_3 lC3_56).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_57).2 <| rowsT_cons (line_facts face4OK_3 lC3_58).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_59).2 <| rowsT_cons (line_facts face4OK_3 lC3_60).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_61).2 <| rowsT_cons (line_facts face4OK_3 lC3_62).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_63).2 <| rowsT_cons (line_facts face4OK_3 lC3_64).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_65).2 <| rowsT_cons (line_facts face4OK_3 lC3_66).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_67).2 <| rowsT_cons (line_facts face4OK_3 lC3_68).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_69).2 <| rowsT_cons (line_facts face4OK_3 lC3_70).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_71).2 <| rowsT_cons (line_facts face4OK_3 lC3_72).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_73).2 <| rowsT_cons (line_facts face4OK_3 lC3_74).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_75).2 <| rowsT_cons (line_facts face4OK_3 lC3_76).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_77).2 <| rowsT_cons (line_facts face4OK_3 lC3_78).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_79).2 <| rowsT_cons (line_facts face4OK_3 lC3_80).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_81).2 <| rowsT_cons (line_facts face4OK_3 lC3_82).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_83).2 <| rowsT_cons (line_facts face4OK_3 lC3_84).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_85).2 <| rowsT_cons (line_facts face4OK_3 lC3_86).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_87).2 <| rowsT_cons (line_facts face4OK_3 lC3_88).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_89).2 <| rowsT_cons (line_facts face4OK_3 lC3_90).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_91).2 <| rowsT_cons (line_facts face4OK_3 lC3_92).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_93).2 <| rowsT_cons (line_facts face4OK_3 lC3_94).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_95).2 <| rowsT_cons (line_facts face4OK_3 lC3_96).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_97).2 <| rowsT_cons (line_facts face4OK_3 lC3_98).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_99).2 <| rowsT_cons (line_facts face4OK_3 lC3_100).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_101).2 <| rowsT_cons (line_facts face4OK_3 lC3_102).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_103).2 <| rowsT_cons (line_facts face4OK_3 lC3_104).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_105).2 <| rowsT_cons (line_facts face4OK_3 lC3_106).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_107).2 <| rowsT_cons (line_facts face4OK_3 lC3_108).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_109).2 <| rowsT_cons (line_facts face4OK_3 lC3_110).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_111).2 <| rowsT_cons (line_facts face4OK_3 lC3_112).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_113).2 <| rowsT_cons (line_facts face4OK_3 lC3_114).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_115).2 <| rowsT_cons (line_facts face4OK_3 lC3_116).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_117).2 <| rowsT_cons (line_facts face4OK_3 lC3_118).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_119).2 <| rowsT_cons (line_facts face4OK_3 lC3_120).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_121).2 <| rowsT_cons (line_facts face4OK_3 lC3_122).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_123).2 <| rowsT_cons (line_facts face4OK_3 lC3_124).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_125).2 <| rowsT_cons (line_facts face4OK_3 lC3_126).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_127).2 <| rowsT_cons (line_facts face4OK_3 lC3_128).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_129).2 <| rowsT_cons (line_facts face4OK_3 lC3_130).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_131).2 <| rowsT_cons (line_facts face4OK_3 lC3_132).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_133).2 <| rowsT_cons (line_facts face4OK_3 lC3_134).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_135).2 <| rowsT_cons (line_facts face4OK_3 lC3_136).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_137).2 <| rowsT_cons (line_facts face4OK_3 lC3_138).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_139).2 <| rowsT_cons (line_facts face4OK_3 lC3_140).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_141).2 <| rowsT_cons (line_facts face4OK_3 lC3_142).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_143).2 <| rowsT_cons (line_facts face4OK_3 lC3_144).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_145).2 <| rowsT_cons (line_facts face4OK_3 lC3_146).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_147).2 <| rowsT_cons (line_facts face4OK_3 lC3_148).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_149).2 <| rowsT_cons (line_facts face4OK_3 lC3_150).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_151).2 <| rowsT_cons (line_facts face4OK_3 lC3_152).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_153).2 <| rowsT_cons (line_facts face4OK_3 lC3_154).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_155).2 <| rowsT_cons (line_facts face4OK_3 lC3_156).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_157).2 <| rowsT_cons (line_facts face4OK_3 lC3_158).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_159).2 <| rowsT_cons (line_facts face4OK_3 lC3_160).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_161).2 <| rowsT_cons (line_facts face4OK_3 lC3_162).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_163).2 <| rowsT_cons (line_facts face4OK_3 lC3_164).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_165).2 <| rowsT_cons (line_facts face4OK_3 lC3_166).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_167).2 <| rowsT_cons (line_facts face4OK_3 lC3_168).2 <| rowsT_cons
    (line_facts face4OK_3 lC3_169).2 <| rowsT_cons (line_facts face4OK_3 lC3_170).2 <| rowsT_end

set_option maxRecDepth 20000 in
/-- **The certified bound on face 3.** -/
theorem coverC_3 : RectGood filsC 3 etaC (((-1700 : ℤ) : ℝ) / 4096) (((1700 : ℤ) : ℝ) / 4096)
    (((4508 : ℤ) : ℝ) / ((5068 : ℕ) : ℝ)) (((5572 : ℤ) : ℝ) / ((5068 : ℕ) : ℝ)) := by
  have h := face_sound filsC faceC3 face4OK_3 etaC (by kernel_fact) gridC3 dataC3 linesC_3
    rowsC_3 cellsC3 (by kernel_fact)
  rw [show gridC3.length = 173 by kernel_fact, show faceC3.wn.length = 31 by kernel_fact] at h
  rwa [show gridC3.getD 1 0 = -1700 by kernel_fact,
    show gridC3.getD 171 0 = 1700 by kernel_fact,
    show faceC3.wn.getD 1 0 = 4508 by kernel_fact,
    show faceC3.wn.getD 29 0 = 5572 by kernel_fact,
    show faceC3.wd = 5068 from rfl, show faceC3.kind = 3 from rfl] at h

/-- **The cover of face 3.** -/
theorem faceCovC_3 : FaceCovC 3 :=
  ⟨_, _, _, _, coverC_3, by norm_num, by norm_num, by norm_num [faceLoC, aF],
    by norm_num [faceHiC, aF]⟩

end PlasmaLean.Design.PolygonCoil
