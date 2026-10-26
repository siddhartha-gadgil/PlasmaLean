/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 14

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

/-- Kernel-checked corner test at `(-1792/NT, 21760/NS)`. -/
theorem cn14_0 : cornerOK gdata (-1792) (21760)
    [630772090, 250786836, 300058387, 69017508, 45654870, 7912432, 1391315] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 21760/NS)`. -/
theorem cn14_1 : cornerOK gdata (-1728) (21760)
    [630772090, 250786836, 300058387, 69017508, 45654870, 7912432, 1391315] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 23040/NS)`. -/
theorem cn14_2 : cornerOK gdata (-1792) (23040)
    [783290561, 301135165, 369273622, 80904915, 54511423, 9189317, 1517588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 23040/NS)`. -/
theorem cn14_3 : cornerOK gdata (-1728) (23040)
    [783290561, 301135165, 369273622, 80904915, 54511423, 9189317, 1517588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 24320/NS)`. -/
theorem cn14_4 : cornerOK gdata (-1792) (24320)
    [977997765, 364879999, 457461701, 95079753, 65569262, 10720701, 1657793] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 24320/NS)`. -/
theorem cn14_5 : cornerOK gdata (-1728) (24320)
    [977997765, 364879999, 457461701, 95079753, 65569262, 10720701, 1657793] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 25600/NS)`. -/
theorem cn14_6 : cornerOK gdata (-1792) (25600)
    [977997765, 364879999, 457461701, 95079753, 65569262, 10720701, 1657793] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 25600/NS)`. -/
theorem cn14_7 : cornerOK gdata (-1728) (25600)
    [977997765, 364879999, 457461701, 95079753, 65569262, 10720701, 1657793] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 20480/NS)`. -/
theorem cn14_8 : cornerOK gdata (-1728) (20480)
    [460851829, 193191515, 224944254, 55066024, 35006358, 6423963, 1173046] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 20480/NS)`. -/
theorem cn14_9 : cornerOK gdata (-1664) (20480)
    [1387166063, 584547192, 696891334, 201156235, 107001055, 22737066, 3457986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 21760/NS)`. -/
theorem cn14_10 : cornerOK gdata (-1664) (21760)
    [1387166063, 584547192, 696891334, 201156235, 107001055, 22737066, 3457986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 23040/NS)`. -/
theorem cn14_11 : cornerOK gdata (-1664) (23040)
    [699130106, 269137091, 333515187, 74352858, 48955363, 8537703, 1387274] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 24320/NS)`. -/
theorem cn14_12 : cornerOK gdata (-1664) (24320)
    [699130106, 269137091, 333515187, 74352858, 48955363, 8537703, 1387274] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1696/NT, 24320/NS)`. -/
theorem cn14_13 : cornerOK gdata (-1696) (24320)
    [460424894, 179447782, 218216893, 40289219, 31055517, 4602277, 783527] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1696/NT, 25600/NS)`. -/
theorem cn14_14 : cornerOK gdata (-1696) (25600)
    [460424894, 179447782, 218216893, 40289219, 31055517, 4602277, 783527] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 25600/NS)`. -/
theorem cn14_15 : cornerOK gdata (-1664) (25600)
    [425685556, 166854158, 204465362, 38088308, 28923517, 4391982, 740000] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 20480/NS)`. -/
theorem cn14_16 : cornerOK gdata (-1536) (20480)
    [1387166063, 584547192, 696891334, 201156235, 107001055, 22737066, 3457986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 21760/NS)`. -/
theorem cn14_17 : cornerOK gdata (-1536) (21760)
    [1472744977, 594935413, 739744005, 212200624, 110354318, 23803389, 3457986] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 21760/NS)`. -/
theorem cn14_18 : cornerOK gdata (-1600) (21760)
    [506416673, 204594663, 247580567, 59167354, 37121706, 6881388, 1166690] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 23040/NS)`. -/
theorem cn14_19 : cornerOK gdata (-1600) (23040)
    [621252169, 240023690, 300224901, 68504128, 43766705, 7904885, 1266587] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 23040/NS)`. -/
theorem cn14_20 : cornerOK gdata (-1536) (23040)
    [1472744977, 594935413, 739744005, 212200624, 110354318, 23803389, 3454465] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 24320/NS)`. -/
theorem cn14_21 : cornerOK gdata (-1600) (24320)
    [621252169, 240023690, 300224901, 68504128, 43766705, 7904885, 1266587] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1632/NT, 24320/NS)`. -/
theorem cn14_22 : cornerOK gdata (-1632) (24320)
    [392950335, 154684364, 191306679, 36002232, 26897197, 4186766, 698226] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1632/NT, 25600/NS)`. -/
theorem cn14_23 : cornerOK gdata (-1632) (25600)
    [392950335, 154684364, 191306679, 36002232, 26897197, 4186766, 698226] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 25600/NS)`. -/
theorem cn14_24 : cornerOK gdata (-1600) (25600)
    [362111466, 142922348, 178709597, 34035144, 24971108, 3987214, 658244] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 24320/NS)`. -/
theorem cn14_25 : cornerOK gdata (-1536) (24320)
    [549734774, 212217963, 269327395, 63028036, 38998061, 7292482, 1154610] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1568/NT, 24320/NS)`. -/
theorem cn14_26 : cornerOK gdata (-1568) (24320)
    [333090470, 131936885, 166751537, 32157542, 23142536, 3795088, 620644] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1568/NT, 25600/NS)`. -/
theorem cn14_27 : cornerOK gdata (-1568) (25600)
    [333090470, 131936885, 166751537, 32157542, 23142536, 3795088, 620644] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 25600/NS)`. -/
theorem cn14_28 : cornerOK gdata (-1536) (25600)
    [305787343, 121627078, 155357384, 30356389, 21405200, 3607991, 584543] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 20480/NS)`. -/
theorem cn14_29 : cornerOK gdata (-1408) (20480)
    [1242881024, 510413457, 680035242, 181602607, 98782422, 20356336, 3324780] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 21760/NS)`. -/
theorem cn14_30 : cornerOK gdata (-1408) (21760)
    [1472744977, 594935413, 739744005, 212200624, 110354318, 23803389, 3454465] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 23040/NS)`. -/
theorem cn14_31 : cornerOK gdata (-1408) (23040)
    [1472744977, 594935413, 739744005, 212200624, 110354318, 23803389, 3454465] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 23040/NS)`. -/
theorem cn14_32 : cornerOK gdata (-1472) (23040)
    [484481210, 185657326, 241054458, 57823966, 34728639, 6705011, 1051457] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 24320/NS)`. -/
theorem cn14_33 : cornerOK gdata (-1472) (24320)
    [515508081, 193124595, 256737509, 60475175, 36454838, 6965073, 1051457] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1504/NT, 24320/NS)`. -/
theorem cn14_34 : cornerOK gdata (-1504) (24320)
    [280140696, 111665493, 144460959, 28630361, 19756576, 3427243, 550292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1504/NT, 25600/NS)`. -/
theorem cn14_35 : cornerOK gdata (-1504) (25600)
    [280140696, 111665493, 144460959, 28630361, 19756576, 3427243, 550292] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 25600/NS)`. -/
theorem cn14_36 : cornerOK gdata (-1472) (25600)
    [515508081, 193124595, 256737509, 60475175, 36454838, 6965073, 1032422] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 24320/NS)`. -/
theorem cn14_37 : cornerOK gdata (-1408) (24320)
    [515508081, 193124595, 256737509, 60475175, 36454838, 6965073, 1032422] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 25600/NS)`. -/
theorem cn14_38 : cornerOK gdata (-1408) (25600)
    [515508081, 193124595, 256737509, 60475175, 36454838, 6965073, 1032422] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 20480/NS)`. -/
theorem cn14_39 : cornerOK gdata (-1344) (20480)
    [1242881024, 510413457, 680035242, 169187289, 98782422, 18867268, 3324780] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 23040/NS)`. -/
theorem cn14_40 : cornerOK gdata (-1344) (23040)
    [1242881024, 510413457, 680035242, 169187289, 98782422, 18867268, 3324780] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 24320/NS)`. -/
theorem cn14_41 : cornerOK gdata (-1344) (24320)
    [449825815, 172176310, 227098001, 55049568, 32185866, 6330447, 936348] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1344/NT, 25600/NS)`. -/
theorem cn14_42 : cornerOK gdata (-1344) (25600)
    [449825815, 172176310, 227098001, 55049568, 32185866, 6330447, 936348] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 20480/NS)`. -/
theorem cn14_43 : cornerOK gdata (-1280) (20480)
    [1072454169, 437899946, 586898238, 149365278, 86831409, 16704556, 2917342] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 23040/NS)`. -/
theorem cn14_44 : cornerOK gdata (-1280) (23040)
    [1072454169, 437899946, 586898238, 149365278, 86831409, 16704556, 2917342] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 24320/NS)`. -/
theorem cn14_45 : cornerOK gdata (-1280) (24320)
    [396826147, 153333828, 200985234, 50026201, 29032902, 5733058, 848479] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 25600/NS)`. -/
theorem cn14_46 : cornerOK gdata (-1280) (25600)
    [757437358, 281162008, 417156727, 94201307, 58903663, 10799689, 1770320] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 20480/NS)`. -/
theorem cn14_47 : cornerOK gdata (-1216) (20480)
    [939702813, 373715190, 504939305, 131528933, 76314579, 14748370, 2551931] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 23040/NS)`. -/
theorem cn14_48 : cornerOK gdata (-1216) (23040)
    [1094574634, 388032693, 572947782, 141506370, 84683646, 15488806, 2551931] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1248/NT, 23040/NS)`. -/
theorem cn14_49 : cornerOK gdata (-1248) (23040)
    [757437358, 281162008, 417156727, 94201307, 58903663, 10799689, 1770320] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1248/NT, 25600/NS)`. -/
theorem cn14_50 : cornerOK gdata (-1248) (25600)
    [757437358, 281162008, 417156727, 94201307, 58903663, 10799689, 1770320] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1216/NT, 25600/NS)`. -/
theorem cn14_51 : cornerOK gdata (-1216) (25600)
    [1094574634, 388032693, 572947782, 141506370, 84683646, 15488806, 2469672] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 20480/NS)`. -/
theorem cn14_52 : cornerOK gdata (-1152) (20480)
    [1867274211, 771452355, 989014677, 288074555, 153435679, 30718287, 5043892] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 23040/NS)`. -/
theorem cn14_53 : cornerOK gdata (-1152) (23040)
    [1867274211, 771452355, 989014677, 288074555, 153435679, 30718287, 5043892] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 25600/NS)`. -/
theorem cn14_54 : cornerOK gdata (-1152) (25600)
    [1094574634, 388032693, 572947782, 141506370, 84683646, 15488806, 2469672] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 20480/NS)`. -/
theorem cn14_55 : cornerOK gdata (-1024) (20480)
    [1867274211, 771452355, 989014677, 288074555, 153435679, 30718287, 5043892] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 23040/NS)`. -/
theorem cn14_56 : cornerOK gdata (-1024) (23040)
    [1867274211, 771452355, 989014677, 288074555, 153435679, 30718287, 5043892] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 23040/NS)`. -/
theorem cn14_57 : cornerOK gdata (-1088) (23040)
    [943830399, 337608030, 483426938, 123063699, 73756063, 13463807, 2148891] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1088/NT, 25600/NS)`. -/
theorem cn14_58 : cornerOK gdata (-1088) (25600)
    [943830399, 337608030, 483426938, 123063699, 73756063, 13463807, 2148891] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 25600/NS)`. -/
theorem cn14_59 : cornerOK gdata (-1024) (25600)
    [810139632, 302512987, 407151261, 106752601, 64175006, 11668620, 1878277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 20480/NS)`. -/
theorem cn14_60 : cornerOK gdata (-896) (20480)
    [1457061823, 636119427, 781023293, 228892547, 123310011, 24157780, 4181581] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 23040/NS)`. -/
theorem cn14_61 : cornerOK gdata (-896) (23040)
    [1457061823, 636119427, 781023293, 228892547, 123310011, 24157780, 4181581] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-960/NT, 23040/NS)`. -/
theorem cn14_62 : cornerOK gdata (-960) (23040)
    [692940289, 274285065, 350823518, 92539610, 55860218, 10083650, 1642819] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-960/NT, 25600/NS)`. -/
theorem cn14_63 : cornerOK gdata (-960) (25600)
    [692940289, 274285065, 350823518, 92539610, 55860218, 10083650, 1642819] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 25600/NS)`. -/
theorem cn14_64 : cornerOK gdata (-896) (25600)
    [589828358, 248995858, 302198699, 80447765, 48617239, 8723794, 1436839] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 20480/NS)`. -/
theorem cn14_65 : cornerOK gdata (-768) (20480)
    [1122440133, 525940974, 614001296, 180543914, 98821423, 18790066, 3489964] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 23040/NS)`. -/
theorem cn14_66 : cornerOK gdata (-768) (23040)
    [1125945536, 574385232, 634414495, 187706734, 100376004, 18790066, 3489964] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-832/NT, 23040/NS)`. -/
theorem cn14_67 : cornerOK gdata (-832) (23040)
    [499694995, 229700832, 260999864, 71429514, 42343477, 7696691, 1256967] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-832/NT, 25600/NS)`. -/
theorem cn14_68 : cornerOK gdata (-832) (25600)
    [499694995, 229700832, 260999864, 71429514, 42343477, 7696691, 1256967] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 25600/NS)`. -/
theorem cn14_69 : cornerOK gdata (-768) (25600)
    [1125945536, 574385232, 634414495, 187706734, 100376004, 18770495, 3480361] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 20480/NS)`. -/
theorem cn14_70 : cornerOK gdata (-640) (20480)
    [1000380977, 581341014, 590557036, 178858816, 93510277, 17894624, 2928727] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 23040/NS)`. -/
theorem cn14_71 : cornerOK gdata (-640) (23040)
    [1125945536, 574385232, 634414495, 187706734, 100376004, 18770495, 3480361] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 25600/NS)`. -/
theorem cn14_72 : cornerOK gdata (-640) (25600)
    [1125945536, 581341014, 634414495, 187706734, 100376004, 18770495, 3480361] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-576/NT, 20480/NS)`. -/
theorem cn14_73 : cornerOK gdata (-576) (20480)
    [1000380977, 581341014, 590557036, 178858816, 93510277, 17894624, 2702329] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-576/NT, 25600/NS)`. -/
theorem cn14_74 : cornerOK gdata (-576) (25600)
    [1000380977, 581341014, 590557036, 178858816, 93510277, 17894624, 2702329] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 20480/NS)`. -/
theorem cn14_75 : cornerOK gdata (-512) (20480)
    [804543887, 503011933, 494747986, 153090634, 78703351, 14931955, 2331449] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 25600/NS)`. -/
theorem cn14_76 : cornerOK gdata (-512) (25600)
    [804543887, 503011933, 494747986, 153090634, 78703351, 14931955, 2331449] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-448/NT, 20480/NS)`. -/
theorem cn14_77 : cornerOK gdata (-448) (20480)
    [647541208, 434859053, 417889006, 132300508, 66845009, 12476937, 2055901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-448/NT, 25600/NS)`. -/
theorem cn14_78 : cornerOK gdata (-448) (25600)
    [647541208, 434859053, 417889006, 132300508, 66845009, 12476937, 2055901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 20480/NS)`. -/
theorem cn14_79 : cornerOK gdata (-384) (20480)
    [1055554306, 656232924, 665296442, 228287716, 107910545, 20952749, 4479144] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 25600/NS)`. -/
theorem cn14_80 : cornerOK gdata (-384) (25600)
    [1055554306, 656232924, 665296442, 228287716, 107910545, 20952749, 4479144] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 20480/NS)`. -/
theorem cn14_81 : cornerOK gdata (-256) (20480)
    [1055554306, 656232924, 665296442, 228287716, 107910545, 20952749, 4479144] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 25600/NS)`. -/
theorem cn14_82 : cornerOK gdata (-256) (25600)
    [1055554306, 656232924, 665296442, 228287716, 107910545, 20952749, 4479144] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-128/NT, 20480/NS)`. -/
theorem cn14_83 : cornerOK gdata (-128) (20480)
    [777889702, 494645556, 502952451, 184182831, 84901495, 16436556, 3921529] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-128/NT, 25600/NS)`. -/
theorem cn14_84 : cornerOK gdata (-128) (25600)
    [777889702, 494645556, 502952451, 184182831, 84901495, 16436556, 3921529] = true := by
  bl_cert

/-- Kernel-checked box `[-1792, -1728]/NT × [21760, 23040]/NS`. -/
theorem cov722 : Cover gdata (-1792) (-1728) (21760) (23040) := by
  ballooning_box "Q:cn14_0,cn14_1,cn14_2,cn14_3"

/-- Kernel-checked box `[-1792, -1728]/NT × [23040, 24320]/NS`. -/
theorem cov723 : Cover gdata (-1792) (-1728) (23040) (24320) := by
  ballooning_box "Q:cn14_2,cn14_3,cn14_4,cn14_5"

/-- Kernel-checked box `[-1792, -1728]/NT × [24320, 25600]/NS`. -/
theorem cov724 : Cover gdata (-1792) (-1728) (24320) (25600) := by
  ballooning_box "Q:cn14_4,cn14_5,cn14_6,cn14_7"

/-- Kernel-checked box `[-1728, -1664]/NT × [20480, 21760]/NS`. -/
theorem cov725 : Cover gdata (-1728) (-1664) (20480) (21760) := by
  ballooning_box "Q:cn14_8,cn14_9,cn14_1,cn14_10"

/-- Kernel-checked box `[-1728, -1664]/NT × [21760, 23040]/NS`. -/
theorem cov726 : Cover gdata (-1728) (-1664) (21760) (23040) := by
  ballooning_box "Q:cn14_1,cn14_10,cn14_3,cn14_11"

/-- Kernel-checked box `[-1728, -1664]/NT × [23040, 24320]/NS`. -/
theorem cov727 : Cover gdata (-1728) (-1664) (23040) (24320) := by
  ballooning_box "Q:cn14_3,cn14_11,cn14_5,cn14_12"

/-- Kernel-checked box `[-1728, -1696]/NT × [24320, 25600]/NS`. -/
theorem cov728 : Cover gdata (-1728) (-1696) (24320) (25600) := by
  ballooning_box "Q:cn14_5,cn14_13,cn14_7,cn14_14"

/-- Kernel-checked box `[-1696, -1664]/NT × [24320, 25600]/NS`. -/
theorem cov729 : Cover gdata (-1696) (-1664) (24320) (25600) := by
  ballooning_box "Q:cn14_13,cn14_12,cn14_14,cn14_15"

/-- Kernel-checked box `[-1664, -1536]/NT × [20480, 21760]/NS`. -/
theorem cov730 : Cover gdata (-1664) (-1536) (20480) (21760) := by
  ballooning_box "Q:cn14_9,cn14_16,cn14_10,cn14_17"

/-- Kernel-checked box `[-1664, -1600]/NT × [21760, 23040]/NS`. -/
theorem cov731 : Cover gdata (-1664) (-1600) (21760) (23040) := by
  ballooning_box "Q:cn14_10,cn14_18,cn14_11,cn14_19"

/-- Kernel-checked box `[-1600, -1536]/NT × [21760, 23040]/NS`. -/
theorem cov732 : Cover gdata (-1600) (-1536) (21760) (23040) := by
  ballooning_box "Q:cn14_18,cn14_17,cn14_19,cn14_20"

/-- Kernel-checked box `[-1664, -1600]/NT × [23040, 24320]/NS`. -/
theorem cov733 : Cover gdata (-1664) (-1600) (23040) (24320) := by
  ballooning_box "Q:cn14_11,cn14_19,cn14_12,cn14_21"

/-- Kernel-checked box `[-1664, -1632]/NT × [24320, 25600]/NS`. -/
theorem cov734 : Cover gdata (-1664) (-1632) (24320) (25600) := by
  ballooning_box "Q:cn14_12,cn14_22,cn14_15,cn14_23"

/-- Kernel-checked box `[-1632, -1600]/NT × [24320, 25600]/NS`. -/
theorem cov735 : Cover gdata (-1632) (-1600) (24320) (25600) := by
  ballooning_box "Q:cn14_22,cn14_21,cn14_23,cn14_24"

/-- Kernel-checked box `[-1600, -1536]/NT × [23040, 24320]/NS`. -/
theorem cov736 : Cover gdata (-1600) (-1536) (23040) (24320) := by
  ballooning_box "Q:cn14_19,cn14_20,cn14_21,cn14_25"

/-- Kernel-checked box `[-1600, -1568]/NT × [24320, 25600]/NS`. -/
theorem cov737 : Cover gdata (-1600) (-1568) (24320) (25600) := by
  ballooning_box "Q:cn14_21,cn14_26,cn14_24,cn14_27"

/-- Kernel-checked box `[-1568, -1536]/NT × [24320, 25600]/NS`. -/
theorem cov738 : Cover gdata (-1568) (-1536) (24320) (25600) := by
  ballooning_box "Q:cn14_26,cn14_25,cn14_27,cn14_28"

/-- Kernel-checked box `[-1536, -1408]/NT × [20480, 21760]/NS`. -/
theorem cov739 : Cover gdata (-1536) (-1408) (20480) (21760) := by
  ballooning_box "Q:cn14_16,cn14_29,cn14_17,cn14_30"

/-- Kernel-checked box `[-1536, -1408]/NT × [21760, 23040]/NS`. -/
theorem cov740 : Cover gdata (-1536) (-1408) (21760) (23040) := by
  ballooning_box "Q:cn14_17,cn14_30,cn14_20,cn14_31"

/-- Kernel-checked box `[-1536, -1472]/NT × [23040, 24320]/NS`. -/
theorem cov741 : Cover gdata (-1536) (-1472) (23040) (24320) := by
  ballooning_box "Q:cn14_20,cn14_32,cn14_25,cn14_33"

/-- Kernel-checked box `[-1536, -1504]/NT × [24320, 25600]/NS`. -/
theorem cov742 : Cover gdata (-1536) (-1504) (24320) (25600) := by
  ballooning_box "Q:cn14_25,cn14_34,cn14_28,cn14_35"

/-- Kernel-checked box `[-1504, -1472]/NT × [24320, 25600]/NS`. -/
theorem cov743 : Cover gdata (-1504) (-1472) (24320) (25600) := by
  ballooning_box "Q:cn14_34,cn14_33,cn14_35,cn14_36"

/-- Kernel-checked box `[-1472, -1408]/NT × [23040, 24320]/NS`. -/
theorem cov744 : Cover gdata (-1472) (-1408) (23040) (24320) := by
  ballooning_box "Q:cn14_32,cn14_31,cn14_33,cn14_37"

/-- Kernel-checked box `[-1472, -1408]/NT × [24320, 25600]/NS`. -/
theorem cov745 : Cover gdata (-1472) (-1408) (24320) (25600) := by
  ballooning_box "Q:cn14_33,cn14_37,cn14_36,cn14_38"

/-- Kernel-checked box `[-1408, -1344]/NT × [20480, 23040]/NS`. -/
theorem cov746 : Cover gdata (-1408) (-1344) (20480) (23040) := by
  ballooning_box "Q:cn14_29,cn14_39,cn14_31,cn14_40"

/-- Kernel-checked box `[-1408, -1344]/NT × [23040, 24320]/NS`. -/
theorem cov747 : Cover gdata (-1408) (-1344) (23040) (24320) := by
  ballooning_box "Q:cn14_31,cn14_40,cn14_37,cn14_41"

/-- Kernel-checked box `[-1408, -1344]/NT × [24320, 25600]/NS`. -/
theorem cov748 : Cover gdata (-1408) (-1344) (24320) (25600) := by
  ballooning_box "Q:cn14_37,cn14_41,cn14_38,cn14_42"

/-- Kernel-checked box `[-1344, -1280]/NT × [20480, 23040]/NS`. -/
theorem cov749 : Cover gdata (-1344) (-1280) (20480) (23040) := by
  ballooning_box "Q:cn14_39,cn14_43,cn14_40,cn14_44"

/-- Kernel-checked box `[-1344, -1280]/NT × [23040, 24320]/NS`. -/
theorem cov750 : Cover gdata (-1344) (-1280) (23040) (24320) := by
  ballooning_box "Q:cn14_40,cn14_44,cn14_41,cn14_45"

/-- Kernel-checked box `[-1344, -1280]/NT × [24320, 25600]/NS`. -/
theorem cov751 : Cover gdata (-1344) (-1280) (24320) (25600) := by
  ballooning_box "Q:cn14_41,cn14_45,cn14_42,cn14_46"

/-- Kernel-checked box `[-1280, -1216]/NT × [20480, 23040]/NS`. -/
theorem cov752 : Cover gdata (-1280) (-1216) (20480) (23040) := by
  ballooning_box "Q:cn14_43,cn14_47,cn14_44,cn14_48"

/-- Kernel-checked box `[-1280, -1248]/NT × [23040, 25600]/NS`. -/
theorem cov753 : Cover gdata (-1280) (-1248) (23040) (25600) := by
  ballooning_box "Q:cn14_44,cn14_49,cn14_46,cn14_50"

/-- Kernel-checked box `[-1248, -1216]/NT × [23040, 25600]/NS`. -/
theorem cov754 : Cover gdata (-1248) (-1216) (23040) (25600) := by
  ballooning_box "Q:cn14_49,cn14_48,cn14_50,cn14_51"

/-- Kernel-checked box `[-1216, -1152]/NT × [20480, 23040]/NS`. -/
theorem cov755 : Cover gdata (-1216) (-1152) (20480) (23040) := by
  ballooning_box "Q:cn14_47,cn14_52,cn14_48,cn14_53"

/-- Kernel-checked box `[-1216, -1152]/NT × [23040, 25600]/NS`. -/
theorem cov756 : Cover gdata (-1216) (-1152) (23040) (25600) := by
  ballooning_box "Q:cn14_48,cn14_53,cn14_51,cn14_54"

/-- Kernel-checked box `[-1152, -1024]/NT × [20480, 23040]/NS`. -/
theorem cov757 : Cover gdata (-1152) (-1024) (20480) (23040) := by
  ballooning_box "Q:cn14_52,cn14_55,cn14_53,cn14_56"

/-- Kernel-checked box `[-1152, -1088]/NT × [23040, 25600]/NS`. -/
theorem cov758 : Cover gdata (-1152) (-1088) (23040) (25600) := by
  ballooning_box "Q:cn14_53,cn14_57,cn14_54,cn14_58"

/-- Kernel-checked box `[-1088, -1024]/NT × [23040, 25600]/NS`. -/
theorem cov759 : Cover gdata (-1088) (-1024) (23040) (25600) := by
  ballooning_box "Q:cn14_57,cn14_56,cn14_58,cn14_59"

/-- Kernel-checked box `[-1024, -896]/NT × [20480, 23040]/NS`. -/
theorem cov760 : Cover gdata (-1024) (-896) (20480) (23040) := by
  ballooning_box "Q:cn14_55,cn14_60,cn14_56,cn14_61"

/-- Kernel-checked box `[-1024, -960]/NT × [23040, 25600]/NS`. -/
theorem cov761 : Cover gdata (-1024) (-960) (23040) (25600) := by
  ballooning_box "Q:cn14_56,cn14_62,cn14_59,cn14_63"

/-- Kernel-checked box `[-960, -896]/NT × [23040, 25600]/NS`. -/
theorem cov762 : Cover gdata (-960) (-896) (23040) (25600) := by
  ballooning_box "Q:cn14_62,cn14_61,cn14_63,cn14_64"

/-- Kernel-checked box `[-896, -768]/NT × [20480, 23040]/NS`. -/
theorem cov763 : Cover gdata (-896) (-768) (20480) (23040) := by
  ballooning_box "Q:cn14_60,cn14_65,cn14_61,cn14_66"

/-- Kernel-checked box `[-896, -832]/NT × [23040, 25600]/NS`. -/
theorem cov764 : Cover gdata (-896) (-832) (23040) (25600) := by
  ballooning_box "Q:cn14_61,cn14_67,cn14_64,cn14_68"

/-- Kernel-checked box `[-832, -768]/NT × [23040, 25600]/NS`. -/
theorem cov765 : Cover gdata (-832) (-768) (23040) (25600) := by
  ballooning_box "Q:cn14_67,cn14_66,cn14_68,cn14_69"

/-- Kernel-checked box `[-768, -640]/NT × [20480, 23040]/NS`. -/
theorem cov766 : Cover gdata (-768) (-640) (20480) (23040) := by
  ballooning_box "Q:cn14_65,cn14_70,cn14_66,cn14_71"

/-- Kernel-checked box `[-768, -640]/NT × [23040, 25600]/NS`. -/
theorem cov767 : Cover gdata (-768) (-640) (23040) (25600) := by
  ballooning_box "Q:cn14_66,cn14_71,cn14_69,cn14_72"

/-- Kernel-checked box `[-640, -576]/NT × [20480, 25600]/NS`. -/
theorem cov768 : Cover gdata (-640) (-576) (20480) (25600) := by
  ballooning_box "Q:cn14_70,cn14_73,cn14_72,cn14_74"

/-- Kernel-checked box `[-576, -512]/NT × [20480, 25600]/NS`. -/
theorem cov769 : Cover gdata (-576) (-512) (20480) (25600) := by
  ballooning_box "Q:cn14_73,cn14_75,cn14_74,cn14_76"

/-- Kernel-checked box `[-512, -448]/NT × [20480, 25600]/NS`. -/
theorem cov770 : Cover gdata (-512) (-448) (20480) (25600) := by
  ballooning_box "Q:cn14_75,cn14_77,cn14_76,cn14_78"

/-- Kernel-checked box `[-448, -384]/NT × [20480, 25600]/NS`. -/
theorem cov771 : Cover gdata (-448) (-384) (20480) (25600) := by
  ballooning_box "Q:cn14_77,cn14_79,cn14_78,cn14_80"

/-- Kernel-checked box `[-384, -256]/NT × [20480, 25600]/NS`. -/
theorem cov772 : Cover gdata (-384) (-256) (20480) (25600) := by
  ballooning_box "Q:cn14_79,cn14_81,cn14_80,cn14_82"

/-- Kernel-checked box `[-256, -128]/NT × [20480, 25600]/NS`. -/
theorem cov773 : Cover gdata (-256) (-128) (20480) (25600) := by
  ballooning_box "Q:cn14_81,cn14_83,cn14_82,cn14_84"

end PlasmaLean.Design.SolovevBallooning
