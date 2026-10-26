/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningEvalCert

/-!
# Ballooning certificate: kernel-checked cells, part 8

52 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(3584/NT, 8192/NS)`. -/
theorem cn08_0 : cornerOK gdata (3584) (8192)
    [245146445, 118238289, 306748337, 60657464, 100494429, 7380211, 10122679] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 8192/NS)`. -/
theorem cn08_1 : cornerOK gdata (3840) (8192)
    [245146445, 118238289, 306748337, 60657464, 100494429, 7380211, 10122679] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 10240/NS)`. -/
theorem cn08_2 : cornerOK gdata (3584) (10240)
    [245146445, 125727171, 318648136, 65356758, 107042858, 7963189, 10900035] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 10240/NS)`. -/
theorem cn08_3 : cornerOK gdata (3840) (10240)
    [245146445, 125727171, 318648136, 65356758, 107042858, 7963189, 10900035] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3584/NT, 12288/NS)`. -/
theorem cn08_4 : cornerOK gdata (3584) (12288)
    [238052758, 125727171, 318648136, 65356758, 107042858, 7963189, 10900035] = true := by
  bl_cert

/-- Kernel-checked corner test at `(3840/NT, 12288/NS)`. -/
theorem cn08_5 : cornerOK gdata (3840) (12288)
    [238052758, 125727171, 318648136, 65356758, 107042858, 7963189, 10900035] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 8192/NS)`. -/
theorem cn08_6 : cornerOK gdata (4096) (8192)
    [219680284, 77808382, 279790709, 40588390, 93175337, 5014868, 9502836] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 10240/NS)`. -/
theorem cn08_7 : cornerOK gdata (4096) (10240)
    [219680284, 82208192, 287488375, 43728206, 98473467, 5422161, 10153165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(4096/NT, 12288/NS)`. -/
theorem cn08_8 : cornerOK gdata (4096) (12288)
    [210741664, 82208192, 287488375, 43728206, 98473467, 5422161, 10153165] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 12288/NS)`. -/
theorem cn08_9 : cornerOK gdata (-4096) (12288)
    [1602100832, 128661684, 874369524, 48926660, 193350311, 5949043, 13166046] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 12288/NS)`. -/
theorem cn08_10 : cornerOK gdata (-3968) (12288)
    [1633941731, 188128358, 891596763, 71996779, 196383215, 8633859, 13296361] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 14336/NS)`. -/
theorem cn08_11 : cornerOK gdata (-4096) (14336)
    [2401987844, 178886913, 1232090277, 65881443, 257481436, 8062228, 16073135] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 14336/NS)`. -/
theorem cn08_12 : cornerOK gdata (-3968) (14336)
    [2451692770, 264265916, 1257762349, 97732054, 261723893, 11915636, 16234269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 16384/NS)`. -/
theorem cn08_13 : cornerOK gdata (-4096) (16384)
    [2401987844, 178886913, 1232090277, 65881443, 257481436, 8062228, 16073135] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 16384/NS)`. -/
theorem cn08_14 : cornerOK gdata (-3968) (16384)
    [2451692770, 264265916, 1257762349, 97732054, 261723893, 11915636, 16234269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 12288/NS)`. -/
theorem cn08_15 : cornerOK gdata (-3840) (12288)
    [1633941731, 188128358, 891596763, 71996779, 196383215, 8633859, 13296361] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 14336/NS)`. -/
theorem cn08_16 : cornerOK gdata (-3840) (14336)
    [2451692770, 387568680, 1257762349, 152745215, 261723893, 17869993, 16234269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 16384/NS)`. -/
theorem cn08_17 : cornerOK gdata (-3840) (16384)
    [2451692770, 469365525, 1257762349, 181415636, 261723893, 21303499, 16234269] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 12288/NS)`. -/
theorem cn08_18 : cornerOK gdata (-3840) (12288)
    [893032171, 268099810, 504151812, 109217781, 107874689, 12708853, 6495874] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 12288/NS)`. -/
theorem cn08_19 : cornerOK gdata (-3584) (12288)
    [1034280024, 389834840, 587273827, 157998211, 122063377, 18095452, 7110172] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 13312/NS)`. -/
theorem cn08_20 : cornerOK gdata (-3840) (13312)
    [1112611227, 321975101, 608888571, 129008299, 125963321, 15046178, 7287875] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 13312/NS)`. -/
theorem cn08_21 : cornerOK gdata (-3584) (13312)
    [1293193364, 470984130, 709229047, 187928725, 143057755, 21578298, 7988701] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 14336/NS)`. -/
theorem cn08_22 : cornerOK gdata (-3584) (14336)
    [1623633773, 570301888, 864956923, 223985700, 168517950, 25815922, 8993209] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 15360/NS)`. -/
theorem cn08_23 : cornerOK gdata (-3840) (15360)
    [1748260088, 469365525, 904028746, 181415636, 174419037, 21303499, 9226029] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 15360/NS)`. -/
theorem cn08_24 : cornerOK gdata (-3584) (15360)
    [2047580080, 692484083, 1060350143, 267665957, 199658405, 30999136, 10144525] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 16384/NS)`. -/
theorem cn08_25 : cornerOK gdata (-3584) (16384)
    [2047580080, 692484083, 1060350143, 267665957, 199658405, 30999136, 10144525] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 12288/NS)`. -/
theorem cn08_26 : cornerOK gdata (-3328) (12288)
    [1109223342, 389834840, 587273827, 157998211, 125790769, 18095452, 8201686] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 13312/NS)`. -/
theorem cn08_27 : cornerOK gdata (-3328) (13312)
    [1293193364, 470984130, 709229047, 187928725, 143057755, 21578298, 7988701] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 14336/NS)`. -/
theorem cn08_28 : cornerOK gdata (-3328) (14336)
    [1628124984, 570301888, 864956923, 223985700, 168517950, 25815922, 9776327] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 15360/NS)`. -/
theorem cn08_29 : cornerOK gdata (-3328) (15360)
    [2047580080, 692484083, 1060350143, 267665957, 199658405, 30999136, 10144525] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 16384/NS)`. -/
theorem cn08_30 : cornerOK gdata (-3328) (16384)
    [2047580080, 692484083, 1060350143, 267665957, 199658405, 30999136, 10144525] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 12288/NS)`. -/
theorem cn08_31 : cornerOK gdata (-3264) (12288)
    [1109223342, 279743421, 575602621, 103764258, 125790769, 11627929, 8201686] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 14336/NS)`. -/
theorem cn08_32 : cornerOK gdata (-3264) (14336)
    [1628124984, 385411945, 794624992, 136900285, 164514491, 16117242, 9776327] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3264/NT, 16384/NS)`. -/
theorem cn08_33 : cornerOK gdata (-3264) (16384)
    [1628124984, 385411945, 794624992, 136900285, 164514491, 16117242, 9776327] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 12288/NS)`. -/
theorem cn08_34 : cornerOK gdata (-3200) (12288)
    [1104192775, 294495149, 572107811, 108889444, 124407665, 12166598, 8036388] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 14336/NS)`. -/
theorem cn08_35 : cornerOK gdata (-3200) (14336)
    [1621074802, 405122728, 790381565, 143358750, 162783017, 16788251, 9573329] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 16384/NS)`. -/
theorem cn08_36 : cornerOK gdata (-3200) (16384)
    [1621074802, 405122728, 790381565, 143358750, 162783017, 16788251, 9573329] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 12288/NS)`. -/
theorem cn08_37 : cornerOK gdata (-3136) (12288)
    [1097850487, 308266035, 568004835, 113573583, 122861267, 12672248, 7857882] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 14336/NS)`. -/
theorem cn08_38 : cornerOK gdata (-3136) (14336)
    [1610527751, 423396534, 784469025, 149198686, 160688079, 17376504, 9345546] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3136/NT, 16384/NS)`. -/
theorem cn08_39 : cornerOK gdata (-3136) (16384)
    [1610527751, 423396534, 784469025, 149198686, 160688079, 17376504, 9345546] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 12288/NS)`. -/
theorem cn08_40 : cornerOK gdata (-3072) (12288)
    [1090349485, 320754706, 563360837, 117718532, 121168736, 13118749, 7668960] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 14336/NS)`. -/
theorem cn08_41 : cornerOK gdata (-3072) (14336)
    [1598221556, 439762812, 777984781, 154281824, 158415390, 17860032, 9106000] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 16384/NS)`. -/
theorem cn08_42 : cornerOK gdata (-3072) (16384)
    [1598221556, 439762812, 777984781, 154281824, 158415390, 17860032, 9106000] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 12288/NS)`. -/
theorem cn08_43 : cornerOK gdata (-3008) (12288)
    [1080687126, 331813161, 557648390, 121288698, 119233077, 13503688, 7463750] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 14336/NS)`. -/
theorem cn08_44 : cornerOK gdata (-3008) (14336)
    [1582202732, 454091561, 769849778, 158558290, 155802988, 18238858, 8846621] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3008/NT, 16384/NS)`. -/
theorem cn08_45 : cornerOK gdata (-3008) (16384)
    [1582202732, 454091561, 769849778, 158558290, 155802988, 18238858, 8846621] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 12288/NS)`. -/
theorem cn08_46 : cornerOK gdata (-2944) (12288)
    [1068433978, 341443699, 550703282, 124269762, 117036490, 13822735, 7241195] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 14336/NS)`. -/
theorem cn08_47 : cornerOK gdata (-2944) (14336)
    [1562873005, 454091561, 760274074, 158558290, 152894018, 18238858, 8571163] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 16384/NS)`. -/
theorem cn08_48 : cornerOK gdata (-2944) (16384)
    [1562873005, 454091561, 760274074, 158558290, 152894018, 18238858, 8571163] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 12288/NS)`. -/
theorem cn08_49 : cornerOK gdata (-2880) (12288)
    [1054513253, 349582326, 543010974, 126650499, 114678103, 14075381, 7009541] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2880/NT, 14336/NS)`. -/
theorem cn08_50 : cornerOK gdata (-2880) (14336)
    [1054513253, 349582326, 543010974, 126650499, 114678103, 14075381, 7009541] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 12288/NS)`. -/
theorem cn08_51 : cornerOK gdata (-2816) (12288)
    [1038575151, 355906970, 534430915, 128341927, 112130664, 14254859, 6768045] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 14336/NS)`. -/
theorem cn08_52 : cornerOK gdata (-2816) (14336)
    [1038575151, 355906970, 534430915, 128341927, 112130664, 14254859, 6768045] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 15360/NS)`. -/
theorem cn08_53 : cornerOK gdata (-2944) (15360)
    [624933727, 240952905, 308048178, 86603107, 58659444, 9805031, 2986540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 15360/NS)`. -/
theorem cn08_54 : cornerOK gdata (-2816) (15360)
    [626261517, 258544794, 312468225, 92148039, 58659444, 10314144, 2986540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 16384/NS)`. -/
theorem cn08_55 : cornerOK gdata (-2816) (16384)
    [626261517, 258544794, 312468225, 92148039, 58659444, 10314144, 2986540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 12288/NS)`. -/
theorem cn08_56 : cornerOK gdata (-2752) (12288)
    [1019496899, 360696192, 524378427, 129428240, 109291853, 14366481, 6511126] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2752/NT, 14336/NS)`. -/
theorem cn08_57 : cornerOK gdata (-2752) (14336)
    [1019496899, 360696192, 524378427, 129428240, 109291853, 14366481, 6511126] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 12288/NS)`. -/
theorem cn08_58 : cornerOK gdata (-2688) (12288)
    [998869119, 363560432, 513704465, 129815461, 106327805, 14404053, 6250450] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 14336/NS)`. -/
theorem cn08_59 : cornerOK gdata (-2688) (14336)
    [998869119, 363560432, 513704465, 129815461, 106327805, 14404053, 6250450] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 15360/NS)`. -/
theorem cn08_60 : cornerOK gdata (-2688) (15360)
    [626261517, 272296147, 314544772, 96214629, 58417499, 10646803, 2903898] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 16384/NS)`. -/
theorem cn08_61 : cornerOK gdata (-2688) (16384)
    [626261517, 272296147, 314544772, 96214629, 58417499, 10646803, 2903898] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2624/NT, 12288/NS)`. -/
theorem cn08_62 : cornerOK gdata (-2624) (12288)
    [975133005, 364541494, 501628518, 129815461, 103157048, 14404053, 5978179] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2624/NT, 14336/NS)`. -/
theorem cn08_63 : cornerOK gdata (-2624) (14336)
    [975133005, 364541494, 501628518, 129815461, 103157048, 14404053, 5978179] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 12288/NS)`. -/
theorem cn08_64 : cornerOK gdata (-2560) (12288)
    [948884337, 364541494, 488411464, 129517414, 99800043, 14367355, 5700923] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 14336/NS)`. -/
theorem cn08_65 : cornerOK gdata (-2560) (14336)
    [1322958232, 488262313, 649178805, 164160451, 124618696, 18222180, 6317479] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 15360/NS)`. -/
theorem cn08_66 : cornerOK gdata (-2560) (15360)
    [621506598, 272296147, 314544772, 96214629, 58298954, 10646803, 2806339] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 16384/NS)`. -/
theorem cn08_67 : cornerOK gdata (-2560) (16384)
    [1322958232, 488262313, 649178805, 164160451, 124618696, 18222180, 6317479] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2496/NT, 12288/NS)`. -/
theorem cn08_68 : cornerOK gdata (-2496) (12288)
    [920920721, 363867429, 474525600, 128618861, 96331260, 14264523, 5443240] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2496/NT, 14336/NS)`. -/
theorem cn08_69 : cornerOK gdata (-2496) (14336)
    [1322958232, 488262313, 649178805, 164160451, 124618696, 18222180, 6317479] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2496/NT, 16384/NS)`. -/
theorem cn08_70 : cornerOK gdata (-2496) (16384)
    [1322958232, 488262313, 649178805, 164160451, 124618696, 18222180, 6317479] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 12288/NS)`. -/
theorem cn08_71 : cornerOK gdata (-2432) (12288)
    [890335057, 361285338, 459473333, 127072034, 92665987, 14093560, 5181940] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 14336/NS)`. -/
theorem cn08_72 : cornerOK gdata (-2432) (14336)
    [1273390749, 482806633, 626832094, 161445432, 119538186, 17912786, 5995526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 16384/NS)`. -/
theorem cn08_73 : cornerOK gdata (-2432) (16384)
    [1273390749, 482806633, 626832094, 161445432, 119538186, 17912786, 5995526] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2368/NT, 12288/NS)`. -/
theorem cn08_74 : cornerOK gdata (-2368) (12288)
    [857324485, 356672870, 443262421, 124839473, 88818341, 13849233, 4914562] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2368/NT, 14336/NS)`. -/
theorem cn08_75 : cornerOK gdata (-2368) (14336)
    [1221054842, 474890458, 603298788, 157944782, 114289689, 17518117, 5670782] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2368/NT, 16384/NS)`. -/
theorem cn08_76 : cornerOK gdata (-2368) (16384)
    [1221054842, 474890458, 603298788, 157944782, 114289689, 17518117, 5670782] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 12288/NS)`. -/
theorem cn08_77 : cornerOK gdata (-2304) (12288)
    [823150357, 350450749, 426339408, 122087428, 84861153, 13549771, 4649104] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 14336/NS)`. -/
theorem cn08_78 : cornerOK gdata (-2304) (14336)
    [1165765872, 464477766, 578319327, 153709600, 108832974, 17047187, 5347270] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 16384/NS)`. -/
theorem cn08_79 : cornerOK gdata (-2304) (16384)
    [1165765872, 464477766, 578319327, 153709600, 108832974, 17047187, 5347270] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 12288/NS)`. -/
theorem cn08_80 : cornerOK gdata (-2240) (12288)
    [787354766, 342451937, 408665392, 118768209, 80805232, 13189626, 4381671] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 14336/NS)`. -/
theorem cn08_81 : cornerOK gdata (-2240) (14336)
    [1109248190, 451825984, 552424346, 148812355, 103271701, 16505116, 5024847] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 16384/NS)`. -/
theorem cn08_82 : cornerOK gdata (-2240) (16384)
    [1109248190, 451825984, 552424346, 148812355, 103271701, 16505116, 5024847] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 12288/NS)`. -/
theorem cn08_83 : cornerOK gdata (-2176) (12288)
    [750103482, 332883031, 390318437, 114957489, 76661480, 12776974, 4116146] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 14336/NS)`. -/
theorem cn08_84 : cornerOK gdata (-2176) (14336)
    [1051001201, 437152566, 525824720, 143328771, 97649280, 15898360, 4704776] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 16384/NS)`. -/
theorem cn08_85 : cornerOK gdata (-2176) (16384)
    [1051001201, 437152566, 525824720, 143328771, 97649280, 15898360, 4704776] = true := by
  bl_cert

/-- Kernel-checked box `[3584, 3840]/NT × [8192, 10240]/NS`. -/
theorem cov413 : Cover gdata (3584) (3840) (8192) (10240) := by
  ballooning_cover "Q:cn08_0,cn08_1,cn08_2,cn08_3"

/-- Kernel-checked box `[3584, 3840]/NT × [10240, 12288]/NS`. -/
theorem cov414 : Cover gdata (3584) (3840) (10240) (12288) := by
  ballooning_cover "Q:cn08_2,cn08_3,cn08_4,cn08_5"

/-- Kernel-checked box `[3840, 4096]/NT × [8192, 10240]/NS`. -/
theorem cov415 : Cover gdata (3840) (4096) (8192) (10240) := by
  ballooning_cover "Q:cn08_1,cn08_6,cn08_3,cn08_7"

/-- Kernel-checked box `[3840, 4096]/NT × [10240, 12288]/NS`. -/
theorem cov416 : Cover gdata (3840) (4096) (10240) (12288) := by
  ballooning_cover "Q:cn08_3,cn08_7,cn08_5,cn08_8"

/-- Kernel-checked box `[-4096, -3968]/NT × [12288, 14336]/NS`. -/
theorem cov417 : Cover gdata (-4096) (-3968) (12288) (14336) := by
  ballooning_cover "Q:cn08_9,cn08_10,cn08_11,cn08_12"

/-- Kernel-checked box `[-4096, -3968]/NT × [14336, 16384]/NS`. -/
theorem cov418 : Cover gdata (-4096) (-3968) (14336) (16384) := by
  ballooning_cover "Q:cn08_11,cn08_12,cn08_13,cn08_14"

/-- Kernel-checked box `[-3968, -3840]/NT × [12288, 14336]/NS`. -/
theorem cov419 : Cover gdata (-3968) (-3840) (12288) (14336) := by
  ballooning_cover "Q:cn08_10,cn08_15,cn08_12,cn08_16"

/-- Kernel-checked box `[-3968, -3840]/NT × [14336, 16384]/NS`. -/
theorem cov420 : Cover gdata (-3968) (-3840) (14336) (16384) := by
  ballooning_cover "Q:cn08_12,cn08_16,cn08_14,cn08_17"

/-- Kernel-checked box `[-3840, -3584]/NT × [12288, 13312]/NS`. -/
theorem cov421 : Cover gdata (-3840) (-3584) (12288) (13312) := by
  ballooning_cover "Q:cn08_18,cn08_19,cn08_20,cn08_21"

/-- Kernel-checked box `[-3840, -3584]/NT × [13312, 14336]/NS`. -/
theorem cov422 : Cover gdata (-3840) (-3584) (13312) (14336) := by
  ballooning_cover "Q:cn08_20,cn08_21,cn08_16,cn08_22"

/-- Kernel-checked box `[-3840, -3584]/NT × [14336, 15360]/NS`. -/
theorem cov423 : Cover gdata (-3840) (-3584) (14336) (15360) := by
  ballooning_cover "Q:cn08_16,cn08_22,cn08_23,cn08_24"

/-- Kernel-checked box `[-3840, -3584]/NT × [15360, 16384]/NS`. -/
theorem cov424 : Cover gdata (-3840) (-3584) (15360) (16384) := by
  ballooning_cover "Q:cn08_23,cn08_24,cn08_17,cn08_25"

/-- Kernel-checked box `[-3584, -3328]/NT × [12288, 13312]/NS`. -/
theorem cov425 : Cover gdata (-3584) (-3328) (12288) (13312) := by
  ballooning_cover "Q:cn08_19,cn08_26,cn08_21,cn08_27"

/-- Kernel-checked box `[-3584, -3328]/NT × [13312, 14336]/NS`. -/
theorem cov426 : Cover gdata (-3584) (-3328) (13312) (14336) := by
  ballooning_cover "Q:cn08_21,cn08_27,cn08_22,cn08_28"

/-- Kernel-checked box `[-3584, -3328]/NT × [14336, 15360]/NS`. -/
theorem cov427 : Cover gdata (-3584) (-3328) (14336) (15360) := by
  ballooning_cover "Q:cn08_22,cn08_28,cn08_24,cn08_29"

/-- Kernel-checked box `[-3584, -3328]/NT × [15360, 16384]/NS`. -/
theorem cov428 : Cover gdata (-3584) (-3328) (15360) (16384) := by
  ballooning_cover "Q:cn08_24,cn08_29,cn08_25,cn08_30"

/-- Kernel-checked box `[-3328, -3264]/NT × [12288, 14336]/NS`. -/
theorem cov429 : Cover gdata (-3328) (-3264) (12288) (14336) := by
  ballooning_cover "Q:cn08_26,cn08_31,cn08_28,cn08_32"

/-- Kernel-checked box `[-3328, -3264]/NT × [14336, 16384]/NS`. -/
theorem cov430 : Cover gdata (-3328) (-3264) (14336) (16384) := by
  ballooning_cover "Q:cn08_28,cn08_32,cn08_30,cn08_33"

/-- Kernel-checked box `[-3264, -3200]/NT × [12288, 14336]/NS`. -/
theorem cov431 : Cover gdata (-3264) (-3200) (12288) (14336) := by
  ballooning_cover "Q:cn08_31,cn08_34,cn08_32,cn08_35"

/-- Kernel-checked box `[-3264, -3200]/NT × [14336, 16384]/NS`. -/
theorem cov432 : Cover gdata (-3264) (-3200) (14336) (16384) := by
  ballooning_cover "Q:cn08_32,cn08_35,cn08_33,cn08_36"

/-- Kernel-checked box `[-3200, -3136]/NT × [12288, 14336]/NS`. -/
theorem cov433 : Cover gdata (-3200) (-3136) (12288) (14336) := by
  ballooning_cover "Q:cn08_34,cn08_37,cn08_35,cn08_38"

/-- Kernel-checked box `[-3200, -3136]/NT × [14336, 16384]/NS`. -/
theorem cov434 : Cover gdata (-3200) (-3136) (14336) (16384) := by
  ballooning_cover "Q:cn08_35,cn08_38,cn08_36,cn08_39"

/-- Kernel-checked box `[-3136, -3072]/NT × [12288, 14336]/NS`. -/
theorem cov435 : Cover gdata (-3136) (-3072) (12288) (14336) := by
  ballooning_cover "Q:cn08_37,cn08_40,cn08_38,cn08_41"

/-- Kernel-checked box `[-3136, -3072]/NT × [14336, 16384]/NS`. -/
theorem cov436 : Cover gdata (-3136) (-3072) (14336) (16384) := by
  ballooning_cover "Q:cn08_38,cn08_41,cn08_39,cn08_42"

/-- Kernel-checked box `[-3072, -3008]/NT × [12288, 14336]/NS`. -/
theorem cov437 : Cover gdata (-3072) (-3008) (12288) (14336) := by
  ballooning_cover "Q:cn08_40,cn08_43,cn08_41,cn08_44"

/-- Kernel-checked box `[-3072, -3008]/NT × [14336, 16384]/NS`. -/
theorem cov438 : Cover gdata (-3072) (-3008) (14336) (16384) := by
  ballooning_cover "Q:cn08_41,cn08_44,cn08_42,cn08_45"

/-- Kernel-checked box `[-3008, -2944]/NT × [12288, 14336]/NS`. -/
theorem cov439 : Cover gdata (-3008) (-2944) (12288) (14336) := by
  ballooning_cover "Q:cn08_43,cn08_46,cn08_44,cn08_47"

/-- Kernel-checked box `[-3008, -2944]/NT × [14336, 16384]/NS`. -/
theorem cov440 : Cover gdata (-3008) (-2944) (14336) (16384) := by
  ballooning_cover "Q:cn08_44,cn08_47,cn08_45,cn08_48"

/-- Kernel-checked box `[-2944, -2880]/NT × [12288, 14336]/NS`. -/
theorem cov441 : Cover gdata (-2944) (-2880) (12288) (14336) := by
  ballooning_cover "Q:cn08_46,cn08_49,cn08_47,cn08_50"

/-- Kernel-checked box `[-2880, -2816]/NT × [12288, 14336]/NS`. -/
theorem cov442 : Cover gdata (-2880) (-2816) (12288) (14336) := by
  ballooning_cover "Q:cn08_49,cn08_51,cn08_50,cn08_52"

/-- Kernel-checked box `[-2944, -2816]/NT × [14336, 15360]/NS`. -/
theorem cov443 : Cover gdata (-2944) (-2816) (14336) (15360) := by
  ballooning_cover "Q:cn08_47,cn08_52,cn08_53,cn08_54"

/-- Kernel-checked box `[-2944, -2816]/NT × [15360, 16384]/NS`. -/
theorem cov444 : Cover gdata (-2944) (-2816) (15360) (16384) := by
  ballooning_cover "Q:cn08_53,cn08_54,cn08_48,cn08_55"

/-- Kernel-checked box `[-2816, -2752]/NT × [12288, 14336]/NS`. -/
theorem cov445 : Cover gdata (-2816) (-2752) (12288) (14336) := by
  ballooning_cover "Q:cn08_51,cn08_56,cn08_52,cn08_57"

/-- Kernel-checked box `[-2752, -2688]/NT × [12288, 14336]/NS`. -/
theorem cov446 : Cover gdata (-2752) (-2688) (12288) (14336) := by
  ballooning_cover "Q:cn08_56,cn08_58,cn08_57,cn08_59"

/-- Kernel-checked box `[-2816, -2688]/NT × [14336, 15360]/NS`. -/
theorem cov447 : Cover gdata (-2816) (-2688) (14336) (15360) := by
  ballooning_cover "Q:cn08_52,cn08_59,cn08_54,cn08_60"

/-- Kernel-checked box `[-2816, -2688]/NT × [15360, 16384]/NS`. -/
theorem cov448 : Cover gdata (-2816) (-2688) (15360) (16384) := by
  ballooning_cover "Q:cn08_54,cn08_60,cn08_55,cn08_61"

/-- Kernel-checked box `[-2688, -2624]/NT × [12288, 14336]/NS`. -/
theorem cov449 : Cover gdata (-2688) (-2624) (12288) (14336) := by
  ballooning_cover "Q:cn08_58,cn08_62,cn08_59,cn08_63"

/-- Kernel-checked box `[-2624, -2560]/NT × [12288, 14336]/NS`. -/
theorem cov450 : Cover gdata (-2624) (-2560) (12288) (14336) := by
  ballooning_cover "Q:cn08_62,cn08_64,cn08_63,cn08_65"

/-- Kernel-checked box `[-2688, -2560]/NT × [14336, 15360]/NS`. -/
theorem cov451 : Cover gdata (-2688) (-2560) (14336) (15360) := by
  ballooning_cover "Q:cn08_59,cn08_65,cn08_60,cn08_66"

/-- Kernel-checked box `[-2688, -2560]/NT × [15360, 16384]/NS`. -/
theorem cov452 : Cover gdata (-2688) (-2560) (15360) (16384) := by
  ballooning_cover "Q:cn08_60,cn08_66,cn08_61,cn08_67"

/-- Kernel-checked box `[-2560, -2496]/NT × [12288, 14336]/NS`. -/
theorem cov453 : Cover gdata (-2560) (-2496) (12288) (14336) := by
  ballooning_cover "Q:cn08_64,cn08_68,cn08_65,cn08_69"

/-- Kernel-checked box `[-2560, -2496]/NT × [14336, 16384]/NS`. -/
theorem cov454 : Cover gdata (-2560) (-2496) (14336) (16384) := by
  ballooning_cover "Q:cn08_65,cn08_69,cn08_67,cn08_70"

/-- Kernel-checked box `[-2496, -2432]/NT × [12288, 14336]/NS`. -/
theorem cov455 : Cover gdata (-2496) (-2432) (12288) (14336) := by
  ballooning_cover "Q:cn08_68,cn08_71,cn08_69,cn08_72"

/-- Kernel-checked box `[-2496, -2432]/NT × [14336, 16384]/NS`. -/
theorem cov456 : Cover gdata (-2496) (-2432) (14336) (16384) := by
  ballooning_cover "Q:cn08_69,cn08_72,cn08_70,cn08_73"

/-- Kernel-checked box `[-2432, -2368]/NT × [12288, 14336]/NS`. -/
theorem cov457 : Cover gdata (-2432) (-2368) (12288) (14336) := by
  ballooning_cover "Q:cn08_71,cn08_74,cn08_72,cn08_75"

/-- Kernel-checked box `[-2432, -2368]/NT × [14336, 16384]/NS`. -/
theorem cov458 : Cover gdata (-2432) (-2368) (14336) (16384) := by
  ballooning_cover "Q:cn08_72,cn08_75,cn08_73,cn08_76"

/-- Kernel-checked box `[-2368, -2304]/NT × [12288, 14336]/NS`. -/
theorem cov459 : Cover gdata (-2368) (-2304) (12288) (14336) := by
  ballooning_cover "Q:cn08_74,cn08_77,cn08_75,cn08_78"

/-- Kernel-checked box `[-2368, -2304]/NT × [14336, 16384]/NS`. -/
theorem cov460 : Cover gdata (-2368) (-2304) (14336) (16384) := by
  ballooning_cover "Q:cn08_75,cn08_78,cn08_76,cn08_79"

/-- Kernel-checked box `[-2304, -2240]/NT × [12288, 14336]/NS`. -/
theorem cov461 : Cover gdata (-2304) (-2240) (12288) (14336) := by
  ballooning_cover "Q:cn08_77,cn08_80,cn08_78,cn08_81"

/-- Kernel-checked box `[-2304, -2240]/NT × [14336, 16384]/NS`. -/
theorem cov462 : Cover gdata (-2304) (-2240) (14336) (16384) := by
  ballooning_cover "Q:cn08_78,cn08_81,cn08_79,cn08_82"

/-- Kernel-checked box `[-2240, -2176]/NT × [12288, 14336]/NS`. -/
theorem cov463 : Cover gdata (-2240) (-2176) (12288) (14336) := by
  ballooning_cover "Q:cn08_80,cn08_83,cn08_81,cn08_84"

/-- Kernel-checked box `[-2240, -2176]/NT × [14336, 16384]/NS`. -/
theorem cov464 : Cover gdata (-2240) (-2176) (14336) (16384) := by
  ballooning_cover "Q:cn08_81,cn08_84,cn08_82,cn08_85"

end PlasmaLean.Design.SolovevBallooning
