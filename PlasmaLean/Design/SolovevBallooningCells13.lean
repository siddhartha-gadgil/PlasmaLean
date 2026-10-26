/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 13

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

/-- Kernel-checked corner test at `(-2944/NT, 23040/NS)`. -/
theorem cn13_0 : cornerOK gdata (-2944) (23040)
    [5700867213, 1649844032, 2408305480, 490465183, 372727696, 58216789, 10679901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 23040/NS)`. -/
theorem cn13_1 : cornerOK gdata (-2816) (23040)
    [5700867213, 1707982248, 2408305480, 501820955, 372727696, 58754404, 10679901] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 24320/NS)`. -/
theorem cn13_2 : cornerOK gdata (-2944) (24320)
    [7958362634, 2215729551, 3301566244, 633207673, 496169547, 75452555, 12476277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 24320/NS)`. -/
theorem cn13_3 : cornerOK gdata (-2816) (24320)
    [7958362634, 2279437660, 3301566244, 643493395, 496169547, 75628701, 12476277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 25600/NS)`. -/
theorem cn13_4 : cornerOK gdata (-2944) (25600)
    [7958362634, 2215729551, 3301566244, 633207673, 496169547, 75452555, 12476277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 25600/NS)`. -/
theorem cn13_5 : cornerOK gdata (-2816) (25600)
    [7958362634, 2279437660, 3301566244, 643493395, 496169547, 75628701, 12476277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 20480/NS)`. -/
theorem cn13_6 : cornerOK gdata (-2816) (20480)
    [2992682602, 995137986, 1334938578, 313828153, 217720838, 36491921, 7601252] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 20480/NS)`. -/
theorem cn13_7 : cornerOK gdata (-2688) (20480)
    [2992682602, 1018003305, 1334938578, 317949813, 217720838, 36491921, 7601252] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 21760/NS)`. -/
theorem cn13_8 : cornerOK gdata (-2816) (21760)
    [4051566621, 1296198989, 1766948619, 395178794, 279325339, 46100323, 8733105] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 21760/NS)`. -/
theorem cn13_9 : cornerOK gdata (-2688) (21760)
    [4051566621, 1319637993, 1766948619, 398000297, 279325339, 46100323, 8733105] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 23040/NS)`. -/
theorem cn13_10 : cornerOK gdata (-2688) (23040)
    [5551365048, 1729400733, 2371482918, 502096142, 363982749, 58754404, 10100968] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 24320/NS)`. -/
theorem cn13_11 : cornerOK gdata (-2688) (24320)
    [7708637184, 2293688567, 3235783349, 643493395, 482476135, 75628701, 11767090] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 25600/NS)`. -/
theorem cn13_12 : cornerOK gdata (-2688) (25600)
    [7708637184, 2293688567, 3235783349, 643493395, 482476135, 75628701, 11767090] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 20480/NS)`. -/
theorem cn13_13 : cornerOK gdata (-2560) (20480)
    [2895426604, 1018149972, 1311723053, 317949813, 211575038, 36441577, 7167858] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 21760/NS)`. -/
theorem cn13_14 : cornerOK gdata (-2560) (21760)
    [3899676702, 1319637993, 1728860969, 398000297, 270340511, 45739850, 8220637] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 23040/NS)`. -/
theorem cn13_15 : cornerOK gdata (-2560) (23040)
    [5312067114, 1729400733, 2308605165, 502096142, 350627201, 57887889, 9476989] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 24320/NS)`. -/
theorem cn13_16 : cornerOK gdata (-2560) (24320)
    [7326945342, 2293688567, 3127321879, 639157459, 462290725, 73942428, 11000139] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 25600/NS)`. -/
theorem cn13_17 : cornerOK gdata (-2560) (25600)
    [7326945342, 2293688567, 3127321879, 639157459, 462290725, 73942428, 11000139] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 20480/NS)`. -/
theorem cn13_18 : cornerOK gdata (-2432) (20480)
    [2756487618, 1018149972, 1271715374, 315468536, 203069684, 35596766, 6718187] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 21760/NS)`. -/
theorem cn13_19 : cornerOK gdata (-2432) (21760)
    [3690820910, 1312924776, 1667648045, 392398670, 258213517, 44363877, 7679504] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 23040/NS)`. -/
theorem cn13_20 : cornerOK gdata (-2432) (23040)
    [4995392111, 1710316429, 2213599601, 491509463, 332999960, 55710136, 8823378] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 24320/NS)`. -/
theorem cn13_21 : cornerOK gdata (-2432) (24320)
    [6849188135, 2253904884, 2980966557, 620705739, 436413124, 70553986, 10190705] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 25600/NS)`. -/
theorem cn13_22 : cornerOK gdata (-2432) (25600)
    [6849188135, 2253904884, 2980966557, 620705739, 436413124, 70553986, 10190705] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 20480/NS)`. -/
theorem cn13_23 : cornerOK gdata (-2304) (20480)
    [2589402464, 997110989, 1217365933, 306714800, 192671381, 34032570, 6250547] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 21760/NS)`. -/
theorem cn13_24 : cornerOK gdata (-2304) (21760)
    [3446946822, 1279001659, 1588897293, 379195172, 243720094, 42122496, 7118251] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 23040/NS)`. -/
theorem cn13_25 : cornerOK gdata (-2304) (23040)
    [4632217873, 1655756581, 2096049822, 471766682, 312267206, 52503747, 8139648] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 24320/NS)`. -/
theorem cn13_26 : cornerOK gdata (-2304) (24320)
    [6290601416, 2165108467, 2797729761, 591257469, 405780345, 65981069, 9350905] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 25600/NS)`. -/
theorem cn13_27 : cornerOK gdata (-2304) (25600)
    [6290601416, 2165108467, 2797729761, 591257469, 405780345, 65981069, 9350905] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 20480/NS)`. -/
theorem cn13_28 : cornerOK gdata (-2240) (20480)
    [973798910, 352225410, 430007326, 94907456, 70813485, 10385083, 2337373] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 21760/NS)`. -/
theorem cn13_29 : cornerOK gdata (-2240) (21760)
    [1256431310, 440964369, 545982746, 114704717, 87111716, 12551932, 2593119] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 23040/NS)`. -/
theorem cn13_30 : cornerOK gdata (-2240) (23040)
    [1633868162, 557000911, 699539876, 139194136, 108382529, 15268283, 2887055] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 24320/NS)`. -/
theorem cn13_31 : cornerOK gdata (-2240) (24320)
    [2143452455, 710286400, 905205598, 169766502, 136519034, 18693471, 3225112] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2240/NT, 25600/NS)`. -/
theorem cn13_32 : cornerOK gdata (-2240) (25600)
    [2143452455, 710286400, 905205598, 169766502, 136519034, 18693471, 3225112] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 20480/NS)`. -/
theorem cn13_33 : cornerOK gdata (-2176) (20480)
    [913903485, 337592817, 407477856, 90576383, 66692321, 9802521, 2188736] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 21760/NS)`. -/
theorem cn13_34 : cornerOK gdata (-2176) (21760)
    [1172754695, 420866258, 515380328, 109057989, 81718117, 11803137, 2421540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 23040/NS)`. -/
theorem cn13_35 : cornerOK gdata (-2176) (23040)
    [1516179013, 529422057, 657314349, 131987555, 101215571, 14338185, 2687084] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 24320/NS)`. -/
theorem cn13_36 : cornerOK gdata (-2176) (24320)
    [1977324625, 672080329, 846536259, 160541296, 126856343, 17506391, 2992495] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 25600/NS)`. -/
theorem cn13_37 : cornerOK gdata (-2176) (25600)
    [1977324625, 672080329, 846536259, 160541296, 126856343, 17506391, 2992495] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 20480/NS)`. -/
theorem cn13_38 : cornerOK gdata (-2112) (20480)
    [853634870, 321882240, 384351935, 86248164, 62521896, 9400181, 2043650] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 21760/NS)`. -/
theorem cn13_39 : cornerOK gdata (-2112) (21760)
    [1089651402, 399555196, 483974805, 103544656, 76273683, 11176865, 2254041] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 23040/NS)`. -/
theorem cn13_40 : cornerOK gdata (-2112) (23040)
    [1401769510, 500137436, 614710736, 124795957, 94062406, 13429100, 2494149] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 24320/NS)`. -/
theorem cn13_41 : cornerOK gdata (-2112) (24320)
    [1816556095, 630820599, 787231664, 151001317, 117218644, 16310109, 2767277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 25600/NS)`. -/
theorem cn13_42 : cornerOK gdata (-2112) (25600)
    [1816556095, 630820599, 787231664, 151001317, 117218644, 16310109, 2767277] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 20480/NS)`. -/
theorem cn13_43 : cornerOK gdata (-2048) (20480)
    [793415510, 305066088, 360878903, 81866457, 58354100, 8997143, 1902906] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 21760/NS)`. -/
theorem cn13_44 : cornerOK gdata (-2048) (21760)
    [1007344536, 376647638, 452373329, 97851366, 70858191, 10650077, 2093072] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 23040/NS)`. -/
theorem cn13_45 : cornerOK gdata (-2048) (23040)
    [1288524607, 468692039, 571701454, 117376606, 86936082, 12691904, 2307997] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 24320/NS)`. -/
theorem cn13_46 : cornerOK gdata (-2048) (24320)
    [1660617999, 587710648, 728656020, 141360474, 107793490, 15229749, 2553365] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 25600/NS)`. -/
theorem cn13_47 : cornerOK gdata (-2048) (25600)
    [1660617999, 587710648, 728656020, 141360474, 107793490, 15229749, 2553365] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 20480/NS)`. -/
theorem cn13_48 : cornerOK gdata (-1984) (20480)
    [733756449, 286996152, 337205343, 77330158, 54211836, 8578782, 1766737] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 21760/NS)`. -/
theorem cn13_49 : cornerOK gdata (-1984) (21760)
    [926640764, 352410913, 420786344, 92041354, 65514597, 10107902, 1937581] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 23040/NS)`. -/
theorem cn13_50 : cornerOK gdata (-1984) (23040)
    [1178233567, 435783113, 528985630, 109867970, 79937876, 11983138, 2129439] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 24320/NS)`. -/
theorem cn13_51 : cornerOK gdata (-1984) (24320)
    [1509599306, 543101794, 670823101, 131709219, 98610284, 14301739, 2352115] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 25600/NS)`. -/
theorem cn13_52 : cornerOK gdata (-1984) (25600)
    [1509599306, 543101794, 670823101, 131709219, 98610284, 14301739, 2352115] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 20480/NS)`. -/
theorem cn13_53 : cornerOK gdata (-1920) (20480)
    [674952373, 267904757, 313442280, 72708843, 50110543, 8151226, 1635648] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 21760/NS)`. -/
theorem cn13_54 : cornerOK gdata (-1920) (21760)
    [847972570, 327158652, 389412852, 86177685, 60269412, 9559859, 1788797] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 23040/NS)`. -/
theorem cn13_55 : cornerOK gdata (-1920) (23040)
    [1072217205, 402100592, 487203156, 102401916, 73170370, 11275173, 1961969] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 24320/NS)`. -/
theorem cn13_56 : cornerOK gdata (-1920) (24320)
    [1364616504, 497526276, 614189880, 122106909, 89715361, 13377007, 2161800] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 25600/NS)`. -/
theorem cn13_57 : cornerOK gdata (-1920) (25600)
    [1364616504, 497526276, 614189880, 122106909, 89715361, 13377007, 2161800] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 20480/NS)`. -/
theorem cn13_58 : cornerOK gdata (-1856) (20480)
    [617773188, 248979269, 290118928, 68061692, 46094147, 7716786, 1510109] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 21760/NS)`. -/
theorem cn13_59 : cornerOK gdata (-1856) (21760)
    [772146714, 301180695, 358549628, 80298154, 55167117, 9005839, 1646362] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 23040/NS)`. -/
theorem cn13_60 : cornerOK gdata (-1856) (23040)
    [970238804, 367665117, 446214030, 94957183, 66619550, 10566084, 1804673] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 24320/NS)`. -/
theorem cn13_61 : cornerOK gdata (-1856) (24320)
    [1227251902, 451869217, 559432484, 112667581, 81203395, 12463430, 1982601] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 25600/NS)`. -/
theorem cn13_62 : cornerOK gdata (-1856) (25600)
    [1227251902, 451869217, 559432484, 112667581, 81203395, 12463430, 1982601] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 20480/NS)`. -/
theorem cn13_63 : cornerOK gdata (-1792) (20480)
    [563146907, 230543040, 267669242, 63528946, 42241449, 7282202, 1390486] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 21760/NS)`. -/
theorem cn13_64 : cornerOK gdata (-1792) (21760)
    [699451973, 275328699, 328597176, 74566646, 50288652, 8456308, 1514893] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 23040/NS)`. -/
theorem cn13_65 : cornerOK gdata (-1792) (23040)
    [874022522, 334088102, 406970177, 87804290, 60413703, 9868549, 1656658] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 24320/NS)`. -/
theorem cn13_66 : cornerOK gdata (-1792) (24320)
    [1097891095, 407610367, 507041988, 103626768, 73148593, 11570812, 1814466] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 25600/NS)`. -/
theorem cn13_67 : cornerOK gdata (-1792) (25600)
    [1097891095, 407610367, 507041988, 103626768, 73148593, 11570812, 1814466] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 20480/NS)`. -/
theorem cn13_68 : cornerOK gdata (-1728) (20480)
    [510504155, 211785672, 245635344, 59150737, 38517743, 6846799, 1277130] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 21760/NS)`. -/
theorem cn13_69 : cornerOK gdata (-1728) (21760)
    [510504155, 211785672, 245635344, 59150737, 38517743, 6846799, 1277130] = true := by
  bl_cert

/-- Kernel-checked box `[-2944, -2816]/NT × [23040, 24320]/NS`. -/
theorem cov671 : Cover gdata (-2944) (-2816) (23040) (24320) := by
  ballooning_box "Q:cn13_0,cn13_1,cn13_2,cn13_3"

/-- Kernel-checked box `[-2944, -2816]/NT × [24320, 25600]/NS`. -/
theorem cov672 : Cover gdata (-2944) (-2816) (24320) (25600) := by
  ballooning_box "Q:cn13_2,cn13_3,cn13_4,cn13_5"

/-- Kernel-checked box `[-2816, -2688]/NT × [20480, 21760]/NS`. -/
theorem cov673 : Cover gdata (-2816) (-2688) (20480) (21760) := by
  ballooning_box "Q:cn13_6,cn13_7,cn13_8,cn13_9"

/-- Kernel-checked box `[-2816, -2688]/NT × [21760, 23040]/NS`. -/
theorem cov674 : Cover gdata (-2816) (-2688) (21760) (23040) := by
  ballooning_box "Q:cn13_8,cn13_9,cn13_1,cn13_10"

/-- Kernel-checked box `[-2816, -2688]/NT × [23040, 24320]/NS`. -/
theorem cov675 : Cover gdata (-2816) (-2688) (23040) (24320) := by
  ballooning_box "Q:cn13_1,cn13_10,cn13_3,cn13_11"

/-- Kernel-checked box `[-2816, -2688]/NT × [24320, 25600]/NS`. -/
theorem cov676 : Cover gdata (-2816) (-2688) (24320) (25600) := by
  ballooning_box "Q:cn13_3,cn13_11,cn13_5,cn13_12"

/-- Kernel-checked box `[-2688, -2560]/NT × [20480, 21760]/NS`. -/
theorem cov677 : Cover gdata (-2688) (-2560) (20480) (21760) := by
  ballooning_box "Q:cn13_7,cn13_13,cn13_9,cn13_14"

/-- Kernel-checked box `[-2688, -2560]/NT × [21760, 23040]/NS`. -/
theorem cov678 : Cover gdata (-2688) (-2560) (21760) (23040) := by
  ballooning_box "Q:cn13_9,cn13_14,cn13_10,cn13_15"

/-- Kernel-checked box `[-2688, -2560]/NT × [23040, 24320]/NS`. -/
theorem cov679 : Cover gdata (-2688) (-2560) (23040) (24320) := by
  ballooning_box "Q:cn13_10,cn13_15,cn13_11,cn13_16"

/-- Kernel-checked box `[-2688, -2560]/NT × [24320, 25600]/NS`. -/
theorem cov680 : Cover gdata (-2688) (-2560) (24320) (25600) := by
  ballooning_box "Q:cn13_11,cn13_16,cn13_12,cn13_17"

/-- Kernel-checked box `[-2560, -2432]/NT × [20480, 21760]/NS`. -/
theorem cov681 : Cover gdata (-2560) (-2432) (20480) (21760) := by
  ballooning_box "Q:cn13_13,cn13_18,cn13_14,cn13_19"

/-- Kernel-checked box `[-2560, -2432]/NT × [21760, 23040]/NS`. -/
theorem cov682 : Cover gdata (-2560) (-2432) (21760) (23040) := by
  ballooning_box "Q:cn13_14,cn13_19,cn13_15,cn13_20"

/-- Kernel-checked box `[-2560, -2432]/NT × [23040, 24320]/NS`. -/
theorem cov683 : Cover gdata (-2560) (-2432) (23040) (24320) := by
  ballooning_box "Q:cn13_15,cn13_20,cn13_16,cn13_21"

/-- Kernel-checked box `[-2560, -2432]/NT × [24320, 25600]/NS`. -/
theorem cov684 : Cover gdata (-2560) (-2432) (24320) (25600) := by
  ballooning_box "Q:cn13_16,cn13_21,cn13_17,cn13_22"

/-- Kernel-checked box `[-2432, -2304]/NT × [20480, 21760]/NS`. -/
theorem cov685 : Cover gdata (-2432) (-2304) (20480) (21760) := by
  ballooning_box "Q:cn13_18,cn13_23,cn13_19,cn13_24"

/-- Kernel-checked box `[-2432, -2304]/NT × [21760, 23040]/NS`. -/
theorem cov686 : Cover gdata (-2432) (-2304) (21760) (23040) := by
  ballooning_box "Q:cn13_19,cn13_24,cn13_20,cn13_25"

/-- Kernel-checked box `[-2432, -2304]/NT × [23040, 24320]/NS`. -/
theorem cov687 : Cover gdata (-2432) (-2304) (23040) (24320) := by
  ballooning_box "Q:cn13_20,cn13_25,cn13_21,cn13_26"

/-- Kernel-checked box `[-2432, -2304]/NT × [24320, 25600]/NS`. -/
theorem cov688 : Cover gdata (-2432) (-2304) (24320) (25600) := by
  ballooning_box "Q:cn13_21,cn13_26,cn13_22,cn13_27"

/-- Kernel-checked box `[-2304, -2240]/NT × [20480, 21760]/NS`. -/
theorem cov689 : Cover gdata (-2304) (-2240) (20480) (21760) := by
  ballooning_box "Q:cn13_23,cn13_28,cn13_24,cn13_29"

/-- Kernel-checked box `[-2304, -2240]/NT × [21760, 23040]/NS`. -/
theorem cov690 : Cover gdata (-2304) (-2240) (21760) (23040) := by
  ballooning_box "Q:cn13_24,cn13_29,cn13_25,cn13_30"

/-- Kernel-checked box `[-2304, -2240]/NT × [23040, 24320]/NS`. -/
theorem cov691 : Cover gdata (-2304) (-2240) (23040) (24320) := by
  ballooning_box "Q:cn13_25,cn13_30,cn13_26,cn13_31"

/-- Kernel-checked box `[-2304, -2240]/NT × [24320, 25600]/NS`. -/
theorem cov692 : Cover gdata (-2304) (-2240) (24320) (25600) := by
  ballooning_box "Q:cn13_26,cn13_31,cn13_27,cn13_32"

/-- Kernel-checked box `[-2240, -2176]/NT × [20480, 21760]/NS`. -/
theorem cov693 : Cover gdata (-2240) (-2176) (20480) (21760) := by
  ballooning_box "Q:cn13_28,cn13_33,cn13_29,cn13_34"

/-- Kernel-checked box `[-2240, -2176]/NT × [21760, 23040]/NS`. -/
theorem cov694 : Cover gdata (-2240) (-2176) (21760) (23040) := by
  ballooning_box "Q:cn13_29,cn13_34,cn13_30,cn13_35"

/-- Kernel-checked box `[-2240, -2176]/NT × [23040, 24320]/NS`. -/
theorem cov695 : Cover gdata (-2240) (-2176) (23040) (24320) := by
  ballooning_box "Q:cn13_30,cn13_35,cn13_31,cn13_36"

/-- Kernel-checked box `[-2240, -2176]/NT × [24320, 25600]/NS`. -/
theorem cov696 : Cover gdata (-2240) (-2176) (24320) (25600) := by
  ballooning_box "Q:cn13_31,cn13_36,cn13_32,cn13_37"

/-- Kernel-checked box `[-2176, -2112]/NT × [20480, 21760]/NS`. -/
theorem cov697 : Cover gdata (-2176) (-2112) (20480) (21760) := by
  ballooning_box "Q:cn13_33,cn13_38,cn13_34,cn13_39"

/-- Kernel-checked box `[-2176, -2112]/NT × [21760, 23040]/NS`. -/
theorem cov698 : Cover gdata (-2176) (-2112) (21760) (23040) := by
  ballooning_box "Q:cn13_34,cn13_39,cn13_35,cn13_40"

/-- Kernel-checked box `[-2176, -2112]/NT × [23040, 24320]/NS`. -/
theorem cov699 : Cover gdata (-2176) (-2112) (23040) (24320) := by
  ballooning_box "Q:cn13_35,cn13_40,cn13_36,cn13_41"

/-- Kernel-checked box `[-2176, -2112]/NT × [24320, 25600]/NS`. -/
theorem cov700 : Cover gdata (-2176) (-2112) (24320) (25600) := by
  ballooning_box "Q:cn13_36,cn13_41,cn13_37,cn13_42"

/-- Kernel-checked box `[-2112, -2048]/NT × [20480, 21760]/NS`. -/
theorem cov701 : Cover gdata (-2112) (-2048) (20480) (21760) := by
  ballooning_box "Q:cn13_38,cn13_43,cn13_39,cn13_44"

/-- Kernel-checked box `[-2112, -2048]/NT × [21760, 23040]/NS`. -/
theorem cov702 : Cover gdata (-2112) (-2048) (21760) (23040) := by
  ballooning_box "Q:cn13_39,cn13_44,cn13_40,cn13_45"

/-- Kernel-checked box `[-2112, -2048]/NT × [23040, 24320]/NS`. -/
theorem cov703 : Cover gdata (-2112) (-2048) (23040) (24320) := by
  ballooning_box "Q:cn13_40,cn13_45,cn13_41,cn13_46"

/-- Kernel-checked box `[-2112, -2048]/NT × [24320, 25600]/NS`. -/
theorem cov704 : Cover gdata (-2112) (-2048) (24320) (25600) := by
  ballooning_box "Q:cn13_41,cn13_46,cn13_42,cn13_47"

/-- Kernel-checked box `[-2048, -1984]/NT × [20480, 21760]/NS`. -/
theorem cov705 : Cover gdata (-2048) (-1984) (20480) (21760) := by
  ballooning_box "Q:cn13_43,cn13_48,cn13_44,cn13_49"

/-- Kernel-checked box `[-2048, -1984]/NT × [21760, 23040]/NS`. -/
theorem cov706 : Cover gdata (-2048) (-1984) (21760) (23040) := by
  ballooning_box "Q:cn13_44,cn13_49,cn13_45,cn13_50"

/-- Kernel-checked box `[-2048, -1984]/NT × [23040, 24320]/NS`. -/
theorem cov707 : Cover gdata (-2048) (-1984) (23040) (24320) := by
  ballooning_box "Q:cn13_45,cn13_50,cn13_46,cn13_51"

/-- Kernel-checked box `[-2048, -1984]/NT × [24320, 25600]/NS`. -/
theorem cov708 : Cover gdata (-2048) (-1984) (24320) (25600) := by
  ballooning_box "Q:cn13_46,cn13_51,cn13_47,cn13_52"

/-- Kernel-checked box `[-1984, -1920]/NT × [20480, 21760]/NS`. -/
theorem cov709 : Cover gdata (-1984) (-1920) (20480) (21760) := by
  ballooning_box "Q:cn13_48,cn13_53,cn13_49,cn13_54"

/-- Kernel-checked box `[-1984, -1920]/NT × [21760, 23040]/NS`. -/
theorem cov710 : Cover gdata (-1984) (-1920) (21760) (23040) := by
  ballooning_box "Q:cn13_49,cn13_54,cn13_50,cn13_55"

/-- Kernel-checked box `[-1984, -1920]/NT × [23040, 24320]/NS`. -/
theorem cov711 : Cover gdata (-1984) (-1920) (23040) (24320) := by
  ballooning_box "Q:cn13_50,cn13_55,cn13_51,cn13_56"

/-- Kernel-checked box `[-1984, -1920]/NT × [24320, 25600]/NS`. -/
theorem cov712 : Cover gdata (-1984) (-1920) (24320) (25600) := by
  ballooning_box "Q:cn13_51,cn13_56,cn13_52,cn13_57"

/-- Kernel-checked box `[-1920, -1856]/NT × [20480, 21760]/NS`. -/
theorem cov713 : Cover gdata (-1920) (-1856) (20480) (21760) := by
  ballooning_box "Q:cn13_53,cn13_58,cn13_54,cn13_59"

/-- Kernel-checked box `[-1920, -1856]/NT × [21760, 23040]/NS`. -/
theorem cov714 : Cover gdata (-1920) (-1856) (21760) (23040) := by
  ballooning_box "Q:cn13_54,cn13_59,cn13_55,cn13_60"

/-- Kernel-checked box `[-1920, -1856]/NT × [23040, 24320]/NS`. -/
theorem cov715 : Cover gdata (-1920) (-1856) (23040) (24320) := by
  ballooning_box "Q:cn13_55,cn13_60,cn13_56,cn13_61"

/-- Kernel-checked box `[-1920, -1856]/NT × [24320, 25600]/NS`. -/
theorem cov716 : Cover gdata (-1920) (-1856) (24320) (25600) := by
  ballooning_box "Q:cn13_56,cn13_61,cn13_57,cn13_62"

/-- Kernel-checked box `[-1856, -1792]/NT × [20480, 21760]/NS`. -/
theorem cov717 : Cover gdata (-1856) (-1792) (20480) (21760) := by
  ballooning_box "Q:cn13_58,cn13_63,cn13_59,cn13_64"

/-- Kernel-checked box `[-1856, -1792]/NT × [21760, 23040]/NS`. -/
theorem cov718 : Cover gdata (-1856) (-1792) (21760) (23040) := by
  ballooning_box "Q:cn13_59,cn13_64,cn13_60,cn13_65"

/-- Kernel-checked box `[-1856, -1792]/NT × [23040, 24320]/NS`. -/
theorem cov719 : Cover gdata (-1856) (-1792) (23040) (24320) := by
  ballooning_box "Q:cn13_60,cn13_65,cn13_61,cn13_66"

/-- Kernel-checked box `[-1856, -1792]/NT × [24320, 25600]/NS`. -/
theorem cov720 : Cover gdata (-1856) (-1792) (24320) (25600) := by
  ballooning_box "Q:cn13_61,cn13_66,cn13_62,cn13_67"

/-- Kernel-checked box `[-1792, -1728]/NT × [20480, 21760]/NS`. -/
theorem cov721 : Cover gdata (-1792) (-1728) (20480) (21760) := by
  ballooning_box "Q:cn13_63,cn13_68,cn13_64,cn13_69"

end PlasmaLean.Design.SolovevBallooning
