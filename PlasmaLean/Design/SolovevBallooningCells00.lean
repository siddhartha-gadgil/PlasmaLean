/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningBoxCert

/-!
# Ballooning certificate: kernel-checked cells, part 0

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

/-- Kernel-checked corner test at `(-4096/NT, 512/NS)`. -/
theorem cn00_0 : cornerOK gdata (-4096) (512)
    [22503277, 3312845, 17718603, 1656238, 6867754, 214684, 717811] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 512/NS)`. -/
theorem cn00_1 : cornerOK gdata (-3968) (512)
    [23006570, 4623389, 18187976, 2371059, 6975854, 290608, 726028] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-4096/NT, 1024/NS)`. -/
theorem cn00_2 : cornerOK gdata (-4096) (1024)
    [7689431, 1593226, 6145967, 782584, 2111647, 102286, 211665] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3968/NT, 1024/NS)`. -/
theorem cn00_3 : cornerOK gdata (-3968) (1024)
    [8007759, 2016566, 6426770, 1009587, 2179581, 125456, 217067] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 512/NS)`. -/
theorem cn00_4 : cornerOK gdata (-3840) (512)
    [23533846, 5996876, 18670362, 3107505, 7064204, 369455, 731453] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3840/NT, 1024/NS)`. -/
theorem cn00_5 : cornerOK gdata (-3840) (1024)
    [8343102, 2509438, 6715726, 1245611, 2244845, 151534, 221943] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3712/NT, 512/NS)`. -/
theorem cn00_6 : cornerOK gdata (-3712) (512)
    [24072532, 7405473, 19151141, 3856003, 7126970, 450618, 733460] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3712/NT, 1024/NS)`. -/
theorem cn00_7 : cornerOK gdata (-3712) (1024)
    [8697051, 3023718, 7012798, 1488024, 2306530, 181335, 226189] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 512/NS)`. -/
theorem cn00_8 : cornerOK gdata (-3584) (512)
    [24613166, 8831104, 19618950, 4606984, 7161507, 531946, 733460] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3584/NT, 1024/NS)`. -/
theorem cn00_9 : cornerOK gdata (-3584) (1024)
    [9069306, 3553082, 7315824, 1733392, 2362799, 211820, 229620] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3456/NT, 512/NS)`. -/
theorem cn00_10 : cornerOK gdata (-3456) (512)
    [25153764, 10253819, 20068921, 5347305, 7165994, 612109, 731754] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3456/NT, 1024/NS)`. -/
theorem cn00_11 : cornerOK gdata (-3456) (1024)
    [9458037, 4090750, 7621848, 1983545, 2413565, 242583, 232213] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 512/NS)`. -/
theorem cn00_12 : cornerOK gdata (-3328) (512)
    [25692134, 11795332, 20500835, 6131979, 7165994, 697921, 726138] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3328/NT, 1024/NS)`. -/
theorem cn00_13 : cornerOK gdata (-3328) (1024)
    [9862464, 4796889, 7933746, 2309851, 2458618, 282583, 233840] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 512/NS)`. -/
theorem cn00_14 : cornerOK gdata (-3200) (512)
    [26213773, 13333035, 20898890, 6899608, 7139838, 782201, 716498] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3200/NT, 1024/NS)`. -/
theorem cn00_15 : cornerOK gdata (-3200) (1024)
    [10277627, 5532433, 8242758, 2646865, 2495477, 324070, 234353] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 512/NS)`. -/
theorem cn00_16 : cornerOK gdata (-3072) (512)
    [26708326, 14809288, 21249357, 7619692, 7077752, 861394, 702399] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-3072/NT, 1024/NS)`. -/
theorem cn00_17 : cornerOK gdata (-3072) (1024)
    [10698999, 6265971, 8542942, 2979198, 2523394, 365015, 234353] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 512/NS)`. -/
theorem cn00_18 : cornerOK gdata (-2944) (512)
    [27175075, 16194201, 21550417, 8275827, 6978688, 933651, 683825] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2944/NT, 1024/NS)`. -/
theorem cn00_19 : cornerOK gdata (-2944) (1024)
    [11119544, 6980424, 8827306, 3299343, 2540857, 404386, 233711] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 512/NS)`. -/
theorem cn00_20 : cornerOK gdata (-2816) (512)
    [27599228, 17448913, 21773437, 8847861, 6843637, 996660, 660997] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2816/NT, 1024/NS)`. -/
theorem cn00_21 : cornerOK gdata (-2816) (1024)
    [11579462, 7657004, 9088580, 3599314, 2546802, 441060, 231807] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 512/NS)`. -/
theorem cn00_22 : cornerOK gdata (-2688) (512)
    [27955001, 18540718, 21910016, 9319500, 6668860, 1048509, 633718] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2688/NT, 1024/NS)`. -/
theorem cn00_23 : cornerOK gdata (-2688) (1024)
    [12034146, 8273256, 9318067, 3869746, 2550733, 473725, 228588] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 512/NS)`. -/
theorem cn00_24 : cornerOK gdata (-2560) (512)
    [28221091, 19437260, 21975446, 9675674, 6460795, 1087436, 602410] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2560/NT, 1024/NS)`. -/
theorem cn00_25 : cornerOK gdata (-2560) (1024)
    [12457527, 8806032, 9591176, 4101199, 2552772, 501048, 223940] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 512/NS)`. -/
theorem cn00_26 : cornerOK gdata (-2432) (512)
    [28364460, 20104718, 21975446, 9901628, 6220688, 1111629, 567548] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2432/NT, 1024/NS)`. -/
theorem cn00_27 : cornerOK gdata (-2432) (1024)
    [12841291, 9237939, 9834279, 4286930, 2552772, 521985, 217859] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 512/NS)`. -/
theorem cn00_28 : cornerOK gdata (-2304) (512)
    [28401984, 20544451, 21920982, 10000463, 5945865, 1121327, 529984] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2304/NT, 1024/NS)`. -/
theorem cn00_29 : cornerOK gdata (-2304) (1024)
    [13195307, 9574849, 10046492, 4431889, 2541669, 536941, 212005] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 512/NS)`. -/
theorem cn00_30 : cornerOK gdata (-2176) (512)
    [28401984, 20544451, 21761162, 10000463, 5642245, 1121327, 489910] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2176/NT, 1024/NS)`. -/
theorem cn00_31 : cornerOK gdata (-2176) (1024)
    [75475591, 54821267, 53890475, 26458006, 13457933, 2832315, 1194672] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2112/NT, 1024/NS)`. -/
theorem cn00_32 : cornerOK gdata (-2112) (1024)
    [75475591, 54821267, 53890475, 26458006, 13457933, 2832315, 1194672] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-2048/NT, 1024/NS)`. -/
theorem cn00_33 : cornerOK gdata (-2048) (1024)
    [73995978, 54318050, 52549095, 25973927, 12835866, 2780647, 1109467] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1984/NT, 1024/NS)`. -/
theorem cn00_34 : cornerOK gdata (-1984) (1024)
    [72457664, 53647656, 51176016, 25402565, 12529128, 2719503, 1025905] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1920/NT, 1024/NS)`. -/
theorem cn00_35 : cornerOK gdata (-1920) (1024)
    [70754656, 52778619, 49693358, 24734684, 12192134, 2647905, 942980] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1856/NT, 1024/NS)`. -/
theorem cn00_36 : cornerOK gdata (-1856) (1024)
    [68962902, 51746671, 48162575, 23987889, 11838551, 2567509, 890675] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1792/NT, 1024/NS)`. -/
theorem cn00_37 : cornerOK gdata (-1792) (1024)
    [67024920, 50554672, 46543549, 23166505, 11458048, 2478662, 860695] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1728/NT, 1024/NS)`. -/
theorem cn00_38 : cornerOK gdata (-1728) (1024)
    [64948031, 49203614, 44846615, 22270638, 11053669, 2381110, 829638] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1664/NT, 1024/NS)`. -/
theorem cn00_39 : cornerOK gdata (-1664) (1024)
    [62785672, 47747095, 43115269, 21325629, 10635987, 2277640, 798306] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1600/NT, 1024/NS)`. -/
theorem cn00_40 : cornerOK gdata (-1600) (1024)
    [60453820, 46211836, 41296360, 20351970, 10192968, 2170393, 765617] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1536/NT, 1024/NS)`. -/
theorem cn00_41 : cornerOK gdata (-1536) (1024)
    [58027961, 44598819, 39465473, 19345192, 9741874, 2058298, 732612] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1472/NT, 1024/NS)`. -/
theorem cn00_42 : cornerOK gdata (-1472) (1024)
    [55516138, 42916446, 37620449, 18313723, 9282288, 1943706, 699265] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1408/NT, 1024/NS)`. -/
theorem cn00_43 : cornerOK gdata (-1408) (1024)
    [87933054, 65773834, 61874165, 27437214, 14454507, 2931378, 1047770] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1280/NT, 1024/NS)`. -/
theorem cn00_44 : cornerOK gdata (-1280) (1024)
    [87933054, 65773834, 61874165, 27437214, 14454507, 2931378, 1047770] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1152/NT, 1024/NS)`. -/
theorem cn00_45 : cornerOK gdata (-1152) (1024)
    [79814792, 60202380, 55633705, 24435406, 12856704, 2584349, 928838] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-1024/NT, 1024/NS)`. -/
theorem cn00_46 : cornerOK gdata (-1024) (1024)
    [71220553, 54278957, 49279493, 21433234, 11264445, 2233335, 813025] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-896/NT, 1024/NS)`. -/
theorem cn00_47 : cornerOK gdata (-896) (1024)
    [62476028, 48145266, 42976377, 18479448, 9720284, 1887202, 702245] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-768/NT, 1024/NS)`. -/
theorem cn00_48 : cornerOK gdata (-768) (1024)
    [53868743, 41956094, 36930208, 15638275, 8277736, 1553653, 598227] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-640/NT, 1024/NS)`. -/
theorem cn00_49 : cornerOK gdata (-640) (1024)
    [45736787, 35795438, 31344021, 12954233, 6983982, 1238659, 502419] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-512/NT, 1024/NS)`. -/
theorem cn00_50 : cornerOK gdata (-512) (1024)
    [41376299, 29739494, 26337428, 10442356, 5840871, 968835, 416540] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-384/NT, 1024/NS)`. -/
theorem cn00_51 : cornerOK gdata (-384) (1024)
    [37723167, 23897877, 22077993, 8123867, 4890278, 821201, 343331] = true := by
  bl_cert

/-- Kernel-checked corner test at `(-256/NT, 1024/NS)`. -/
theorem cn00_52 : cornerOK gdata (-256) (1024)
    [90464511, 35608752, 51617582, 14205767, 10667241, 1676209, 666647] = true := by
  bl_cert

/-- Kernel-checked corner test at `(0/NT, 1024/NS)`. -/
theorem cn00_53 : cornerOK gdata (0) (1024)
    [90464511, 35608752, 51617582, 14205767, 10667241, 1676209, 666647] = true := by
  bl_cert

/-- Kernel-checked box `[-4096, -3968]/NT × [0, 512]/NS`. -/
theorem cov0 : Cover gdata (-4096) (-3968) (0) (512) := by
  ballooning_box "Z:cn00_0,cn00_1"

/-- Kernel-checked box `[-4096, -3968]/NT × [512, 1024]/NS`. -/
theorem cov1 : Cover gdata (-4096) (-3968) (512) (1024) := by
  ballooning_box "Q:cn00_0,cn00_1,cn00_2,cn00_3"

/-- Kernel-checked box `[-3968, -3840]/NT × [0, 512]/NS`. -/
theorem cov2 : Cover gdata (-3968) (-3840) (0) (512) := by
  ballooning_box "Z:cn00_1,cn00_4"

/-- Kernel-checked box `[-3968, -3840]/NT × [512, 1024]/NS`. -/
theorem cov3 : Cover gdata (-3968) (-3840) (512) (1024) := by
  ballooning_box "Q:cn00_1,cn00_4,cn00_3,cn00_5"

/-- Kernel-checked box `[-3840, -3712]/NT × [0, 512]/NS`. -/
theorem cov4 : Cover gdata (-3840) (-3712) (0) (512) := by
  ballooning_box "Z:cn00_4,cn00_6"

/-- Kernel-checked box `[-3840, -3712]/NT × [512, 1024]/NS`. -/
theorem cov5 : Cover gdata (-3840) (-3712) (512) (1024) := by
  ballooning_box "Q:cn00_4,cn00_6,cn00_5,cn00_7"

/-- Kernel-checked box `[-3712, -3584]/NT × [0, 512]/NS`. -/
theorem cov6 : Cover gdata (-3712) (-3584) (0) (512) := by
  ballooning_box "Z:cn00_6,cn00_8"

/-- Kernel-checked box `[-3712, -3584]/NT × [512, 1024]/NS`. -/
theorem cov7 : Cover gdata (-3712) (-3584) (512) (1024) := by
  ballooning_box "Q:cn00_6,cn00_8,cn00_7,cn00_9"

/-- Kernel-checked box `[-3584, -3456]/NT × [0, 512]/NS`. -/
theorem cov8 : Cover gdata (-3584) (-3456) (0) (512) := by
  ballooning_box "Z:cn00_8,cn00_10"

/-- Kernel-checked box `[-3584, -3456]/NT × [512, 1024]/NS`. -/
theorem cov9 : Cover gdata (-3584) (-3456) (512) (1024) := by
  ballooning_box "Q:cn00_8,cn00_10,cn00_9,cn00_11"

/-- Kernel-checked box `[-3456, -3328]/NT × [0, 512]/NS`. -/
theorem cov10 : Cover gdata (-3456) (-3328) (0) (512) := by
  ballooning_box "Z:cn00_10,cn00_12"

/-- Kernel-checked box `[-3456, -3328]/NT × [512, 1024]/NS`. -/
theorem cov11 : Cover gdata (-3456) (-3328) (512) (1024) := by
  ballooning_box "Q:cn00_10,cn00_12,cn00_11,cn00_13"

/-- Kernel-checked box `[-3328, -3200]/NT × [0, 512]/NS`. -/
theorem cov12 : Cover gdata (-3328) (-3200) (0) (512) := by
  ballooning_box "Z:cn00_12,cn00_14"

/-- Kernel-checked box `[-3328, -3200]/NT × [512, 1024]/NS`. -/
theorem cov13 : Cover gdata (-3328) (-3200) (512) (1024) := by
  ballooning_box "Q:cn00_12,cn00_14,cn00_13,cn00_15"

/-- Kernel-checked box `[-3200, -3072]/NT × [0, 512]/NS`. -/
theorem cov14 : Cover gdata (-3200) (-3072) (0) (512) := by
  ballooning_box "Z:cn00_14,cn00_16"

/-- Kernel-checked box `[-3200, -3072]/NT × [512, 1024]/NS`. -/
theorem cov15 : Cover gdata (-3200) (-3072) (512) (1024) := by
  ballooning_box "Q:cn00_14,cn00_16,cn00_15,cn00_17"

/-- Kernel-checked box `[-3072, -2944]/NT × [0, 512]/NS`. -/
theorem cov16 : Cover gdata (-3072) (-2944) (0) (512) := by
  ballooning_box "Z:cn00_16,cn00_18"

/-- Kernel-checked box `[-3072, -2944]/NT × [512, 1024]/NS`. -/
theorem cov17 : Cover gdata (-3072) (-2944) (512) (1024) := by
  ballooning_box "Q:cn00_16,cn00_18,cn00_17,cn00_19"

/-- Kernel-checked box `[-2944, -2816]/NT × [0, 512]/NS`. -/
theorem cov18 : Cover gdata (-2944) (-2816) (0) (512) := by
  ballooning_box "Z:cn00_18,cn00_20"

/-- Kernel-checked box `[-2944, -2816]/NT × [512, 1024]/NS`. -/
theorem cov19 : Cover gdata (-2944) (-2816) (512) (1024) := by
  ballooning_box "Q:cn00_18,cn00_20,cn00_19,cn00_21"

/-- Kernel-checked box `[-2816, -2688]/NT × [0, 512]/NS`. -/
theorem cov20 : Cover gdata (-2816) (-2688) (0) (512) := by
  ballooning_box "Z:cn00_20,cn00_22"

/-- Kernel-checked box `[-2816, -2688]/NT × [512, 1024]/NS`. -/
theorem cov21 : Cover gdata (-2816) (-2688) (512) (1024) := by
  ballooning_box "Q:cn00_20,cn00_22,cn00_21,cn00_23"

/-- Kernel-checked box `[-2688, -2560]/NT × [0, 512]/NS`. -/
theorem cov22 : Cover gdata (-2688) (-2560) (0) (512) := by
  ballooning_box "Z:cn00_22,cn00_24"

/-- Kernel-checked box `[-2688, -2560]/NT × [512, 1024]/NS`. -/
theorem cov23 : Cover gdata (-2688) (-2560) (512) (1024) := by
  ballooning_box "Q:cn00_22,cn00_24,cn00_23,cn00_25"

/-- Kernel-checked box `[-2560, -2432]/NT × [0, 512]/NS`. -/
theorem cov24 : Cover gdata (-2560) (-2432) (0) (512) := by
  ballooning_box "Z:cn00_24,cn00_26"

/-- Kernel-checked box `[-2560, -2432]/NT × [512, 1024]/NS`. -/
theorem cov25 : Cover gdata (-2560) (-2432) (512) (1024) := by
  ballooning_box "Q:cn00_24,cn00_26,cn00_25,cn00_27"

/-- Kernel-checked box `[-2432, -2304]/NT × [0, 512]/NS`. -/
theorem cov26 : Cover gdata (-2432) (-2304) (0) (512) := by
  ballooning_box "Z:cn00_26,cn00_28"

/-- Kernel-checked box `[-2432, -2304]/NT × [512, 1024]/NS`. -/
theorem cov27 : Cover gdata (-2432) (-2304) (512) (1024) := by
  ballooning_box "Q:cn00_26,cn00_28,cn00_27,cn00_29"

/-- Kernel-checked box `[-2304, -2176]/NT × [0, 512]/NS`. -/
theorem cov28 : Cover gdata (-2304) (-2176) (0) (512) := by
  ballooning_box "Z:cn00_28,cn00_30"

/-- Kernel-checked box `[-2304, -2176]/NT × [512, 1024]/NS`. -/
theorem cov29 : Cover gdata (-2304) (-2176) (512) (1024) := by
  ballooning_box "Q:cn00_28,cn00_30,cn00_29,cn00_31"

/-- Kernel-checked box `[-2176, -2112]/NT × [0, 1024]/NS`. -/
theorem cov30 : Cover gdata (-2176) (-2112) (0) (1024) := by
  ballooning_box "Z:cn00_31,cn00_32"

/-- Kernel-checked box `[-2112, -2048]/NT × [0, 1024]/NS`. -/
theorem cov31 : Cover gdata (-2112) (-2048) (0) (1024) := by
  ballooning_box "Z:cn00_32,cn00_33"

/-- Kernel-checked box `[-2048, -1984]/NT × [0, 1024]/NS`. -/
theorem cov32 : Cover gdata (-2048) (-1984) (0) (1024) := by
  ballooning_box "Z:cn00_33,cn00_34"

/-- Kernel-checked box `[-1984, -1920]/NT × [0, 1024]/NS`. -/
theorem cov33 : Cover gdata (-1984) (-1920) (0) (1024) := by
  ballooning_box "Z:cn00_34,cn00_35"

/-- Kernel-checked box `[-1920, -1856]/NT × [0, 1024]/NS`. -/
theorem cov34 : Cover gdata (-1920) (-1856) (0) (1024) := by
  ballooning_box "Z:cn00_35,cn00_36"

/-- Kernel-checked box `[-1856, -1792]/NT × [0, 1024]/NS`. -/
theorem cov35 : Cover gdata (-1856) (-1792) (0) (1024) := by
  ballooning_box "Z:cn00_36,cn00_37"

/-- Kernel-checked box `[-1792, -1728]/NT × [0, 1024]/NS`. -/
theorem cov36 : Cover gdata (-1792) (-1728) (0) (1024) := by
  ballooning_box "Z:cn00_37,cn00_38"

/-- Kernel-checked box `[-1728, -1664]/NT × [0, 1024]/NS`. -/
theorem cov37 : Cover gdata (-1728) (-1664) (0) (1024) := by
  ballooning_box "Z:cn00_38,cn00_39"

/-- Kernel-checked box `[-1664, -1600]/NT × [0, 1024]/NS`. -/
theorem cov38 : Cover gdata (-1664) (-1600) (0) (1024) := by
  ballooning_box "Z:cn00_39,cn00_40"

/-- Kernel-checked box `[-1600, -1536]/NT × [0, 1024]/NS`. -/
theorem cov39 : Cover gdata (-1600) (-1536) (0) (1024) := by
  ballooning_box "Z:cn00_40,cn00_41"

/-- Kernel-checked box `[-1536, -1472]/NT × [0, 1024]/NS`. -/
theorem cov40 : Cover gdata (-1536) (-1472) (0) (1024) := by
  ballooning_box "Z:cn00_41,cn00_42"

/-- Kernel-checked box `[-1472, -1408]/NT × [0, 1024]/NS`. -/
theorem cov41 : Cover gdata (-1472) (-1408) (0) (1024) := by
  ballooning_box "Z:cn00_42,cn00_43"

/-- Kernel-checked box `[-1408, -1280]/NT × [0, 1024]/NS`. -/
theorem cov42 : Cover gdata (-1408) (-1280) (0) (1024) := by
  ballooning_box "Z:cn00_43,cn00_44"

/-- Kernel-checked box `[-1280, -1152]/NT × [0, 1024]/NS`. -/
theorem cov43 : Cover gdata (-1280) (-1152) (0) (1024) := by
  ballooning_box "Z:cn00_44,cn00_45"

/-- Kernel-checked box `[-1152, -1024]/NT × [0, 1024]/NS`. -/
theorem cov44 : Cover gdata (-1152) (-1024) (0) (1024) := by
  ballooning_box "Z:cn00_45,cn00_46"

/-- Kernel-checked box `[-1024, -896]/NT × [0, 1024]/NS`. -/
theorem cov45 : Cover gdata (-1024) (-896) (0) (1024) := by
  ballooning_box "Z:cn00_46,cn00_47"

/-- Kernel-checked box `[-896, -768]/NT × [0, 1024]/NS`. -/
theorem cov46 : Cover gdata (-896) (-768) (0) (1024) := by
  ballooning_box "Z:cn00_47,cn00_48"

/-- Kernel-checked box `[-768, -640]/NT × [0, 1024]/NS`. -/
theorem cov47 : Cover gdata (-768) (-640) (0) (1024) := by
  ballooning_box "Z:cn00_48,cn00_49"

/-- Kernel-checked box `[-640, -512]/NT × [0, 1024]/NS`. -/
theorem cov48 : Cover gdata (-640) (-512) (0) (1024) := by
  ballooning_box "Z:cn00_49,cn00_50"

/-- Kernel-checked box `[-512, -384]/NT × [0, 1024]/NS`. -/
theorem cov49 : Cover gdata (-512) (-384) (0) (1024) := by
  ballooning_box "Z:cn00_50,cn00_51"

/-- Kernel-checked box `[-384, -256]/NT × [0, 1024]/NS`. -/
theorem cov50 : Cover gdata (-384) (-256) (0) (1024) := by
  ballooning_box "Z:cn00_51,cn00_52"

/-- Kernel-checked box `[-256, 0]/NT × [0, 1024]/NS`. -/
theorem cov51 : Cover gdata (-256) (0) (0) (1024) := by
  ballooning_box "Z:cn00_52,cn00_53"

end PlasmaLean.Design.SolovevBallooning
