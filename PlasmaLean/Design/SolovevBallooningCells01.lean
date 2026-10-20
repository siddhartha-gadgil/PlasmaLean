/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningData

/-!
# Ballooning certificate: kernel-checked cells, part 1

52 boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

/-- Kernel-checked corner test at `(0/NT, 1024/NS)`. -/
theorem cn01_0 : cornerOK gdata (0) (1024)
    [90052064, 33379506, 50893448, 14104982, 10487760, 1626592, 628356] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(256/NT, 1024/NS)`. -/
theorem cn01_1 : cornerOK gdata (256) (1024)
    [90052064, 33379506, 50893448, 14104982, 10487760, 1626592, 628356] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(384/NT, 1024/NS)`. -/
theorem cn01_2 : cornerOK gdata (384) (1024)
    [37820045, 17177778, 20204073, 7112530, 4317144, 728034, 226432] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(512/NT, 1024/NS)`. -/
theorem cn01_3 : cornerOK gdata (512) (1024)
    [41316420, 21372518, 23720871, 8655561, 5034657, 907418, 282145] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(640/NT, 1024/NS)`. -/
theorem cn01_4 : cornerOK gdata (640) (1024)
    [45588273, 25497801, 27892939, 10346095, 5911390, 1180087, 347038] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(768/NT, 1024/NS)`. -/
theorem cn01_5 : cornerOK gdata (768) (1024)
    [50319769, 29408586, 32461509, 12530230, 6929340, 1467054, 420431] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(896/NT, 1024/NS)`. -/
theorem cn01_6 : cornerOK gdata (896) (1024)
    [55442411, 33069873, 37366279, 14812500, 8064825, 1762339, 502900] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1024/NT, 1024/NS)`. -/
theorem cn01_7 : cornerOK gdata (1024) (1024)
    [60860846, 37289352, 42391711, 17150022, 9290288, 2059121, 595691] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1152/NT, 1024/NS)`. -/
theorem cn01_8 : cornerOK gdata (1152) (1024)
    [66486481, 41639673, 47375109, 19478701, 10587412, 2349515, 698096] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1280/NT, 1024/NS)`. -/
theorem cn01_9 : cornerOK gdata (1280) (1024)
    [72179384, 45736413, 52172244, 21720329, 11932675, 2624370, 829922] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1408/NT, 1024/NS)`. -/
theorem cn01_10 : cornerOK gdata (1408) (1024)
    [77961885, 49512783, 56785413, 23825431, 13322656, 2877238, 973241] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1536/NT, 1024/NS)`. -/
theorem cn01_11 : cornerOK gdata (1536) (1024)
    [84046301, 52964753, 61331960, 25750848, 14799096, 3104408, 1131377] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1664/NT, 1024/NS)`. -/
theorem cn01_12 : cornerOK gdata (1664) (1024)
    [89775884, 56041396, 66198940, 27506921, 16277640, 3308219, 1294787] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1792/NT, 1024/NS)`. -/
theorem cn01_13 : cornerOK gdata (1792) (1024)
    [95011497, 58779157, 71709122, 29088760, 17729677, 3493544, 1460195] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(1920/NT, 1024/NS)`. -/
theorem cn01_14 : cornerOK gdata (1920) (1024)
    [99714851, 60689427, 76896254, 30254568, 19110636, 3628103, 1623735] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2048/NT, 1024/NS)`. -/
theorem cn01_15 : cornerOK gdata (2048) (1024)
    [103771308, 61721961, 81645298, 30978447, 20441556, 3709427, 1783196] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2176/NT, 1024/NS)`. -/
theorem cn01_16 : cornerOK gdata (2176) (1024)
    [107162164, 61859386, 85912638, 31242140, 21815027, 3735983, 1935242] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2304/NT, 1024/NS)`. -/
theorem cn01_17 : cornerOK gdata (2304) (1024)
    [109927528, 61859386, 89691461, 31242140, 23076158, 3735983, 2078556] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2432/NT, 1024/NS)`. -/
theorem cn01_18 : cornerOK gdata (2432) (1024)
    [109927528, 61154471, 89691461, 31063303, 23076158, 3710414, 2078556] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2496/NT, 1024/NS)`. -/
theorem cn01_19 : cornerOK gdata (2496) (1024)
    [72274614, 33845143, 57979459, 18220666, 14769742, 2169802, 1395698] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2560/NT, 1024/NS)`. -/
theorem cn01_20 : cornerOK gdata (2560) (1024)
    [73400350, 33399259, 59356538, 18020087, 15187840, 2140466, 1440428] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2624/NT, 1024/NS)`. -/
theorem cn01_21 : cornerOK gdata (2624) (1024)
    [74367559, 32858598, 60597700, 17759056, 15570979, 2104294, 1483314] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2688/NT, 1024/NS)`. -/
theorem cn01_22 : cornerOK gdata (2688) (1024)
    [75271017, 32208716, 61782021, 17436216, 15940143, 2061515, 1523260] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2752/NT, 1024/NS)`. -/
theorem cn01_23 : cornerOK gdata (2752) (1024)
    [76093349, 31447981, 62891835, 17050508, 16289307, 2011955, 1560892] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2816/NT, 1024/NS)`. -/
theorem cn01_24 : cornerOK gdata (2816) (1024)
    [76803019, 30592372, 63896404, 16610034, 16609138, 1956585, 1596130] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2880/NT, 1024/NS)`. -/
theorem cn01_25 : cornerOK gdata (2880) (1024)
    [77454973, 29646582, 64842105, 16117489, 16913170, 1895764, 1630107] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(2944/NT, 1024/NS)`. -/
theorem cn01_26 : cornerOK gdata (2944) (1024)
    [78005345, 28633916, 65687202, 15584475, 17189025, 1830814, 1660386] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3008/NT, 1024/NS)`. -/
theorem cn01_27 : cornerOK gdata (3008) (1024)
    [78482422, 27532270, 66451341, 15000436, 17441312, 1760442, 1688672] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3072/NT, 1024/NS)`. -/
theorem cn01_28 : cornerOK gdata (3072) (1024)
    [78857903, 26369800, 67109572, 14379776, 17662769, 1686370, 1714474] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3136/NT, 1024/NS)`. -/
theorem cn01_29 : cornerOK gdata (3136) (1024)
    [79206447, 25146170, 67728543, 13722686, 17872749, 1608554, 1737055] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3200/NT, 1024/NS)`. -/
theorem cn01_30 : cornerOK gdata (3200) (1024)
    [79436888, 23868417, 68220718, 13032931, 18044589, 1527388, 1758466] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3264/NT, 1024/NS)`. -/
theorem cn01_31 : cornerOK gdata (3264) (1024)
    [79634916, 22553512, 68664976, 12319671, 18201687, 1443964, 1776271] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 1024/NS)`. -/
theorem cn01_32 : cornerOK gdata (3328) (1024)
    [79634916, 21195046, 68664976, 11579961, 18201687, 1357835, 1776271] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3328/NT, 512/NS)`. -/
theorem cn01_33 : cornerOK gdata (3328) (512)
    [32339289, 16636349, 28329768, 8090141, 7774860, 1009079, 694885] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3456/NT, 512/NS)`. -/
theorem cn01_34 : cornerOK gdata (3456) (512)
    [24831962, 7467464, 21488653, 3925343, 5753682, 475845, 548780] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 512/NS)`. -/
theorem cn01_35 : cornerOK gdata (3584) (512)
    [32339289, 16636349, 28329768, 8090141, 7774860, 1009079, 694885] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3584/NT, 1024/NS)`. -/
theorem cn01_36 : cornerOK gdata (3584) (1024)
    [79815537, 16636349, 69853980, 8090141, 18655344, 1009079, 1832648] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3648/NT, 1024/NS)`. -/
theorem cn01_37 : cornerOK gdata (3648) (1024)
    [79815537, 14180251, 69908846, 7715638, 18687523, 912642, 1838040] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3712/NT, 1024/NS)`. -/
theorem cn01_38 : cornerOK gdata (3712) (1024)
    [109348997, 20611838, 100270595, 10662769, 28000053, 1304414, 2741461] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3840/NT, 1024/NS)`. -/
theorem cn01_39 : cornerOK gdata (3840) (1024)
    [109348997, 20611838, 100270595, 10662769, 28000053, 1304414, 2741461] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(3968/NT, 1024/NS)`. -/
theorem cn01_40 : cornerOK gdata (3968) (1024)
    [107838719, 16232257, 99145987, 8331406, 27735450, 1032703, 2722438] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(4096/NT, 1024/NS)`. -/
theorem cn01_41 : cornerOK gdata (4096) (1024)
    [106214117, 11995847, 97780013, 6065464, 27379658, 769263, 2694193] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 1024/NS)`. -/
theorem cn01_42 : cornerOK gdata (-4096) (1024)
    [36425530, 5271393, 29291372, 2509955, 9608510, 323268, 958596] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3968/NT, 1024/NS)`. -/
theorem cn01_43 : cornerOK gdata (-3968) (1024)
    [37302947, 7233410, 30038607, 3514011, 9780792, 429731, 971125] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-4096/NT, 2048/NS)`. -/
theorem cn01_44 : cornerOK gdata (-4096) (2048)
    [36425530, 5271393, 29291372, 2509955, 9608510, 323268, 958596] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3968/NT, 2048/NS)`. -/
theorem cn01_45 : cornerOK gdata (-3968) (2048)
    [37302947, 7233410, 30038607, 3514011, 9780792, 429731, 971125] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 1024/NS)`. -/
theorem cn01_46 : cornerOK gdata (-3840) (1024)
    [38213657, 9383913, 30783707, 4551722, 9928349, 543597, 980086] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3840/NT, 2048/NS)`. -/
theorem cn01_47 : cornerOK gdata (-3840) (2048)
    [38213657, 9383913, 30783707, 4551722, 9928349, 543597, 980086] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3712/NT, 1024/NS)`. -/
theorem cn01_48 : cornerOK gdata (-3712) (1024)
    [39136470, 11599243, 31503458, 5609263, 10044577, 665162, 984802] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3712/NT, 2048/NS)`. -/
theorem cn01_49 : cornerOK gdata (-3712) (2048)
    [39136470, 11599243, 31503458, 5609263, 10044577, 665162, 984802] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 1024/NS)`. -/
theorem cn01_50 : cornerOK gdata (-3584) (1024)
    [40066639, 13852065, 32189329, 6671164, 10126498, 787792, 984971] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3584/NT, 2048/NS)`. -/
theorem cn01_51 : cornerOK gdata (-3584) (2048)
    [40066639, 13852065, 32189329, 6671164, 10126498, 787792, 984971] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 1024/NS)`. -/
theorem cn01_52 : cornerOK gdata (-3456) (1024)
    [40981969, 16113408, 32818757, 7719825, 10170402, 909540, 984971] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3456/NT, 2048/NS)`. -/
theorem cn01_53 : cornerOK gdata (-3456) (2048)
    [40981969, 16113408, 32818757, 7719825, 10170402, 909540, 984971] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 1024/NS)`. -/
theorem cn01_54 : cornerOK gdata (-3328) (1024)
    [41895063, 18651910, 33416057, 8882743, 10174671, 1044923, 980219] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3328/NT, 2048/NS)`. -/
theorem cn01_55 : cornerOK gdata (-3328) (2048)
    [41895063, 18651910, 33416057, 8882743, 10174671, 1044923, 980219] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 1024/NS)`. -/
theorem cn01_56 : cornerOK gdata (-3200) (1024)
    [42778964, 21152342, 33949316, 10009807, 10174671, 1176851, 970186] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3200/NT, 2048/NS)`. -/
theorem cn01_57 : cornerOK gdata (-3200) (2048)
    [42778964, 21152342, 33949316, 10009807, 10174671, 1176851, 970186] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 1024/NS)`. -/
theorem cn01_58 : cornerOK gdata (-3072) (1024)
    [43611087, 23560795, 34396158, 11081781, 10133334, 1301773, 954600] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-3072/NT, 2048/NS)`. -/
theorem cn01_59 : cornerOK gdata (-3072) (2048)
    [43611087, 23560795, 34396158, 11081781, 10133334, 1301773, 954600] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 1024/NS)`. -/
theorem cn01_60 : cornerOK gdata (-2944) (1024)
    [44369466, 25813702, 34738510, 12063320, 10045638, 1416000, 933543] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2944/NT, 2048/NS)`. -/
theorem cn01_61 : cornerOK gdata (-2944) (2048)
    [44369466, 25813702, 34738510, 12063320, 10045638, 1416000, 933543] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2816/NT, 1024/NS)`. -/
theorem cn01_62 : cornerOK gdata (-2816) (1024)
    [45078888, 27848523, 34937103, 12927462, 9903375, 1516120, 906468] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2816/NT, 2048/NS)`. -/
theorem cn01_63 : cornerOK gdata (-2816) (2048)
    [45078888, 27848523, 34937103, 12927462, 9903375, 1516120, 906468] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2688/NT, 1024/NS)`. -/
theorem cn01_64 : cornerOK gdata (-2688) (1024)
    [45704738, 29604269, 34988737, 13648973, 9707031, 1598812, 873694] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2688/NT, 2048/NS)`. -/
theorem cn01_65 : cornerOK gdata (-2688) (2048)
    [45704738, 29604269, 34988737, 13648973, 9707031, 1598812, 873694] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2560/NT, 1024/NS)`. -/
theorem cn01_66 : cornerOK gdata (-2560) (1024)
    [45704738, 29604269, 34988737, 13648973, 9477766, 1598812, 835592] = true := by
  decide +kernel

/-- Kernel-checked corner test at `(-2560/NT, 2048/NS)`. -/
theorem cn01_67 : cornerOK gdata (-2560) (2048)
    [45704738, 29604269, 34988737, 13648973, 9477766, 1598812, 835592] = true := by
  decide +kernel

/-- Kernel-checked box `[0, 256]/NT × [0, 1024]/NS`. -/
theorem cov52 : Cover gdata (0) (256) (0) (1024) := by
  ballooning_cover "Z:cn01_0,cn01_1"

/-- Kernel-checked box `[256, 384]/NT × [0, 1024]/NS`. -/
theorem cov53 : Cover gdata (256) (384) (0) (1024) := by
  ballooning_cover "Z:cn01_1,cn01_2"

/-- Kernel-checked box `[384, 512]/NT × [0, 1024]/NS`. -/
theorem cov54 : Cover gdata (384) (512) (0) (1024) := by
  ballooning_cover "Z:cn01_2,cn01_3"

/-- Kernel-checked box `[512, 640]/NT × [0, 1024]/NS`. -/
theorem cov55 : Cover gdata (512) (640) (0) (1024) := by
  ballooning_cover "Z:cn01_3,cn01_4"

/-- Kernel-checked box `[640, 768]/NT × [0, 1024]/NS`. -/
theorem cov56 : Cover gdata (640) (768) (0) (1024) := by
  ballooning_cover "Z:cn01_4,cn01_5"

/-- Kernel-checked box `[768, 896]/NT × [0, 1024]/NS`. -/
theorem cov57 : Cover gdata (768) (896) (0) (1024) := by
  ballooning_cover "Z:cn01_5,cn01_6"

/-- Kernel-checked box `[896, 1024]/NT × [0, 1024]/NS`. -/
theorem cov58 : Cover gdata (896) (1024) (0) (1024) := by
  ballooning_cover "Z:cn01_6,cn01_7"

/-- Kernel-checked box `[1024, 1152]/NT × [0, 1024]/NS`. -/
theorem cov59 : Cover gdata (1024) (1152) (0) (1024) := by
  ballooning_cover "Z:cn01_7,cn01_8"

/-- Kernel-checked box `[1152, 1280]/NT × [0, 1024]/NS`. -/
theorem cov60 : Cover gdata (1152) (1280) (0) (1024) := by
  ballooning_cover "Z:cn01_8,cn01_9"

/-- Kernel-checked box `[1280, 1408]/NT × [0, 1024]/NS`. -/
theorem cov61 : Cover gdata (1280) (1408) (0) (1024) := by
  ballooning_cover "Z:cn01_9,cn01_10"

/-- Kernel-checked box `[1408, 1536]/NT × [0, 1024]/NS`. -/
theorem cov62 : Cover gdata (1408) (1536) (0) (1024) := by
  ballooning_cover "Z:cn01_10,cn01_11"

/-- Kernel-checked box `[1536, 1664]/NT × [0, 1024]/NS`. -/
theorem cov63 : Cover gdata (1536) (1664) (0) (1024) := by
  ballooning_cover "Z:cn01_11,cn01_12"

/-- Kernel-checked box `[1664, 1792]/NT × [0, 1024]/NS`. -/
theorem cov64 : Cover gdata (1664) (1792) (0) (1024) := by
  ballooning_cover "Z:cn01_12,cn01_13"

/-- Kernel-checked box `[1792, 1920]/NT × [0, 1024]/NS`. -/
theorem cov65 : Cover gdata (1792) (1920) (0) (1024) := by
  ballooning_cover "Z:cn01_13,cn01_14"

/-- Kernel-checked box `[1920, 2048]/NT × [0, 1024]/NS`. -/
theorem cov66 : Cover gdata (1920) (2048) (0) (1024) := by
  ballooning_cover "Z:cn01_14,cn01_15"

/-- Kernel-checked box `[2048, 2176]/NT × [0, 1024]/NS`. -/
theorem cov67 : Cover gdata (2048) (2176) (0) (1024) := by
  ballooning_cover "Z:cn01_15,cn01_16"

/-- Kernel-checked box `[2176, 2304]/NT × [0, 1024]/NS`. -/
theorem cov68 : Cover gdata (2176) (2304) (0) (1024) := by
  ballooning_cover "Z:cn01_16,cn01_17"

/-- Kernel-checked box `[2304, 2432]/NT × [0, 1024]/NS`. -/
theorem cov69 : Cover gdata (2304) (2432) (0) (1024) := by
  ballooning_cover "Z:cn01_17,cn01_18"

/-- Kernel-checked box `[2432, 2496]/NT × [0, 1024]/NS`. -/
theorem cov70 : Cover gdata (2432) (2496) (0) (1024) := by
  ballooning_cover "Z:cn01_18,cn01_19"

/-- Kernel-checked box `[2496, 2560]/NT × [0, 1024]/NS`. -/
theorem cov71 : Cover gdata (2496) (2560) (0) (1024) := by
  ballooning_cover "Z:cn01_19,cn01_20"

/-- Kernel-checked box `[2560, 2624]/NT × [0, 1024]/NS`. -/
theorem cov72 : Cover gdata (2560) (2624) (0) (1024) := by
  ballooning_cover "Z:cn01_20,cn01_21"

/-- Kernel-checked box `[2624, 2688]/NT × [0, 1024]/NS`. -/
theorem cov73 : Cover gdata (2624) (2688) (0) (1024) := by
  ballooning_cover "Z:cn01_21,cn01_22"

/-- Kernel-checked box `[2688, 2752]/NT × [0, 1024]/NS`. -/
theorem cov74 : Cover gdata (2688) (2752) (0) (1024) := by
  ballooning_cover "Z:cn01_22,cn01_23"

/-- Kernel-checked box `[2752, 2816]/NT × [0, 1024]/NS`. -/
theorem cov75 : Cover gdata (2752) (2816) (0) (1024) := by
  ballooning_cover "Z:cn01_23,cn01_24"

/-- Kernel-checked box `[2816, 2880]/NT × [0, 1024]/NS`. -/
theorem cov76 : Cover gdata (2816) (2880) (0) (1024) := by
  ballooning_cover "Z:cn01_24,cn01_25"

/-- Kernel-checked box `[2880, 2944]/NT × [0, 1024]/NS`. -/
theorem cov77 : Cover gdata (2880) (2944) (0) (1024) := by
  ballooning_cover "Z:cn01_25,cn01_26"

/-- Kernel-checked box `[2944, 3008]/NT × [0, 1024]/NS`. -/
theorem cov78 : Cover gdata (2944) (3008) (0) (1024) := by
  ballooning_cover "Z:cn01_26,cn01_27"

/-- Kernel-checked box `[3008, 3072]/NT × [0, 1024]/NS`. -/
theorem cov79 : Cover gdata (3008) (3072) (0) (1024) := by
  ballooning_cover "Z:cn01_27,cn01_28"

/-- Kernel-checked box `[3072, 3136]/NT × [0, 1024]/NS`. -/
theorem cov80 : Cover gdata (3072) (3136) (0) (1024) := by
  ballooning_cover "Z:cn01_28,cn01_29"

/-- Kernel-checked box `[3136, 3200]/NT × [0, 1024]/NS`. -/
theorem cov81 : Cover gdata (3136) (3200) (0) (1024) := by
  ballooning_cover "Z:cn01_29,cn01_30"

/-- Kernel-checked box `[3200, 3264]/NT × [0, 1024]/NS`. -/
theorem cov82 : Cover gdata (3200) (3264) (0) (1024) := by
  ballooning_cover "Z:cn01_30,cn01_31"

/-- Kernel-checked box `[3264, 3328]/NT × [0, 1024]/NS`. -/
theorem cov83 : Cover gdata (3264) (3328) (0) (1024) := by
  ballooning_cover "Z:cn01_31,cn01_32"

/-- Kernel-checked box `[3328, 3456]/NT × [0, 512]/NS`. -/
theorem cov84 : Cover gdata (3328) (3456) (0) (512) := by
  ballooning_cover "Z:cn01_33,cn01_34"

/-- Kernel-checked box `[3456, 3584]/NT × [0, 512]/NS`. -/
theorem cov85 : Cover gdata (3456) (3584) (0) (512) := by
  ballooning_cover "Z:cn01_34,cn01_35"

/-- Kernel-checked box `[3328, 3584]/NT × [512, 1024]/NS`. -/
theorem cov86 : Cover gdata (3328) (3584) (512) (1024) := by
  ballooning_cover "Q:cn01_33,cn01_35,cn01_32,cn01_36"

/-- Kernel-checked box `[3584, 3648]/NT × [0, 1024]/NS`. -/
theorem cov87 : Cover gdata (3584) (3648) (0) (1024) := by
  ballooning_cover "Z:cn01_36,cn01_37"

/-- Kernel-checked box `[3648, 3712]/NT × [0, 1024]/NS`. -/
theorem cov88 : Cover gdata (3648) (3712) (0) (1024) := by
  ballooning_cover "Z:cn01_37,cn01_38"

/-- Kernel-checked box `[3712, 3840]/NT × [0, 1024]/NS`. -/
theorem cov89 : Cover gdata (3712) (3840) (0) (1024) := by
  ballooning_cover "Z:cn01_38,cn01_39"

/-- Kernel-checked box `[3840, 3968]/NT × [0, 1024]/NS`. -/
theorem cov90 : Cover gdata (3840) (3968) (0) (1024) := by
  ballooning_cover "Z:cn01_39,cn01_40"

/-- Kernel-checked box `[3968, 4096]/NT × [0, 1024]/NS`. -/
theorem cov91 : Cover gdata (3968) (4096) (0) (1024) := by
  ballooning_cover "Z:cn01_40,cn01_41"

/-- Kernel-checked box `[-4096, -3968]/NT × [1024, 2048]/NS`. -/
theorem cov92 : Cover gdata (-4096) (-3968) (1024) (2048) := by
  ballooning_cover "Q:cn01_42,cn01_43,cn01_44,cn01_45"

/-- Kernel-checked box `[-3968, -3840]/NT × [1024, 2048]/NS`. -/
theorem cov93 : Cover gdata (-3968) (-3840) (1024) (2048) := by
  ballooning_cover "Q:cn01_43,cn01_46,cn01_45,cn01_47"

/-- Kernel-checked box `[-3840, -3712]/NT × [1024, 2048]/NS`. -/
theorem cov94 : Cover gdata (-3840) (-3712) (1024) (2048) := by
  ballooning_cover "Q:cn01_46,cn01_48,cn01_47,cn01_49"

/-- Kernel-checked box `[-3712, -3584]/NT × [1024, 2048]/NS`. -/
theorem cov95 : Cover gdata (-3712) (-3584) (1024) (2048) := by
  ballooning_cover "Q:cn01_48,cn01_50,cn01_49,cn01_51"

/-- Kernel-checked box `[-3584, -3456]/NT × [1024, 2048]/NS`. -/
theorem cov96 : Cover gdata (-3584) (-3456) (1024) (2048) := by
  ballooning_cover "Q:cn01_50,cn01_52,cn01_51,cn01_53"

/-- Kernel-checked box `[-3456, -3328]/NT × [1024, 2048]/NS`. -/
theorem cov97 : Cover gdata (-3456) (-3328) (1024) (2048) := by
  ballooning_cover "Q:cn01_52,cn01_54,cn01_53,cn01_55"

/-- Kernel-checked box `[-3328, -3200]/NT × [1024, 2048]/NS`. -/
theorem cov98 : Cover gdata (-3328) (-3200) (1024) (2048) := by
  ballooning_cover "Q:cn01_54,cn01_56,cn01_55,cn01_57"

/-- Kernel-checked box `[-3200, -3072]/NT × [1024, 2048]/NS`. -/
theorem cov99 : Cover gdata (-3200) (-3072) (1024) (2048) := by
  ballooning_cover "Q:cn01_56,cn01_58,cn01_57,cn01_59"

/-- Kernel-checked box `[-3072, -2944]/NT × [1024, 2048]/NS`. -/
theorem cov100 : Cover gdata (-3072) (-2944) (1024) (2048) := by
  ballooning_cover "Q:cn01_58,cn01_60,cn01_59,cn01_61"

/-- Kernel-checked box `[-2944, -2816]/NT × [1024, 2048]/NS`. -/
theorem cov101 : Cover gdata (-2944) (-2816) (1024) (2048) := by
  ballooning_cover "Q:cn01_60,cn01_62,cn01_61,cn01_63"

/-- Kernel-checked box `[-2816, -2688]/NT × [1024, 2048]/NS`. -/
theorem cov102 : Cover gdata (-2816) (-2688) (1024) (2048) := by
  ballooning_cover "Q:cn01_62,cn01_64,cn01_63,cn01_65"

/-- Kernel-checked box `[-2688, -2560]/NT × [1024, 2048]/NS`. -/
theorem cov103 : Cover gdata (-2688) (-2560) (1024) (2048) := by
  ballooning_cover "Q:cn01_64,cn01_66,cn01_65,cn01_67"

end PlasmaLean.Design.SolovevBallooning
