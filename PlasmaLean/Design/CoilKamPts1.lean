/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 2 and 3

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(2, 0)`. -/
theorem ckPt_2_0 : ckPt 2 0 = some (398512713694735235482066, 855244136318742016397318) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 1)`. -/
theorem ckPt_2_1 : ckPt 2 1 = some (359269274815370807083953, 576155453074657537068265) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 2)`. -/
theorem ckPt_2_2 : ckPt 2 2 = some (275967941634011570420069, 653623401273463597981415) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 3)`. -/
theorem ckPt_2_3 : ckPt 2 3 = some (149890866609756797885022, 31370715014989935260585) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 4)`. -/
theorem ckPt_2_4 : ckPt 2 4 = some (415869711766766784259142, 146701153880403006836018) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 5)`. -/
theorem ckPt_2_5 : ckPt 2 5 = some (490257957365630557769475, 57674808145659848303970) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 6)`. -/
theorem ckPt_2_6 : ckPt 2 6 = some (153331769910037205585476, 322501289319610933849820) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 7)`. -/
theorem ckPt_2_7 : ckPt 2 7 = some (244731075177578613890264, 1080951609384258629275860) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 8)`. -/
theorem ckPt_2_8 : ckPt 2 8 = some (531213771940966385224181, 1220854765381975570040606) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 9)`. -/
theorem ckPt_2_9 : ckPt 2 9 = some (502833646575721393684876, 865804059756464660138777) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 10)`. -/
theorem ckPt_2_10 : ckPt 2 10 = some (154293464278773754057649, 534672522869628631903256) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 11)`. -/
theorem ckPt_2_11 : ckPt 2 11 = some (146540413351250900877961, 176571918844634877432030) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 12)`. -/
theorem ckPt_2_12 : ckPt 2 12 = some (217528886190614007126344, 306292286033535747709179) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 13)`. -/
theorem ckPt_2_13 : ckPt 2 13 = some (522683858921708213376564, 480306914680015702119729) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 14)`. -/
theorem ckPt_2_14 : ckPt 2 14 = some (44857998445804040422965, 399917727189430469211224) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 15)`. -/
theorem ckPt_2_15 : ckPt 2 15 = some (228399982578288543520723, 848672525546378413009339) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 16)`. -/
theorem ckPt_2_16 : ckPt 2 16 = some (398535422566474436893891, 855225664728459056636643) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 17)`. -/
theorem ckPt_2_17 : ckPt 2 17 = some (359277662822914354669311, 576140358305601479242617) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 18)`. -/
theorem ckPt_2_18 : ckPt 2 18 = some (276008727757338529527707, 653580543509810497868824) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 19)`. -/
theorem ckPt_2_19 : ckPt 2 19 = some (149916879176965427167524, 31363111741057252717641) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 20)`. -/
theorem ckPt_2_20 : ckPt 2 20 = some (415865803741639888832220, 146705319254138284954415) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 21)`. -/
theorem ckPt_2_21 : ckPt 2 21 = some (490209411229070846533930, 57721612904676652172447) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 22)`. -/
theorem ckPt_2_22 : ckPt 2 22 = some (153331390560169642815775, 322547205653731357857195) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 23)`. -/
theorem ckPt_2_23 : ckPt 2 23 = some (244753563316376693297344, 1080988764500682978727762) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 24)`. -/
theorem ckPt_2_24 : ckPt 2 24 = some (531222409160479994141909, 1220888770023464596314258) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 25)`. -/
theorem ckPt_2_25 : ckPt 2 25 = some (502826453081513961352541, 865831004508598810275406) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 26)`. -/
theorem ckPt_2_26 : ckPt 2 26 = some (154295998296153823222290, 534680496377855458304038) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 27)`. -/
theorem ckPt_2_27 : ckPt 2 27 = some (146519345985670110282978, 176538855582945509384276) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 28)`. -/
theorem ckPt_2_28 : ckPt 2 28 = some (217524463828610815772414, 306313729072022601085676) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 29)`. -/
theorem ckPt_2_29 : ckPt 2 29 = some (522714887622762674589417, 480267648577256887370588) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 30)`. -/
theorem ckPt_2_30 : ckPt 2 30 = some (44875778457124028109680, 399912038321830031520411) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(2, 31)`. -/
theorem ckPt_2_31 : ckPt 2 31 = some (228390489117748856600037, 848690475492071147466921) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 0)`. -/
theorem ckPt_3_0 : ckPt 3 0 = some (188270282321881391486733, 930504722719701238055592) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 1)`. -/
theorem ckPt_3_1 : ckPt 3 1 = some (28671822753334740196728, 790113094535436210936045) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 2)`. -/
theorem ckPt_3_2 : ckPt 3 2 = some (329287242113289954938045, 381264739777728422609697) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 3)`. -/
theorem ckPt_3_3 : ckPt 3 3 = some (351040545991173268088876, 849837557547845182407448) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 4)`. -/
theorem ckPt_3_4 : ckPt 3 4 = some (44466739112624035885044, 716251812812634719898445) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 5)`. -/
theorem ckPt_3_5 : ckPt 3 5 = some (106932364468019720157648, 3712367108157242291333) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 6)`. -/
theorem ckPt_3_6 : ckPt 3 6 = some (635204137894572153674190, 614408049346373679668299) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 7)`. -/
theorem ckPt_3_7 : ckPt 3 7 = some (394762910042448965658075, 1058892020759371878951637) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 8)`. -/
theorem ckPt_3_8 : ckPt 3 8 = some (158537957522885778741622, 1307507638979279472957341) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 9)`. -/
theorem ckPt_3_9 : ckPt 3 9 = some (54792687091554762292951, 1189339662532716541426480) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 10)`. -/
theorem ckPt_3_10 : ckPt 3 10 = some (342423298253329668555397, 745688632502953197764369) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 11)`. -/
theorem ckPt_3_11 : ckPt 3 11 = some (68861212593480756171471, 827724703099386357830157) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 12)`. -/
theorem ckPt_3_12 : ckPt 3 12 = some (9923085999408660584495, 604505063073370201769223) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 13)`. -/
theorem ckPt_3_13 : ckPt 3 13 = some (92853127359347383732641, 101442596319180197652125) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 14)`. -/
theorem ckPt_3_14 : ckPt 3 14 = some (666202058542571092588188, 1261097944298194483918227) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 15)`. -/
theorem ckPt_3_15 : ckPt 3 15 = some (395241364804930117447586, 1237924128186863394122970) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 16)`. -/
theorem ckPt_3_16 : ckPt 3 16 = some (188254669104996756414102, 930496822070192839754933) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 17)`. -/
theorem ckPt_3_17 : ckPt 3 17 = some (28704057294738916089426, 790108373011973301142366) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 18)`. -/
theorem ckPt_3_18 : ckPt 3 18 = some (329286322855838427836182, 381279523053771455921539) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 19)`. -/
theorem ckPt_3_19 : ckPt 3 19 = some (351055096486464831142411, 849808829414254362615018) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 20)`. -/
theorem ckPt_3_20 : ckPt 3 20 = some (44436117039358652866303, 716215872295221044749394) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 21)`. -/
theorem ckPt_3_21 : ckPt 3 21 = some (106891121410261383165510, 3713974757518598388524) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 22)`. -/
theorem ckPt_3_22 : ckPt 3 22 = some (635190116887711546604952, 614435185080292327277362) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 23)`. -/
theorem ckPt_3_23 : ckPt 3 23 = some (394782559760531643560802, 1058921745687241256345776) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 24)`. -/
theorem ckPt_3_24 : ckPt 3 24 = some (158541714265716481512356, 1307533173041690078667669) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 25)`. -/
theorem ckPt_3_25 : ckPt 3 25 = some (54788056271782134183803, 1189357484849327345592696) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 26)`. -/
theorem ckPt_3_26 : ckPt 3 26 = some (342397748484078146029242, 745704997060460502410772) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 27)`. -/
theorem ckPt_3_27 : ckPt 3 27 = some (68858328424127423486462, 827721450557481090450437) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 28)`. -/
theorem ckPt_3_28 : ckPt 3 28 = some (9891538431541293564783, 604557972179889416248359) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 29)`. -/
theorem ckPt_3_29 : ckPt 3 29 = some (92879607746011008589965, 101453799894756757123894) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 30)`. -/
theorem ckPt_3_30 : ckPt 3 30 = some (666247072123675960066850, 1261086197674534298756762) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(3, 31)`. -/
theorem ckPt_3_31 : ckPt 3 31 = some (395254361939960709280963, 1237926530451148558483394) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
