/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 12 and 13

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(12, 0)`. -/
theorem ckPt_12_0 : ckPt 12 0 = some (195608727422153694598549, 1125723493050203482956577) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 1)`. -/
theorem ckPt_12_1 : ckPt 12 1 = some (188329788314658245614687, 664544734097032094588879) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 2)`. -/
theorem ckPt_12_2 : ckPt 12 2 = some (211806148364593203565352, 192031949404447058416993) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 3)`. -/
theorem ckPt_12_3 : ckPt 12 3 = some (369115657141768090919995, 797215682117928611394481) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 4)`. -/
theorem ckPt_12_4 : ckPt 12 4 = some (258717092987328416601091, 126179293582116942897308) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 5)`. -/
theorem ckPt_12_5 : ckPt 12 5 = some (307331894490677415022849, 150484512356429446066073) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 6)`. -/
theorem ckPt_12_6 : ckPt 12 6 = some (565057324222603981756573, 548443855997980549710538) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 7)`. -/
theorem ckPt_12_7 : ckPt 12 7 = some (307940616208943923478838, 625488484153860159061147) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 8)`. -/
theorem ckPt_12_8 : ckPt 12 8 = some (367810515435525987079811, 1238075830762628698768956) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 9)`. -/
theorem ckPt_12_9 : ckPt 12 9 = some (428816809019728964106068, 1411869253550727043154044) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 10)`. -/
theorem ckPt_12_10 : ckPt 12 10 = some (120973329462626519408059, 213197434256682036857595) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 11)`. -/
theorem ckPt_12_11 : ckPt 12 11 = some (426918148254177278639000, 938787937782325250402999) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 12)`. -/
theorem ckPt_12_12 : ckPt 12 12 = some (275573003916499251052780, 442563835284764464360987) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 13)`. -/
theorem ckPt_12_13 : ckPt 12 13 = some (397942832140755777667857, 138613875385537966385898) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 14)`. -/
theorem ckPt_12_14 : ckPt 12 14 = some (619040774415514130628630, 695584941693744245385837) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 15)`. -/
theorem ckPt_12_15 : ckPt 12 15 = some (209596829269288944768385, 1031996286855149482628062) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 16)`. -/
theorem ckPt_12_16 : ckPt 12 16 = some (195619109178503652212564, 1125768271023191509807084) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 17)`. -/
theorem ckPt_12_17 : ckPt 12 17 = some (188338785246554071391836, 664574187833703283692807) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 18)`. -/
theorem ckPt_12_18 : ckPt 12 18 = some (211761781836775024069186, 192012909994185895759273) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 19)`. -/
theorem ckPt_12_19 : ckPt 12 19 = some (369120174445605583440437, 797180902144962679184229) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 20)`. -/
theorem ckPt_12_20 : ckPt 12 20 = some (258708899099230193167248, 126189273000341444901135) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 21)`. -/
theorem ckPt_12_21 : ckPt 12 21 = some (307320764291646018237414, 150449903430999925783259) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 22)`. -/
theorem ckPt_12_22 : ckPt 12 22 = some (565021648636868292050470, 548427656031431123186944) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 23)`. -/
theorem ckPt_12_23 : ckPt 12 23 = some (307945026661858510311438, 625482573018475962129070) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 24)`. -/
theorem ckPt_12_24 : ckPt 12 24 = some (367788431308349600962661, 1238056286949681303125438) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 25)`. -/
theorem ckPt_12_25 : ckPt 12 25 = some (428797710893241872987609, 1411834367726505147452822) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 26)`. -/
theorem ckPt_12_26 : ckPt 12 26 = some (120964981459944056856733, 213176626450820637759804) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 27)`. -/
theorem ckPt_12_27 : ckPt 12 27 = some (426878171706204115198738, 938776942370292529299509) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 28)`. -/
theorem ckPt_12_28 : ckPt 12 28 = some (275565269423267715773971, 442558262589003849666189) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 29)`. -/
theorem ckPt_12_29 : ckPt 12 29 = some (397957502522699064843118, 138546322530256873015302) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 30)`. -/
theorem ckPt_12_30 : ckPt 12 30 = some (619064650683171958822031, 695572758805836443250379) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(12, 31)`. -/
theorem ckPt_12_31 : ckPt 12 31 = some (209584334388140022679901, 1031956873532348219182954) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 0)`. -/
theorem ckPt_13_0 : ckPt 13 0 = some (159427110922180160244057, 1310423798260429197956790) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 1)`. -/
theorem ckPt_13_1 : ckPt 13 1 = some (395552051392052785019444, 1060754085001587815408857) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 2)`. -/
theorem ckPt_13_2 : ckPt 13 2 = some (635683775194354959175913, 614906699348547622636735) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 3)`. -/
theorem ckPt_13_3 : ckPt 13 3 = some (106638288044291524234031, 4648164005924414047125) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 4)`. -/
theorem ckPt_13_4 : ckPt 13 4 = some (44106008703628244118901, 718652511155586568590208) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 5)`. -/
theorem ckPt_13_5 : ckPt 13 5 = some (351600358823338376437934, 853847573009478315755946) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 6)`. -/
theorem ckPt_13_6 : ckPt 13 6 = some (329969817788371204893767, 386940607511227997805703) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 7)`. -/
theorem ckPt_13_7 : ckPt 13 7 = some (29438118606290826320704, 797577875059554768261902) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 8)`. -/
theorem ckPt_13_8 : ckPt 13 8 = some (187210609418587085643902, 939994757974501194553711) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 9)`. -/
theorem ckPt_13_9 : ckPt 13 9 = some (394022592618420901630587, 1249393738035365224599416) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 10)`. -/
theorem ckPt_13_10 : ckPt 13 10 = some (665405855508609725438026, 1272823271671197884110665) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 11)`. -/
theorem ckPt_13_11 : ckPt 13 11 = some (92462659635289965049703, 109552656076499595281949) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 12)`. -/
theorem ckPt_13_12 : ckPt 13 12 = some (11339638114755592854258, 602040008273358241414970) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 13)`. -/
theorem ckPt_13_13 : ckPt 13 13 = some (70080837453196721304668, 828817878082579695311717) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 14)`. -/
theorem ckPt_13_14 : ckPt 13 14 = some (342733568709753795380208, 748464216886930067873751) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 15)`. -/
theorem ckPt_13_15 : ckPt 13 15 = some (54281539080501315598702, 1192663901894270034152573) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 16)`. -/
theorem ckPt_13_16 : ckPt 13 16 = some (159416579243540425034333, 1310496401042838884139548) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 17)`. -/
theorem ckPt_13_17 : ckPt 13 17 = some (395551743059930057629877, 1060836398961989448699018) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 18)`. -/
theorem ckPt_13_18 : ckPt 13 18 = some (635665548357964746412034, 614951049699304433875144) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 19)`. -/
theorem ckPt_13_19 : ckPt 13 19 = some (106612245516368056540005, 4633895715237169697777) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 20)`. -/
theorem ckPt_13_20 : ckPt 13 20 = some (44074394794227725981140, 718618569165487226067427) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 21)`. -/
theorem ckPt_13_21 : ckPt 13 21 = some (351600360026178390408565, 853808928002405499234833) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 22)`. -/
theorem ckPt_13_22 : ckPt 13 22 = some (329958981269847558407838, 386947500069712738602810) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 23)`. -/
theorem ckPt_13_23 : ckPt 13 23 = some (29455388575119594230616, 797559106967020343477447) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 24)`. -/
theorem ckPt_13_24 : ckPt 13 24 = some (187219116732347525968186, 939975337775515861616607) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 25)`. -/
theorem ckPt_13_25 : ckPt 13 25 = some (394017705262770472172529, 1249373285469659121843655) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 26)`. -/
theorem ckPt_13_26 : ckPt 13 26 = some (665392325115803813320338, 1272792589779071509880503) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 27)`. -/
theorem ckPt_13_27 : ckPt 13 27 = some (92460530845261566622408, 109552094035605289890772) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 28)`. -/
theorem ckPt_13_28 : ckPt 13 28 = some (11297968609775182184701, 602021630982877979166565) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 29)`. -/
theorem ckPt_13_29 : ckPt 13 29 = some (70081360782197328252625, 828826615330036207391241) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 30)`. -/
theorem ckPt_13_30 : ckPt 13 30 = some (342730198320016977072875, 748398064232670612404701) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(13, 31)`. -/
theorem ckPt_13_31 : ckPt 13 31 = some (54253313752185745450418, 1192599039026049642100260) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
