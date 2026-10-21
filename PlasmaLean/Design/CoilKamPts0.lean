/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 0 and 1

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(0, 0)`. -/
theorem ckPt_0_0 : ckPt 0 0 = some (908636140092835716337740, 7710826189001417238696) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 1)`. -/
theorem ckPt_0_1 : ckPt 0 1 = some (836358770727593954488977, 107794937756096387799597) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 2)`. -/
theorem ckPt_0_2 : ckPt 0 2 = some (771734260731463491731478, 106936069914797452230792) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 3)`. -/
theorem ckPt_0_3 : ckPt 0 3 = some (231321642340932293063540, 227405261317274757915363) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 4)`. -/
theorem ckPt_0_4 : ckPt 0 4 = some (1627348871305867002567, 375158856332465004350036) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 5)`. -/
theorem ckPt_0_5 : ckPt 0 5 = some (234491972043410026437667, 227059518222643050347011) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 6)`. -/
theorem ckPt_0_6 : ckPt 0 6 = some (774805115845572786428451, 107505381964676875536492) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 7)`. -/
theorem ckPt_0_7 : ckPt 0 7 = some (839336417066556520289617, 107137622626471933100164) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 8)`. -/
theorem ckPt_0_8 : ckPt 0 8 = some (911482232090427184612409, 7123875502878349506901) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 9)`. -/
theorem ckPt_0_9 : ckPt 0 9 = some (619110469512112061975152, 42441080104862718000266) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 10)`. -/
theorem ckPt_0_10 : ckPt 0 10 = some (259656943669044949281868, 96081137414852438741888) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 11)`. -/
theorem ckPt_0_11 : ckPt 0 11 = some (40871337175643381225290, 365817016592063980649122) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 12)`. -/
theorem ckPt_0_12 : ckPt 0 12 = some (1084796947239647831789, 324135994456675003413966) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 13)`. -/
theorem ckPt_0_13 : ckPt 0 13 = some (43055760458964423260932, 365680710875596856878401) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 14)`. -/
theorem ckPt_0_14 : ckPt 0 14 = some (257282020794090465398359, 96345612583494078935694) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 15)`. -/
theorem ckPt_0_15 : ckPt 0 15 = some (616527902875588416647177, 41998176499061217123079) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 16)`. -/
theorem ckPt_0_16 : ckPt 0 16 = some (908700637225961229549562, 7713512090081341068963) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 17)`. -/
theorem ckPt_0_17 : ckPt 0 17 = some (836411950369717378722037, 107789205401668755017728) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 18)`. -/
theorem ckPt_0_18 : ckPt 0 18 = some (771805962008838710175280, 106908444624980037067262) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 19)`. -/
theorem ckPt_0_19 : ckPt 0 19 = some (231382185095225794717880, 227400967268180676230255) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 20)`. -/
theorem ckPt_0_20 : ckPt 0 20 = some (1621056571424821376277, 375137794750909480459738) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 21)`. -/
theorem ckPt_0_21 : ckPt 0 21 = some (234558742692163027611964, 227055230322887355969989) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 22)`. -/
theorem ckPt_0_22 : ckPt 0 22 = some (774838467151266244253090, 107487192331883351296791) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 23)`. -/
theorem ckPt_0_23 : ckPt 0 23 = some (839363835014474281931571, 107134506812345528512536) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 24)`. -/
theorem ckPt_0_24 : ckPt 0 24 = some (911503524072189542282666, 7128954719721080656419) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 25)`. -/
theorem ckPt_0_25 : ckPt 0 25 = some (619109177572530619994307, 42432360526687855382739) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 26)`. -/
theorem ckPt_0_26 : ckPt 0 26 = some (259663724983214085460032, 96072646764399367898673) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 27)`. -/
theorem ckPt_0_27 : ckPt 0 27 = some (40871786576782240613557, 365789893471463105742906) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 28)`. -/
theorem ckPt_0_28 : ckPt 0 28 = some (1074449112547782235815, 324156701493401449687373) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 29)`. -/
theorem ckPt_0_29 : ckPt 0 29 = some (43099015919708986137344, 365672931880148943707252) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 30)`. -/
theorem ckPt_0_30 : ckPt 0 30 = some (257266896249734529028591, 96370771317259317303222) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(0, 31)`. -/
theorem ckPt_0_31 : ckPt 0 31 = some (616494892598904071355428, 41994227087696349167006) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 0)`. -/
theorem ckPt_1_0 : ckPt 1 0 = some (392484708210682721753932, 210091708176640341427434) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 1)`. -/
theorem ckPt_1_1 : ckPt 1 1 = some (672315157162169375385113, 83141481140227792364635) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 2)`. -/
theorem ckPt_1_2 : ckPt 1 2 = some (787251758928157614155712, 228527248908111488609319) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 3)`. -/
theorem ckPt_1_3 : ckPt 1 3 = some (831673380109622850139587, 173962563634050154263089) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 4)`. -/
theorem ckPt_1_4 : ckPt 1 4 = some (101856668051498155324919, 203786045437554443718326) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 5)`. -/
theorem ckPt_1_5 : ckPt 1 5 = some (626312790588783800153811, 189713418000915693773038) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 6)`. -/
theorem ckPt_1_6 : ckPt 1 6 = some (484002086795499599631258, 761364184407544927495130) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 7)`. -/
theorem ckPt_1_7 : ckPt 1 7 = some (589411959261129075227703, 648032883678372797310533) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 8)`. -/
theorem ckPt_1_8 : ckPt 1 8 = some (588205186942621975699668, 380411485116263846694975) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 9)`. -/
theorem ckPt_1_9 : ckPt 1 9 = some (627542756149376532808658, 92214679068044189037811) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 10)`. -/
theorem ckPt_1_10 : ckPt 1 10 = some (578913727322174908986481, 231867220933032474583212) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 11)`. -/
theorem ckPt_1_11 : ckPt 1 11 = some (337908281902888908842209, 87652577159838404791705) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 12)`. -/
theorem ckPt_1_12 : ckPt 1 12 = some (1852662409736927430257, 55821470945501410148659) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 13)`. -/
theorem ckPt_1_13 : ckPt 1 13 = some (424676631461539898520643, 171129332101876646474841) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 14)`. -/
theorem ckPt_1_14 : ckPt 1 14 = some (295263694138871515610071, 727201103977512223494697) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 15)`. -/
theorem ckPt_1_15 : ckPt 1 15 = some (330982700608411670539301, 455519535575701212091928) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 16)`. -/
theorem ckPt_1_16 : ckPt 1 16 = some (392503108117282697889604, 210093664131325686029397) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 17)`. -/
theorem ckPt_1_17 : ckPt 1 17 = some (672361875868205224461991, 83128308900637557777179) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 18)`. -/
theorem ckPt_1_18 : ckPt 1 18 = some (787272741092861208565214, 228511288676297772151280) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 19)`. -/
theorem ckPt_1_19 : ckPt 1 19 = some (831675743328069343868253, 173943983923830472049982) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 20)`. -/
theorem ckPt_1_20 : ckPt 1 20 = some (101833183590970302461369, 203752400868330396966262) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 21)`. -/
theorem ckPt_1_21 : ckPt 1 21 = some (626330367817896354362995, 189723838137159123310914) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 22)`. -/
theorem ckPt_1_22 : ckPt 1 22 = some (484067008906534466231902, 761371402906651350454028) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 23)`. -/
theorem ckPt_1_23 : ckPt 1 23 = some (589444830442664603682206, 648058182950046219756997) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 24)`. -/
theorem ckPt_1_24 : ckPt 1 24 = some (588225115410354132191606, 380425397818036837296405) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 25)`. -/
theorem ckPt_1_25 : ckPt 1 25 = some (627557319088497734194724, 92224209396843386299062) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 26)`. -/
theorem ckPt_1_26 : ckPt 1 26 = some (578903205480005254139786, 231844179892857433003205) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 27)`. -/
theorem ckPt_1_27 : ckPt 1 27 = some (337910364376729759343202, 87639057781515260767895) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 28)`. -/
theorem ckPt_1_28 : ckPt 1 28 = some (1847292795898980914995, 55781275516313494746389) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 29)`. -/
theorem ckPt_1_29 : ckPt 1 29 = some (424704799093724567635721, 171138914956463878579237) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 30)`. -/
theorem ckPt_1_30 : ckPt 1 30 = some (295235904697935896287188, 727212685279328263263147) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(1, 31)`. -/
theorem ckPt_1_31 : ckPt 1 31 = some (330958783950925227024244, 455514817781611989145654) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
