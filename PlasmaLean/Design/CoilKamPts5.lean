/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 10 and 11

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(10, 0)`. -/
theorem ckPt_10_0 : ckPt 10 0 = some (226029098646709583856329, 248325222827794250201206) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 1)`. -/
theorem ckPt_10_1 : ckPt 10 1 = some (239429976421456707753900, 36548997933281682639385) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 2)`. -/
theorem ckPt_10_2 : ckPt 10 2 = some (324376929783318743954090, 143018805301320267392052) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 3)`. -/
theorem ckPt_10_3 : ckPt 10 3 = some (249830882345044462886298, 792214899978886410883337) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 4)`. -/
theorem ckPt_10_4 : ckPt 10 4 = some (559055283149087987113483, 191677811940909182113107) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 5)`. -/
theorem ckPt_10_5 : ckPt 10 5 = some (917143635650248827307106, 317583196948376838073377) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 6)`. -/
theorem ckPt_10_6 : ckPt 10 6 = some (376755969981009104066784, 482612659753570371933072) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 7)`. -/
theorem ckPt_10_7 : ckPt 10 7 = some (238830409007779834938562, 277646805332407485945657) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 8)`. -/
theorem ckPt_10_8 : ckPt 10 8 = some (606747803672296778310217, 95550913678262249460444) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 9)`. -/
theorem ckPt_10_9 : ckPt 10 9 = some (1181548205688611960151635, 264499130722920770207678) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 10)`. -/
theorem ckPt_10_10 : ckPt 10 10 = some (224241268944097473040292, 248828668134406063887714) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 11)`. -/
theorem ckPt_10_11 : ckPt 10 11 = some (257622573531097638312192, 663916934612466670148822) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 12)`. -/
theorem ckPt_10_12 : ckPt 10 12 = some (111950477713964543843239, 46318161151520139246300) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 13)`. -/
theorem ckPt_10_13 : ckPt 10 13 = some (371417424508001712712068, 350842253830254345162241) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 14)`. -/
theorem ckPt_10_14 : ckPt 10 14 = some (340927161222550390069802, 106061428117956564107275) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 15)`. -/
theorem ckPt_10_15 : ckPt 10 15 = some (130139812149901243504497, 275013963828952508975942) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 16)`. -/
theorem ckPt_10_16 : ckPt 10 16 = some (226023160898495073825287, 248334771476353971501268) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 17)`. -/
theorem ckPt_10_17 : ckPt 10 17 = some (239406017385203231770869, 36570514386326648085084) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 18)`. -/
theorem ckPt_10_18 : ckPt 10 18 = some (324357069734817453811055, 143009166009816921648522) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 19)`. -/
theorem ckPt_10_19 : ckPt 10 19 = some (249817883253294382522794, 792173016540199056105688) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 20)`. -/
theorem ckPt_10_20 : ckPt 10 20 = some (559033040345603839069618, 191652423971305682900903) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 21)`. -/
theorem ckPt_10_21 : ckPt 10 21 = some (917079426897656652163555, 317571127493451628559968) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 22)`. -/
theorem ckPt_10_22 : ckPt 10 22 = some (376747994088212403277501, 482586939107689999628043) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 23)`. -/
theorem ckPt_10_23 : ckPt 10 23 = some (238813830465599442139271, 277653397034436598267985) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 24)`. -/
theorem ckPt_10_24 : ckPt 10 24 = some (606727409071667031008860, 95518232996840138661520) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 25)`. -/
theorem ckPt_10_25 : ckPt 10 25 = some (1181506792281470465354791, 264475277861032441542148) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 26)`. -/
theorem ckPt_10_26 : ckPt 10 26 = some (224235325116160458693670, 248830131019020693957824) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 27)`. -/
theorem ckPt_10_27 : ckPt 10 27 = some (257648702094438035457340, 663888079067841643112330) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 28)`. -/
theorem ckPt_10_28 : ckPt 10 28 = some (111952119798331626808398, 46291415482387584882774) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 29)`. -/
theorem ckPt_10_29 : ckPt 10 29 = some (371434606194319376415676, 350883053321948735141071) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 30)`. -/
theorem ckPt_10_30 : ckPt 10 30 = some (340966127312979054644132, 106059529075974826923280) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(10, 31)`. -/
theorem ckPt_10_31 : ckPt 10 31 = some (130146903015884079668644, 275013641690142845969390) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 0)`. -/
theorem ckPt_11_0 : ckPt 11 0 = some (82633896786307081133516, 351682094741853263486170) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 1)`. -/
theorem ckPt_11_1 : ckPt 11 1 = some (185276439615541815575367, 190241337830305150856589) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 2)`. -/
theorem ckPt_11_2 : ckPt 11 2 = some (641157054900837988217475, 63334407186804405806291) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 3)`. -/
theorem ckPt_11_3 : ckPt 11 3 = some (225705175822885345800770, 575320115390358540910666) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 4)`. -/
theorem ckPt_11_4 : ckPt 11 4 = some (726768890341262268357488, 81471989345835685295882) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 5)`. -/
theorem ckPt_11_5 : ckPt 11 5 = some (30727133423177486693488, 364319937652352708724986) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 6)`. -/
theorem ckPt_11_6 : ckPt 11 6 = some (732066783199316142901761, 51995014467379680711087) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 7)`. -/
theorem ckPt_11_7 : ckPt 11 7 = some (30074977549490009749838, 141845631627605214288222) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 8)`. -/
theorem ckPt_11_8 : ckPt 11 8 = some (348961275702207923910027, 344986873750280762767595) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 9)`. -/
theorem ckPt_11_9 : ckPt 11 9 = some (991318756843204096816246, 450700259132676900953230) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 10)`. -/
theorem ckPt_11_10 : ckPt 11 10 = some (1303798539178706749584009, 56750485251175773844469) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 11)`. -/
theorem ckPt_11_11 : ckPt 11 11 = some (606535379991295988358609, 373236783420888331749122) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 12)`. -/
theorem ckPt_11_12 : ckPt 11 12 = some (1063923163545844988945141, 142227701853655389204770) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 13)`. -/
theorem ckPt_11_13 : ckPt 11 13 = some (589378399053157824146755, 215266114287946220100504) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 14)`. -/
theorem ckPt_11_14 : ckPt 11 14 = some (226865857744100230816893, 247586512529122590046785) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 15)`. -/
theorem ckPt_11_15 : ckPt 11 15 = some (78509572913188286767618, 339736657073371117820636) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 16)`. -/
theorem ckPt_11_16 : ckPt 11 16 = some (82630040879389112221764, 351694019825707707436658) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 17)`. -/
theorem ckPt_11_17 : ckPt 11 17 = some (185284069707542178904465, 190247869051369398677064) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 18)`. -/
theorem ckPt_11_18 : ckPt 11 18 = some (641124791928476668107307, 63323489939871677926473) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 19)`. -/
theorem ckPt_11_19 : ckPt 11 19 = some (225697777098277950389897, 575272451083108088306342) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 20)`. -/
theorem ckPt_11_20 : ckPt 11 20 = some (726737795126140079396639, 81449108385508664959209) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 21)`. -/
theorem ckPt_11_21 : ckPt 11 21 = some (30720858587662261972392, 364298130914136726795561) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 22)`. -/
theorem ckPt_11_22 : ckPt 11 22 = some (732017597677874264970527, 51982223797790214312656) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 23)`. -/
theorem ckPt_11_23 : ckPt 11 23 = some (30094382713242439781662, 141855386531930112256760) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 24)`. -/
theorem ckPt_11_24 : ckPt 11 24 = some (348940835764861816191891, 344988189860715129618027) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 25)`. -/
theorem ckPt_11_25 : ckPt 11 25 = some (991292938988932114415597, 450692841821687570266496) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 26)`. -/
theorem ckPt_11_26 : ckPt 11 26 = some (1303761412441959855720753, 56749743397833169234595) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 27)`. -/
theorem ckPt_11_27 : ckPt 11 27 = some (606528381766140505224265, 373238496197432493595184) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 28)`. -/
theorem ckPt_11_28 : ckPt 11 28 = some (1063946298314363902029678, 142278027196024998958913) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 29)`. -/
theorem ckPt_11_29 : ckPt 11 29 = some (589382781225818286417303, 215290834033019403804830) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 30)`. -/
theorem ckPt_11_30 : ckPt 11 30 = some (226898724375557963382378, 247558513250740575171378) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(11, 31)`. -/
theorem ckPt_11_31 : ckPt 11 31 = some (78516470566144035266953, 339719840250052454365416) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
