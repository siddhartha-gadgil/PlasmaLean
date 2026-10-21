/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 4 and 5

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(4, 0)`. -/
theorem ckPt_4_0 : ckPt 4 0 = some (358258090317485896626433, 1228684158489953837032358) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 1)`. -/
theorem ckPt_4_1 : ckPt 4 1 = some (299355897904557202207507, 619634991296056538225716) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 2)`. -/
theorem ckPt_4_2 : ckPt 4 2 = some (556463613367235606262721, 546389428156134329166394) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 3)`. -/
theorem ckPt_4_3 : ckPt 4 3 = some (298613645203583843465776, 149217741721274940187035) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 4)`. -/
theorem ckPt_4_4 : ckPt 4 4 = some (267374073369748881492352, 130323846497235401030790) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 5)`. -/
theorem ckPt_4_5 : ckPt 4 5 = some (377757280847476687604860, 803784179816825943569108) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 6)`. -/
theorem ckPt_4_6 : ckPt 4 6 = some (203127729029636845959772, 200514808249002027178658) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 7)`. -/
theorem ckPt_4_7 : ckPt 4 7 = some (196874830552599374099027, 654345895597146192180154) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 8)`. -/
theorem ckPt_4_8 : ckPt 4 8 = some (204013774287089220945892, 1113491308962377019604187) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 9)`. -/
theorem ckPt_4_9 : ckPt 4 9 = some (218310595733748916744440, 1017346522452775896549816) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 10)`. -/
theorem ckPt_4_10 : ckPt 4 10 = some (628886704219244323951598, 678460407687585053681214) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 11)`. -/
theorem ckPt_4_11 : ckPt 4 11 = some (409764092427560728384308, 119760468816490221423371) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 12)`. -/
theorem ckPt_4_12 : ckPt 4 12 = some (289595584929724442677242, 425949934447284492310750) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 13)`. -/
theorem ckPt_4_13 : ckPt 4 13 = some (412352635244475481498275, 932550750456233750797483) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 14)`. -/
theorem ckPt_4_14 : ckPt 4 14 = some (107800739637721638416669, 206989188886274539534183) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 15)`. -/
theorem ckPt_4_15 : ckPt 4 15 = some (417520555415336051273991, 1400964068478411689619084) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 16)`. -/
theorem ckPt_4_16 : ckPt 4 16 = some (358243528055170437023961, 1228687513128483166256343) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 17)`. -/
theorem ckPt_4_17 : ckPt 4 17 = some (299352674765661772247162, 619652532512140515541187) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 18)`. -/
theorem ckPt_4_18 : ckPt 4 18 = some (556427735318258562449890, 546403724923124987436861) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 19)`. -/
theorem ckPt_4_19 : ckPt 4 19 = some (298597700347713356099866, 149161515257335130274503) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 20)`. -/
theorem ckPt_4_20 : ckPt 4 20 = some (267367683185001353430479, 130362894151296107623022) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 21)`. -/
theorem ckPt_4_21 : ckPt 4 21 = some (377752189165040993538257, 803764694633879168247661) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 22)`. -/
theorem ckPt_4_22 : ckPt 4 22 = some (203090123856790641192491, 200526510343708378803412) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 23)`. -/
theorem ckPt_4_23 : ckPt 4 23 = some (196870709967291359888392, 654346925283630449390895) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 24)`. -/
theorem ckPt_4_24 : ckPt 4 24 = some (204023995349684110747400, 1113489656189155740758783) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 25)`. -/
theorem ckPt_4_25 : ckPt 4 25 = some (218317242561239012827125, 1017340102500408307360912) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 26)`. -/
theorem ckPt_4_26 : ckPt 4 26 = some (628882979351819139372015, 678447655220382489248546) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 27)`. -/
theorem ckPt_4_27 : ckPt 4 27 = some (409800220580317891508000, 119745286685572294740804) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 28)`. -/
theorem ckPt_4_28 : ckPt 4 28 = some (289606823888900551628496, 425909613774569744428598) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 29)`. -/
theorem ckPt_4_29 : ckPt 4 29 = some (412334099110630403701074, 932607955305138221898344) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 30)`. -/
theorem ckPt_4_30 : ckPt 4 30 = some (107780486620345383503609, 206997537455367154512463) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(4, 31)`. -/
theorem ckPt_4_31 : ckPt 4 31 = some (417554882655053397102902, 1400980795673985259118580) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 0)`. -/
theorem ckPt_5_0 : ckPt 5 0 = some (348933794148685925419324, 357910625709705436147698) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 1)`. -/
theorem ckPt_5_1 : ckPt 5 1 = some (30203247837669095974053, 156920471755231264699703) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 2)`. -/
theorem ckPt_5_2 : ckPt 5 2 = some (735525492457206836135917, 33724253492992654321144) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 3)`. -/
theorem ckPt_5_3 : ckPt 5 3 = some (24971090051725145996677, 384335662310506468768380) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 4)`. -/
theorem ckPt_5_4 : ckPt 5 4 = some (721396211151160850188915, 61232960938195933656980) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 5)`. -/
theorem ckPt_5_5 : ckPt 5 5 = some (221921022041399068125648, 555477185389408168822379) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 6)`. -/
theorem ckPt_5_6 : ckPt 5 6 = some (642891244942388721636591, 82751839636703388327409) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 7)`. -/
theorem ckPt_5_7 : ckPt 5 7 = some (184826531946675905858597, 171088908111543247343745) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 8)`. -/
theorem ckPt_5_8 : ckPt 5 8 = some (79981172115294159099769, 332392973666949433790475) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 9)`. -/
theorem ckPt_5_9 : ckPt 5 9 = some (73555051696031752388336, 319520487514684084656587) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 10)`. -/
theorem ckPt_5_10 : ckPt 5 10 = some (233885363652550861418186, 225265921695793934773363) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 11)`. -/
theorem ckPt_5_11 : ckPt 5 11 = some (581192907236654200685118, 189570131789776262908870) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 12)`. -/
theorem ckPt_5_12 : ckPt 5 12 = some (1056066186115091256337416, 170942347670591989890028) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 13)`. -/
theorem ckPt_5_13 : ckPt 5 13 = some (600728279130126784676577, 399195174306568108133067) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 14)`. -/
theorem ckPt_5_14 : ckPt 5 14 = some (1305938290948301013166322, 75104061527284475649450) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 15)`. -/
theorem ckPt_5_15 : ckPt 5 15 = some (990856931431443159925405, 464182329791743809111025) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 16)`. -/
theorem ckPt_5_16 : ckPt 5 16 = some (348904111657615333295183, 357931882554532016640671) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 17)`. -/
theorem ckPt_5_17 : ckPt 5 17 = some (30179018350374558114691, 156946607958539686354089) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 18)`. -/
theorem ckPt_5_18 : ckPt 5 18 = some (735438228959505988150879, 33712093588146239381483) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 19)`. -/
theorem ckPt_5_19 : ckPt 5 19 = some (25001009532586714850235, 384322916977113464587349) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 20)`. -/
theorem ckPt_5_20 : ckPt 5 20 = some (721378291223944546147874, 61214508181026324709213) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 21)`. -/
theorem ckPt_5_21 : ckPt 5 21 = some (221930781182934645620561, 555427229186792891905175) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 22)`. -/
theorem ckPt_5_22 : ckPt 5 22 = some (642848459680993669794432, 82742622621780140480224) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 23)`. -/
theorem ckPt_5_23 : ckPt 5 23 = some (184822227522516661350888, 171083337790433084610273) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 24)`. -/
theorem ckPt_5_24 : ckPt 5 24 = some (79955882124256612161125, 332393499298648776227948) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 25)`. -/
theorem ckPt_5_25 : ckPt 5 25 = some (73534878782715931055116, 319521963131242703447132) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 26)`. -/
theorem ckPt_5_26 : ckPt 5 26 = some (233897342511239704856676, 225253024852649677220675) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 27)`. -/
theorem ckPt_5_27 : ckPt 5 27 = some (581158755889497820406670, 189555781565813020039661) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 28)`. -/
theorem ckPt_5_28 : ckPt 5 28 = some (1056096216246949220467853, 170963024941679803541370) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 29)`. -/
theorem ckPt_5_29 : ckPt 5 29 = some (600713029328161607118754, 399254842640156507757084) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 30)`. -/
theorem ckPt_5_30 : ckPt 5 30 = some (1306024641422340141647918, 75051973256801062205197) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(5, 31)`. -/
theorem ckPt_5_31 : ckPt 5 31 = some (990917245043856393007839, 464153243617035122733825) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
