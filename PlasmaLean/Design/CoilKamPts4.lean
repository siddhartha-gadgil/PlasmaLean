/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 8 and 9

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(8, 0)`. -/
theorem ckPt_8_0 : ckPt 8 0 = some (504392988503823521610879, 24886184229518919549666) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 1)`. -/
theorem ckPt_8_1 : ckPt 8 1 = some (82987113051503527584318, 22097814164793812161584) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 2)`. -/
theorem ckPt_8_2 : ckPt 8 2 = some (326173751628852582230795, 581804533527122268723327) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 3)`. -/
theorem ckPt_8_3 : ckPt 8 3 = some (1143633192180105770767851, 279213781725641281808471) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 4)`. -/
theorem ckPt_8_4 : ckPt 8 4 = some (7513912069731895946445, 111931277735024882131949) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 5)`. -/
theorem ckPt_8_5 : ckPt 8 5 = some (1153176008761413329446067, 272990960198325578847991) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 6)`. -/
theorem ckPt_8_6 : ckPt 8 6 = some (332431894996666614491021, 570917708974018099598934) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 7)`. -/
theorem ckPt_8_7 : ckPt 8 7 = some (55746043342862447684174, 30850312760591162545368) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 8)`. -/
theorem ckPt_8_8 : ckPt 8 8 = some (467367114483208632561388, 21277184226177790092993) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 9)`. -/
theorem ckPt_8_9 : ckPt 8 9 = some (212441584636523882564715, 114743787277676243341643) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 10)`. -/
theorem ckPt_8_10 : ckPt 8 10 = some (227443098856069164891796, 724689631607691440914291) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 11)`. -/
theorem ckPt_8_11 : ckPt 8 11 = some (829834962350669309824156, 94463218706194716625825) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 12)`. -/
theorem ckPt_8_12 : ckPt 8 12 = some (15547881621015520088547, 155317388671082457836393) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 13)`. -/
theorem ckPt_8_13 : ckPt 8 13 = some (861409372924700596130180, 94660202951733681858106) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 14)`. -/
theorem ckPt_8_14 : ckPt 8 14 = some (260821965340257207361818, 724889385886289162143498) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 15)`. -/
theorem ckPt_8_15 : ckPt 8 15 = some (248649448776076479775957, 114097511191504330913441) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 16)`. -/
theorem ckPt_8_16 : ckPt 8 16 = some (504313931227663746750613, 24871020293395068804328) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 17)`. -/
theorem ckPt_8_17 : ckPt 8 17 = some (82987609105823810500788, 22094771622876023627641) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 18)`. -/
theorem ckPt_8_18 : ckPt 8 18 = some (326134685931860097576482, 581763978510851068164500) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 19)`. -/
theorem ckPt_8_19 : ckPt 8 19 = some (1143599685604492890237363, 279183201104295715486747) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 20)`. -/
theorem ckPt_8_20 : ckPt 8 20 = some (7502629459004281595775, 111916403504180129453279) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 21)`. -/
theorem ckPt_8_21 : ckPt 8 21 = some (1153091956681603341725549, 272968823505997045929095) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 22)`. -/
theorem ckPt_8_22 : ckPt 8 22 = some (332430177685058200494807, 570892847000346026306898) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 23)`. -/
theorem ckPt_8_23 : ckPt 8 23 = some (55714125788493364909196, 30844524459356550047659) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 24)`. -/
theorem ckPt_8_24 : ckPt 8 24 = some (467311779461019332006039, 21275139639242254136885) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 25)`. -/
theorem ckPt_8_25 : ckPt 8 25 = some (212414378946331531577965, 114753220436015742394755) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 26)`. -/
theorem ckPt_8_26 : ckPt 8 26 = some (227406791595676370911312, 724678039235249222980650) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 27)`. -/
theorem ckPt_8_27 : ckPt 8 27 = some (829807246903162387806395, 94491398690239659503201) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 28)`. -/
theorem ckPt_8_28 : ckPt 8 28 = some (15564882649622266811065, 155340528614705598542415) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 29)`. -/
theorem ckPt_8_29 : ckPt 8 29 = some (861494473538566972136232, 94678717227043533918472) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 30)`. -/
theorem ckPt_8_30 : ckPt 8 30 = some (260845007430788928669235, 724918247113506586760516) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(8, 31)`. -/
theorem ckPt_8_31 : ckPt 8 31 = some (248697056951939130859178, 114088758659138708762774) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 0)`. -/
theorem ckPt_9_0 : ckPt 9 0 = some (202011254936905103883536, 314441694920697788968320) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 1)`. -/
theorem ckPt_9_1 : ckPt 9 1 = some (99040273145517352372013, 253351528909245071364937) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 2)`. -/
theorem ckPt_9_2 : ckPt 9 2 = some (277053387457951843695779, 740732572532172622865572) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 3)`. -/
theorem ckPt_9_3 : ckPt 9 3 = some (43020779408088373147659, 564181902670978508408655) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 4)`. -/
theorem ckPt_9_4 : ckPt 9 4 = some (1127443545254502672953878, 842737251146785731124150) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 5)`. -/
theorem ckPt_9_5 : ckPt 9 5 = some (703539611484850374502762, 673440179779990973178293) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 6)`. -/
theorem ckPt_9_6 : ckPt 9 6 = some (307304367711724263908338, 1562326693293016569516762) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 7)`. -/
theorem ckPt_9_7 : ckPt 9 7 = some (73139467649805298164422, 235877003035120415417087) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 8)`. -/
theorem ckPt_9_8 : ckPt 9 8 = some (576047064547537674082959, 496551214269070056594835) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 9)`. -/
theorem ckPt_9_9 : ckPt 9 9 = some (206506133860086023102846, 812784330726069910581150) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 10)`. -/
theorem ckPt_9_10 : ckPt 9 10 = some (129853485503022446621739, 1049911532227712996424512) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 11)`. -/
theorem ckPt_9_11 : ckPt 9 11 = some (30771610089239336018577, 326342896765267066936794) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 12)`. -/
theorem ckPt_9_12 : ckPt 9 12 = some (592978639545989559434646, 421651555081629869757249) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 13)`. -/
theorem ckPt_9_13 : ckPt 9 13 = some (654974232670019212436815, 121677689753527098237713) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 14)`. -/
theorem ckPt_9_14 : ckPt 9 14 = some (153209887299289348126282, 439064974972066861009275) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 15)`. -/
theorem ckPt_9_15 : ckPt 9 15 = some (12628517018261955137642, 176806386787687222425890) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 16)`. -/
theorem ckPt_9_16 : ckPt 9 16 = some (202000283201371622634528, 314405731677650592605313) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 17)`. -/
theorem ckPt_9_17 : ckPt 9 17 = some (99014483564372328076747, 253340351168259403098197) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 18)`. -/
theorem ckPt_9_18 : ckPt 9 18 = some (277035305056285993506170, 740690496924197036009111) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 19)`. -/
theorem ckPt_9_19 : ckPt 9 19 = some (43001534980410450480698, 564153338021680358656275) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 20)`. -/
theorem ckPt_9_20 : ckPt 9 20 = some (1127389028104564366424592, 842683090002343438875315) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 21)`. -/
theorem ckPt_9_21 : ckPt 9 21 = some (703488866712119964136791, 673404979538392160166182) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 22)`. -/
theorem ckPt_9_22 : ckPt 9 22 = some (307284288905545173244934, 1562266658813737340773864) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 23)`. -/
theorem ckPt_9_23 : ckPt 9 23 = some (73126678351273107742644, 235890843339287796091784) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 24)`. -/
theorem ckPt_9_24 : ckPt 9 24 = some (576030661884252648072337, 496518280204087536346911) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 25)`. -/
theorem ckPt_9_25 : ckPt 9 25 = some (206488549953078330518656, 812760023798759595254772) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 26)`. -/
theorem ckPt_9_26 : ckPt 9 26 = some (129846829100578045761521, 1049875740398605318074488) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 27)`. -/
theorem ckPt_9_27 : ckPt 9 27 = some (30763334801194611440067, 326338660130614911420437) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 28)`. -/
theorem ckPt_9_28 : ckPt 9 28 = some (592976082549219982055965, 421706488703141559885060) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 29)`. -/
theorem ckPt_9_29 : ckPt 9 29 = some (655005629614900599091739, 121685389138530926538427) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 30)`. -/
theorem ckPt_9_30 : ckPt 9 30 = some (153241114399239701531184, 439053015425466051380858) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(9, 31)`. -/
theorem ckPt_9_31 : ckPt 9 31 = some (12624903936875254761834, 176843391748704787915641) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
