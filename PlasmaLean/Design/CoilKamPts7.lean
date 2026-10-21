/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 14 and 15

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(14, 0)`. -/
theorem ckPt_14_0 : ckPt 14 0 = some (525565150652312005981821, 1226100863478605036063431) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 1)`. -/
theorem ckPt_14_1 : ckPt 14 1 = some (239659753465863322559989, 1085722413856500669381098) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 2)`. -/
theorem ckPt_14_2 : ckPt 14 2 = some (149257862740908651370136, 326245214208066545909946) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 3)`. -/
theorem ckPt_14_3 : ckPt 14 3 = some (493539798462632337320313, 60484661555913119917201) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 4)`. -/
theorem ckPt_14_4 : ckPt 14 4 = some (418746864432749471346952, 148821378963136787136919) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 5)`. -/
theorem ckPt_14_5 : ckPt 14 5 = some (152609625497834924594612, 29747804824874691786549) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 6)`. -/
theorem ckPt_14_6 : ckPt 14 6 = some (278860457683114732688800, 652385385105345059975712) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 7)`. -/
theorem ckPt_14_7 : ckPt 14 7 = some (362545285576247674515344, 575388293298413046407293) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 8)`. -/
theorem ckPt_14_8 : ckPt 14 8 = some (402114392460029833092062, 854984497034845806895287) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 9)`. -/
theorem ckPt_14_9 : ckPt 14 9 = some (232210296452754908087210, 848921052719952965041772) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 10)`. -/
theorem ckPt_14_10 : ckPt 14 10 = some (48809841736385660648330, 400351266963324879696198) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 11)`. -/
theorem ckPt_14_11 : ckPt 14 11 = some (518772608423277044657170, 480248398637069883716196) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 12)`. -/
theorem ckPt_14_12 : ckPt 14 12 = some (213541071841440241848439, 305061367521088706361555) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 13)`. -/
theorem ckPt_14_13 : ckPt 14 13 = some (142259105799886468625635, 173969190359124185195609) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 14)`. -/
theorem ckPt_14_14 : ckPt 14 14 = some (149403976252565837150177, 538510794469154184240753) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 15)`. -/
theorem ckPt_14_15 : ckPt 14 15 = some (497364634351361729742060, 870698433833045614031233) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 16)`. -/
theorem ckPt_14_16 : ckPt 14 16 = some (525624367665045535580830, 1226177892864921312419760) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 17)`. -/
theorem ckPt_14_17 : ckPt 14 17 = some (239701516997629721255689, 1085790067053128037593920) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 18)`. -/
theorem ckPt_14_18 : ckPt 14 18 = some (149284479066159151578032, 326324411142345076698414) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 19)`. -/
theorem ckPt_14_19 : ckPt 14 19 = some (493493879829217732410966, 60534639246236536160720) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 20)`. -/
theorem ckPt_14_20 : ckPt 14 20 = some (418724651202966709025695, 148829176951389840212103) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 21)`. -/
theorem ckPt_14_21 : ckPt 14 21 = some (152633831431326453354587, 29750604304455332120793) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 22)`. -/
theorem ckPt_14_22 : ckPt 14 22 = some (278875574348790081510922, 652354932364818780186264) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 23)`. -/
theorem ckPt_14_23 : ckPt 14 23 = some (362537603146454637575487, 575386252572353810028500) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 24)`. -/
theorem ckPt_14_24 : ckPt 14 24 = some (402122347091456564161045, 854975232022257323578647) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 25)`. -/
theorem ckPt_14_25 : ckPt 14 25 = some (232201469548623977605228, 848905397345748455943094) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 26)`. -/
theorem ckPt_14_26 : ckPt 14 26 = some (48806701347191070894113, 400352485060788628062339) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 27)`. -/
theorem ckPt_14_27 : ckPt 14 27 = some (518759546802781187207590, 480231085506261928124411) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 28)`. -/
theorem ckPt_14_28 : ckPt 14 28 = some (213557270808775318875576, 305070767449516031124752) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 29)`. -/
theorem ckPt_14_29 : ckPt 14 29 = some (142220186182896301071931, 174005134202505772113238) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 30)`. -/
theorem ckPt_14_30 : ckPt 14 30 = some (149369560089831340349547, 538506995246446397186761) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(14, 31)`. -/
theorem ckPt_14_31 : ckPt 14 31 = some (497327140957047471312408, 870648482958946519570930) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 0)`. -/
theorem ckPt_15_0 : ckPt 15 0 = some (583178767740083398036067, 384786146311015861317559) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 1)`. -/
theorem ckPt_15_1 : ckPt 15 1 = some (584124663841736462454450, 652592663211844511670738) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 2)`. -/
theorem ckPt_15_2 : ckPt 15 2 = some (478743659204124894695519, 765438537462215113188278) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 3)`. -/
theorem ckPt_15_3 : ckPt 15 3 = some (621394627425988931648284, 193010252977617088575293) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 4)`. -/
theorem ckPt_15_4 : ckPt 15 4 = some (106338198443451136800381, 201111995176731797186600) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 5)`. -/
theorem ckPt_15_5 : ckPt 15 5 = some (835770591965558471171331, 171735598869418816177906) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 6)`. -/
theorem ckPt_15_6 : ckPt 15 6 = some (790939087675060213754895, 230494096525267047813932) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 7)`. -/
theorem ckPt_15_7 : ckPt 15 7 = some (675589608240976552517181, 81228130239928885310309) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 8)`. -/
theorem ckPt_15_8 : ckPt 15 8 = some (395596827085253678092070, 208104411386394615353704) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 9)`. -/
theorem ckPt_15_9 : ckPt 15 9 = some (334116850408636423343980, 453481096717921530309014) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 10)`. -/
theorem ckPt_15_10 : ckPt 15 10 = some (298571456502877727880738, 725178062098400232315989) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 11)`. -/
theorem ckPt_15_11 : ckPt 15 11 = some (428178650300827199289444, 169081498360224922144340) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 12)`. -/
theorem ckPt_15_12 : ckPt 15 12 = some (5502826919306407845488, 53602065649891004995329) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 13)`. -/
theorem ckPt_15_13 : ckPt 15 13 = some (334029995621567681322126, 90170411694636440764465) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 14)`. -/
theorem ckPt_15_14 : ckPt 15 14 = some (574723884151468879556467, 228801237896080230268457) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 15)`. -/
theorem ckPt_15_15 : ckPt 15 15 = some (622983435268661956700080, 95956835445483975721256) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 16)`. -/
theorem ckPt_15_16 : ckPt 15 16 = some (583254141882205772294704, 384802294145213677252406) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 17)`. -/
theorem ckPt_15_17 : ckPt 15 17 = some (584217952525595383910736, 652638370702746086632678) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 18)`. -/
theorem ckPt_15_18 : ckPt 15 18 = some (478828793776214621770611, 765445130776192486847014) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 19)`. -/
theorem ckPt_15_19 : ckPt 15 19 = some (621433066467581607809006, 193024972922595569223278) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 20)`. -/
theorem ckPt_15_20 : ckPt 15 20 = some (106336108865861647630479, 201084051265266114332140) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 21)`. -/
theorem ckPt_15_21 : ckPt 15 21 = some (835760251097955937264000, 171719797065390945723204) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 22)`. -/
theorem ckPt_15_22 : ckPt 15 22 = some (790957730422648397243913, 230478043013014292925124) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 23)`. -/
theorem ckPt_15_23 : ckPt 15 23 = some (675606912217199253600473, 81219968005106911275825) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 24)`. -/
theorem ckPt_15_24 : ckPt 15 24 = some (395593844121971104584357, 208105767940992160055368) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 25)`. -/
theorem ckPt_15_25 : ckPt 15 25 = some (334125429991841589405226, 453484708010847385563183) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 26)`. -/
theorem ckPt_15_26 : ckPt 15 26 = some (298570067340787963948194, 725161876421179020576247) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 27)`. -/
theorem ckPt_15_27 : ckPt 15 27 = some (428177568090464394389854, 169098075385445194743931) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 28)`. -/
theorem ckPt_15_28 : ckPt 15 28 = some (5532608047865230643069, 53585682541643174642059) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 29)`. -/
theorem ckPt_15_29 : ckPt 15 29 = some (334038071351009432473290, 90178135398744956556968) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 30)`. -/
theorem ckPt_15_30 : ckPt 15 30 = some (574683549648022466468841, 228830127646491191976215) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(15, 31)`. -/
theorem ckPt_15_31 : ckPt 15 31 = some (622910515112506813400514, 95946267700667490842573) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
