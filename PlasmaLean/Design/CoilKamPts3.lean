/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows 6 and 7

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam

/-- Kernel evaluation of the grid point `(6, 0)`. -/
theorem ckPt_6_0 : ckPt 6 0 = some (664077283147093308108911, 114305050270526457063211) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 1)`. -/
theorem ckPt_6_1 : ckPt 6 1 = some (173891413645558569043861, 263873465214811938480060) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 2)`. -/
theorem ckPt_6_2 : ckPt 6 2 = some (321369364848777679874030, 483713259958126863334883) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 3)`. -/
theorem ckPt_6_3 : ckPt 6 3 = some (877883679733597962232054, 306035712558251944379206) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 4)`. -/
theorem ckPt_6_4 : ckPt 6 4 = some (527931687438648372524083, 204021474158732735186240) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 5)`. -/
theorem ckPt_6_5 : ckPt 6 5 = some (277793777561836826738043, 801315693070201942185467) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 6)`. -/
theorem ckPt_6_6 : ckPt 6 6 = some (351524723945894642951006, 138214054081856894340148) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 7)`. -/
theorem ckPt_6_7 : ckPt 6 7 = some (211251108487933811017320, 36164385806939479034853) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 8)`. -/
theorem ckPt_6_8 : ckPt 6 8 = some (195243325941822077382739, 251803268711648018107579) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 9)`. -/
theorem ckPt_6_9 : ckPt 6 9 = some (95879562201966518530289, 281696364815958460909096) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 10)`. -/
theorem ckPt_6_10 : ckPt 6 10 = some (303013912775712532097626, 96892350003606040079386) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 11)`. -/
theorem ckPt_6_11 : ckPt 6 11 = some (413025735966772842795908, 339813350446625801901198) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 12)`. -/
theorem ckPt_6_12 : ckPt 6 12 = some (157269603679195086862538, 33763867063183931101947) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 13)`. -/
theorem ckPt_6_13 : ckPt 6 13 = some (209138033058800726603730, 678349054781674204074625) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 14)`. -/
theorem ckPt_6_14 : ckPt 6 14 = some (273693757189051017641583, 265328506477016221466686) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 15)`. -/
theorem ckPt_6_15 : ckPt 6 15 = some (1232021418534054454159108, 282339714026177608349305) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 16)`. -/
theorem ckPt_6_16 : ckPt 6 16 = some (664055106732570421669397, 114231353683683303315277) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 17)`. -/
theorem ckPt_6_17 : ckPt 6 17 = some (173858909545150666007675, 263852346597703596453797) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 18)`. -/
theorem ckPt_6_18 : ckPt 6 18 = some (321304205742853316221537, 483643281328453358874490) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 19)`. -/
theorem ckPt_6_19 : ckPt 6 19 = some (877807165548652061143480, 306053712139734716637537) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 20)`. -/
theorem ckPt_6_20 : ckPt 6 20 = some (527879900435391409011968, 203982802883980723782577) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 21)`. -/
theorem ckPt_6_21 : ckPt 6 21 = some (277794406093486187994862, 801256446442148630690920) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 22)`. -/
theorem ckPt_6_22 : ckPt 6 22 = some (351527577420224405873645, 138220104208008785423083) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 23)`. -/
theorem ckPt_6_23 : ckPt 6 23 = some (211218437629173672269929, 36193968964607890772952) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 24)`. -/
theorem ckPt_6_24 : ckPt 6 24 = some (195232719447890364238277, 251824216944746221296475) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 25)`. -/
theorem ckPt_6_25 : ckPt 6 25 = some (95857793667674447687548, 281711328789248356728407) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 26)`. -/
theorem ckPt_6_26 : ckPt 6 26 = some (302986796748169942236459, 96861845432131392849135) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 27)`. -/
theorem ckPt_6_27 : ckPt 6 27 = some (413036240595629016388001, 339808436828518476806375) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 28)`. -/
theorem ckPt_6_28 : ckPt 6 28 = some (157319478174508398353589, 33746429418238979525634) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 29)`. -/
theorem ckPt_6_29 : ckPt 6 29 = some (209151916152205152112770, 678402416311063307364234) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 30)`. -/
theorem ckPt_6_30 : ckPt 6 30 = some (273744049603688156744673, 265365479074119006449115) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(6, 31)`. -/
theorem ckPt_6_31 : ckPt 6 31 = some (1232120777407080162160031, 282437403711283751183563) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 0)`. -/
theorem ckPt_7_0 : ckPt 7 0 = some (558185952268520772187834, 552261978486370134432468) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 1)`. -/
theorem ckPt_7_1 : ckPt 7 1 = some (31917722306097432377485, 176060291667276364315176) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 2)`. -/
theorem ckPt_7_2 : ckPt 7 2 = some (247411449526201675304167, 1515312934146611119906166) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 3)`. -/
theorem ckPt_7_3 : ckPt 7 3 = some (760887198706934268405448, 644412428376869995111238) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 4)`. -/
theorem ckPt_7_4 : ckPt 7 4 = some (1176272393494008967051369, 863670564734216597628334) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 5)`. -/
theorem ckPt_7_5 : ckPt 7 5 = some (81829620772694477746979, 583511569253527970277381) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 6)`. -/
theorem ckPt_7_6 : ckPt 7 6 = some (247363599992151152439006, 720160670615820476034444) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 7)`. -/
theorem ckPt_7_7 : ckPt 7 7 = some (122400285423620501284474, 230339830830490365920220) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 8)`. -/
theorem ckPt_7_8 : ckPt 7 8 = some (222435875394049716700369, 289198340274435719368272) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 9)`. -/
theorem ckPt_7_9 : ckPt 7 9 = some (6656744135126971313963, 149845233544214700380072) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 10)`. -/
theorem ckPt_7_10 : ckPt 7 10 = some (171116425090167854500556, 467596709832325827891771) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 11)`. -/
theorem ckPt_7_11 : ckPt 7 11 = some (639154630878686628506140, 151992129221575750855962) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 12)`. -/
theorem ckPt_7_12 : ckPt 7 12 = some (579298370296814073893385, 388777890369189958468951) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 13)`. -/
theorem ckPt_7_13 : ckPt 7 13 = some (19108992660262209482347, 289707148854085848782584) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 14)`. -/
theorem ckPt_7_14 : ckPt 7 14 = some (139647763683848428957988, 1091339468851347304675610) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 15)`. -/
theorem ckPt_7_15 : ckPt 7 15 = some (196844591745424756502851, 860382785316530970144834) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 16)`. -/
theorem ckPt_7_16 : ckPt 7 16 = some (558142565557233396176564, 552208685965667882421570) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 17)`. -/
theorem ckPt_7_17 : ckPt 7 17 = some (31906071728184977110778, 176048828277776344483030) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 18)`. -/
theorem ckPt_7_18 : ckPt 7 18 = some (247429593792498343418835, 1515172199509093900295148) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 19)`. -/
theorem ckPt_7_19 : ckPt 7 19 = some (760828876021023100678461, 644337704325928101454241) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 20)`. -/
theorem ckPt_7_20 : ckPt 7 20 = some (1176175769759451206016331, 863648983378954310553584) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 21)`. -/
theorem ckPt_7_21 : ckPt 7 21 = some (81815552572360511994592, 583510993086408495739490) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 22)`. -/
theorem ckPt_7_22 : ckPt 7 22 = some (247367121109078551302847, 720106480293650162424957) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 23)`. -/
theorem ckPt_7_23 : ckPt 7 23 = some (122376297178277308710018, 230314468875608609823247) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 24)`. -/
theorem ckPt_7_24 : ckPt 7 24 = some (222430311073180303022579, 289167425963380822429931) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 25)`. -/
theorem ckPt_7_25 : ckPt 7 25 = some (6639060543347596596773, 149810903935153154382238) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 26)`. -/
theorem ckPt_7_26 : ckPt 7 26 = some (171103005489666598423232, 467609755985524373587286) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 27)`. -/
theorem ckPt_7_27 : ckPt 7 27 = some (639161381825734880169407, 152037908493636434191214) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 28)`. -/
theorem ckPt_7_28 : ckPt 7 28 = some (579347870577969889348469, 388772876092937957838601) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 29)`. -/
theorem ckPt_7_29 : ckPt 7 29 = some (19099257201527317983763, 289684399943197091373897) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 30)`. -/
theorem ckPt_7_30 : ckPt 7 30 = some (139613870570924588523328, 1091433234543286336079162) := by
  decide +kernel

/-- Kernel evaluation of the grid point `(7, 31)`. -/
theorem ckPt_7_31 : ckPt 7 31 = some (196886477024469893529701, 860458792630837781594800) := by
  decide +kernel

end PlasmaLean.Design.CoilKam
