module
public import TopHeightSecantCache.DommaschkTopHeightSecantSUFFIX
public import PlasmaLean.Design.DommaschkClosedBandAction
public import PlasmaLean.Design.DommaschkPilotArcLengthPacket

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkClosedBandSecantSUFFIX
open Set MeasureTheory Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkLowerActionPath
open DommaschkEndpointMirrorBranch DommaschkQ0R478MirrorBranch327 DommaschkPairedFirstWellAction
open DommaschkPhaseZeroRegularBirth DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkCommonEndpointTracesSUFFIX (checkpoint)
open DommaschkTopHeightSecantSUFFIX (UpperSecant)
open DommaschkClosedBandAction (Separated)
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
set_option linter.style.longLine false

theorem both_on_paths {φ : ℝ} {x : Plane} {y z : ℝ → Plane}
    (obs : DommaschkCalibratedFamilySUFFIX.Observed φ y)
    (p : DommaschkSignedObservable.Path (checkpoint .q0r470).length
      (checkpoint .q0r470).forwardExit (checkpoint .q0r470).backwardExit
      (checkpoint .q0r470).forwardRows (checkpoint .q0r470).backwardRows x y)
    (signed : Signed (MirrorEndpoint.start .q0r478) (checkpoint .q0r478).forwardRows
      (checkpoint .q0r478).backwardRows (OUTER_LENGTH/64) z) :
    Gains y z ∧ UpperSecant y z ∧ Separated y z := by
  have old := DommaschkTopHeightSecantSUFFIX.both_on_paths obs p signed
  refine ⟨old.1,old.2,?_⟩
  have pilot := signed_of_clock p p.forward p.backward
  have reg := DommaschkSignedTraceDomain.on_path p (by change 0 < 391; norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have insideI : ∀ t ∈ Icc (-(325/64):ℝ) (325/64), DommaschkSignedTraceDomain.Region (y t) := by
    intro t ht
    apply reg
    change -(391:ℝ)/64 ≤ t ∧ t ≤ 391/64
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have f := signed.forward
  have b := signed.backward
  rw [show (checkpoint .q0r478).forwardRows = fwdRows ++ (checkpoint .q0r478).forwardRows.drop 327
    by with_unfolding_all rfl] at f
  rw [show (checkpoint .q0r478).backwardRows = backRows ++ (checkpoint .q0r478).backwardRows.drop 327
    by with_unfolding_all rfl] at b
  have room : (327/64:ℝ) < OUTER_LENGTH/64 := by norm_num
  obtain ⟨fb⟩ := fwd_branch f.prefix room
  obtain ⟨bb⟩ := back_branch b.prefix room
  have outerRegions := regions f.prefix b.prefix (n := 327) (by norm_num) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) DommaschkQ0R478PolynomialFirstWell.forward_regular
    DommaschkQ0R478PolynomialFirstWell.backward_regular
  have cmp := on_chosen_paths (i := checkpoint .q0r470) (o := checkpoint .q0r478) p signed
    (by change 325 ≤ 391; norm_num) (by change 325 ≤ 391; norm_num) DommaschkComparedBirths325OnSUFFIX.paired
  apply DommaschkClosedBandAction.on_paths pilot signed (by change 325/64 < (391:ℝ)/64; norm_num)
    room insideI (by simpa only [Nat.cast_ofNat,neg_div] using outerRegions) obs.2.2.1 _ cmp fb bb
  have front := pilot.forward
  have back := pilot.backward
  rw [show (checkpoint .q0r470).forwardRows = DommaschkPositionFramesFwd.blocks.flatten.take 316 ++
    (checkpoint .q0r470).forwardRows.drop 316 by with_unfolding_all rfl] at front
  rw [show (checkpoint .q0r470).backwardRows = DommaschkPositionFramesBack.blocks.flatten.take 316 ++
    (checkpoint .q0r470).backwardRows.drop 316 by with_unfolding_all rfl] at back
  have tracked := tracks_of_take front.prefix back.prefix
  have ci : Icc (-(316/64):ℝ) (316/64) ⊆ Icc (-(325/64):ℝ) (325/64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have roomC : Icc (-(316/64):ℝ) (316/64) ⊆ Ioo (-((checkpoint .q0r470).length/64:ℝ)) ((checkpoint .q0r470).length/64:ℝ) := by
    change Icc (-(316/64):ℝ) (316/64) ⊆ Ioo (-(391/64)) (391/64)
    apply Icc_subset_Ioo <;> norm_num
  obtain ⟨_,cw,_⟩ := pilot.inputs roomC (fun t ht => insideI t (ci ht))
  apply DommaschkPilotArcLength.packet.trans
  apply DommaschkPilotArcLength.arclength (by change 316 ≤ 391; norm_num) (by change 316 ≤ 391; norm_num) tracked
  · simpa only [Nat.cast_ofNat] using cw
  intro t ht
  have range := insideI t (ci ht)
  change _ ≤ DommaschkPhysicalActionPanel.arcDensity (y t 0) t (y t 1)
  rw [DommaschkSignedTraceDensity.density_eq t range]
  exact DommaschkSignedTraceDensity.radius_le_speed t (y t)
