module
public import PolynomialFirstWellCache.DommaschkQ0R478PolynomialFirstWell
public import RegularBirthArcsCache.DommaschkRegularBirthArcsSUFFIX
public import ComparedTraceCache.DommaschkComparedBirths325OnSUFFIX
public import PlasmaLean.Design.DommaschkPairedFirstWellAction

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTopHeightSecantSUFFIX
open Set Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkLowerActionPath
open DommaschkEndpointMirrorBranch DommaschkQ0R478MirrorBranch327
open DommaschkPhaseZeroRegularBirth DommaschkFirstMirrorWell DommaschkPairedFirstWellAction
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open DommaschkCommonEndpointTracesSUFFIX (checkpoint)
open Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
set_option linter.style.longLine false

/-- The one-way Cartesian action at the common upper mirror height. -/
def J (y : ℝ → Plane) (l r : ℝ) : ℝ :=
  action (DommaschkNativeWellAction.field y) (DommaschkNativeWellAction.density y)
    l r DommaschkNativeWellAction.level

def UpperSecant (y z : ℝ → Plane) : Prop :=
  ∃ l ∈ Ioo (-325/64:ℝ) (-324/64), ∃ r ∈ Ioo (324/64:ℝ) (325/64),
  ∃ L ∈ Ioo (-327/64:ℝ) (-325/64), ∃ R ∈ Ioo (325/64:ℝ) (327/64),
    LaunchWell (DommaschkNativeWellAction.field y) 0 DommaschkNativeWellAction.level l r ∧
    LaunchWell (DommaschkNativeWellAction.field z) 0 DommaschkNativeWellAction.level L R ∧
    J y l r ≤ DommaschkActionArchiveMass.mass ∧
    DommaschkQ0R478PolynomialFloor325.innerMass ≤ J z L R ∧
    J y l r < DommaschkNativeWellAction.target ∧ DommaschkNativeWellAction.target < J z L R ∧
    1/250 < J z L R - J y l r ∧ 1/2 < (J z L R - J y l r)/(239/500-47/100)

theorem top_of_wells {y z : ℝ → Plane} (inner : DommaschkNativeWellAction.FirstWellAction y)
    (outer : DommaschkQ0R478PolynomialFirstWell.Conclusion z) : UpperSecant y z := by
  obtain ⟨l,hl,r,hr,wi,_,_,included,mass,below⟩ := inner
  obtain ⟨L,hL,R,hR,wo,above,lower⟩ := outer
  have cap : J y l r ≤ DommaschkActionArchiveMass.mass := included.trans mass
  have floor : DommaschkQ0R478PolynomialFloor325.innerMass ≤ J z L R := lower
  have gap : (1/250:ℝ) < DommaschkQ0R478PolynomialFloor325.innerMass - DommaschkActionArchiveMass.mass := by
    norm_num [DommaschkQ0R478PolynomialFloor325.innerMass,DommaschkActionArchiveMass.mass]
  have diff := gap.trans_le (sub_le_sub floor cap)
  refine ⟨l,hl,r,hr,L,hL,R,hR,wi,wo,cap,floor,cap.trans_lt below,above.trans_le floor,diff,?_⟩
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 239/500-47/100)]
  exact lt_of_eq_of_lt (by norm_num) diff

/-- The original synchronized bounds and the independent upper-height integral apply
to the same two chosen trajectories. -/
theorem both_on_paths {φ : ℝ} {x : Plane} {y z : ℝ → Plane}
    (obs : DommaschkCalibratedFamilySUFFIX.Observed φ y)
    (p : DommaschkSignedObservable.Path (checkpoint .q0r470).length
      (checkpoint .q0r470).forwardExit (checkpoint .q0r470).backwardExit
      (checkpoint .q0r470).forwardRows (checkpoint .q0r470).backwardRows x y)
    (signed : Signed (MirrorEndpoint.start .q0r478) (checkpoint .q0r478).forwardRows
      (checkpoint .q0r478).backwardRows (OUTER_LENGTH/64) z) : Gains y z ∧ UpperSecant y z := by
  have f := signed.forward
  have b := signed.backward
  rw [show (checkpoint .q0r478).forwardRows = fwdRows ++ (checkpoint .q0r478).forwardRows.drop 327
    by with_unfolding_all rfl] at f
  rw [show (checkpoint .q0r478).backwardRows = backRows ++ (checkpoint .q0r478).backwardRows.drop 327
    by with_unfolding_all rfl] at b
  have fw := f.prefix
  have bw := b.prefix
  have room : (327/64:ℝ) < OUTER_LENGTH/64 := by norm_num
  have fc : Outward (MirrorEndpoint.start .q0r478) (fwdRows.take 325) 1 (OUTER_LENGTH/64) z :=
    (show Outward _ (fwdRows.take 325 ++ fwdRows.drop 325) _ _ _ by
      simpa only [List.take_append_drop] using fw).prefix
  have bc : Outward (MirrorEndpoint.start .q0r478) (backRows.take 325) (-1) (OUTER_LENGTH/64) (fun t => z (-t)) :=
    (show Outward _ (backRows.take 325 ++ backRows.drop 325) _ _ _ by
      simpa only [List.take_append_drop] using bw).prefix
  refine ⟨?_, top_of_wells obs.2.1 (DommaschkQ0R478PolynomialFirstWell.on_path signed room fw bw (tracks_of_take fc bc))⟩
  have cmp := on_chosen_paths (i := checkpoint .q0r470) (o := checkpoint .q0r478) p signed
    (by change 325 ≤ 391; norm_num) (by change 325 ≤ 391; norm_num) DommaschkComparedBirths325OnSUFFIX.paired
  obtain ⟨fb⟩ := fwd_branch fw room
  obtain ⟨bb⟩ := back_branch bw room
  have reg := regions fw bw (n := 327) (by norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    DommaschkQ0R478PolynomialFirstWell.forward_regular DommaschkQ0R478PolynomialFirstWell.backward_regular
  exact gains_of_branches obs.2.2.1 obs.2.2.2.2.2 cmp signed room (by simpa only [Nat.cast_ofNat] using reg) fb bb

theorem from_common_tori : ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
    ∀ φ : ℝ, |φ| ≤ 1/2^19 → ∃ y z : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧ DommaschkCalibratedFamilySUFFIX.Observed φ y ∧
      z φ = coordinates.symm (birth uC zC uA zA (239/500) φ) ∧
      Signed (MirrorEndpoint.start .q0r478) (checkpoint .q0r478).forwardRows
        (checkpoint .q0r478).backwardRows (OUTER_LENGTH/64) z ∧ Gains y z ∧ UpperSecant y z := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,calibrate⟩ := DommaschkRegularBirthArcsSUFFIX.pilot
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  obtain ⟨_,y,born,p,obs,_⟩ := calibrate φ small
  have pass := each .q0r478 φ (by simpa [MirrorEndpoint.opposite,MirrorEndpoint.width,azimuth] using small)
  obtain ⟨z,bornZ,signed,_⟩ := DommaschkQ0R478RegularBirths.from_passage
    (extraF := (checkpoint .q0r478).forwardRows.drop 327) (extraB := (checkpoint .q0r478).backwardRows.drop 327)
    small pass (by change 327/64 < (OUTER_LENGTH:ℝ)/64; norm_num) rfl rfl (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  exact ⟨y,z,born,obs,bornZ,signed,both_on_paths obs p signed⟩

end PlasmaLean.Design.DommaschkTopHeightSecantSUFFIX
