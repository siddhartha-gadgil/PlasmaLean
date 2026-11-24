module
public import PlasmaLean.Design.DommaschkLowerActionPath
public import SecondaryMirrorTimeCache.DommaschkQ0R478MirrorTimeSeparation

/-! # The second launch's interior lower-action cover and its actual first upper well -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkQ0R478LowerFirstWell
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature Set
open DommaschkLowerActionPath DommaschkEndpointMirrorBranch DommaschkMirrorLaunch
open DommaschkSecondaryActionCore DommaschkSecondaryActionMass
open DommaschkQ0R478MirrorBranch327 DommaschkQ0R478MirrorTimeSeparation
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

def Core (y : ℝ → Plane) : Prop := Covers false (density y) (field y) height (-322/64) inner

def Conclusion (y : ℝ → Plane) : Prop :=
  ∃ l ∈ Ioo (-327/64:ℝ) (-325/64), ∃ r ∈ Ioo (325/64:ℝ) (327/64),
    LaunchWell (field y) 0 height l r ∧ target < innerMass ∧
    innerMass ≤ action (field y) (DommaschkNativeWellAction.density y) l r height

theorem forward_regular : fwdRows.all DommaschkSignedTraceDomain.packed = true := by with_unfolding_all rfl
theorem backward_regular : backRows.all DommaschkSignedTraceDomain.packed = true := by with_unfolding_all rfl

/-- On any sufficiently long actual trajectory, the 644 packed blocks on its strictly interior
core give the lower bound for the norm-of-Cartesian-velocity integral between its first mirrors. -/
theorem on_path {entry : State} {fr br : List Step} {T : ℝ} {y : ℝ → Plane}
    (signed : Signed entry fr br T y) (room : 327/64 < T)
    (f : Outward entry fwdRows 1 T y) (b : Outward entry backRows (-1) T (fun t => y (-t)))
    (cells : Core y) : Conclusion y := by
  obtain ⟨fb⟩ := fwd_branch f room
  obtain ⟨bb⟩ := back_branch b room
  let r := fb.time highHeight
  let l := bb.time highHeight
  have hr : r ∈ Ioo (325/64:ℝ) (327/64) := (fwd_root_separation f fb).2.1
  have hl : l ∈ Ioo (325/64:ℝ) (327/64) := (back_root_separation b bb).2.1
  have level : (highHeight : ℝ) = height := by
    norm_num [highHeight,DommaschkFirstMirrorLaunchSign.height,height]
  have well : LaunchWell (field y) 0 height (-l) r := by
    refine ⟨by linarith [hl.1],by linarith [hr.1],(bb.hit highHeight).trans level,
      (fb.hit highHeight).trans level,?_⟩
    intro t ht
    rcases le_total 0 t with pos | neg
    · exact (fb.before highHeight t ⟨pos,ht.2⟩).trans_eq level
    · have h := bb.before highHeight (-t) ⟨by linarith,by linarith [ht.1]⟩
      change DommaschkMirrorTubeCrossing.strength t (y t) < height
      simpa only [neg_neg] using h.trans_eq level
  have su : Icc (-l) r ⊆ Icc (-327/64) (327/64) :=
    Icc_subset_Icc (by linarith [hl.2]) hr.2.le
  have valid := regions f b (n := 327) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) forward_regular backward_regular
  have hreg : ∀ t ∈ Icc (-327/64:ℝ) (327/64), DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [Nat.cast_ofNat] using valid
  have inside : Icc (-l) r ⊆ Ioo (-T) T := fun t ht =>
    ⟨by linarith [ht.1,hl.2], by linarith [ht.2,hr.2]⟩
  obtain ⟨cf,cw,eq⟩ := signed.inputs inside (fun t ht => hreg t (su ht))
  have m := floor_on_enclosing_interval (f := field y) (w := density y) (l := -l) (r := r)
    (by linarith [hl.1]) (by linarith [hr.1]) cells
    (fun t ht => by rw [← eq t ht]; exact norm_nonneg _) cf cw
  refine ⟨-l,⟨by linarith [hl.2],by linarith [hl.1]⟩,r,hr,well,m.1,m.2.trans_eq ?_⟩
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by linarith [hl.1,hr.1])] at ht
  exact congrArg (fun v => v * _) (eq t ht).symm

/-- The exact core and a signed endpoint passage discharge every hypothesis at the same birth. -/
theorem from_passage {uC zC uA zA : Theory.KAM.FA} {φ T : ℝ} {fe be : Set Plane}
    {fr br extraF extraB : List Step} (room : 327/64 < T)
    (flink : fr = fwdRows ++ extraF) (blink : br = backRows ++ extraB)
    (passage : DommaschkEndpointSignedTrace.FromBirth .q0r478 uC zC uA zA φ T fe be
      (physicalSlabs (MirrorEndpoint.start .q0r478) 0 fr) (physicalSlabs (MirrorEndpoint.start .q0r478) 0 br))
    (rectangles : ∀ y, Tracks fwdRows backRows 322 y → Core y) :
    AtBirth .q0r478 uC zC uA zA φ (fun y => Signed (MirrorEndpoint.start .q0r478) fr br T y ∧ Conclusion y) := by
  apply observe (by rfl) passage
  intro y signed
  have fullF := signed.forward
  have fullB := signed.backward
  rw [flink] at fullF
  rw [blink] at fullB
  have f := fullF.prefix
  have b := fullB.prefix
  have fc : Outward (MirrorEndpoint.start .q0r478) (fwdRows.take 322) 1 T y :=
    (show Outward (MirrorEndpoint.start .q0r478) (fwdRows.take 322 ++ fwdRows.drop 322)
      1 T y by simpa only [List.take_append_drop] using f).prefix
  have bc : Outward (MirrorEndpoint.start .q0r478) (backRows.take 322) (-1) T (fun t => y (-t)) :=
    (show Outward (MirrorEndpoint.start .q0r478) (backRows.take 322 ++ backRows.drop 322)
      (-1) T (fun t => y (-t)) by simpa only [List.take_append_drop] using b).prefix
  exact ⟨signed,on_path signed room f b (rectangles y (tracks_of_take fc bc))⟩

end PlasmaLean.Design.DommaschkQ0R478LowerFirstWell
