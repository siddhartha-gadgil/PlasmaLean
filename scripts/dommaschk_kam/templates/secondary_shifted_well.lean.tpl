module
public import PlasmaLean.Design.DommaschkSecondaryHeightCollar
public import SecondaryFirstWellLowerCache.DommaschkQ0R478LowerFirstWell
public import SecondaryShiftedBirthCache.DommaschkShiftedActionBirth267R032Of048

/-! # A common physical trajectory, all near-upper first mirrors, and their action bounds -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkQ0R478ShiftedFirstWell
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature Set
open DommaschkLowerActionPath DommaschkEndpointMirrorBranch DommaschkMirrorLaunch
open DommaschkSecondaryActionMass DommaschkQ0R478MirrorBranch327
open DommaschkQ0R478MirrorTimeSeparation Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
open DommaschkSecondaryHeightCollar
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

abbrev Core := DommaschkQ0R478LowerFirstWell.Core
abbrev shortMass := DommaschkShiftedActionBirth267R032Of048.lowerMass
abbrev fullMass := DommaschkQ0R478ShiftedAction267.lowerMass
abbrev window := Icc lower height
abbrev lowerTime : ℝ := 2599/512

/-- All first wells and the finite action floor are on a common physical trajectory.
The stronger target follows if the full original 322-pair physical cover holds on that trajectory. -/
def Result (y : ℝ → Plane) : Prop :=
  ∀ h ∈ window, ∃ l ∈ Ioo (-327/64:ℝ) (-lowerTime), ∃ r ∈ Ioo lowerTime (327/64:ℝ),
    LaunchWell (field y) 0 h l r ∧
    shortMass ≤ action (field y) (DommaschkNativeWellAction.density y) l r h ∧
    (Core y → target < fullMass ∧ fullMass ≤ action (field y) (DommaschkNativeWellAction.density y) l r h)

/-- The larger original physical cover makes the strict target simultaneous throughout the window. -/
def Complete (y : ℝ → Plane) : Prop :=
  ∀ h ∈ window, ∃ l ∈ Ioo (-327/64:ℝ) (-lowerTime), ∃ r ∈ Ioo lowerTime (327/64:ℝ),
    LaunchWell (field y) 0 h l r ∧
    target < fullMass ∧ fullMass ≤ action (field y) (DommaschkNativeWellAction.density y) l r h

theorem complete_of_core {y : ℝ → Plane} (res : Result y) (c : Core y) : Complete y := by
  intro h hh
  obtain ⟨l,hl,r,hr,well,_,full⟩ := res h hh
  exact ⟨l,hl,r,hr,well,full c⟩

theorem take_rows {entry : State} {rs : List Step} {sign T : ℝ} {y : ℝ → Plane}
    (d : Outward entry rs sign T y) (n : ℕ) : Outward entry (rs.take n) sign T y :=
  (show Outward entry (rs.take n ++ rs.drop n) sign T y by simpa only [List.take_append_drop] using d).prefix

private theorem partial_action {y : ℝ → Plane} {h l r : ℝ} (hh : h ∈ window)
    (follows : Tracks fwdRows backRows 32 y) (left : l ≤ -32/64) (right : 32/64 ≤ r)
    (nonneg : ∀ t ∈ Icc l r, 0 ≤ density y t)
    (cf : ContinuousOn (field y) (Icc l r)) (cw : ContinuousOn (density y) (Icc l r)) :
    shortMass ≤ action (field y) (density y) l r h := by
  have old := DommaschkLowerCoverQ0R478L295R359.cover follows
  rw [DommaschkLowerCoverQ0R478L295R359.Covered,
    show DommaschkLowerCoverQ0R478L295R359.start = (-32/64:ℝ) by
      norm_num [DommaschkLowerCoverQ0R478L295R359.start]] at old
  have moved := (Certificates.LowerActionHeightShift.covers (h := h) (by
    have := hh.1; change height-267/134217728 ≤ h at this; linarith) _
    DommaschkShiftedActionBirth267R032Of048.checked old).1
  have sx := Icc_subset_Icc left right
  have b := Certificates.NativeActionInterval.exact_lower_mass
    DommaschkShiftedActionBirth267R032Of048.length_rows moved
    (fun t ht => nonneg t (sx ht)) (cf.mono sx) (cw.mono sx)
  rw [DommaschkShiftedActionBirth267R032Of048.sum_rows] at b
  apply le_trans _ (action_mono_interval left (by norm_num) right cf cw nonneg)
  norm_num [shortMass,DommaschkShiftedActionBirth267R032Of048.lowerMass] at b ⊢
  exact b

theorem on_path {entry : State} {fr br : List Step} {T : ℝ} {y : ℝ → Plane}
    (signed : Signed entry fr br T y) (room : 327/64 < T)
    (f : Outward entry fwdRows 1 T y) (b : Outward entry backRows (-1) T (fun t => y (-t))) :
    Result y := by
  obtain ⟨fb⟩ := fwd_branch f room
  obtain ⟨bb⟩ := back_branch b room
  have high : (highHeight : ℝ) = height := by
    norm_num [highHeight,DommaschkFirstMirrorLaunchSign.height,height]
  have valid := regions f b (n := 327) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    DommaschkQ0R478LowerFirstWell.forward_regular DommaschkQ0R478LowerFirstWell.backward_regular
  intro h hh
  let j := level hh
  let r := fb.time j
  let s := bb.time j
  have slopes := time_near_upper fb highHeight high hh
  have slopb := time_near_upper bb highHeight high hh
  have separated {t top : ℝ} (near : |t-top| < 1/512) (lo : 325/64 < top) : lowerTime < t := by
    have d := (abs_lt.mp near).1
    dsimp [lowerTime]; linarith
  have hr : r ∈ Ioo lowerTime (327/64) :=
    ⟨separated slopes (fwd_root_separation f fb).2.1.1,(fb.interior_time j).2⟩
  have hs : s ∈ Ioo lowerTime (327/64) :=
    ⟨separated slopb (back_root_separation b bb).2.1.1,(bb.interior_time j).2⟩
  have small : (32/64 : ℝ) < lowerTime := by norm_num [lowerTime]
  have ss := small.trans hs.1
  have rr := small.trans hr.1
  have unitPos := (by norm_num : (0:ℝ) < 32/64)
  have well : LaunchWell (field y) 0 h (-s) r := by
    refine ⟨neg_lt_zero.mpr (unitPos.trans ss),unitPos.trans rr,bb.hit j,fb.hit j,?_⟩
    intro t ht
    rcases le_total 0 t with pos | neg
    · exact fb.before j t ⟨pos,ht.2⟩
    · have v := bb.before j (-t) ⟨by linarith,by linarith [ht.1]⟩
      change DommaschkMirrorTubeCrossing.strength t (y t) < h
      simpa only [neg_neg,j,DommaschkSecondaryHeightCollar.level] using v
  have inside : Icc (-s) r ⊆ Ioo (-T) T := fun t ht =>
    ⟨by linarith [hs.2,ht.1],by linarith [hr.2,ht.2]⟩
  obtain ⟨cf,cw,eq⟩ := signed.inputs inside (fun t ht => valid t
    ⟨by norm_num; linarith [hs.2,ht.1], by norm_num; linarith [hr.2,ht.2]⟩)
  have hn : ∀ t ∈ Icc (-s) r, 0 ≤ density y t :=
    fun t ht => by rw [← eq t ht]; exact norm_nonneg _
  have cart : action (field y) (density y) (-s) r h =
      action (field y) (DommaschkNativeWellAction.density y) (-s) r h := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (well.left_lt.trans well.lt_right).le] at ht
    exact congrArg (fun v => v * _) (eq t ht).symm
  refine ⟨-s,⟨by linarith [hs.2],by linarith [hs.1]⟩,r,hr,well,?_,?_⟩
  · rw [← cart]
    exact partial_action hh (tracks_of_take (take_rows f 32) (take_rows b 32))
      (by simpa only [neg_div] using neg_le_neg ss.le) rr.le hn cf cw
  · intro cells
    obtain ⟨_,_,above,bound⟩ := DommaschkQ0R478ShiftedAction267.first_well hh.1 cells well hn cf cw
    exact ⟨above,bound.trans_eq cart⟩

theorem from_passage {uC zC uA zA : Theory.KAM.FA} {φ T : ℝ} {fe be : Set Plane}
    {fr br extraF extraB : List Step} (room : 327/64 < T)
    (flink : fr = fwdRows ++ extraF) (blink : br = backRows ++ extraB)
    (passage : DommaschkEndpointSignedTrace.FromBirth .q0r478 uC zC uA zA φ T fe be
      (physicalSlabs (MirrorEndpoint.start .q0r478) 0 fr) (physicalSlabs (MirrorEndpoint.start .q0r478) 0 br)) :
    AtBirth .q0r478 uC zC uA zA φ (fun y => Signed (MirrorEndpoint.start .q0r478) fr br T y ∧ Result y) := by
  apply observe (by rfl) passage
  intro y signed
  have f := signed.forward
  have b := signed.backward
  rw [flink] at f
  rw [blink] at b
  exact ⟨signed,on_path signed room f.prefix b.prefix⟩

end PlasmaLean.Design.DommaschkQ0R478ShiftedFirstWell
