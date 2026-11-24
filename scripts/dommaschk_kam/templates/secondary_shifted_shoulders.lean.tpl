module
public import PlasmaLean.Theory.Kinetic.MirrorActionShoulders
public import SecondaryShiftedWellCache.DommaschkQ0R478ShiftedFirstWell
public import GroupedMirrorOrderedCache.DommaschkQ0R478Drop1Over270000SubmirrorPrefix317

/-! # Strict near-upper first-well action from the two outer intervals and the measured core -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkQ0R478ShiftedFirstWellShoulders
open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature Set
open DommaschkLowerActionPath DommaschkEndpointMirrorBranch DommaschkMirrorLaunch
open DommaschkSecondaryActionMass DommaschkQ0R478MirrorBranch327
open DommaschkQ0R478ShiftedFirstWell
open Kinetic.MirrorActionEnvelope Kinetic.MirrorHeightAction
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
set_option linter.style.longLine false

/-- Uniform on the closed incoming 317-pair core of the same true solution. -/
private theorem strength_below {entry : State} {T : ℝ} {y : ℝ → Plane}
    (f : Outward entry fwdRows 1 T y) (b : Outward entry backRows (-1) T (fun t => y (-t))) :
    ∀ t ∈ Icc (-317/64:ℝ) (317/64),
      field y t < (↑(DommaschkFirstMirrorLaunchSign.height false - (1/270000)) : ℝ) := by
  have fs := f.contained
  have bs := b.contained
  rw [show fwdRows = DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.fwdRows ++ fwdTail by with_unfolding_all rfl] at fs
  rw [show backRows = DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.backRows ++ backTail by with_unfolding_all rfl] at bs
  have F := (DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.fwd_below entry).on_nonempty_prefix
    (post := fwdTail) (by intro hn; have e := congrArg List.length hn; change 317 = 0 at e; omega) fs
  have B := (DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.back_below entry).on_nonempty_prefix
    (post := backTail) (by intro hn; have e := congrArg List.length hn; change 317 = 0 at e; omega) bs
  have lenF : DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.fwdRows.length = 317 := rfl
  have lenB : DommaschkQ0R478Drop1Over270000SubmirrorPrefix317.backRows.length = 317 := rfl
  simp only [lenF,lenB,Nat.cast_ofNat,zero_add] at F B
  intro t ht
  rcases le_total 0 t with a | a
  · exact F t ⟨a,ht.2⟩
  · have x := B (-t) ⟨by linarith,by linarith [ht.1]⟩
    simpa only [neg_neg,field] using x

/-- Native inner mass plus 285 outward intervals on each side gives a strict contribution
of more than 43/100 before any mirror in the near-upper height band. -/
theorem mass_on_core {entry : State} {T : ℝ} {y : ℝ → Plane}
    (f : Outward entry fwdRows 1 T y) (b : Outward entry backRows (-1) T (fun t => y (-t)))
    {h : ℝ} (hh : h ∈ window)
    (cf : ContinuousOn (field y) (Icc (-317/64:ℝ) (317/64)))
    (cw : ContinuousOn (density y) (Icc (-317/64:ℝ) (317/64))) :
    43/100 < action (field y) (density y) (-317/64) (317/64) h := by
  have region := regions f b (n := 327) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    DommaschkQ0R478LowerFirstWell.forward_regular DommaschkQ0R478LowerFirstWell.backward_regular
  have minimum (t : ℝ) (ht : t ∈ Icc (-317/64:ℝ) (317/64)) : 7/8 ≤ density y t :=
    DommaschkSignedTraceDensity.density_lower _ (region t
      ⟨by norm_num; linarith [ht.1],by norm_num; linarith [ht.2]⟩)
  have inside : Icc (-32/64:ℝ) (32/64) ⊆ Icc (-317/64) (317/64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have orig := DommaschkLowerCoverQ0R478L295R359.cover (tracks_of_take (take_rows f 32) (take_rows b 32))
  rw [DommaschkLowerCoverQ0R478L295R359.Covered,
    show DommaschkLowerCoverQ0R478L295R359.start = (-32/64:ℝ) by norm_num [DommaschkLowerCoverQ0R478L295R359.start]] at orig
  have moved := (Certificates.LowerActionHeightShift.covers (h := h) (by
    have := hh.1; change height-267/134217728 ≤ h at this; linarith) _
    DommaschkShiftedActionBirth267R032Of048.checked orig).1
  have core := Certificates.NativeActionInterval.exact_lower_mass
    DommaschkShiftedActionBirth267R032Of048.length_rows moved
    (fun t ht => (by norm_num : (0:ℝ) ≤ 7/8).trans (minimum t (inside ht))) (cf.mono inside) (cw.mono inside)
  rw [DommaschkShiftedActionBirth267R032Of048.sum_rows] at core
  have normLower : (161/5000:ℝ)^2 <
      2*(DommaschkSecondaryHeightCollar.lower - ↑(DommaschkFirstMirrorLaunchSign.height false - 1/270000)) := by
    norm_num [DommaschkSecondaryHeightCollar.lower,height,DommaschkFirstMirrorLaunchSign.height]
  have integrand (t : ℝ) (ht : t ∈ Icc (-317/64:ℝ) (317/64)) :
      (7/8)*(161/5000) ≤ density y t * Real.sqrt (2*(h-field y t)) := by
    have speed : (161/5000:ℝ) < Real.sqrt (2*(h-field y t)) := by
      apply (Real.lt_sqrt (by norm_num)).2
      exact normLower.trans_le (mul_le_mul_of_nonneg_left
        (sub_le_sub hh.1 (strength_below f b t ht).le) (by norm_num))
    exact mul_le_mul (minimum t ht) speed.le (by norm_num)
      ((by norm_num : (0:ℝ) ≤ 7/8).trans (minimum t ht))
  have ext := action_add_shoulders (a := -317/64) (b := -32/64) (c := 32/64) (d := 317/64)
    (by norm_num) (by norm_num) (by norm_num) cf cw
    (fun t ht => integrand t ⟨ht.1,by linarith [ht.2]⟩)
    (fun t ht => integrand t ⟨by linarith [ht.1],ht.2⟩) core
  exact lt_of_lt_of_le (by norm_num) ext

def Result (y : ℝ → Plane) : Prop :=
  ∀ h ∈ window, ∃ l ∈ Ioo (-327/64:ℝ) (-lowerTime), ∃ r ∈ Ioo lowerTime (327/64:ℝ),
    LaunchWell (field y) 0 h l r ∧
    43/100 < action (field y) (DommaschkNativeWellAction.density y) l r h ∧
    (Core y → target < fullMass ∧ fullMass ≤ action (field y) (DommaschkNativeWellAction.density y) l r h)

theorem on_path {entry : State} {fr br : List Step} {T : ℝ} {y : ℝ → Plane}
    (signed : Signed entry fr br T y) (room : 327/64 < T)
    (f : Outward entry fwdRows 1 T y) (b : Outward entry backRows (-1) T (fun t => y (-t))) :
    Result y := by
  intro h hh
  obtain ⟨l,hl,r,hr,well,_,full⟩ := DommaschkQ0R478ShiftedFirstWell.on_path signed room f b h hh
  have enough : (317/64:ℝ) < lowerTime := by norm_num [lowerTime]
  have lb : l ≤ -317/64 := by
    calc
      l ≤ -lowerTime := hl.2.le
      _ ≤ -(317/64) := neg_le_neg enough.le
      _ = -317/64 := by ring
  have rb := (enough.trans hr.1).le
  have region := regions f b (n := 327) (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    DommaschkQ0R478LowerFirstWell.forward_regular DommaschkQ0R478LowerFirstWell.backward_regular
  have inpath : Icc l r ⊆ Ioo (-T) T := fun t ht =>
    ⟨by linarith [hl.1,ht.1],by linarith [hr.2,ht.2]⟩
  obtain ⟨cf,cw,eq⟩ := signed.inputs inpath (fun t ht => region t
    ⟨by norm_num; linarith [hl.1,ht.1],by norm_num; linarith [hr.2,ht.2]⟩)
  have sub := Icc_subset_Icc lb rb
  have outer := action_mono_interval (f := field y) (w := density y) (h := h) lb (by norm_num) rb
    cf cw (fun t ht => by rw [← eq t ht]; exact norm_nonneg _)
  have cart : action (field y) (density y) l r h =
      action (field y) (DommaschkNativeWellAction.density y) l r h := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (well.left_lt.trans well.lt_right).le] at ht
    exact congrArg (fun v => v * _) (eq t ht).symm
  exact ⟨l,hl,r,hr,well,(mass_on_core f b hh (cf.mono sub) (cw.mono sub)).trans_le (outer.trans_eq cart),full⟩

theorem from_passage {uC zC uA zA : Theory.KAM.FA} {φ T : ℝ} {fe be : Set Plane}
    {fr br extraF extraB : List Step} (room : 327/64 < T)
    (flink : fr = fwdRows ++ extraF) (blink : br = backRows ++ extraB)
    (passage : DommaschkEndpointSignedTrace.FromBirth .q0r478 uC zC uA zA φ T fe be
      (physicalSlabs (MirrorEndpoint.start .q0r478) 0 fr) (physicalSlabs (MirrorEndpoint.start .q0r478) 0 br)) :
    AtBirth .q0r478 uC zC uA zA φ (fun y => Signed (MirrorEndpoint.start .q0r478) fr br T y ∧ Result y) := by
  apply observe (by rfl) passage
  intro y ypath
  have F := ypath.forward
  have B := ypath.backward
  rw [flink] at F
  rw [blink] at B
  exact ⟨ypath,on_path ypath room F.prefix B.prefix⟩

end PlasmaLean.Design.DommaschkQ0R478ShiftedFirstWellShoulders
