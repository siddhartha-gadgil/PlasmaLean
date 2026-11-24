/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorBranchBracket
public import PlasmaLean.Design.DommaschkLowerActionPath
public import PlasmaLean.Design.DommaschkCommonLittlejohnTime
public import PlasmaLean.Design.DommaschkEndpointTraceFamily
public import PlasmaLean.Design.DommaschkSignedBirthApproach

/-! # Transverse physical mirror births on either side of a phase-zero section -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
open Set Certificates.PositionFrameSlabs DommaschkLowerActionPath DommaschkMirrorLaunch
open DommaschkFirstMirrorWell DommaschkCartesianAngleFlow DommaschkCartesianMirrorBirth
open DommaschkCommonLittlejohnTime (UniformAt BandAt)
open DommaschkFirstMirrorLaunchSign DommaschkTrappedBirthCoordinates DommaschkSignedTraceDomain
open DommaschkSignedObservable DommaschkEndpointSignedTrace
open Kinetic.MirrorHeightBand Kinetic.MirrorWellPersistence Contract.TrappedBirthCoordinates

set_option maxRecDepth 12000

/-- The full Cartesian position-height neighborhood and the two accessible velocity lifts
are found around the same physical position. -/
def OpenBirth (x : Fields.Space) : Prop :=
  (∀ h ∈ Icc (height false : ℝ) (height true), (x,h) ∈ interior regularBirths) ∧ Lifted x ∧
    UniformAt x ∧ BandAt x

/-- A strictly exterior cap in each direction and an ODE on a larger closed interval give
openness even at the two boundary heights. -/
theorem open_birth {entry : State} {fr br : List Step} {T a b φ : ℝ} {y : ℝ → Plane}
    (path : Signed entry fr br T y) (room : b < T) (angle : |φ| ≤ a)
    (region : ∀ t ∈ Icc (-b) b, Region (y t))
    (fwd : Branch (field y) a b (height false) (height true) (1 / 400))
    (back : Branch (fun t => field y (-t)) a b (height false) (height true) (1 / 400)) :
    OpenBirth (point y φ) := by
  have ab : a < b := by
    have j := fwd.interior_time ⟨height false,le_rfl,by norm_num [height]⟩
    exact j.1.trans j.2
  have inside : φ ∈ Ioo (-b) b := ⟨(neg_lt_neg ab).trans_le (abs_le.mp angle).1,
    (abs_le.mp angle).2.trans_lt ab⟩
  have both (h : ℝ) (hh : h ∈ Icc (height false : ℝ) (height true)) :
      (point y φ,h) ∈ interior regularBirths ∧ ‖B (point y φ)‖ < h := by
    have positive : 0 < h := (by norm_num [height] : 0 < (height false : ℝ)).trans_le hh.1
    have bracket := fwd.bracket back ⟨h,hh⟩ (by change 0 < 1 / 400 / (2 * h); positivity) angle
    have flow : FlowBracketIn velocity (fun q => ‖B q‖) regular (-b) φ b (point y φ,h) := by
      refine ⟨point y,rfl,?_,bracket,fun t ht => in_regular (region t ht) t⟩
      intro t ht
      have mid : t ∈ Ioo (-T) T := ⟨(neg_lt_neg room).trans_le ht.1,ht.2.trans_lt room⟩
      exact cartesian_ode ((path.ode t (Ioo_subset_Icc_self mid)).hasDerivAt
        (Icc_mem_nhds mid.1 mid.2)) (region t ht)
    obtain ⟨W,op,here,sub⟩ := regular_birth_open_of_local isOpen_regular inside.1 inside.2
      (fun q hq => (velocity_smooth hq).contDiffWithinAt)
      (fun q hq => (strength_smooth hq).contDiffWithinAt)
      (fun q hq => (speed_smooth hq).continuousAt.continuousWithinAt)
      (fun q hq => ⟨rfl,speed_pos hq,field_ne_zero hq,aligned hq⟩) flow
    exact ⟨interior_maximal sub op here,fwd.central_below back ⟨h,hh⟩ (abs_le.mp angle)⟩
  have cart := in_regular (region φ (Ioo_subset_Icc_self inside)) φ
  have lifted : Lifted (point y φ) := by
    intro m e h hm he hh neg S energies pitches supp ener pitch
    exact lift_mem_interior neg hm he (both h hh).2 (strength_smooth cart).continuousAt
      supp ener pitch (both h hh).1
  have uniform := DommaschkCommonLittlejohnTime.uniform_of_lifted cart (fun h hh => (both h hh).2)
    lifted
  exact ⟨fun h hh => (both h hh).1,lifted,uniform,uniform.band⟩

/-- A single Cartesian position-height radius works along a closed signed arc and at both
endpoint heights. The radius can depend on the trajectory. -/
def UniformTube (a : ℝ) (y : ℝ → Plane) : Prop :=
  ∃ δ > 0, Metric.cthickening δ ((point y '' Icc (-a) a) ×ˢ
    Icc (height false : ℝ) (height true)) ⊆ interior regularBirths

theorem tube_of_centers {a : ℝ} {y : ℝ → Plane}
    (cont : ContinuousOn (point y) (Icc (-a) a))
    (all : ∀ t ∈ Icc (-a) a, OpenBirth (point y t)) : UniformTube a y := by
  have compact := (isCompact_Icc.image_of_continuousOn cont).prod
    (isCompact_Icc (a := (height false : ℝ)) (b := height true))
  apply compact.exists_cthickening_subset_open isOpen_interior
  rintro ⟨x,h⟩ ⟨⟨t,ht,rfl⟩,hh⟩
  exact (all t ht).1 h hh

/-- A closed central arc of births and its common position-height neighborhood. -/
def Population (a : ℝ) (y : ℝ → Plane) : Prop :=
  (∀ t ∈ Icc (-a) a, OpenBirth (point y t)) ∧ UniformTube a y

theorem population {entry : State} {fr br : List Step} {T a b : ℝ} {y : ℝ → Plane}
    (path : Signed entry fr br T y) (room : b < T)
    (region : ∀ t ∈ Icc (-b) b, Region (y t))
    (fwd : Branch (field y) a b (height false) (height true) (1 / 400))
    (back : Branch (fun t => field y (-t)) a b (height false) (height true) (1 / 400)) :
    Population a y := by
  have ab : a < b := by
    have root := fwd.interior_time ⟨height false,le_rfl,by norm_num [height]⟩
    exact root.1.trans root.2
  have all (t : ℝ) (ht : t ∈ Icc (-a) a) :=
    open_birth path room (abs_le.mpr ht) region fwd back
  refine ⟨all,tube_of_centers ?_ all⟩
  intro t ht
  have atCap : t ∈ Icc (-b) b := ⟨(neg_le_neg ab.le).trans ht.1,ht.2.trans ab.le⟩
  have mid : t ∈ Ioo (-T) T := ⟨(neg_lt_neg room).trans_le atCap.1,atCap.2.trans_lt room⟩
  have d := (path.ode t (Ioo_subset_Icc_self mid)).hasDerivAt (Icc_mem_nhds mid.1 mid.2)
  exact (cartesian_ode d (region t atCap)).continuousAt.continuousWithinAt

/-- Use the ODE and the true pair of tube lists from any central section. -/
theorem signed_of_clock {n : ℕ} {fs bs entry : State} {fr br F G : List Step}
    {x : Plane} {y : ℝ → Plane} (p : Path n fs bs fr br x y)
    (forward : ∀ u ∈ physicalSlabs entry 0 F, ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t)
    (back : ∀ u ∈ physicalSlabs entry 0 G, ∀ t ∈ Icc u.start u.stop, y (-t) ∈ u.tube t) :
    Signed entry F G (n / 64) y := by
  obtain ⟨f,b⟩ := DommaschkSignedMirrorSlope.clock_odes p (a := 0) le_rfl (le_refl _)
  exact ⟨by simpa only [neg_div] using p.ode,
    ⟨fun t ht => (f t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2),forward⟩,
    ⟨fun t ht => (b t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2),back⟩⟩

open Theory.KAM
open DommaschkEndpointTraceFamily (Checkpoint)

/-- Preserve the original position, in the same time parameter as the entire signed
field line, while making the endpoint-dependent tubes available to the observer. -/
theorem at_original_birth {e : MirrorEndpoint} (phase : e.opposite = false)
    {c : Checkpoint} {uC zC uA zA : FA} {φ : ℝ} {P : (ℝ → Plane) → Prop}
    (passage : c.Passage e uC zC uA zA φ) (room : |φ| ≤ c.length / 64)
    (applyOn : ∀ y, Signed e.start c.forwardRows c.backwardRows (c.length / 64) y →
      (∀ t ∈ Icc (-(c.length : ℝ) / 64) (c.length / 64), Region (y t)) ∧ P y) :
    ∃ y, y φ = coordinates.symm (birth uC zC uA zA e.radius φ) ∧ P y := by
  obtain ⟨σ,a,unit,clock,src,approach,y,start,be,fe,ode,ft,bt⟩ := passage
  simp only [phase,azimuth,Bool.false_eq_true,↓reduceIte,sub_zero] at *
  -- The geometric path forgets the pilot-specific tube lists. Both actual lists are
  -- retained by the signed evidence handed to the observer below.
  have p : Path c.length c.forwardExit c.backwardExit [] [] (coordinates.symm (a |φ|)) y :=
    ⟨start,by simpa only [neg_div] using be,fe,by simpa only [neg_div] using ode,
      by simp [physicalSlabs],by simp [physicalSlabs]⟩
  obtain ⟨reg,property⟩ := applyOn y (signed_of_clock p ft bt)
  have same := DommaschkSignedBirthApproach.along p unit clock room approach (by
    intro t ht
    have r := reg t ht
    have den := DommaschkSignedTraceDenominator.regular t r.1 r.2
    exact ⟨by linarith [r.1.1],ne_of_gt (by linarith)⟩)
  have first := same (show (0 : ℝ) ∈ Icc 0 |φ| from ⟨le_rfl,abs_nonneg _⟩)
  refine ⟨y,?_,property⟩
  apply coordinates.injective
  simpa only [mul_zero,add_zero,src,ContinuousLinearEquiv.apply_symm_apply] using first.symm

end PlasmaLean.Design.DommaschkPhaseZeroRegularBirth
