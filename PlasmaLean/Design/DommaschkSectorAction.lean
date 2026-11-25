/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkRadialSectionAction
public import PlasmaLean.Theory.Fields.MovingBirthClock
public import PlasmaLean.Theory.Kinetic.ContinuousFirstWellAction

/-! # The compact locus of prescribed first-well actions on the launch sector -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSectorAction
open Set Fields Contract Forms Theory.KAM WEll1Z2 DommaschkKamC KamNewton
open Certificates.PositionFrameSlabs (Plane coordinates)
open DommaschkRadialActionAlternative DommaschkRadialFamilyContinuity
open DommaschkRadialSectionAction DommaschkMirrorLaunch DommaschkFirstMirrorWell
open DommaschkSignedTraceDomain DommaschkCartesianAngleFlow DommaschkCompactLaunchPhases
open DommaschkNativeWellAction Kinetic.FirstWellContinuation Kinetic.MirrorActionEnvelope
open Kinetic.MirrorHeightAction

abbrev Phase := Icc (-(1 / 2 ^ 19 : ℝ)) (1 / 2 ^ 19)
abbrev Parameter := Phase × Radius

theorem continuous_sector_birth {uC zC uA zA : FA}
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA)) :
    Continuous fun p : Parameter => location uC zC uA zA p.2 p.1 := by
  have phase : Continuous (fun p : Parameter => ((0 : ℝ), (p.1 : ℝ))) :=
    continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)
  have u : Continuous (fun p : Parameter => (p.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
  have combine {f g : Parameter → ℝ} (cf : Continuous f) (cg : Continuous g) :
      Continuous fun p : Parameter => blend p.2 (f p) (g p) :=
    ((continuous_const.sub u).mul cf).add (u.mul cg)
  exact continuous_cylinder
    (combine (ec.contDiff_R.continuous.comp phase) (ea.contDiff_R.continuous.comp phase))
    (continuous_subtype_val.comp continuous_fst)
    (combine (ec.contDiff_z.continuous.comp phase) (ea.contDiff_z.continuous.comp phase))

set_option maxRecDepth 12000 in
/-- The field and arclength density are jointly continuous across phase, radius and azimuth.
The birth clock itself is the varying original phase. -/
theorem capped_sector {uC zC uA zA : FA} {Y : Parameter → ℝ → Plane}
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA))
    (born : ∀ p, Y p p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1))
    (paths : ∀ p, Enclosed (Y p) (-cap) cap) (signs : ∀ p, Signs (Y p)) :
    CappedFamily (fun p => field (Y p)) (fun p => density (Y p)) (fun _ => level) cap := by
  have cb : Continuous fun p : Parameter => point (Y p) p.1 :=
    (continuous_sector_birth ec ea).congr fun p => by
      unfold point location
      rw [born p]
      rfl
  have joint := TrajectoryFamily.continuousOn_of_moving_birth (V := velocity)
    (compact_window (-cap) cap) (fun _ hx => velocity_smooth (window_regular hx))
    (continuous_subtype_val.comp continuous_fst : Continuous (fun p : Parameter => (p.1 : ℝ)))
    (fun p => Icc_subset_Icc (by norm_num [cap]) (by norm_num [cap]) p.1.property) cb
    (fun p t ht => (paths p).cartesian ht) (fun p t ht => point_mem ht ((paths p).region t ht))
  have reg (q : Parameter × ℝ) (hq : q ∈ (univ : Set Parameter) ×ˢ Icc (-cap) cap) :
      point (Y q.1) q.2 ∈ regular := in_regular ((paths q.1).region q.2 hq.2) q.2
  refine ⟨by norm_num [cap], continuous_const, ?_, ?_, fun p => (signs p).low,
    fun p => (signs p).back, fun p => (signs p).front⟩
  · intro q hq
    change ContinuousWithinAt (fun z : Parameter × ℝ => ‖B (point (Y z.1) z.2)‖) _ q
    exact (strength_smooth (reg q hq)).continuousAt.comp_continuousWithinAt
      (f := fun z : Parameter × ℝ => point (Y z.1) z.2) (joint q hq)
  · have cv : ContinuousOn (fun q : Parameter × ℝ => ‖velocity (point (Y q.1) q.2)‖)
        (univ ×ˢ Icc (-cap) cap) := fun q hq =>
      (velocity_smooth (reg q hq)).continuousAt.norm.comp_continuousWithinAt
        (f := fun z : Parameter × ℝ => point (Y z.1) z.2) (joint q hq)
    exact cv.congr fun q hq => (paths q.1).density_eq hq.2

/-- The target set contains exactly the original first wells attaining the target.
It is compact and has an interior-radius representative at every phase. -/
def Sector (uC zC uA zA : FA) : Prop :=
  ∃ (Y : Parameter → ℝ → Plane) (L R J : Parameter → ℝ),
    (∀ p, Y p p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧
      Enclosed (Y p) (-cap) cap ∧ LaunchWell (field (Y p)) 0 level (L p) (R p) ∧
      deriv (field (Y p)) (L p) ≠ 0 ∧ deriv (field (Y p)) (R p) ≠ 0 ∧
      J p = action (field (Y p)) (density (Y p)) (L p) (R p) level) ∧
    Continuous L ∧ Continuous R ∧ Continuous J ∧ IsCompact {p | J p = target} ∧
    ∀ φ : Phase, ∃ u : Radius, (u : ℝ) ∈ Ioo (47 / 100) (239 / 500) ∧ J (φ, u) = target

theorem sector_of_sections {uC zC uA zA : FA}
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA))
    (entries : ∀ φ : Phase, Entries uC zC uA zA φ) (sections : Sections fun y => Signs y ∧ Simple y)
    (compare : ∀ (φ : Phase) (Y : Radius → ℝ → Plane),
      (∀ u, Y u φ = coordinates.symm (birth uC zC uA zA u φ)) →
      (∀ u, Enclosed (Y u) (-cap) cap) → (∀ u, Signs (Y u)) → Alternative Y) :
    Sector uC zC uA zA := by
  have each (p : Parameter) : ∃ y : ℝ → Plane,
      y p.1 = coordinates.symm (birth uC zC uA zA p.2 p.1) ∧
      Enclosed y (-cap) cap ∧ (Signs y ∧ Simple y) := by
    obtain ⟨k, _, passage⟩ := entries p.1 p.2
    exact from_section (abs_le.mpr p.1.property) passage sections
  choose Y born path obs using each
  have whole := capped_sector ec ea born path fun p => (obs p).1
  obtain ⟨L, R, cl, cr, well, cj⟩ := whole.continuous_first_wells fun p => (obs p).2
  let J (p : Parameter) := action (field (Y p)) (density (Y p)) (L p) (R p) level
  refine ⟨Y, L, R, J, fun p => ⟨born p, path p, well p, ((obs p).2 _ _ (well p)).1,
    ((obs p).2 _ _ (well p)).2, rfl⟩, cl, cr, cj, (isClosed_eq cj continuous_const).isCompact, ?_⟩
  intro φ
  have alt := compare φ (fun u => Y (φ, u)) (fun u => born (φ, u)) (fun u => path (φ, u))
    (fun u => (obs (φ, u)).1)
  obtain ⟨u, l, r, interior, w, value⟩ := prescribed_of_regular alt fun u => (obs (φ, u)).2
  obtain ⟨el, er⟩ := (well (φ, u)).unique w
  exact ⟨u, interior, by simpa only [J, el, er] using value⟩

end PlasmaLean.Design.DommaschkSectorAction
