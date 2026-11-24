/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalArcTrace
public import PlasmaLean.Design.DommaschkActionArchiveMass
public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import PlasmaLean.Design.DommaschkSignedTraceDensity
public import PlasmaLean.Theory.Kinetic.MirrorActionEnvelope

/-! # The true one-way action in the well between the two physical first mirrors -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkNativeWellAction
open Set Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkPhysicalActionPanel
open DommaschkBounceField DommaschkJacobian DommaschkKam DommaschkMirrorTubeCrossing
open Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope

abbrev level : ℝ := 5300546391395933 / 5000000000000000
abbrev target : ℝ := 6799610938322487 / 5000000000000000
def density (y : ℝ → Plane) (t : ℝ) : ℝ :=
  ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖
def field (y : ℝ → Plane) (t : ℝ) : ℝ := strength t (y t)

theorem continuous_inputs {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State}
    {fr br : List Step} {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y)
    {a b : ℝ} (inside : Icc a b ⊆ Ioo (-(n : ℝ) / 64) (n / 64))
    (valid : ∀ t ∈ Icc a b, DommaschkSignedTraceDomain.Region (y t)) :
    ContinuousOn (field y) (Icc a b) ∧ ContinuousOn (density y) (Icc a b) := by
  have cont : ContinuousOn y (Icc a b) := by
    intro t ht
    have h := inside ht
    exact ((path.ode t (Ioo_subset_Icc_self h)).hasDerivAt
      (Icc_mem_nhds h.1 h.2)).continuousAt.continuousWithinAt
  have cf : ContinuousOn (field y) (Icc a b) := by
    change ContinuousOn (fun t => strength t (y t)) (Icc a b)
    simpa only [one_mul] using
      continuousOn_strength cont 1 (fun t ht => by linarith [(valid t ht).1.1])
  refine ⟨cf, (DommaschkSignedTraceDensity.continuousOn_density_region cont valid).congr ?_⟩
  intro t ht
  have box := valid t ht
  have positive := DommaschkSignedTraceDenominator.regular t box.1 box.2
  exact arcDensity_on_path path (inside ht) (by linarith [box.1.1]) (by linarith)

/-- Both contacts belong to the component of the launch, the core gives a lower
bound on its action, and the complete padded quadrature gives a strict upper bound. -/
def FirstWellAction (y : ℝ → Plane) : Prop :=
  ∃ l ∈ Ioo (-325 / 64:ℝ) (-324 / 64), ∃ r ∈ Ioo (324 / 64:ℝ) (325 / 64),
    LaunchWell (field y) 0 level l r ∧
    553 / 2000 < action (field y) (density y) l r level ∧
    action (field y) (density y) (-324 / 64) (324 / 64) level ≤
      action (field y) (density y) l r level ∧
    action (field y) (density y) l r level ≤
      action (field y) (density y) (-325 / 64) (325 / 64) level ∧
    action (field y) (density y) (-325 / 64) (325 / 64) level ≤ DommaschkActionArchiveMass.mass ∧
    DommaschkActionArchiveMass.mass < target

theorem first_well {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y) (reached : 325 < n)
    (valid : ∀ t ∈ Icc (-325 / 64) (325 / 64), DommaschkSignedTraceDomain.Region (y t))
    (floor : 553 / 2000 < action (field y) (density y) (-316 / 64) (316 / 64) level)
    (covers : Certificates.MirrorActionQuadrature.Covers true (density y) (field y) level
      (-325 / 64) DommaschkActionQ0R470.slabs)
    (hits : DommaschkSignedMirrorSlope.FirstTransverseBoth
      (324 / 64) (325 / 64) level (1 / 400) y) :
    FirstWellAction y := by
  obtain ⟨⟨r, rb, rh, rf, _⟩, l, lb, lh, lf, _⟩ := hits
  have well : LaunchWell (field y) 0 level (-l) r := by
    refine ⟨by linarith [lb.1], by linarith [rb.1], lh, rh, ?_⟩
    intro u hu
    rcases le_total 0 u with h | h
    · exact rf u ⟨h,hu.2⟩
    · simpa only [neg_neg, field] using lf (-u) ⟨by linarith, by linarith [hu.1]⟩
  have room : (325:ℝ) < n := by exact_mod_cast reached
  obtain ⟨cf,cw⟩ := continuous_inputs path
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) valid
  have core (t : ℝ) (ht : t ∈ Ioo (-324 / 64:ℝ) (324 / 64)) : field y t < level :=
    well.accessible t ⟨by linarith [lb.1,ht.1], by linarith [rb.1,ht.2]⟩
  obtain ⟨lower,upper⟩ := well.action_bounds (by linarith [lb.2] : -325 / 64 ≤ -l) rb.2.le
    (by norm_num : (-324:ℝ) / 64 ≤ 0) (by norm_num : (0:ℝ) ≤ 324 / 64) core cf cw
    (fun t _ => norm_nonneg _)
  have core_growth := action_mono_interval (by norm_num : (-324:ℝ) / 64 ≤ -316 / 64)
    (by norm_num : (-316:ℝ) / 64 ≤ 316 / 64) (by norm_num : (316:ℝ) / 64 ≤ 324 / 64)
    (h := level) (cf.mono (Icc_subset_Icc (by norm_num) (by norm_num)))
    (cw.mono (Icc_subset_Icc (by norm_num) (by norm_num))) (fun t _ => norm_nonneg _)
  exact ⟨-l, ⟨by linarith [lb.2], by linarith [lb.1]⟩, r, rb, well,
    floor.trans_le (core_growth.trans lower), lower, upper,
    DommaschkActionArchiveMass.closed_upper covers (fun t _ => norm_nonneg _) cf cw,
    by norm_num [DommaschkActionArchiveMass.mass,target]⟩

end PlasmaLean.Design.DommaschkNativeWellAction
