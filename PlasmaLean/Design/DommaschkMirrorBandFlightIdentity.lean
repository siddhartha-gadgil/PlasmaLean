/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorBandPassage
public import PlasmaLean.Theory.Kinetic.MirrorActionTransverse

/-! # Height derivative of the true Cartesian action at each first-mirror pair -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkMirrorBandFlightIdentity

open Certificates.PositionFrameSlabs DommaschkMirrorBandAction DommaschkSignedTraceDomain
open DommaschkSignedTraceDensity DommaschkSignedObservable DommaschkPhysicalActionPanel
open DommaschkFirstMirrorLaunchSign DommaschkMirrorTubeCrossing Kinetic Set MeasureTheory
open MirrorHeightAction MirrorActionEnvelope MirrorActionFlight

abbrev bound : ℝ := 325 / 64

abbrev profile (y : ℝ → Plane) (t : ℝ) := strength t (y t)

abbrev density (y : ℝ → Plane) (t : ℝ) := arcDensity (y t 0) t (y t 1)

/-- Both observables use the same signed trajectory and the same first mirrors at every
height. The clipped action is an ambient real function, so its derivative also makes sense
at the two endpoints of the archived height band. -/
def Identity (y : ℝ → Plane) : Prop :=
  ∃ (p : Outward y 1) (m : Outward y (-1)),
    (∀ h : Heights,
      wellAction y p m h = action (profile y) (density y) (-bound) bound h ∧
      oneWayBounceTime (density y) (profile y) h (-bound) bound =
        oneWayBounceTime (density y) (profile y) h (-m.time h) (p.time h) ∧
      HasDerivAt (action (profile y) (density y) (-bound) bound)
        (oneWayBounceTime (density y) (profile y) h (-m.time h) (p.time h)) (h : ℝ) ∧
      0 < oneWayBounceTime (density y) (profile y) h (-m.time h) (p.time h)) ∧
    ∀ i j : Heights, wellAction y p m j - wellAction y p m i =
      ∫ h in (i : ℝ)..(j : ℝ), oneWayBounceTime (density y) (profile y) h (-bound) bound

theorem on_path {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path 325 fs bs fr br x y) (region : ∀ t ∈ Icc (-bound) bound, Region (y t))
    (family : ActionFamily y) : Identity y := by
  obtain ⟨p, m, _, _, action_eq⟩ := family
  have cy₀ : ContinuousOn y (Icc (-((325 : ℕ) : ℝ) / 64) (((325 : ℕ) : ℝ) / 64)) :=
    fun t ht => (path.ode t ht).continuousWithinAt
  have cy : ContinuousOn y (Icc (-bound) bound) := by norm_num [bound] at cy₀ ⊢; exact cy₀
  have cf : ContinuousOn (profile y) (Icc (-bound) bound) := by
    simpa only [profile, one_mul] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) (region t ht).1.1)
  have cw : ContinuousOn (density y) (Icc (-bound) bound) := continuousOn_density_region cy region
  refine ⟨p, m, ?_, ?_⟩
  · intro h
    have mp := m.interior_time h
    have pp := p.interior_time h
    have al : -bound ≤ -m.time h := neg_le_neg mp.2.le
    have rb : p.time h ≤ bound := pp.2.le
    have well : LaunchWell (profile y) 0 h (-m.time h) (p.time h) := by
      refine ⟨by linarith [mp.1], by linarith [pp.1], ?_, ?_, ?_⟩
      · simpa only [profile, neg_one_mul] using m.hit h
      · simpa only [profile, one_mul] using p.hit h
      · intro t ht
        rcases le_total 0 t with pos | neg
        · simpa only [profile, one_mul] using p.before h t ⟨pos, ht.2⟩
        · simpa only [profile, neg_one_mul, neg_neg] using
            m.before h (-t) ⟨neg_nonneg.mpr neg, by linarith [ht.1]⟩
    have left (t : ℝ) (ht : t ∈ Ico (-bound) (-m.time h)) : (h : ℝ) < profile y t := by
      simpa only [profile, neg_one_mul, neg_neg] using
        m.after h (-t) ⟨by linarith [ht.2], (neg_le.mp ht.1)⟩
    have right (t : ℝ) (ht : t ∈ Ioc (p.time h) bound) : (h : ℝ) < profile y t := by
      simpa only [profile, one_mul] using p.after h t ht
    obtain ⟨vp, vp_rate, dp⟩ := p.transverse h
    obtain ⟨vm, vm_rate, dm⟩ := m.transverse h
    have positive : (0 : ℝ) < (1 / 400) / (2 * (h : ℝ)) := by
      have low := h.2.1
      change (height false : ℝ) ≤ h at low
      exact div_pos (by norm_num) (mul_pos (by norm_num)
        (lt_of_lt_of_le (by norm_num [height]) low))
    have dr : HasDerivAt (profile y) vp (p.time h) := by simpa only [profile, one_mul] using dp
    have refl : HasDerivAt (fun t => profile y (-t)) vm (- -m.time h) := by
      simpa only [profile, neg_one_mul, neg_neg] using dm
    have dl : HasDerivAt (profile y) (-vm) (-m.time h) := by
      simpa only [Function.comp_def, neg_neg, mul_neg_one] using
        refl.comp (-m.time h) (hasDerivAt_neg (-m.time h))
    have sub : Icc (-m.time h) (p.time h) ⊆ Icc (-bound) bound := Icc_subset_Icc al rb
    obtain ⟨it, pos⟩ := well.finite_bounce_time (cf.mono sub) (cw.mono sub)
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8)
        (density_lower t (region t (sub (Ioo_subset_Icc_self ht)))))
      dl (neg_neg_of_pos (positive.trans vm_rate)) dr (positive.trans vp_rate)
    have time_eq := time_eq_between al rb it
      (fun t ht => ht.2.eq_or_lt.elim (fun hit => hit.symm ▸ well.left_hit.ge)
        (fun lt => (left t ⟨ht.1, lt⟩).le))
      (fun t ht => ht.1.eq_or_lt.elim (fun hit => hit ▸ well.right_hit.ge)
        (fun lt => (right t ⟨lt, ht.2⟩).le))
    have d := hasDerivAt_two_mirrors al rb well cf cw left right dl
      (ne_of_lt (neg_neg_of_pos (positive.trans vm_rate))) dr (positive.trans vp_rate).ne'
    exact ⟨action_eq h, time_eq, d.congr_deriv time_eq, pos⟩
  · intro i j
    rw [action_eq i, action_eq j]
    exact (compact_window (by norm_num [bound]) cf cw i j).2

end PlasmaLean.Design.DommaschkMirrorBandFlightIdentity
