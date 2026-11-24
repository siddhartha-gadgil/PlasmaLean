/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkMirrorBandFlightIdentity
public import PlasmaLean.Design.DommaschkRowFlightBudget
public import PlasmaLean.Theory.Kinetic.MirrorActionInverseBounds

/-! # Quantitative recovery of mirror height from the true first-well action -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkActionHeightInverse

open Set Certificates.PositionFrameSlabs DommaschkMirrorBandAction DommaschkFirstMirrorLaunchSign
open DommaschkMirrorBandFlightIdentity DommaschkRowFlightBudget Kinetic.MirrorActionInverseBounds
open Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope

abbrev ambient (y : ℝ → Plane) := action (profile y) (density y) (-bound) bound

abbrev time (y : ℝ → Plane) (p : Outward y 1) (m : Outward y (-1)) (h : Heights) :=
  oneWayBounceTime (density y) (profile y) h (-m.time h) (p.time h)

/-- The first-well action has a quantitative inverse over its entire attained interval.
The slopes are the same physical flight times that occur between these very first mirrors. -/
def Calibration (y : ℝ → Plane) : Prop :=
  ∃ (p : Outward y 1) (m : Outward y (-1)),
    (∀ h : Heights, wellAction y p m h = ambient y h ∧
      HasDerivAt (ambient y) (time y p m h) (h : ℝ) ∧ 14 < time y p m h ∧ time y p m h < 264) ∧
    Secants (wellAction y p m) 14 264 ∧ InverseBounds (wellAction y p m) 14 264 ∧
    range (wellAction y p m) = Icc (ambient y (height false)) (ambient y (height true))

/-- Identify the first contact on each unique outward branch before combining its action
derivative with the quantitative mirror-to-mirror time on the same trajectory. -/
theorem of_identity {y : ℝ → Plane} {φ : ℝ} (actual : Identity y) (whole : WholeTime φ y) :
    Calibration y := by
  obtain ⟨p, m, atHeight, _⟩ := actual
  have exactTime (h : Heights) : 14 < time y p m h ∧ time y p m h < 264 := by
    obtain ⟨l, hl, r, hr, _, well, _, lo, hi⟩ := whole h h.2
    change l ∈ Ioo (-(325 / 64)) (-(316 / 64)) at hl
    have er := p.unique_time h r (Ioo_subset_Icc_self hr)
      (by simpa only [one_mul] using well.right_hit)
    have el := m.unique_time h (-l) ⟨by linarith [hl.2], by linarith [hl.1]⟩
      (by simpa only [neg_one_mul, neg_neg] using well.left_hit)
    rw [show l = -m.time h by linarith only [el], er] at lo hi
    exact ⟨lo, hi⟩
  let T := fun t => oneWayBounceTime (density y) (profile y) t (-bound) bound
  have deriv (h : ℝ) (hh : h ∈ Heights) : HasDerivAt (ambient y) (T h) h :=
    (atHeight ⟨h, hh⟩).2.2.1.congr_deriv (atHeight ⟨h, hh⟩).2.1.symm
  have rate (h : ℝ) (hh : h ∈ Heights) : 14 < T h ∧ T h < 264 := by
    have eq : T h = time y p m ⟨h, hh⟩ := (atHeight ⟨h, hh⟩).2.1
    rw [eq]
    exact exactTime _
  have sec := secants_of_derivatives deriv rate
  have equal : wellAction y p m = fun h : Heights => ambient y h :=
    funext (fun h => (atHeight h).1)
  have concrete : Secants (wellAction y p m) 14 264 := equal ▸ sec
  refine ⟨p, m, fun h => ⟨(atHeight h).1, (atHeight h).2.2.1, exactTime h⟩, concrete,
    inverse_of_secants (by norm_num) (by norm_num) concrete, ?_⟩
  rw [equal]
  apply range_eq_interval (by norm_num [height])
    (fun h hh => (deriv h hh).continuousAt.continuousWithinAt)
  intro h hh k hk order
  rcases order.eq_or_lt with rfl | strict
  · exact le_rfl
  · have inc := (sec ⟨h, hh⟩ ⟨k, hk⟩ strict).1
    change 14 * (k - h) < ambient y k - ambient y h at inc
    linarith

/-- The action width across the two actual archived endpoint heights is strictly
between these rational values. -/
theorem endpoint_width {y : ℝ → Plane} (h : Calibration y) :
    9046573590327 / 1250000000000000 <
      ambient y (height true) - ambient y (height false) ∧
    ambient y (height true) - ambient y (height false) < 42648132640113 / 312500000000000 := by
  obtain ⟨p, m, phys, inc, _, _⟩ := h
  have ord : (height false : ℝ) ≤ height true := by norm_num [height]
  let lo : Heights := ⟨height false, le_rfl, ord⟩
  let hi : Heights := ⟨height true, ord, le_rfl⟩
  have v := inc lo hi (by change (height false : ℝ) < height true; norm_num [height])
  rw [(phys lo).1, (phys hi).1] at v
  convert v using 2 <;> norm_num [lo, hi, height]

end PlasmaLean.Design.DommaschkActionHeightInverse
