/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkActionFlightFloor
public import PlasmaLean.Design.DommaschkActionHeightInverse
public import PlasmaLean.Theory.Kinetic.MirrorActionHeightShift

/-! # Comparing two radial labels by shifting the pilot height -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFiniteRadialAction
open Set Certificates.PositionFrameSlabs Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope
open Kinetic.MirrorActionInverseBounds DommaschkMirrorBandAction DommaschkMirrorBandFlightIdentity
open DommaschkActionFlightFloor DommaschkFirstMirrorLaunchSign
open DommaschkActionHeightInverse (ambient)

/-- Quantitative height coordinate on the same pilot trajectory as the absolute action cap. -/
def HeightScale (y : ℝ → Plane) : Prop :=
  Secants (fun h : Heights => ambient y h) allFloor 264 ∧
    InverseBounds (fun h : Heights => ambient y h) allFloor 264

theorem height_scale {y : ℝ → Plane} {φ : ℝ} (identity : Identity y)
    (times : TimeBounds φ y) : HeightScale y := by
  obtain ⟨p, m, spec, _⟩ := identity
  let T := fun h => oneWayBounceTime (density y) (profile y) h (-bound) bound
  have der (h : ℝ) (hh : h ∈ Heights) : HasDerivAt (ambient y) (T h) h :=
    (spec ⟨h, hh⟩).2.2.1.congr_deriv (spec ⟨h, hh⟩).2.1.symm
  have rate (h : ℝ) (hh : h ∈ Heights) : allFloor < T h ∧ T h < 264 := by
    obtain ⟨l, hl, r, hr, _, well, _, _, low, high, _⟩ := times h hh
    let k : Heights := ⟨h, hh⟩
    have er := p.unique_time k r (Ioo_subset_Icc_self hr)
      (by simpa only [k, DommaschkNativeWellAction.field, one_mul] using well.right_hit)
    have el := m.unique_time k (-l) ⟨by linarith [hl.2], by linarith [hl.1]⟩
      (by simpa only [k, DommaschkNativeWellAction.field, neg_one_mul, neg_neg] using well.left_hit)
    rw [show l = -m.time k by linarith only [el], er] at low high
    have eq : T h = oneWayBounceTime (density y) (profile y) h (-m.time k) (p.time k) :=
      (spec k).2.1
    rw [eq]
    exact ⟨low, high⟩
  have sec := secants_of_derivatives der rate
  exact ⟨sec, inverse_of_secants (by norm_num [allFloor]) (by norm_num) sec⟩

/-- The observed range of pilot first-well actions has an absolute minimum width. -/
theorem endpoint_width {y : ℝ → Plane} (scale : HeightScale y) :
    71 / 2500 < ambient y (height true) - ambient y (height false) := by
  have hh : (height false : ℝ) ≤ height true := by norm_num [height]
  let low : Heights := ⟨height false, le_rfl, hh⟩
  let high : Heights := ⟨height true, hh, le_rfl⟩
  have inc := (scale.1 low high (by change (height false : ℝ) < height true; norm_num [height])).1
  change allFloor * ((height true : ℝ) - height false) <
    ambient y (height true) - ambient y (height false) at inc
  exact lt_trans (by norm_num [allFloor, height]) inc

/-- The clipped pilot integral on its fixed window is the action between any nominated
pair of first mirrors at the same height. -/
theorem first_action {y : ℝ → Plane} {φ h l r : ℝ} (identity : Identity y)
    (times : TimeBounds φ y) (hh : h ∈ Heights) (well : LaunchWell (profile y) 0 h l r)
    (bf : ContinuousOn (profile y) (Icc (-bound) bound))
    (bw : ContinuousOn (density y) (Icc (-bound) bound)) :
    ambient y h = action (profile y) (density y) l r h := by
  obtain ⟨l', hl, r', hr, _, first, _⟩ := times h hh
  obtain ⟨rfl, rfl⟩ := first.unique well
  obtain ⟨p, m, _⟩ := identity
  let k : Heights := ⟨h, hh⟩
  have er := p.unique_time k r' (Ioo_subset_Icc_self hr)
    (by simpa only [profile, k, one_mul] using well.right_hit)
  have el := m.unique_time k (-l') ⟨by linarith [hl.2], by linarith [hl.1]⟩
    (by simpa only [profile, k, neg_one_mul, neg_neg] using well.left_hit)
  apply action_eq_between hl.1.le (well.left_lt.trans well.lt_right).le hr.2.le bf bw
  · intro t ht
    rcases ht.2.eq_or_lt with eq | lt'
    · exact eq ▸ well.left_hit.ge
    · have after := m.after k (-t) ⟨by linarith only [el, lt'], by linarith only [ht.1]⟩
      simpa only [profile, k, neg_one_mul, neg_neg] using after.le
  · intro t ht
    rcases ht.1.eq_or_lt with eq | lt'
    · exact eq ▸ well.right_hit.ge
    · have after := p.after k t ⟨by linarith only [er, lt'], ht.2⟩
      simpa only [profile, k, one_mul] using after.le

/-- At radial spacing 1/125, two pointwise comparisons on the raised pilot well
imply an action increment exceeding 1/375 between the true first wells.
Only the base trajectory needs a certified height derivative. -/
theorem finite_increment {y : ℝ → Plane} {φ h l r L R : ℝ} {g v : ℝ → ℝ}
    (scale : HeightScale y) (known : TimeBounds φ y) (h0 : h ∈ Heights)
    (h1 : h + 1 / 18000 ∈ Heights)
    (base : LaunchWell (profile y) 0 (h + 1 / 18000) l r)
    (identified : action (profile y) (density y) l r (h + 1 / 18000) =
      ambient y (h + 1 / 18000))
    (other : LaunchWell g 0 h L R)
    (bf : ContinuousOn (profile y) (Icc l r)) (bw : ContinuousOn (density y) (Icc l r))
    (gf : ContinuousOn g (Icc L R)) (gv : ContinuousOn v (Icc L R))
    (vn : ∀ t ∈ Icc L R, 0 ≤ v t)
    (pair : ∀ t ∈ Ioo l r,
      3999 / 4000 * density y t ≤ v t ∧ g t ≤ profile y t - 1 / 18000) :
    L ≤ l ∧ r ≤ R ∧ 1 / 375 < action g v L R h - ambient y h := by
  obtain ⟨left, right, cmp⟩ := base.transfer_height other bf bw gf gv vn (by
    intro t ht
    exact ⟨(pair t ht).1, by linarith only [(pair t ht).2]⟩)
  rw [identified] at cmp
  obtain ⟨l', _, r', _, _, first, cap, _⟩ := known _ h1
  obtain ⟨rfl, rfl⟩ := first.unique base
  change action (profile y) (density y) _ _ _ ≤ _ at cap
  rw [identified] at cap
  have inc := (scale.1 ⟨h, h0⟩ ⟨h + 1 / 18000, h1⟩ (by
    change h < h + 1 / 18000
    linarith)).1
  change allFloor * ((h + 1 / 18000) - h) < ambient y (h + 1 / 18000) - ambient y h at inc
  norm_num [allFloor, DommaschkActionArchiveMass.mass] at cap inc
  exact ⟨left, right, by linarith only [cmp, cap, inc]⟩

/-- A second line can be certified by comparing its two observables directly against the
shifted pilot well. The only hypotheses on the second line are its own first-well data. -/
def PairTest (y : ℝ → Plane) : Prop :=
  ∀ h ∈ Heights, h + 1 / 18000 ∈ Heights →
    ∀ l r, LaunchWell (profile y) 0 (h + 1 / 18000) l r →
    ∀ (g v : ℝ → ℝ) L R, LaunchWell g 0 h L R →
      ContinuousOn g (Icc L R) → ContinuousOn v (Icc L R) → (∀ t ∈ Icc L R, 0 ≤ v t) →
      (∀ t ∈ Ioo l r, 3999 / 4000 * density y t ≤ v t ∧ g t ≤ profile y t - 1 / 18000) →
      L ≤ l ∧ r ≤ R ∧ 1 / 375 < action g v L R h - ambient y h

theorem pair_test {y : ℝ → Plane} {φ : ℝ} (identity : Identity y) (times : TimeBounds φ y)
    (bf : ContinuousOn (profile y) (Icc (-bound) bound))
    (bw : ContinuousOn (density y) (Icc (-bound) bound)) : PairTest y := by
  intro h h0 h1 l r base g v L R other gf gv vn pair
  obtain ⟨l', hl, r', hr, _, first, _⟩ := times _ h1
  obtain ⟨rfl, rfl⟩ := first.unique base
  have sub : Icc l' r' ⊆ Icc (-bound) bound := Icc_subset_Icc hl.1.le hr.2.le
  exact finite_increment (height_scale identity times) times h0 h1 base
    (first_action identity times h1 base bf bw).symm other (bf.mono sub) (bw.mono sub)
    gf gv vn pair

end PlasmaLean.Design.DommaschkFiniteRadialAction
