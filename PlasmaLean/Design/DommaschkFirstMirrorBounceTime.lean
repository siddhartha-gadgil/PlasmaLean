/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorBounceTime
public import PlasmaLean.Design.DommaschkFirstMirrorWell
public import PlasmaLean.Design.DommaschkSignedBirthApproach

/-! # Finite one-way flight time in the first signed QA2R mirror wells -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstMirrorBounceTime
open Set MeasureTheory Certificates.PositionFrameSlabs Kinetic.MirrorActionEnvelope
open DommaschkSignedMirrorSlope DommaschkSignedObservable DommaschkMirrorTubeCrossing
open DommaschkSignedTraceDomain DommaschkPhysicalActionPanel
set_option maxRecDepth 8000

/-- The endpoints of the first mirror well bracket the launch angle and enclose
a finite positive integral of the genuine arclength density over parallel speed. -/
def Flight (a b h φ : ℝ) (y : ℝ → Plane) : Prop :=
  let f := fun s => strength s (y s)
  let w := fun s => arcDensity (y s 0) s (y s 1)
  ∃ l ∈ Ioo (-b) (-a), ∃ r ∈ Ioo a b, φ ∈ Ioo l r ∧ LaunchWell f 0 h l r ∧
    IntervalIntegrable (fun t => w t / Real.sqrt (2 * (h - f t))) volume l r ∧
    0 < oneWayBounceTime w f h l r

theorem of_contacts {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y) {a b h k φ : ℝ}
    (inside : |φ| ≤ a) (stop : b ≤ n / 64) (height : 0 < h) (rate : 0 < k)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (hits : FirstTransverseBoth a b h k y) : Flight a b h φ y := by
  obtain ⟨⟨r, rb, rh, pr, _, vr, rp, rd⟩, ⟨s, sb, sh, ps, _, vs, sp, sd⟩⟩ := hits
  let f := fun t => strength t (y t)
  have base : 0 ≤ a := (abs_nonneg φ).trans inside
  have well : LaunchWell f 0 h (-s) r := by
    refine ⟨by linarith [sb.1], by linarith [rb.1], sh, rh, ?_⟩
    intro t ht
    rcases le_total 0 t with right | left
    · exact pr t ⟨right, ht.2⟩
    · simpa only [neg_neg] using ps (-t) ⟨neg_nonneg.mpr left, by linarith [ht.1]⟩
  have sub : Icc (-s) r ⊆ Icc (-(n : ℝ) / 64) (n / 64) := by
    apply Icc_subset_Icc <;> linarith [sb.2, rb.2]
  have cy : ContinuousOn y (Icc (-s) r) :=
    fun t ht => ((path.ode t (sub ht)).mono sub).continuousWithinAt
  have reg (t) (ht : t ∈ Icc (-s) r) := region t (sub ht)
  have cf : ContinuousOn f (Icc (-s) r) := by
    simpa only [one_mul, f] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0:ℝ) < 7/8) (reg t ht).1.1)
  have positive := div_pos rate (by positivity : 0 < 2*h)
  have back : HasDerivAt (fun t => f (-t)) vs (- -s) := by simpa only [neg_neg] using sd
  have dl : HasDerivAt f (-vs) (-s) := by
    have d : HasDerivAt (fun t : ℝ => -t) (-1) (-s) := hasDerivAt_neg _
    simpa only [Function.comp_def, neg_neg, mul_neg_one] using back.comp (-s) d
  obtain ⟨integrable, pos⟩ := well.finite_bounce_time cf
    (DommaschkSignedTraceDensity.continuousOn_density_region cy reg)
    (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7/8)
      (DommaschkSignedTraceDensity.density_lower t (reg t (Ioo_subset_Icc_self ht))))
    dl (neg_neg_of_pos (positive.trans sp)) rd (positive.trans rp)
  refine ⟨-s, ⟨neg_lt_neg sb.2, neg_lt_neg sb.1⟩, r, rb, ?_, well, integrable, pos⟩
  exact ⟨(neg_lt_neg sb.1).trans_le (abs_le.mp inside).1, (abs_le.mp inside).2.trans_lt rb.1⟩

end PlasmaLean.Design.DommaschkFirstMirrorBounceTime
