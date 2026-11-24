/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.MirrorWellComponent
public import PlasmaLean.Design.DommaschkSignedMirrorSlope
public import PlasmaLean.Design.DommaschkSignedTraceDensity

/-! # Components and arclength mirror births of the signed pilot trace -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstMirrorWell
open Set Certificates.PositionFrameSlabs Kinetic.MirrorActionEnvelope
open DommaschkSignedMirrorSlope DommaschkSignedObservable DommaschkMirrorTubeCrossing
open DommaschkSignedTraceDomain DommaschkPhysicalActionPanel DommaschkBounceField DommaschkKam
open DommaschkJacobian Contract
set_option maxRecDepth 8000

/-- The physical Cartesian point on the signed geometric-angle clock. -/
def point (y : ℝ → Plane) (t : ℝ) : Fields.Space := cylPoint (y t 0) t (y t 1)

/-- Exact turning brackets, connected components and the physical arclength
mirror-birth predicate at every point between the two first contacts. -/
def Identified (a b h : ℝ) (y : ℝ → Plane) : Prop :=
  ∃ l ∈ Ioo (-b) (-a), ∃ r ∈ Ioo a b,
    LaunchWell (fun t => strength t (y t)) 0 h l r ∧
    connectedComponentIn {t | strength t (y t) < h} 0 = Ioo l r ∧
    connectedComponentIn {t | strength t (y t) ≤ h} 0 = Icc l r ∧
    ∀ t ∈ Icc l r, RegularMirrorBirth (DommaschkQA2R.field DommaschkQA2R.candidate)
      (point y t) h

/-- The entire central angular interval lies between the two first contacts. -/
theorem Identified.at_launch {a b h φ : ℝ} {y : ℝ → Plane} (well : Identified a b h y)
    (central : |φ| ≤ a) :
    RegularMirrorBirth (DommaschkQA2R.field DommaschkQA2R.candidate) (point y φ) h := by
  obtain ⟨l, hl, r, hr, _, _, _, regular⟩ := well
  obtain ⟨lo, hi⟩ := abs_le.mp central
  exact regular φ ⟨hl.2.le.trans lo, hi.trans hr.1.le⟩

private theorem oriented {y : ℝ → Plane} {t : ℝ}
    (ode : HasDerivAt y (euclideanFlow 0 1 t (y t)) t) (reg : Region (y t)) :
    let B := DommaschkQA2R.field DommaschkQA2R.candidate
    let speed := arcDensity (y t 0) t (y t 1)
    0 < speed ∧ B (point y t) ≠ 0 ∧ HasDerivAt (point y)
      (speed • Kinetic.GCLittlejohn.bhat B (point y t)) t := by
  have hr : 0 < y t 0 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7/8) reg.1.1
  have hd := DommaschkSignedTraceDenominator.regular t reg.1 reg.2
  have hp := toroidal_pos_of_den hr (lt_trans (by norm_num : (0 : ℝ) < 1/64) hd)
  have geom := Kinetic.MirrorWell.cylindrical_trace_speed
    (DommaschkQA2R.field DommaschkQA2R.candidate) (fun s => y s 0) (fun s => y s 1) 0 t hr
  simp only [zero_add] at geom
  have az : -Real.sin t * (DommaschkQA2R.field DommaschkQA2R.candidate (point y t)) 0 +
      Real.cos t * (DommaschkQA2R.field DommaschkQA2R.candidate (point y t)) 1 =
      cylBphi (y t 0) t (y t 1) := by simp [cylBphi, point]
  unfold point at az
  rw [az] at geom
  have dr := (proj 0).hasFDerivAt.comp_hasDerivAt t ode
  have dz := (proj 1).hasFDerivAt.comp_hasDerivAt t ode
  apply geom hp
  · change HasDerivAt (fun s => y s 0) ((physicalFlow 0 1 t (y t).ofLp) 0) t at dr
    simpa [physicalFlow, cylBR] using dr
  · change HasDerivAt (fun s => y s 1) ((physicalFlow 0 1 t (y t).ofLp) 1) t at dz
    simpa [physicalFlow, cylBz] using dz

/-- First transverse encounters and the certified physical region imply all parts
of the launch well on the same physical trajectory. -/
theorem identify {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {x : Plane} {y : ℝ → Plane} (path : Path n fs bs fr br x y) {a b h k : ℝ}
    (ha : 0 ≤ a) (stop : b ≤ n / 64) (height : 0 < h) (rate : 0 < k)
    (region : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64), Region (y t))
    (hits : FirstTransverseBoth a b h k y) : Identified a b h y := by
  obtain ⟨⟨r, rb, rh, pr, _, vr, rp, rd⟩, ⟨s, sb, sh, ps, _, vs, sp, sd⟩⟩ := hits
  let f := fun t => strength t (y t)
  have w : LaunchWell f 0 h (-s) r := by
    refine ⟨by linarith [sb.1], by linarith [rb.1], sh, rh, ?_⟩
    intro t ht
    rcases le_total 0 t with right | left
    · exact pr t ⟨right, ht.2⟩
    · simpa only [neg_neg] using ps (-t) ⟨neg_nonneg.mpr left, by linarith [ht.1]⟩
  have positive : 0 < k / (2*h) := div_pos rate (by positivity)
  have right : 0 < vr := positive.trans rp
  have left : 0 < vs := positive.trans sp
  have back : HasDerivAt (fun t => f (-t)) vs (- -s) := by simpa only [neg_neg] using sd
  refine ⟨-s, ⟨neg_lt_neg sb.2, neg_lt_neg sb.1⟩, r, rb, w, w.strict_component,
    w.transverse_component back left rd right, ?_⟩
  intro t ht
  have interior {q : ℝ} (hq : q ∈ Icc (-s) r) : q ∈ Ioo (-(n : ℝ)/64) (n/64) :=
    ⟨by linarith [hq.1, sb.2], by linarith [hq.2, rb.2]⟩
  have ode {q : ℝ} (hq : q ∈ Icc (-s) r) := (path.ode q (Ioo_subset_Icc_self
    (interior hq))).hasDerivAt (Icc_mem_nhds (interior hq).1 (interior hq).2)
  have cy : ContinuousOn y (Icc (-s) r) := fun q hq => (ode hq).continuousAt.continuousWithinAt
  have reg (q : ℝ) (hq : q ∈ Icc (-s) r) := region q (Ioo_subset_Icc_self (interior hq))
  have dl : HasDerivAt f (-vs) (-s) := by
    have d : HasDerivAt (fun u : ℝ => -u) (-1) (-s) := (hasDerivAt_id (-s)).neg
    simpa only [Function.comp_def, neg_neg, mul_neg_one] using back.comp (-s) d
  exact w.regular_at (B := DommaschkQA2R.field DommaschkQA2R.candidate) (X := point y) ht
    (DommaschkSignedTraceDensity.continuousOn_density_region cy reg)
    (fun q hq => oriented (ode hq) (reg q hq))
    (by change deriv f (-s) < 0; rw [dl.deriv]; exact neg_neg_of_pos left)
    (by change 0 < deriv f r; rw [rd.deriv]; exact right)

/-- Preserve the section reached by each birth while applying a consequence
to its existing path and observables. -/
theorem map_birth {P Q : Plane → Prop} (old : BirthWith P) (lift : ∀ x, P x → Q x) :
    BirthWith Q := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,each⟩ := old
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,ic,ia,nested,fun φ hφ => ?_⟩
  obtain ⟨s,v,hs,hφ,hv,ode,p⟩ := each φ hφ
  exact ⟨s,v,hs,hφ,hv,ode,lift _ p⟩

end PlasmaLean.Design.DommaschkFirstMirrorWell
