/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalFirstMirrorValues
public import PlasmaLean.Theory.Kinetic.FirstMirrorHeightDistribution

/-! # Sampling heights with two sufficiently steep first mirrors on one actual QA2R line -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkFirstMirrorHeightSampling
open Set MeasureTheory Kinetic.FirstMirror DommaschkFirstMirrorLaunchSign
open DommaschkPhysicalFirstMirrorValues Certificates.PositionFrameSlabs

abbrev baseline : Measure ℝ := uniformHeight (height false) (height true)

/-- Certified probability lower bound for uniform height on the archived band. -/
abbrev fraction : ℝ := 667367655761 / 1292367655761

theorem baseline_isProbability : IsProbabilityMeasure baseline :=
  uniformHeight_isProbability (by norm_num [height])

/-- For these two given first-contact maps, the observation uses the actual physical slopes. -/
def successful {phase a b c d : ℝ} {y : ℝ → Plane}
    (p : Family (profile phase y false) a b (height false) (height true))
    (q : Family (profile phase y true) c d (height false) (height true)) : Set ℝ :=
  {H | ∃ h : Icc (height false : ℝ) (height true), (h : ℝ) = H ∧
    1 / 1250 < deriv (profile phase y false) (p.time h) ∧
    1 / 1250 < deriv (profile phase y true) (q.time h)}

/-- The sampling law is chosen after the line and its two first-contact maps are fixed. The
second clause applies to any normalized sampling density bounded only on unsuccessful heights. -/
def Sampled (phase : ℝ) (y : ℝ → Plane) (a b c d : ℝ) (rate : ℝ := fraction) : Prop :=
  ∃ p : Family (profile phase y false) a b (height false) (height true),
    ∃ q : Family (profile phase y true) c d (height false) (height true),
      MeasurableSet (successful p q) ∧ ENNReal.ofReal rate ≤ baseline (successful p q) ∧
      ∀ (alt : Measure ℝ) [IsProbabilityMeasure alt] (ρ : ℝ → ENNReal) (C : ENNReal),
        alt = baseline.withDensity ρ → (∀ᵐ h ∂(baseline.restrict (successful p q)ᶜ), ρ h ≤ C) →
        1 - C * (1 - ENNReal.ofReal rate) ≤ alt (successful p q)

/-- A measurable height-selection rule on a sample space inherits the probability bound
from its pushforward. The first-contact maps in both conclusions are the same. -/
theorem on_height_map {phase a b c d rate : ℝ} {y : ℝ → Plane}
    (data : Sampled phase y a b c d rate) {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {H : X → ℝ} (mh : Measurable H) :
    ∃ p : Family (profile phase y false) a b (height false) (height true),
      ∃ q : Family (profile phase y true) c d (height false) (height true),
        MeasurableSet (H ⁻¹' successful p q) ∧
        (ν.map H = baseline → ENNReal.ofReal rate ≤ ν (H ⁻¹' successful p q)) ∧
        ∀ (alt : Measure ℝ) [IsProbabilityMeasure alt] (ρ : ℝ → ENNReal) (C : ENNReal),
          ν.map H = alt → alt = baseline.withDensity ρ →
          (∀ᵐ h ∂(baseline.restrict (successful p q)ᶜ), ρ h ≤ C) →
          1 - C * (1 - ENNReal.ofReal rate) ≤ ν (H ⁻¹' successful p q) := by
  obtain ⟨p,q,mg,base,change⟩ := data
  refine ⟨p,q,mh mg,fun law => probability_of_height_map ν mh mg law base,?_⟩
  intro alt prob ρ C law density upper
  exact probability_of_height_map ν mh mg law (change alt ρ C density upper)

private theorem sampled_of_area {phase a b c d lo rate : ℝ} {y : ℝ → Plane}
    {p : Family (profile phase y false) a b (height false) (height true)}
    {q : Family (profile phase y true) c d (height false) (height true)}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (area : ENNReal.ofReal lo ≤ volume (successful p q))
    (value : lo / ((height true : ℝ) - height false) = rate) : Sampled phase y a b c d rate := by
  have within : successful p q ⊆ Icc (height false : ℝ) (height true) := by
    rintro _ ⟨h,rfl,_⟩
    exact h.2
  have normalized := uniformHeight_lower (by norm_num [height]) within area
  rw [value] at normalized
  have measurable := measurable_good_heights p q ha hc (1 / 1250)
  refine ⟨p,q,measurable,normalized,?_⟩
  intro alt prob ρ C law density
  let _ := baseline_isProbability
  exact probability_of_bad_density measurable normalized law density

theorem of_physical {phase a b c d : ℝ} {y : ℝ → Plane} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hit : Good phase y a b c d) : Sampled phase y a b c d := by
  obtain ⟨p,q,_,area⟩ := hit
  exact sampled_of_area (p := p) (q := q) ha hc area (by norm_num [height,fraction])

/-- Doubling the baseline density on the failed set still leaves a strictly positive bound. -/
theorem doubled_density_floor :
    1 - (2 : ENNReal) * (1 - ENNReal.ofReal fraction) =
      ENNReal.ofReal (42367655761 / 1292367655761) := by
  have fpos : 0 ≤ fraction := by norm_num [fraction]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ fpos]
  rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_sub _ (by norm_num [fraction])]
  congr 1
  norm_num [fraction]

open DommaschkMirrorLaunch DommaschkEndpointTraceFamily

/-- The original torus-interpolated seed, full signed physical ODE, and the actual
height sampling theorem are witnessed by the same single trajectory. -/
def Birth (e : MirrorEndpoint) (c : Checkpoint) (k j l i : ℕ)
    (uC zC uA zA : Theory.KAM.FA) (φ : ℝ) (rate : ℝ := fraction) : Prop :=
  let α := azimuth e.opposite
  let T : ℝ := c.length / 64
  ∃ y : ℝ → Plane, y (φ - α) = coordinates.symm (birth uC zC uA zA e.radius φ) ∧
    (∀ t ∈ Icc (-T) T, HasDerivWithinAt y (DommaschkJacobian.euclideanFlow α 1 t (y t))
      (Icc (-T) T) t) ∧
    Sampled α y (k / 64) (((j : ℝ) + 1) / 64) (l / 64) (((i : ℝ) + 1) / 64) rate

theorem of_launch {e : MirrorEndpoint} {c : Checkpoint} {k j l i : ℕ}
    {uC zC uA zA : Theory.KAM.FA} {φ : ℝ} (actual : FromLaunch e c k j l i uC zC uA zA φ) :
    Birth e c k j l i uC zC uA zA φ := by
  obtain ⟨_,_,y,_,_,_,_,_,born,_,_,ode,_,_,area⟩ := actual
  exact ⟨y,born,ode,of_physical (by positivity) (by positivity) area⟩

/-- The actual two bracket widths determine the probability loss independently. -/
def bracketRate (a b c d : ℝ) : ℝ :=
  let Δ : ℝ := height true - height false
  (Δ - (1 / 1250) * ((b - a) + (d - c))) / Δ

set_option maxRecDepth 12000 in
/-- An archived, capped first-mirror passage retains its specific width improvement. -/
theorem of_launch_width {e : MirrorEndpoint} {c : Checkpoint} {k j l i : ℕ}
    {uC zC uA zA : Theory.KAM.FA} {φ : ℝ} (hit : FromLaunch e c k j l i uC zC uA zA φ)
    (fr : Side (azimuth e.opposite) e.start false k j c.forwardRows)
    (br : Side (azimuth e.opposite) e.start true l i c.backwardRows)
    (fl : c.forwardRows.length = c.length) (bl : c.backwardRows.length = c.length) :
    Birth e c k j l i uC zC uA zA φ
      (bracketRate (k/64) (((j:ℝ)+1)/64) (l/64) (((i:ℝ)+1)/64)) := by
  obtain ⟨_,_,y,_,_,_,_,_,born,_,_,ode,f,b,p,q,_,_⟩ := hit
  obtain ⟨fb,_,_⟩ := fr.inputs (y := y) f
  obtain ⟨bb,_,_⟩ := br.inputs (y := y) b
  have width {k j : ℕ} (h : k ≤ j) : (k:ℝ)/64 ≤ ((j:ℝ)+1)/64 := by
    have ij : (k : ℝ) ≤ j := by exact_mod_cast h
    linarith
  have der (back : Bool) {s t : ℝ} (hs : 0 ≤ s) (st : s ≤ t) (full : t ≤ c.length/64)
      (box : ∀ v ∈ Icc 0 t, DommaschkSignedTraceDomain.Region (y (clock back v))) :
      ∀ v ∈ Ioo s t, DifferentiableAt ℝ (profile (azimuth e.opposite) y back) v := by
    have dv := vector_differentiableOn back ode hs st full
      (fun v hv => (by norm_num : (0:ℝ) < 7/8).trans_le (box v ⟨hs.trans hv.1,hv.2⟩).1.1)
    intro v hv
    have positive := DommaschkToroidalFieldBounds.strength_lower
      (azimuth e.opposite + clock back v) (box v ⟨hs.trans hv.1.le,hv.2.le⟩)
    have nz : vector (azimuth e.opposite) y back v ≠ 0 :=
      norm_pos_iff.mp ((by norm_num : (0:ℝ) < 7/8).trans positive)
    exact ((dv v (Ioo_subset_Icc_self hv)).differentiableAt (Icc_mem_nhds hv.1 hv.2)).norm ℝ nz
  have fj : (j:ℝ)+1 ≤ c.length := by exact_mod_cast (fl ▸ fr.reaches : j < c.length)
  have bj : (i:ℝ)+1 ≤ c.length := by exact_mod_cast (bl ▸ br.reaches : i < c.length)
  have df := der false (by positivity) (width fr.before) (by linarith) fb
  have dg := der true (by positivity) (width br.before) (by linarith) bb
  have area := two_sided_good_heights p q (by positivity) (by positivity) (1/1250) df dg
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr (width fr.before)) (sub_nonneg.mpr (width br.before)),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_sub _ (mul_nonneg (by norm_num)
      (add_nonneg (sub_nonneg.mpr (width fr.before)) (sub_nonneg.mpr (width br.before))))] at area
  exact ⟨y,born,ode,sampled_of_area (p := p) (q := q) (by positivity) (by positivity) area rfl⟩

end PlasmaLean.Design.DommaschkFirstMirrorHeightSampling
