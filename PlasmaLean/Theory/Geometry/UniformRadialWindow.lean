/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic

/-! # Uniform intervals around attained values in compact radial families -/

@[expose] public section
noncomputable section
namespace PlasmaLean.UniformRadialWindow

open Set MeasureTheory

/-- Real radii in the given closed interval whose observable is within the tolerance. -/
def window {a b : ℝ} (f : Icc a b → ℝ) (j ε : ℝ) : Set ℝ :=
  {r | ∃ h : r ∈ Icc a b, |f ⟨r,h⟩ - j| < ε}

/-- A set of real radii contains a full closed interval of the prescribed length. -/
def HasInterval (s : Set ℝ) (length : ℝ) : Prop :=
  ∃ c : ℝ, Icc c (c+length) ⊆ s

theorem HasInterval.volume {s : Set ℝ} {length : ℝ} (h : HasInterval s length) :
    ENNReal.ofReal length ≤ volume s := by
  obtain ⟨c,sub⟩ := h
  have estimate := measure_mono (μ := MeasureTheory.volume) sub
  simpa only [Real.volume_Icc,add_sub_cancel_left] using estimate

private theorem interval_of_modulus {a b j ε length : ℝ} {f : Icc a b → ℝ}
    (x : Icc a b) (len : 0 ≤ length) (width : length ≤ b - a)
    (modulus : ∀ r : Icc a b, |(r:ℝ)-x| ≤ length → |f r-j| < ε) :
    HasInterval (window f j ε) length := by
  let c := min (x:ℝ) (b-length)
  have ac : a ≤ c := le_min x.2.1 (by linarith)
  have cb : c+length ≤ b := by
    have : c ≤ b-length := min_le_right _ _
    linarith
  have xc : c ≤ (x:ℝ) := min_le_left _ _
  have cx : (x:ℝ) ≤ c+length := by
    have : (x:ℝ)-length ≤ c := le_min (by linarith) (sub_le_sub_right x.2.2 _)
    linarith
  refine ⟨c,?_⟩
  intro r hr
  have mem : r ∈ Icc a b := ⟨ac.trans hr.1,hr.2.trans cb⟩
  refine ⟨mem,modulus ⟨r,mem⟩ ?_⟩
  change |r-(x:ℝ)| ≤ length
  exact abs_le.mpr ⟨by linarith [hr.1],by linarith [hr.2]⟩

/-- One positive interval length works for all parameters and all attained fiber values. -/
theorem uniform {P : Type*} [PseudoMetricSpace P] [CompactSpace P] {a b : ℝ} (ab : a < b)
    {F : P × Icc a b → ℝ} (continuous : Continuous F) {ε : ℝ} (positive : 0 < ε) :
    ∃ length > 0, ∀ (p : P) (j : ℝ), j ∈ range (fun r => F (p,r)) →
      HasInterval (window (fun r => F (p,r)) j ε) length := by
  obtain ⟨δ,hδ,control⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous) ε positive
  let length := min (b-a) (δ/2)
  have pos : 0 < length := lt_min (sub_pos.mpr ab) (half_pos hδ)
  refine ⟨length,pos,?_⟩
  intro p j hit
  obtain ⟨x,rfl⟩ := hit
  apply interval_of_modulus x pos.le (min_le_left _ _)
  intro r hr
  have close : dist r x < δ := by
    change |(r:ℝ)-(x:ℝ)| < δ
    exact hr.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ))
  have prod : dist (p,r) (p,x) < δ := by simpa [Prod.dist_eq] using close
  exact control prod

/-- An explicit radius width for a nonnegative radial Lipschitz constant.
At constant fibers the entire radial interval qualifies. -/
theorem lipschitz {a b j ε L : ℝ} (ab : a < b) (eps : 0 < ε) (nonneg : 0 ≤ L)
    {f : Icc a b → ℝ} (bound : ∀ r x : Icc a b, |f r-f x| ≤ L * |(r:ℝ)-x|)
    (hit : j ∈ range f) :
    let length := if L = 0 then b-a else min (b-a) (ε/(2*L))
    0 < length ∧ HasInterval (window f j ε) length := by
  obtain ⟨x,rfl⟩ := hit
  split_ifs with zero
  · refine ⟨sub_pos.mpr ab,interval_of_modulus x (sub_nonneg.mpr ab.le) le_rfl ?_⟩
    intro r _
    simpa only [zero,zero_mul] using (bound r x).trans_lt (by simpa [zero] using eps)
  · have hl := lt_of_le_of_ne nonneg (Ne.symm zero)
    have pos : 0 < min (b-a) (ε/(2*L)) := lt_min (sub_pos.mpr ab) (div_pos eps (by positivity))
    refine ⟨pos,interval_of_modulus x pos.le (min_le_left _ _) ?_⟩
    intro r hr
    have h := (le_div_iff₀ (show 0 < 2*L by positivity)).mp (hr.trans (min_le_right _ _))
    have v := bound r x
    nlinarith

end PlasmaLean.UniformRadialWindow
