/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedObservable
public import PlasmaLean.Design.DommaschkMirrorStrengthSlope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Unique transverse mirror encounters on a single signed QA2R field line -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedMirrorSlope
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkMirrorTubeCrossing
open DommaschkJacobian (euclideanFlow)
open Set

/-- At any occurrence of the level inside this bracket the time is unique in
the closed bracket and the outward derivative has the specified lower bound. -/
def Regular (a b h k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ t ∈ Ioo a b, f t = h → (∀ u ∈ Icc a b, f u = h → u = t) ∧
    ∃ v > k / (2 * h), HasDerivAt f v t

def RegularBoth (a b h k : ℝ) (y : ℝ → Plane) : Prop :=
  Regular a b h k (fun t => strength t (y t)) ∧
    Regular a b h k (fun t => strength (-t) (y (-t)))

def FirstTransverse (a b h k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ t ∈ Ioo a b, f t = h ∧ (∀ u ∈ Ico 0 t, f u < h) ∧
    (∀ u ∈ Icc a b, f u = h → u = t) ∧ ∃ v > k / (2 * h), HasDerivAt f v t

/-- First encounters on both sides of the same field line. Time and derivative
on the negative side are expressed in increasing elapsed angle. -/
def FirstTransverseBoth (a b h k : ℝ) (y : ℝ → Plane) : Prop :=
  FirstTransverse a b h k (fun t => strength t (y t)) ∧
    FirstTransverse a b h k (fun t => strength (-t) (y (-t)))

theorem first_transverse {a b h k : ℝ} {y : ℝ → Plane}
    (first : FirstBoth a b h y) (reg : RegularBoth a b h k y) :
    FirstTransverseBoth a b h k y := by
  obtain ⟨⟨f, hf, eqf, belowf⟩, b', hb, eqb, belowb⟩ := first
  exact ⟨⟨f, hf, eqf, belowf, reg.1 f hf eqf⟩, ⟨b', hb, eqb, belowb, reg.2 b' hb eqb⟩⟩

/-- Positivity throughout the open interval and continuity across its endpoints
make every interior encounter unique on the closed interval. -/
theorem regular_of_square {a b h k : ℝ} {f : ℝ → ℝ} (cont : ContinuousOn f (Icc a b))
    (nonneg : ∀ t, 0 ≤ f t) (hp : 0 < h) (kp : 0 < k)
    (slope : ∀ t ∈ Ioo a b, ∃ v > k, HasDerivAt (fun u => (f u) ^ 2) v t) :
    Regular a b h k f := by
  have inc : StrictMonoOn (fun t => (f t) ^ 2) (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ((continuous_pow 2).comp_continuousOn cont)
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨v, hv, derivative⟩ := slope t ht
    change 0 < deriv (fun u => (f u) ^ 2) t
    rw [derivative.deriv]
    exact kp.trans hv
  intro t ht hit
  refine ⟨fun u hu same => inc.injOn hu (Ioo_subset_Icc_self ht) ?_,
    DommaschkMirrorStrengthSlope.at_positive_level nonneg hp hit (slope t ht)⟩
  exact congrArg (· ^ 2) (same.trans hit.symm)

private theorem reverse_rate (t : ℝ) (x : Plane) :
    -euclideanFlow 0 1 (-t) x = euclideanFlow 0 (-1) t x := by
  ext j
  fin_cases j <;> simp [euclideanFlow, DommaschkBounceField.physicalFlow]

/-- Restrict the signed ODE to a positive elapsed-angle subinterval, and
differentiate the same line after replacing its clock by its negative. -/
theorem clock_odes {n : ℕ} {fs bs : State} {fr br : List Step} {x : Plane} {y : ℝ → Plane}
    (path : Path n fs bs fr br x y) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ (n : ℝ) / 64) :
    (∀ t ∈ Icc a b, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc a b) t) ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => y (-u))
      (euclideanFlow 0 (-1) t (y (-t))) (Icc a b) t := by
  have nonneg : (0 : ℝ) ≤ (n : ℝ) / 64 := by positivity
  have subset : Icc a b ⊆ Icc (-(n : ℝ) / 64) (n / 64) := by
    intro u hu
    exact ⟨by linarith [hu.1], hu.2.trans hb⟩
  have negmap : MapsTo (fun u : ℝ => -u) (Icc a b) (Icc (-(n : ℝ) / 64) (n / 64)) := by
    intro u hu
    exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  refine ⟨fun t ht => (path.ode t (subset ht)).mono subset, ?_⟩
  intro t ht
  have d := (path.ode (-t) (negmap ht)).scomp t (hasDerivWithinAt_neg t (Icc a b)) negmap
  simpa only [Function.comp_def, neg_one_smul, reverse_rate] using d

end PlasmaLean.Design.DommaschkSignedMirrorSlope
