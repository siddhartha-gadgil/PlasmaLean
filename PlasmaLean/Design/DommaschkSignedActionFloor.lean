/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkSignedTraceDensity
public import PlasmaLean.Design.DommaschkFirstMirrorLaunchSign
public import PlasmaLean.Theory.Kinetic.CylindricalActionSensitivity

/-! # Physical action accumulated over a signed premirror interval -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedActionFloor

open Certificates.PositionFrameSlabs DommaschkSignedTraceDomain DommaschkJacobian
open Kinetic.CylindricalActionSensitivity DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign
open DommaschkSignedTraceDensity MeasureTheory Set

/-- The integrand uses Cartesian arclength along the physical trajectory. -/
def integrand (h : ℝ) (y : ℝ → Plane) (t : ℝ) : ℝ :=
  ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖ * √(2 * (h - strength t (y t)))

/-- Integrability and a length-dependent lower bound at any height throughout
a finite physical solution segment in the certified cylindrical region. -/
theorem action_floor {a b h low : ℝ} {y : ℝ → Plane} (hab : a ≤ b)
    (ode : ∀ t ∈ Icc a b, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc a b) t)
    (region : ∀ t ∈ Icc a b, Region (y t))
    (below : ∀ t ∈ Icc a b, strength t (y t) ≤ low) :
    IntervalIntegrable (integrand h y) volume a b ∧
      (b-a) * (7/8) * √(2*(h-low)) ≤
        physicalAction (fun t => y t 0) (fun t => y t 1) (fun t => strength t (y t)) a b h := by
  let F := fun t => euclideanFlow 0 1 t (y t)
  let w := fun t => speed (y t 0) (F t 0) (F t 1)
  let g := fun t => w t * √(2 * (h - strength t (y t)))
  have cy : ContinuousOn y (Icc a b) := fun t ht => (ode t ht).continuousWithinAt
  have hr (t : ℝ) (ht : t ∈ Icc a b) : 0 < y t 0 := by linarith [(region t ht).1.1]
  have cw : ContinuousOn w (Icc a b) := continuousOn_speed_region cy region
  have cb : ContinuousOn (fun t => strength t (y t)) (Icc a b) := by
    simpa only [one_mul] using continuousOn_strength cy 1 hr
  have cg : ContinuousOn g (Icc a b) :=
    cw.mul ((continuousOn_const.mul (continuousOn_const.sub cb)).sqrt)
  have ig : IntervalIntegrable g volume a b := cg.intervalIntegrable_of_Icc hab
  have agree : EqOn g (integrand h y) (Ioo a b) := by
    intro t ht
    have dy := (ode t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have d (j : Fin 2) : HasDerivAt (fun s => y s j) (F t j) t :=
      (proj j).hasFDerivAt.comp_hasDerivAt t dy
    have id' : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    simp only [integrand, cartesian_speed (d 0) id' (d 1), mul_one, g, w]
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp ig).congr_fun agree
      measurableSet_Ioo
  · change _ ≤ ∫ t in a..b, integrand h y t
    rw [← intervalIntegral.integral_congr_Ioo_of_le hab agree]
    have bound (t : ℝ) (ht : t ∈ Icc a b) : 7/8 * √(2*(h-low)) ≤ g t := by
      have angular : y t 0 ≤ w t := radius_le_speed t (y t)
      apply mul_le_mul ((region t ht).1.1.trans angular) _ (Real.sqrt_nonneg _) (norm_nonneg _)
      exact Real.sqrt_le_sqrt (by linarith [below t ht])
    have estimate := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) ig bound
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using estimate

/-- Every positive angular width gives a strict rational action floor at the
recorded upper height whenever the field is below the recorded lower height. -/
theorem strict_floor {a b : ℝ} {y : ℝ → Plane} (hab : a < b)
    (ode : ∀ t ∈ Icc a b, HasDerivWithinAt y (euclideanFlow 0 1 t (y t)) (Icc a b) t)
    (region : ∀ t ∈ Icc a b, Region (y t))
    (below : ∀ t ∈ Icc a b, strength t (y t) < height false) :
    IntervalIntegrable (integrand (height true) y) volume a b ∧
      (b - a) * (7 / 250) <
        physicalAction (fun t => y t 0) (fun t => y t 1) (fun t => strength t (y t))
          a b (height true) := by
  obtain ⟨integ, mass⟩ := action_floor (h := (height true : ℝ)) hab.le ode region
    (fun t ht => (below t ht).le)
  have speed_margin : (4 : ℝ) / 125 < √(2 * ((height true : ℝ) - height false)) :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num [height])
  refine ⟨integ, lt_of_lt_of_le ?_ mass⟩
  calc
    (b - a) * (7 / 250) = ((b - a) * (7 / 8)) * (4 / 125) := by ring
    _ < _ := mul_lt_mul_of_pos_left speed_margin (mul_pos (sub_pos.mpr hab) (by norm_num))

end PlasmaLean.Design.DommaschkSignedActionFloor
