/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPhysicalActionPanel
public import PlasmaLean.Design.DommaschkSignedObservable

/-! # The arclength derivative on a signed physical trajectory -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalActionPanel
open Certificates.PositionFrameSlabs DommaschkBounceField DommaschkKam
open DommaschkJacobian DommaschkSignedObservable Contract

/-- The geometrical density bounded by the action cells is the norm of the
Cartesian derivative on the physical angle-parametrized trajectory. -/
theorem arcDensity_of_ode {y : ℝ → Plane} {t : ℝ}
    (ode : HasDerivAt y (euclideanFlow 0 1 t (y t)) t) (hr : 0 < y t 0)
    (hd : 0 < atPoint dD (y t 0) t (y t 1)) :
    ‖deriv (fun s => cylPoint (y s 0) s (y s 1)) t‖ = arcDensity (y t 0) t (y t 1) := by
  apply norm_deriv_eq_density (R := fun s => y s 0) (z := fun s => y s 1) hr hd
  · have d := (DommaschkJacobian.proj 0).hasFDerivAt.comp_hasDerivAt t ode
    change HasDerivAt (fun s => y s 0) ((physicalFlow 0 1 t (y t).ofLp) 0) t at d
    simpa only [physicalFlow, zero_add, one_mul, Matrix.cons_val_zero] using d
  · have d := (DommaschkJacobian.proj 1).hasFDerivAt.comp_hasDerivAt t ode
    change HasDerivAt (fun s => y s 1) ((physicalFlow 0 1 t (y t).ofLp) 1) t at d
    simpa only [physicalFlow, zero_add, one_mul, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using d

/-- Every interior point of a certified signed trajectory satisfies the
arclength formula as soon as the cylindrical radius and toroidal field are positive. -/
theorem arcDensity_on_path {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State}
    {fr br : List Step} {x : Plane} {y : ℝ → Plane} (path : DommaschkSignedObservable.Path
      n fs bs fr br x y) {t : ℝ} (ht : t ∈ Set.Ioo (-(n : ℝ) / 64) (n / 64))
    (hr : 0 < y t 0) (hd : 0 < atPoint dD (y t 0) t (y t 1)) :
    ‖deriv (fun s => cylPoint (y s 0) s (y s 1)) t‖ = arcDensity (y t 0) t (y t 1) :=
  arcDensity_of_ode ((path.ode t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)) hr hd

end PlasmaLean.Design.DommaschkPhysicalActionPanel
