/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkPeriodicBirthCollar
public import PlasmaLean.Design.DommaschkCartesianAngleFlow
public import PlasmaLean.Design.DommaschkCompactLaunchPhases

/-! # Cartesian field lines on the full-period launch collar -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPeriodicBirthCollar
open Set Filter Fields Contract DommaschkJacobian DommaschkBounceField
open DommaschkCartesianAngleFlow (B velocity regular)
set_option maxRecDepth 8192

def position (y : ℝ → PhysicalPlane) (φ t : ℝ) : Space :=
  cylPoint (y t 0) (φ+t) (y t 1)

private theorem allowed {p : PhysicalPlane} {φ : ℝ} (h : Bounds (p 0) (p 1) φ) :
    cylPoint (p 0) φ (p 1) ∈ regular := by
  have hr : 0 < p 0 := by linarith only [h.1]
  constructor
  · change 0 < CylAlgebra.r2 _
    rw [DommaschkCartesianAngleFlow.radial_at]
    positivity
  · rw [DommaschkCartesianAngleFlow.angular_at]
    exact mul_pos hr (toroidal_pos_of_den hr h.2.1)

private theorem tangent {y : ℝ → PhysicalPlane} {φ t : ℝ}
    (hd : HasDerivAt y (euclideanFlow φ 1 t (y t)) t)
    (h : Bounds (y t 0) (y t 1) (φ+t)) :
    HasDerivAt (position y φ) (velocity (position y φ t)) t := by
  have hR : 0 < y t 0 := by linarith only [h.1]
  have hφ := toroidal_pos_of_den hR h.2.1
  have geo := Kinetic.MirrorWell.cylindrical_trace_speed B (fun s => y s 0) (fun s => y s 1) φ t hR
  dsimp only at geo
  have az : -Real.sin (φ+t)*B (position y φ t) 0 + Real.cos (φ+t)*B (position y φ t) 1 =
      DommaschkKam.cylBphi (y t 0) (φ+t) (y t 1) := by simp [position,DommaschkKam.cylBphi]
  unfold position at az
  rw [az] at geo
  have dr := (proj 0).hasFDerivAt.comp_hasDerivAt t hd
  have dz := (proj 1).hasFDerivAt.comp_hasDerivAt t hd
  change HasDerivAt (fun s => y s 0) ((physicalFlow φ 1 t (y t).ofLp) 0) t at dr
  change HasDerivAt (fun s => y s 1) ((physicalFlow φ 1 t (y t).ofLp) 1) t at dz
  have geom := geo hφ (by simpa [physicalFlow, DommaschkKam.cylBR] using dr)
    (by simpa [physicalFlow, DommaschkKam.cylBz] using dz)
  have reg : position y φ t ∈ regular := allowed h
  have hs : DommaschkCartesianAngleFlow.speed (position y φ t) =
      y t 0 * ‖B (position y φ t)‖ / DommaschkKam.cylBphi (y t 0) (φ+t) (y t 1) := by
    rw [DommaschkCartesianAngleFlow.speed,DommaschkCartesianAngleFlow.factor,position,
      DommaschkCartesianAngleFlow.radial_at,DommaschkCartesianAngleFlow.angular_at]
    field_simp [hR.ne',hφ.ne']
  rw [DommaschkCartesianAngleFlow.aligned reg,hs]
  exact geom.2.2

/-- Physical autonomous field line from the specified Cartesian launch, with the
strength and regularity estimates holding also at both endpoints. -/
def CartesianPassage (x₀ : State) (φ : ℝ) : Prop :=
    ∃ X : ℝ → Space, X 0 = cylPoint (x₀ 0) φ (x₀ 1) ∧
      ContinuousOn X (Icc (-duration) duration) ∧
      (∀ t ∈ Icc (-duration) duration, X t ∈ regular ∧ ‖B (X t)‖ < cap) ∧
      ∀ t ∈ Ioo (-duration) duration, HasDerivAt X (velocity (X t)) t

theorem Passage.cartesian {x₀ : State} {φ : ℝ} (pass : Passage x₀ φ) :
    CartesianPassage x₀ φ := by
  obtain ⟨y, hy, h⟩ := pass
  have hy' : (y 0).ofLp = x₀ := hy
  refine ⟨position y φ,by simp [position,hy'],?_,?_,?_⟩
  · have hc : ContinuousOn y (Icc (-duration) duration) :=
      fun t ht => (h t ht).1.continuousWithinAt
    have chart : Continuous (fun p : PhysicalPlane × ℝ => cylPoint (p.1 0) (φ+p.2) (p.1 1)) :=
      DommaschkCompactLaunchPhases.continuous_cylinder ((proj 0).continuous.comp continuous_fst)
        (continuous_const.add continuous_snd) ((proj 1).continuous.comp continuous_fst)
    exact chart.comp_continuousOn (hc.prodMk continuousOn_id)
  · intro t ht
    exact ⟨allowed (h t ht).2.1,(h t ht).2.1.2.2.2.2⟩
  · intro t ht
    have here := h t ⟨ht.1.le,ht.2.le⟩
    exact tangent (here.1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)) here.2.1

end PlasmaLean.Design.DommaschkPeriodicBirthCollar
