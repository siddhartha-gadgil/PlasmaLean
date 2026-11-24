/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCompactLittlejohnArc

/-! # The compact set of all original pilot launch positions on a common embedded torus pair -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCompactLaunchPhases
open Set Fields Contract Forms Theory.KAM WEll1Z2 DommaschkMirrorLaunch DommaschkKamC KamNewton
open DommaschkCompactLittlejohnArc DommaschkCartesianAngleFlow DommaschkCommonLittlejohnTime

/-- Cartesian launch positions use the interpolated radius and vertical coordinate at each
original phase. The interpolation parameter is held fixed as the phase varies. -/
def location (uC zC uA zA : FA) (u t : ℝ) : Space :=
  let b := birth uC zC uA zA u t
  cylPoint (b 0) t (b 1)

/-- The cylindrical-to-Cartesian map preserves continuity of all three component functions. -/
theorem continuous_cylinder {X : Type*} [TopologicalSpace X] {r a z : X → ℝ}
    (cr : Continuous r) (ca : Continuous a) (cz : Continuous z) :
    Continuous (fun t => cylPoint (r t) (a t) (z t)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact cr.mul (Real.continuous_cos.comp ca)
  · exact cr.mul (Real.continuous_sin.comp ca)
  · exact cz

/-- The two embedded tori provide actual continuous coordinate functions of launch phase. -/
theorem continuous_location {uC zC uA zA : FA}
    (c : EmbeddedTorus (RofC uC) (Zof zC)) (a : EmbeddedTorus (RofC uA) (Zof zA)) (u : ℝ) :
    Continuous (location uC zC uA zA u) := by
  have phase : Continuous (fun t : ℝ => ((0 : ℝ),t)) := continuous_const.prodMk continuous_id
  have blendC {f g : ℝ → ℝ} (cf : Continuous f) (cg : Continuous g) :
      Continuous (fun t => blend u (f t) (g t)) :=
    (continuous_const.mul cf).add (continuous_const.mul cg)
  apply continuous_cylinder _ continuous_id _
  · exact blendC (c.contDiff_R.continuous.comp phase) (a.contDiff_R.continuous.comp phase)
  · exact blendC (c.contDiff_z.continuous.comp phase) (a.contDiff_z.continuous.comp phase)

/-- One controlled time, open set, and positive birth-space radius cover every original launch
phase simultaneously whenever its actual reference neighborhoods are regular and compatible. -/
theorem uniform_launches {uC zC uA zA : FA} {u a : ℝ} (ha : 0 ≤ a)
    (ec : EmbeddedTorus (RofC uC) (Zof zC)) (ea : EmbeddedTorus (RofC uA) (Zof zA))
    (every : ∀ t ∈ Icc (-a) a, location uC zC uA zA u t ∈ regular ∧
      UniformAt (location uC zC uA zA u t)) :
    Uniform (location uC zC uA zA u '' Icc (-a) a) := by
  have map := continuous_location ec ea u
  apply of_compact (isCompact_Icc.image map) ((nonempty_Icc.mpr (neg_le_self ha)).image _)
  · rintro _ ⟨t,ht,rfl⟩
    exact (strength_smooth (every t ht).1).continuousAt.continuousWithinAt
  · rintro _ ⟨t,ht,rfl⟩
    exact (every t ht).2

end PlasmaLean.Design.DommaschkCompactLaunchPhases
