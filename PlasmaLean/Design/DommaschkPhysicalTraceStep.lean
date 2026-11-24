/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameBall
public import PlasmaLean.Design.DommaschkFramedTaylorResidual
public import PlasmaLean.Design.DommaschkPhysicalJacobian

/-! # Realizing sparse QA2R field certificates on a saved position step

Coefficient identities attach arbitrary reference and trial Taylor packets to
the stored position polynomials. The converted frame is the same affine frame
in the scalar proof and the physical inverse-defect calculation.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalTraceStep

open Certificates PositionFrameSlabs QPoly TrajectoryTaylorModel DommaschkKam
open DommaschkBounceField DommaschkBounceTaylor DommaschkJacobian Set
open scoped RealInnerProductSpace

/-- Exact agreement of both model centers, with the radial origin restored. -/
structure CenterMatches (r : Step) (m : Inputs) : Prop where
  radial : polynomial r 0 = add [29/32] m.u.poly
  vertical : polynomial r 1 = m.z.poly

theorem CenterMatches.position {r : Step} {m : Inputs} (h : CenterMatches r m) (a t : ℝ) :
    PositionFrameSlabs.coordinates (reference a r t) =
      FramedTaylorResidual.position m (coord a t) := by
  funext i
  fin_cases i <;>
    simp [reference, FramedTaylorResidual.position, PositionFrameSlabs.coordinates, h.radial,
      h.vertical, dkR0, eval_add]

theorem CenterMatches.velocity {r : Step} {m : Inputs} (h : CenterMatches r m) (a t : ℝ) :
    PositionFrameSlabs.coordinates (referenceVelocity a r t) =
      FramedTaylorResidual.velocity m 128 (coord a t) := by
  have clock (t : ℝ) : coord a t = 128*t-(128*a+1) := by unfold coord; ring
  have eq : (fun t => PositionFrameSlabs.coordinates (reference a r t)) =
      fun t => FramedTaylorResidual.position m (128*t-(128*a+1)) := by
    funext x
    rw [h.position a x, clock]
  have der := PositionFrameSlabs.coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_reference a r t)
  change HasDerivAt (fun t => PositionFrameSlabs.coordinates (reference a r t))
    (PositionFrameSlabs.coordinates (referenceVelocity a r t)) t at der
  rw [eq] at der
  rw [clock]
  exact der.unique (FramedTaylorResidual.position_derivative m 128 (128*a+1) t)

/-- Four rational endpoint entries in the normalized physical matrix. -/
def frameData (m : PositionFrameSlabs.Frame) : Fin 2 → Fin 2 → ℚ :=
  !![m.a / (2:ℚ)^40, m.b / (2:ℚ)^40; m.c / (2:ℚ)^40, m.d / (2:ℚ)^40]

/-- The matrix Taylor model passed to the sparse residual checker. -/
def residualFrame (s : PositionFrameSlabs.State) (r : Step) : FramedTaylorResidual.Frame :=
  FramedTaylorResidual.Frame.ofEndpoints (frameData s.frame) (frameData r.frame)

private theorem eval_entry (a b : ℤ) (u : ℝ) :
    eval (FramedTaylorResidual.affine (a/(2:ℚ)^40) (b/(2:ℚ)^40)).poly u = entry a b u := by
  rw [FramedTaylorResidual.eval_affine]
  unfold entry
  push_cast
  ring

/-- The coordinate adjugate in the sparse proof is precisely the inverse
continuous linear equivalence in the moving-frame ODE proof. -/
theorem pulled_eq {lim : Limits} {s : PositionFrameSlabs.State} {r : Step}
    (hg : geometry lim s r = true) {u : ℝ} (hu : |u| ≤ 1) (v : DommaschkBounceField.State) :
    (frameEquiv s.frame r.frame u).symm (PositionFrameSlabs.coordinates.symm v) =
      PositionFrameSlabs.coordinates.symm
        (FramedTaylorResidual.pulled (residualFrame s r) u v) := by
  change (frameEquiv s.frame r.frame u).symm.toContinuousLinearMap _ = _
  rw [frameEquiv_backward (det_ne_zero hg hu)]
  ext i
  fin_cases i <;>
    simp [backward, FramedTaylorResidual.pulled, residualFrame,
      FramedTaylorResidual.Frame.ofEndpoints,
      frameData, PositionFrameSlabs.coordinates, eval_entry, affineDet] <;> ring

/-- A true transformed central defect on the model coordinates gives the
residual hypothesis of the physical moving-frame theorem. -/
theorem residual_of_pulled {lim : Limits} {s : PositionFrameSlabs.State} {r : Step} {m : Inputs}
    (hg : geometry lim s r = true) (hm : CenterMatches r m) {a phase sign t : ℝ}
    (ht : t ∈ Icc a (a + 1 / 64))
    (actual : let u := coord a t
              let v := physicalFlow phase sign t (FramedTaylorResidual.position m u) -
                FramedTaylorResidual.velocity m 128 u
              let w := FramedTaylorResidual.pulled (residualFrame s r) u v
              Real.sqrt ((w 0) ^ 2 + (w 1) ^ 2) ≤ (r.defect : ℝ)) :
    ‖(moving s r a t).symm (euclideanFlow phase sign t (reference a r t) -
      referenceVelocity a r t)‖ ≤ r.defect := by
  let u := coord a t
  let e := PositionFrameSlabs.coordinates
  let d := physicalFlow phase sign t (FramedTaylorResidual.position m u) -
    FramedTaylorResidual.velocity m 128 u
  have velocity : euclideanFlow phase sign t (reference a r t) - referenceVelocity a r t =
      e.symm d := by
    apply e.injective
    rw [map_sub, e.apply_symm_apply]
    change (physicalFlow phase sign t (PositionFrameSlabs.coordinates (reference a r t)) -
      PositionFrameSlabs.coordinates (referenceVelocity a r t)) = _
    rw [hm.position, hm.velocity]
  rw [velocity]
  change ‖(frameEquiv s.frame r.frame u).symm (PositionFrameSlabs.coordinates.symm d)‖ ≤ _
  rw [pulled_eq hg (abs_coord_le ht), EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs]
  exact actual

/-- The coordinate bounds on a Euclidean trial ball agree with the two
dyadic error radii in the scalar trace and shared field packet. -/
theorem trial_membership {lim : Limits} {s : PositionFrameSlabs.State} {r : Step} {m : Inputs}
    (ok : test lim s r = true) (hm : CenterMatches r m)
    (hu : (m.u.radius : ℝ) = r.physicalTrial / (2 : ℝ) ^ 80)
    (hz : m.z.radius = m.u.radius) {a t : ℝ} (ht : t ∈ Icc a (a + 1 / 64))
    {v : Plane} (hv : v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)) :
    let x := reference a r t + moving s r a t v
    m.u.Mem (coord a t) (x 0 - dkR0) ∧ m.z.Mem (coord a t) (x 1) := by
  obtain ⟨geo, grow⟩ := Bool.and_eq_true_iff.mp ok
  have op := frame_op_norm geo (abs_coord_le ht)
  have radius := (growth_sound grow).2.2.2.2.2.2.2.1
  have V : ‖v‖ ≤ r.trial / (2 : ℝ) ^ 80 := by simpa using hv
  have bound : ‖moving s r a t v‖ ≤ r.physicalTrial / (2 : ℝ) ^ 80 := by
    apply ((moving s r a t).toContinuousLinearMap.le_opNorm_of_le V).trans
    apply (mul_le_mul_of_nonneg_right op (by positivity)).trans
    simpa only [← mul_div_assoc] using
      div_le_div_of_nonneg_right radius (by positivity : 0 ≤ (2:ℝ) ^ 80)
  have c (i : Fin 2) : |moving s r a t v i| ≤ r.physicalTrial / (2 : ℝ) ^ 80 :=
    (PiLp.norm_apply_le _ i).trans bound
  have h := hm.position a t
  have x := congrFun h 0
  have z := congrFun h 1
  change reference a r t 0 = dkR0 + eval m.u.poly (coord a t) at x
  change reference a r t 1 = eval m.z.poly (coord a t) at z
  dsimp only
  constructor
  · rw [Model.Mem, hu, PiLp.add_apply, x]
    convert c 0 using 2
    ring
  · rw [Model.Mem, hz, hu, PiLp.add_apply, z, add_sub_cancel_left]
    exact c 1

/-- Positive radius and field denominator on the trial ball supply all
qualitative ODE conditions. The remaining two inputs are the numerical
logarithmic norm and the inverse-frame residual for the same field. -/
theorem field_bounds {lim : Limits} {s : PositionFrameSlabs.State} {r : Step} {a phase sign : ℝ}
    (ok : test lim s r = true)
    (reg : ∀ t ∈ Icc a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      let x := reference a r t + moving s r a t v
      0 < x 0 ∧ atPoint dD (x 0) (phase + sign * t) (x 1) ≠ 0)
    (quad : ∀ t ∈ Ico a (a + 1 / 64), ∀ v ∈ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80),
      ∀ w : Plane, let x := reference a r t + moving s r a t v
      ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian (velocityJacobian phase sign t x)
        (moving s r a t) (frameVelocity s.frame r.frame) w⟫ ≤ r.mu * ‖w‖^2)
    (res : ∀ t ∈ Ico a (a + 1 / 64), ‖(moving s r a t).symm
      (euclideanFlow phase sign t (reference a r t) - referenceVelocity a r t)‖ ≤ r.defect) :
    FieldBounds s r a (euclideanFlow phase sign) (velocityJacobian phase sign) ballDomain := by
  let S := Icc a (a + 1 / 64) ×ˢ Metric.closedBall (0 : Plane) (r.trial / (2 : ℝ) ^ 80)
  let x := fun q : ℝ × Plane => reference a r q.1 + moving s r a q.1 q.2
  let g := fun q : ℝ × Plane => (q.1,x q)
  have geo := (Bool.and_eq_true_iff.mp ok).1
  have cm : ContinuousOn (fun t => (moving s r a t).toContinuousLinearMap) (Icc a (a + 1 / 64)) :=
    fun _ ht => (hasDerivWithinAt_frame geo a ht).continuousWithinAt
  have fstmem : MapsTo Prod.fst S (Icc a (a + 1 / 64)) := fun _ h => h.1
  have cp : Continuous (reference a r) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_reference a r t).continuousAt)
  have cg : ContinuousOn g S := continuous_fst.continuousOn.prodMk
    ((cp.comp continuous_fst).continuousOn.add
      ((cm.comp continuous_fst.continuousOn fstmem).clm_apply continuous_snd.continuousOn))
  have regular {q : ℝ × Plane} (hq : q ∈ S) :
      0 < x q 0 ∧ clockValue dD phase sign (g q) ≠ 0 := reg _ hq.1 _ hq.2
  refine ⟨?_,?_,?_,quad,res⟩
  · intro q hq
    exact (continuousAt_euclideanFlow phase sign (g q) (regular hq).1
      (regular hq).2).comp_continuousWithinAt (cg q hq)
  · intro q hq
    exact (continuousAt_velocityJacobian phase sign (g q) (regular hq).2).comp_continuousWithinAt
      (cg q hq)
  · intro t ht v hv
    obtain ⟨hr,hd⟩ := reg t ht v hv
    exact physical_derivative phase sign t _ hr hd

end PlasmaLean.Design.DommaschkPhysicalTraceStep
