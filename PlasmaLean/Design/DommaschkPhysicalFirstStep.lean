/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Certificates.PositionFrameBall
public import PlasmaLean.Design.DommaschkPositionFramesFwd
public import PlasmaLean.Design.DommaschkReferenceFirstDefect
public import PlasmaLean.Design.DommaschkJacobianFirstBound
public import PlasmaLean.Design.DommaschkPhysicalJacobian
public import PlasmaLean.Design.DommaschkBounceLaunchStep

/-! # Physical first forward step of the position-frame trace

At q = 0 and launch radius 47/100, the archived moving frame, nominal curve,
and their exact field certificates apply to the same first interval of angle
1/64. Local regularity uses the larger launch rectangle.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPhysicalFirstStep

open Certificates PositionFrameSlabs TrajectoryTaylorModel QPoly
open DommaschkKam DommaschkBounceField DommaschkBounceTaylorFirst Set
open scoped RealInnerProductSpace

/-- Transferred initial state of the forward trajectory. -/
abbrev seed := DommaschkPositionFramesFwd.start

/-- The first step in the checked block, including all raw trajectory coefficients. -/
def row : Step := DommaschkPositionFramesFwd.block0.head (by intro h; contradiction)

theorem checked : test pilotLimits seed row = true := by with_unfolding_all rfl

private theorem geo : geometry pilotLimits seed row = true := (Bool.and_eq_true_iff.mp checked).1
private theorem grow : growth pilotLimits seed row = true := (Bool.and_eq_true_iff.mp checked).2

private theorem norm_clock {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) : |coord 0 t| ≤ 1 :=
  abs_coord_le (by simpa only [zero_add] using ht)

private theorem center (t : ℝ) : reference 0 row t 0 =
    dkR0 + eval trial.u.poly (128*t-1) ∧ reference 0 row t 1 = eval trial.z.poly (128*t-1) := by
  have radial : polynomial row 0 = add [29/32] trial.u.poly := by with_unfolding_all rfl
  have vertical : polynomial row 1 = trial.z.poly := by with_unfolding_all rfl
  simp [reference, coord, radial, vertical, dkR0, eval_add]

private theorem reference_eq (t : ℝ) :
    PositionFrameSlabs.coordinates (reference 0 row t) = DommaschkReferenceFirst.position t := by
  funext i
  fin_cases i
  · exact (center t).1
  · exact (center t).2

private theorem velocity_eq (t : ℝ) :
    PositionFrameSlabs.coordinates (referenceVelocity 0 row t) =
      DommaschkReferenceFirst.velocity t := by
  have eq : (fun t => PositionFrameSlabs.coordinates (reference 0 row t)) =
      DommaschkReferenceFirst.position := funext reference_eq
  have der := PositionFrameSlabs.coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_reference 0 row t)
  change HasDerivAt (fun t => PositionFrameSlabs.coordinates (reference 0 row t))
    (PositionFrameSlabs.coordinates (referenceVelocity 0 row t)) t at der
  rw [eq] at der
  exact der.unique (DommaschkReferenceFirst.position_derivative t)

/-- Every transformed trial-ball point supplies the two actual spatial input
enclosures for both the physical field and its quantitative Jacobian bound. -/
theorem trial_membership {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) {v : Plane}
    (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference 0 row t + moving seed row 0 t v
    trial.u.Mem (128*t-1) (x 0 - dkR0) ∧ trial.z.Mem (128*t-1) (x 1) := by
  have op := frame_op_norm geo (norm_clock ht)
  have radius := (growth_sound grow).2.2.2.2.2.2.2.1
  have V : ‖v‖ ≤ row.trial/(2:ℝ)^80 := by simpa using hv
  have bound : ‖moving seed row 0 t v‖ ≤ row.physicalTrial/(2:ℝ)^80 := by
    apply ((moving seed row 0 t).toContinuousLinearMap.le_opNorm_of_le V).trans
    apply (mul_le_mul_of_nonneg_right op (by positivity)).trans
    simpa only [← mul_div_assoc] using
      div_le_div_of_nonneg_right radius (by positivity : 0 ≤ (2 : ℝ)^80)
  have c (i : Fin 2) : |moving seed row 0 t v i| ≤ row.physicalTrial/(2:ℝ)^80 :=
    (PiLp.norm_apply_le _ i).trans bound
  have ru : (trial.u.radius : ℝ) = row.physicalTrial/(2:ℝ)^80 := by
    change ((2962422779848895172 / 2^80 : ℚ) : ℝ) = 2962422779848895172 / (2:ℝ)^80
    norm_num
  have rz : trial.z.radius = trial.u.radius := by rfl
  dsimp only
  constructor
  · rw [Model.Mem, ru, PiLp.add_apply, (center t).1]
    convert c 0 using 2
    ring
  · rw [Model.Mem, rz, ru, PiLp.add_apply, (center t).2, add_sub_cancel_left]
    exact c 1

private theorem square_regular {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) {v : Plane}
    (hv : v ∈ trialSquare (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference 0 row t + moving seed row 0 t v
    0 < x 0 ∧ atPoint dD (x 0) (0 + 1 * t) (x 1) ≠ 0 := by
  let x := reference 0 row t + moving seed row 0 t v
  have hT : row.trial/(2:ℝ)^80 ≤ 1/100000 := by
    change 2950393085339130478/(2:ℝ)^80 ≤ 1/100000
    norm_num
  have vnorm : ‖v‖ ≤ 1/10000 := by
    have c (i : Fin 2) : |v i| ≤ 1/100000 := (abs_le.mpr (hv i)).trans hT
    have sq (i : Fin 2) := pow_le_pow_left₀ (abs_nonneg _) (c i) 2
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have r := sq 0
    have z := sq 1
    rw [sq_abs] at r z
    linarith
  have op : ‖(moving seed row 0 t).toContinuousLinearMap‖ ≤ 2 := by
    apply (frame_op_norm geo (norm_clock ht)).trans
    change (1103994687697 / 1099511627776 : ℚ) ≤ (2 : ℝ)
    norm_num
  have error (i : Fin 2) : |moving seed row 0 t v i| ≤ 1/1000 :=
    (PiLp.norm_apply_le _ i).trans <| ((moving seed row 0 t).toContinuousLinearMap.le_opNorm_of_le
      vnorm).trans ((mul_le_mul_of_nonneg_right op (by norm_num)).trans (by norm_num))
  have zero : (0 : Plane) ∈ Metric.closedBall 0 (row.trial / (2 : ℝ) ^ 80) :=
    Metric.mem_closedBall_self (by positivity)
  obtain ⟨u,z⟩ := trial_membership ht zero
  simp only [map_zero, add_zero] at u z
  have hs : |128*t-1| ≤ 1 := by simpa [coord] using norm_clock ht
  have R := enclose (c := ⟨[9/100],1/1000⟩) hs u (by kernel_fact)
  have Z := enclose (c := ⟨[],1/200⟩) hs z (by kernel_fact)
  norm_num [Model.Mem, dkR0, abs_le] at R Z
  have er := abs_le.mp (error 0)
  have ez := abs_le.mp (error 1)
  have box : PositionFrameSlabs.coordinates x ∈ Icc (tubeLo false) (tubeHi false) := by
    constructor <;> intro i <;> fin_cases i <;>
      norm_num [PositionFrameSlabs.coordinates, x, tubeLo, tubeHi] <;> linarith
  have pos := tube_speeds false (phase := 0) (sign := 1) (by norm_num)
    (by norm_num [sectionPhase]) ht (PositionFrameSlabs.coordinates x) box
  refine ⟨?_,pos.1.ne'⟩
  have low := box.1 0
  change 63/64 ≤ x 0 at low
  linarith

private theorem frame_action {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) (v : Plane) :
    moving seed row 0 t v 0 =
      DommaschkReferenceFirst.frame 0 0 t * v 0 + DommaschkReferenceFirst.frame 0 1 t * v 1 ∧
    moving seed row 0 t v 1 =
      DommaschkReferenceFirst.frame 1 0 t * v 0 + DommaschkReferenceFirst.frame 1 1 t * v 1 := by
  change (frameEquiv seed.frame row.frame (coord 0 t)).toContinuousLinearMap v 0 = _ ∧
    (frameEquiv seed.frame row.frame (coord 0 t)).toContinuousLinearMap v 1 = _
  rw [frameEquiv_forward (det_ne_zero geo (norm_clock ht))]
  change forward DommaschkJacobian.firstLeft DommaschkJacobian.firstRight (coord 0 t) v 0 = _ ∧
    forward DommaschkJacobian.firstLeft DommaschkJacobian.firstRight (coord 0 t) v 1 = _
  constructor <;> norm_num [forward, entry, coord, DommaschkJacobian.firstLeft,
    DommaschkJacobian.firstRight, DommaschkReferenceFirst.frame, DommaschkReferenceFirst.frameEnd]
    <;> ring

/-- The central defect certificate applies to the same Euclidean affine frame
and the same differentiated dyadic reference as the scalar trajectory step. -/
theorem physical_residual {t : ℝ} (ht : t ∈ Icc 0 (1 / 64)) :
    ‖(moving seed row 0 t).symm
      (DommaschkJacobian.euclideanFlow 0 1 t (reference 0 row t) - referenceVelocity 0 row t)‖ ≤
        row.defect := by
  let d := physicalFlow 0 1 t (DommaschkReferenceFirst.position t) -
    DommaschkReferenceFirst.velocity t
  let e := PositionFrameSlabs.coordinates
  have residual : DommaschkJacobian.euclideanFlow 0 1 t (reference 0 row t) -
      referenceVelocity 0 row t = e.symm d := by
    apply e.injective
    rw [map_sub, e.apply_symm_apply]
    change (physicalFlow 0 1 t (PositionFrameSlabs.coordinates (reference 0 row t)) -
      PositionFrameSlabs.coordinates (referenceVelocity 0 row t)) = _
    rw [reference_eq, velocity_eq]
  let w := DommaschkReferenceFirst.pullback t d
  have inv : (moving seed row 0 t).symm (e.symm d) = e.symm w := by
    apply (moving seed row 0 t).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have eq := frame_action ht (e.symm w)
    have hw := DommaschkReferenceFirst.frame_pullback ht d
    ext i
    fin_cases i
    · exact (eq.1.trans hw.1).symm
    · exact (eq.2.trans hw.2).symm
  rw [residual, inv, EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs]
  exact DommaschkReferenceFirst.framed_defect ht

private theorem bounds_of_regular (domain : RegularityDomain)
    (reg : ∀ {t : ℝ}, t ∈ Icc 0 (1 / 64) → ∀ {v : Plane},
      v ∈ domain.region (row.trial / (2 : ℝ) ^ 80) →
      let x := reference 0 row t + moving seed row 0 t v
      0 < x 0 ∧ atPoint dD (x 0) (0 + 1 * t) (x 1) ≠ 0) :
    FieldBounds seed row 0 (DommaschkJacobian.euclideanFlow 0 1)
      (DommaschkJacobian.velocityJacobian 0 1) domain := by
  let S := Icc (0 : ℝ) (1/64) ×ˢ domain.region (row.trial / (2 : ℝ) ^ 80)
  let x := fun q : ℝ × Plane => reference 0 row q.1 + moving seed row 0 q.1 q.2
  let g := fun q : ℝ × Plane => (q.1,x q)
  have cm : ContinuousOn (fun t => (moving seed row 0 t).toContinuousLinearMap) (Icc 0 (1/64)) := by
    intro t ht
    simpa only [moving, zero_add] using
      (hasDerivWithinAt_frame geo 0 (by simpa using ht)).continuousWithinAt
  have fstmem : MapsTo Prod.fst S (Icc 0 (1/64)) := fun _ h => h.1
  have cp : Continuous (reference 0 row) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_reference 0 row t).continuousAt)
  have cg : ContinuousOn g S := continuous_fst.continuousOn.prodMk
    ((cp.comp continuous_fst).continuousOn.add
      ((cm.comp continuous_fst.continuousOn fstmem).clm_apply continuous_snd.continuousOn))
  have regular {q : ℝ × Plane} (hq : q ∈ S) :
      0 < x q 0 ∧ DommaschkJacobian.clockValue dD 0 1 (g q) ≠ 0 := reg hq.1 hq.2
  constructor
  · simp only [zero_add]
    intro q hq
    exact (DommaschkJacobian.continuousAt_euclideanFlow 0 1 (g q)
      (regular hq).1 (regular hq).2).comp_continuousWithinAt (cg q hq)
  · simp only [zero_add]
    intro q hq
    exact (DommaschkJacobian.continuousAt_velocityJacobian 0 1 (g q)
      (regular hq).2).comp_continuousWithinAt (cg q hq)
  · simp only [zero_add]
    intro t ht v hv
    obtain ⟨hr,hd⟩ := reg ht hv
    exact DommaschkJacobian.physical_derivative 0 1 t _ hr hd
  · simp only [zero_add]
    intro t ht v hv w
    have ht' := Ico_subset_Icc_self ht
    obtain ⟨hu,hz⟩ := trial_membership ht' hv
    have hj := DommaschkJacobian.physical_clock_log_norm ht' hu hz w
    have eq := DommaschkJacobian.velocityJacobian_spatial 0 1 t (x (t,v))
    simp only [zero_add,one_mul,one_smul] at eq
    change ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (DommaschkJacobian.velocityJacobian 0 1 t (x (t,v))) _ _ w⟫ ≤ _
    rw [eq]
    have mu : (201/10000 : ℝ) ≤ (row.mu : ℝ) := by
      change (201/10000 : ℝ) ≤ ((25957146047869133785551/1229689707490054184020096 : ℚ) : ℝ)
      norm_num
    have leftFrame : seed.frame = DommaschkJacobian.firstLeft := rfl
    have rightFrame : row.frame = DommaschkJacobian.firstRight := rfl
    simpa only [x, Prod.fst, Prod.snd, moving, leftFrame, rightFrame, coord, sub_zero] using
      hj.trans (mul_le_mul_of_nonneg_right mu (sq_nonneg _))
  · simp only [zero_add]
    exact fun _ ht => physical_residual (Ico_subset_Icc_self ht)

/-- Regularity and numerical inputs on the larger Cartesian square. -/
theorem field_bounds : FieldBounds seed row 0 (DommaschkJacobian.euclideanFlow 0 1)
    (DommaschkJacobian.velocityJacobian 0 1) :=
  bounds_of_regular squareDomain square_regular

/-- On the Euclidean trial ball, the quantitative Taylor enclosures also give
all denominator and radius conditions for local existence. -/
theorem ball_field_bounds : FieldBounds seed row 0 (DommaschkJacobian.euclideanFlow 0 1)
    (DommaschkJacobian.velocityJacobian 0 1) ballDomain := by
  apply bounds_of_regular
  intro t ht v hv
  let x := reference 0 row t + moving seed row 0 t v
  obtain ⟨hu,hz⟩ := trial_membership ht hv
  have hs : |128*t-1| ≤ 1 := by simpa [coord] using norm_clock ht
  have radial := enclose (c := ⟨[1/10],1/20⟩) hs hu (by kernel_fact)
  have hr : 0 < x 0 := by
    change (⟨[1/10],1/20⟩ : Model).Mem (128*t-1) (x 0 - dkR0) at radial
    norm_num [Model.Mem, dkR0, abs_le] at radial
    linarith
  have hD := (physical_clock_ranges ht hu hz).1
  have eq := (field_id hr t (x 1)).1
  refine ⟨hr, ?_⟩
  simp only [zero_add, one_mul]
  change atPoint dD (x 0) t (x 1) ≠ 0
  rw [eq]
  exact (zero_lt_one.trans hD).ne'

/-- The first forward interval of the archived pilot now has a physical QA2R
solution through every transferred entry point, with its certified Euclidean
error at all times and its exact exit ellipsoid ready for the next step. -/
theorem physical_first_step :
    Fields.TrajectorySlabs.Step (DommaschkJacobian.euclideanFlow 0 1)
      (physicalSlab seed row 0) (stateSet seed) (stateSet (next row)) :=
  physical_step_ball checked ball_field_bounds

end PlasmaLean.Design.DommaschkPhysicalFirstStep
