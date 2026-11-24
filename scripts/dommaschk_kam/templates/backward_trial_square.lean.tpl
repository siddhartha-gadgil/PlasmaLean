/-- Each of the four endpoint frame rows fits the original forward spatial box. -/
theorem projections : PositionFrameProjection.Fits previous.frame row.frame row.trial
    ${radius} := by
  constructor <;> unfold PositionFrameProjection.rowFits <;>
    apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl

private theorem reflected_membership {t : ℝ} (ht : t ∈ Icc (${index} / 64) (${index} / 64 + 1 / 64))
    {v : Plane} (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference (${index} / 64) row t + moving previous row (${index} / 64) t v
    ${jac}.trial.u.Mem (128*t-${offset}) (x 0 - dkR0) ∧
      ${jac}.trial.z.Mem (128*t-${offset}) (-x 1) := by
  let s := coord (${index}/64) t
  have hs : |s| ≤ 1 := abs_coord_le ht
  have det := det_ne_zero ((Bool.and_eq_true_iff.mp checked).1) hs
  have bound (i : Fin 2) : |moving previous row (${index}/64) t v i| ≤ (${radius}:ℝ)/2^80 :=
    PositionFrameProjection.coordinates_le projections hs det (by simpa using hv) i
  have hr := congrFun (central.position (${index}/64) t) 0
  have hz := congrFun (central.position (${index}/64) t) 1
  change reference (${index}/64) row t 0 = dkR0 + QPoly.eval backReference.u.poly s at hr
  change reference (${index}/64) row t 1 = QPoly.eval backReference.z.poly s at hz
  have ru : backReference.u.poly = ${jac}.trial.u.poly :=
    eq_of_beq (by kernel_fact)
  have rz : backReference.z.poly = QPoly.scale (-1) ${jac}.trial.z.poly :=
    eq_of_beq (by kernel_fact)
  rw [ru] at hr
  rw [rz,QPoly.eval_scale,Rat.cast_neg,Rat.cast_one,neg_one_mul] at hz
  have rad : (${jac}.trial.u.radius : ℝ) =
      (${radius}:ℝ)/2^80 := by
    change ((${radius}/2^80 : ℚ) : ℝ) = _
    norm_num
  have radz : ${jac}.trial.z.radius =
      ${jac}.trial.u.radius := rfl
  dsimp only
  rw [← clock]
  constructor
  · rw [Model.Mem,rad,PiLp.add_apply,hr]
    convert bound 0 using 2
    ring
  · rw [Model.Mem,radz,rad,PiLp.add_apply,hz]
    convert bound 1 using 1
    rw [show -(-QPoly.eval ${jac}.trial.z.poly s +
      moving previous row (${index}/64) t v 1) - QPoly.eval ${jac}.trial.z.poly s =
      -(moving previous row (${index}/64) t v 1) by ring, abs_neg]
