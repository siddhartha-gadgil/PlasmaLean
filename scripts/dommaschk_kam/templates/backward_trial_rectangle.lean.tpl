/-- Exact containment of the backward trial in the common signed rectangle. -/
theorem projections : PositionFrameProjection.Rectangle previous.frame row.frame row.trial
    ${radial} ${vertical} := by
  constructor <;> unfold PositionFrameProjection.rowFits <;>
    apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl

private theorem reflected_membership {t : ℝ} (ht : t ∈ Icc (${index} / 64) (${index} / 64 + 1 / 64))
    {v : Plane} (hv : v ∈ Metric.closedBall (0 : Plane) (row.trial / (2 : ℝ) ^ 80)) :
    let x := reference (${index} / 64) row t + moving previous row (${index} / 64) t v
    ${jac}.trial.u.Mem (128*t-${offset}) (x 0 - dkR0) ∧
      ${jac}.trial.z.Mem (128*t-${offset}) (-x 1) := by
  have hu : backReference.u.poly = ${jac}.trial.u.poly := eq_of_beq (by kernel_fact)
  have hz : backReference.z.poly = QPoly.scale (-1) ${jac}.trial.z.poly := eq_of_beq (by kernel_fact)
  have ur : (${jac}.trial.u.radius : ℝ) = (${radial} : ℝ) / 2 ^ 80 := by
    change ((${radial} / 2 ^ 80 : ℚ) : ℝ) = _
    norm_num
  have zr : (${jac}.trial.z.radius : ℝ) = (${vertical} : ℝ) / 2 ^ 80 := by
    change ((${vertical} / 2 ^ 80 : ℚ) : ℝ) = _
    norm_num
  simpa only [clock] using DommaschkProjectedTrial.reflected_membership
    checked central hu hz projections ur zr ht hv
