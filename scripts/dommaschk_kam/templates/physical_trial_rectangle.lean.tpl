  have box : PositionFrameProjection.Rectangle previous.frame row.frame row.trial
      ${radial} ${vertical} := by
    constructor <;> unfold PositionFrameProjection.rowFits <;>
      apply (Int.ble'_eq_true _ _).mp <;> with_unfolding_all rfl
  have ru : (${jac}.trial.u.radius : ℝ) = (${radial} : ℝ) / 2^80 := by
    change ((${radial} / 2^80 : ℚ) : ℝ) = _
    norm_num
  have rz : (${jac}.trial.z.radius : ℝ) = (${vertical} : ℝ) / 2^80 := by
    change ((${vertical} / 2^80 : ℚ) : ℝ) = _
    norm_num
  simpa only [clock] using
    DommaschkProjectedTrial.trial_membership checked trialMatches box ru rz ht hv
