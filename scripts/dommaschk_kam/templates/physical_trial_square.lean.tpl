  have radius : (${jac}.trial.u.radius : ℝ) =
      row.physicalTrial / (2 : ℝ) ^ 80 := by
    change ((${error} / 2^80 : ℚ) : ℝ) = ${error} / (2 : ℝ) ^ 80
    norm_num
  simpa only [clock] using trial_membership checked trialMatches radius (by rfl) ht hv
