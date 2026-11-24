open PlasmaLean.Certificates.PositionFrameSlabs
open scoped RealInnerProductSpace

/-- Common certified growth allowance for the two physical clock directions. -/
def logNorm : ℚ := ${rate}

/-- Actual harmonics on the archived clock, for either coordinate width. -/
theorem clock_inputs {t R z : ℝ} (ht : t ∈ Set.Icc (${i}/64 : ℝ) (${end}/64))
    (hu : trial.u.Mem (128*t-${offset}) (R-dkR0)) (hz : trial.z.Mem (128*t-${offset}) z) :
    trial.Mem (128*t-${offset}) (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) := by
  let p := ${harmonic}.packet (${local} : Fin ${count})
  have h : t ∈ Set.Icc ((↑(${base}+(${local} : Fin ${count}).val : ℕ) : ℝ)/64)
      (((↑(${base}+(${local} : Fin ${count}).val : ℕ) : ℝ)+1)/64) := by norm_num at ht ⊢; exact ht
  have hc := Certificates.TrajectoryHarmonicPacket.physical p false 0 false h
  have hs := Certificates.TrajectoryHarmonicPacket.physical p false 0 true h
  refine ⟨hu,hz,?_,?_⟩
  · change ((p false 0).model false).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at hc ⊢
    exact hc
  · change ((p false 0).model true).Mem _ _
    norm_num [Certificates.TrajectoryTrig.wave] at hs ⊢
    exact hs

/-- The physical field denominator stays positive on the rectangle. -/
theorem denominator_pos {t R z : ℝ} (ht : t ∈ Set.Icc (${i}/64 : ℝ) (${end}/64))
    (hu : trial.u.Mem (128*t-${offset}) (R-dkR0)) (hz : trial.z.Mem (128*t-${offset}) z) :
    0 < evR (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)) dD := by
  have hs : |128*t-${offset}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact lt_of_lt_of_le (by norm_num) (dD_range hs (dD_checked.mem hs (clock_inputs ht hu hz))).1

/-- The enclosed transformed field Jacobian satisfies the common recorded rate. -/
theorem physical_clock_log_norm {t R z : ℝ} (ht : t ∈ Set.Icc (${i}/64 : ℝ) (${end}/64))
    (hu : trial.u.Mem (128*t-${offset}) (R-dkR0)) (hz : trial.z.Mem (128*t-${offset}) z)
    (w : Plane) : ⟪w, Fields.LogNormTrajectory.MovingFrame.jacobian
      (spatialMatrix (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))
      (frameEquiv leftFrame rightFrame (128*t-${offset})) (frameVelocity leftFrame rightFrame) w⟫ ≤
      (logNorm : ℝ)*‖w‖^2 := by
  have hs : |128*t-${offset}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact spatial_log_norm_of_cover ${panel}.accepted leftFrame rightFrame _ _ _ _ _ hs
    (models_mem hs (clock_inputs ht hu hz)) w

/-- The common rate fits the forward witness. -/
theorem fits_record : logNorm ≤ ${forward_rate} := by norm_num [logNorm]
