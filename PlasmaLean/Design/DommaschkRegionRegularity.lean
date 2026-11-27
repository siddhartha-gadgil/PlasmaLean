/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkCartesianAngleFlow
public import PlasmaLean.Theory.Fields.FlowLabel

/-!
# Regularity of the QA2R field and of its field-line equation on the spatial envelope

One place for the regularity statements used by the guiding-centre drift bound of note N-216, at
the points `cylPoint (p 0) t (p 1)` with `p` in the closed envelope `Region` and `t` any angle.

* `field_contDiffAt`, `field_contDiffAt_one`: the Cartesian field is `C²` (hence `C¹`) there;
  `field_ne_zero`, `field_curl`, `field_div`: it does not vanish, and is curl- and
  divergence-free; `vacuum_at` collects the four statements.
* `norm_gradAbsB_le`, `norm_gradAbsB_le_region`: `‖∇|B|‖ ≤ ‖DB‖` (operator norm) where the field
  is differentiable and nonzero, in particular on the envelope.
* `contDiffAt_spaceTime`: the space-time field `(1, euclideanFlow 0 1 t x)`, which is
  `FlowLabel.field (euclideanFlow 0 1)`, is `C¹` at every `(t, x)` with positive radius and
  nonzero toroidal denominator; `isOpen_good` shows that these points form an open set, and
  `region_subset_good` that it contains `ℝ × Region` (`contDiffAt_spaceTime_region`).

**Sanity.** `good_example` is a concrete point of the open set, and `not_good_axis` shows that
the points on the axis of the cylinder are excluded.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkRegionRegularity
open Fields Contract Set
open Certificates.PositionFrameSlabs (Plane)
open DommaschkSignedTraceDomain DommaschkBounceField DommaschkKam DommaschkJacobian
open DommaschkCartesianAngleFlow DkPoly

/-! ## The Cartesian field -/

/-- The QA2R field is twice continuously differentiable off the axis. -/
theorem contDiffAt_domain {x : Space} (hx : x ∈ CylAlgebra.domain) : ContDiffAt ℝ 2 B x :=
  (DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).contDiffOn.contDiffAt
    ((DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).isOpen.mem_nhds hx)

/-- The Maxwell curl of a derivative operator is the kernel's curl. -/
theorem curl_eq_curlOp (L : Space →L[ℝ] Space) : curl L = Vacuum.curlOp L := by
  obtain ⟨h0, h1, h2⟩ := curl_coords L
  ext i
  fin_cases i <;> simp [h0, h1, h2, Vacuum.curlOp]

/-- The QA2R field is `C²` at every point of the envelope, at every angle. -/
theorem field_contDiffAt {p : Plane} (reg : Region p) (t : ℝ) :
    ContDiffAt ℝ 2 B (cylPoint (p 0) t (p 1)) :=
  contDiffAt_domain (in_regular reg t).1

/-- The QA2R field is `C¹` at every point of the envelope, at every angle. -/
theorem field_contDiffAt_one {p : Plane} (reg : Region p) (t : ℝ) :
    ContDiffAt ℝ 1 B (cylPoint (p 0) t (p 1)) :=
  (field_contDiffAt reg t).of_le (by norm_num)

/-- The QA2R field does not vanish on the envelope. -/
theorem field_ne_zero {p : Plane} (reg : Region p) (t : ℝ) : B (cylPoint (p 0) t (p 1)) ≠ 0 :=
  DommaschkCartesianAngleFlow.field_ne_zero (in_regular reg t)

/-- The QA2R field is curl-free on the envelope. -/
theorem field_curl {p : Plane} (reg : Region p) (t : ℝ) :
    curl (fderiv ℝ B (cylPoint (p 0) t (p 1))) = 0 := by
  rw [curl_eq_curlOp]
  exact (DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).curl_eq_zero _ (in_regular reg t).1

/-- The QA2R field is divergence-free on the envelope. -/
theorem field_div {p : Plane} (reg : Region p) (t : ℝ) :
    Vacuum.fieldDiv B (cylPoint (p 0) t (p 1)) = 0 :=
  (DommaschkQA2R.field_vacuum DommaschkQA2R.candidate).div_eq_zero _ (in_regular reg t).1

/-- All regularity statements of the vacuum field at a point of the envelope. -/
theorem vacuum_at {p : Plane} (reg : Region p) (t : ℝ) :
    ContDiffAt ℝ 2 B (cylPoint (p 0) t (p 1)) ∧ B (cylPoint (p 0) t (p 1)) ≠ 0 ∧
      curl (fderiv ℝ B (cylPoint (p 0) t (p 1))) = 0 ∧
      Vacuum.fieldDiv B (cylPoint (p 0) t (p 1)) = 0 :=
  ⟨field_contDiffAt reg t, field_ne_zero reg t, field_curl reg t, field_div reg t⟩

/-! ## The gradient of the field strength -/

/-- **The gradient of the field strength is bounded by the operator norm of the derivative of
the field**, where the field is differentiable and does not vanish (`∇|B| = (DB)ᵀ b`). -/
theorem norm_gradAbsB_le {F : Space → Space} {x : Space} (hF : DifferentiableAt ℝ F x)
    (h0 : F x ≠ 0) : ‖Kinetic.GCLittlejohn.gradAbsB F x‖ ≤ ‖fderiv ℝ F x‖ := by
  have hn : DifferentiableAt ℝ (fun y : Space => ‖y‖) (F x) := (differentiableAt_id.norm ℝ h0)
  have comp : fderiv ℝ (fun y => ‖F y‖) x =
      (fderiv ℝ (fun y : Space => ‖y‖) (F x)).comp (fderiv ℝ F x) := fderiv_comp x hn hF
  rw [Kinetic.GCLittlejohn.gradAbsB, gradient, LinearIsometryEquiv.norm_map, comp]
  calc ‖(fderiv ℝ (fun y : Space => ‖y‖) (F x)).comp (fderiv ℝ F x)‖
      ≤ ‖fderiv ℝ (fun y : Space => ‖y‖) (F x)‖ * ‖fderiv ℝ F x‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ F x‖ := by
        gcongr
        have lip : LipschitzWith 1 (fun y : Space => ‖y‖) := lipschitzWith_one_norm
        simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := F x) lip
    _ = ‖fderiv ℝ F x‖ := one_mul _

/-- On the envelope the gradient of the QA2R field strength is bounded by the operator norm of
the derivative of the field. -/
theorem norm_gradAbsB_le_region {p : Plane} (reg : Region p) (t : ℝ) :
    ‖Kinetic.GCLittlejohn.gradAbsB B (cylPoint (p 0) t (p 1))‖ ≤
      ‖fderiv ℝ B (cylPoint (p 0) t (p 1))‖ :=
  norm_gradAbsB_le ((field_contDiffAt reg t).differentiableAt (by norm_num)) (field_ne_zero reg t)

/-! ## The field-line equation on space-time -/

/-- Space-time points with positive radius and nonzero toroidal denominator. -/
def good : Set (ℝ × Plane) := {q | 0 < q.2 0 ∧ atPoint dD (q.2 0) q.1 (q.2 1) ≠ 0}

/-- A sparse polynomial along the angular clock is smooth on space-time. -/
theorem contDiff_clock (p : SP) :
    ContDiff ℝ 1 (fun q : ℝ × Plane => atPoint p (q.2 0) q.1 (q.2 1)) := by
  induction p with
  | nil => exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × Plane => (0 : ℝ)))
  | cons m p ih =>
    change ContDiff ℝ 1 (fun q : ℝ × Plane =>
      (m.q : ℝ) * ((q.2 0 - dkR0) ^ m.a * (q.2 1) ^ m.b *
        (Real.cos (2 * q.1)) ^ m.c * (Real.sin (2 * q.1)) ^ m.d) +
      atPoint p (q.2 0) q.1 (q.2 1))
    apply ContDiff.add _ ih
    fun_prop

/-- The good set is open. -/
theorem isOpen_good : IsOpen good := by
  have hr : Continuous (fun q : ℝ × Plane => q.2 0) := by fun_prop
  exact (isOpen_lt continuous_const hr).inter
    ((contDiff_clock dD).continuous.isOpen_preimage _ isOpen_compl_singleton)

/-- Space-time over the closed envelope lies in the good set. -/
theorem region_subset_good {p : Plane} (reg : Region p) (t : ℝ) : (t, p) ∈ good :=
  ⟨by linarith [reg.1.1],
    (lt_trans (by norm_num) (DommaschkSignedTraceDenominator.regular t reg.1 reg.2)).ne'⟩

/-- **The space-time field of the field-line equation is `C¹` on the good set.** The map is
`FlowLabel.field (euclideanFlow 0 1)`. -/
theorem contDiffAt_spaceTime {q : ℝ × Plane} (hq : q ∈ good) :
    ContDiffAt ℝ 1 (fun y : ℝ × Plane => ((1 : ℝ), euclideanFlow 0 1 y.1 y.2)) q := by
  have cd := (contDiff_clock dD).contDiffAt (x := q)
  have ratio : ContDiffAt ℝ 1
      (fun y : ℝ × Plane => fun i : Fin 2 =>
        (![atPoint dnR (y.2 0) y.1 (y.2 1) / atPoint dD (y.2 0) y.1 (y.2 1),
          atPoint dnZ (y.2 0) y.1 (y.2 1) / atPoint dD (y.2 0) y.1 (y.2 1)] : Fin 2 → ℝ) i) q := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_clock dnR).contDiffAt.div cd hq.2
    · exact (contDiff_clock dnZ).contDiffAt.div cd hq.2
  have flow : ContDiffAt ℝ 1 (fun y : ℝ × Plane => euclideanFlow 0 1 y.1 y.2) q := by
    have hr : Continuous (fun y : ℝ × Plane => y.2 0) := by fun_prop
    apply (coordinates.symm.contDiff.contDiffAt.comp q ratio).congr_of_eventuallyEq
    filter_upwards [hr.continuousAt.eventually_const_lt hq.1,
      cd.continuousAt.eventually_ne hq.2] with y hR hden
    have key := ratio_eq_physical 0 1 y.1 (coordinates y.2) hR
      (by simpa [clockPoly] using hden)
    rw [euclideanFlow, ← key]
    congr 1
    funext i
    fin_cases i <;> simp [ratioFlow, clockPoly]
  exact contDiffAt_const.prodMk flow

/-- The space-time field is `C¹` at every angle over the closed envelope. -/
theorem contDiffAt_spaceTime_region {p : Plane} (reg : Region p) (t : ℝ) :
    ContDiffAt ℝ 1 (FlowLabel.field (euclideanFlow 0 1)) (t, p) :=
  contDiffAt_spaceTime (region_subset_good reg t)

/-- **Sanity**: points on the axis of the cylinder are not in the good set. -/
theorem not_good_axis (t : ℝ) (x : Plane) (hx : x 0 = 0) : (t, x) ∉ good := by
  intro h
  have := h.1
  simp [hx] at this

/-- **Sanity**: a concrete point of the envelope, at angle zero, lies in the good set. -/
theorem good_example : ((0 : ℝ), (WithLp.toLp 2 ![15 / 16, 0] : Plane)) ∈ good := by
  apply region_subset_good
  simp only [Region, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end PlasmaLean.Design.DommaschkRegionRegularity
