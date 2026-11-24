/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.TrappedBirthBand
public import PlasmaLean.Theory.Fields.CurlProduct
public import PlasmaLean.Theory.Fields.FormBridges
public import PlasmaLean.Theory.Kinetic.LorentzExistence

/-! # Local Littlejohn motion in a nonvanishing current-free magnetic field -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.VacuumLittlejohnLocal
open Fields Vacuum GCLittlejohn Contract Set Metric
open scoped RealInnerProductSpace Topology

variable {B : Space → Space} {Ω : Set Space}

/-- Curl-freeness cancels the parallel part of the guiding-centre correction at every velocity. -/
theorem parallel_eq_norm {x : Space} (nzero : B x ≠ 0) (diff : DifferentiableAt ℝ B x)
    (nocurl : curl (fderiv ℝ B x) = 0) (m q v : ℝ) : BstarPar m q B v x = ‖B x‖ := by
  have hn := norm_ne_zero_iff.mpr nzero
  have mul := curl_fderiv_smul (f := fun y => ‖B y‖⁻¹) ((diff.norm ℝ nzero).inv hn) diff
  have curl_unit : curlb B x = cross (gradient (fun y => ‖B y‖⁻¹) x) (B x) := by
    change curl (fderiv ℝ (fun y => ‖B y‖⁻¹ • B y) x) = _
    simpa only [nocurl, smul_zero, zero_add] using mul
  rw [BstarPar, Bstar, inner_add_right, inner_smul_right, bhat, inner_smul_left,
    inner_smul_left, curl_unit, inner_cross_self', real_inner_self_eq_norm_sq]
  simp [hn, pow_two]

/-- The ordinary nonzero vacuum region, with all parallel velocities allowed. -/
def regular (B : Space → Space) (Ω : Set Space) : Set Space := {x | x ∈ Ω ∧ B x ≠ 0}

theorem isOpen_regular (vac : VacuumField Ω B) : IsOpen (regular B Ω) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact Filter.inter_mem (vac.isOpen.mem_nhds hx.1)
    ((vac.contDiffOn.continuousOn.continuousAt (vac.isOpen.mem_nhds hx.1)).eventually_ne hx.2)

theorem vacuum_parallel (vac : VacuumField Ω B) {x : Space} (hx : x ∈ regular B Ω)
    (m q v : ℝ) : BstarPar m q B v x = ‖B x‖ := by
  apply parallel_eq_norm hx.2
    ((vac.contDiffOn.contDiffAt (vac.isOpen.mem_nhds hx.1)).differentiableAt (by norm_num))
  simpa only [fieldCurl, Forms.curlOp_eq_curl] using vac.curl_eq_zero x hx.1

theorem velocity_smooth (vac : VacuumField Ω B) (m q μ : ℝ) :
    ContDiffOn ℝ 1 (littlejohnVelocity B m q μ) (regular B Ω ×ˢ univ) := by
  let U := regular B Ω
  have op : IsOpen U := isOpen_regular vac
  have field : ContDiffOn ℝ 2 B U := vac.contDiffOn.mono fun _ hx => hx.1
  have strength : ContDiffOn ℝ 2 (fun x => ‖B x‖) U := field.norm ℝ fun _ hx => hx.2
  have unit : ContDiffOn ℝ 2 (bhat B) U :=
    (strength.inv fun _ hx => norm_ne_zero_iff.mpr hx.2).smul field
  have rotation : ContDiffOn ℝ 1 (curlb B) U :=
    curlCLM.contDiff.comp_contDiffOn (unit.fderiv_of_isOpen op (by norm_num))
  have grad : ContDiffOn ℝ 1 (gradAbsB B) U :=
    (InnerProductSpace.toDual ℝ Space).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (strength.fderiv_of_isOpen op (by norm_num))
  intro w hw
  have here : w.1 ∈ U := hw.1
  have nh := op.mem_nhds here
  have eval {f : Space → Space} (hd : ContDiffOn ℝ 1 f U) :
      ContDiffAt ℝ 1 (fun y : Space × ℝ => f y.1) w := (hd.contDiffAt nh).comp w contDiffAt_fst
  have star : ContDiffAt ℝ 1 (fun y : Space × ℝ => Bstar m q B y.2 y.1) w :=
    (eval (field.of_le (by norm_num))).add
      (((contDiffAt_const.mul contDiffAt_snd).div_const q).smul (eval rotation))
  have norm : ContDiffAt ℝ 1 (fun y : Space × ℝ => BstarPar m q B y.2 y.1) w :=
    (eval (unit.of_le (by norm_num))).inner ℝ star
  have den : BstarPar m q B w.2 w.1 ≠ 0 := by
    rw [vacuum_parallel vac here]
    exact norm_ne_zero_iff.mpr here.2
  have crossB := contDiff_cross.contDiffAt.comp w
    ((eval (unit.of_le (by norm_num))).prodMk (eval grad))
  have scale : ContDiffAt ℝ 1 (fun _ : Space × ℝ => μ / q) w := contDiffAt_const
  have accel : ContDiffAt ℝ 1 (fun _ : Space × ℝ => -(μ / m)) w := contDiffAt_const
  exact (((norm.inv den).smul ((contDiffAt_snd.smul star).add
    (scale.smul crossB))).prodMk
      ((accel.mul (norm.inv den)).mul (star.inner ℝ (eval grad)))).contDiffWithinAt

/-- The physical initial-value problem has a solution on a positive closed time interval.
The full derivative holds at both endpoints and the trajectory stays in the regular region. -/
theorem exists_orbit (vac : VacuumField Ω B) (m q : ℝ) (birth : GCBirth)
    (hx : birth.1 ∈ regular B Ω) :
    ∃ T > 0, ∃ y, GCBirthOrbitOn B m q birth y T ∧
      ∀ t ∈ Icc 0 T, (y t).1 ∈ regular B Ω ∧ 0 < BstarPar m q B (y t).2 (y t).1 := by
  let w := (birth.1, birth.2.1)
  have op := isOpen_regular vac
  obtain ⟨ε, pos, sol⟩ := ODEGlobal.uniform_local_existence (op.prod isOpen_univ)
    (velocity_smooth vac m q birth.2.2) (isCompact_singleton (x := w))
    (singleton_subset_iff.mpr ⟨hx, mem_univ _⟩)
  obtain ⟨y, at0, ode⟩ := sol w (mem_singleton w) 0
  have h0 : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith, by linarith⟩
  have cont : ContinuousAt (fun t => (y t).1) 0 :=
    continuous_fst.continuousAt.comp (ode 0 h0).continuousAt
  obtain ⟨δ, δpos, ball⟩ := Metric.mem_nhds_iff.mp (cont.preimage_mem_nhds
    (op.mem_nhds (by rwa [at0])))
  let T := min ε δ / 2
  have half : 0 < T := half_pos (lt_min pos δpos)
  have low : T < ε := by dsimp [T]; linarith [min_le_left ε δ]
  have rad : T < δ := by dsimp [T]; linarith [min_le_right ε δ]
  refine ⟨T, half, y, ⟨at0, fun t ht => ode t ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩, ?_⟩
  intro t ht
  have keep : (y t).1 ∈ regular B Ω := ball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt rad)
  exact ⟨keep, (vacuum_parallel vac keep m q _).symm ▸ norm_pos_iff.mpr keep.2⟩

end PlasmaLean.Kinetic.VacuumLittlejohnLocal
