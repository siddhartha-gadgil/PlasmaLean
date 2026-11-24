/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.ClosedIntervalODEUniqueness
public import PlasmaLean.Design.DommaschkSignedTraceDomain
public import PlasmaLean.Design.DommaschkSignedTraceDenominator

/-! # The interpolated off-section birth lies on the same signed physical field line -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkSignedBirthApproach
open Set Filter Topology DommaschkBounceField DommaschkKam DommaschkKam.DkPoly
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkMirrorLaunch
open DommaschkSignedTraceDomain
set_option maxRecDepth 8192

private theorem smooth_polynomial (phase sign : ℝ) (p : SP) :
    ContDiff ℝ 1 (clockPoly phase sign p) := by
  induction p with
  | nil =>
    exact (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × DommaschkBounceField.State => (0 : ℝ)))
  | cons m p ih =>
    change ContDiff ℝ 1 (fun a : ℝ × DommaschkBounceField.State =>
      (m.q : ℝ) * ((a.2 0 - dkR0)^m.a * (a.2 1)^m.b *
        Real.cos (2 * (phase + sign * a.1))^m.c * Real.sin (2 * (phase + sign * a.1))^m.d) +
        clockPoly phase sign p a)
    apply ContDiff.add _ ih
    fun_prop

/-- The true clock-dependent spatial velocity is jointly C¹ locally at every regular
point. Only positivity of the cylindrical radius and a nonzero denominator are needed. -/
theorem physical_smooth (phase sign : ℝ) (q : ℝ × DommaschkBounceField.State)
    (hR : 0 < q.2 0) (hD : clockPoly phase sign dD q ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × DommaschkBounceField.State =>
      physicalFlow phase sign p.1 p.2) q := by
  have den := smooth_polynomial phase sign dD
  have ratio : ContDiffAt ℝ 1 (fun p : ℝ × DommaschkBounceField.State =>
      ratioFlow phase sign p.1 p.2) q := by
    apply contDiffAt_pi.mpr
    intro i
    have term (p : SP) : ContDiffAt ℝ 1 (fun b : ℝ × DommaschkBounceField.State =>
        sign * (clockPoly phase sign p b / clockPoly phase sign dD b)) q :=
      contDiffAt_const.mul ((smooth_polynomial phase sign p).contDiffAt.div den.contDiffAt hD)
    fin_cases i
    · exact term dnR
    · exact term dnZ
  apply ratio.congr_of_eventuallyEq
  have rad : Continuous (fun a : ℝ × DommaschkBounceField.State => a.2 0) := by fun_prop
  filter_upwards [rad.continuousAt.eventually_const_lt hR,
    den.continuous.continuousAt.eventually_ne hD] with p hr hd
  exact (ratio_eq_physical phase sign p.1 p.2 hr hd).symm

private theorem clock_subset {φ σ T : ℝ} (unit : |σ| = 1) (section_time : φ + σ * |φ| = 0)
    (room : |φ| ≤ T) : MapsTo (fun s => φ + σ * s) (Icc 0 |φ|) (Icc (-T) T) := by
  intro s hs
  have e : φ + σ * s = σ * (s - |φ|) := by nlinarith only [section_time]
  have m : |φ + σ * s| ≤ T := by
    rw [e, abs_mul, unit, one_mul, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1]
  exact abs_le.mp m

/-- Identification at every elapsed approach time, for the given solution and given
signed trajectory. It also applies when the segment degenerates at phase zero. -/
theorem along {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {φ σ : ℝ} {approach : ℝ → DommaschkBounceField.State} {y : ℝ → Plane}
    (path : Path n fs bs fr br (coordinates.symm (approach |φ|)) y)
    (unit : |σ| = 1) (section_time : φ + σ * |φ| = 0) (room : |φ| ≤ n / 64)
    (ode : ∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach
      (physicalFlow φ σ t (approach t)) (Icc 0 |φ|) t)
    (regular : ∀ t ∈ Icc (-(n : ℝ) / 64) (n / 64),
      0 < y t 0 ∧ atPoint dD (y t 0) t (y t 1) ≠ 0) :
    EqOn approach (fun t => coordinates (y (φ + σ * t))) (Icc 0 |φ|) := by
  let clock := fun t : ℝ => φ + σ * t
  have subset : MapsTo clock (Icc 0 |φ|) (Icc (-(n : ℝ) / 64) (n / 64)) := by
    simpa only [neg_div] using clock_subset unit section_time room
  have true_ode (s : ℝ) (hs : s ∈ Icc 0 |φ|) := path.ode (clock s) (subset hs)
  apply Fields.ode_eqOn_of_terminal ode
  · intro s hs
    have d := coordinates.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
      (clock s) (true_ode s hs)
    have d' : HasDerivWithinAt (fun t => coordinates (y t))
        (physicalFlow 0 1 (clock s) (coordinates (y (clock s))))
        (Icc (-(n : ℝ) / 64) (n / 64)) (clock s) :=
      d.congr_deriv (coordinates.apply_symm_apply _)
    have ds : HasDerivAt clock σ s := by
      simpa only [clock, id_eq, mul_one] using ((hasDerivAt_id s).const_mul σ).const_add φ
    apply (d'.scomp s ds.hasDerivWithinAt subset).congr_deriv
    ext i
    fin_cases i <;> simp [physicalFlow, clock]
  · intro s hs
    obtain ⟨hr, hd⟩ := regular (clock s) (subset hs)
    exact physical_smooth φ σ _ hr hd
  · rw [section_time, path.starts, coordinates.apply_symm_apply]

/-- The same physical signed trajectory passes through the actual interpolated birth
at its original geometric toroidal angle. All regularity comes from the two archives. -/
theorem birth_position {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {uC zC uA zA : Theory.KAM.FA} {φ σ : ℝ}
    {approach : ℝ → DommaschkBounceField.State} {y : ℝ → Plane}
    (path : Path n fs bs fr br (coordinates.symm (approach |φ|)) y)
    (unit : |σ| = 1) (section_time : φ + σ * |φ| = 0) (small : |φ| ≤ 1 / 2 ^ 19)
    (start : approach 0 = birth uC zC uA zA (47 / 100) φ)
    (ode : ∀ t ∈ Icc 0 |φ|, HasDerivWithinAt approach
      (physicalFlow φ σ t (approach t)) (Icc 0 |φ|) t)
    (hn : 0 < n) (hf : fr = DommaschkPositionFramesFwd.blocks.flatten.take n)
    (hb : br = DommaschkPositionFramesBack.blocks.flatten.take n)
    (lf : fr.length = n) (lb : br.length = n) :
    y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) := by
  have one : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e := along path unit section_time (by linarith) ode (by
    intro t ht
    obtain ⟨r,z⟩ := DommaschkSignedTraceDomain.on_path path hn hf hb lf lb t ht
    have d := DommaschkSignedTraceDenominator.regular t r z
    exact ⟨by linarith [r.1], ne_of_gt (by linarith)⟩)
  have at_zero := e (show (0 : ℝ) ∈ Icc 0 |φ| from ⟨le_rfl, abs_nonneg _⟩)
  rw [start] at at_zero
  apply coordinates.injective
  simpa only [mul_zero, add_zero, ContinuousLinearEquiv.apply_symm_apply] using at_zero.symm

open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2

/-- A property of an actual signed field line through every admissible angle of the
same pair of nested Q-16 tori. The birth point is evaluated on that signed field line. -/
def ThroughBirth (P : ℝ → (ℝ → Plane) → Prop) : Prop :=
  ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
    IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
      (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
    DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
    ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → ∃ y : ℝ → Plane,
      y φ = coordinates.symm (birth uC zC uA zA (47 / 100) φ) ∧ P φ y

/-- Attach a birth-angle observable to the very same signed trajectory and Q-16 tori
as the section observable. The implication may depend on the admitted physical angle. -/
theorem from_birthWith {n : ℕ} {fs bs : Certificates.PositionFrameSlabs.State} {fr br : List Step}
    {A : Plane → (ℝ → Plane) → Prop} {P : ℝ → (ℝ → Plane) → Prop}
    (births : BirthWith (fun x => ∃ y, Path n fs bs fr br x y ∧ A x y))
    (hn : 0 < n) (hf : fr = DommaschkPositionFramesFwd.blocks.flatten.take n)
    (hb : br = DommaschkPositionFramesBack.blocks.flatten.take n)
    (lf : fr.length = n) (lb : br.length = n)
    (at_angle : ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 →
      ∀ x y, Path n fs bs fr br x y → A x y → P φ y) : ThroughBirth P := by
  obtain ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,each⟩ := births
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,fun φ small => ?_⟩
  obtain ⟨σ,approach,unit,section_time,start,ode,y,path,prop⟩ := each φ small
  exact ⟨y,birth_position path unit section_time small start ode hn hf hb lf lb,
    at_angle φ small _ y path prop⟩

end PlasmaLean.Design.DommaschkSignedBirthApproach
