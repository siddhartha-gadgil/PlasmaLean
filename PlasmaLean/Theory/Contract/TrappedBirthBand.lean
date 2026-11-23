/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.GuidingCentreLittlejohn
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# A finite-time radial band for trapped guiding centres

All physical inputs are arguments. The model is static, collisionless Littlejohn with zero
electric field. A regular unperturbed mirror well defines eligibility at birth. Positive
coverage refers to a supplied birth measure. The excursion is measured in configuration space
as change of distance to a supplied reference axis. The equations must have a solution through
the horizon from every covered birth, and the estimate applies also to every partial solution.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PlasmaLean.Fields PlasmaLean.Kinetic.GCLittlejohn
open scoped RealInnerProductSpace

namespace PlasmaLean.Contract

/-- A positive fraction of a specified finite reference population. -/
structure BirthCoverage {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (reference covered : Set X) (fraction : ℝ) : Prop where
  reference_measurable : MeasurableSet reference
  covered_measurable : MeasurableSet covered
  subset : covered ⊆ reference
  finite : ν reference ≠ ⊤
  reference_pos : 0 < ν.real reference
  fraction_pos : 0 < fraction
  fraction_le_one : fraction ≤ 1
  mass_le : fraction * ν.real reference ≤ ν.real covered

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {reference covered : Set X}
  {fraction : ℝ}

/-- The covered population has positive mass, even when the reference measure is unnormalised. -/
theorem BirthCoverage.covered_pos (h : BirthCoverage ν reference covered fraction) :
    0 < ν.real covered := (mul_pos h.fraction_pos h.reference_pos).trans_le h.mass_le

/-- Any losses disjoint from the covered births consume at most the complementary fraction
of the reference measure. The measure may count particles or weight them by initial energy. -/
theorem BirthCoverage.loss_le (h : BirthCoverage ν reference covered fraction) {lost : Set X}
    (href : lost ⊆ reference) (hsafe : Disjoint lost covered) :
    ν.real lost ≤ (1 - fraction) * ν.real reference := by
  have incl : lost ⊆ reference \ covered := fun x hx =>
    ⟨href hx, fun hcov => Set.disjoint_left.mp hsafe hx hcov⟩
  have hsubset := measureReal_mono (μ := ν) incl (measure_ne_top_of_subset sdiff_subset h.finite)
  rw [measureReal_sdiff h.subset h.covered_measurable h.finite] at hsubset
  linarith [h.mass_le]

/-- Counting the entire finite positive reference population gives coverage one. -/
theorem BirthCoverage.full (hset : MeasurableSet reference) (hfin : ν reference ≠ ⊤)
    (hpos : 0 < ν.real reference) : BirthCoverage ν reference reference 1 :=
  ⟨hset, hset, Subset.rfl, hfin, hpos, zero_lt_one, le_rfl, by simp⟩

/-- A positive target fraction excludes an empty covered population. -/
theorem not_birthCoverage_empty : ¬ BirthCoverage ν reference ∅ fraction := by
  intro h
  simpa using h.covered_pos

/-- At a regular mirror birth, the magnetic strength along the arclength field line equals
the mirror height at two simple turning points and stays strictly below it between them.
Time zero may be at either turning point. The parameter here is arclength in metres. -/
def RegularMirrorBirth (B : Space → Space) (x : Space) (height : ℝ) : Prop :=
  ∃ (line : ℝ → Space) (a b : ℝ), a < b ∧ 0 ∈ Icc a b ∧ line 0 = x ∧
    (∀ s ∈ Icc a b, B (line s) ≠ 0 ∧ HasDerivAt line (bhat B (line s)) s) ∧
    ‖B (line a)‖ = height ∧ ‖B (line b)‖ = height ∧
    (∀ s ∈ Ioo a b, ‖B (line s)‖ < height) ∧
    (deriv (fun s => ‖B (line s)‖) a < 0 ∧ 0 < deriv (fun s => ‖B (line s)‖) b)

/-- A uniform magnetic field cannot support even one such trapped birth. -/
theorem not_regularMirrorBirth_const (F x : Space) (height : ℝ) :
    ¬ RegularMirrorBirth (fun _ => F) x height := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  simp at h

/-- At birth the coordinates are position, parallel velocity, and magnetic moment. -/
abbrev GCBirth := Space × ℝ × ℝ

/-- Predeclared thermal reference population for one species. Energy is in joules, magnetic
moment in joules per tesla and pitch μ/E in inverse tesla. -/
def trappedReference (B : Space → Space) (m : ℝ) (support : Set GCBirth)
    (energy pitch : Set ℝ) : Set GCBirth := {b | b ∈ support ∧
    let E := hamiltonian m b.2.2 B b.1 b.2.1
    0 < b.2.2 ∧ 0 < E ∧ E ∈ energy ∧ b.2.2 / E ∈ pitch ∧ RegularMirrorBirth B b.1 (E / b.2.2)}

/-- The Littlejohn right-hand side for position and parallel velocity at a fixed moment. -/
def littlejohnVelocity (B : Space → Space) (m q μ : ℝ) (w : Space × ℝ) : Space × ℝ :=
  ((BstarPar m q B w.2 w.1)⁻¹ •
    (w.2 • Bstar m q B w.2 w.1 + (μ / q) • cross (bhat B w.1) (gradAbsB B w.1)),
    -(μ / m) * (BstarPar m q B w.2 w.1)⁻¹ * ⟪Bstar m q B w.2 w.1, gradAbsB B w.1⟫)

/-- Finite-time Littlejohn solution with initial position, velocity and moment fixed by the
birth. Regularity of the physical denominators is a separate acceptance obligation. -/
def GCBirthOrbitOn (B : Space → Space) (m q : ℝ) (b : GCBirth) (z : ℝ → Space × ℝ)
    (t : ℝ) : Prop := z 0 = (b.1, b.2.1) ∧ ∀ s ∈ Icc 0 t,
      HasDerivAt z (littlejohnVelocity B m q b.2.2 (z s)) s

/-- The interval equation agrees with the existing all-time Littlejohn model. -/
theorem gcBirthOrbitOn_of_littlejohn {B : Space → Space} {m q μ : ℝ}
    {x : ℝ → Space} {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B x v) (t : ℝ) :
    GCBirthOrbitOn B m q (x 0, v 0, μ) (fun s => (x s, v s)) t :=
  ⟨rfl, fun s _ => (h.hX s).prodMk (h.hv s)⟩

/-- Field-level band form of C2 for a specified single-species Littlejohn population.
The axis and birth distribution come from the application. The regularity and excursion
clauses quantify over partial trajectories also, so a trajectory that hits a singularity
early cannot be discarded by selecting a better solution. -/
structure GuidingCentreBand (B : Space → Space) (m q : ℝ) (axis : Set Space)
    (ν : Measure GCBirth) (support covered : Set GCBirth) (energy pitch : Set ℝ)
    (fraction excursion horizon : ℝ) : Prop where
  mass_pos : 0 < m
  charge_ne : q ≠ 0
  axis_nonempty : axis.Nonempty
  axis_compact : IsCompact axis
  horizon_pos : 0 < horizon
  excursion_nonneg : 0 ≤ excursion
  coverage : BirthCoverage ν (trappedReference B m support energy pitch) covered fraction
  exists_orbit : ∀ b ∈ covered, ∃ z, GCBirthOrbitOn B m q b z horizon
  controls : ∀ b ∈ covered, ∀ t ∈ Icc 0 horizon, ∀ z, GCBirthOrbitOn B m q b z t →
    B (z t).1 ≠ 0 ∧ BstarPar m q B (z t).2 (z t).1 ≠ 0 ∧
      |Metric.infDist (z t).1 axis - Metric.infDist b.1 axis| ≤ excursion

variable {B : Space → Space} {m q : ℝ} {axis : Set Space} {births : Measure GCBirth}
    {support band : Set GCBirth} {energy pitch : Set ℝ} {f d T : ℝ}

/-- Births with a radial excursion exceeding the tolerance along even one partial trajectory
before the horizon have measure at most (1−f) times the trapped reference mass. -/
theorem GuidingCentreBand.radial_loss_le
    (h : GuidingCentreBand B m q axis births support band energy pitch f d T) :
    births.real {b ∈ trappedReference B m support energy pitch | ∃ t ∈ Icc 0 T,
      ∃ z, GCBirthOrbitOn B m q b z t ∧ d < |Metric.infDist (z t).1 axis - Metric.infDist b.1 axis|}
      ≤ (1 - f) * births.real (trappedReference B m support energy pitch) := by
  apply h.coverage.loss_le
  · intro b hb
    exact hb.1
  apply Set.disjoint_left.mpr
  rintro b ⟨_, t, ht, z, hz, hfail⟩ hb
  exact hfail.not_ge (h.controls b hb t ht z hz).2.2

/-- Positive trapped coverage rules out the vacuous uniform-field witness. -/
theorem not_guidingCentreBand_const (F : Space) :
    ¬ GuidingCentreBand (fun _ => F) m q axis births support band energy pitch f d T := by
  intro h
  have he : trappedReference (fun _ => F) m support energy pitch = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact not_regularMirrorBirth_const F b.1 _ hb.2.2.2.2.2
  have hpos := h.coverage.reference_pos
  simp [he] at hpos

/-- Comparison with a reduced position in the same physical length and time units. Endpoint
position errors enter additively. An exact initial match removes the initial error term. -/
theorem radial_excursion_of_reduction {axis : Set Space} {x₀ x y₀ y : Space} {e₀ e d : ℝ}
    (h₀ : dist x₀ y₀ ≤ e₀) (ht : dist x y ≤ e)
    (hy : |Metric.infDist y axis - Metric.infDist y₀ axis| ≤ d) :
    |Metric.infDist x axis - Metric.infDist x₀ axis| ≤ d + e₀ + e := by
  have lip (a b : Space) : |Metric.infDist a axis - Metric.infDist b axis| ≤ dist a b := by
    simpa [Real.dist_eq] using (Metric.lipschitz_infDist_pt axis).dist_le_mul a b
  have h₁ := abs_le.mp ((lip x y).trans ht)
  have h₂ := abs_le.mp ((lip x₀ y₀).trans h₀)
  obtain ⟨h₃, h₄⟩ := abs_le.mp hy
  exact abs_le.mpr ⟨by linarith [h₁.1, h₂.2], by linarith [h₁.2, h₂.1]⟩

end PlasmaLean.Contract
