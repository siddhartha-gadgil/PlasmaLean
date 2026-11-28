/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Contract.TrappedBirthBand
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PlasmaLean.Kernel.Vacuum

/-!
# The band form of clause C2 with fixed inputs

`GuidingCentreBand` takes every physical quantity as an argument, so whoever proves it may choose
them: a point-mass birth law, a one-point support, a tiny horizon, a huge excursion or a large
ball as the "axis" (audit of 25 November 2026, AW-H3, AW-M3, AW-M4). This module separates the
**specification** of the band form, fixed before any proof, from the **claim** about a field.

* `BandSpec` collects the inputs: species, birth law, support, energy and pitch windows, a closed
  reference axis, the required horizon, the allowed radial excursion and the required fraction.
  All numbers stay symbolic.
* `BandSpec.Admissible` is a property of the specification alone: positive horizon and fraction
  at most one, a birth law absolutely continuous with respect to volume, a support with nonempty
  interior, an axis that is a closed `C¹` curve.
* `MeetsBand s B` is the claim: on some open region containing every partial orbit, `B` is `C²`
  and divergence-free, and `GuidingCentreBand` holds with the axis, horizon, excursion and
  birth data of `s` and a covered fraction at least `s.minFraction`.
* `BandContract s B` is the band form of C2: `s.Admissible ∧ MeetsBand s B`.

The prover chooses only the region, the covered births and the attained fraction. A family of
statements of the form "for each excursion there is some positive horizon" does not give
`BandContract` for a specification whose horizon is fixed in advance.

**Contract status (user decision, 29 November 2026).** `BandContract` is adopted as the band form
of clause C2; `GuidingCentreBand` alone is a lemma-level predicate. The definition does not
constrain how the support is described, how long the horizon is or how large the excursion is.
An instance therefore counts as progress on C2 only if its specification states the horizon
against the bounce time of the population and the excursion against the orbit width, and gives
the support without reference to the trapped population it is compared with. This acceptance
rule is applied at review, not in Lean (note N-213). The instance
`DommaschkWideTubeRows000Band.band_contract` (note N-216) is formal and does not meet it.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory PlasmaLean.Fields PlasmaLean.Vacuum PlasmaLean.Kinetic.GCLittlejohn

namespace PlasmaLean.Contract

/-- Inputs of the band form of C2, fixed before any proof. Units as in `GuidingCentreBand`:
SI for the species, energy in joules, pitch `μ/E` in inverse tesla, horizon in seconds,
excursion in metres. -/
structure BandSpec where
  /-- Mass of the species. -/
  m : ℝ
  /-- Charge of the species. -/
  q : ℝ
  /-- Birth law on position, parallel velocity and magnetic moment. -/
  ν : Measure GCBirth
  /-- Birth region in phase space. -/
  support : Set GCBirth
  /-- Energy window. -/
  energy : Set ℝ
  /-- Pitch window. -/
  pitch : Set ℝ
  /-- Reference axis, a closed curve of period one. -/
  axis : ℝ → Space
  /-- Required confinement time. -/
  horizon : ℝ
  /-- Allowed change of distance to the axis. -/
  excursion : ℝ
  /-- Required covered fraction of the trapped reference population. -/
  minFraction : ℝ

namespace BandSpec

/-- Conditions on the specification alone. The birth law must not concentrate on a null set
(so a single orbit is not a population), the support must have interior, and the axis must be
a closed `C¹` curve (not an arbitrary compact set). -/
structure Admissible (s : BandSpec) : Prop where
  mass_pos : 0 < s.m
  charge_ne : s.q ≠ 0
  horizon_pos : 0 < s.horizon
  excursion_nonneg : 0 ≤ s.excursion
  minFraction_pos : 0 < s.minFraction
  minFraction_le_one : s.minFraction ≤ 1
  birth_ac : s.ν ≪ volume
  support_interior : (interior s.support).Nonempty
  axis_smooth : ContDiff ℝ 1 s.axis
  axis_closed : Function.Periodic s.axis 1

/-- The axis of an admissible specification is a nonempty compact set. -/
theorem Admissible.axis_compact {s : BandSpec} (h : s.Admissible) : IsCompact (range s.axis) :=
  h.axis_closed.compact_of_continuous one_ne_zero h.axis_smooth.continuous

theorem Admissible.axis_nonempty {s : BandSpec} (_h : s.Admissible) :
    (range s.axis).Nonempty := range_nonempty _

/-- The trapped reference population of the specification in the field `B`. -/
def reference (s : BandSpec) (B : Space → Space) : Set GCBirth :=
  trappedReference B s.m s.support s.energy s.pitch

end BandSpec

/-- The claim of the band form for the field `B`. The prover chooses only an open region, the
covered births and the attained fraction; the field must be a `C²` divergence-free field on the
region, and every partial orbit from a covered birth stays in it. -/
def MeetsBand (s : BandSpec) (B : Space → Space) : Prop :=
  ∃ (Ω : Set Space) (covered : Set GCBirth) (fraction : ℝ),
    IsOpen Ω ∧ ContDiffOn ℝ 2 B Ω ∧ (∀ x ∈ Ω, fieldDiv B x = 0) ∧
    s.minFraction ≤ fraction ∧
    GuidingCentreBand B s.m s.q (range s.axis) s.ν s.support covered s.energy s.pitch fraction
      s.excursion s.horizon ∧
    ∀ b ∈ covered, ∀ t ∈ Icc 0 s.horizon, ∀ z, GCBirthOrbitOn B s.m s.q b z t → (z t).1 ∈ Ω

/-- The band form of clause C2 for a fixed specification. -/
def BandContract (s : BandSpec) (B : Space → Space) : Prop := s.Admissible ∧ MeetsBand s B

variable {s : BandSpec} {B : Space → Space}

/-- Losses with an excursion beyond the specified tolerance before the specified horizon have
measure at most `1 - minFraction` times the trapped reference mass. -/
theorem MeetsBand.radial_loss_le (h : MeetsBand s B) :
    s.ν.real {b ∈ s.reference B | ∃ t ∈ Icc 0 s.horizon, ∃ z, GCBirthOrbitOn B s.m s.q b z t ∧
      s.excursion < |Metric.infDist (z t).1 (range s.axis) - Metric.infDist b.1 (range s.axis)|}
      ≤ (1 - s.minFraction) * s.ν.real (s.reference B) := by
  obtain ⟨_, _, f, _, _, _, hf, hband, _⟩ := h
  have hle := hband.radial_loss_le
  have hnn : 0 ≤ s.ν.real (s.reference B) := measureReal_nonneg
  exact hle.trans (mul_le_mul_of_nonneg_right (by linarith) hnn)

/-- A covered trapped birth exists, and the field is divergence-free on an open neighbourhood
of its position. -/
theorem MeetsBand.exists_birth (h : MeetsBand s B) :
    ∃ b ∈ s.reference B, ∃ Ω : Set Space, IsOpen Ω ∧ b.1 ∈ Ω ∧ ∀ x ∈ Ω, fieldDiv B x = 0 := by
  obtain ⟨Ω, covered, f, hΩ, _, hdiv, _, hband, hstay⟩ := h
  have hpos := hband.coverage.covered_pos
  obtain ⟨b, hb⟩ : covered.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    simp [hne] at hpos
  obtain ⟨z, hz⟩ := hband.exists_orbit b hb
  have h0 : GCBirthOrbitOn B s.m s.q b z 0 :=
    ⟨hz.1, fun t ht => hz.2 t ⟨ht.1, ht.2.trans hband.horizon_pos.le⟩⟩
  have hmem := hstay b hb 0 ⟨le_rfl, hband.horizon_pos.le⟩ z h0
  rw [hz.1] at hmem
  exact ⟨b, hband.coverage.subset hb, Ω, hΩ, hmem, hdiv⟩

/-- A shorter horizon is easier: restricting every orbit to a shorter interval keeps the
claim. -/
theorem MeetsBand.mono_horizon (h : MeetsBand s B) {T : ℝ} (hT : 0 < T)
    (hle : T ≤ s.horizon) : MeetsBand { s with horizon := T } B := by
  obtain ⟨Ω, covered, f, hΩ, hreg, hdiv, hf, hband, hstay⟩ := h
  refine ⟨Ω, covered, f, hΩ, hreg, hdiv, hf, ?_, ?_⟩
  · refine ⟨hband.mass_pos, hband.charge_ne, hband.axis_nonempty, hband.axis_compact, hT,
      hband.excursion_nonneg, hband.coverage, ?_, ?_⟩
    · intro b hb
      obtain ⟨z, hz⟩ := hband.exists_orbit b hb
      exact ⟨z, hz.1, fun t ht => hz.2 t ⟨ht.1, ht.2.trans hle⟩⟩
    · intro b hb t ht z hz
      exact hband.controls b hb t ⟨ht.1, ht.2.trans hle⟩ z hz
  · intro b hb t ht z hz
    exact hstay b hb t ⟨ht.1, ht.2.trans hle⟩ z hz

/-- A larger excursion tolerance or a smaller required fraction is easier. -/
theorem MeetsBand.mono_tolerance (h : MeetsBand s B) {d f₀ : ℝ} (hd : s.excursion ≤ d)
    (hf₀ : f₀ ≤ s.minFraction) : MeetsBand { s with excursion := d, minFraction := f₀ } B := by
  obtain ⟨Ω, covered, f, hΩ, hreg, hdiv, hf, hband, hstay⟩ := h
  refine ⟨Ω, covered, f, hΩ, hreg, hdiv, hf₀.trans hf, ?_, hstay⟩
  refine ⟨hband.mass_pos, hband.charge_ne, hband.axis_nonempty, hband.axis_compact,
    hband.horizon_pos, hband.excursion_nonneg.trans hd, hband.coverage, hband.exists_orbit, ?_⟩
  intro b hb t ht z hz
  obtain ⟨h1, h2, h3⟩ := hband.controls b hb t ht z hz
  exact ⟨h1, h2, h3.trans hd⟩

/-- A uniform field never meets the band form: it has no trapped births. -/
theorem not_meetsBand_const (F : Space) : ¬ MeetsBand s (fun _ => F) := by
  rintro ⟨_, _, _, _, _, _, _, hband, _⟩
  exact not_guidingCentreBand_const F hband

end PlasmaLean.Contract
