/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnLocal
public import PlasmaLean.Theory.Fields.LocalFlowDisplacement

/-! # Uniform short-time Littlejohn motion with the magnetic moment as a state coordinate -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.VacuumLittlejohnWindow
open Fields Contract Set Metric MeasureTheory Vacuum GCLittlejohn VacuumLittlejohnLocal
open scoped Topology

abbrev state (p : GCBirth) : Space × ℝ := (p.1, p.2.1)

/-- The fifth physical coordinate is constant along the augmented system. -/
def augmented (B : Space → Space) (m q : ℝ) (p : GCBirth) : GCBirth :=
  let v := littlejohnVelocity B m q p.2.2 (state p)
  (v.1, v.2, 0)

private theorem affine (B : Space → Space) (m q μ : ℝ) (w : Space × ℝ) :
    littlejohnVelocity B m q μ w = littlejohnVelocity B m q 0 w +
      μ • (littlejohnVelocity B m q 1 w - littlejohnVelocity B m q 0 w) := by
  apply Prod.ext
  · ext i
    simp [littlejohnVelocity, PiLp.add_apply, PiLp.smul_apply, div_eq_mul_inv]
    ring
  · simp [littlejohnVelocity, div_eq_mul_inv]
    ring

variable {B : Space → Space} {Ω : Set Space}

/-- Smoothness in magnetic moment follows from the affine dependence of the actual equation. -/
theorem augmented_smooth (vac : VacuumField Ω B) (m q : ℝ) {p : GCBirth}
    (hx : p.1 ∈ regular B Ω) : ContDiffAt ℝ 1 (augmented B m q) p := by
  have space : ContDiffAt ℝ 1 state p :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp p contDiffAt_snd)
  have μ : ContDiffAt ℝ 1 (fun b : GCBirth => b.2.2) p := contDiffAt_snd.comp p contDiffAt_snd
  have vel (k : ℝ) :
      ContDiffAt ℝ 1 (fun b : GCBirth => littlejohnVelocity B m q k (state b)) p :=
    ((velocity_smooth vac m q k).contDiffAt (((isOpen_regular vac).prod isOpen_univ).mem_nhds
      (show state p ∈ regular B Ω ×ˢ univ from ⟨hx, mem_univ _⟩))).comp p space
  have full : ContDiffAt ℝ 1 (fun b : GCBirth => littlejohnVelocity B m q b.2.2 (state b)) p :=
    ((vel 0).add (μ.smul ((vel 1).sub (vel 0)))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun b => affine B m q b.2.2 (state b))
  exact full.fst.prodMk (full.snd.prodMk contDiffAt_const)

/-- One witness on the full interval and control of *every* solution on any initial subinterval. -/
def Control (B : Space → Space) (m q T d : ℝ) (b : GCBirth) : Prop :=
  (∃ y, GCBirthOrbitOn B m q b y T) ∧ ∀ t ∈ Icc 0 T, ∀ y, GCBirthOrbitOn B m q b y t →
    B (y t).1 ≠ 0 ∧ BstarPar m q B (y t).2 (y t).1 = ‖B (y t).1‖ ∧
      0 < BstarPar m q B (y t).2 (y t).1 ∧ dist (y t).1 b.1 < d

theorem Control.mono {m q T s d : ℝ} {b : GCBirth} (h : Control B m q T d b) (le : s ≤ T) :
    Control B m q s d b := by
  obtain ⟨⟨y, at0, ode⟩, all⟩ := h
  exact ⟨⟨y, at0, fun t ht => ode t (Icc_subset_Icc_right le ht)⟩,
    fun t ht => all t (Icc_subset_Icc_right le ht)⟩

/-- The same position cap bounds radial excursion measured from any chosen axis set. -/
theorem Control.radial {m q T d : ℝ} {b : GCBirth} (h : Control B m q T d b)
    (axis : Set Space) {t : ℝ} (ht : t ∈ Icc 0 T) {y : ℝ → Space × ℝ}
    (orbit : GCBirthOrbitOn B m q b y t) : |infDist (y t).1 axis - infDist b.1 axis| < d := by
  have limit : |infDist (y t).1 axis - infDist b.1 axis| ≤ dist (y t).1 b.1 := by
    simpa [Real.dist_eq] using (lipschitz_infDist_pt axis).dist_le_mul (y t).1 b.1
  exact limit.trans_lt (h.2 t ht y orbit).2.2.2

private def moment : GCBirth →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Space (ℝ × ℝ))

private def projection : GCBirth →L[ℝ] Space × ℝ :=
  (ContinuousLinearMap.fst ℝ Space (ℝ × ℝ)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ Space (ℝ × ℝ)))

/-- Around any regular seed, a single positive duration enforces any prescribed positive
position cap for every nearby birth and every partial solution of the contracted equation. -/
theorem exists_control (vac : VacuumField Ω B) (m q : ℝ) {p : GCBirth} {d : ℝ}
    (hx : p.1 ∈ regular B Ω) (hd : 0 < d) :
    ∃ W : Set GCBirth, IsOpen W ∧ p ∈ W ∧ ∃ T > 0, ∀ b ∈ W, Control B m q T d b := by
  let U : Set GCBirth := (fun b : GCBirth => b.1) ⁻¹' regular B Ω
  have op : IsOpen U := (isOpen_regular vac).preimage continuous_fst
  obtain ⟨W, openW, seed, _, T, Tpos, flow⟩ :=
    LocalFlowDisplacement.common_window (augmented_smooth vac m q hx) op hx hd
  refine ⟨W, openW, seed, T, Tpos, ?_⟩
  intro b hb
  obtain ⟨z, start, during⟩ := flow b hb
  have invariant (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivAt (fun t => (z t).2.2) 0 s :=
    moment.hasFDerivAt.comp_hasDerivAt s (during s hs).1
  have fixed : ∀ t ∈ Icc 0 T, (z t).2.2 = b.2.2 := eq_of_has_deriv_right_eq
    (fun s hs => (invariant s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s _ => (hasDerivAt_const s b.2.2).hasDerivWithinAt)
    (fun s hs => (invariant s hs).continuousAt.continuousWithinAt) continuousOn_const
    (by rw [start])
  have original : GCBirthOrbitOn B m q b (fun t => state (z t)) T := by
    refine ⟨congrArg state start, fun s hs => ?_⟩
    have dz := projection.hasFDerivAt.comp_hasDerivAt s (during s hs).1
    change HasDerivAt (fun t => state (z t))
      (littlejohnVelocity B m q (z s).2.2 (state (z s))) s at dz
    rwa [fixed s hs] at dz
  refine ⟨⟨_, original⟩, ?_⟩
  intro t ht y other
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have positive (s : ℝ) (hs : s ∈ Icc 0 T) : (z s).1 ∈ regular B Ω := (during s hs).2.1
  have agree := LocalFlowDisplacement.agree_from_start other.2 (fun s hs => original.2 s (sub hs))
    (fun s hs => (velocity_smooth vac m q b.2.2).contDiffAt
      (((isOpen_regular vac).prod isOpen_univ).mem_nhds
        (show state (z s) ∈ regular B Ω ×ˢ univ from ⟨positive s (sub hs), mem_univ _⟩)))
    (other.1.trans original.1.symm)
  rw [agree (right_mem_Icc.mpr ht.1)]
  have regularNow := positive t ht
  have par := vacuum_parallel vac regularNow m q (z t).2.1
  have limit : dist (z t).1 b.1 ≤ dist (z t) b := le_max_left _ _
  exact ⟨regularNow.2, par, par.symm ▸ norm_pos_iff.mpr regularNow.2,
    limit.trans_lt (during t ht).2.2⟩

/-- Any controlled nonempty open set inside a measurable finite trapped reference gives
the contracted band with its actual mass ratio. -/
theorem guidingCentreBand {m q T d : ℝ} {axis : Set Space} {W S : Set GCBirth}
    {energies pitches : Set ℝ} (ν : Measure GCBirth)
    [Measure.IsOpenPosMeasure ν] (hm : 0 < m) (hq : q ≠ 0)
    (haxis : axis.Nonempty) (compact : IsCompact axis) (hT : 0 < T) (hd : 0 < d)
    (op : IsOpen W) (occurs : W.Nonempty) (inside : W ⊆ trappedReference B m S energies pitches)
    (meas : MeasurableSet (trappedReference B m S energies pitches))
    (finite : ν (trappedReference B m S energies pitches) ≠ ⊤)
    (control : ∀ b ∈ W, Control B m q T d b) :
    GuidingCentreBand B m q axis ν S W energies pitches
      (ν.real W / ν.real (trappedReference B m S energies pitches)) d T := by
  have covered : 0 < ν.real W := ENNReal.toReal_pos (op.measure_pos ν occurs).ne'
    (measure_ne_top_of_subset inside finite)
  have less := measureReal_mono (μ := ν) inside finite
  have positive := covered.trans_le less
  refine ⟨hm, hq, haxis, compact, hT, hd.le,
    ⟨meas, op.measurableSet, inside, finite, positive, div_pos covered positive,
      (div_le_one positive).mpr less, (div_mul_cancel₀ _ positive.ne').le⟩,
    fun b hb => (control b hb).1, ?_⟩
  intro b hb t ht y orbit
  have safe := (control b hb).2 t ht y orbit
  exact ⟨safe.1, safe.2.2.1.ne', ((control b hb).radial axis ht orbit).le⟩

end PlasmaLean.Kinetic.VacuumLittlejohnWindow
