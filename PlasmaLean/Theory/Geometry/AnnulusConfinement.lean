/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AnnulusFibreFlux
public import PlasmaLean.Theory.Geometry.AveragedConfinement

/-!
# Second-order confinement on an annulus of periodic orbits

Angles and phase are in turns, and the physical angular velocity in the fast fibre
is the inverse period. The stream and corrector are constructed from the volume equations.
All bounds for a proposed exit use the trajectory only through that exit.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AnnulusFibreFlux.VolumeChart

open Set AnnulusStream PeriodicOrbit AveragedConfinement
open scoped ContDiff

variable {lo hi : ℝ} (C : VolumeChart lo hi)

/-- Phase coordinates over the open radial collar. -/
abbrev PhaseCollar (lo hi : ℝ) := collar lo hi ×ˢ (univ : Set ℝ)

/-- Physical fast velocity, in turns per unit time, on the lifted circle. -/
def fast (z : Base × ℝ) : Base × ℝ := (0, (C.T z.1)⁻¹)

/-- The constructed scalars and their directional derivatives. Both scalars descend
under a full base-angle turn and a full fibre turn. -/
structure CorrectedStream where
  /-- The normalized base stream. -/
  label : Base → ℝ
  /-- The zero-mean phase correction, measured in label units per unit perturbation. -/
  correction : Base × ℝ → ℝ
  smooth_label : ContDiffOn ℝ ∞ label (collar lo hi)
  smooth_correction : ContDiffOn ℝ ∞ correction (PhaseCollar lo hi)
  label_periodic : ∀ r ∈ Ioo lo hi, Function.Periodic (fun θ ↦ label (θ, r)) 1
  angle_turn : ∀ z ∈ PhaseCollar lo hi, correction (z + ((1, 0), 0)) = correction z
  phase_turn : ∀ p ∈ collar lo hi, Function.Periodic (fun s ↦ correction (p, s)) 1
  mean_zero : ∀ p ∈ collar lo hi, Lifted.mean correction p = 0
  lower : ∀ θ, label (θ, 0) = 0
  upper : ∀ θ, label (θ, 1) = 1
  regular : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → label p ∈ Icc (0 : ℝ) 1 ∧ fderiv ℝ label p ≠ 0
  cancels : ∀ z ∈ PhaseCollar lo hi,
    fderiv ℝ correction z (C.fast z) = -fderiv ℝ label z.1 (C.Y z).1

/-- Translation by a deck period preserves the derivative on the open collar. -/
theorem translated_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set V} (hU : IsOpen U) {F : V → ℝ} {v p : V} (hp : p ∈ U)
    (heq : ∀ x ∈ U, F (x + v) = F x) :
    fderiv ℝ F (p + v) = fderiv ℝ F p := by
  have h : (fun x ↦ F (x + v)) =ᶠ[nhds p] F :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hp, heq⟩
  rw [← fderiv_comp_add_right]
  exact h.fderiv_eq

/-- Construct both scalars from volume preservation, nonsingularity and averaged
boundary tangency. All phase and angular derivatives are ordinary derivatives on the cover. -/
theorem exists_correctedStream (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (C.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (C.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → C.meanField p ≠ 0) :
    Nonempty C.CorrectedStream := by
  obtain ⟨ψ, hψ, hper, h0, h1, hrange, hW⟩ := C.exists_normalized_invariant hlo hhi h₀ h₁ hn
  let f := C.labelDrift ψ
  let g := Lifted.corrector C.T f
  have hU : IsOpen (collar lo hi) := isOpen_collar
  have hf : ContDiffOn ℝ ∞ f (PhaseCollar lo hi) := C.labelDrift_smooth hψ
  have hg : ContDiffOn ℝ ∞ g (PhaseCollar lo hi) := Lifted.contDiffOn_corrector hU C.T_smooth hf
  have hfc (p : Base) (hp : p ∈ collar lo hi) : Continuous fun s ↦ f (p, s) :=
    hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) fun _ ↦ ⟨hp, trivial⟩
  have hm (p : Base) (hp : p ∈ collar lo hi) : Lifted.mean f p = 0 :=
    (C.mean_labelDrift ψ p hp).trans (hW p hp)
  have hfs (p : Base) (hp : p ∈ collar lo hi) : Function.Periodic (fun s ↦ f (p, s)) 1 :=
    fun s ↦ by simp [f, labelDrift, C.Y_phase p hp s]
  have hfθ (p : Base) (hp : p ∈ collar lo hi) (s : ℝ) : f (p + (1, 0), s) = f (p, s) := by
    have hd : fderiv ℝ ψ (p + (1, 0)) = fderiv ℝ ψ p :=
      translated_fderiv hU hp (fun ⟨θ, r⟩ hx ↦ by simpa [Prod.mk_add_mk] using hper r hx.2 θ)
    simp [f, labelDrift, hd, C.Y_turn p hp s]
  refine ⟨⟨ψ, g, hψ, hg, hper, ?_, fun p hp ↦ Lifted.periodic_corrector _ _ _ (hfc p hp)
    (hfs p hp), fun p hp ↦ Lifted.mean_corrector _ _ _ (hfc p hp), h0, h1, hrange, ?_⟩⟩
  · rintro ⟨p, s⟩ hp
    rw [Prod.mk_add_mk, add_zero]
    simp [g, Lifted.corrector, Lifted.primitive, Lifted.mean, C.T_turn p hp.1, hfθ p hp.1]
  · rintro ⟨p, s⟩ hp
    have hunit := Lifted.fderiv_corrector_phase s hU hp.1
      (C.T_smooth.of_le (by simp)) (hf.of_le (by simp))
    rw [hm p hp.1] at hunit
    have hv : C.fast (p, s) = (C.T p)⁻¹ • ((0, 1) : Base × ℝ) := by simp [fast]
    change fderiv ℝ (Lifted.corrector C.T f) (p, s) (C.fast (p, s)) = _
    rw [hv, map_smul, hunit, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (C.period_pos p hp.1).ne']
    simp [f, labelDrift]

variable {C}

/-- Every interior base point has a positive distance in label from both edge values. -/
theorem CorrectedStream.label_mem_interior (S : C.CorrectedStream) (hlo : lo < 0) (hhi : 1 < hi)
    {p : Base} (hp : p.2 ∈ Ioo (0 : ℝ) 1) : S.label p ∈ Ioo (0 : ℝ) 1 := by
  have hcoll : p ∈ collar lo hi := ⟨trivial, hlo.trans hp.1, hp.2.trans hhi⟩
  have hd := (S.smooth_label.contDiffAt (isOpen_collar.mem_nhds hcoll)).differentiableAt (by simp)
  obtain ⟨hr, hn⟩ := S.regular p (Ioo_subset_Icc_self hp)
  have hnear := continuous_snd.continuousAt (Ioo_mem_nhds hp.1 hp.2)
  constructor
  · apply lt_of_le_of_ne hr.1
    intro he
    have hl : IsLocalMin S.label p := by
      filter_upwards [hnear] with q hq
      exact he ▸ (S.regular q (Ioo_subset_Icc_self hq)).1.1
    exact hn (hl.hasFDerivAt_eq_zero hd.hasFDerivAt)
  · apply lt_of_le_of_ne hr.2
    intro he
    have hu : IsLocalMax S.label p := by
      filter_upwards [hnear] with q hq
      exact he ▸ (S.regular q (Ioo_subset_Icc_self hq)).1.2
    exact hn (hu.hasFDerivAt_eq_zero hd.hasFDerivAt)

/-- One birth margin in label works for all angles on an interior radial subband. -/
theorem CorrectedStream.exists_uniform_birth_margin (S : C.CorrectedStream)
    (hlo : lo < 0) (hhi : 1 < hi) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : Base, p.2 ∈ Icc a b →
      δ ≤ S.label p ∧ S.label p ≤ 1 - δ := by
  let box : Set Base := Icc 0 1 ×ˢ Icc a b
  let margin := fun p : Base ↦ min (S.label p) (1 - S.label p)
  have interior {r : ℝ} (hr : r ∈ Icc a b) : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hin {r : ℝ} (hr : r ∈ Icc a b) : r ∈ Ioo lo hi :=
    ⟨hlo.trans (interior hr).1, (interior hr).2.trans hhi⟩
  have hc : ContinuousOn S.label box := S.smooth_label.continuousOn.mono
    (fun q hq ↦ ⟨trivial, hin hq.2⟩)
  have compact : IsCompact box := isCompact_Icc.prod isCompact_Icc
  obtain ⟨q, hq, hmin⟩ := compact.exists_isMinOn
    (show box.Nonempty from ⟨(0, a), by simp [box, hab]⟩)
    (show ContinuousOn margin box from hc.inf (continuousOn_const.sub hc))
  have hq' := S.label_mem_interior hlo hhi (interior hq.2)
  refine ⟨margin q, lt_min hq'.1 (sub_pos.mpr hq'.2), ?_⟩
  rintro ⟨θ, r⟩ hr
  have he := (S.label_periodic r (hin hr)).sub_int_mul_eq (x := θ) ⌊θ⌋
  have hperiod : S.label (Int.fract θ, r) = S.label (θ, r) := by
    simpa only [Int.fract, mul_one] using he
  have hm := hmin (show (Int.fract θ, r) ∈ box from
    ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hr⟩)
  change margin q ≤ min (S.label _) (1 - S.label _) at hm
  rw [hperiod] at hm
  exact ⟨le_min_iff.mp hm |>.1, le_sub_comm.mp (le_min_iff.mp hm).2⟩

/-- The exact derivative along a lifted perturbed orbit. -/
theorem CorrectedStream.orbit_derivative (S : C.CorrectedStream) {z : ℝ → Base × ℝ}
    {t ε : ℝ} (hp : z t ∈ PhaseCollar lo hi)
    (hz : HasDerivAt z (C.fast (z t) + ε • C.Y (z t)) t) :
    HasDerivAt (fun u ↦ S.label (z u).1 + ε * S.correction (z u))
      (ε ^ 2 * fderiv ℝ S.correction (z t) (C.Y (z t))) t := by
  have hψ := (S.smooth_label.contDiffAt (isOpen_collar.mem_nhds hp.1)).differentiableAt (by simp)
  have hopen := (isOpen_collar.prod isOpen_univ).mem_nhds hp
  have hg := (S.smooth_correction.contDiffAt hopen).differentiableAt (by simp)
  have hL := hψ.hasFDerivAt.comp (z t) hasFDerivAt_fst
  apply corrected_hasDerivAt (ψ := S.label ∘ Prod.fst) hL.differentiableAt hg _ _ hz
  · rw [hL.fderiv]
    simp [fast]
  · rw [hL.fderiv]
    exact S.cancels (z t) hp

/-- At any proposed first hit the label is strictly between the edge values, under the
second-order budget. The bounds and the equation are tested on that orbit segment only. -/
theorem CorrectedStream.excludes_first_hit (S : C.CorrectedStream) {z : ℝ → Base × ℝ}
    {t ε G K δ : ℝ} (ht : 0 ≤ t) (hc : ∀ s ∈ Icc 0 t, z s ∈ PhaseCollar lo hi)
    (hz : ∀ s ∈ Icc 0 t, HasDerivAt z (C.fast (z s) + ε • C.Y (z s)) s)
    (hstart : δ ≤ S.label (z 0).1 ∧ S.label (z 0).1 ≤ 1 - δ)
    (hg₀ : |S.correction (z 0)| ≤ G) (hgt : |S.correction (z t)| ≤ G)
    (hk : ∀ s ∈ Icc 0 t, |fderiv ℝ S.correction (z s) (C.Y (z s))| ≤ K)
    (hbudget : 2 * |ε| * G + t * ε ^ 2 * K < δ) :
    (z t).1.2 ≠ 0 ∧ (z t).1.2 ≠ 1 := by
  have h := no_boundary_hit ht
    (fun s hs ↦ (S.orbit_derivative (hc s hs) (hz s hs)).hasDerivWithinAt)
    hk hg₀ hgt hstart hbudget
  constructor
  · intro h0
    have he : (z t).1 = ((z t).1.1, 0) := Prod.ext rfl h0
    have hh : S.label (z t).1 = 0 := he ▸ S.lower _
    exact (ne_of_gt h.1) hh
  · intro h1
    have he : (z t).1 = ((z t).1.1, 1) := Prod.ext rfl h1
    have hh : S.label (z t).1 = 1 := he ▸ S.upper _
    exact (ne_of_lt h.2) hh

end PlasmaLean.AnnulusFibreFlux.VolumeChart
