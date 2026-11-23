/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AnnulusConfinementBounds
public import PlasmaLean.Theory.Kinetic.BoozerGCForward

/-!
# Existence of confined trajectories on the averaging time window

On the angular and phase cover, both periodic lifts can run arbitrarily far. Their
velocities are bounded on the closed radial band. Hence on a finite time interval
every partial solution belongs to a compact ball intersected with the band. Forward
continuation supplies a solution through the entire confinement window.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AnnulusFibreFlux.VolumeChart

open Set AnnulusStream
open scoped ContDiff Topology

variable {lo hi : ℝ} {C : VolumeChart lo hi}

/-- The lifted vector field with perturbation amplitude ε. -/
def perturbedField (C : VolumeChart lo hi) (ε : ℝ) (z : Base × ℝ) : Base × ℝ :=
  C.fast z + ε • C.Y z

/-- The lifted perturbed equation is smooth throughout the open collar. -/
theorem perturbedField_smooth (C : VolumeChart lo hi) (ε : ℝ) :
    ContDiffOn ℝ ∞ (C.perturbedField ε) (PhaseCollar lo hi) := by
  have hT : ContDiffOn ℝ ∞ (fun z : Base × ℝ => C.T z.1) (PhaseCollar lo hi) :=
    C.T_smooth.comp contDiffOn_fst fun _ hz => hz.1
  have hfast : ContDiffOn ℝ ∞ C.fast (PhaseCollar lo hi) :=
    contDiffOn_const.prodMk (hT.inv fun z hz => (C.period_pos z.1 hz.1).ne')
  exact hfast.add ((contDiffOn_const (c := ε)).smul C.Y_smooth)

/-- For fixed ε the lift has bounded speed over the entire closed radial band. -/
theorem exists_speed_bound (C : VolumeChart lo hi) (hlo : lo < 0) (hhi : 1 < hi) (ε : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : Base × ℝ, z.1.2 ∈ Icc (0 : ℝ) 1 → ‖C.perturbedField ε z‖ ≤ M := by
  have hθ (r : ℝ) (hr : r ∈ Ioo lo hi) (s : ℝ) :
      Function.Periodic (fun θ => ‖C.perturbedField ε ((θ, r), s)‖) 1 := by
    intro θ
    have hY := C.Y_turn (θ, r) ⟨trivial, hr⟩ s
    have hT := C.T_turn (θ, r) ⟨trivial, hr⟩
    simp only [Prod.mk_add_mk, add_zero] at hY hT
    simp [perturbedField, fast, hT, hY]
  have hs (p : Base) (hp : p ∈ collar lo hi) :
      Function.Periodic (fun s => ‖C.perturbedField ε (p, s)‖) 1 := by
    intro s
    simp [perturbedField, fast, C.Y_phase p hp s]
  obtain ⟨M, hM, hbd⟩ := exists_periodic_band_bound hlo zero_le_one hhi
    (C.perturbedField_smooth ε).continuousOn.norm hθ hs
  exact ⟨M, hM, fun z hz => by simpa using hbd z hz⟩

namespace CorrectedStream

/-- Through every initial point satisfying the label budget there exists a lifted
solution for the prescribed finite horizon, staying strictly inside the annulus. -/
theorem ConfinementWindow.exists_orbit {S : C.CorrectedStream} {G K : ℝ}
    (h : S.ConfinementWindow G K) (hK : 0 < K) (hlo : lo < 0) (hhi : 1 < hi)
    {z₀ : Base × ℝ} (hz₀ : z₀.1.2 ∈ Ioo (0 : ℝ) 1) {t ε δ : ℝ} (ht : 0 ≤ t)
    (hlabel : δ ≤ S.label z₀.1 ∧ S.label z₀.1 ≤ 1 - δ)
    (hbudget : 2 * |ε| * G + t * ε ^ 2 * K < δ) :
    ∃ z : ℝ → Base × ℝ, z 0 = z₀ ∧ ∀ u ∈ Icc 0 t,
      HasDerivAt z (C.perturbedField ε (z u)) u ∧ (z u).1.2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨M, hM, speed⟩ := C.exists_speed_bound hlo hhi ε
  let band : Set (Base × ℝ) := (fun z => z.1.2) ⁻¹' Icc (0 : ℝ) 1
  let U := PhaseCollar lo hi
  let region := band ∩ Metric.closedBall z₀ (M * t)
  have compact : IsCompact region := (isCompact_closedBall _ _).inter_left
    (isClosed_Icc.preimage (continuous_snd.comp continuous_fst))
  have incl {z : Base × ℝ} (hz : z.1.2 ∈ Icc (0 : ℝ) 1) : z ∈ U :=
    ⟨⟨trivial, hlo.trans_le hz.1, hz.2.trans_lt hhi⟩, trivial⟩
  have stay {c : ℝ} (hc : c ∈ Icc 0 t) {z : ℝ → Base × ℝ} (h0 : z 0 = z₀)
      (hz : ∀ u ∈ Icc 0 c, HasDerivAt z (C.perturbedField ε (z u)) u) :
      ∀ u ∈ Icc 0 c, (z u).1.2 ∈ Ioo (0 : ℝ) 1 := by
    apply h z c ε δ (fun u hu => (hz u hu).continuousAt.continuousWithinAt)
      (h0 ▸ hz₀) (h0 ▸ hlabel) (fun u hu _ => hz u hu)
    apply lt_of_le_of_lt _ hbudget
    gcongr
    exact hc.2
  have apriori (c : ℝ) (hc : c ∈ Icc 0 t) (z : ℝ → Base × ℝ) (h0 : z 0 = z₀)
      (hz : ∀ u ∈ Icc 0 c, HasDerivAt z (C.perturbedField ε (z u)) u) (u : ℝ)
      (hu : u ∈ Icc 0 c) : z u ∈ region := by
    have hb := stay hc h0 hz
    refine ⟨Ioo_subset_Icc_self (hb u hu), ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, ← h0]
    have hd := norm_image_sub_le_of_norm_deriv_le_segment' (f := z)
      (f' := fun s => C.perturbedField ε (z s)) (C := M)
      (fun s hs => (hz s hs).hasDerivWithinAt)
      (fun s hs => speed (z s) (Ioo_subset_Icc_self (hb s (Ico_subset_Icc_self hs)))) u hu
    exact hd.trans (mul_le_mul_of_nonneg_left (by linarith [hu.2, hc.2]) hM.le)
  obtain ⟨z, h0, hz⟩ := Fields.ODEGlobal.exists_forward_of_apriori
    (isOpen_collar.prod isOpen_univ) ((C.perturbedField_smooth ε).of_le (by simp)) compact
    (fun z hmem => incl hmem.1) (incl (Ioo_subset_Icc_self hz₀)) ht apriori
  exact ⟨z, h0, fun u hu => ⟨hz u hu, stay ⟨ht, le_rfl⟩ h0 hz u hu⟩⟩

end CorrectedStream

/-- Averaged tangency at both edges and a nonsingular projected mean give a
uniform second-order orbit-existence and confinement budget. Every closed radial
birth band strictly inside the annulus has a common positive label margin. -/
theorem exists_confined_orbits (C : VolumeChart lo hi) (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (C.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (C.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → C.meanField p ≠ 0) :
    ∃ G K : ℝ, 0 < G ∧ 0 < K ∧ ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (z₀ : Base × ℝ), z₀.1.2 ∈ Icc a b →
        ∀ (t ε : ℝ), 0 ≤ t → 2 * |ε| * G + t * ε ^ 2 * K < δ →
          ∃ z : ℝ → Base × ℝ, z 0 = z₀ ∧ ∀ u ∈ Icc 0 t,
            HasDerivAt z (C.perturbedField ε (z u)) u ∧ (z u).1.2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨S, G, K, hG, hK, hw⟩ := C.exists_confinement_window hlo hhi h₀ h₁ hn
  refine ⟨G, K, hG, hK, ?_⟩
  intro a b ha hab hb
  obtain ⟨δ, hδ, hmargin⟩ := S.exists_uniform_birth_margin hlo hhi ha hab hb
  refine ⟨δ, hδ, ?_⟩
  intro z₀ hbirth t ε ht hbudget
  exact hw.exists_orbit hK hlo hhi ⟨ha.trans_le hbirth.1, hbirth.2.trans_lt hb⟩ ht
    (hmargin z₀.1 hbirth) hbudget

/-- For a fixed closed birth band strictly inside the annulus, a single pair of
positive constants gives existence and confinement up to `c / ε²` for every
sufficiently small nonzero perturbation and all initial angles and phases. -/
theorem exists_inverse_square_orbits (C : VolumeChart lo hi) (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (C.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (C.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → C.meanField p ≠ 0)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < |ε| → |ε| < ε₀ →
      ∀ z₀ : Base × ℝ, z₀.1.2 ∈ Icc a b →
        ∃ z : ℝ → Base × ℝ, z 0 = z₀ ∧ ∀ t ∈ Icc 0 (c / ε ^ 2),
          HasDerivAt z (C.perturbedField ε (z t)) t ∧ (z t).1.2 ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨G, K, hG, hK, hbands⟩ := C.exists_confined_orbits hlo hhi h₀ h₁ hn
  obtain ⟨δ, hδ, hbudget⟩ := hbands a b ha hab hb
  refine ⟨δ / (2 * K), δ / (4 * G), by positivity, by positivity, ?_⟩
  intro ε hpos hsmall z₀ hbirth
  apply hbudget z₀ hbirth _ ε (by positivity)
  have hne : ε ≠ 0 := abs_pos.mp hpos
  have hfirst := (lt_div_iff₀ (by positivity : 0 < 4 * G)).mp hsmall
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hne)]
  have hterm : δ / (2 * K) * K = δ / 2 := by field_simp
  rw [hterm]
  linarith

end PlasmaLean.AnnulusFibreFlux.VolumeChart
