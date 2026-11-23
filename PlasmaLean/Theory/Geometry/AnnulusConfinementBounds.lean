/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Geometry.AnnulusConfinement
public import PlasmaLean.Theory.Geometry.ActionFaceBarrier

/-!
# Uniform second-order confinement bounds

Reduction of the angle and phase modulo one makes a closed radial band compact.
Consequently both the corrector and its derivative along the perturbation field
admit finite bounds independent of the orbit and of the perturbation parameter.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.AnnulusFibreFlux.VolumeChart

open Set AnnulusStream
open scoped ContDiff

variable {lo hi : ℝ} {C : VolumeChart lo hi}

/-- A continuous doubly periodic scalar has a single bound over every closed radial
subband of the open collar. Both lifts may range over the entire real line. -/
theorem exists_periodic_band_bound {a b : ℝ} (ha : lo < a) (hab : a ≤ b) (hb : b < hi)
    {F : Base × ℝ → ℝ} (hc : ContinuousOn F (PhaseCollar lo hi))
    (hθ : ∀ r ∈ Ioo lo hi, ∀ u, Function.Periodic (fun θ ↦ F ((θ, r), u)) 1)
    (hs : ∀ p ∈ collar lo hi, Function.Periodic (fun u ↦ F (p, u)) 1) :
    ∃ G : ℝ, 0 < G ∧ ∀ z : Base × ℝ, z.1.2 ∈ Icc a b → |F z| ≤ G := by
  let box : Set (Base × ℝ) := (Icc 0 1 ×ˢ Icc a b) ×ˢ Icc 0 1
  have hk : IsCompact box := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hn : box.Nonempty := ⟨((0, a), 0), by simp [box, hab]⟩
  have hin {r : ℝ} (hr : r ∈ Icc a b) : r ∈ Ioo lo hi := ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  have hcont : ContinuousOn (fun z ↦ |F z|) box :=
    hc.abs.mono fun z hz ↦ ⟨⟨trivial, hin hz.1.2⟩, trivial⟩
  obtain ⟨m, _, hm⟩ := hk.exists_isMaxOn hn hcont
  refine ⟨|F m| + 1, by positivity, ?_⟩
  rintro ⟨⟨θ, r⟩, u⟩ hr
  let θ' := Int.fract θ
  let u' := Int.fract u
  have hθ' : F ((θ', r), u) = F ((θ, r), u) := by
    simpa only [θ', Int.fract, mul_one] using (hθ r (hin hr) u).sub_int_mul_eq (x := θ) ⌊θ⌋
  have hu' : F ((θ', r), u') = F ((θ', r), u) := by
    simpa only [u', Int.fract, mul_one] using
      (hs (θ', r) ⟨trivial, hin hr⟩).sub_int_mul_eq (x := u) ⌊u⌋
  have hmem : ((θ', r), u') ∈ box :=
    ⟨⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hr⟩,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
  rw [← hθ', ← hu']
  exact (hm hmem).trans (by linarith)

namespace CorrectedStream

/-- The second-order coefficient in the exact corrected evolution. -/
def remainder (S : C.CorrectedStream) (z : Base × ℝ) : ℝ := fderiv ℝ S.correction z (C.Y z)

/-- Uniform bounds for the corrector and the second-order coefficient, independent of
both the trajectory and the perturbation strength. -/
theorem exists_uniform_bounds (S : C.CorrectedStream) {a b : ℝ}
    (ha : lo < a) (hab : a ≤ b) (hb : b < hi) :
    ∃ G K : ℝ, 0 < G ∧ 0 < K ∧ ∀ z : Base × ℝ, z.1.2 ∈ Icc a b →
      |S.correction z| ≤ G ∧ |S.remainder z| ≤ K := by
  have hV : IsOpen (PhaseCollar lo hi) := isOpen_collar.prod isOpen_univ
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ S.correction) (PhaseCollar lo hi) := by
    apply S.smooth_correction.fderiv_of_isOpen hV
    simp
  have hc : ContinuousOn S.remainder (PhaseCollar lo hi) :=
    (hd.clm_apply C.Y_smooth).continuousOn
  have hθ (r : ℝ) (hr : r ∈ Ioo lo hi) (u : ℝ) :
      Function.Periodic (fun θ ↦ S.correction ((θ, r), u)) 1 := fun θ ↦ by
    simpa using S.angle_turn ((θ, r), u) ⟨⟨trivial, hr⟩, trivial⟩
  obtain ⟨G, hG, hg⟩ := exists_periodic_band_bound ha hab hb
    S.smooth_correction.continuousOn hθ S.phase_turn
  have hrθ (r : ℝ) (hr : r ∈ Ioo lo hi) (u : ℝ) :
      Function.Periodic (fun θ ↦ S.remainder ((θ, r), u)) 1 := by
    intro θ
    have hz : ((θ, r), u) ∈ PhaseCollar lo hi := ⟨⟨trivial, hr⟩, trivial⟩
    have hshift := translated_fderiv hV hz S.angle_turn
    have hY := C.Y_turn (θ, r) hz.1 u
    simpa [remainder] using congrArg₂ (fun (L : Base × ℝ →L[ℝ] ℝ) v ↦ L v) hshift hY
  have hrs (p : Base) (hp : p ∈ collar lo hi) :
      Function.Periodic (fun u ↦ S.remainder (p, u)) 1 := by
    intro u
    have hz : (p, u) ∈ PhaseCollar lo hi := ⟨hp, trivial⟩
    have hshift := translated_fderiv (v := ((0 : Base), 1)) hV hz (F := S.correction)
      (by rintro ⟨q, s⟩ hq; simpa using S.phase_turn q hq.1 s)
    have hY := C.Y_phase p hp u
    simpa [remainder] using congrArg₂ (fun (L : Base × ℝ →L[ℝ] ℝ) v ↦ L v) hshift hY
  obtain ⟨K, hK, hk⟩ := exists_periodic_band_bound ha hab hb hc hrθ hrs
  exact ⟨G, K, hG, hK, fun z hz ↦ ⟨hg z hz, hk z hz⟩⟩

/-- Every existing solution curve started with the stated label margin stays in the open
band throughout the finite-time budget. The ODE is only required on the closed band. -/
def ConfinementWindow (S : C.CorrectedStream) (G K : ℝ) : Prop :=
  ∀ (z : ℝ → Base × ℝ) (t ε δ : ℝ), ContinuousOn z (Icc 0 t) →
    (z 0).1.2 ∈ Ioo (0 : ℝ) 1 → (δ ≤ S.label (z 0).1 ∧ S.label (z 0).1 ≤ 1 - δ) →
    (∀ s ∈ Icc 0 t, (z s).1.2 ∈ Icc (0 : ℝ) 1 →
      HasDerivAt z (C.fast (z s) + ε • C.Y (z s)) s) →
    2 * |ε| * G + t * ε ^ 2 * K < δ → ∀ s ∈ Icc 0 t, (z s).1.2 ∈ Ioo (0 : ℝ) 1

/-- The two confinement constants can be chosen once for a corrected stream, before
the initial trajectory and perturbation strength are specified. -/
theorem exists_confinement_window (S : C.CorrectedStream) (hlo : lo < 0) (hhi : 1 < hi) :
    ∃ G K : ℝ, 0 < G ∧ 0 < K ∧ S.ConfinementWindow G K := by
  obtain ⟨G, K, hG, hK, hbounds⟩ := S.exists_uniform_bounds hlo zero_le_one hhi
  refine ⟨G, K, hG, hK, ?_⟩
  intro z t ε δ hc hrad hlabel hz hbudget s hs
  by_contra hout
  obtain ⟨u, hu, hedge, hband⟩ := ActionFaceBarrier.first_hit_of_departure hc.fst.snd hrad hs hout
  have hsub : Icc 0 u ⊆ Icc 0 t := Icc_subset_Icc_right hu.2
  have hcollar (v : ℝ) (hv : v ∈ Icc 0 u) : z v ∈ PhaseCollar lo hi :=
    ⟨⟨trivial, hlo.trans_le (hband v hv).1, (hband v hv).2.trans_lt hhi⟩, trivial⟩
  have hbud : 2 * |ε| * G + u * ε ^ 2 * K < δ := by
    apply lt_of_le_of_lt _ hbudget
    gcongr
    exact hu.2
  obtain ⟨hn₀, hn₁⟩ := S.excludes_first_hit hu.1 hcollar
    (fun v hv ↦ hz v (hsub hv) (hband v hv)) hlabel
    (hbounds _ (hband 0 (left_mem_Icc.mpr hu.1))).1
    (hbounds _ (hband u (right_mem_Icc.mpr hu.1))).1
    (fun v hv ↦ (hbounds (z v) (hband v hv)).2) hbud
  exact hedge.elim hn₀ hn₁

/-- An explicit inverse-square time window for a nonzero perturbation. At most half
of the initial label margin is used by each of the two error terms. -/
theorem ConfinementWindow.inverse_square {S : C.CorrectedStream} {G K : ℝ}
    (h : S.ConfinementWindow G K) (hG : 0 < G) (hK : 0 < K) {z : ℝ → Base × ℝ} {t ε δ : ℝ}
    (hc : ContinuousOn z (Icc 0 t)) (hrad : (z 0).1.2 ∈ Ioo (0 : ℝ) 1)
    (hlabel : δ ≤ S.label (z 0).1 ∧ S.label (z 0).1 ≤ 1 - δ)
    (hz : ∀ s ∈ Icc 0 t, (z s).1.2 ∈ Icc (0 : ℝ) 1 →
      HasDerivAt z (C.fast (z s) + ε • C.Y (z s)) s)
    (hne : ε ≠ 0) (hε : |ε| < δ / (4 * G)) (ht : t ≤ δ / (2 * ε ^ 2 * K)) :
    ∀ s ∈ Icc 0 t, (z s).1.2 ∈ Ioo (0 : ℝ) 1 := by
  apply h z t ε δ hc hrad hlabel hz
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 4 * G)).mp hε
  have htime := (le_div_iff₀ (by positivity : 0 < 2 * ε ^ 2 * K)).mp ht
  linarith

end CorrectedStream

/-- A positive volume chart with a nonvanishing averaged field tangent to the two
boundary circles admits a normalized radial label, a smooth periodic corrector, and
uniform second-order confinement for every existing solution with an interior margin. -/
theorem exists_confinement_window (C : VolumeChart lo hi) (hlo : lo < 0) (hhi : 1 < hi)
    (h₀ : ∀ θ, (C.meanField (θ, 0)).2 = 0) (h₁ : ∀ θ, (C.meanField (θ, 1)).2 = 0)
    (hn : ∀ p : Base, p.2 ∈ Icc (0 : ℝ) 1 → C.meanField p ≠ 0) :
    ∃ (S : C.CorrectedStream) (G K : ℝ), 0 < G ∧ 0 < K ∧ S.ConfinementWindow G K := by
  obtain ⟨S⟩ := C.exists_correctedStream hlo hhi h₀ h₁ hn
  exact ⟨S, S.exists_confinement_window hlo hhi⟩

end PlasmaLean.AnnulusFibreFlux.VolumeChart
