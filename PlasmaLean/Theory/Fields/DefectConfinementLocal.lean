/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.DefectConfinement

/-!
# Finite-length confinement from an approximate first integral, local version

`fieldLine_confined_of_defect_local`: the first-exit argument of
`Fields.fieldLine_confined_of_defect` for a curve `γ` that is only known to satisfy
`γ' = B(γ)` on `[0, L]` (no global existence of the field line is assumed); the conclusion
holds for `s ∈ [0, L]` with `δ s < I_b - I_a`. `fieldLine_confined_of_defect_global` recovers
the global version.
-/

public section
noncomputable section
namespace PlasmaLean.Fields
open Set Filter Topology

/-- Drift bound along a curve that is a field line on `[0, t]` and has stayed in
`T ∩ {I ≤ I_b}` on `[0, t]`. -/
theorem defect_drift_local {B : Space → Space} {I : Space → ℝ} {T : Set Space} {Ib δ : ℝ}
    (hI : ∀ x ∈ T, DifferentiableAt ℝ I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {γ : ℝ → Space} {t : ℝ} (hγ : ∀ u ∈ Icc 0 t, HasDerivAt γ (B (γ u)) u)
    (hstay : ∀ u ∈ Icc 0 t, γ u ∈ T ∧ I (γ u) ≤ Ib) (ht : 0 ≤ t) :
    I (γ t) ≤ I (γ 0) + δ * t := by
  have hd : ∀ u ∈ Icc 0 t, HasDerivAt (fun v => I (γ v)) (fderiv ℝ I (γ u) (B (γ u))) u :=
    fun u hu => (hI _ (hstay u hu).1).hasFDerivAt.comp_hasDerivAt u (hγ u hu)
  have h := Kinetic.invariant_drift hd (fun u hu => hdef _ (hstay u hu).1 (hstay u hu).2)
    ⟨ht, le_rfl⟩
  have := (abs_le.mp h).2
  linarith

/-- **Local first-exit confinement** (Theorem A for curves that are field lines only on
`[0, L]`; conclusion for `s ∈ [0, L]`).
If `I > I_b` on the frontier of the closed set `T` and `|B · ∇I| ≤ δ` on
`T ∩ {I ≤ I_b}`, then a forward field line starting in `T` with `I ≤ I_a` stays in `T`,
with `I(γ s) ≤ I_a + δ s`, for every `s ≥ 0` with `δ s < I_b - I_a`. -/
theorem fieldLine_confined_of_defect_local {B : Space → Space} {I : Space → ℝ} {T : Set Space}
    {Ia Ib δ : ℝ} (hδ : 0 ≤ δ) (hT : IsClosed T) (hI : ∀ x ∈ T, DifferentiableAt ℝ I x)
    (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {L : ℝ} {γ : ℝ → Space} (hγL : ∀ t ∈ Icc 0 L, HasDerivAt γ (B (γ t)) t) (h0 : γ 0 ∈ T)
    (hIa : I (γ 0) ≤ Ia) :
    ∀ s ∈ Icc 0 L, δ * s < Ib - Ia → γ s ∈ T ∧ I (γ s) ≤ Ia + δ * s := by
  intro s hsL hδs
  have hs : 0 ≤ s := hsL.1
  have hγ : ∀ u ∈ Icc 0 s, HasDerivAt γ (B (γ u)) u :=
    fun u hu => hγL u ⟨hu.1, hu.2.trans hsL.2⟩
  have hab : Ia < Ib := by nlinarith
  have hγc : ∀ u ∈ Icc 0 s, ContinuousAt γ u := fun u hu => (hγ u hu).continuousAt
  -- the set of "bad" parameters in `[0, s]`
  set Bd := {t ∈ Icc 0 s | ¬ (γ t ∈ interior T ∧ I (γ t) < Ib)} with hBd
  -- main claim: no bad parameter
  have hgood : ∀ t ∈ Icc 0 s, γ t ∈ interior T ∧ I (γ t) < Ib := by
    by_contra hne
    push Not at hne
    obtain ⟨t₀, ht₀, hbad⟩ := hne
    have hBne : Bd.Nonempty := ⟨t₀, ht₀, fun h => absurd h.2 (not_lt.mpr (hbad h.1))⟩
    have hBbdd : BddBelow Bd := ⟨0, fun t ht => ht.1.1⟩
    set t₁ := sInf Bd
    have ht₁0 : 0 ≤ t₁ := le_csInf hBne (fun t ht => ht.1.1)
    have ht₁s : t₁ ≤ s := (csInf_le hBbdd ⟨ht₀, fun h => absurd h.2 (not_lt.mpr (hbad h.1))⟩).trans
      ht₀.2
    -- before `t₁` everything is good
    have hbefore : ∀ u ∈ Ico 0 t₁, γ u ∈ interior T ∧ I (γ u) < Ib := by
      intro u hu
      by_contra hcon
      have : u ∈ Bd := ⟨⟨hu.1, hu.2.le.trans ht₁s⟩, hcon⟩
      exact absurd (csInf_le hBbdd this) (not_le.mpr hu.2)
    -- at `t₁`: in `T`, with `I ≤ I_b`
    have hat : γ t₁ ∈ T ∧ I (γ t₁) ≤ Ib := by
      rcases ht₁0.eq_or_lt with h | h
      · rw [← h]; exact ⟨h0, hIa.trans hab.le⟩
      · have hev : ∀ᶠ u in 𝓝[<] t₁, γ u ∈ T ∧ I (γ u) < Ib := by
          filter_upwards [Ioo_mem_nhdsLT h] with u hu
          exact ⟨interior_subset (hbefore u ⟨hu.1.le, hu.2⟩).1, (hbefore u ⟨hu.1.le, hu.2⟩).2⟩
        have hlim : Tendsto γ (𝓝[<] t₁) (𝓝 (γ t₁)) :=
          (hγc t₁ ⟨ht₁0, ht₁s⟩).tendsto.mono_left nhdsWithin_le_nhds
        have hmem : γ t₁ ∈ T := hT.mem_of_tendsto hlim (hev.mono fun u hu => hu.1)
        refine ⟨hmem, ?_⟩
        have hIlim : Tendsto (fun u => I (γ u)) (𝓝[<] t₁) (𝓝 (I (γ t₁))) :=
          ((hI _ hmem).continuousAt.tendsto).comp hlim
        exact le_of_tendsto hIlim (hev.mono fun u hu => hu.2.le)
    -- drift bound at `t₁`
    have hstay : ∀ u ∈ Icc 0 t₁, γ u ∈ T ∧ I (γ u) ≤ Ib := by
      intro u hu
      rcases hu.2.eq_or_lt with h | h
      · rw [h]; exact hat
      · exact ⟨interior_subset (hbefore u ⟨hu.1, h⟩).1, (hbefore u ⟨hu.1, h⟩).2.le⟩
    have hdr := defect_drift_local hI hdef (fun u hu => hγ u ⟨hu.1, hu.2.trans ht₁s⟩) hstay ht₁0
    have hlt : I (γ t₁) < Ib := by nlinarith [mul_le_mul_of_nonneg_left ht₁s hδ]
    have hint : γ t₁ ∈ interior T := by
      by_contra hn
      have : γ t₁ ∈ frontier T := by rw [hT.frontier_eq]; exact ⟨hat.1, hn⟩
      exact absurd (hfront _ this) (not_lt.mpr hlt.le)
    -- the good set is a neighbourhood of `t₁`
    have hnhds : {u | γ u ∈ interior T ∧ I (γ u) < Ib} ∈ 𝓝 t₁ := by
      have h1 : {u | γ u ∈ interior T} ∈ 𝓝 t₁ :=
        (hγc t₁ ⟨ht₁0, ht₁s⟩).preimage_mem_nhds (isOpen_interior.mem_nhds hint)
      have hIc : ContinuousAt (fun u => I (γ u)) t₁ :=
        (hI _ hat.1).continuousAt.comp (hγc t₁ ⟨ht₁0, ht₁s⟩)
      have h2 : {u | I (γ u) < Ib} ∈ 𝓝 t₁ := hIc.preimage_mem_nhds (Iio_mem_nhds hlt)
      exact Filter.inter_mem h1 h2
    obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    obtain ⟨b, hb, hbt⟩ := (csInf_lt_iff hBbdd hBne).mp (lt_add_of_pos_right t₁ hη)
    have hb1 : t₁ ≤ b := csInf_le hBbdd hb
    have hbmem : b ∈ Metric.ball t₁ η := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    exact hb.2 (hball hbmem)
  -- conclude with the drift bound
  have hstay : ∀ u ∈ Icc 0 s, γ u ∈ T ∧ I (γ u) ≤ Ib := fun u hu =>
    ⟨interior_subset (hgood u hu).1, (hgood u hu).2.le⟩
  exact ⟨(hstay s ⟨hs, le_rfl⟩).1, by linarith [defect_drift_local hI hdef hγ hstay hs]⟩


/-- Sanity: the local version implies the global one on every `[0, L]`. -/
theorem fieldLine_confined_of_defect_global {B : Space → Space} {I : Space → ℝ}
    {T : Set Space} {Ia Ib δ : ℝ} (hδ : 0 ≤ δ) (hT : IsClosed T)
    (hI : ∀ x ∈ T, DifferentiableAt ℝ I x) (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ T) (hIa : I (γ 0) ≤ Ia)
    (s : ℝ) (hs : 0 ≤ s) (hδs : δ * s < Ib - Ia) : γ s ∈ T ∧ I (γ s) ≤ Ia + δ * s :=
  fieldLine_confined_of_defect_local hδ hT hI hfront hdef (L := s)
    (fun t ht => hγ t ht.1) h0 hIa s ⟨hs, le_rfl⟩ hδs

end PlasmaLean.Fields
