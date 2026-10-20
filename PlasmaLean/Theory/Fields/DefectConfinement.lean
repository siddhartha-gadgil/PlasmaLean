/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FirstIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Finite-length field-line confinement from an approximate first integral

Theorem A of `notes/theory/first-stellarator-rung.md` (§2.1), an elementary first-exit
argument. Let `T` be a closed set and `I` a function differentiable at every point of
`T`. Suppose

* (i) `I > I_b` on the frontier of `T`;
* (ii) the *defect* is small: `|DI(x) B(x)| = |B · ∇I| ≤ δ` on `T ∩ {I ≤ I_b}`.

Then a forward field line `γ' = B(γ)` starting in `T` with `I(γ 0) ≤ I_a` stays in `T`,
with `I(γ s) ≤ I_a + δ s`, for every parameter `s ≥ 0` with `δ s < I_b - I_a`
(`fieldLine_confined_of_defect`).

The defect is stable under perturbations of the field: if `‖B' - B‖ ≤ η` and
`‖DI‖ ≤ G` then the defect of `I` for `B'` is at most `δ + η G`
(`defect_of_perturbation`); the two combine in `fieldLine_confined_of_perturbation`.

Sanity: `δ = 0` recovers all-time confinement (`fieldLine_confined_of_exact`), and
`uniform_confined_instance` is a non-vacuous instance (a uniform field, `I = ‖x‖²`, the
unit ball) whose finite-length conclusion is consistent with the true exit time.

Scope: field-line statements only (the parameter is the field-line parameter `s`, not
particle time, and not arc length unless `|B| = 1`); no existence of field lines is
postulated, statements quantify over supplied curves. Guiding-centre confinement is a
separate question.
-/

public section
noncomputable section
namespace PlasmaLean.Fields
open Set Filter Topology

/-- Drift bound along a field line that has stayed in `T ∩ {I ≤ I_b}` on `[0, t]`. -/
theorem defect_drift {B : Space → Space} {I : Space → ℝ} {T : Set Space} {Ib δ : ℝ}
    (hI : ∀ x ∈ T, DifferentiableAt ℝ I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) {t : ℝ}
    (hstay : ∀ u ∈ Icc 0 t, γ u ∈ T ∧ I (γ u) ≤ Ib) (ht : 0 ≤ t) :
    I (γ t) ≤ I (γ 0) + δ * t := by
  have hd : ∀ u ∈ Icc 0 t, HasDerivAt (fun v => I (γ v)) (fderiv ℝ I (γ u) (B (γ u))) u :=
    fun u hu => (hI _ (hstay u hu).1).hasFDerivAt.comp_hasDerivAt u (hγ u hu.1)
  have h := Kinetic.invariant_drift hd (fun u hu => hdef _ (hstay u hu).1 (hstay u hu).2)
    ⟨ht, le_rfl⟩
  have := (abs_le.mp h).2
  linarith

/-- **First-exit confinement from a small defect** (Theorem A).
If `I > I_b` on the frontier of the closed set `T` and `|B · ∇I| ≤ δ` on
`T ∩ {I ≤ I_b}`, then a forward field line starting in `T` with `I ≤ I_a` stays in `T`,
with `I(γ s) ≤ I_a + δ s`, for every `s ≥ 0` with `δ s < I_b - I_a`. -/
theorem fieldLine_confined_of_defect {B : Space → Space} {I : Space → ℝ} {T : Set Space}
    {Ia Ib δ : ℝ} (hδ : 0 ≤ δ) (hT : IsClosed T) (hI : ∀ x ∈ T, DifferentiableAt ℝ I x)
    (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ T) (hIa : I (γ 0) ≤ Ia) :
    ∀ s, 0 ≤ s → δ * s < Ib - Ia → γ s ∈ T ∧ I (γ s) ≤ Ia + δ * s := by
  intro s hs hδs
  have hab : Ia < Ib := by nlinarith
  have hγc : ∀ u, 0 ≤ u → ContinuousAt γ u := fun u hu => (hγ u hu).continuousAt
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
          (hγc t₁ ht₁0).tendsto.mono_left nhdsWithin_le_nhds
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
    have hdr := defect_drift hI hdef hγ hstay ht₁0
    have hlt : I (γ t₁) < Ib := by nlinarith [mul_le_mul_of_nonneg_left ht₁s hδ]
    have hint : γ t₁ ∈ interior T := by
      by_contra hn
      have : γ t₁ ∈ frontier T := by rw [hT.frontier_eq]; exact ⟨hat.1, hn⟩
      exact absurd (hfront _ this) (not_lt.mpr hlt.le)
    -- the good set is a neighbourhood of `t₁`
    have hnhds : {u | γ u ∈ interior T ∧ I (γ u) < Ib} ∈ 𝓝 t₁ := by
      have h1 : {u | γ u ∈ interior T} ∈ 𝓝 t₁ :=
        (hγc t₁ ht₁0).preimage_mem_nhds (isOpen_interior.mem_nhds hint)
      have hIc : ContinuousAt (fun u => I (γ u)) t₁ :=
        (hI _ hat.1).continuousAt.comp (hγc t₁ ht₁0)
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
  exact ⟨(hstay s ⟨hs, le_rfl⟩).1, by linarith [defect_drift hI hdef hγ hstay hs]⟩

/-- **Defect under field perturbation.** If `|DI·B| ≤ δ`, `‖B' - B‖ ≤ η` and `‖DI‖ ≤ G`
on `K`, then `|DI·B'| ≤ δ + η G` on `K`. -/
theorem defect_of_perturbation {B B' : Space → Space} {I : Space → ℝ} {K : Set Space}
    {δ η G : ℝ} (hdef : ∀ x ∈ K, |fderiv ℝ I x (B x)| ≤ δ)
    (hη : ∀ x ∈ K, ‖B' x - B x‖ ≤ η) (hG : ∀ x ∈ K, ‖fderiv ℝ I x‖ ≤ G) :
    ∀ x ∈ K, |fderiv ℝ I x (B' x)| ≤ δ + η * G := by
  intro x hx
  have hsplit : fderiv ℝ I x (B' x) = fderiv ℝ I x (B x) + fderiv ℝ I x (B' x - B x) := by
    rw [map_sub]; ring
  have hle : |fderiv ℝ I x (B' x - B x)| ≤ η * G := by
    have h1 := (fderiv ℝ I x).le_opNorm (B' x - B x)
    rw [Real.norm_eq_abs] at h1
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG x hx)
    calc |fderiv ℝ I x (B' x - B x)| ≤ ‖fderiv ℝ I x‖ * ‖B' x - B x‖ := h1
      _ ≤ G * η := mul_le_mul (hG x hx) (hη x hx) (norm_nonneg _) hG0
      _ = η * G := mul_comm _ _
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add (hdef x hx) hle)

/-- Composition: a defect bound `δ` for `B`, a field error `η` and a gradient bound `G`
give finite-length confinement for the perturbed field `B'` for every `s ≥ 0` with
`(δ + η G) s < I_b - I_a`. -/
theorem fieldLine_confined_of_perturbation {B B' : Space → Space} {I : Space → ℝ}
    {T : Set Space} {Ia Ib δ η G : ℝ} (hδ : 0 ≤ δ) (hη0 : 0 ≤ η) (hG0 : 0 ≤ G)
    (hT : IsClosed T)
    (hI : ∀ x ∈ T, DifferentiableAt ℝ I x) (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hdef : ∀ x ∈ T, I x ≤ Ib → |fderiv ℝ I x (B x)| ≤ δ)
    (hη : ∀ x ∈ T, I x ≤ Ib → ‖B' x - B x‖ ≤ η)
    (hG : ∀ x ∈ T, I x ≤ Ib → ‖fderiv ℝ I x‖ ≤ G)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B' γ) (h0 : γ 0 ∈ T) (hIa : I (γ 0) ≤ Ia) :
    ∀ s, 0 ≤ s → (δ + η * G) * s < Ib - Ia →
      γ s ∈ T ∧ I (γ s) ≤ Ia + (δ + η * G) * s := by
  have hdef' := defect_of_perturbation (K := {x | x ∈ T ∧ I x ≤ Ib}) (B := B) (B' := B')
    (I := I) (fun x hx => hdef x hx.1 hx.2) (fun x hx => hη x hx.1 hx.2)
    (fun x hx => hG x hx.1 hx.2)
  exact fieldLine_confined_of_defect (by positivity) hT hI hfront
    (fun x hx h => hdef' x ⟨hx, h⟩) hγ h0 hIa

/-! ### Sanity checks -/

/-- Degenerate case `δ = 0`: an exact first integral on `T ∩ {I ≤ I_b}` with `I > I_b`
on the frontier confines every field line starting in `T ∩ {I ≤ I_a}`, `I_a < I_b`, for
all `s ≥ 0` (all-time confinement, as in `sublevel_confined`). -/
theorem fieldLine_confined_of_exact {B : Space → Space} {I : Space → ℝ} {T : Set Space}
    {Ia Ib : ℝ} (hab : Ia < Ib) (hT : IsClosed T) (hI : ∀ x ∈ T, DifferentiableAt ℝ I x)
    (hfront : ∀ x ∈ frontier T, Ib < I x)
    (hexact : ∀ x ∈ T, I x ≤ Ib → fderiv ℝ I x (B x) = 0)
    {γ : ℝ → Space} (hγ : IsForwardFieldLine B γ) (h0 : γ 0 ∈ T) (hIa : I (γ 0) ≤ Ia) :
    ∀ s, 0 ≤ s → γ s ∈ T ∧ I (γ s) ≤ Ia := by
  intro s hs
  have h := fieldLine_confined_of_defect (δ := 0) le_rfl hT hI hfront
    (fun x hx h => by rw [hexact x hx h, abs_zero]) hγ h0 hIa s hs (by linarith)
  simpa using h

/-- Degenerate case `η = 0`: the perturbation bound reduces to the defect bound. -/
theorem defect_of_perturbation_zero {B : Space → Space} {I : Space → ℝ} {K : Set Space}
    {δ G : ℝ} (hdef : ∀ x ∈ K, |fderiv ℝ I x (B x)| ≤ δ)
    (hG : ∀ x ∈ K, ‖fderiv ℝ I x‖ ≤ G) :
    ∀ x ∈ K, |fderiv ℝ I x (B x)| ≤ δ + 0 * G :=
  defect_of_perturbation hdef (fun x _ => by simp) hG

/-- Derivative of `‖x‖²`. -/
theorem hasFDerivAt_normSq (x : Space) :
    HasFDerivAt (fun y : Space => ‖y‖ ^ 2) ((2 : ℕ) • innerSL ℝ x) x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt

/-- **Non-vacuous instance.** For the uniform field `B ≡ c e₃` (`‖e₃‖ = 1`), the function
`I = ‖x‖²` on the closed unit ball with `I_b = 1/2` has defect `≤ 2|c|`; the line
`γ(t) = t c e₃` from the origin is therefore certified to stay in the ball for
`2|c| s < 1/2`. (It truly exits at `|c| s = 1`, so the certified length is consistent.) -/
theorem uniform_confined_instance (c : ℝ) {s : ℝ} (hs : 0 ≤ s) (hcs : 2 * |c| * s < 1 / 2) :
    ‖s • c • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ ≤ 1 := by
  set e : Space := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hγ : IsForwardFieldLine (fun _ => c • e) (fun t => t • c • e) := fun t _ => by
    simpa using (hasDerivAt_id t).smul_const (c • e)
  have hfront : ∀ x ∈ frontier (Metric.closedBall (0 : Space) 1), (1 / 2 : ℝ) < ‖x‖ ^ 2 := by
    intro x hx
    rw [frontier_closedBall (0 : Space) one_ne_zero, mem_sphere_zero_iff_norm] at hx
    rw [hx]; norm_num
  have hdef : ∀ x ∈ Metric.closedBall (0 : Space) 1, ‖x‖ ^ 2 ≤ 1 / 2 →
      |fderiv ℝ (fun y : Space => ‖y‖ ^ 2) x (c • e)| ≤ 2 * |c| := by
    intro x hx _
    rw [(hasFDerivAt_normSq x).fderiv]
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, inner_smul_right,
      nsmul_eq_mul, Nat.cast_ofNat, abs_mul]
    have h1 := abs_real_inner_le_norm x e
    rw [he, mul_one] at h1
    rw [abs_of_pos (two_pos : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg c, abs_nonneg (inner ℝ x e)]
  have h := fieldLine_confined_of_defect (Ia := 0) (by positivity) Metric.isClosed_closedBall
    (fun x _ => ((hasFDerivAt_normSq x).differentiableAt)) hfront hdef hγ (by simp)
    (by simp) s hs (by linarith)
  simpa using h.1

end PlasmaLean.Fields
