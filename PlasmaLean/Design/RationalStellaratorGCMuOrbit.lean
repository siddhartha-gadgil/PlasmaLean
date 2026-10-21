/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuField
public import PlasmaLean.Theory.Fields.FieldLineBootstrap

/-!
# `μ > 0` Littlejohn orbits as field lines of a time-changed field

For the Littlejohn guiding-centre model in the rational stellarator field `B = field (1/4)` with
magnetic moment `μ ≥ 0`, energy `E > 0` and `v_∥(0) > 0`:

* `VmuF c ρ₀ λ = (c √(1 − λ|B|)/|B|) gcFieldMu ρ₀ λ` is the velocity field of the passing orbits
  (`c = √(2E/m)`, `ρ₀ = (m/q)√(2E/m)`, `λ = μ/E`); it is `C¹` on `muRegion λ`
  (`VmuF_contDiffOn`).
* `littlejohn_mu_local_fwd`, `littlejohn_mu_local_bwd`: **on every time interval `[0, b]` (resp.
  `[a, 0]`) on which the orbit stays in `muRegion λ`**, energy is conserved, `v_∥ > 0`,
  `v_∥ = √(2(E − μ|B|)/m)` and `dX/dt = VmuF(X)` — no regularity of the orbit outside that
  interval is assumed (the local versions `hamiltonian_hasDerivAt_of`, `passing_hasDerivAt_of`
  of the global identities of `Theory/Kinetic/GuidingCentreLittlejohn` and
  `Theory/Kinetic/GuidingCentrePassing`).
* `littlejohn_of_fieldLine`: conversely, a field line `Y` of `VmuF` in `muRegion λ` with
  `v_∥ = √(2(E − μ|B(Y)|)/m)` is a Littlejohn orbit.
* **`littlejohn_mu_eq_fieldLine`**: a Littlejohn orbit starting where the field line `Y` of
  `VmuF` from `X 0` is trapped in a compact subset of `muRegion λ` coincides with `Y` for all
  time (`Theory/Fields/FieldLineBootstrap`, `curve_eq_of_local`).

**Sanity.** `VmuF_zero`: for `λ = 0` the field is `(c/|B|) gcField ρ₀`, the `μ = 0` time change.
-/

open scoped RealInnerProductSpace

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open Set PlasmaLean.Fields PlasmaLean.Design.RationalStellarator PlasmaLean.Kinetic
  PlasmaLean.Kinetic.GCLittlejohn PlasmaLean.Kinetic.GCPassing PlasmaLean.Fields.Bootstrap

/-- **The velocity field of the `μ > 0` passing guiding centres**:
`(c √(1 − λ|B|)/|B|) · gcFieldMu ρ₀ λ` (with `c = √(2E/m)`, this is `(v_∥/B*_∥) B̃_{E,μ}`). -/
def VmuF (c ρ₀ lm : ℝ) (x : Space) : Space :=
  (c * √(1 - lm * ‖field (1 / 4) x‖) / ‖field (1 / 4) x‖) • gcFieldMu ρ₀ lm x

/-- **Sanity**: for `λ = 0` the field is the `μ = 0` time change `(c/|B|) gcField ρ₀`. -/
theorem VmuF_zero (c ρ₀ : ℝ) (x : Space) :
    VmuF c ρ₀ 0 x = (c / ‖field (1 / 4) x‖) • gcField ρ₀ x := by
  simp [VmuF, gcFieldMu_zero]

/-- The time change is smooth on `muRegion λ`. -/
theorem VmuF_scalar_contDiffOn (c lm : ℝ) : ContDiffOn ℝ 1
    (fun x => c * √(1 - lm * ‖field (1 / 4) x‖) / ‖field (1 / 4) x‖) (muRegion lm) := by
  have hN := (normB_contDiffOn 1).mono (fun x (hx : x ∈ muRegion lm) => hx.1)
  have hs : ContDiffOn ℝ 1 (fun x => √(1 - lm * ‖field (1 / 4) x‖)) (muRegion lm) :=
    (contDiffOn_const.sub (contDiffOn_const.mul hN)).sqrt fun x hx => by
      have := hx.2; linarith
  exact (contDiffOn_const.mul hs).div hN fun x hx => norm_ne_zero_iff.2 hx.1.2

/-- **`VmuF` is `C¹`** on `muRegion λ`. -/
theorem VmuF_contDiffOn (c ρ₀ lm : ℝ) : ContDiffOn ℝ 1 (VmuF c ρ₀ lm) (muRegion lm) :=
  (VmuF_scalar_contDiffOn c lm).smul (gcFieldMu_contDiffOn ρ₀ lm)

/-! ## Local versions of the energy and passing identities -/

/-- The energy is stationary at every time where `|B|` is differentiable along the orbit. -/
theorem hamiltonian_hasDerivAt_of {m q μ : ℝ} {B : Space → Space} {X : ℝ → Space} {v : ℝ → ℝ}
    (h : LittlejohnOrbit m q μ B X v) (hm : m ≠ 0) {t : ℝ}
    (hd : DifferentiableAt ℝ (fun y => ‖B y‖) (X t)) :
    HasDerivAt (fun s => hamiltonian m μ B (X s) (v s)) 0 t := by
  have hn : HasDerivAt (fun s => ‖B (X s)‖)
      (⟪gradAbsB B (X t), (BstarPar m q B (v t) (X t))⁻¹ •
        (v t • Bstar m q B (v t) (X t) + (μ / q) • cross (bhat B (X t)) (gradAbsB B (X t)))⟫)
      t := by
    exact (hd.hasGradientAt.hasFDerivAt).comp_hasDerivAt t (h.hX t)
  have hH := (((h.hv t).pow 2).const_mul m |>.div_const 2).add (hn.const_mul μ)
  convert hH using 1
  · funext s; simp [hamiltonian]
  · rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
      PlasmaLean.Kinetic.inner_cross_self']
    field_simp
    rw [real_inner_comm]
    ring

/-- **The passing identity at one time**: if `v_∥(t) = σ √(2(E − μ|B(X t)|)/m)` with a positive
radicand and `|B|`, `b` are differentiable at `X t`, then `dX/dt = (v_∥/B*_∥) B̃_{E,μ}(X)` at
`t`. -/
theorem passing_hasDerivAt_of {m q μ E σ : ℝ} {B : Space → Space} {X : ℝ → Space}
    {v : ℝ → ℝ} (h : LittlejohnOrbit m q μ B X v) (hm : m ≠ 0) (hq : q ≠ 0) (hσ : σ ^ 2 = 1)
    {t : ℝ}
    (hu : 0 < 2 * (E - μ * ‖B (X t)‖) / m)
    (hvt : v t = σ * √(2 * (E - μ * ‖B (X t)‖) / m))
    (hn : DifferentiableAt ℝ (fun y => ‖B y‖) (X t)) (hb : DifferentiableAt ℝ (bhat B) (X t)) :
    HasDerivAt X
      ((v t / BstarPar m q B (v t) (X t)) • modFieldFn (rhoE m q μ E σ B) B (X t)) t := by
  set w := √(2 * (E - μ * ‖B (X t)‖) / m)
  have hw : 0 < w := Real.sqrt_pos.2 hu
  have hgr := hasGradientAt_rhoE (q := q) (σ := σ) hm hn hu
  rw [modFieldFn_eq hgr.differentiableAt hb, hgr.gradient]
  have hid := passing_velocity_identity (m := m) (q := q) (μ := μ) (v := v t)
    (r := rhoE m q μ E σ B (X t)) (g := (-(σ * μ) / (q * w)) • gradAbsB B (X t)) B (X t)
    (by rw [rhoE, hvt]; ring)
    (by rw [smul_smul, hvt]; congr 1; field_simp; linear_combination (-μ) * hσ)
  convert h.hX t using 1
  rw [div_eq_inv_mul, ← smul_smul, hid]

/-! ## The local ODE of a Littlejohn orbit -/

section Local

variable {m q μ E : ℝ} {X : ℝ → Space} {v : ℝ → ℝ}

/-- `2(E − μ|B|)/m = (2E/m)(1 − λ|B|)` with `λ = μ/E`. -/
theorem radicand_eq (hE : 0 < E) (nB : ℝ) :
    2 * (E - μ * nB) / m = 2 * E / m * (1 - μ / E * nB) := by
  field_simp

/-- **The local ODE**: on every interval `[a, b] ∋ 0` on which the orbit stays in
`muRegion (μ/E)`, `v_∥ = √(2(E − μ|B|)/m) > 0` and `dX/dt = VmuF(X)`. -/
theorem littlejohn_mu_local (hm : 0 < m) (hq : q ≠ 0) (hE : 0 < E)
    (h : LittlejohnOrbit m q μ (field (1 / 4)) X v)
    (hE0 : hamiltonian m μ (field (1 / 4)) (X 0) (v 0) = E) (hv0 : 0 < v 0) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hXU : ∀ s ∈ Icc a b, X s ∈ muRegion (μ / E)) :
    ∀ s ∈ Icc a b, v s = √(2 * (E - μ * ‖field (1 / 4) (X s)‖) / m) ∧
      HasDerivAt X (VmuF √(2 * E / m) (m / q * √(2 * E / m)) (μ / E) (X s)) s := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (h.hX t).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (h.hv t).continuousAt
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha, hb⟩
  have hlt : ∀ s ∈ Icc a b, μ * ‖field (1 / 4) (X s)‖ < E := fun s hs => by
    have h2 := (hXU s hs).2
    rw [div_mul_eq_mul_div, div_lt_one hE] at h2; exact h2
  -- energy conservation on `[a, b]`
  have hBc : ContinuousOn (fun s => ‖field (1 / 4) (X s)‖) (Icc a b) :=
    ((field_contDiffOn_n (1 / 4) 0).continuousOn.comp hXc.continuousOn
      (fun s hs => (hXU s hs).1.1)).norm
  have hHc : ContinuousOn (fun s => hamiltonian m μ (field (1 / 4)) (X s) (v s)) (Icc a b) := by
    unfold hamiltonian
    exact (((continuous_const.mul (hvc.pow 2)).div_const 2).continuousOn).add
      (continuousOn_const.mul hBc)
  have hHd : ∀ s ∈ Ico a b, HasDerivWithinAt
      (fun s => hamiltonian m μ (field (1 / 4)) (X s) (v s)) 0 (Ici s) s := fun s hs =>
    (hamiltonian_hasDerivAt_of h hm.ne' (differentiableAt_normB
      (hXU s (Ico_subset_Icc_self hs)).1)).hasDerivWithinAt
  have hconst := constant_of_has_deriv_right_zero hHc hHd
  have hH : ∀ s ∈ Icc a b, hamiltonian m μ (field (1 / 4)) (X s) (v s) = E := fun s hs => by
    rw [hconst s hs, ← hconst 0 h0ab, hE0]
  -- `v² = 2(E − μ|B|)/m > 0`
  have hv2 : ∀ s ∈ Icc a b, v s ^ 2 = 2 * (E - μ * ‖field (1 / 4) (X s)‖) / m := fun s hs => by
    have := hH s hs
    unfold hamiltonian at this
    field_simp
    linarith
  have hpos : ∀ s ∈ Icc a b, 0 < 2 * (E - μ * ‖field (1 / 4) (X s)‖) / m := fun s hs => by
    have := hlt s hs
    have : 0 < E - μ * ‖field (1 / 4) (X s)‖ := by linarith
    positivity
  have hne : ∀ s ∈ Icc a b, v s ≠ 0 := fun s hs h0 => by
    have := hv2 s hs; rw [h0] at this; linarith [hpos s hs]
  -- `v > 0` (intermediate value theorem)
  have hvpos : ∀ s ∈ Icc a b, 0 < v s := by
    intro s hs
    by_contra hle
    rw [not_lt] at hle
    rcases le_total 0 s with h0s | hs0
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' h0s hvc.continuousOn ⟨hle, hv0.le⟩
      exact hne r ⟨by linarith [hr.1], by linarith [hr.2, hs.2]⟩ hr0
    · obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hs0 hvc.continuousOn ⟨hle, hv0.le⟩
      exact hne r ⟨by linarith [hr.1, hs.1], by linarith [hr.2]⟩ hr0
  intro s hs
  have hvs : v s = √(2 * (E - μ * ‖field (1 / 4) (X s)‖) / m) := by
    rw [← hv2 s hs, Real.sqrt_sq (hvpos s hs).le]
  refine ⟨hvs, ?_⟩
  have hd := passing_hasDerivAt_of (σ := 1) (E := E) h hm.ne' hq (by norm_num) (hpos s hs)
    (by rw [one_mul]; exact hvs) (differentiableAt_normB (hXU s hs).1)
    (differentiableAt_bhat (hXU s hs).1)
  rw [BstarPar_field, modFieldFn_rhoE_eq hm hq hE (hXU s hs).1 (hlt s hs), hvs,
    radicand_eq hE, Real.sqrt_mul (by positivity)] at hd
  exact hd

/-- **Field lines of `VmuF` are Littlejohn orbits**: a field line `Y` of `VmuF` in
`muRegion (μ/E)`, with `v_∥ = √(2(E − μ|B(Y)|)/m)`, solves the Littlejohn equations. -/
theorem littlejohn_of_fieldLine (hm : 0 < m) (hq : q ≠ 0) (hE : 0 < E) {Y : ℝ → Space}
    (hY : ∀ t, HasDerivAt Y (VmuF √(2 * E / m) (m / q * √(2 * E / m)) (μ / E) (Y t)) t)
    (hYU : ∀ t, Y t ∈ muRegion (μ / E)) :
    LittlejohnOrbit m q μ (field (1 / 4)) Y
      (fun t => √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m)) := by
  have hlt : ∀ t, μ * ‖field (1 / 4) (Y t)‖ < E := fun t => by
    have h2 := (hYU t).2
    rw [div_mul_eq_mul_div, div_lt_one hE] at h2; exact h2
  have hpos : ∀ t, 0 < 2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m := fun t => by
    have := hlt t
    have : 0 < E - μ * ‖field (1 / 4) (Y t)‖ := by linarith
    positivity
  -- the velocity field in Littlejohn form
  have hV : ∀ t, VmuF √(2 * E / m) (m / q * √(2 * E / m)) (μ / E) (Y t) =
      (√(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m) / ‖field (1 / 4) (Y t)‖) •
        modFieldFn (rhoE m q μ E 1 (field (1 / 4))) (field (1 / 4)) (Y t) := fun t => by
    rw [modFieldFn_rhoE_eq hm hq hE (hYU t).1 (hlt t), VmuF, radicand_eq hE,
      Real.sqrt_mul (by positivity)]
  have hgr : ∀ t, HasGradientAt (rhoE m q μ E 1 (field (1 / 4)))
      ((-(1 * μ) / (q * √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m))) •
        gradAbsB (field (1 / 4)) (Y t)) (Y t) := fun t =>
    hasGradientAt_rhoE hm.ne' (differentiableAt_normB (hYU t).1) (hpos t)
  -- `B̃` against the passing identity
  have hmod : ∀ t, modFieldFn (rhoE m q μ E 1 (field (1 / 4))) (field (1 / 4)) (Y t) =
      field (1 / 4) (Y t) + rhoE m q μ E 1 (field (1 / 4)) (Y t) • curlb (field (1 / 4)) (Y t) +
        cross ((-(1 * μ) / (q * √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m))) •
          gradAbsB (field (1 / 4)) (Y t)) (bhat (field (1 / 4)) (Y t)) := fun t => by
    rw [modFieldFn_eq (hgr t).differentiableAt (differentiableAt_bhat (hYU t).1), (hgr t).gradient]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · -- the position equation
    set w := √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m)
    have hw : 0 < w := Real.sqrt_pos.2 (hpos t)
    have hid := passing_velocity_identity (m := m) (q := q) (μ := μ) (v := w)
      (r := rhoE m q μ E 1 (field (1 / 4)) (Y t))
      (g := (-(1 * μ) / (q * w)) • gradAbsB (field (1 / 4)) (Y t)) (field (1 / 4)) (Y t)
      (by rw [rhoE]; ring) (by rw [smul_smul]; congr 1; field_simp)
    have := hY t
    rw [hV t, hmod t, div_eq_inv_mul, ← smul_smul, hid, ← BstarPar_field m q w] at this
    exact this
  · -- the parallel-velocity equation
    set w := √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m)
    have hw : 0 < w := Real.sqrt_pos.2 (hpos t)
    have hwf : (fun t => √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m)) =
        fun t => rhoE m m μ E 1 (field (1 / 4)) (Y t) := by
      funext s; rw [rhoE, div_self hm.ne', mul_one, one_mul]
    have hgw := hasGradientAt_rhoE (q := m) (σ := 1) hm.ne' (differentiableAt_normB (hYU t).1)
      (hpos t)
    have hd := (hgw.hasFDerivAt).comp_hasDerivAt t (hY t)
    rw [hwf]
    convert hd using 1
    · rfl
    rw [InnerProductSpace.toDual_apply_apply, hV t, hmod t, BstarPar_field, Bstar]
    rw [show √(2 * (E - μ * ‖field (1 / 4) (Y t)‖) / m) = w from rfl]
    have hcr : ⟪gradAbsB (field (1 / 4)) (Y t), cross ((-(1 * μ) / (q * w)) •
        gradAbsB (field (1 / 4)) (Y t)) (bhat (field (1 / 4)) (Y t))⟫ = 0 := by
      rw [PlasmaLean.Kinetic.GuidingCentre.cross_smul_left', inner_smul_right,
        PlasmaLean.Kinetic.inner_cross_self, mul_zero]
    have hr : rhoE m q μ E 1 (field (1 / 4)) (Y t) = m * w / q := by rw [rhoE]; ring
    rw [inner_smul_left, inner_smul_right, inner_add_right, hcr, add_zero, hr,
      real_inner_comm (gradAbsB _ _)]
    simp only [RCLike.conj_to_real]
    field_simp

/-- **A `μ > 0` Littlejohn orbit is the trapped field line of `VmuF`**: if the field line `Y` of
`VmuF` from `X 0` stays in a compact `K ⊆ muRegion (μ/E)`, then `X = Y` for all time, and
`v_∥ = √(2(E − μ|B(X)|)/m) > 0` (the orbit is passing). -/
theorem littlejohn_mu_eq_fieldLine (hm : 0 < m) (hq : q ≠ 0) (hE : 0 < E)
    (h : LittlejohnOrbit m q μ (field (1 / 4)) X v)
    (hE0 : hamiltonian m μ (field (1 / 4)) (X 0) (v 0) = E) (hv0 : 0 < v 0) {Y : ℝ → Space}
    {K : Set Space} (hK : IsCompact K) (hKU : K ⊆ muRegion (μ / E))
    (hY : ∀ t, HasDerivAt Y (VmuF √(2 * E / m) (m / q * √(2 * E / m)) (μ / E) (Y t)) t)
    (hYK : ∀ t, Y t ∈ K) (h0 : X 0 = Y 0) :
    X = Y ∧ ∀ t, v t = √(2 * (E - μ * ‖field (1 / 4) (X t)‖) / m) ∧ 0 < v t := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (h.hX t).continuousAt
  have hXY : X = Y := curve_eq_of_local (isOpen_muRegion _) (VmuF_contDiffOn _ _ _) hK hKU hXc hY
    hYK h0
    (fun b hb hU s hs => (littlejohn_mu_local hm hq hE h hE0 hv0 le_rfl hb hU s hs).2)
    (fun a ha hU s hs => (littlejohn_mu_local hm hq hE h hE0 hv0 ha le_rfl hU s hs).2)
  refine ⟨hXY, fun t => ?_⟩
  have hU : ∀ s ∈ Icc (min t 0) (max t 0), X s ∈ muRegion (μ / E) := fun s _ => by
    rw [hXY]; exact hKU (hYK s)
  have ht : t ∈ Icc (min t 0) (max t 0) := ⟨min_le_left _ _, le_max_left _ _⟩
  have hv := (littlejohn_mu_local hm hq hE h hE0 hv0 (min_le_right _ _) (le_max_right _ _) hU t
    ht).1
  refine ⟨hv, ?_⟩
  rw [hv]
  have h2 := (hU t ht).2
  rw [div_mul_eq_mul_div, div_lt_one hE] at h2
  have : 0 < E - μ * ‖field (1 / 4) (X t)‖ := by linarith
  exact Real.sqrt_pos.2 (by positivity)

end Local

end PlasmaLean.Design.RationalStellaratorGC
