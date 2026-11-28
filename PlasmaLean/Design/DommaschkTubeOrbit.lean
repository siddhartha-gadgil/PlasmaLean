/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkTubeDrift
public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnLocal
public import PlasmaLean.Theory.Kinetic.BoozerGCForward

/-!
# Existence of the QA2R guiding-centre orbit in a certified tube

`DommaschkTubeDrift.stays_in_tube` controls every Littlejohn guiding-centre orbit on `[0, T]`
born in the tube of a chain. Here the orbit is shown to exist on the whole of `[0, T]`, under
the same hypotheses.

* `side_conditions_mono`: the conditions of `stays_in_tube` that involve the time hold for
  every earlier time (`0 ≤ κ` follows from the other hypotheses). The constants are those of
  `stays_in_tube`: the speed bound `M` and the bound `cφ` of the toroidal component on the
  tube, and the drift bound with the energy factor `2H - μ bT`.
* `state_mem`: every partial orbit on `[0, t]`, `t ≤ T`, has its position in the image of the
  compact core window and parallel speed at most `vpar` (energy conservation with `bT ≤ |B|`).
* `birth_mem`: the state at birth satisfies the same bounds.
* `exists_orbit`: a Littlejohn orbit on `[0, T]` exists, by forward continuation
  (`Fields.ODEGlobal.exists_forward_of_apriori`) in the open set of states with position off
  the axis and nonvanishing field, where the Littlejohn right-hand side is `C¹`.
* `exists_orbit_stays_in_tube`: the orbit together with the conclusion of `stays_in_tube`.

**Sanity.** `orbit_zero` is the affine orbit on `[0, 0]`, the degenerate instance of the model
used for the state at birth. No concrete chain is constructed here.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkTubeOrbit

open Certificates PositionFrameSlabs PositionFrameTube DommaschkJacobian DommaschkTubeCheck
open DommaschkTubeSymmetry DommaschkSignedTraceDomain DommaschkJacobianReflection Fields Set
open Contract Kinetic Kinetic.GCLittlejohn
open DommaschkCartesianAngleFlow DommaschkCylindricalDrift DommaschkTubeDrift
open DommaschkKam (cylBphi)

/-- **The affine orbit on `[0, 0]`.** The affine path through the state at birth with the
Littlejohn velocity there is an orbit on the degenerate interval, for any field. -/
theorem orbit_zero (F : Space → Space) (m q : ℝ) (bth : GCBirth) :
    GCBirthOrbitOn F m q bth (fun s : ℝ => (bth.1, bth.2.1) +
      s • littlejohnVelocity F m q bth.2.2 (bth.1, bth.2.1)) 0 := by
  refine ⟨by simp, fun s hs => ?_⟩
  obtain rfl : s = 0 := le_antisymm hs.2 hs.1
  have d := ((hasDerivAt_id (0 : ℝ)).smul_const
    (littlejohnVelocity F m q bth.2.2 (bth.1, bth.2.1))).const_add (bth.1, bth.2.1)
  simpa using d

section Orbit

variable {s₀ e : State} {rows : List Step} {bs : List ℕ} {E Bq : ℚ}
  {m q g bT cφ M κ r vpar b' T θ₀ R₀ z₀ : ℝ} {bth : GCBirth}
  (ch : Chain s₀ e rows bs E Bq) (hsec : sectionCheck rows bs = true) (hbT : 0 < bT)
  (hfield : ∀ t ∈ Ioo (-stop rows) (stop rows), ∀ x ∈ outerD s₀ rows t,
    ‖gradAbsB B (cylPoint (x 0) t (x 1))‖ ≤ g ∧ bT ≤ ‖B (cylPoint (x 0) t (x 1))‖ ∧
      cylBphi (x 0) t (x 1) ≤ cφ ∧ ‖euclideanFlow 0 1 t x‖ ≤ M)
  (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ bth.2.2) (start : bth.1 = cylPoint R₀ θ₀ z₀)
  (hp₀ : ((θ₀, WithLp.toLp 2 ![R₀, z₀]) : ℝ × Plane) ∈
    FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs))
  (hT : 0 ≤ T)
  (hκ : labelConstant E Bq * (1 + M) * (8 / 7 *
    ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) / (|q| * bT ^ 2) * g)) ≤ κ)
  (hstart : ‖Lab s₀ rows (θ₀, WithLp.toLp 2 ![R₀, z₀]) - point s₀.point‖ ≤ r)
  (hball : r + κ * T + 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 ≤ s₀.radius / 2 ^ 80)
  (hvpar : 2 * (hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) ≤ m * vpar ^ 2)
  (hvpar0 : 0 ≤ vpar)
  (hwin : |θ₀| + (vpar / bT * (cφ / (7 / 8)) + 8 / 7 *
    ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) / (|q| * bT ^ 2) * g)) * T ≤ b')
  (hb' : b' < stop rows)

include ch hbT hfield hm hq hμ start hp₀ hκ hball hvpar0 hwin in
/-- **The side conditions hold at earlier times.** Under the hypotheses of `stays_in_tube`,
`κ` is nonnegative, and the conditions on the label ball and on the window of angles hold with
any `t ∈ [0, T]` in place of `T`. -/
theorem side_conditions_mono {t : ℝ} (ht : t ∈ Icc 0 T) :
    0 ≤ κ ∧ r + κ * t + 2 * |(s₀.point.y : ℝ)| / 2 ^ 80 ≤ s₀.radius / 2 ^ 80 ∧
      |θ₀| + (vpar / bT * (cφ / (7 / 8)) + 8 / 7 *
        ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) / (|q| * bT ^ 2) * g)) * t ≤
          b' := by
  have tb := tube ch
  have hC : 0 ≤ labelConstant E Bq := le_trans zero_le_one tb.one_le
  obtain ⟨hg, hcφ, hM, hc0⟩ := constants_nonneg ch hbT hfield hm hq hμ start hp₀
  set D := 8 / 7 *
    ((2 * hamiltonian m bth.2.2 B bth.1 bth.2.1 - bth.2.2 * bT) / (|q| * bT ^ 2) * g) with hD
  have hD0 : 0 ≤ D := mul_nonneg (by norm_num) (mul_nonneg hc0 hg)
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hL0 : 0 ≤ vpar / bT * (cφ / (7 / 8)) + D := by positivity
  have h1 := mul_le_mul_of_nonneg_left ht.2 hκ0
  have h2 := mul_le_mul_of_nonneg_left ht.2 hL0
  exact ⟨hκ0, by linarith, by linarith⟩

include ch hsec hbT hfield hm hq hμ start hp₀ hκ hstart hball hvpar hvpar0 hwin hb'

/-- **A-priori bound for partial orbits.** Under the hypotheses of `stays_in_tube`, every
Littlejohn orbit on `[0, t]`, `t ≤ T`, has its position in the image of the core window and
parallel speed at most `vpar` at the times of `[0, t]`. -/
theorem state_mem {t : ℝ} (ht : t ∈ Icc 0 T) {z : ℝ → Space × ℝ}
    (orbit : GCBirthOrbitOn B m q bth z t) : ∀ s ∈ Icc 0 t,
      (z s).1 ∈ (fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) '' window s₀ rows b' ∧
        |(z s).2| ≤ vpar := by
  obtain ⟨-, hball', hwin'⟩ :=
    side_conditions_mono ch hbT hfield hm hq hμ start hp₀ hκ hball hvpar0 hwin ht
  have tb := tube ch
  have e0 : (2 : ℝ) * 0 - stop rows = -stop rows := by ring
  obtain ⟨X, -, h⟩ := stays_in_tube ch hsec hbT hfield hm hq hμ start hp₀ orbit ht.1 hκ hstart
    hball' hvpar hvpar0 hwin' hb'
  have reg : ∀ τ ∈ Icc 0 t, (z τ).1 ∈ regular := by
    intro τ hτ
    obtain ⟨hpt, hreg, -⟩ := h τ hτ
    rw [hpt]
    exact in_regular (region_of_outerD ch (tb.subset hreg.1 hreg.2)) _
  have energy := CylindricalDrift.hamiltonian_eq_birth hm.ne' orbit (fun τ hτ =>
    ((DommaschkRegionRegularity.contDiffAt_domain (reg τ hτ).1).differentiableAt
      (by norm_num)).norm ℝ (field_ne_zero (reg τ hτ)))
  intro s hs
  obtain ⟨hpt, hreg, hcore, habs, -⟩ := h s hs
  refine ⟨⟨X s, ⟨abs_le.mp habs, hcore⟩, hpt.symm⟩, ?_⟩
  have hstr : bT ≤ ‖B (z s).1‖ := by
    rw [hpt]
    exact (hfield (X s).1 (e0 ▸ hreg.1) (X s).2 (tb.subset hreg.1 hreg.2)).2.1
  refine abs_le_of_sq_le_sq ?_ hvpar0
  have hE : m * (z s).2 ^ 2 / 2 + bth.2.2 * ‖B (z s).1‖ =
      hamiltonian m bth.2.2 B bth.1 bth.2.1 := energy s hs
  have := mul_le_mul_of_nonneg_left hstr hμ
  have : m * (z s).2 ^ 2 ≤ m * vpar ^ 2 := by linarith
  exact le_of_mul_le_mul_left this hm

include hT

/-- **The state at birth.** Under the hypotheses of `stays_in_tube`, the position at birth lies
in the image of the core window and the parallel speed at birth is at most `vpar`. -/
theorem birth_mem :
    bth.1 ∈ (fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) '' window s₀ rows b' ∧
      |bth.2.1| ≤ vpar := by
  have h := state_mem ch hsec hbT hfield hm hq hμ start hp₀ hκ hstart hball hvpar hvpar0 hwin hb'
    (left_mem_Icc.mpr hT) (orbit_zero B m q bth) 0 (left_mem_Icc.mpr le_rfl)
  simpa using h

/-- **Existence of the orbit.** Under the hypotheses of `stays_in_tube` (without the orbit), a
Littlejohn guiding-centre orbit in the QA2R field with the given birth exists on `[0, T]`. -/
theorem exists_orbit : ∃ z : ℝ → Space × ℝ, GCBirthOrbitOn B m q bth z T := by
  have vac := DommaschkQA2R.field_vacuum DommaschkQA2R.candidate
  have op := (VacuumLittlejohnLocal.isOpen_regular vac).prod (isOpen_univ (X := ℝ))
  have compact : IsCompact (((fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) ''
      window s₀ rows b') ×ˢ Icc (-vpar) vpar) :=
    ((isCompact_window ch hsec hb').image continuous_cylPoint).prod isCompact_Icc
  have sub : ((fun p : ℝ × Plane => cylPoint (p.2 0) p.1 (p.2 1)) '' window s₀ rows b') ×ˢ
      Icc (-vpar) vpar ⊆ VacuumLittlejohnLocal.regular B CylAlgebra.domain ×ˢ univ := by
    rintro ⟨x, v⟩ ⟨⟨p, hp, rfl⟩, -⟩
    have hx := in_regular (region_of_window ch hsec hb' hp) p.1
    exact ⟨⟨hx.1, field_ne_zero hx⟩, mem_univ v⟩
  have birth := birth_mem ch hsec hbT hfield hm hq hμ start hp₀ hT hκ hstart hball hvpar hvpar0
    hwin hb'
  obtain ⟨z, hz0, hz⟩ := ODEGlobal.exists_forward_of_apriori op
    (VacuumLittlejohnLocal.velocity_smooth vac m q bth.2.2)
    compact sub (x₀ := (bth.1, bth.2.1)) (sub ⟨birth.1, abs_le.mp birth.2⟩) hT
    (fun t ht γ h0 hγ s hs => by
      have h := state_mem ch hsec hbT hfield hm hq hμ start hp₀ hκ hstart hball hvpar hvpar0
        hwin hb' ht (z := γ) ⟨h0, hγ⟩ s hs
      exact ⟨h.1, abs_le.mp h.2⟩)
  exact ⟨z, hz0, hz⟩

/-- **A QA2R guiding centre born in the tube exists on `[0, T]` and stays in the tube.** Under
the hypotheses of `stays_in_tube` (without the orbit) there are a Littlejohn guiding-centre
orbit on `[0, T]` with the given birth and a lifted path of it that stays in the region of the
tube, in the doubled core and in the window of angles `[-b', b']`, with its label moving by at
most `κ t`. -/
theorem exists_orbit_stays_in_tube :
    ∃ (z : ℝ → Space × ℝ) (X : ℝ → ℝ × Plane), GCBirthOrbitOn B m q bth z T ∧
      X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ t ∈ Icc 0 T,
      (z t).1 = cylPoint ((X t).2 0) (X t).1 ((X t).2 1) ∧
      X t ∈ FlowLabel.region (2 * 0 - stop rows) (stop rows) (innerD s₀ rows bs) ∧
      (X t).2 ∈ coreD flipIso s₀ 0 rows (X t).1 ∧ |(X t).1| ≤ b' ∧
      ‖Lab s₀ rows (X t) - Lab s₀ rows (θ₀, WithLp.toLp 2 ![R₀, z₀])‖ ≤ κ * t := by
  obtain ⟨z, orbit⟩ := exists_orbit ch hsec hbT hfield hm hq hμ start hp₀ hT hκ hstart hball
    hvpar hvpar0 hwin hb'
  obtain ⟨X, hX0, h⟩ := stays_in_tube ch hsec hbT hfield hm hq hμ start hp₀ orbit hT hκ hstart
    hball hvpar hvpar0 hwin hb'
  exact ⟨z, X, orbit, hX0, h⟩

end Orbit

end PlasmaLean.Design.DommaschkTubeOrbit
