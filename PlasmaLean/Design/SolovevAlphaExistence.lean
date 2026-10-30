/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevAlpha
public import PlasmaLean.Design.SolovevOnePlasma
public import PlasmaLean.Theory.Kinetic.LorentzExistence

/-!
# 3.5 MeV alpha orbits of the reactor Solov'ev field exist for all time (audit finding MA-M2)

`SolovevAlpha.reactor_alpha_confined` says that *every* Newton–Lorentz orbit of an alpha with
energy at most 3.5 MeV born in `ψ̃ ≤ ψ̃_e/4` stays confined for all real times. Until now the only
orbit shown to satisfy the hypotheses was the alpha at rest on the axis
(`reactor_alpha_confined_nonvacuous`). This file proves that the hypotheses are satisfied by an
orbit through **every** admissible initial condition.

The Solov'ev field `B = ∇Ψ × ∇φ + F ∇φ` is singular on the vertical axis `R = 0`
(`∇φ = (-y, x, 0)/R²`), so it is only `C¹` on `{R² ≠ 0}` (`field_contDiffOn`), and the
global existence theorem of `LorentzExistence` for globally `C¹` fields does not apply
directly. Instead, the confinement argument itself (conservation of canonical momentum and
speed, now on closed time intervals: `orbit_trapped_Icc`) traps every interval solution in
the compact set `{ψ̃ ≤ 11 L⁴/192} × closedBall 0 |v₀|`, which lies in `R² ≥ L²/2`
(`solovev_apriori`). The continuation theorem `lorentzOrbit_exists_of_apriori` then gives
the global orbit.

Results:

* `solovev_orbit_exists`: under the rigidity and birth hypotheses of `Solovev.orbit_confined`,
  a Lorentz orbit through `(x₀, v₀)` exists for all real times;
* **`reactor_alpha_orbit_exists`**: for every alpha mass and charge in the stated ranges, every
  initial position with `ψ̃ ≤ ψ̃_e/4` and every initial velocity of kinetic energy at most
  3.5 MeV (any pitch), there is a Lorentz orbit of `reactorField` for all real times;
* **`reactor_alpha_born_confined`**: for the same data, such an orbit exists **and** every such
  orbit satisfies `ψ̃ ≤ (11/12) ψ̃_e`, `R² ≥ 50` for all real times;
* **`reactor_alpha_confined_nonvacuous_35MeV`**: an explicit witness at exactly 3.5 MeV (rounded
  constants), born on the magnetic axis, confined for all time;
* `reactor_alpha_orbit_exists_label`: the same in the flux-label form `label x₀ ≤ 3/11` used by
  the alpha conjunct of `solovev_one_plasma_*`, so that conjunct is non-vacuous at 3.5 MeV;
* sanity: `reactor_alpha_orbit_exists_rest` recovers the old rest-orbit case from the new
  theorem (degenerate case).

Scope: as in `SolovevAlpha` (exact axisymmetric equilibrium, static fields, non-relativistic
collisionless full orbits). Uniqueness of the orbit is not stated.
-/

public section
noncomputable section
namespace PlasmaLean.Design.SolovevAlpha
open PlasmaLean.Fields PlasmaLean.Fields.ODEGlobal PlasmaLean.Kinetic PlasmaLean.Design.Solovev
  Set WithLp

/-- The complement of the vertical axis is open. -/
theorem isOpen_offAxis : IsOpen {x : Space | R2 x ≠ 0} := by
  have hc : Continuous R2 := continuous_iff_continuousAt.mpr fun x => by
    unfold R2
    exact ((((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).continuous.pow 2).add
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).continuous.pow 2))).continuousAt
  exact isOpen_ne_fun hc continuous_const

/-- The Solov'ev field is `C¹` off the vertical axis. -/
theorem field_contDiffOn (A L F : ℝ) : ContDiffOn ℝ 1 (field A L F) {x | R2 x ≠ 0} := by
  have hc : ∀ j : Fin 3, ContDiff ℝ 1 (fun y : Space => y j) := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).contDiff
  have hR : ContDiffOn ℝ 1 R2 {x | R2 x ≠ 0} := by
    have : ContDiff ℝ 1 (fun y : Space => y 0 ^ 2 + y 1 ^ 2) := ((hc 0).pow 2).add ((hc 1).pow 2)
    exact this.contDiffOn
  obtain ⟨e0, e1, e2⟩ := field_coords A L F
  refine contDiffOn_piLp' 2 fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [e0]
    exact ((contDiffOn_const.mul ((hc 0).mul (hc 2)).contDiffOn).neg).sub
      ((contDiffOn_const.mul (hc 1).contDiffOn).div hR fun x hx => hx)
  · simp only [Fin.mk_one]
    rw [e1]
    exact ((contDiffOn_const.mul ((hc 1).mul (hc 2)).contDiffOn).neg).add
      ((contDiffOn_const.mul (hc 0).contDiffOn).div hR fun x hx => hx)
  · simp only [Fin.reduceFinMk]
    rw [e2]
    exact (contDiffOn_const.mul ((((hc 2).pow 2).contDiffOn.add hR).sub contDiffOn_const))

/-- The sublevel set `{ψ̃ ≤ c}` with `c ≤ L⁴/16` is compact. -/
theorem isCompact_psiT_le {L c : ℝ} (hL : 0 < L) (hc : c ≤ L ^ 4 / 16) :
    IsCompact {x : Space | psiT L x ≤ c} := by
  have hcont : Continuous (psiT L) :=
    continuous_iff_continuousAt.mpr fun x => (psiT_hasFDerivAt L x).continuousAt
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const)
    ((Metric.isBounded_closedBall (x := (0 : Space)) (r := 4 * L / 3)).subset fun x hx => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact region_norm hL x (le_trans hx hc)

/-- **A priori bound for the Solov'ev field.** Under the hypotheses of `orbit_confined`, every
solution of the Newton–Lorentz system from `(x₀, v₀)` on a finite interval stays in the compact set
`{ψ̃ ≤ 11 L⁴/192} × closedBall 0 |v₀|`, which lies off the vertical axis. -/
theorem solovev_apriori {A L F m q : ℝ} (hA : 0 < A) (hL : 0 < L) (hm : m ≠ 0) (hq : q ≠ 0)
    {x₀ v₀ : Space} (hrig : |m| * ‖v₀‖ ≤ |q| * (A * L / 64)) (hψ0 : psiT L x₀ ≤ L ^ 4 / 64) :
    APrioriBounded (lorentzField m q (field A L F)) ({x | R2 x ≠ 0} ×ˢ univ) (x₀, v₀) := by
  have hL4 : 0 < L ^ 4 := by positivity
  have hx0 : ‖x₀‖ ≤ 4 * L / 3 := region_norm hL x₀ (by linarith)
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hc : 0 < A / L ^ 2 := by positivity
  have hk : |m| * ‖v₀‖ / |q| ≤ A * L / 64 := by
    rw [div_le_iff₀ hqpos]; linarith
  have hgap : flux A L x₀ + |m| * ‖v₀‖ / |q| * (4 * L / 3 + ‖x₀‖) ≤
      A / L ^ 2 * (11 * L ^ 4 / 192) := by
    have h1 : |m| * ‖v₀‖ / |q| * (4 * L / 3 + ‖x₀‖) ≤ A * L / 64 * (8 * L / 3) :=
      mul_le_mul hk (by linarith) (by positivity) (by positivity)
    have h2 : flux A L x₀ ≤ A / L ^ 2 * (L ^ 4 / 64) :=
      mul_le_mul_of_nonneg_left hψ0 hc.le
    have e1 : A / L ^ 2 * (L ^ 4 / 64) = A * L ^ 2 / 64 := by field_simp
    have e2 : A / L ^ 2 * (11 * L ^ 4 / 192) = 11 * (A * L ^ 2) / 192 := by field_simp
    rw [e2]; rw [e1] at h2; nlinarith
  have hreg : ∀ y, flux A L y ≤ A / L ^ 2 * (L ^ 4 / 16) → ‖y‖ ≤ 4 * L / 3 := fun y hy =>
    region_norm hL y (le_of_mul_le_mul_left hy hc)
  have hlt : A / L ^ 2 * (11 * L ^ 4 / 192) < A / L ^ 2 * (L ^ 4 / 16) :=
    mul_lt_mul_of_pos_left (by nlinarith) hc
  intro T
  refine ⟨{x | psiT L x ≤ 11 * L ^ 4 / 192} ×ˢ Metric.closedBall 0 ‖v₀‖,
    (isCompact_psiT_le hL (by nlinarith)).prod (isCompact_closedBall _ _), ?_,
    fun c hc' γ h0 hγ t ht => ?_⟩
  · rintro ⟨x, v⟩ ⟨hx, -⟩
    refine ⟨?_, mem_univ v⟩
    have := (region_bounds hL x (le_trans hx (by nlinarith))).1
    change R2 x ≠ 0
    have : 0 < L ^ 2 / 2 := by positivity
    linarith
  · have h0m : (0 : ℝ) ∈ Icc (-c) c := ⟨by linarith [hc'.1], hc'.1⟩
    have hγ0 : (γ 0).1 = x₀ ∧ (γ 0).2 = v₀ := by rw [h0]; exact ⟨rfl, rfl⟩
    have hgap' : flux A L (γ 0).1 + |m| * ‖(γ 0).2‖ / |q| * (4 * L / 3 + ‖(γ 0).1‖) ≤
        A / L ^ 2 * (11 * L ^ 4 / 192) := by rw [hγ0.1, hγ0.2]; exact hgap
    have hp := orbit_trapped_Icc hm hq (flux_hasFDerivAt A L) (field_axisymmetric A L F) hlt
      (by positivity) hreg (by linarith [hc'.1]) hc'.1 hγ hgap' t ht
    refine ⟨le_of_mul_le_mul_left hp hc, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, speed_eq_Icc hγ ht h0m, hγ0.2]

/-- **Existence of Solov'ev orbits for all time.** Under the rigidity and birth hypotheses of
`orbit_confined` (`|m| |v₀| ≤ |q| A L / 64`, `ψ̃(x₀) ≤ L⁴/64`), there is a Newton–Lorentz orbit of
the Solov'ev field defined for all real times with `x 0 = x₀`, `v 0 = v₀`. -/
theorem solovev_orbit_exists {A L F m q : ℝ} (hA : 0 < A) (hL : 0 < L) (hm : m ≠ 0)
    (hq : q ≠ 0) {x₀ v₀ : Space} (hrig : |m| * ‖v₀‖ ≤ |q| * (A * L / 64))
    (hψ0 : psiT L x₀ ≤ L ^ 4 / 64) :
    ∃ x v : ℝ → Space, LorentzOrbit m q (fun _ => 0) (field A L F) x v ∧ x 0 = x₀ ∧
      v 0 = v₀ := by
  have hx₀ : R2 x₀ ≠ 0 := by
    have := (region_bounds hL x₀ (by nlinarith [pow_pos hL 4])).1
    have : 0 < L ^ 2 / 2 := by positivity
    linarith
  exact lorentzOrbit_exists_of_apriori hm isOpen_offAxis (field_contDiffOn A L F) hx₀
    (solovev_apriori hA hL hm hq hrig hψ0)

/-- **3.5 MeV alpha orbits exist for all time.** For every alpha mass
`m ∈ [6.6446e-27, 6.6448e-27] kg` and charge `2e` (`e ∈ [1.6021e-19, 1.6023e-19] C`), every
initial position with `ψ̃ ≤ ψ̃_e/4` and every initial velocity of kinetic energy at most 3.5 MeV
(any direction), there is a Newton–Lorentz orbit of `reactorField` defined for all real times. -/
theorem reactor_alpha_orbit_exists {m e : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6448e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x₀ v₀ : Space}
    (hK : m * ‖v₀‖ ^ 2 ≤ 2 * (3.5e6 * e)) (hψ0 : psiT 10 x₀ ≤ 10 ^ 4 / 16 / 4) :
    ∃ x v : ℝ → Space, LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v ∧ x 0 = x₀ ∧
      v 0 = v₀ := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have he : 0 < e := lt_of_lt_of_le (by norm_num) he1
  exact solovev_orbit_exists (A := 7 / 4) (L := 10) (F := 50) (by norm_num) (by norm_num)
    hm.ne' (by positivity) (alpha35_rigidity hm1 hm2 he1 he2 (norm_nonneg _) hK)
    (by linarith)

/-- **Every 3.5 MeV alpha born in the core has an orbit, and every such orbit is confined
forever.** For alpha data in the stated ranges, an initial position with `ψ̃ ≤ ψ̃_e/4` and an
initial velocity of kinetic energy at most 3.5 MeV: a Lorentz orbit of `reactorField` through
`(x₀, v₀)` exists for all real times, and every such orbit satisfies `ψ̃ ≤ (11/12) ψ̃_e` and
`R² ≥ 50` at every real time. -/
theorem reactor_alpha_born_confined {m e : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6448e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x₀ v₀ : Space}
    (hK : m * ‖v₀‖ ^ 2 ≤ 2 * (3.5e6 * e)) (hψ0 : psiT 10 x₀ ≤ 10 ^ 4 / 16 / 4) :
    (∃ x v : ℝ → Space, LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v ∧ x 0 = x₀ ∧
      v 0 = v₀) ∧
    ∀ x v : ℝ → Space, LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v → x 0 = x₀ →
      v 0 = v₀ → ∀ t, psiT 10 (x t) ≤ 11 / 12 * (10 ^ 4 / 16) ∧ 50 ≤ R2 (x t) := by
  refine ⟨reactor_alpha_orbit_exists hm1 hm2 he1 he2 hK hψ0, fun x v h hx hv t => ?_⟩
  subst hx hv
  exact reactor_alpha_confined hm1 hm2 he1 he2 h hK hψ0 t

/-- The speed of a 3.5 MeV alpha with the rounded constants. -/
@[expose] def alpha35Speed : ℝ := Real.sqrt (2 * (3.5e6 * 1.6022e-19) / 6.6447e-27)

/-- The initial velocity `alpha35Speed · e_x`. -/
@[expose] def alpha35Velocity : Space := toLp 2 ![alpha35Speed, 0, 0]

/-- The initial velocity `alpha35Velocity` carries exactly 3.5 MeV of kinetic energy:
`m |v₀|² = 2 · 3.5 MeV`. -/
theorem alpha35Velocity_energy :
    6.6447e-27 * ‖alpha35Velocity‖ ^ 2 = 2 * (3.5e6 * 1.6022e-19) := by
  have hn : ‖alpha35Velocity‖ ^ 2 = alpha35Speed ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [alpha35Velocity, Fin.sum_univ_three]
  rw [hn, alpha35Speed, Real.sq_sqrt (by norm_num)]
  field_simp

/-- **Non-vacuity at the advertised energy.** There is a 3.5 MeV alpha (exactly, rounded
constants) born on the magnetic axis whose Newton–Lorentz orbit of `reactorField` exists for all
real times and satisfies all hypotheses of `reactor_alpha_confined`; it stays confined
(`ψ̃ ≤ (11/12) ψ̃_e`, `R² ≥ 50`) for every real time. -/
theorem reactor_alpha_confined_nonvacuous_35MeV :
    ∃ (m e : ℝ) (x v : ℝ → Space), 6.6446e-27 ≤ m ∧ m ≤ 6.6448e-27 ∧ 1.6021e-19 ≤ e ∧
      e ≤ 1.6023e-19 ∧ LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v ∧
      m * ‖v 0‖ ^ 2 = 2 * (3.5e6 * e) ∧ psiT 10 (x 0) ≤ 10 ^ 4 / 16 / 4 ∧
      ∀ t, psiT 10 (x t) ≤ 11 / 12 * (10 ^ 4 / 16) ∧ 50 ≤ R2 (x t) := by
  have hψ0 : psiT 10 (toLp 2 ![10, 0, 0] : Space) ≤ 10 ^ 4 / 16 / 4 := by
    rw [reactor_axis_psi]; norm_num
  obtain ⟨⟨x, v, h, hx, hv⟩, hconf⟩ := reactor_alpha_born_confined (m := 6.6447e-27)
    (e := 1.6022e-19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    alpha35Velocity_energy.le hψ0
  refine ⟨6.6447e-27, 1.6022e-19, x, v, by norm_num, by norm_num, by norm_num, by norm_num, h,
    by rw [hv]; exact alpha35Velocity_energy, by rw [hx]; exact hψ0, hconf x v h hx hv⟩

/-- **Existence in the flux-label form of `solovev_one_plasma_*`.** For alpha data in the stated
ranges, every initial position with flux label `label x₀ ≤ 3/11` (birth in the core) and every
initial velocity of kinetic energy at most 3.5 MeV start a Lorentz orbit of `reactorField` for
all real times; the alpha conjunct of `solovev_one_plasma`, `…_actual`, `…_highQ_actual`,
`…_ignited_actual` and `…_actual_coarea` therefore applies to genuine 3.5 MeV orbits. -/
theorem reactor_alpha_orbit_exists_label {m e : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6448e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x₀ v₀ : Space}
    (hK : m * ‖v₀‖ ^ 2 ≤ 2 * (3.5e6 * e)) (hs0 : SolovevOnePlasma.label x₀ ≤ 3 / 11) :
    ∃ x v : ℝ → Space, LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v ∧ x 0 = x₀ ∧
      v 0 = v₀ :=
  reactor_alpha_orbit_exists hm1 hm2 he1 he2 hK
    (by have := (SolovevOnePlasma.birth_in_core_iff x₀).1 hs0; linarith)

/-- Sanity (degenerate case): at zero velocity on the magnetic axis the new existence theorem
applies as well (the old rest-orbit witness `axis_rest_orbit` is one such orbit). -/
theorem reactor_alpha_orbit_exists_rest :
    ∃ x v : ℝ → Space, LorentzOrbit 6.6447e-27 (2 * 1.6022e-19) (fun _ => 0) reactorField x v ∧
      x 0 = toLp 2 ![10, 0, 0] ∧ v 0 = 0 :=
  reactor_alpha_orbit_exists (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp; norm_num) (by rw [reactor_axis_psi]; norm_num)

end PlasmaLean.Design.SolovevAlpha
