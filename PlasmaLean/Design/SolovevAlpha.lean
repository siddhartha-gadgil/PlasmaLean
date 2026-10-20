/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.Solovev

/-!
# 3.5 MeV fusion alphas confined for all time in a reactor-scale Solov'ev equilibrium

We take the exact Solov'ev family of `PlasmaLean.Design.Solovev`
(`ψ̃ = R² z²/2 + (R² - L²)²/4`, `B = (A/L²) ∇ψ̃ × ∇φ + F ∇φ`, `p = p₀ - 3 (A/L²)² ψ̃ / μ₀`)
at the reactor-scale parameters

  `L = 10 m`, `A = 7/4 T`, `F = 50 T m`, `p₀ = 3 A² / (16 μ₀) = 147 / (256 μ₀)`.

The plasma region is `ψ̃ ≤ ψ̃_e := L⁴/16 = 625 m⁴`, where the pressure is nonnegative.

Proved here (rigorous, standard axioms only):

* `reactor_force_balance`: the kernel law `ForceBalance` (`J × B = ∇p`, actual Ampère current
  and actual pressure gradient) at every point off the vertical axis, for every `μ₀ ≠ 0`;
* `reactor_pressure_nonneg`, `reactor_pressure_pos`: `p ≥ 0` on the plasma region and
  `p ≥ p₀/12 > 0` on `ψ̃ ≤ (11/12) ψ̃_e`;
* `reactor_axis_field`: `B = 5 T` exactly on the magnetic axis `(10, 0, 0)`;
* `reactor_beta`: `β_axis = 2 μ₀ p₀ / B_axis² = 147/3200 ≈ 4.6%` exactly;
* `reactor_axis_pressure`: `456,900 Pa ≤ p₀ ≤ 457,000 Pa` for `μ₀ ∈ [1.2566e-6, 1.2567e-6]`;
* `reactor_region_bounds`: the plasma region lies in `50 ≤ R² ≤ 150`, `z² ≤ 25`
  (so `7.07 m ≤ R ≤ 12.25 m`, minor radius `a = (√150 - √50)/2 ≈ 2.59 m`), and the midplane
  points `R² = 50`, `R² = 150` lie on the boundary `ψ̃ = ψ̃_e` (`reactor_edge_points`);
* `reactor_alpha_confined` (main result): for every alpha mass
  `m ∈ [6.6446e-27, 6.6448e-27] kg`, elementary charge `e ∈ [1.6021e-19, 1.6023e-19] C`
  (charge `2e`), and initial kinetic energy at most `3.5 MeV = 3.5e6 e J`, every full
  Newton–Lorentz orbit starting in `ψ̃ ≤ ψ̃_e/4` satisfies `ψ̃ ≤ (11/12) ψ̃_e` and `R² ≥ 50`
  for ALL real times `t`, hence stays in the plasma region with positive pressure;
* `alpha35_rigidity`: the key rigidity lemma `m ‖v‖ ≤ 2e · A L / 64 = 2e · 0.2734375`
  (the actual rigidity is `≈ 0.26940 T m`, a 1.5% margin);
* rejected fixtures: `iter_like_alpha35_rejected` (the `iter_like` instance `L = 6`,
  `A = 7/5` violates the rigidity hypothesis for every 3.5 MeV alpha) and
  `reactor_alpha37_rejected` (the reactor instance's hypothesis fails at 3.7 MeV, showing
  the margin is genuinely thin).

Numerical only (NOT proved in Lean; from quadrature in `notes/theory/guiding-centre-averaging.md`
§3.2, rechecked by midpoint quadrature): plasma current
`I_p = (3 A / (μ₀ L²)) ∫_region R dR dz ≈ 11.9 MA`; edge safety factor `q_edge ≈ 2.65`
(field-line quadrature); volume-averaged `⟨β⟩ ≈ 2.2%`; the birth region `ψ̃ ≤ ψ̃_e/4` carries
`≈ 57%` of the fusion power for a `P_fus ∝ p²` birth profile. The on-axis safety factor formula
`q₀ = (F/L)/(√2 A)` is derived informally from the on-axis linearization; only the arithmetic
enclosure `2.02 ≤ q₀ ≤ 2.021` of that expression is proved (`reactor_q0_formula_bounds`).

Scope: this is an exact axisymmetric Solov'ev equilibrium (tokamak-like, NOT a
stellarator). Fields are static, the model is collisionless and non-relativistic, and the
dynamics is the full-orbit Newton–Lorentz equation (no guiding-centre approximation).
Orbits are supplied (existence is not constructed). The pressure formula continues to
negative values outside the plasma region; the field is not matched to coils or a vacuum
region, and no MHD or kinetic stability claim is made.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.SolovevAlpha
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Design.Solovev WithLp

/-- The reactor-scale Solov'ev field: `L = 10 m`, `A = 7/4 T`, `F = 50 T m`. -/
@[expose] def reactorField : Space → Space := field (7 / 4) 10 50

/-- The reactor-scale pressure with `p₀ = 3 A² / (16 μ₀)` (vanishing on `ψ̃ = L⁴/16`). -/
@[expose] def reactorPressure (μ₀ : ℝ) : Space → ℝ :=
  pressure μ₀ (3 * (7 / 4) ^ 2 / (16 * μ₀)) (7 / 4) 10

/-! ## The equilibrium -/

/-- Force balance `J × B = ∇p` (the kernel law) for the reactor instance at every point off
the vertical axis, with the actual Ampère current and actual pressure gradient. -/
theorem reactor_force_balance (μ₀ : ℝ) (hμ : μ₀ ≠ 0) {x : Space} (hx : R2 x ≠ 0) :
    ForceBalance (ofLp (reactorField x)) (ofLp (current μ₀ (7 / 4) 10 50 x))
      (ofLp (pressureGrad μ₀ (7 / 4) 10 x)) :=
  force_balance μ₀ (7 / 4) 10 50 hμ hx

/-- The pressure gradient used in `reactor_force_balance` is the actual gradient of
`reactorPressure`. -/
theorem reactor_pressure_hasFDerivAt (μ₀ : ℝ) (x : Space) :
    HasFDerivAt (reactorPressure μ₀) (innerSL ℝ (pressureGrad μ₀ (7 / 4) 10 x)) x :=
  pressure_hasFDerivAt _ _ _ _ x

/-- `∇ · B = 0` for the reactor instance off the vertical axis. -/
theorem reactor_divergence_free {x : Space} (hx : R2 x ≠ 0) :
    divergence (fderiv ℝ reactorField x) = 0 :=
  field_divergence_free _ _ _ hx

/-- The pressure is nonnegative on the plasma region `ψ̃ ≤ 10⁴/16`. -/
theorem reactor_pressure_nonneg {μ₀ : ℝ} (hμ : 0 < μ₀) {x : Space}
    (hx : psiT 10 x ≤ 10 ^ 4 / 16) : 0 ≤ reactorPressure μ₀ x :=
  pressure_nonneg hμ (by norm_num) hx

/-- Closed form of the reactor pressure: `p = p₀ (1 - 16 ψ̃ / 10⁴)`. -/
theorem reactorPressure_eq (μ₀ : ℝ) (hμ : μ₀ ≠ 0) (x : Space) :
    reactorPressure μ₀ x = 147 / (256 * μ₀) * (1 - 16 * psiT 10 x / 10 ^ 4) := by
  unfold reactorPressure pressure
  field_simp
  ring

/-- On `ψ̃ ≤ (11/12) ψ̃_e` the pressure is at least `p₀/12 > 0`. -/
theorem reactor_pressure_pos {μ₀ : ℝ} (hμ : 0 < μ₀) {x : Space}
    (hx : psiT 10 x ≤ 11 * 10 ^ 4 / 192) :
    147 / (256 * μ₀) / 12 ≤ reactorPressure μ₀ x ∧ 0 < reactorPressure μ₀ x := by
  rw [reactorPressure_eq μ₀ hμ.ne']
  have hp : 0 < 147 / (256 * μ₀) := by positivity
  have h1 : 1 / 12 ≤ 1 - 16 * psiT 10 x / 10 ^ 4 := by linarith
  constructor
  · nlinarith
  · nlinarith

/-- The on-axis toroidal field is exactly 5 T. -/
theorem reactor_axis_field : reactorField (toLp 2 ![10, 0, 0]) = toLp 2 ![0, 5, 0] := by
  rw [reactorField, (axis_values (7 / 4) 10 50 (by norm_num)).2]; norm_num

/-- The magnetic axis `(10, 0, 0)` has `ψ̃ = 0`. -/
theorem reactor_axis_psi : psiT 10 (toLp 2 ![10, 0, 0]) = 0 :=
  (axis_values (7 / 4) 10 50 (by norm_num)).1

/-- On-axis beta `2 μ₀ p₀ / B_axis² = 147/3200 ≈ 4.6%`, for every `μ₀ > 0`. -/
theorem reactor_beta (μ₀ : ℝ) (hμ : 0 < μ₀) :
    2 * μ₀ * (3 * (7 / 4 : ℝ) ^ 2 / (16 * μ₀)) / 5 ^ 2 = 147 / 3200 := by
  field_simp; norm_num

/-- With `μ₀ ∈ [1.2566e-6, 1.2567e-6]` (bracketing `4π × 10⁻⁷`) the axis pressure lies in
`[456 900, 457 000] Pa`. -/
theorem reactor_axis_pressure (μ₀ : ℝ) (h1 : 1.2566e-6 ≤ μ₀) (h2 : μ₀ ≤ 1.2567e-6) :
    456900 ≤ 3 * (7 / 4 : ℝ) ^ 2 / (16 * μ₀) ∧ 3 * (7 / 4 : ℝ) ^ 2 / (16 * μ₀) ≤ 457000 := by
  have hμ : 0 < μ₀ := lt_of_lt_of_le (by norm_num) h1
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- The plasma region `ψ̃ ≤ 10⁴/16` lies in `50 ≤ R² ≤ 150`, `z² ≤ 25`, `‖x‖ ≤ 40/3`. -/
theorem reactor_region_bounds (x : Space) (hx : psiT 10 x ≤ 10 ^ 4 / 16) :
    50 ≤ R2 x ∧ R2 x ≤ 150 ∧ x 2 ^ 2 ≤ 25 ∧ ‖x‖ ≤ 40 / 3 := by
  obtain ⟨h1, h2, h3⟩ := region_bounds (L := 10) (by norm_num) x hx
  have h4 := region_norm (L := 10) (by norm_num) x hx
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The inboard and outboard midplane points `R² = 50`, `R² = 150` lie on the plasma
boundary `ψ̃ = 10⁴/16`, so the region bounds in `R` are attained (minor radius
`(√150 - √50)/2 ≈ 2.59 m`). -/
theorem reactor_edge_points (r : ℝ) (hr : r ^ 2 = 50 ∨ r ^ 2 = 150) :
    psiT 10 (toLp 2 ![r, 0, 0]) = 10 ^ 4 / 16 := by
  have e : psiT 10 (toLp 2 ![r, 0, 0]) = r ^ 2 * 0 ^ 2 / 2 + (r ^ 2 - 10 ^ 2) ^ 2 / 4 := by
    simp [psiT, R2]
  rcases hr with h | h <;> rw [e, h] <;> norm_num

/-- Arithmetic enclosure of the (informally derived) on-axis safety-factor expression
`q₀ = (F/L)/(√2 A) = 5 / (√2 · 7/4) ∈ [2.02, 2.021]`. Only the arithmetic is proved; the
identification of this expression with the field-line winding number is not formalized. -/
theorem reactor_q0_formula_bounds :
    2.02 ≤ (50 / 10 : ℝ) / (Real.sqrt 2 * (7 / 4)) ∧
      (50 / 10 : ℝ) / (Real.sqrt 2 * (7 / 4)) ≤ 2.021 := by
  have hs : 0 < Real.sqrt 2 := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hlo : 1.4142 ≤ Real.sqrt 2 := by nlinarith
  have hhi : Real.sqrt 2 ≤ 1.41422 := by nlinarith
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-! ## Rigidity of 3.5 MeV alphas -/

/-- Rigidity lemma: an alpha particle (mass `m ∈ [6.6446e-27, 6.6448e-27] kg`, charge `2e`,
`e ∈ [1.6021e-19, 1.6023e-19] C`) with kinetic energy at most `3.5 MeV`
(`m s² ≤ 2 · 3.5e6 · e`) satisfies `|m| s ≤ |2e| · A L / 64` with `A L / 64 = 0.2734375 T m`.
The true rigidity is `≈ 0.26940 T m` (margin 1.5%). -/
theorem alpha35_rigidity {m e s : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6448e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) (hs : 0 ≤ s)
    (hK : m * s ^ 2 ≤ 2 * (3.5e6 * e)) :
    |m| * s ≤ |2 * e| * (7 / 4 * 10 / 64) := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have he : 0 < e := lt_of_lt_of_le (by norm_num) he1
  rw [abs_of_pos hm, abs_of_pos (by positivity)]
  -- `(m s)² = m (m s²) ≤ 7e6 m e ≤ (2 e · 35/128)²`.
  have hsq : (m * s) ^ 2 ≤ (2 * e * (7 / 4 * 10 / 64)) ^ 2 := by
    have h1 : (m * s) ^ 2 ≤ m * (2 * (3.5e6 * e)) := by
      have := mul_le_mul_of_nonneg_left hK hm.le
      nlinarith
    have h2 : m * (2 * (3.5e6 * e)) ≤ (2 * e * (7 / 4 * 10 / 64)) ^ 2 := by
      have : 7e6 * m ≤ 4 * e * (7 / 4 * 10 / 64) ^ 2 := by nlinarith
      nlinarith
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- Kinetic energy is conserved along the orbit, so the rigidity condition at time 0 is the
relevant one; this records that the initial-energy hypothesis bounds the energy for all
times (speed conservation from `FullOrbit`). -/
theorem reactor_alpha_energy_all_time {m e : ℝ} (hm : m ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v) (t : ℝ) :
    ‖v t‖ = ‖v 0‖ :=
  speed_conserved hm h t 0

/-! ## Main theorem -/

/-- **3.5 MeV alphas are confined for all time.** In the exact reactor-scale Solov'ev
equilibrium (`L = 10 m`, `A = 7/4 T`, `F = 50 T m`, `B_axis = 5 T`), every full
Newton–Lorentz orbit of an alpha particle with mass `m ∈ [6.6446e-27, 6.6448e-27] kg`,
charge `2e` (`e ∈ [1.6021e-19, 1.6023e-19] C`) and initial kinetic energy at most
`3.5 MeV` (any pitch), starting with `ψ̃ ≤ ψ̃_e/4 = 10⁴/64`, satisfies
`ψ̃ ≤ (11/12) ψ̃_e` and `R² ≥ 50` for every real time `t` (in particular all `t ≥ 0`),
so it never leaves the plasma region `ψ̃ ≤ ψ̃_e`.

Scope: axisymmetric (tokamak-like) exact equilibrium, static fields, no collisions,
non-relativistic full-orbit dynamics (no guiding-centre approximation); orbit supplied. -/
theorem reactor_alpha_confined {m e : ℝ} (hm1 : 6.6446e-27 ≤ m) (hm2 : m ≤ 6.6448e-27)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x v : ℝ → Space}
    (h : LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v)
    (hK : m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e))
    (hψ0 : psiT 10 (x 0) ≤ 10 ^ 4 / 16 / 4) (t : ℝ) :
    psiT 10 (x t) ≤ 11 / 12 * (10 ^ 4 / 16) ∧ 50 ≤ R2 (x t) := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have he : 0 < e := lt_of_lt_of_le (by norm_num) he1
  have hψ0' : psiT 10 (x 0) ≤ 10 ^ 4 / 64 := by linarith
  have hx0 : ‖x 0‖ ≤ 4 * 10 / 3 := region_norm (L := 10) (by norm_num) _ (by linarith)
  have hrig := alpha35_rigidity hm1 hm2 he1 he2 (norm_nonneg _) hK
  obtain ⟨h1, h2⟩ := orbit_confined (A := 7 / 4) (L := 10) (F := 50) (by norm_num)
    (by norm_num) hm.ne' (by positivity) h hrig hψ0' hx0 t
  exact ⟨by linarith, by linarith⟩

/-- Corollary: the orbit stays in the plasma region `ψ̃ ≤ ψ̃_e` and the local pressure along
it is at least `p₀/12 > 0`, for all real times. -/
theorem reactor_alpha_in_plasma {μ₀ m e : ℝ} (hμ : 0 < μ₀) (hm1 : 6.6446e-27 ≤ m)
    (hm2 : m ≤ 6.6448e-27) (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) {x v : ℝ → Space}
    (h : LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v)
    (hK : m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e))
    (hψ0 : psiT 10 (x 0) ≤ 10 ^ 4 / 16 / 4) (t : ℝ) :
    psiT 10 (x t) ≤ 10 ^ 4 / 16 ∧ 0 < reactorPressure μ₀ (x t) := by
  have := (reactor_alpha_confined hm1 hm2 he1 he2 h hK hψ0 t).1
  exact ⟨by linarith, (reactor_pressure_pos hμ (by linarith)).2⟩

/-- Sanity: the `FullOrbit` rounded constants (`m = 6.6447e-27 kg`, `e = 1.6022e-19 C`)
are covered by the main theorem. -/
theorem reactor_alpha_confined_rounded {x v : ℝ → Space}
    (h : LorentzOrbit 6.6447e-27 (2 * 1.6022e-19) (fun _ => 0) reactorField x v)
    (hK : 6.6447e-27 * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * 1.6022e-19))
    (hψ0 : psiT 10 (x 0) ≤ 10 ^ 4 / 64) (t : ℝ) :
    psiT 10 (x t) ≤ 11 * 10 ^ 4 / 192 ∧ 50 ≤ R2 (x t) := by
  have := reactor_alpha_confined (m := 6.6447e-27) (e := 1.6022e-19) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hK (by linarith) t
  exact ⟨by linarith, this.2⟩

/-- Sanity: an alpha at rest at the magnetic axis is covered (degenerate case: zero energy,
`ψ̃ = 0`), and stays confined. -/
theorem reactor_alpha_at_rest {x v : ℝ → Space}
    (h : LorentzOrbit 6.6447e-27 (2 * 1.6022e-19) (fun _ => 0) reactorField x v)
    (hv : v 0 = 0) (hx : x 0 = toLp 2 ![10, 0, 0]) (t : ℝ) :
    psiT 10 (x t) ≤ 11 * 10 ^ 4 / 192 ∧ 50 ≤ R2 (x t) :=
  reactor_alpha_confined_rounded h (by simp [hv]; norm_num)
    (by rw [hx, reactor_axis_psi]; norm_num) t


/-- The constant orbit `x ≡ (10, 0, 0)`, `v ≡ 0` (an alpha at rest on the magnetic axis) is a
genuine Newton–Lorentz orbit of `reactorField`: the Lorentz force `q v × B` vanishes. -/
theorem axis_rest_orbit (m q : ℝ) :
    LorentzOrbit m q (fun _ => 0) reactorField (fun _ => toLp 2 ![10, 0, 0]) (fun _ => 0) where
  position t := hasDerivAt_const t _
  newton t := ⟨0, hasDerivAt_const t _, by simp [cross]⟩

/-- Non-vacuity: the full hypothesis bundle of `reactor_alpha_confined` is satisfiable, by the
constructed rest orbit on the axis with the rounded `FullOrbit` constants. -/
theorem reactor_alpha_confined_nonvacuous :
    ∃ (m e : ℝ) (x v : ℝ → Space), 6.6446e-27 ≤ m ∧ m ≤ 6.6448e-27 ∧ 1.6021e-19 ≤ e ∧
      e ≤ 1.6023e-19 ∧ LorentzOrbit m (2 * e) (fun _ => 0) reactorField x v ∧
      m * ‖v 0‖ ^ 2 ≤ 2 * (3.5e6 * e) ∧ psiT 10 (x 0) ≤ 10 ^ 4 / 16 / 4 :=
  ⟨6.6447e-27, 1.6022e-19, _, _, by norm_num, by norm_num, by norm_num, by norm_num,
    axis_rest_orbit _ _, by norm_num, by rw [reactor_axis_psi]; norm_num⟩

/-! ## Rejected fixtures -/

/-- Rejected fixture: in the `iter_like` instance (`L = 6 m`, `A = 7/5 T`) the rigidity
hypothesis `|m| s ≤ |q| A L / 64` of `orbit_confined` FAILS for every 3.5 MeV alpha
(rigidity `≈ 0.269 T m > 0.13125 T m`). -/
theorem iter_like_alpha35_rejected {m e s : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) (hs : 0 ≤ s)
    (hK : m * s ^ 2 = 2 * (3.5e6 * e)) :
    ¬ |m| * s ≤ |2 * e| * (7 / 5 * 6 / 64) := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have he : 0 < e := lt_of_lt_of_le (by norm_num) he1
  rw [abs_of_pos hm, abs_of_pos (by positivity)]
  intro hle
  have hsq : (m * s) ^ 2 ≤ (2 * e * (7 / 5 * 6 / 64)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have h1 : (m * s) ^ 2 = m * (2 * (3.5e6 * e)) := by rw [← hK]; ring
  rw [h1] at hsq
  nlinarith

/-- Rejected fixture showing the margin is thin: in the reactor instance the rigidity
hypothesis fails for every alpha of energy exactly 3.7 MeV. -/
theorem reactor_alpha37_rejected {m e s : ℝ} (hm1 : 6.6446e-27 ≤ m)
    (he1 : 1.6021e-19 ≤ e) (he2 : e ≤ 1.6023e-19) (hs : 0 ≤ s)
    (hK : m * s ^ 2 = 2 * (3.7e6 * e)) :
    ¬ |m| * s ≤ |2 * e| * (7 / 4 * 10 / 64) := by
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) hm1
  have he : 0 < e := lt_of_lt_of_le (by norm_num) he1
  rw [abs_of_pos hm, abs_of_pos (by positivity)]
  intro hle
  have hsq : (m * s) ^ 2 ≤ (2 * e * (7 / 4 * 10 / 64)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have h1 : (m * s) ^ 2 = m * (2 * (3.7e6 * e)) := by rw [← hK]; ring
  rw [h1] at hsq
  nlinarith

end PlasmaLean.Design.SolovevAlpha
