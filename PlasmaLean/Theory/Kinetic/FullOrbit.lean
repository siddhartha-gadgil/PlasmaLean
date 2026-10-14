/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.BiotSavart
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Full-orbit Newton–Lorentz dynamics (task K1)

A classical charged particle of mass `m` and charge `q` moves in static fields
`E, B : Space → Space` by `m v' = q (E(x) + v × B(x))`, `x' = v`, in SI units. This is
a model (non-relativistic, no radiation, no self-field, no collisions); it is not a
statement about every physical effect.

Results:

* the magnetic force does no work, so speed is conserved in a pure magnetic field;
* with an electrostatic potential `Φ` (`∇Φ = -E`), the energy `m|v|²/2 + qΦ(x)` is
  conserved for all time;
* in a uniform field `B₀ e_z` an explicit helix solves the equations, its distance from
  the guiding-centre line is exactly the Larmor radius `m|u|/(|q| B₀)`;
* exact rational bounds on Larmor radii for a 10 keV deuteron and a 3.5 MeV alpha
  particle at 5 T, using supplied CODATA-rounded constants.

Trajectory existence for general fields, guiding-centre reduction error and any
confinement in a nonuniform toroidal field are separate obligations.
-/
public section
noncomputable section
namespace PlasmaLean.Kinetic
open PlasmaLean.Fields WithLp
open scoped RealInnerProductSpace

/-- A classical Newton–Lorentz trajectory for all times, with explicit velocity. -/
structure LorentzOrbit (m q : ℝ) (E B : Space → Space) (x v : ℝ → Space) : Prop where
  position : ∀ t, HasDerivAt x (v t) t
  newton : ∀ t, ∃ a, HasDerivAt v a t ∧ m • a = q • (E (x t) + cross (v t) (B (x t)))

/-- The cross product is orthogonal to its first factor. -/
theorem inner_cross_self (u w : Space) : ⟪u, cross u w⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, cross]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact dot_self_cross _ _

/-- The cross product is orthogonal to its second factor. -/
theorem inner_cross_self' (u w : Space) : ⟪w, cross u w⟫ = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, cross]
  simp only [star_trivial]
  rw [dotProduct_comm]
  exact dot_cross_self _ _

/-- Power delivered by the Lorentz force: only the electric field does work. -/
theorem lorentz_power (q : ℝ) (e b v : Space) :
    ⟪v, q • (e + cross v b)⟫ = q * ⟪v, e⟫ := by
  rw [inner_smul_right, inner_add_right, inner_cross_self, add_zero]

/-- Rate of change of the kinetic energy along an orbit equals the electric power. -/
theorem kinetic_energy_deriv {m q : ℝ} {E B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q E B x v) (t : ℝ) :
    HasDerivAt (fun s => m / 2 * ‖v s‖ ^ 2) (q * ⟪v t, E (x t)⟫) t := by
  obtain ⟨a, ha, hlaw⟩ := h.newton t
  have hn := (ha.norm_sq).const_mul (m / 2)
  convert hn using 1
  have : m / 2 * (2 * ⟪v t, a⟫) = ⟪v t, m • a⟫ := by
    rw [inner_smul_right]; ring
  rw [this, hlaw, lorentz_power]

/-- The velocity of an orbit is differentiable at every time. -/
theorem LorentzOrbit.velocity_differentiable {m q : ℝ} {E B : Space → Space}
    {x v : ℝ → Space} (h : LorentzOrbit m q E B x v) : Differentiable ℝ v := fun t => by
  obtain ⟨a, ha, -⟩ := h.newton t
  exact ha.differentiableAt

/-- In a purely magnetic field the kinetic energy is constant for all time. -/
theorem kinetic_energy_conserved {m q : ℝ} {B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (s t : ℝ) :
    m / 2 * ‖v s‖ ^ 2 = m / 2 * ‖v t‖ ^ 2 := by
  have hd (r : ℝ) := kinetic_energy_deriv h r
  refine is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => ?_) s t
  simp [(hd r).deriv]

/-- Speed is conserved in a pure magnetic field (for nonzero mass). -/
theorem speed_conserved {m q : ℝ} (hm : m ≠ 0) {B : Space → Space} {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) B x v) (s t : ℝ) : ‖v s‖ = ‖v t‖ := by
  have h2 := kinetic_energy_conserved h s t
  have hsq : ‖v s‖ ^ 2 = ‖v t‖ ^ 2 := by
    have : m / 2 ≠ 0 := div_ne_zero hm two_ne_zero
    exact mul_left_cancel₀ this h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-- Electrostatic potential: `Φ` is differentiable with gradient `-E`. -/
@[expose] def IsPotential (Φ : Space → ℝ) (E : Space → Space) : Prop :=
  ∀ y, HasFDerivAt Φ (-(innerSL ℝ (E y))) y

/-- Total energy: kinetic plus electrostatic potential energy. -/
@[expose] def orbitEnergy (m q : ℝ) (Φ : Space → ℝ) (x v : ℝ → Space) (t : ℝ) : ℝ :=
  m / 2 * ‖v t‖ ^ 2 + q * Φ (x t)

/-- Energy conservation for Newton–Lorentz orbits in static electrostatic and
magnetic fields. -/
theorem energy_conserved {m q : ℝ} {E B : Space → Space} {Φ : Space → ℝ}
    {x v : ℝ → Space} (h : LorentzOrbit m q E B x v) (hΦ : IsPotential Φ E) (s t : ℝ) :
    orbitEnergy m q Φ x v s = orbitEnergy m q Φ x v t := by
  have hd (r : ℝ) : HasDerivAt (orbitEnergy m q Φ x v) 0 r := by
    have hp : HasDerivAt (fun s => Φ (x s)) (-⟪E (x r), v r⟫) r := by
      have := (hΦ (x r)).comp_hasDerivAt r (h.position r)
      convert this using 1
      · rfl
      · simp
    change HasDerivAt (fun s => m / 2 * ‖v s‖ ^ 2 + q * Φ (x s)) 0 r
    convert (kinetic_energy_deriv h r).add (hp.const_mul q) using 1
    rw [real_inner_comm]; ring
  refine is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => ?_) s t
  exact (hd r).deriv

/-- Sanity: a constant potential gives zero electric field, recovering the magnetic case. -/
theorem constant_potential (c : ℝ) : IsPotential (fun _ => c) (fun _ => 0) := by
  intro y
  simpa using hasFDerivAt_const c y

/-! ## Exact gyration in a uniform magnetic field -/

/-- Transport a coordinate derivative to Euclidean space. -/
theorem hasDerivAt_toLp {f : ℝ → Fin 3 → ℝ} {f' : Fin 3 → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (toLp 2 (f s) : Space)) (toLp 2 f') t := by
  have := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.hasFDerivAt.comp_hasDerivAt
    t hf
  exact this

/-- Uniform magnetic field of strength `B₀` along the third axis. -/
@[expose] def uniformField (B₀ : ℝ) : Space → Space := fun _ => toLp 2 ![0, 0, B₀]

/-- Helical velocity: perpendicular speed `u`, parallel speed `w`, gyrofrequency `ω`. -/
@[expose] def helixVelocity (u w ω : ℝ) (t : ℝ) : Space :=
  toLp 2 ![u * Real.cos (ω * t), -(u * Real.sin (ω * t)), w]

/-- Helical position about the guiding-centre line through `X`. -/
@[expose] def helixPosition (X : Space) (u w ω : ℝ) (t : ℝ) : Space :=
  X + toLp 2 ![u / ω * Real.sin (ω * t), u / ω * Real.cos (ω * t), w * t]

/-- The explicit helix solves the Newton–Lorentz equations in a uniform field, with
gyrofrequency `ω = q B₀ / m` (nonzero mass and field strength). -/
theorem helix_orbit {m q B₀ : ℝ} (hm : m ≠ 0) (hω : q * B₀ / m ≠ 0) (X : Space) (u w : ℝ) :
    LorentzOrbit m q (fun _ => 0) (uniformField B₀)
      (helixPosition X u w (q * B₀ / m)) (helixVelocity u w (q * B₀ / m)) := by
  set ω := q * B₀ / m with hωdef
  constructor
  · intro t
    have h0 : HasDerivAt (fun s => u / ω * Real.sin (ω * s)) (u * Real.cos (ω * t)) t := by
      have := (((hasDerivAt_id' t).const_mul ω).sin).const_mul (u / ω)
      convert this using 1
      field_simp
    have h1 : HasDerivAt (fun s => u / ω * Real.cos (ω * s)) (-(u * Real.sin (ω * t))) t := by
      have := (((hasDerivAt_id' t).const_mul ω).cos).const_mul (u / ω)
      convert this using 1
      field_simp
    have h2 : HasDerivAt (fun s => w * s) w t := by
      simpa using (hasDerivAt_id' t).const_mul w
    have hc : HasDerivAt (fun s => ![u / ω * Real.sin (ω * s), u / ω * Real.cos (ω * s), w * s])
        ![u * Real.cos (ω * t), -(u * Real.sin (ω * t)), w] t := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      exacts [h0, h1, h2]
    exact (hasDerivAt_toLp hc).const_add X
  · intro t
    refine ⟨toLp 2 ![-(u * ω * Real.sin (ω * t)), -(u * ω * Real.cos (ω * t)), 0], ?_, ?_⟩
    · have h0 : HasDerivAt (fun s => u * Real.cos (ω * s)) (-(u * ω * Real.sin (ω * t))) t := by
        have := (((hasDerivAt_id' t).const_mul ω).cos).const_mul u
        convert this using 1
        ring
      have h1 : HasDerivAt (fun s => -(u * Real.sin (ω * s))) (-(u * ω * Real.cos (ω * t))) t := by
        have := ((((hasDerivAt_id' t).const_mul ω).sin).const_mul (-u))
        convert this using 1
        · funext s; ring
        · ring
      apply hasDerivAt_toLp
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      exacts [h0, h1, hasDerivAt_const t w]
    · ext i
      fin_cases i <;>
        simp [uniformField, helixVelocity, cross, cross_apply, hωdef] <;>
        field_simp

/-- Distance of the helix from its guiding-centre line equals the Larmor radius
`|u/ω|`, at every time. Here `perp` drops the parallel coordinate. -/
theorem helix_gyroradius (X : Space) (u w ω t : ℝ) :
    (helixPosition X u w ω t 0 - X 0) ^ 2 + (helixPosition X u w ω t 1 - X 1) ^ 2 =
      (u / ω) ^ 2 := by
  simp only [helixPosition, PiLp.add_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_sub_cancel_left]
  have := Real.sin_sq_add_cos_sq (ω * t)
  nlinarith [this]

/-- Sanity: the helix has constant speed, consistent with `speed_conserved`. -/
theorem helix_speed (u w ω t : ℝ) : ‖helixVelocity u w ω t‖ ^ 2 = u ^ 2 + w ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [helixVelocity, Fin.sum_univ_three]
  nlinarith [Real.sin_sq_add_cos_sq (ω * t)]

/-- Larmor radius `|u/ω|` with `ω = qB₀/m` is `m |u| / (|q| |B₀|)`. -/
theorem larmor_radius_formula (m q B₀ u : ℝ) (hm : 0 < m) :
    |u / (q * B₀ / m)| = m * |u| / (|q| * |B₀|) := by
  rw [abs_div, abs_div, abs_mul, abs_of_pos hm]
  rcases eq_or_ne (|q| * |B₀|) 0 with h | h
  · simp [h]
  · field_simp

/-! ## Realistic gyroradii

Supplied constants (SI, rounded): deuteron mass `3.3436e-27` kg, alpha mass
`6.6447e-27` kg, elementary charge `1.6022e-19` C. For kinetic energy `K` entirely
perpendicular, `r_L² = 2 m K / (q² B²)`. Rounding choices are explicit inputs, not
derived physical constants. -/

/-- Squared Larmor radius from mass, perpendicular kinetic energy, charge and field. -/
@[expose] def larmorRadiusSq (m K q B : ℝ) : ℝ := 2 * m * K / (q ^ 2 * B ^ 2)

/-- Consistency: `larmorRadiusSq` is the square of `m u / (q B)` with `K = m u²/2`. -/
theorem larmorRadiusSq_eq (m q B u : ℝ) (hm : m ≠ 0) :
    larmorRadiusSq m (m * u ^ 2 / 2) q B = (m * u / (q * B)) ^ 2 := by
  unfold larmorRadiusSq
  rcases eq_or_ne (q * B) 0 with h | h
  · have : q ^ 2 * B ^ 2 = 0 := by rw [← mul_pow, h]; ring
    simp [this, h]
  · have : q ^ 2 * B ^ 2 ≠ 0 := by rw [← mul_pow]; exact pow_ne_zero _ h
    field_simp

/-- A 10 keV deuteron at 5 T has Larmor radius below 4.1 mm (`r_L² < (4.1e-3)²`). -/
theorem deuteron_10keV_5T :
    larmorRadiusSq (3.3436e-27) (10e3 * 1.6022e-19) (1.6022e-19) 5 < (4.1e-3) ^ 2 := by
  norm_num [larmorRadiusSq]

/-- A 3.5 MeV fusion alpha at 5 T has Larmor radius between 5.3 and 5.5 cm. -/
theorem alpha_3_5MeV_5T :
    (5.3e-2) ^ 2 < larmorRadiusSq (6.6447e-27) (3.5e6 * 1.6022e-19) (2 * 1.6022e-19) 5 ∧
    larmorRadiusSq (6.6447e-27) (3.5e6 * 1.6022e-19) (2 * 1.6022e-19) 5 < (5.5e-2) ^ 2 := by
  norm_num [larmorRadiusSq]

/-- Doubling the field quarters the squared Larmor radius (scaling sanity). -/
theorem larmorRadiusSq_double_field (m K q B : ℝ) :
    larmorRadiusSq m K q (2 * B) = larmorRadiusSq m K q B / 4 := by
  unfold larmorRadiusSq
  rw [mul_pow, div_div]
  ring_nf

end PlasmaLean.Kinetic
