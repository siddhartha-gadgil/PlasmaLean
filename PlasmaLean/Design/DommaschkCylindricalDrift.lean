/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.CylindricalDrift
public import PlasmaLean.Design.DommaschkRegionFieldBounds

/-!
# QA2R guiding centres in lifted cylindrical coordinates

The statements of `Kinetic/CylindricalDrift` for the QA2R field
`B = DommaschkQA2R.field DommaschkQA2R.candidate`, the planar field-line equation
`euclideanFlow 0 1` (the toroidal angle as time) and the lifted points over the closed envelope
`Region` (`7/8 ≤ R ≤ 1`, `|z| ≤ 5/64`), for the drift bound of note N-216. The Littlejohn
equations are a supplied model.

* `cylVelocity_field_of_ne`, `cylVelocity_field`: the cylindrical velocity of `B` is
  `omega = B_φ / R` times the space-time field `(1, euclideanFlow 0 1 θ (R, z))`.
* `continuousAt_velocity`: the Littlejohn right-hand side is continuous off the axis where the
  field does not vanish.
* `exists_lift_decomp`: an orbit on `[0, T]` that stays off the axis and where `B ≠ 0` has a
  lifted path `X`; at the times with `X τ` over the envelope its velocity is
  `λ (1, euclideanFlow 0 1) + w`, `λ = (v_∥/|B|) B_φ/R`, and
  `‖w‖ ≤ max 1 R⁻¹ · 2H₀/(|q||B|²) ‖∇|B|‖` with `H₀` the energy at birth (conserved on
  `[0, T]`, `CylindricalDrift.hamiltonian_eq_birth`).
* `max_inv_le`, `omega_bounds`, `abs_rate_le`, `norm_perturbation_le`: the constants of the
  envelope, from `DommaschkRegionFieldBounds`: `max 1 R⁻¹ ≤ 8/7`,
  `47/50 ≤ B_φ/R ≤ (13/10)/(7/8)`, `|λ| ≤ |v_∥|/(47/50) · (13/10)/(7/8)`,
  `‖w‖ ≤ (8/7) · 2H/(|q| (47/50)²) ‖DB‖`.
* `exists_lift_bounds`: the lifted orbit with these constants.
* `norm_drift_le_strength`, `norm_perturbation_le_strength`: where `bT ≤ |B|`, the drift is at
  most `(2H - μ bT)/(|q| bT²) ‖∇|B|‖` (the coefficient is `(2H - μ|B|)/(|q||B|²)`).
* `omega_le`: an upper bound `cφ` of `B_φ` gives `B_φ / R ≤ cφ / (7/8)` on the envelope.

The hypothesis on the orbit is stated in space (off the axis, `B ≠ 0`); it holds in particular
while the orbit is over the envelope. The operator norm `‖DB‖` is left in the bounds: no
numerical bound for it on the envelope is proved here.

**Sanity.** `overRegion_example`: a concrete lifted point over the envelope, where the angular
speed of the field line is at least `47/50`.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCylindricalDrift
open Fields Contract Set Kinetic Kinetic.GCLittlejohn Fields.CylindricalLift
open DommaschkSignedTraceDomain DommaschkBounceField DommaschkKam DommaschkJacobian
open DommaschkCartesianAngleFlow

/-- Lifted points over the closed envelope, at any angle. -/
def overRegion : Set (ℝ × Plane) := {p | Region p.2}

/-- The angular speed of the field line through a lifted point, `B_φ / R`. -/
def omega (p : ℝ × Plane) : ℝ := cylBphi (p.2 0) p.1 (p.2 1) / p.2 0

/-- The cylindrical velocity of the QA2R field is `B_φ / R` times the space-time field of the
field-line equation, where the radius and the toroidal component do not vanish. -/
theorem cylVelocity_field_of_ne {R t z : ℝ} (hR : R ≠ 0) (hφ : cylBphi R t z ≠ 0) :
    cylVelocity t R (B (cylPoint R t z)) =
      (cylBphi R t z / R) • ((1 : ℝ), euclideanFlow 0 1 t (WithLp.toLp 2 ![R, z])) := by
  refine Prod.ext ?_ ?_
  · simp only [cylVelocity, cylBphi, Prod.smul_fst, smul_eq_mul, mul_one]
    ring
  · ext i
    fin_cases i
    · simp [cylVelocity, euclideanFlow, physicalFlow, cylBR]
      field_simp
    · simp [cylVelocity, euclideanFlow, physicalFlow, cylBz]
      field_simp

/-- Over the envelope the cylindrical velocity of the QA2R field is `omega` times the space-time
field of the field-line equation. -/
theorem cylVelocity_field {p : ℝ × Plane} (reg : Region p.2) :
    cylVelocity p.1 (p.2 0) (B (cylPoint (p.2 0) p.1 (p.2 1))) =
      omega p • FlowLabel.field (euclideanFlow 0 1) p := by
  have hr : 0 < p.2 0 := by linarith [reg.1.1]
  have ha := (in_regular reg p.1).2
  rw [angular_at] at ha
  have hφ : 0 < cylBphi (p.2 0) p.1 (p.2 1) := pos_of_mul_pos_right ha hr.le
  have h := cylVelocity_field_of_ne hr.ne' hφ.ne'
  have hp : (WithLp.toLp 2 ![p.2 0, p.2 1] : Plane) = p.2 := by
    ext i; fin_cases i <;> rfl
  rw [hp] at h
  exact h

/-- The Littlejohn right-hand side of the QA2R field is continuous at every state off the axis
where the field does not vanish. -/
theorem continuousAt_velocity {x : Space} (hx : x ∈ CylAlgebra.domain) (h0 : B x ≠ 0)
    (m q μ v : ℝ) : ContinuousAt (littlejohnVelocity B m q μ) (x, v) := by
  have vac := DommaschkQA2R.field_vacuum DommaschkQA2R.candidate
  have op := (VacuumLittlejohnLocal.isOpen_regular vac).prod (isOpen_univ (X := ℝ))
  exact (VacuumLittlejohnLocal.velocity_smooth vac m q μ).continuousOn.continuousAt
    (op.mem_nhds ⟨⟨hx, h0⟩, mem_univ v⟩)

/-! ## The lifted orbit -/

/-- **Lifted QA2R guiding-centre orbit.** A Littlejohn orbit in the QA2R field on `[0, T]` that
stays off the axis and where the field does not vanish has a lifted path `X = (θ, (R, z))`. At
every time at which the lifted point is over the envelope, its velocity is
`λ (1, euclideanFlow 0 1 θ (R, z)) + w` with `λ = (v_∥/|B|) B_φ/R`, and the lifted drift `w` is
bounded in terms of the energy at birth. -/
theorem exists_lift_decomp {m q : ℝ} {b : GCBirth} {z : ℝ → Space × ℝ} {T θ₀ R₀ z₀ : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ b.2.2)
    (orbit : GCBirthOrbitOn B m q b z T)
    (regular : ∀ τ ∈ Icc 0 T, (z τ).1 ∈ CylAlgebra.domain ∧ B (z τ).1 ≠ 0)
    (start : b.1 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ τ ∈ Icc 0 T,
      (z τ).1 = cylPoint ((X τ).2 0) (X τ).1 ((X τ).2 1) ∧ 0 < (X τ).2 0 ∧
      (Region (X τ).2 →
        HasDerivAt X (CylindricalDrift.rate B omega (z τ) (X τ) •
            FlowLabel.field (euclideanFlow 0 1) (X τ) +
          CylindricalDrift.perturbation B m q b.2.2 (z τ) (X τ)) τ ∧
        ‖CylindricalDrift.perturbation B m q b.2.2 (z τ) (X τ)‖ ≤ max 1 ((X τ).2 0)⁻¹ *
          (2 * hamiltonian m b.2.2 B b.1 b.2.1 / (|q| * ‖B (z τ).1‖ ^ 2) *
            ‖gradAbsB B (z τ).1‖)) := by
  have hv := CylindricalDrift.continuousOn_velocity orbit (fun τ hτ =>
    continuousAt_velocity (regular τ hτ).1 (regular τ hτ).2 m q b.2.2 (z τ).2)
  have energy := CylindricalDrift.hamiltonian_eq_birth hm.ne' orbit (fun τ hτ =>
    ((DommaschkRegionRegularity.contDiffAt_domain (regular τ hτ).1).differentiableAt
      (by norm_num)).norm ℝ (regular τ hτ).2)
  obtain ⟨X, hX0, h⟩ := CylindricalDrift.exists_lift_decomp (G := overRegion) (ω := omega)
    (F := euclideanFlow 0 1)
    (fun p hp => (DommaschkRegionRegularity.field_contDiffAt hp p.1).differentiableAt
      (by norm_num))
    (fun p hp => DommaschkRegionRegularity.field_ne_zero hp p.1)
    (fun p hp => DommaschkRegionRegularity.field_curl hp p.1)
    (fun p hp => cylVelocity_field hp) hT hm.le hq hμ orbit hv
    (fun τ hτ => (regular τ hτ).1) start hR₀
  refine ⟨X, hX0, fun τ hτ => ?_⟩
  obtain ⟨hpt, hpos, hdec⟩ := h τ hτ
  refine ⟨hpt, hpos, fun hG => ?_⟩
  have hd := hdec hG
  rwa [energy τ hτ] at hd

/-! ## Numerical constants on the envelope -/

/-- On the envelope `max 1 R⁻¹ ≤ 8/7`. -/
theorem max_inv_le {p : Plane} (reg : Region p) : max 1 (p 0)⁻¹ ≤ 8 / 7 := by
  refine max_le (by norm_num) ?_
  rw [inv_le_comm₀ (by linarith [reg.1.1]) (by norm_num)]
  linarith [reg.1.1]

/-- On the envelope the angular speed `B_φ / R` of the field line lies in
`[47/50, (13/10)/(7/8)]`. -/
theorem omega_bounds {p : ℝ × Plane} (reg : Region p.2) :
    47 / 50 ≤ omega p ∧ omega p ≤ (13 / 10) / (7 / 8) := by
  obtain ⟨lo, hi⟩ := DommaschkRegionFieldBounds.toroidal_bounds reg p.1
  have hr : 0 < p.2 0 := by linarith [reg.1.1]
  constructor
  · rw [omega, le_div_iff₀ hr]
    nlinarith [reg.1.2]
  · rw [omega, div_le_div_iff₀ hr (by norm_num)]
    nlinarith [reg.1.1]

/-- The coefficient `λ = (v_∥/|B|) B_φ/R` over the envelope. -/
theorem abs_rate_le {p : ℝ × Plane} {w : Space × ℝ} (reg : Region p.2)
    (hx : w.1 = cylPoint (p.2 0) p.1 (p.2 1)) :
    |CylindricalDrift.rate B omega w p| ≤ |w.2| / (47 / 50) * ((13 / 10) / (7 / 8)) := by
  obtain ⟨lo, hi⟩ := omega_bounds reg
  have hB := DommaschkRegionFieldBounds.strength_ge reg p.1
  rw [← hx] at hB
  rw [CylindricalDrift.abs_rate_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ omega p)]
  gcongr

/-- The lifted drift over the envelope, with the constants of the envelope:
`‖w‖ ≤ (8/7) · 2H/(|q| (47/50)²) ‖DB‖`. -/
theorem norm_perturbation_le {m q μ : ℝ} {p : ℝ × Plane} {w : Space × ℝ} (reg : Region p.2)
    (hx : w.1 = cylPoint (p.2 0) p.1 (p.2 1)) (hm : 0 ≤ m) (hμ : 0 ≤ μ) (hq : q ≠ 0) :
    ‖CylindricalDrift.perturbation B m q μ w p‖ ≤
      8 / 7 * (2 * hamiltonian m μ B w.1 w.2 / (|q| * (47 / 50) ^ 2) * ‖fderiv ℝ B w.1‖) := by
  have hr : 0 < p.2 0 := by linarith [reg.1.1]
  have nz := DommaschkRegionRegularity.field_ne_zero reg p.1
  have hB := DommaschkRegionFieldBounds.strength_ge reg p.1
  have hg := DommaschkRegionRegularity.norm_gradAbsB_le_region reg p.1
  rw [← hx] at nz hB hg
  have hH : 0 ≤ 2 * hamiltonian m μ B w.1 w.2 := by
    have h1 := mul_nonneg hm (sq_nonneg w.2)
    have h2 := mul_nonneg hμ (norm_nonneg (B w.1))
    rw [hamiltonian]
    linarith
  have hq' : 0 < |q| := abs_pos.mpr hq
  refine (CylindricalDrift.norm_perturbation_le hr nz hm hμ).trans ?_
  have hmax := max_inv_le reg
  gcongr

/-- **Lifted QA2R guiding-centre orbit with the constants of the envelope.** As
`exists_lift_decomp`; at the times at which the lifted point is over the envelope, the drift is
at most `(8/7) · 2H₀/(|q| (47/50)²) ‖DB‖`, the coefficient of the field-line equation is at
most `|v_∥|/(47/50) · (13/10)/(7/8)`, and `m v_∥² ≤ 2H₀`, with `H₀` the energy at birth. -/
theorem exists_lift_bounds {m q : ℝ} {b : GCBirth} {z : ℝ → Space × ℝ} {T θ₀ R₀ z₀ : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m) (hq : q ≠ 0) (hμ : 0 ≤ b.2.2)
    (orbit : GCBirthOrbitOn B m q b z T)
    (regular : ∀ τ ∈ Icc 0 T, (z τ).1 ∈ CylAlgebra.domain ∧ B (z τ).1 ≠ 0)
    (start : b.1 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ τ ∈ Icc 0 T,
      (z τ).1 = cylPoint ((X τ).2 0) (X τ).1 ((X τ).2 1) ∧ 0 < (X τ).2 0 ∧
      (Region (X τ).2 →
        HasDerivAt X (CylindricalDrift.rate B omega (z τ) (X τ) •
            FlowLabel.field (euclideanFlow 0 1) (X τ) +
          CylindricalDrift.perturbation B m q b.2.2 (z τ) (X τ)) τ ∧
        ‖CylindricalDrift.perturbation B m q b.2.2 (z τ) (X τ)‖ ≤
          8 / 7 * (2 * hamiltonian m b.2.2 B b.1 b.2.1 / (|q| * (47 / 50) ^ 2) *
            ‖fderiv ℝ B (z τ).1‖) ∧
        |CylindricalDrift.rate B omega (z τ) (X τ)| ≤
          |(z τ).2| / (47 / 50) * ((13 / 10) / (7 / 8)) ∧
        m * (z τ).2 ^ 2 ≤ 2 * hamiltonian m b.2.2 B b.1 b.2.1) := by
  have energy := CylindricalDrift.hamiltonian_eq_birth hm.ne' orbit (fun τ hτ =>
    ((DommaschkRegionRegularity.contDiffAt_domain (regular τ hτ).1).differentiableAt
      (by norm_num)).norm ℝ (regular τ hτ).2)
  obtain ⟨X, hX0, h⟩ := exists_lift_decomp hT hm hq hμ orbit regular start hR₀
  refine ⟨X, hX0, fun τ hτ => ?_⟩
  obtain ⟨hpt, hpos, hdec⟩ := h τ hτ
  refine ⟨hpt, hpos, fun hG => ⟨(hdec hG).1, ?_, abs_rate_le hG hpt, ?_⟩⟩
  · rw [← energy τ hτ]
    exact norm_perturbation_le hG hpt hm.le hμ hq
  · rw [← energy τ hτ]
    exact CylindricalDrift.mass_mul_sq_le hμ _ _

/-! ## Bounds with a lower bound of the field strength -/

/-- **Drift bound with the magnetic moment.** Where `bT ≤ |F|`, the drift speed is at most
`(2H - μ bT)/(|q| bT²) ‖∇|F|‖`: the coefficient of the drift is
`(m v_∥² + μ|F|)/(|q||F|²)` and `m v_∥² + μ|F| = 2H - μ|F|`. This is smaller than the bound
`2H/(|q||F|²) ‖∇|F|‖` of `LabelDrift.norm_drift_le` by the term with `μ`. -/
theorem norm_drift_le_strength {F : Space → Space} {m q μ bT : ℝ} {x : Space} (hm : 0 ≤ m)
    (hμ : 0 ≤ μ) (hq : q ≠ 0) (hbT : 0 < bT) (hstr : bT ≤ ‖F x‖) (v : ℝ) :
    ‖LabelDrift.drift F m q μ (x, v)‖ ≤
      (2 * hamiltonian m μ F x v - μ * bT) / (|q| * bT ^ 2) * ‖gradAbsB F x‖ := by
  have hn : 0 < ‖F x‖ := hbT.trans_le hstr
  have hqa : 0 < |q| := abs_pos.mpr hq
  have den : |q * ‖F x‖ ^ 2| = |q| * ‖F x‖ ^ 2 := by rw [abs_mul, abs_of_pos (pow_pos hn 2)]
  have h1 : 0 ≤ m * v ^ 2 := mul_nonneg hm (sq_nonneg v)
  have h2 : 0 ≤ μ * ‖F x‖ := mul_nonneg hμ hn.le
  have h3 : μ * bT ≤ μ * ‖F x‖ := mul_le_mul_of_nonneg_left hstr hμ
  have unit : ‖bhat F x‖ = 1 := by
    rw [bhat, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have geom : ‖cross (bhat F x) (gradAbsB F x)‖ ≤ ‖gradAbsB F x‖ := by
    simpa only [unit, one_mul] using norm_cross_le (bhat F x) (gradAbsB F x)
  have coeff : (m * v ^ 2 + μ * ‖F x‖) / (|q| * ‖F x‖ ^ 2) ≤
      (2 * hamiltonian m μ F x v - μ * bT) / (|q| * bT ^ 2) := by
    have sq : bT ^ 2 ≤ ‖F x‖ ^ 2 := pow_le_pow_left₀ hbT.le hstr 2
    calc (m * v ^ 2 + μ * ‖F x‖) / (|q| * ‖F x‖ ^ 2)
        ≤ (m * v ^ 2 + μ * ‖F x‖) / (|q| * bT ^ 2) :=
          div_le_div_of_nonneg_left (add_nonneg h1 h2) (by positivity)
            (mul_le_mul_of_nonneg_left sq hqa.le)
      _ ≤ (2 * hamiltonian m μ F x v - μ * bT) / (|q| * bT ^ 2) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          rw [hamiltonian]
          linarith
  rw [LabelDrift.drift, norm_smul, Real.norm_eq_abs, abs_div, den,
    abs_of_nonneg (add_nonneg h1 h2)]
  exact mul_le_mul coeff geom (norm_nonneg _)
    ((div_nonneg (add_nonneg h1 h2) (by positivity)).trans coeff)

/-- The lifted drift where `bT ≤ |F|`: at most
`max 1 R⁻¹ · (2H - μ bT)/(|q| bT²) ‖∇|F|‖`. -/
theorem norm_perturbation_le_strength {F : Space → Space} {m q μ bT : ℝ} {p : ℝ × Plane}
    {w : Space × ℝ} (hR : 0 < p.2 0) (hm : 0 ≤ m) (hμ : 0 ≤ μ) (hq : q ≠ 0) (hbT : 0 < bT)
    (hstr : bT ≤ ‖F w.1‖) :
    ‖CylindricalDrift.perturbation F m q μ w p‖ ≤ max 1 (p.2 0)⁻¹ *
      ((2 * hamiltonian m μ F w.1 w.2 - μ * bT) / (|q| * bT ^ 2) * ‖gradAbsB F w.1‖) := by
  obtain ⟨x, v⟩ := w
  exact (norm_cylVelocity_le hR _ _).trans (mul_le_mul_of_nonneg_left
    (norm_drift_le_strength hm hμ hq hbT hstr v) (le_max_of_le_left zero_le_one))

/-- On the envelope, an upper bound `cφ` of the toroidal component gives
`B_φ / R ≤ cφ / (7/8)`. -/
theorem omega_le {p : ℝ × Plane} (reg : Region p.2) {cφ : ℝ}
    (h : cylBphi (p.2 0) p.1 (p.2 1) ≤ cφ) : omega p ≤ cφ / (7 / 8) := by
  have hr : 0 < p.2 0 := by linarith [reg.1.1]
  have pos : 0 ≤ omega p := le_trans (by norm_num) (omega_bounds reg).1
  have hc : 0 ≤ cφ := by
    have e : cylBphi (p.2 0) p.1 (p.2 1) = omega p * p.2 0 := by
      rw [omega, div_mul_cancel₀ _ hr.ne']
    exact (e ▸ mul_nonneg pos hr.le).trans h
  calc omega p ≤ cφ / p.2 0 := div_le_div_of_nonneg_right h hr.le
    _ ≤ cφ / (7 / 8) := div_le_div_of_nonneg_left hc (by norm_num) reg.1.1

/-! ## Sanity -/

/-- **Sanity**: a concrete lifted point over the envelope; the angular speed of the field line
there is at least `47/50`. -/
theorem overRegion_example :
    ((0 : ℝ), (WithLp.toLp 2 ![15 / 16, 0] : Plane)) ∈ overRegion ∧
      47 / 50 ≤ omega ((0 : ℝ), (WithLp.toLp 2 ![15 / 16, 0] : Plane)) := by
  have reg : Region (WithLp.toLp 2 ![15 / 16, 0] : Plane) := by
    simp only [Region, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  exact ⟨reg, (omega_bounds (p := ((0 : ℝ), (WithLp.toLp 2 ![15 / 16, 0] : Plane))) reg).1⟩

end PlasmaLean.Design.DommaschkCylindricalDrift
