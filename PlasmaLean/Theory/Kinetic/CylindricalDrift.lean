/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.LabelDrift
public import PlasmaLean.Theory.Fields.CylindricalLift
public import PlasmaLean.Theory.Fields.FlowLabel

/-!
# Littlejohn guiding centres in lifted cylindrical coordinates

A Littlejohn guiding-centre orbit (a supplied model, see `Kinetic/GuidingCentreLittlejohn`) that
stays off the `z`-axis is written in the lifted cylindrical coordinates `(θ, (R, z))` of
`Fields/CylindricalLift`. Where the field is nonvanishing and curl-free, and its cylindrical
velocity is a multiple `ω` of the space-time field `(1, F)` of a planar field-line equation
`x' = F θ x`, the lifted orbit moves along `(1, F)` up to the cross-field drift.

* `exists_lift`: the lifted path `X` of an orbit on `[0, T]`, with
  `X' = cylVelocity θ R (dX/dt)`. This needs no hypothesis on the field except continuity of the
  velocity along the orbit (`continuousOn_velocity` gives it from continuity of the Littlejohn
  right-hand side at the states visited).
* `perturbation`, `rate`: the lifted drift `w = cylVelocity θ R (drift)` and the coefficient
  `λ = (v_∥ / |B|) ω`.
* `cylVelocity_littlejohn`: at one point, `cylVelocity θ R (dX/dt) = λ (1, F) + w`.
* `norm_perturbation_le`: `‖w‖ ≤ max 1 R⁻¹ · 2H/(|q||B|²) ‖∇|B|‖` (sup norm on `ℝ × Plane`).
* `exists_lift_decomp`: the two statements together, for an orbit and a set `G` of lifted points
  on which the hypotheses hold; the decomposition is asserted at the times with `X τ ∈ G`.
* `abs_fst_cylVelocity_le`, `abs_angle_rate_le`, `abs_rate_le`: bounds on the angular speed.
* `hamiltonian_hasDerivAt`, `hamiltonian_eq_birth`: the energy `H = m v_∥²/2 + μ|B|` is constant
  on `[0, T]` (the all-time statement is `GCLittlejohn.energy_const`), so `H` in the bound may be
  replaced by its value at birth; `mass_mul_sq_le` bounds `v_∥` by the energy.

**Sanity.** `cylVelocity_decomp_example` checks the algebra of the decomposition on concrete
vectors. An instance with all hypotheses discharged (the toroidal field `∇φ`) is in
`Sanity/CylindricalDrift`.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.CylindricalDrift
open Fields GCLittlejohn Contract Set Fields.CylindricalLift
open scoped RealInnerProductSpace

variable {B : Space → Space} {m q μ : ℝ}

/-! ## The lifted path -/

/-- The position velocity is continuous on `[0, T]` when the Littlejohn right-hand side is
continuous at the states visited. -/
theorem continuousOn_velocity {b : GCBirth} {z : ℝ → Space × ℝ} {T : ℝ}
    (orbit : GCBirthOrbitOn B m q b z T)
    (cont : ∀ τ ∈ Icc 0 T, ContinuousAt (littlejohnVelocity B m q b.2.2) (z τ)) :
    ContinuousOn (fun τ => (littlejohnVelocity B m q b.2.2 (z τ)).1) (Icc 0 T) := fun τ hτ =>
  (continuous_fst.continuousAt.comp
    ((cont τ hτ).comp (orbit.2 τ hτ).continuousAt)).continuousWithinAt

/-- **Lifted cylindrical coordinates of a guiding-centre orbit.** An orbit on `[0, T]` that stays
off the `z`-axis, with continuous velocity, has a lifted path `X = (θ, (R, z))` whose velocity is
the cylindrical form of the guiding-centre velocity. -/
theorem exists_lift {b : GCBirth} {z : ℝ → Space × ℝ} {T θ₀ R₀ z₀ : ℝ} (hT : 0 ≤ T)
    (orbit : GCBirthOrbitOn B m q b z T)
    (hv : ContinuousOn (fun τ => (littlejohnVelocity B m q b.2.2 (z τ)).1) (Icc 0 T))
    (axis : ∀ τ ∈ Icc 0 T, 0 < (z τ).1 0 ^ 2 + (z τ).1 1 ^ 2)
    (start : b.1 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ τ ∈ Icc 0 T,
      (z τ).1 = cylPoint ((X τ).2 0) (X τ).1 ((X τ).2 1) ∧ 0 < (X τ).2 0 ∧
      HasDerivAt X (cylVelocity (X τ).1 ((X τ).2 0)
        (littlejohnVelocity B m q b.2.2 (z τ)).1) τ := by
  have pos : ∀ τ ∈ Icc 0 T, HasDerivAt (fun t => (z t).1)
      (littlejohnVelocity B m q b.2.2 (z τ)).1 τ := fun τ hτ =>
    (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt.comp_hasDerivAt τ (orbit.2 τ hτ)
  have start' : (z 0).1 = cylPoint R₀ θ₀ z₀ := by rw [orbit.1, start]
  obtain ⟨θ, R, hθ, hR, h⟩ := CylindricalLift.exists_lift hT pos hv axis start' hR₀
  refine ⟨fun σ => (θ σ, WithLp.toLp 2 ![R σ, (z σ).1 2]), ?_, fun τ hτ => ?_⟩
  · have h2 : (z 0).1 2 = z₀ := by rw [start']; exact (cylPoint_coords R₀ θ₀ z₀).2.2
    simp only [hθ, hR, h2]
  · obtain ⟨hpos, hpt, hd⟩ := h τ hτ
    exact ⟨hpt, hpos, hd⟩

/-! ## The decomposition at one point -/

/-- The cross-field drift in lifted cylindrical coordinates, at the lifted point `X` of the
guiding-centre state `z`. -/
def perturbation (B : Space → Space) (m q μ : ℝ) (z : Space × ℝ) (X : ℝ × Plane) : ℝ × Plane :=
  cylVelocity X.1 (X.2 0) (LabelDrift.drift B m q μ z)

/-- The coefficient of the space-time field `(1, F)` in the lifted guiding-centre velocity. -/
def rate (B : Space → Space) (ω : ℝ × Plane → ℝ) (z : Space × ℝ) (X : ℝ × Plane) : ℝ :=
  z.2 / ‖B z.1‖ * ω X

/-- **Lifted guiding-centre velocity.** At a state `w` whose position has lifted coordinates `p`,
where the field is differentiable, nonvanishing and curl-free, and has cylindrical velocity
`ω (1, F)`, the guiding-centre velocity is `(v_∥/|B|) ω (1, F)` plus the lifted drift. -/
theorem cylVelocity_littlejohn {F : ℝ → Plane → Plane} {ω : ℝ × Plane → ℝ} {p : ℝ × Plane}
    {w : Space × ℝ} (nzero : B w.1 ≠ 0) (diff : DifferentiableAt ℝ B w.1)
    (nocurl : curl (fderiv ℝ B w.1) = 0) (hq : q ≠ 0)
    (rel : cylVelocity p.1 (p.2 0) (B w.1) = ω p • FlowLabel.field F p) :
    cylVelocity p.1 (p.2 0) (littlejohnVelocity B m q μ w).1 =
      rate B ω w p • FlowLabel.field F p + perturbation B m q μ w p := by
  obtain ⟨x, v⟩ := w
  rw [LabelDrift.velocity_vacuum nzero diff nocurl hq, cylVelocity_add, cylVelocity_smul, rel,
    smul_smul]
  rfl

/-- The lifted drift is at most `max 1 R⁻¹ · 2H/(|q||B|²) ‖∇|B|‖`. -/
theorem norm_perturbation_le {p : ℝ × Plane} {w : Space × ℝ} (hR : 0 < p.2 0)
    (nzero : B w.1 ≠ 0) (hm : 0 ≤ m) (hμ : 0 ≤ μ) :
    ‖perturbation B m q μ w p‖ ≤ max 1 (p.2 0)⁻¹ *
      (2 * hamiltonian m μ B w.1 w.2 / (|q| * ‖B w.1‖ ^ 2) * ‖gradAbsB B w.1‖) := by
  obtain ⟨x, v⟩ := w
  exact (norm_cylVelocity_le hR _ _).trans (mul_le_mul_of_nonneg_left
    (LabelDrift.norm_drift_le nzero hm hμ v) (le_max_of_le_left zero_le_one))

/-! ## The angular speed -/

/-- The angular speed is at most the Cartesian speed over the radius. -/
theorem abs_fst_cylVelocity_le {R : ℝ} (hR : 0 < R) (θ : ℝ) (u : Space) :
    |(cylVelocity θ R u).1| ≤ ‖u‖ / R := by
  have hu : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hcs := Real.cos_sq_add_sin_sq θ
  have habs : |-Real.sin θ * u 0 + Real.cos θ * u 1| ≤ ‖u‖ := by
    refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hu]
    nlinarith [sq_nonneg (Real.cos θ * u 0 + Real.sin θ * u 1), sq_nonneg (u 2),
      sq_nonneg (u 0), sq_nonneg (u 1)]
  rw [cylVelocity, abs_div, abs_of_pos hR]
  exact div_le_div_of_nonneg_right habs hR.le

/-- The angular speed of a velocity `λ (1, F) + w` is at most `|λ| + ‖w‖`. -/
theorem abs_angle_rate_le (F : ℝ → Plane → Plane) (lam : ℝ) (p w : ℝ × Plane) :
    |(lam • FlowLabel.field F p + w).1| ≤ |lam| + ‖w‖ := by
  have h1 : (lam • FlowLabel.field F p + w).1 = lam + w.1 := by
    simp [FlowLabel.field]
  have h2 : |w.1| ≤ ‖w‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_fst_le w
  rw [h1]
  exact (abs_add_le _ _).trans (by linarith)

/-- The size of the coefficient `λ = (v_∥/|B|) ω`. -/
theorem abs_rate_eq (ω : ℝ × Plane → ℝ) (z : Space × ℝ) (X : ℝ × Plane) :
    |rate B ω z X| = |z.2| / ‖B z.1‖ * |ω X| := by
  rw [rate, abs_mul, abs_div, abs_of_nonneg (norm_nonneg _)]

/-- The angular speed of the lifted guiding centre: `|θ'| ≤ (|v_∥|/|B|) |ω| + ‖w‖`. -/
theorem abs_rate_le (F : ℝ → Plane → Plane) (ω : ℝ × Plane → ℝ) (z : Space × ℝ)
    (X w : ℝ × Plane) :
    |(rate B ω z X • FlowLabel.field F X + w).1| ≤ |z.2| / ‖B z.1‖ * |ω X| + ‖w‖ := by
  rw [← abs_rate_eq]
  exact abs_angle_rate_le F _ X w

/-! ## Conservation of the energy on a time interval -/

/-- The energy has zero derivative at a time where the Littlejohn equations hold and the field
strength is differentiable. -/
theorem hamiltonian_hasDerivAt {z : ℝ → Space × ℝ} {s : ℝ} (hm : m ≠ 0)
    (ode : HasDerivAt z (littlejohnVelocity B m q μ (z s)) s)
    (diff : DifferentiableAt ℝ (fun y => ‖B y‖) (z s).1) :
    HasDerivAt (fun t => hamiltonian m μ B (z t).1 (z t).2) 0 s := by
  have hX : HasDerivAt (fun t => (z t).1) (littlejohnVelocity B m q μ (z s)).1 s :=
    (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt.comp_hasDerivAt s ode
  have hv : HasDerivAt (fun t => (z t).2) (littlejohnVelocity B m q μ (z s)).2 s :=
    (ContinuousLinearMap.snd ℝ Space ℝ).hasFDerivAt.comp_hasDerivAt s ode
  have hn : HasDerivAt (fun t => ‖B (z t).1‖)
      (⟪gradAbsB B (z s).1, (littlejohnVelocity B m q μ (z s)).1⟫) s := by
    exact (diff.hasGradientAt.hasFDerivAt).comp_hasDerivAt s hX
  have hH := (((hv.pow 2).const_mul m).div_const 2).add (hn.const_mul μ)
  convert hH using 1
  · funext t; simp [hamiltonian]
  simp only [littlejohnVelocity]
  rw [inner_smul_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_cross_self', real_inner_comm (gradAbsB B (z s).1)]
  field_simp
  push_cast
  ring

/-- **Energy conservation on `[0, T]`.** Along an orbit whose field strength is differentiable at
the points visited, the energy keeps its value at birth. -/
theorem hamiltonian_eq_birth {b : GCBirth} {z : ℝ → Space × ℝ} {T : ℝ} (hm : m ≠ 0)
    (orbit : GCBirthOrbitOn B m q b z T)
    (diff : ∀ τ ∈ Icc 0 T, DifferentiableAt ℝ (fun y => ‖B y‖) (z τ).1) :
    ∀ τ ∈ Icc 0 T, hamiltonian m b.2.2 B (z τ).1 (z τ).2 = hamiltonian m b.2.2 B b.1 b.2.1 := by
  intro τ hτ
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt (fun t => hamiltonian m b.2.2 B (z t).1 (z t).2) 0 s :=
    fun s hs => hamiltonian_hasDerivAt hm (orbit.2 s hs) (diff s hs)
  have h := constant_of_has_deriv_right_zero
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) τ hτ
  simpa only [orbit.1] using h

/-- The parallel kinetic energy is at most the energy. -/
theorem mass_mul_sq_le (hμ : 0 ≤ μ) (x : Space) (v : ℝ) :
    m * v ^ 2 ≤ 2 * hamiltonian m μ B x v := by
  have h := mul_nonneg hμ (norm_nonneg (B x))
  rw [hamiltonian]
  linarith

/-! ## The lifted orbit with its decomposition -/

/-- **Lifted guiding-centre orbit along a planar field-line equation.** Let `G` be a set of
lifted points `(θ, (R, z))` at which `B` is differentiable, nonvanishing and curl-free, and has
cylindrical velocity `ω (1, F)`. An orbit on `[0, T]` off the axis with continuous velocity has a
lifted path `X`, and at every time with `X τ ∈ G` its velocity is
`λ (1, F) + w`, with `λ = (v_∥/|B|) ω` (`rate`) and `w` the lifted drift (`perturbation`), which
is bounded by the energy. -/
theorem exists_lift_decomp {F : ℝ → Plane → Plane} {ω : ℝ × Plane → ℝ} {G : Set (ℝ × Plane)}
    (diff : ∀ p ∈ G, DifferentiableAt ℝ B (cylPoint (p.2 0) p.1 (p.2 1)))
    (nzero : ∀ p ∈ G, B (cylPoint (p.2 0) p.1 (p.2 1)) ≠ 0)
    (nocurl : ∀ p ∈ G, curl (fderiv ℝ B (cylPoint (p.2 0) p.1 (p.2 1))) = 0)
    (rel : ∀ p ∈ G, cylVelocity p.1 (p.2 0) (B (cylPoint (p.2 0) p.1 (p.2 1))) =
      ω p • FlowLabel.field F p)
    {b : GCBirth} {z : ℝ → Space × ℝ} {T θ₀ R₀ z₀ : ℝ} (hT : 0 ≤ T) (hm : 0 ≤ m) (hq : q ≠ 0)
    (hμ : 0 ≤ b.2.2) (orbit : GCBirthOrbitOn B m q b z T)
    (hv : ContinuousOn (fun τ => (littlejohnVelocity B m q b.2.2 (z τ)).1) (Icc 0 T))
    (axis : ∀ τ ∈ Icc 0 T, 0 < (z τ).1 0 ^ 2 + (z τ).1 1 ^ 2)
    (start : b.1 = cylPoint R₀ θ₀ z₀) (hR₀ : 0 < R₀) :
    ∃ X : ℝ → ℝ × Plane, X 0 = (θ₀, WithLp.toLp 2 ![R₀, z₀]) ∧ ∀ τ ∈ Icc 0 T,
      (z τ).1 = cylPoint ((X τ).2 0) (X τ).1 ((X τ).2 1) ∧ 0 < (X τ).2 0 ∧
      (X τ ∈ G →
        HasDerivAt X (rate B ω (z τ) (X τ) • FlowLabel.field F (X τ) +
          perturbation B m q b.2.2 (z τ) (X τ)) τ ∧
        ‖perturbation B m q b.2.2 (z τ) (X τ)‖ ≤ max 1 ((X τ).2 0)⁻¹ *
          (2 * hamiltonian m b.2.2 B (z τ).1 (z τ).2 / (|q| * ‖B (z τ).1‖ ^ 2) *
            ‖gradAbsB B (z τ).1‖)) := by
  obtain ⟨X, hX0, h⟩ := exists_lift hT orbit hv axis start hR₀
  refine ⟨X, hX0, fun τ hτ => ?_⟩
  obtain ⟨hpt, hpos, hd⟩ := h τ hτ
  refine ⟨hpt, hpos, fun hG => ?_⟩
  have nz : B (z τ).1 ≠ 0 := by rw [hpt]; exact nzero _ hG
  have df : DifferentiableAt ℝ B (z τ).1 := by rw [hpt]; exact diff _ hG
  have nc : curl (fderiv ℝ B (z τ).1) = 0 := by rw [hpt]; exact nocurl _ hG
  have rl : cylVelocity (X τ).1 ((X τ).2 0) (B (z τ).1) = ω (X τ) • FlowLabel.field F (X τ) := by
    rw [hpt]; exact rel _ hG
  refine ⟨?_, norm_perturbation_le hpos nz hm hμ⟩
  rwa [← cylVelocity_littlejohn nz df nc hq rl]

/-! ## Sanity -/

/-- **Sanity**: the algebra of the decomposition on concrete vectors. At angle `0` and radius
`2`, the field `(0, 3, 0)` has cylindrical velocity `(3/2) (1, 0)`, and a velocity
`2 B + (1, 0, 5)` has cylindrical velocity `3 (1, 0) + (0, (1, 5))`. -/
theorem cylVelocity_decomp_example :
    cylVelocity 0 2 ((2 : ℝ) • (WithLp.toLp 2 ![0, 3, 0] : Space) + WithLp.toLp 2 ![1, 0, 5]) =
      (2 * (3 / 2) : ℝ) • FlowLabel.field (fun _ _ => (0 : Plane)) (0, WithLp.toLp 2 ![2, 0]) +
        cylVelocity 0 2 (WithLp.toLp 2 ![1, 0, 5]) := by
  refine Prod.ext ?_ ?_
  · simp [cylVelocity, FlowLabel.field]
    norm_num
  · ext i
    fin_cases i <;> simp [cylVelocity, FlowLabel.field]

end PlasmaLean.Kinetic.CylindricalDrift
