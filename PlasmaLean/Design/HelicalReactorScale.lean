/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalEquilibrium

/-!
# A reactor-scale SI instance of the exact helical equilibrium

Scale the dimensionless helical equilibrium of `HelicalEquilibrium` (ellipticity `a = 1/4`)
by a pitch length `L` (metres) and a field unit `B_u` (tesla):
`B(X) = B_u B̂(X/L)`, `p(X) = B_u² (p₀ - 4 ψ(X/L))/μ₀`, `J = (∇ × B)/μ₀`.

General scaling results (any `L, B_u ≠ 0`):

* `scaled_force_balance`: the kernel law `ForceBalance` (`J × B = ∇p`) holds at every point
  for the scaled fields, with actual derivatives;
* `scaled_orbit`: a physical Newton–Lorentz orbit of mass `M`, charge `Q` becomes a
  dimensionless orbit with charge `Q B_u` and velocity `V/L`.

Plasma region. The pressure vanishes on the flux surface `ψ = ψ_b = p₀/4`. The smooth
formula continues to negative pressure outside; replacing it there by `p = 0` would NOT
be an equilibrium of the same field, since `(∇ × B) × B = -4 ∇ψ ≠ 0` (it would require a
pressure-jump current sheet and a different exterior field, not treated here). All claims
about physical plasma therefore concern the region `ψ ≤ ψ_b`, and the orbit theorem shows
that the covered particles never leave it. (The orbit hypothesis is stated for the smooth
field on all of space; only its values in the plasma region are sampled along the orbit,
but that localization is not formalized.)

Reactor-scale choice (`reactor_*`): `L = 2 m` (helical period `π L ≈ 6.3 m`),
`B_u = 5/4 T` so that the axial field on the magnetic axis is `5 T`, `p₀ = 8/25` so that
`β_axis = p₀/8 = 4%` exactly and the peak pressure is `≈ 0.398 MPa`. The confinement
theorem `plasma_orbit_confined` keeps particles at radius `r < L/√8 ≈ 0.71 m` and inside
the pressure-positive plasma `ψ ≤ ψ_b` for ALL times, for every deuteron up to 30 keV and
every alpha particle up to 60 keV starting near the axis (`reactor_deuteron_confined`,
`reactor_alpha_confined`). Fusion-born 3.5 MeV alphas are NOT covered by this crude
canonical-momentum bound.

Scope: straight helical model (infinite aspect ratio), not a toroidal stellarator; not
coil-derived; no stability claim; orbits supplied, non-relativistic and collisionless.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.HelicalReactorScale
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Design.HelicalFamily
  PlasmaLean.Design.HelicalEquilibrium WithLp
open PlasmaLean.Design.HelicalStellarator (K K_norm_sq)

/-! ## Plasma-region confinement in dimensionless form -/

/-- On the shell `r² = 1/8`, `ψ ≥ 35/384` (for `a = 1/4`). -/
theorem inner_shell_bound (x : Space) (hx : r2 x = 1 / 8) : 35 / 384 ≤ eqPsi (1 / 4) x := by
  have hP := abs_P_le x
  rw [hx] at hP
  have hl := neg_abs_le (P x)
  unfold eqPsi psi amp
  rw [hx]
  nlinarith

/-- Inside `r² ≤ 1/8`, `‖K‖ ≤ 17/16`. -/
theorem K_norm_le_inner (x : Space) (hx : r2 x ≤ 1 / 8) : ‖K x‖ ≤ 17 / 16 := by
  have h2 : ‖K x‖ ^ 2 ≤ (17 / 16) ^ 2 := by
    rw [K_norm_sq]; unfold HelicalStellarator.r2; unfold r2 at hx; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h2

/-- Dimensionless plasma-region confinement: with normalized rigidity at most `1/64`,
an orbit starting at `r² < 1/8` with `ψ ≤ 1/25` keeps `r² < 1/8` and `ψ ≤ 2/25` for all
real times; with `p₀ = 8/25` this is the pressure-positive plasma `ψ ≤ p₀/4`. -/
theorem plasma_orbit_confined {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (eqField (1 / 4)) x v)
    (hrig : |m| * ‖v 0‖ ≤ |q| / 64) (hr0 : r2 (x 0) < 1 / 8)
    (hψ0 : eqPsi (1 / 4) (x 0) ≤ 1 / 25) (t : ℝ) :
    r2 (x t) < 1 / 8 ∧ eqPsi (1 / 4) (x t) ≤ 2 / 25 := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hband (s : ℝ) (hs : r2 (x s) ≤ 1 / 8) : eqPsi (1 / 4) (x s) ≤ 2 / 25 := by
    have hb := noether_flux_band hm h (helicalK_killing 1)
      (psi_hasFDerivAt (1 / 4) (2 * (1 / 4) / 3)) (eqField_symmetric (1 / 4)) s
    have hKs := K_norm_le_inner _ hs
    have hK0 := K_norm_le_inner _ hr0.le
    have h3 : |m| * ‖v 0‖ * (‖K (x s)‖ + ‖K (x 0)‖) ≤ |q| / 64 * (17 / 8) :=
      mul_le_mul hrig (by linarith) (by positivity) (by positivity)
    have h4 : |q| * (eqPsi (1 / 4) (x s) - eqPsi (1 / 4) (x 0)) ≤ |q| * (17 / 512) := by
      have := le_abs_self (eqPsi (1 / 4) (x s) - eqPsi (1 / 4) (x 0))
      unfold eqPsi at *
      nlinarith
    have := le_of_mul_le_mul_left h4 hqpos
    linarith
  have hr : r2 (x t) < 1 / 8 := by
    by_contra hge
    push Not at hge
    have hcont : Continuous fun s => r2 (x s) := continuous_r2.comp h.continuous_position
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hcont.continuousOn
      (Set.mem_uIcc.mpr (Or.inl ⟨hr0.le, hge⟩))
    have := hband s hs.le
    have := inner_shell_bound _ hs
    linarith
  exact ⟨hr, hband t hr.le⟩

/-! ## Scaling to physical units -/

/-- Physical field `B(X) = B_u B̂(X/L)`. -/
@[expose] def physField (Bu L : ℝ) (X : Space) : Space := Bu • eqField (1 / 4) (L⁻¹ • X)

/-- Physical pressure `p(X) = B_u² (p₀ - 4 ψ(X/L))/μ₀`. -/
@[expose] def physPressure (μ₀ p₀ Bu L : ℝ) (X : Space) : ℝ :=
  Bu ^ 2 * pressure μ₀ p₀ (1 / 4) (L⁻¹ • X)

/-- Physical pressure gradient. -/
@[expose] def physPressureGrad (μ₀ Bu L : ℝ) (X : Space) : Space :=
  (Bu ^ 2 * L⁻¹) • pressureGrad μ₀ (1 / 4) (L⁻¹ • X)

/-- Physical Ampère current `J = (∇ × B)/μ₀`. -/
@[expose] def physCurrent (μ₀ Bu L : ℝ) (X : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (physField Bu L) X)

/-- The scaled pressure gradient is the actual derivative. -/
theorem physPressure_hasFDerivAt (μ₀ p₀ Bu L : ℝ) (X : Space) :
    HasFDerivAt (physPressure μ₀ p₀ Bu L) (innerSL ℝ (physPressureGrad μ₀ Bu L X)) X := by
  have hs : HasFDerivAt (fun Y : Space => L⁻¹ • Y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) X :=
    (hasFDerivAt_id X).const_smul L⁻¹
  have := ((pressure_hasFDerivAt μ₀ p₀ (1 / 4) (L⁻¹ • X)).comp X hs).const_mul (Bu ^ 2)
  refine this.congr_fderiv ?_
  ext v
  simp [physPressureGrad]
  ring

/-- Scalars pull out of the first factor of the cross product. -/
theorem cross_smul_left' (c : ℝ) (u w : Space) : cross (c • u) w = c • cross u w := by
  rw [← crossBilinear_apply, map_smul, _root_.smul_apply, crossBilinear_apply]

/-- Derivative of the scaled field. -/
theorem physField_hasFDerivAt (Bu L : ℝ) (X : Space) :
    HasFDerivAt (physField Bu L)
      ((Bu * L⁻¹) • fieldDeriv (1 / 4) (2 * (1 / 4) / 3) 4 2 (L⁻¹ • X)) X := by
  have hs : HasFDerivAt (fun Y : Space => L⁻¹ • Y) (L⁻¹ • ContinuousLinearMap.id ℝ Space) X :=
    (hasFDerivAt_id X).const_smul L⁻¹
  have := ((field_hasFDerivAt (1 / 4) (2 * (1 / 4) / 3) 4 2 (L⁻¹ • X)).comp X hs).const_smul Bu
  refine this.congr_fderiv ?_
  ext v i
  simp [mul_smul, smul_comm Bu L⁻¹]

/-- Force balance `J × B = ∇p` at every point for the scaled fields (`L ≠ 0`). -/
theorem scaled_force_balance (μ₀ Bu L : ℝ) (X : Space) :
    ForceBalance (ofLp (physField Bu L X)) (ofLp (physCurrent μ₀ Bu L X))
      (ofLp (physPressureGrad μ₀ Bu L X)) := by
  refine ⟨?_⟩
  have h := curl_cross_field (1 / 4) (L⁻¹ • X)
  have hc : physCurrent μ₀ Bu L X =
      (μ₀⁻¹ * (Bu * L⁻¹)) • curl (fieldDeriv (1 / 4) (2 * (1 / 4) / 3) 4 2 (L⁻¹ • X)) := by
    rw [physCurrent, (physField_hasFDerivAt Bu L X).fderiv, curl, map_smul, smul_smul]
    rfl
  have e : crossProduct (ofLp (physCurrent μ₀ Bu L X)) (ofLp (physField Bu L X)) =
      ofLp (cross (physCurrent μ₀ Bu L X) (physField Bu L X)) := by simp [cross]
  rw [e, hc, physField, cross_smul_left', cross_smul_right]
  change ofLp ((μ₀⁻¹ * (Bu * L⁻¹)) • Bu • cross (curl (fieldDeriv (1 / 4) (2 * (1 / 4) / 3) 4 2
    (L⁻¹ • X))) (field (1 / 4) (2 * (1 / 4) / 3) 4 2 (L⁻¹ • X))) = _
  rw [h, physPressureGrad, pressureGrad, smul_smul, smul_smul, smul_smul]
  congr 2
  ring

/-- A physical orbit in the scaled field is a dimensionless orbit with charge `Q B_u` and
velocity `V/L`. -/
theorem scaled_orbit {M Q Bu L : ℝ} {X V : ℝ → Space}
    (h : LorentzOrbit M Q (fun _ => 0) (physField Bu L) X V) :
    LorentzOrbit M (Q * Bu) (fun _ => 0) (eqField (1 / 4)) (fun t => L⁻¹ • X t)
      (fun t => L⁻¹ • V t) := by
  refine ⟨fun t => (h.position t).const_smul L⁻¹, fun t => ?_⟩
  obtain ⟨A, hA, hlaw⟩ := h.newton t
  refine ⟨L⁻¹ • A, hA.const_smul L⁻¹, ?_⟩
  rw [zero_add] at hlaw ⊢
  rw [physField, cross_smul_right] at hlaw
  have hl : cross (L⁻¹ • V t) (eqField (1 / 4) (L⁻¹ • X t)) =
      L⁻¹ • cross (V t) (eqField (1 / 4) (L⁻¹ • X t)) := cross_smul_left' _ _ _
  rw [hl, smul_comm M L⁻¹ A, hlaw, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- Physical radius bound: `r²(X/L) < 1/8` means `X₀² + X₁² < L²/8`. -/
theorem r2_scaled (L : ℝ) (hL : L ≠ 0) (X : Space) :
    r2 (L⁻¹ • X) < 1 / 8 ↔ X 0 ^ 2 + X 1 ^ 2 < L ^ 2 / 8 := by
  have hL2 : 0 < L ^ 2 := by positivity
  simp only [r2, PiLp.smul_apply, smul_eq_mul]
  rw [show (L⁻¹ * X 0) ^ 2 + (L⁻¹ * X 1) ^ 2 = (X 0 ^ 2 + X 1 ^ 2) / L ^ 2 by
    field_simp]
  rw [div_lt_iff₀ hL2]
  constructor <;> intro h <;> linarith

/-- Physical plasma-region confinement for the scaled field (`L, B_u > 0`, `M, Q ≠ 0`):
rigidity `|M| ‖V‖ ≤ |Q| B_u L / 64`, start at radius² `< L²/8` with `ψ(X/L) ≤ 1/25`. -/
theorem physical_orbit_confined {M Q Bu L : ℝ} (hM : M ≠ 0) (hQ : Q ≠ 0) (hBu : 0 < Bu)
    (hL : 0 < L) {X V : ℝ → Space} (h : LorentzOrbit M Q (fun _ => 0) (physField Bu L) X V)
    (hrig : |M| * ‖V 0‖ ≤ |Q| * Bu * L / 64) (hr0 : X 0 0 ^ 2 + X 0 1 ^ 2 < L ^ 2 / 8)
    (hψ0 : eqPsi (1 / 4) (L⁻¹ • X 0) ≤ 1 / 25) (t : ℝ) :
    X t 0 ^ 2 + X t 1 ^ 2 < L ^ 2 / 8 ∧ eqPsi (1 / 4) (L⁻¹ • X t) ≤ 2 / 25 := by
  have hs := scaled_orbit h
  have hq : Q * Bu ≠ 0 := mul_ne_zero hQ hBu.ne'
  have hrig' : |M| * ‖L⁻¹ • V 0‖ ≤ |Q * Bu| / 64 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL, abs_mul, abs_of_pos hBu]
    have : |M| * (L⁻¹ * ‖V 0‖) = (|M| * ‖V 0‖) / L := by field_simp
    rw [this, div_le_iff₀ hL]
    linarith
  have hr0' : r2 (L⁻¹ • X 0) < 1 / 8 := (r2_scaled L hL.ne' (X 0)).mpr hr0
  obtain ⟨h1, h2⟩ := plasma_orbit_confined hM hq hs hrig' hr0' hψ0 t
  exact ⟨(r2_scaled L hL.ne' (X t)).mp h1, h2⟩

/-! ## Reactor-scale numbers: `L = 2 m`, `B_u = 5/4 T`, `p₀ = 8/25` -/

/-- The axial field on the magnetic axis is `5 T`. -/
theorem reactor_axis_field (z : ℝ) :
    physField (5 / 4) 2 (toLp 2 ![0, 0, z]) = toLp 2 ![0, 0, 5] := by
  have h := (axis_values (1 / 4) (2⁻¹ * z)).2
  have e : (2 : ℝ)⁻¹ • (toLp 2 ![0, 0, z] : Space) = toLp 2 ![0, 0, 2⁻¹ * z] := by
    ext i; fin_cases i <;> simp
  rw [physField, e, h]
  ext i; fin_cases i <;> norm_num

/-- `β_axis = 2 μ₀ p / |B|² = 4%` exactly (independent of `μ₀`). -/
theorem reactor_beta_axis (μ₀ z : ℝ) (hμ : μ₀ ≠ 0) :
    2 * μ₀ * physPressure μ₀ (8 / 25) (5 / 4) 2 (toLp 2 ![0, 0, z]) /
      ‖physField (5 / 4) 2 (toLp 2 ![0, 0, z])‖ ^ 2 = 1 / 25 := by
  have e : (2 : ℝ)⁻¹ • (toLp 2 ![0, 0, z] : Space) = toLp 2 ![0, 0, 2⁻¹ * z] := by
    ext i; fin_cases i <;> simp
  rw [reactor_axis_field, physPressure, e, pressure, (axis_values (1 / 4) (2⁻¹ * z)).1,
    EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  field_simp
  norm_num

/-- Peak (on-axis) pressure `B_u² p₀ / μ₀ = 1/(2 μ₀)` lies between 0.3978 and 0.3979 MPa. -/
theorem reactor_peak_pressure (μ₀ z : ℝ) (h1 : 1.2566e-6 ≤ μ₀) (h2 : μ₀ ≤ 1.2567e-6) :
    397800 ≤ physPressure μ₀ (8 / 25) (5 / 4) 2 (toLp 2 ![0, 0, z]) ∧
      physPressure μ₀ (8 / 25) (5 / 4) 2 (toLp 2 ![0, 0, z]) ≤ 397900 := by
  have hμ : 0 < μ₀ := lt_of_lt_of_le (by norm_num) h1
  have e : (2 : ℝ)⁻¹ • (toLp 2 ![0, 0, z] : Space) = toLp 2 ![0, 0, 2⁻¹ * z] := by
    ext i; fin_cases i <;> simp
  rw [physPressure, e, pressure, (axis_values (1 / 4) (2⁻¹ * z)).1]
  constructor
  · rw [show (5 / 4 : ℝ) ^ 2 * ((8 / 25 - 4 * 0) / μ₀) = 1 / (2 * μ₀) by field_simp; ring,
      le_div_iff₀ (by positivity)]
    nlinarith
  · rw [show (5 / 4 : ℝ) ^ 2 * ((8 / 25 - 4 * 0) / μ₀) = 1 / (2 * μ₀) by field_simp; ring,
      div_le_iff₀ (by positivity)]
    nlinarith

/-- Along a confined orbit the physical pressure is nonnegative (the orbit stays in the
plasma `ψ ≤ p₀/4 = 2/25`). -/
theorem reactor_pressure_nonneg (μ₀ : ℝ) (hμ : 0 < μ₀) (X : Space)
    (hX : eqPsi (1 / 4) ((2 : ℝ)⁻¹ • X) ≤ 2 / 25) :
    0 ≤ physPressure μ₀ (8 / 25) (5 / 4) 2 X := by
  unfold physPressure
  exact mul_nonneg (by positivity) (pressure_nonneg μ₀ _ _ hμ _ (by linarith))

/-- Deuterons (`3.3436e-27 kg`, `1.6022e-19 C`) of kinetic energy at most 30 keV satisfy
the rigidity hypothesis `M ‖V‖ ≤ Q B_u L / 64` with `B_u L = 5/2 T m`. -/
theorem deuteron_rigidity (s : ℝ) (hK : 3.3436e-27 * s ^ 2 ≤ 2 * (30e3 * 1.6022e-19)) :
    |(3.3436e-27 : ℝ)| * s ≤ |(1.6022e-19 : ℝ)| * (5 / 4) * 2 / 64 := by
  rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
  nlinarith [sq_nonneg (3.3436e-27 * s - 1.6022e-19 * (5 / 4) * 2 / 64)]

/-- Alpha particles (`6.6447e-27 kg`, `2 × 1.6022e-19 C`) up to 60 keV satisfy it too. -/
theorem alpha_rigidity (s : ℝ) (hK : 6.6447e-27 * s ^ 2 ≤ 2 * (60e3 * 1.6022e-19)) :
    |(6.6447e-27 : ℝ)| * s ≤ |(2 * 1.6022e-19 : ℝ)| * (5 / 4) * 2 / 64 := by
  rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
  nlinarith [sq_nonneg (6.6447e-27 * s - 2 * 1.6022e-19 * (5 / 4) * 2 / 64)]

/-- All-time confinement of every deuteron up to 30 keV starting within radius² `< 1/2 m²`
with `ψ(X/L) ≤ 1/25`: it stays at radius² `< 1/2 m²` (`r < 0.71 m`) inside the
pressure-positive plasma, for all times. -/
theorem reactor_deuteron_confined {X V : ℝ → Space}
    (h : LorentzOrbit 3.3436e-27 1.6022e-19 (fun _ => 0) (physField (5 / 4) 2) X V)
    (hK : 3.3436e-27 * ‖V 0‖ ^ 2 ≤ 2 * (30e3 * 1.6022e-19))
    (hr0 : X 0 0 ^ 2 + X 0 1 ^ 2 < 2 ^ 2 / 8)
    (hψ0 : eqPsi (1 / 4) ((2 : ℝ)⁻¹ • X 0) ≤ 1 / 25) (t : ℝ) :
    X t 0 ^ 2 + X t 1 ^ 2 < 2 ^ 2 / 8 ∧ eqPsi (1 / 4) ((2 : ℝ)⁻¹ • X t) ≤ 2 / 25 :=
  physical_orbit_confined (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    (deuteron_rigidity _ hK) hr0 hψ0 t

/-- The same all-time confinement for alpha particles up to 60 keV. -/
theorem reactor_alpha_confined {X V : ℝ → Space}
    (h : LorentzOrbit 6.6447e-27 (2 * 1.6022e-19) (fun _ => 0) (physField (5 / 4) 2) X V)
    (hK : 6.6447e-27 * ‖V 0‖ ^ 2 ≤ 2 * (60e3 * 1.6022e-19))
    (hr0 : X 0 0 ^ 2 + X 0 1 ^ 2 < 2 ^ 2 / 8)
    (hψ0 : eqPsi (1 / 4) ((2 : ℝ)⁻¹ • X 0) ≤ 1 / 25) (t : ℝ) :
    X t 0 ^ 2 + X t 1 ^ 2 < 2 ^ 2 / 8 ∧ eqPsi (1 / 4) ((2 : ℝ)⁻¹ • X t) ≤ 2 / 25 :=
  physical_orbit_confined (by norm_num) (by norm_num) (by norm_num) (by norm_num) h
    (alpha_rigidity _ hK) hr0 hψ0 t

end PlasmaLean.Design.HelicalReactorScale
