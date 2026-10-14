/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.HelicalDivergence
public import PlasmaLean.Kernel.Equilibrium

/-!
# An exact helically symmetric finite-pressure ideal-MHD equilibrium

Within the family of `HelicalDivergence` (unit pitch, `K = (-x₁, x₀, 1)`), take
`ψ = r² + a (1 + (2/3) r²) P` (`P = r² cos 2χ`), i.e. `b = 2a/3`, and the axial flux
function `F(ψ) = 4 + 2ψ`. This solves the helical Grad–Shafranov (JFKO) equation
`∇·(∇ψ/|K|²) + F F'/|K|² - 2F/|K|⁴ + μ₀ p'(ψ) = 0` with constant `μ₀ p' = -4`; the
solution was found by a symbolic polynomial search and is checked here directly:

* `force_balance`: the domain-kernel law `ForceBalance` (`J × B = ∇p`) holds at every
  point of space, with `J = (∇ × B)/μ₀` computed from the actual Fréchet derivative and
  `p = (p₀ - 4ψ)/μ₀` with its actual gradient;
* `field_divergence_free` (from `HelicalDivergence`): `∇ · B = 0` everywhere;
* `field_symmetric`, `field_firstIntegral`: helical symmetry and exact flux surfaces;
* `orbit_confined` (with `a = 1/4`): every full Newton–Lorentz orbit with normalized
  rigidity `m ‖v‖ ≤ |q|/16` starting at `r² < 1` with `ψ ≤ 1/8` stays at `r² < 1` and
  `ψ ≤ 5/16` for ALL real times. Because `{ψ ≤ c}` has an unbounded component at large `r`
  when `a ≠ 0`, the proof uses a separating shell `r² = 1` on which `ψ ≥ 7/12`;
* `fieldLine_confined`: the same tube is a forward field-line barrier;
* `pressure_nonneg`, `axis_values`, `beta_axis`: `p ≥ 0` on `{ψ ≤ p₀/4}`, the axial field
  on the magnetic axis is `4` and `β_axis = p₀/8`;
* `psi_not_axisymmetric`, `field_not_axisymmetric`: genuinely nonaxisymmetric for `a ≠ 0`.

Scope: dimensionless straight helical model (infinite aspect ratio) — the idealization of
quasi-helical symmetry; toroidal curvature is not treated. The field is not derived from
coils and the boundary is not matched to a vacuum region. No MHD or kinetic stability is
claimed. Orbits are supplied; their existence is not proved.
-/

open scoped RealInnerProductSpace

public section
noncomputable section
namespace PlasmaLean.Design.HelicalEquilibrium
open PlasmaLean.Fields PlasmaLean.Kinetic PlasmaLean.Design.HelicalFamily WithLp
open PlasmaLean.Design.HelicalStellarator (K K_norm_sq)

/-- The equilibrium field with helical ellipticity `a`. -/
@[expose] def eqField (a : ℝ) : Space → Space := field a (2 * a / 3) 4 2

/-- The equilibrium flux function. -/
@[expose] def eqPsi (a : ℝ) : Space → ℝ := psi a (2 * a / 3)

/-- Ampère current `J = (∇ × B)/μ₀`. -/
@[expose] def current (μ₀ a : ℝ) (x : Space) : Space :=
  μ₀⁻¹ • curl (fderiv ℝ (eqField a) x)

/-- Pressure `p = (p₀ - 4ψ)/μ₀`. -/
@[expose] def pressure (μ₀ p₀ a : ℝ) (x : Space) : ℝ := (p₀ - 4 * eqPsi a x) / μ₀

/-- Pressure gradient `∇p = -(4/μ₀) ∇ψ`. -/
@[expose] def pressureGrad (μ₀ a : ℝ) (x : Space) : Space :=
  (-4 / μ₀) • gPsi a (2 * a / 3) x

/-- The pressure gradient formula, as an actual Fréchet derivative. -/
theorem pressure_hasFDerivAt (μ₀ p₀ a : ℝ) (x : Space) :
    HasFDerivAt (pressure μ₀ p₀ a) (innerSL ℝ (pressureGrad μ₀ a x)) x := by
  have := (((psi_hasFDerivAt a (2 * a / 3) x).const_mul 4).const_sub p₀).const_mul μ₀⁻¹
  refine hfd this (fun y => by simp [pressure, eqPsi, div_eq_inv_mul]) ?_
  ext v
  simp [pressureGrad]
  ring

/-- Curl of the field derivative in coordinates. -/
theorem curl_fieldDeriv (a b F0 F1 : ℝ) (x : Space) :
    curl (fieldDeriv a b F0 F1 x) = toLp 2
      ![dB x (N2 a b F0 F1 x) (dN2 a b F0 F1 x) (basis 1) -
          dB x (N1 a b F0 F1 x) (dN1 a b F0 F1 x) (basis 2),
        dB x (N0 a b F0 F1 x) (dN0 a b F0 F1 x) (basis 2) -
          dB x (N2 a b F0 F1 x) (dN2 a b F0 F1 x) (basis 0),
        dB x (N1 a b F0 F1 x) (dN1 a b F0 F1 x) (basis 0) -
          dB x (N0 a b F0 F1 x) (dN0 a b F0 F1 x) (basis 1)] := by
  obtain ⟨c0, c1, c2⟩ := curl_coords (fieldDeriv a b F0 F1 x)
  apply space_ext
  · rw [c0, (fieldDeriv_apply _ _ _ _ _ _).2.2, (fieldDeriv_apply _ _ _ _ _ _).2.1]; simp
  · rw [c1, (fieldDeriv_apply _ _ _ _ _ _).1, (fieldDeriv_apply _ _ _ _ _ _).2.2]; simp
  · rw [c2, (fieldDeriv_apply _ _ _ _ _ _).2.1, (fieldDeriv_apply _ _ _ _ _ _).1]; simp

/-- The JFKO identity in vector form (with `μ₀ = 1`): `(∇ × B) × B = -4 ∇ψ`. -/
theorem curl_cross_field (a : ℝ) (x : Space) :
    cross (curl (fieldDeriv a (2 * a / 3) 4 2 x)) (field a (2 * a / 3) 4 2 x) =
      (-4 : ℝ) • gPsi a (2 * a / 3) x := by
  rw [curl_fieldDeriv]
  have hD := (D_pos x).ne'
  unfold D r2 at hD
  apply space_ext
  all_goals
    simp only [cross, cross_apply, dB, Dinv, D, r2, dN0, dG1, dP, dC, dS, P, amp, dP1, P1,
      dA, dR, dG2, dQ, Q, G2, Fv, psi, dF, dPsi, N0, G1, dDinv, basis, add_apply, smul_apply,
      sub_apply, PiLp.proj_apply, ne_eq, one_ne_zero, not_false_eq_true,
      PiLp.single_eq_of_ne, smul_eq_mul, Fin.reduceEq, PiLp.single_eq_same, neg_apply, dN1,
      dG0, dP0, P0, N1, G0, zero_ne_one, dN2, N2, field, gPsi, PiLp.smul_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
      Fin.isValue, mul_one, mul_zero, add_zero, zero_add, sub_zero]
  all_goals field_simp
  all_goals ring

open Matrix in
/-- Force balance `J × B = ∇p` (the domain-kernel law) at every point, with the actual
Ampère current and the actual pressure gradient. -/
theorem force_balance (μ₀ a : ℝ) (x : Space) :
    ForceBalance (ofLp (eqField a x)) (ofLp (current μ₀ a x)) (ofLp (pressureGrad μ₀ a x)) := by
  refine ⟨?_⟩
  have h := curl_cross_field a x
  have hc : current μ₀ a x = μ₀⁻¹ • curl (fieldDeriv a (2 * a / 3) 4 2 x) := by
    rw [current, eqField, (field_hasFDerivAt a (2 * a / 3) 4 2 x).fderiv]
  have e : ofLp (current μ₀ a x) ⨯₃ ofLp (eqField a x) =
      ofLp (cross (current μ₀ a x) (eqField a x)) := by simp [cross]
  rw [e, hc, ← crossBilinear_apply, map_smul, _root_.smul_apply,
    crossBilinear_apply, eqField, h, pressureGrad, smul_smul]
  congr 2
  ring

/-- Consequence via the kernel: the field is tangent to the isobars, `B · ∇p = 0`. -/
theorem field_pressure_tangent (μ₀ a : ℝ) (x : Space) :
    ofLp (eqField a x) ⬝ᵥ ofLp (pressureGrad μ₀ a x) = 0 := by
  have := force_balance μ₀ a x
  exact field_tangency _ (ofLp (current μ₀ a x)) _

/-- `∇ · B = 0` for the equilibrium field. -/
theorem eqField_divergence_free (a : ℝ) (x : Space) :
    divergence (fderiv ℝ (eqField a) x) = 0 :=
  field_divergence_free a (2 * a / 3) 4 2 x

/-- Helical symmetry of the magnetic force. -/
theorem eqField_symmetric (a : ℝ) : SymmetricFlux (eqField a) (gPsi a (2 * a / 3)) K :=
  field_symmetric a (2 * a / 3) 4 2

/-! ## On-axis values, pressure and nonaxisymmetry -/

/-- On the magnetic axis `x₀ = x₁ = 0`: `ψ = 0`, `B = (0, 0, 4)`. -/
theorem axis_values (a z : ℝ) :
    eqPsi a (toLp 2 ![0, 0, z]) = 0 ∧ eqField a (toLp 2 ![0, 0, z]) = toLp 2 ![0, 0, 4] := by
  constructor
  · simp [eqPsi, psi, r2, amp, P]
  · ext i
    fin_cases i <;> simp [eqField, field, Dinv, D, r2, N0, N1, N2, G0, G1, G2, Fv, psi, amp,
      P, Q, P0, P1]

/-- On-axis beta `2 μ₀ p / |B|² = p₀ / 8` (independent of `μ₀`). -/
theorem beta_axis (μ₀ p₀ a z : ℝ) (hμ : μ₀ ≠ 0) :
    2 * μ₀ * pressure μ₀ p₀ a (toLp 2 ![0, 0, z]) /
      ‖eqField a (toLp 2 ![0, 0, z])‖ ^ 2 = p₀ / 8 := by
  obtain ⟨h1, h2⟩ := axis_values a z
  rw [pressure, h1, h2, EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]
  field_simp
  ring

/-- The pressure is nonnegative on `{ψ ≤ p₀/4}` (for `μ₀ > 0`). -/
theorem pressure_nonneg (μ₀ p₀ a : ℝ) (hμ : 0 < μ₀) (x : Space) (hx : eqPsi a x ≤ p₀ / 4) :
    0 ≤ pressure μ₀ p₀ a x := by
  unfold pressure
  apply div_nonneg _ hμ.le
  linarith

/-- The flux function is not rotation invariant (for `a ≠ 0`). -/
theorem psi_not_axisymmetric (a : ℝ) (ha : a ≠ 0) :
    eqPsi a (toLp 2 ![1, 0, 0]) ≠ eqPsi a (toLp 2 ![0, 1, 0]) := by
  intro h
  have h' : a + 2 * a / 3 = -(2 * a / 3) + -a := by
    simpa [eqPsi, psi, r2, amp, P, C, S] using h
  exact ha (by linarith)

/-- The field is not axisymmetric: its axial component (preserved by rotations about the
axis) is `4 + 4a` at `(1,0,0)` and `4 - 4a` at `(0,1,0)`. -/
theorem field_not_axisymmetric (a : ℝ) (ha : a ≠ 0) :
    eqField a (toLp 2 ![1, 0, 0]) 2 ≠ eqField a (toLp 2 ![0, 1, 0]) 2 := by
  have e1 : eqField a (toLp 2 ![1, 0, 0]) 2 = 4 + 4 * a := by
    simp [eqField, field, Dinv, D, r2, N2, G0, G1, Fv, psi, amp, P, P0, P1, C, S]
    ring
  have e2 : eqField a (toLp 2 ![0, 1, 0]) 2 = 4 - 4 * a := by
    simp [eqField, field, Dinv, D, r2, N2, G0, G1, Fv, psi, amp, P, P0, P1, C, S]
    ring
  rw [e1, e2]
  intro h
  exact ha (by linarith)

/-! ## Separating shell and all-time confinement (`a = 1/4`) -/

/-- `|P| ≤ r²`. -/
theorem abs_P_le (x : Space) : |P x| ≤ r2 x := by
  have := HelicalStellarator.ellipse_le x
  simpa [P, C, S, r2, HelicalStellarator.r2] using this

/-- On the shell `r² = 1`, `ψ ≥ 7/12` (for `a = 1/4`). -/
theorem shell_bound (x : Space) (hx : r2 x = 1) : 7 / 12 ≤ eqPsi (1 / 4) x := by
  have hP := abs_P_le x
  rw [hx] at hP
  have hl := neg_abs_le (P x)
  unfold eqPsi psi amp
  rw [hx]
  nlinarith

/-- Inside the tube `r² ≤ 1` the symmetry generator has norm at most `3/2`. -/
theorem K_norm_le (x : Space) (hx : r2 x ≤ 1) : ‖K x‖ ≤ 3 / 2 := by
  have h2 : ‖K x‖ ^ 2 ≤ (3 / 2) ^ 2 := by
    rw [K_norm_sq]; unfold HelicalStellarator.r2; unfold r2 at hx; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h2

/-- `r²` is continuous. -/
theorem continuous_r2 : Continuous r2 := by unfold r2; fun_prop

/-- All-time full-orbit confinement in the exact helical equilibrium (`a = 1/4`): for
every mass `m ≠ 0` and charge `q ≠ 0`, an orbit with normalized rigidity at most `1/16`
starting at `r² < 1` with `ψ ≤ 1/8` satisfies `r² < 1` and `ψ ≤ 5/16` for all real times. -/
theorem orbit_confined {m q : ℝ} (hm : m ≠ 0) (hq : q ≠ 0) {x v : ℝ → Space}
    (h : LorentzOrbit m q (fun _ => 0) (eqField (1 / 4)) x v)
    (hrig : |m| * ‖v 0‖ ≤ |q| / 16) (hr0 : r2 (x 0) < 1) (hψ0 : eqPsi (1 / 4) (x 0) ≤ 1 / 8)
    (t : ℝ) : r2 (x t) < 1 ∧ eqPsi (1 / 4) (x t) ≤ 5 / 16 := by
  have hqpos : 0 < |q| := abs_pos.mpr hq
  have hband (s : ℝ) (hs : r2 (x s) ≤ 1) : eqPsi (1 / 4) (x s) ≤ 5 / 16 := by
    have hb := noether_flux_band hm h (helicalK_killing 1)
      (psi_hasFDerivAt (1 / 4) (2 * (1 / 4) / 3)) (eqField_symmetric (1 / 4)) s
    have hKs := K_norm_le _ hs
    have hK0 := K_norm_le _ hr0.le
    have h3 : |m| * ‖v 0‖ * (‖K (x s)‖ + ‖K (x 0)‖) ≤ |q| / 16 * 3 :=
      mul_le_mul hrig (by linarith) (by positivity) (by positivity)
    have h4 : |q| * (eqPsi (1 / 4) (x s) - eqPsi (1 / 4) (x 0)) ≤ |q| * (3 / 16) := by
      have := le_abs_self (eqPsi (1 / 4) (x s) - eqPsi (1 / 4) (x 0))
      unfold eqPsi at *
      nlinarith
    have := le_of_mul_le_mul_left h4 hqpos
    linarith
  have hr : r2 (x t) < 1 := by
    by_contra hge
    push Not at hge
    have hcont : Continuous fun s => r2 (x s) := continuous_r2.comp h.continuous_position
    obtain ⟨s, -, hs⟩ := intermediate_value_uIcc (a := 0) (b := t) hcont.continuousOn
      (Set.mem_uIcc.mpr (Or.inl ⟨hr0.le, hge⟩))
    have := hband s hs.le
    have := shell_bound _ hs
    linarith
  exact ⟨hr, hband t hr.le⟩

/-- The tube is also a forward field-line barrier: a field line starting at `r² < 1` with
`ψ ≤ 1/2` never reaches the shell `r² = 1`. -/
theorem fieldLine_confined {γ : ℝ → Space} (hγ : IsForwardFieldLine (eqField (1 / 4)) γ)
    (hr0 : r2 (γ 0) < 1) (hψ0 : eqPsi (1 / 4) (γ 0) ≤ 1 / 2) {t : ℝ} (ht : 0 ≤ t) :
    r2 (γ t) < 1 ∧ eqPsi (1 / 4) (γ t) = eqPsi (1 / 4) (γ 0) := by
  have hfi := field_firstIntegral (1 / 4) (2 * (1 / 4) / 3) 4 2
  have hcons (s : ℝ) (hs : 0 ≤ s) : eqPsi (1 / 4) (γ s) = eqPsi (1 / 4) (γ 0) :=
    firstIntegral_conserved_forward hfi hγ hs
  refine ⟨?_, hcons t ht⟩
  by_contra hge
  push Not at hge
  have hcont : ContinuousOn (fun s => r2 (γ s)) (Set.Icc 0 t) := by
    refine continuous_r2.comp_continuousOn ?_
    intro s hs
    exact (hγ s hs.1).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hseq⟩ := intermediate_value_Icc ht hcont ⟨hr0.le, hge⟩
  have := shell_bound _ hseq
  have := hcons s hs.1
  linarith

end PlasmaLean.Design.HelicalEquilibrium
