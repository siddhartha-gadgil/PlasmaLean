/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnLocal
public import PlasmaLean.Theory.Fields.BiotSavart

/-!
# Drift of field-line labels along Littlejohn guiding centres

A **label** is a function `L` on space that is constant along field lines: `∇L · B = 0`. Along a
solution of the Littlejohn equations (a supplied model, see `Kinetic/GuidingCentreLittlejohn`)
the parallel motion does not change `L`, so its rate of change comes from the cross-field drift
alone.

* `label_hasDerivAt`: `d/dt L(X) = (B*_∥)⁻¹ ((m v_∥²/q) ∇L·(∇×b) + (μ/q) ∇L·(b × ∇|B|))`.
* `rate_vacuum`: for a nonvanishing curl-free field this is
  `(m v_∥² + μ|B|)/(q|B|²) ∇L·(b × ∇|B|)`.
* `abs_rate_vacuum_le`: with `m, μ ≥ 0` its size is at most
  `2H/(|q||B|²) ‖∇L‖ ‖∇|B|‖`, `H = m v_∥²/2 + μ|B|` the conserved energy.
* `label_displacement_le`: a uniform rate bound `ρ` on the part of an orbit in `[0, T]` gives
  `|L(X(t)) − L(X(0))| ≤ ρ t`.

The last statement is the direct first-order drift bound. It has no averaging over the bounce
motion, so it is useful on the scale of one bounce only.
-/

@[expose] public section
noncomputable section
namespace PlasmaLean.Kinetic.LabelDrift
open Fields GCLittlejohn Contract Set
open scoped RealInnerProductSpace

variable {B : Space → Space} {L : Space → ℝ} {m q μ : ℝ}

/-- Rate of change of a label at a guiding-centre state `(X, v_∥)`. -/
def rate (B : Space → Space) (L : Space → ℝ) (m q μ : ℝ) (w : Space × ℝ) : ℝ :=
  (BstarPar m q B w.2 w.1)⁻¹ * (m * w.2 ^ 2 / q * ⟪gradient L w.1, curlb B w.1⟫ +
    μ / q * ⟪gradient L w.1, cross (bhat B w.1) (gradAbsB B w.1)⟫)

/-- Along a Littlejohn solution a label changes only through the cross-field drift. -/
theorem label_hasDerivAt {z : ℝ → Space × ℝ} {s : ℝ}
    (ode : HasDerivAt z (littlejohnVelocity B m q μ (z s)) s)
    (diff : DifferentiableAt ℝ L (z s).1) (along : ⟪gradient L (z s).1, B (z s).1⟫ = 0) :
    HasDerivAt (fun t => L (z t).1) (rate B L m q μ (z s)) s := by
  have pos : HasDerivAt (fun t => (z t).1) (littlejohnVelocity B m q μ (z s)).1 s :=
    (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt.comp_hasDerivAt s ode
  have h := diff.hasGradientAt.hasFDerivAt.comp_hasDerivAt s pos
  have value : rate B L m q μ (z s) =
      (InnerProductSpace.toDual ℝ Space (gradient L (z s).1))
        (littlejohnVelocity B m q μ (z s)).1 := by
    simp only [rate, littlejohnVelocity, Bstar, InnerProductSpace.toDual_apply_apply,
      inner_smul_right, inner_add_right, along]
    ring
  rw [value]
  exact h

/-- In a nonvanishing curl-free field the curvature and gradient drifts combine. -/
theorem rate_vacuum {x : Space} (nzero : B x ≠ 0) (diff : DifferentiableAt ℝ B x)
    (nocurl : curl (fderiv ℝ B x) = 0) (v : ℝ) :
    rate B L m q μ (x, v) = (m * v ^ 2 + μ * ‖B x‖) / (q * ‖B x‖ ^ 2) *
      ⟪gradient L x, cross (bhat B x) (gradAbsB B x)⟫ := by
  have hn := norm_ne_zero_iff.mpr nzero
  have dn := diff.norm ℝ nzero
  have mul := curl_fderiv_smul (f := fun y => ‖B y‖⁻¹) (dn.inv hn) diff
  have curl_unit : curlb B x = cross (gradient (fun y => ‖B y‖⁻¹) x) (B x) := by
    change curl (fderiv ℝ (fun y => ‖B y‖⁻¹ • B y) x) = _
    simpa only [nocurl, smul_zero, zero_add] using mul
  have grad_inv : gradient (fun y => ‖B y‖⁻¹) x = (-(‖B x‖ ^ 2)⁻¹) • gradAbsB B x := by
    have hi := (hasDerivAt_inv hn).comp_hasFDerivAt x dn.hasGradientAt.hasFDerivAt
    have hg : HasGradientAt (fun y => ‖B y‖⁻¹) ((-(‖B x‖ ^ 2)⁻¹) • gradAbsB B x) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert hi using 1
      · rfl
      · rw [map_smul]
        rfl
    exact hg.gradient
  have swap : cross (gradAbsB B x) (B x) = -cross (B x) (gradAbsB B x) := by
    simp only [cross, ← WithLp.toLp_neg]
    rw [← cross_anticomm]
  have left (c : ℝ) (u w : Space) : cross (c • u) w = c • cross u w := by
    simp only [cross, WithLp.ofLp_smul, map_smul, LinearMap.smul_apply, WithLp.toLp_smul]
  have unit : cross (bhat B x) (gradAbsB B x) = ‖B x‖⁻¹ • cross (B x) (gradAbsB B x) := left _ _ _
  change (BstarPar m q B v x)⁻¹ * _ = _
  rw [VacuumLittlejohnLocal.parallel_eq_norm nzero diff nocurl, curl_unit, grad_inv,
    left, swap, unit]
  simp only [inner_smul_right, inner_neg_right]
  field_simp

/-- Size of the vacuum label rate in terms of the conserved energy. -/
theorem abs_rate_vacuum_le {x : Space} (nzero : B x ≠ 0) (diff : DifferentiableAt ℝ B x)
    (nocurl : curl (fderiv ℝ B x) = 0) (hm : 0 ≤ m) (hμ : 0 ≤ μ) (v : ℝ) :
    |rate B L m q μ (x, v)| ≤ 2 * hamiltonian m μ B x v / (|q| * ‖B x‖ ^ 2) *
      (‖gradient L x‖ * ‖gradAbsB B x‖) := by
  have hn : 0 < ‖B x‖ := norm_pos_iff.mpr nzero
  have den : |q * ‖B x‖ ^ 2| = |q| * ‖B x‖ ^ 2 := by rw [abs_mul, abs_of_pos (pow_pos hn 2)]
  rw [rate_vacuum nzero diff nocurl, abs_mul, abs_div, den]
  have num : |m * v ^ 2 + μ * ‖B x‖| ≤ 2 * hamiltonian m μ B x v := by
    have h1 : 0 ≤ m * v ^ 2 := mul_nonneg hm (sq_nonneg v)
    have h2 : 0 ≤ μ * ‖B x‖ := mul_nonneg hμ hn.le
    rw [abs_of_nonneg (add_nonneg h1 h2), hamiltonian]
    linarith
  have unit : ‖bhat B x‖ = 1 := by
    rw [bhat, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have geom : |⟪gradient L x, cross (bhat B x) (gradAbsB B x)⟫| ≤
      ‖gradient L x‖ * ‖gradAbsB B x‖ := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    simpa only [unit, one_mul] using norm_cross_le (bhat B x) (gradAbsB B x)
  have hH : 0 ≤ 2 * hamiltonian m μ B x v := (abs_nonneg _).trans num
  gcongr

/-- **Direct first-order drift bound.** If the label rate is at most `ρ` at every state visited
before time `T`, the label moves by at most `ρ t`. -/
theorem label_displacement_le {b : GCBirth} {z : ℝ → Space × ℝ} {T ρ : ℝ}
    (orbit : GCBirthOrbitOn B m q b z T)
    (diff : ∀ s ∈ Icc 0 T, DifferentiableAt ℝ L (z s).1)
    (along : ∀ s ∈ Icc 0 T, ⟪gradient L (z s).1, B (z s).1⟫ = 0)
    (bound : ∀ s ∈ Icc 0 T, |rate B L m q b.2.2 (z s)| ≤ ρ) :
    ∀ t ∈ Icc 0 T, |L (z t).1 - L b.1| ≤ ρ * t := by
  intro t ht
  have sub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have key := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => L (z s).1) (f' := fun s => rate B L m q b.2.2 (z s))
    (fun s hs => (label_hasDerivAt (orbit.2 s (sub hs)) (diff s (sub hs))
      (along s (sub hs))).hasDerivWithinAt)
    (fun s hs => by simpa only [Real.norm_eq_abs] using bound s (sub hs))
    (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
  simpa only [orbit.1, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] using key

/-- A uniform field has no cross-field drift: every label rate vanishes. -/
theorem rate_const (F : Space) (w : Space × ℝ) :
    rate (fun _ => F) L m q μ w = 0 := by
  have hg : gradAbsB (fun _ => F) w.1 = 0 := by simp [gradAbsB]
  have hc : curlb (fun _ => F) w.1 = 0 := curlb_const F w.1
  simp [rate, hg, hc, cross]

end PlasmaLean.Kinetic.LabelDrift
