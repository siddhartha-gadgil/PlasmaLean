/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Kinetic.VacuumLittlejohnLocal
public import PlasmaLean.Theory.Fields.BiotSavart
public import PlasmaLean.Theory.Fields.LipschitzLabel

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

For labels that are only Lipschitz (for instance the point where the field line meets a section,
with a Lipschitz constant from a Grönwall estimate):

* `velocity_vacuum`: the guiding-centre velocity is `(v_∥/|B|) B` plus the drift
  `(m v_∥² + μ|B|)/(q|B|²) b × ∇|B|`; `norm_drift_le` bounds the drift by the energy.
* `lipschitz_displacement_le`: for a `K`-Lipschitz label that is constant on field lines,
  `|L(X(t)) − L(X(0))| ≤ c t` when `K` times the drift bound is at most `c` along the orbit.
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

/-- In a nonvanishing curl-free field, `∇×b = |B|⁻¹ b × ∇|B|`. -/
theorem curlb_vacuum {x : Space} (nzero : B x ≠ 0) (diff : DifferentiableAt ℝ B x)
    (nocurl : curl (fderiv ℝ B x) = 0) :
    curlb B x = ‖B x‖⁻¹ • cross (bhat B x) (gradAbsB B x) := by
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
  rw [curl_unit, grad_inv, left, swap, bhat, left, smul_neg, neg_smul, neg_neg, smul_smul]
  congr 1
  field_simp

/-- The cross-field drift velocity of a guiding centre in a curl-free field. -/
def drift (B : Space → Space) (m q μ : ℝ) (w : Space × ℝ) : Space :=
  ((m * w.2 ^ 2 + μ * ‖B w.1‖) / (q * ‖B w.1‖ ^ 2)) • cross (bhat B w.1) (gradAbsB B w.1)

/-- In a nonvanishing curl-free field the guiding-centre velocity is parallel streaming plus
the drift. -/
theorem velocity_vacuum {x : Space} (nzero : B x ≠ 0) (diff : DifferentiableAt ℝ B x)
    (nocurl : curl (fderiv ℝ B x) = 0) (hq : q ≠ 0) (v : ℝ) :
    (littlejohnVelocity B m q μ (x, v)).1 = (v / ‖B x‖) • B x + drift B m q μ (x, v) := by
  have hn := norm_ne_zero_iff.mpr nzero
  simp only [littlejohnVelocity, drift, Bstar]
  rw [VacuumLittlejohnLocal.parallel_eq_norm nzero diff nocurl, curlb_vacuum nzero diff nocurl]
  simp only [smul_add, smul_smul, add_assoc]
  congr 1
  · congr 1
    field_simp
  · rw [← add_smul]
    congr 1
    field_simp

/-- The drift speed is at most `2H/(|q||B|²) ‖∇|B|‖`. -/
theorem norm_drift_le {x : Space} (nzero : B x ≠ 0) (hm : 0 ≤ m) (hμ : 0 ≤ μ) (v : ℝ) :
    ‖drift B m q μ (x, v)‖ ≤
      2 * hamiltonian m μ B x v / (|q| * ‖B x‖ ^ 2) * ‖gradAbsB B x‖ := by
  have hn : 0 < ‖B x‖ := norm_pos_iff.mpr nzero
  have den : |q * ‖B x‖ ^ 2| = |q| * ‖B x‖ ^ 2 := by rw [abs_mul, abs_of_pos (pow_pos hn 2)]
  have num : |m * v ^ 2 + μ * ‖B x‖| ≤ 2 * hamiltonian m μ B x v := by
    have h1 : 0 ≤ m * v ^ 2 := mul_nonneg hm (sq_nonneg v)
    have h2 : 0 ≤ μ * ‖B x‖ := mul_nonneg hμ hn.le
    rw [abs_of_nonneg (add_nonneg h1 h2), hamiltonian]
    linarith
  have unit : ‖bhat B x‖ = 1 := by
    rw [bhat, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have geom : ‖cross (bhat B x) (gradAbsB B x)‖ ≤ ‖gradAbsB B x‖ := by
    simpa only [unit, one_mul] using norm_cross_le (bhat B x) (gradAbsB B x)
  have hH : 0 ≤ 2 * hamiltonian m μ B x v := (abs_nonneg _).trans num
  rw [drift, norm_smul, Real.norm_eq_abs, abs_div, den]
  gcongr

/-- **Drift of a Lipschitz label.** In an open region where `B` is `C¹`, nonvanishing and
curl-free, let `L` be constant on field lines and locally `K`-Lipschitz. If `K` times the drift
bound is at most `c` at the states visited, the label moves by at most `c t`. -/
theorem lipschitz_displacement_le {U : Set Space} {K : NNReal} {b : GCBirth}
    {z : ℝ → Space × ℝ} {T c : ℝ} (hU : IsOpen U) (smooth : ∀ x ∈ U, ContDiffAt ℝ 1 B x)
    (nzero : ∀ x ∈ U, B x ≠ 0) (nocurl : ∀ x ∈ U, curl (fderiv ℝ B x) = 0)
    (lip : ∀ x ∈ U, ∃ W ∈ nhds x, LipschitzOnWith K L W)
    (inv : Fields.LipschitzLabel.InvariantOn B L U)
    (hm : 0 ≤ m) (hq : q ≠ 0) (hμ : 0 ≤ b.2.2) (orbit : GCBirthOrbitOn B m q b z T)
    (inU : ∀ s ∈ Icc 0 T, (z s).1 ∈ U)
    (bound : ∀ s ∈ Icc 0 T, K * (2 * hamiltonian m b.2.2 B (z s).1 (z s).2 /
      (|q| * ‖B (z s).1‖ ^ 2) * ‖gradAbsB B (z s).1‖) ≤ c) :
    ∀ t ∈ Icc 0 T, |L (z t).1 - L b.1| ≤ c * t := by
  have start : (z 0).1 = b.1 := by rw [orbit.1]
  have key := Fields.LipschitzLabel.displacement_le hU smooth lip inv
    (X := fun s => (z s).1) (lam := fun s => (z s).2 / ‖B (z s).1‖)
    (w := fun s => drift B m q b.2.2 (z s)) inU
    (fun s hs => by
      have pos : HasDerivAt (fun t => (z t).1) (littlejohnVelocity B m q b.2.2 (z s)).1 s :=
        (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt.comp_hasDerivAt s (orbit.2 s hs)
      have hx := inU s hs
      rwa [show z s = ((z s).1, (z s).2) from rfl, velocity_vacuum (nzero _ hx)
        ((smooth _ hx).differentiableAt (by norm_num)) (nocurl _ hx) hq] at pos)
    (fun s hs => (mul_le_mul_of_nonneg_left
      (norm_drift_le (nzero _ (inU s hs)) hm hμ (z s).2) K.coe_nonneg).trans (bound s hs))
  simpa only [start] using key

end PlasmaLean.Kinetic.LabelDrift
