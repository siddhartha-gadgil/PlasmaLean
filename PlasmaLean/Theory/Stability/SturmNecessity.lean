/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.BallooningInfinite

/-!
# Sturm/Jacobi necessity for variable coefficients: conjugate points

For the ballooning (Sturm–Liouville) form `E(ξ) = ∫ (P ξ'² + Q ξ²)` with weight `W`, the
Barta certificate (`Ballooning.BartaCertificate.lower_bound`) and its piecewise version
(`BallooningInfinite.FluxBound.glue`) are *sufficient* for `E ≥ c ∫ W ξ²`. This module
proves the classical *necessity* direction in its conjugate-point form (Jacobi 1837;
Gelfand–Fomin, *Calculus of Variations*, §§26–29; Courant–Hilbert I, Ch. VI).

**Data** (`ConjugatePoint P Q W c a z`): a Jacobi field `u` at level `c` on `[a, z]`,
i.e. `u` is `C¹`, the flux `P u'` is differentiable with derivative
`k = (Q − c W) u` (so `−(P u')' + (Q − c W) u = 0`), and `u(a) = u(z) = 0`; the start
condition `u'(a) = 1` of the initial-value problem is recorded to rule out `u ≡ 0`.
Existence of the IVP solution is NOT formalized: the Jacobi field is supplied (for
example by a validated ODE enclosure).

**Results.**

* `ConjugatePoint.energy_shift_zero`, `ConjugatePoint.energy_eq`: integration by parts
  gives `E_{[a,z]}(u) = c ∫_a^z W u²` exactly (the truncated Jacobi field has
  `E − c M = 0`), refuting strict positivity of `E − c M`.
* `ConjugatePoint.exists_ne_zero`, `ConjugatePoint.mass_pos`: the field is nontrivial.
* `ConjugatePoint.energy_lt`: for every `c' > c`, `E(u) < c' ∫ W u²` on `[a, z]`, so
  `E ≥ c' M` fails for an admissible displacement (`λ₁([a, z]) ≤ c`).
* `ConjugatePoint.no_jacobiData`, `ConjugatePoint.no_bartaCertificate`: a conjugate
  point in `(a, b]` rules out every positive supersolution (Jacobi/Picone data) at any
  level `c' > c` on the larger interval `[a, b]` — the piecewise flux bound applies to the
  truncated field `u·1_{[a,z]}`, which is not `C¹` on `[a, b]`.
* `ConjugatePoint.truncated_energy_zero`: the zero-extended field `ξ = u` on `[a, z]`,
  `0` on `(z, b]` (continuous, piecewise `C¹`) has `∫_a^b (P ξ'² + (Q − c W) ξ²) = 0`.
* Sanity: `cosConjugate` — for constant coefficients `P = p`, `Q = q`, `W = 1` the field
  `sin(ω (x − a))/ω` has conjugate point `a + π/ω` at level `c = q + p ω²`, recovering the
  constant-coefficient threshold of `Ballooning.const_stable_iff`.

Not covered: the strict statement at the level `c` itself on a strictly larger interval
(which needs a perturbation of the broken extremal) and the Sturm oscillation count.
-/
public section

noncomputable section
namespace PlasmaLean.Stability.SturmNecessity
open intervalIntegral Set PlasmaLean.Stability PlasmaLean.Stability.BallooningInfinite
open scoped Interval

/-- A **Jacobi field with a conjugate point**: on `[a, z]` (`a < z`), `u` is `C¹` with
`u(a) = u(z) = 0`, `u'(a) = 1`, and the flux `P u'` has derivative `(Q − c W) u`. -/
structure ConjugatePoint (P Q W : ℝ → ℝ) (c a z : ℝ) where
  /-- The Jacobi field. -/
  u : ℝ → ℝ
  /-- Its derivative. -/
  u' : ℝ → ℝ
  hlt : a < z
  hu : ∀ x ∈ Icc a z, HasDerivAt u (u' x) x
  hu'c : ContinuousOn u' (Icc a z)
  jacobi : ∀ x ∈ Icc a z, HasDerivAt (fun y => P y * u' y) ((Q x - c * W x) * u x) x
  left : u a = 0
  right : u z = 0
  start : u' a = 1

namespace ConjugatePoint
variable {P Q W : ℝ → ℝ} {c a z : ℝ} (J : ConjugatePoint P Q W c a z)

include J in
/-- The conjugate point lies to the right of the start point. -/
theorem hle : a ≤ z := J.hlt.le

include J in
/-- The interval `[a, z]` as a `uIcc`. -/
theorem uIcc_eq : uIcc a z = Icc a z := uIcc_of_le J.hle

/-- The Jacobi field is `C¹` on `[a, z]`. -/
theorem c1On : C1On J.u J.u' a z :=
  ⟨fun x hx => J.hu x (J.uIcc_eq ▸ hx), J.uIcc_eq ▸ J.hu'c⟩

/-- **Energy identity.** `∫_a^z (P u'² + (Q − c W) u²) = [P u' u]_a^z = 0`. -/
theorem energy_shift_zero (hQ : Continuous Q) (hW : Continuous W) :
    newcombForm P (fun x => Q x - c * W x) a z J.u J.u' = 0 := by
  have hI := J.uIcc_eq
  have hd : ∀ x ∈ uIcc a z, HasDerivAt (fun y => (P y * J.u' y) * J.u y)
      (P x * J.u' x ^ 2 + (Q x - c * W x) * J.u x ^ 2) x := by
    intro x hx
    rw [hI] at hx
    have := (J.jacobi x hx).mul (J.hu x hx)
    convert this using 1; ring
  have hPu'c : ContinuousOn (fun y => P y * J.u' y) (uIcc a z) :=
    fun x hx => (J.jacobi x (hI ▸ hx)).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun x => P x * J.u' x ^ 2 + (Q x - c * W x) * J.u x ^ 2)
      MeasureTheory.volume a z := by
    have e : (fun x => P x * J.u' x ^ 2 + (Q x - c * W x) * J.u x ^ 2) =
        fun x => (P x * J.u' x) * J.u' x + (Q x - c * W x) * J.u x ^ 2 := by
      funext x; ring
    rw [e]
    exact ((hPu'c.mul J.c1On.cont).add
      ((by fun_prop : Continuous fun x => Q x - c * W x).continuousOn.mul
        (J.c1On.continuousOn.pow 2))).intervalIntegrable
  unfold newcombForm
  rw [integral_eq_sub_of_hasDerivAt hd hint, J.left, J.right]
  ring

/-- **The Jacobi field has energy `c` times its mass**: `E_{[a,z]}(u) = c ∫_a^z W u²`. -/
theorem energy_eq (hP : Continuous P) (hQ : Continuous Q) (hW : Continuous W) :
    newcombForm P Q a z J.u J.u' = c * ∫ x in a..z, W x * J.u x ^ 2 := by
  rw [newcombForm_shift c J.c1On hP hQ hW, J.energy_shift_zero hQ hW, zero_add]

/-- The Jacobi field is not identically zero: `u'(a) = 1` forces `u(x) ≠ 0` for some
`x ∈ (a, z)`. -/
theorem exists_ne_zero : ∃ x ∈ Ioo a z, J.u x ≠ 0 := by
  have h1 := (J.hu a ⟨le_rfl, J.hle⟩).eventually_ne (c := 0) (by rw [J.start]; exact one_ne_zero)
  have h2 : ∀ᶠ x in nhdsWithin a (Ioi a), J.u x ≠ 0 :=
    h1.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  obtain ⟨x, hx1, hx2⟩ := (h2.and (Ioo_mem_nhdsGT J.hlt)).exists
  exact ⟨x, hx2, hx1⟩

/-- With a positive continuous weight the Jacobi field has positive mass. -/
theorem mass_pos (hW : Continuous W) (hWpos : ∀ x ∈ Icc a z, 0 < W x) :
    0 < ∫ x in a..z, W x * J.u x ^ 2 := by
  obtain ⟨x₀, hx₀, hne⟩ := J.exists_ne_zero
  refine integral_pos J.hlt (hW.continuousOn.mul ((J.uIcc_eq ▸ J.c1On.continuousOn).pow 2))
    (fun x hx => mul_nonneg (hWpos x (Ioc_subset_Icc_self hx)).le (sq_nonneg _))
    ⟨x₀, Ioo_subset_Icc_self hx₀, mul_pos (hWpos x₀ (Ioo_subset_Icc_self hx₀)) (by positivity)⟩

/-- **Necessity (variable coefficients).** A conjugate point at level `c` makes
`E ≥ c' ∫ W ξ²` fail on `[a, z]` for every `c' > c`: the Jacobi field itself (admissible:
`C¹`, vanishing at both ends) has `E(u) < c' ∫ W u²`. -/
theorem energy_lt (hP : Continuous P) (hQ : Continuous Q) (hW : Continuous W)
    (hWpos : ∀ x ∈ Icc a z, 0 < W x) {c' : ℝ} (hc : c < c') :
    newcombForm P Q a z J.u J.u' < c' * ∫ x in a..z, W x * J.u x ^ 2 := by
  rw [J.energy_eq hP hQ hW]
  exact mul_lt_mul_of_pos_right hc (J.mass_pos hW hWpos)

include J in
/-- **No positive supersolution beyond a conjugate point.** If `[a, z] ⊆ [a, b]` carries a
conjugate point at level `c`, then no positive Jacobi supersolution
`-(P w')' + (Q − c' W) w ≥ 0` exists on `[a, b]` for any `c' > c` (with `P, Q, W` continuous,
`P ≥ 0` everywhere and `W > 0` on `[a, z]`). -/
theorem no_jacobiData (hP : Continuous P) (hQ : Continuous Q) (hW : Continuous W)
    (hPpos : ∀ x, 0 ≤ P x) (hWpos : ∀ x ∈ Icc a z, 0 < W x) {b c' : ℝ} (hzb : z ≤ b)
    (hc : c < c') : IsEmpty (JacobiData P (fun x => Q x - c' * W x) (Icc a b)) := by
  refine ⟨fun D => ?_⟩
  have hsub : Icc a z ⊆ Icc a b := Icc_subset_Icc le_rfl hzb
  have F := (D.toPicone hP.continuousOn fun x _ => hPpos x).fluxBound J.hle hsub
    (fun x _ => hPpos x) hP.continuousOn
    (by fun_prop : Continuous fun x => Q x - c' * W x).continuousOn
  have h0 := F.nonneg J.c1On J.left J.right
  have hs := newcombForm_shift c' J.c1On hP hQ hW
  have hlt := J.energy_lt hP hQ hW hWpos hc
  linarith

/-- The same obstruction for the Barta certificates of `Ballooning` on a symmetric segment
`[-L, L]`: a conjugate point `[−L, z]` (`z ≤ L`) at level `c` rules out every Barta
certificate at a level `c' > c`. -/
theorem no_bartaCertificate (op : Ballooning.BallooningOperator)
    (J : ConjugatePoint op.P op.Q op.W c (-op.L) z) (hP : Continuous op.P)
    (hQ : Continuous op.Q) (hW : Continuous op.W) (hz : z ≤ op.L) {c' : ℝ} (hc : c < c') :
    IsEmpty (op.BartaCertificate c') := by
  have hzL : Icc (-op.L) z ⊆ Icc (-op.L) op.L := Icc_subset_Icc le_rfl hz
  refine ⟨fun cert => ?_⟩
  have hD : JacobiData op.P (fun x => op.Q x - c' * op.W x) (Icc (-op.L) z) :=
    { u := cert.w, u' := cert.w', k := cert.k
      hu := fun x hx => cert.hw x (hzL hx)
      hu'c := cert.hw'c.mono hzL
      hk := fun x hx => cert.hk x (hzL hx)
      hkc := cert.hkc.mono hzL
      pos := fun x hx => cert.pos x (hzL hx)
      super := fun x hx => by have := cert.super x (hzL hx); nlinarith }
  have F := (hD.toPicone (hP.continuousOn) fun x hx => (op.P_pos x (hzL hx)).le).fluxBound
    J.hle subset_rfl (fun x hx => (op.P_pos x (hzL hx)).le) hP.continuousOn
    (by fun_prop : Continuous fun x => op.Q x - c' * op.W x).continuousOn
  have h0 := F.nonneg J.c1On J.left J.right
  have hs := newcombForm_shift c' J.c1On hP hQ hW
  have hlt := J.energy_lt hP hQ hW (fun x hx => op.W_pos x (hzL hx)) hc
  linarith

/-- The truncated Jacobi field: `u` on `(-∞, z]`, `0` after. -/
@[expose] def truncated (x : ℝ) : ℝ := if x ≤ z then J.u x else 0

/-- Its (almost-everywhere) derivative. -/
@[expose] def truncated' (x : ℝ) : ℝ := if x ≤ z then J.u' x else 0

/-- **The truncated Jacobi field has `E − c M = 0` on every `[a, b] ⊇ [a, z]`.** The
zero extension is continuous and piecewise `C¹`; its shifted energy on `[a, b]` vanishes,
so the form `E − c M` is not strictly positive on the piecewise-`C¹` class. -/
theorem truncated_energy_zero (hP : Continuous P) (hQ : Continuous Q) (hW : Continuous W)
    {b : ℝ} (hzb : z ≤ b) :
    newcombForm P (fun x => Q x - c * W x) a b J.truncated J.truncated' = 0 := by
  have hI := J.uIcc_eq
  have e1 : ∀ x ∈ uIcc a z,
      P x * J.truncated' x ^ 2 + (Q x - c * W x) * J.truncated x ^ 2 =
        P x * J.u' x ^ 2 + (Q x - c * W x) * J.u x ^ 2 := by
    intro x hx
    rw [hI] at hx
    simp [truncated, truncated', hx.2]
  have e2 : EqOn (fun _ => (0 : ℝ))
      (fun x => P x * J.truncated' x ^ 2 + (Q x - c * W x) * J.truncated x ^ 2) (Ι z b) := by
    intro x hx
    rw [uIoc_of_le hzb] at hx
    simp [truncated, truncated', not_le.mpr hx.1]
  have hint1 : IntervalIntegrable
      (fun x => P x * J.truncated' x ^ 2 + (Q x - c * W x) * J.truncated x ^ 2)
      MeasureTheory.volume a z := by
    have h := newcomb_integrable (f := P) (g := fun x => Q x - c * W x) J.c1On hP.continuousOn
      (by fun_prop : Continuous fun x => Q x - c * W x).continuousOn
    exact h.congr (fun x hx => (e1 x (uIoc_subset_uIcc hx)).symm)
  have hint2 : IntervalIntegrable
      (fun x => P x * J.truncated' x ^ 2 + (Q x - c * W x) * J.truncated x ^ 2)
      MeasureTheory.volume z b :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr e2
  unfold newcombForm
  rw [← integral_add_adjacent_intervals hint1 hint2, integral_congr e1,
    ← intervalIntegral.integral_congr_ae (f := fun _ => (0 : ℝ))
      (Filter.Eventually.of_forall fun x hx => e2 hx)]
  have := J.energy_shift_zero hQ hW
  unfold newcombForm at this
  rw [this]
  simp

end ConjugatePoint

/-! ## Sanity: constant coefficients -/

/-- **Constant-coefficient conjugate point.** For `P = p > 0`, `Q = q`, `W = 1` and any
`ω > 0`, the field `u(x) = sin(ω (x − a))/ω` is a Jacobi field at level `c = q + p ω²`
with conjugate point `a + π/ω`. -/
@[expose] def cosConjugate (p q a ω : ℝ) (hω : 0 < ω) :
    ConjugatePoint (fun _ => p) (fun _ => q) (fun _ => 1) (q + p * ω ^ 2) a (a + Real.pi / ω) where
  u x := Real.sin (ω * (x - a)) / ω
  u' x := Real.cos (ω * (x - a))
  hlt := by have := div_pos Real.pi_pos hω; linarith
  hu x _ := by
    have := ((((hasDerivAt_id' x).sub_const a).const_mul ω).sin).div_const ω
    convert this using 1
    field_simp
  hu'c := by fun_prop
  jacobi x _ := by
    have := ((((hasDerivAt_id' x).sub_const a).const_mul ω).cos).const_mul p
    convert this using 1
    field_simp
    ring
  left := by simp
  right := by
    have : ω * (Real.pi / ω) = Real.pi := by field_simp
    simp [this]
  start := by simp

/-- Sanity: with constant coefficients, a segment of length `π/ω` cannot carry a Barta
certificate on `[a, a + π/ω]` at any level above `q + p ω²` — the sharp
constant-coefficient Dirichlet eigenvalue `q + p (π/ℓ)²` for length `ℓ = π/ω`. -/
theorem const_no_jacobiData {p q a ω c' : ℝ} (hp : 0 < p) (hω : 0 < ω)
    (hc : q + p * ω ^ 2 < c') :
    IsEmpty (JacobiData (fun _ => p) (fun x => (fun _ => q) x - c' * (fun _ => (1 : ℝ)) x)
      (Icc a (a + Real.pi / ω))) :=
  (cosConjugate p q a ω hω).no_jacobiData continuous_const continuous_const continuous_const
    (fun _ => hp.le) (fun _ _ => one_pos) le_rfl hc

end PlasmaLean.Stability.SturmNecessity
