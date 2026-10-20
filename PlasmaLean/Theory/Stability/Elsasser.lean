/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Elsässer variables, energy, cross-helicity and the transport cancellation

Track T9 warm-up (source: `notes/holomorphic-bundles-kym-wick-rotations.md` §4 and
`notes/pde-bounds-and-verification-roadmap.md` §7).

Velocity `v` and normalized magnetic perturbation `b = B/√(μ₀ρ)` live in a real inner
product space `V` (for the PDE this would be `L²` of divergence-free fields). The Elsässer
variables are `z₊ = v + b` and `z₋ = v - b`. We prove:

* the energy identity `‖z₊‖² + ‖z₋‖² = 2(‖v‖² + ‖b‖²)`;
* the cross-helicity identity `‖z₊‖² - ‖z₋‖² = 4⟪v, b⟫`;
* the inverse formulas `v = ½(z₊ + z₋)`, `b = ½(z₊ - z₋)`;
* the bound `|⟪v, b⟫| ≤ (‖v‖² + ‖b‖²)/2`.

## Abstract transport cancellation

A transport operator `T w u` stands for `(w·∇)u`. For divergence-free `w` tangent to the
boundary, `∫ (w·∇)u · u = ½ ∫ w·∇|u|² = 0`. We take this as the hypothesis
`IsSkewTransport T : ∀ w u, ⟪T w u, u⟫ = 0`; it is **not** derived from a PDE here. The
pressure gradient is modelled by a vector `g` orthogonal to both `z₊` and `z₋` (the abstract
form of `∫ ∇P · z = 0` for divergence-free `z`). For the abstract system

`z₊' = T v_A z₊ - T z₋ z₊ - g`,  `z₋' = -T v_A z₋ - T z₊ z₋ - g`

we prove the exact derivative of `‖z₊‖² + ‖z₋‖²` without any skewness assumption
(`elsasser_energy_hasDerivAt_general`), and that under skewness the cubic terms
`⟪T z∓ z±, z±⟫` vanish so that each of `‖z₊‖²`, `‖z₋‖²` is conserved.

Scope remark: the energy cancellation uses only skewness of transport. It would equally
cancel a co-propagating term `T z± z±`. The genuine null structure (that only
counter-propagating waves interact) is reflected in the *form* of the system, and matters
for commuted/higher-order estimates, which are not treated here.
-/
public section

noncomputable section
namespace PlasmaLean.Stability.Elsasser

open scoped InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Forward Elsässer variable `z₊ = v + b`. -/
@[expose] def zPlus (v b : V) : V := v + b

/-- Backward Elsässer variable `z₋ = v - b`. -/
@[expose] def zMinus (v b : V) : V := v - b

/-- Energy identity: `‖z₊‖² + ‖z₋‖² = 2(‖v‖² + ‖b‖²)` (parallelogram law). -/
theorem energy_identity (v b : V) :
    ‖zPlus v b‖ ^ 2 + ‖zMinus v b‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖b‖ ^ 2) := by
  rw [zPlus, zMinus, norm_add_sq_real, norm_sub_sq_real]
  ring

/-- Cross-helicity identity: `‖z₊‖² - ‖z₋‖² = 4⟪v, b⟫`. -/
theorem cross_helicity_identity (v b : V) :
    ‖zPlus v b‖ ^ 2 - ‖zMinus v b‖ ^ 2 = 4 * ⟪v, b⟫ := by
  rw [zPlus, zMinus, norm_add_sq_real, norm_sub_sq_real]
  ring

/-- Inverse formula for the velocity: `v = ½ (z₊ + z₋)`. -/
theorem v_eq_half_sum (v b : V) : v = (1 / 2 : ℝ) • (zPlus v b + zMinus v b) := by
  rw [zPlus, zMinus, show v + b + (v - b) = (2 : ℝ) • v by rw [two_smul]; abel, smul_smul]
  norm_num

/-- Inverse formula for the magnetic perturbation: `b = ½ (z₊ - z₋)`. -/
theorem b_eq_half_diff (v b : V) : b = (1 / 2 : ℝ) • (zPlus v b - zMinus v b) := by
  rw [zPlus, zMinus, show v + b - (v - b) = (2 : ℝ) • b by rw [two_smul]; abel, smul_smul]
  norm_num

/-- Cross-helicity is bounded by half the energy: `|⟪v, b⟫| ≤ (‖v‖² + ‖b‖²)/2`. -/
theorem abs_inner_le_half_energy (v b : V) :
    |⟪v, b⟫| ≤ (‖v‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  have h := abs_real_inner_le_norm v b
  nlinarith [sq_nonneg (‖v‖ - ‖b‖)]

omit [InnerProductSpace ℝ V] in
/-- Sanity (b = 0): with no magnetic perturbation both Elsässer variables equal `v`. -/
theorem zPlus_zMinus_of_b_zero (v : V) : zPlus v 0 = v ∧ zMinus v 0 = v := by
  simp [zPlus, zMinus]

omit [InnerProductSpace ℝ V] in
/-- Sanity (b = 0): the energy identity reduces to `2‖v‖² = 2‖v‖²` and cross-helicity
vanishes. -/
theorem cross_helicity_b_zero (v : V) :
    ‖zPlus v 0‖ ^ 2 - ‖zMinus v 0‖ ^ 2 = 0 := by
  simp [zPlus, zMinus]

/-- Sanity (pure forward Alfvén wave `v = b`): `z₋ = 0`, and the whole energy is carried by
`z₊ = 2v`. -/
theorem pure_forward_wave (v : V) :
    zMinus v v = 0 ∧ zPlus v v = (2 : ℝ) • v := by
  simp [zMinus, zPlus, two_smul]

omit [InnerProductSpace ℝ V] in
/-- Sanity (pure backward Alfvén wave `v = -b`): `z₊ = 0`. -/
theorem pure_backward_wave (b : V) : zPlus (-b) b = 0 := by
  simp [zPlus]

/-- Sanity: the cross-helicity bound is sharp, attained by a pure forward wave. -/
theorem abs_inner_eq_half_energy_forward (v : V) :
    |⟪v, v⟫| = (‖v‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)]
  ring

/-! ### Abstract transport skewness and the energy law -/

/-- Abstract skewness of a transport operator `T w u ≈ (w·∇)u`: `⟪T w u, u⟫ = 0` for all
`w, u`. This is the hypothesis replacing `∫ (w·∇)u·u = 0` for divergence-free `w` tangent
to the boundary. -/
@[expose] def IsSkewTransport (T : V → V → V) : Prop :=
  ∀ w u, ⟪T w u, u⟫ = 0

/-- If `T w` is linear, skewness polarizes to antisymmetry:
`⟪T w u, u'⟫ = -⟪T w u', u⟫`. -/
theorem IsSkewTransport.antisymm {T : V → V →ₗ[ℝ] V} (hT : IsSkewTransport (fun w u => T w u))
    (w u u' : V) : ⟪T w u, u'⟫ = -⟪T w u', u⟫ := by
  have h := hT w (u + u')
  have h1 := hT w u
  have h2 := hT w u'
  have h2' : ⟪u', T w u'⟫ = 0 := by rw [real_inner_comm]; exact h2
  simp only [map_add, inner_add_left, inner_add_right] at h h1
  linarith

/-- Under skewness, the self-interaction cubic terms `⟪T z∓ z±, z±⟫` vanish. -/
theorem cubic_terms_vanish {T : V → V → V} (hT : IsSkewTransport T) (zp zm : V) :
    ⟪T zm zp, zp⟫ = 0 ∧ ⟪T zp zm, zm⟫ = 0 :=
  ⟨hT zm zp, hT zp zm⟩

/-- Exact energy derivative for the abstract Elsässer system, with no skewness assumption.
Here `z₊' = T v_A z₊ - T z₋ z₊ - g`, `z₋' = -T v_A z₋ - T z₊ z₋ - g`, and the pressure term
`g` is orthogonal to `z₊(t)` and `z₋(t)`. The derivative of `‖z₊‖² + ‖z₋‖²` is a linear
(background) part plus the cubic part `-2(⟪T z₋ z₊, z₊⟫ + ⟪T z₊ z₋, z₋⟫)`. -/
theorem elsasser_energy_hasDerivAt_general (T : V → V → V) (vA g : V) (zp zm : ℝ → V) (t : ℝ)
    (hp : HasDerivAt zp (T vA (zp t) - T (zm t) (zp t) - g) t)
    (hm : HasDerivAt zm (-T vA (zm t) - T (zp t) (zm t) - g) t)
    (hgp : ⟪g, zp t⟫ = 0) (hgm : ⟪g, zm t⟫ = 0) :
    HasDerivAt (fun s => ‖zp s‖ ^ 2 + ‖zm s‖ ^ 2)
      (2 * (⟪T vA (zp t), zp t⟫ - ⟪T vA (zm t), zm t⟫)
        - 2 * (⟪T (zm t) (zp t), zp t⟫ + ⟪T (zp t) (zm t), zm t⟫)) t := by
  have hgp' : ⟪zp t, g⟫ = 0 := by rw [real_inner_comm]; exact hgp
  have hgm' : ⟪zm t, g⟫ = 0 := by rw [real_inner_comm]; exact hgm
  refine HasDerivAt.congr_deriv (HasDerivAt.add hp.norm_sq hm.norm_sq) ?_
  simp only [inner_sub_right, inner_neg_right, hgp', hgm']
  rw [real_inner_comm (zp t) (T vA (zp t)), real_inner_comm (zp t) (T (zm t) (zp t)),
    real_inner_comm (zm t) (T vA (zm t)), real_inner_comm (zm t) (T (zp t) (zm t))]
  ring

/-- Under transport skewness the total Elsässer energy `‖z₊‖² + ‖z₋‖²` has zero derivative:
both the background-propagation term and the cubic term vanish. -/
theorem elsasser_energy_hasDerivAt_zero {T : V → V → V} (hT : IsSkewTransport T) (vA g : V)
    (zp zm : ℝ → V) (t : ℝ)
    (hp : HasDerivAt zp (T vA (zp t) - T (zm t) (zp t) - g) t)
    (hm : HasDerivAt zm (-T vA (zm t) - T (zp t) (zm t) - g) t)
    (hgp : ⟪g, zp t⟫ = 0) (hgm : ⟪g, zm t⟫ = 0) :
    HasDerivAt (fun s => ‖zp s‖ ^ 2 + ‖zm s‖ ^ 2) 0 t := by
  refine (elsasser_energy_hasDerivAt_general T vA g zp zm t hp hm hgp hgm).congr_deriv ?_
  rw [hT, hT, hT, hT]
  ring

/-- Under transport skewness `‖z₊‖²` alone is conserved (see `zMinus_energy_hasDerivAt_zero`
and `cross_helicity_hasDerivAt_zero` for `‖z₋‖²` and the cross-helicity). -/
theorem zPlus_energy_hasDerivAt_zero {T : V → V → V} (hT : IsSkewTransport T) (vA g : V)
    (zp zm : ℝ → V) (t : ℝ)
    (hp : HasDerivAt zp (T vA (zp t) - T (zm t) (zp t) - g) t) (hgp : ⟪g, zp t⟫ = 0) :
    HasDerivAt (fun s => ‖zp s‖ ^ 2) 0 t := by
  have hgp' : ⟪zp t, g⟫ = 0 := by rw [real_inner_comm]; exact hgp
  refine hp.norm_sq.congr_deriv ?_
  simp only [inner_sub_right, hgp']
  rw [real_inner_comm (T vA (zp t)) (zp t), real_inner_comm (T (zm t) (zp t)) (zp t), hT, hT]
  ring

/-- Under transport skewness `‖z₋‖²` alone is conserved. -/
theorem zMinus_energy_hasDerivAt_zero {T : V → V → V} (hT : IsSkewTransport T) (vA g : V)
    (zp zm : ℝ → V) (t : ℝ)
    (hm : HasDerivAt zm (-T vA (zm t) - T (zp t) (zm t) - g) t) (hgm : ⟪g, zm t⟫ = 0) :
    HasDerivAt (fun s => ‖zm s‖ ^ 2) 0 t := by
  have hgm' : ⟪zm t, g⟫ = 0 := by rw [real_inner_comm]; exact hgm
  refine hm.norm_sq.congr_deriv ?_
  simp only [inner_sub_right, inner_neg_right, hgm']
  rw [real_inner_comm (T vA (zm t)) (zm t), real_inner_comm (T (zp t) (zm t)) (zm t), hT, hT]
  ring

/-- Under transport skewness the cross-helicity `‖z₊‖² - ‖z₋‖²` (`= 4⟪v, b⟫`) has zero
derivative. -/
theorem cross_helicity_hasDerivAt_zero {T : V → V → V} (hT : IsSkewTransport T) (vA g : V)
    (zp zm : ℝ → V) (t : ℝ)
    (hp : HasDerivAt zp (T vA (zp t) - T (zm t) (zp t) - g) t)
    (hm : HasDerivAt zm (-T vA (zm t) - T (zp t) (zm t) - g) t)
    (hgp : ⟪g, zp t⟫ = 0) (hgm : ⟪g, zm t⟫ = 0) :
    HasDerivAt (fun s => ‖zp s‖ ^ 2 - ‖zm s‖ ^ 2) 0 t := by
  refine HasDerivAt.congr_deriv (HasDerivAt.sub
    (zPlus_energy_hasDerivAt_zero hT vA g zp zm t hp hgp)
    (zMinus_energy_hasDerivAt_zero hT vA g zp zm t hm hgm)) ?_
  ring

/-- Accepted fixture (non-vacuity): `T w u = ⟪w, u⟫ x - ⟪x, u⟫ w` is skew in any real inner
product space, for any fixed `x` (an abstract analogue of rotation by `w ∧ x`). -/
theorem wedge_transport_isSkew (x : V) :
    IsSkewTransport (fun w u : V => ⟪w, u⟫ • x - ⟪x, u⟫ • w) := by
  intro w u
  simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real]
  ring

/-- Rejected fixture: the identity transport `T w u = u` is not skew on a nontrivial space;
its "cubic" term `⟪T w u, u⟫ = ‖u‖²` does not vanish. -/
theorem identity_transport_not_skew [Nontrivial V] :
    ¬ IsSkewTransport (fun _ u : V => u) := by
  intro h
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have := h 0 u
  simp only [real_inner_self_eq_norm_sq] at this
  exact hu (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this))

end PlasmaLean.Stability.Elsasser
