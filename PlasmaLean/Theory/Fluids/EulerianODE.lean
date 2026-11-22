/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.WeakQuasisymmetry
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Eulerian quadratic ODEs: energy and helicity are conserved

Source: D. Sullivan, *3D incompressible fluids: combinatorial models, eigenspace models, and a
conjecture about well-posedness of the 3D zero viscosity limit*, J. Differential Geom. 97 (2014)
141–148, Part 2 (note N-46).

Sullivan calls a quadratic ODE `ẋ = Q(x)` on a real inner product space *Eulerian* if there are
a self-adjoint operator `D` and a totally skew-symmetric trilinear form `{ , , }` with
`⟪Q x, z⟫ = {x, D x, z}`. For the 3D Euler equation, `x` is the velocity (as a 1-form),
`D = curl` and `{a, b, c} = ∫ a ∧ b ∧ c`, so that `Q x` is the projection of `x × curl x`.

`EulerianODE D T Q` records what is used: `D` is symmetric, `T a b c` vanishes when the third
argument repeats the first or the second, and `⟪Q x, z⟫ = T x (D x) z`. Linearity of `T` is not
needed.

* `EulerianODE.energy_conserved`: `‖x‖²` is constant along solutions (Sullivan's
  Proposition 7.3 (1)).
* `EulerianODE.helicity_conserved`: `⟪x, D x⟫` is constant along solutions. Sullivan does not
  state this; it follows in one line from the same skew-symmetry, and for the Euler equation
  it is the conservation of helicity `∫ u · curl u`.

Sanity instance: on `ℝ³` with `T a b c = ⟪a × b, c⟫` the Eulerian ODE is `ẋ = x × D x`, the
equation of the free rigid body (`rigidBody_eulerian`); the two invariants are the squared
angular momentum and twice the kinetic energy. Degenerate case: `D = 0` gives `Q = 0`
(`eulerianODE_zero`). Counterexample: the linear ODE `ẋ = x` does not conserve the norm, so
it is not Eulerian for any `D` and `T` (`not_eulerianODE_id`).

Not covered: the invariant Gaussian measure (Proposition 7.3 (2)), convergence of the
truncations to the Euler equation (Theorem 7.5), and the conjecture.
-/

open scoped RealInnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Fluids

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Eulerian quadratic ODE data** (Sullivan): `⟪Q x, z⟫ = T x (D x) z` with `D` symmetric
and `T` vanishing when its third argument repeats the first or the second (two consequences
of total skew-symmetry). -/
structure EulerianODE (D : E →L[ℝ] E) (T : E → E → E → ℝ) (Q : E → E) : Prop where
  /-- `D` is symmetric. -/
  symm : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫
  /-- `{a, b, a} = 0`. -/
  skew_left : ∀ a b, T a b a = 0
  /-- `{a, b, b} = 0`. -/
  skew_right : ∀ a b, T a b b = 0
  /-- `⟪Q x, z⟫ = {x, D x, z}`. -/
  spec : ∀ x z, ⟪Q x, z⟫ = T x (D x) z

/-- **Energy** (Sullivan, Proposition 7.3 (1)): `‖x‖²` is constant along solutions of an
Eulerian ODE. -/
theorem EulerianODE.energy_conserved {D : E →L[ℝ] E} {T : E → E → E → ℝ} {Q : E → E}
    (h : EulerianODE D T Q) {x : ℝ → E} (hx : ∀ t, HasDerivAt x (Q (x t)) t) (s t : ℝ) :
    ‖x s‖ ^ 2 = ‖x t‖ ^ 2 := by
  have hd : ∀ r, HasDerivAt (fun u => ⟪x u, x u⟫) 0 r := fun r => by
    have e : ⟪x r, Q (x r)⟫ = 0 := by rw [real_inner_comm, h.spec, h.skew_left]
    have e' : ⟪Q (x r), x r⟫ = 0 := by rw [h.spec, h.skew_left]
    have := (hx r).inner ℝ (hx r)
    rw [e, e', add_zero] at this
    exact this
  have hc := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s t
  simpa [real_inner_self_eq_norm_sq] using hc

/-- **Helicity**: `⟪x, D x⟫` is constant along solutions of an Eulerian ODE. For the Euler
equation (`D = curl`) this is the helicity `∫ u · curl u`. -/
theorem EulerianODE.helicity_conserved {D : E →L[ℝ] E} {T : E → E → E → ℝ} {Q : E → E}
    (h : EulerianODE D T Q) {x : ℝ → E} (hx : ∀ t, HasDerivAt x (Q (x t)) t) (s t : ℝ) :
    ⟪x s, D (x s)⟫ = ⟪x t, D (x t)⟫ := by
  have hd : ∀ r, HasDerivAt (fun u => ⟪x u, D (x u)⟫) 0 r := fun r => by
    have h2 : HasDerivAt (fun u => D (x u)) (D (Q (x r))) r :=
      D.hasFDerivAt.comp_hasDerivAt r (hx r)
    have e : ⟪x r, D (Q (x r))⟫ = 0 := by
      rw [← h.symm, real_inner_comm, h.spec, h.skew_right]
    have e' : ⟪Q (x r), D (x r)⟫ = 0 := by rw [h.spec, h.skew_right]
    have := (hx r).inner ℝ h2
    rw [e, e', add_zero] at this
    exact this
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) s t

/-! ### Sanity -/

open PlasmaLean.Fields in
/-- **Concrete instance: the free rigid body.** On `ℝ³` with the triple product as 3-form,
the Eulerian ODE of a symmetric `D` is `ẋ = x × D x`. -/
theorem rigidBody_eulerian (D : Space →L[ℝ] Space) (hD : ∀ x y, ⟪D x, y⟫ = ⟪x, D y⟫) :
    EulerianODE D (fun a b c => ⟪cross a b, c⟫) (fun x => cross x (D x)) where
  symm := hD
  skew_left a b := by rw [real_inner_comm]; exact inner_cross_left_self a b
  skew_right a b := by rw [real_inner_comm]; exact inner_cross_right_self a b
  spec _ _ := rfl

/-- Degenerate case: with `D = 0` and the zero form, the Eulerian ODE is `ẋ = 0`. -/
theorem eulerianODE_zero : EulerianODE (0 : E →L[ℝ] E) (fun _ _ _ => 0) (fun _ => 0) where
  symm _ _ := by simp
  skew_left _ _ := rfl
  skew_right _ _ := rfl
  spec _ _ := by simp

/-- Counterexample: `Q x = x` is not Eulerian for any `D` and `T` on a nontrivial space
(`⟪Q x, x⟫ = ‖x‖²` cannot vanish). -/
theorem not_eulerianODE_id [Nontrivial E] (D : E →L[ℝ] E) (T : E → E → E → ℝ) :
    ¬ EulerianODE D T (fun x => x) := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have := h.spec x x
  rw [h.skew_left, real_inner_self_eq_norm_sq] at this
  exact hx (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

end PlasmaLean.Fluids
