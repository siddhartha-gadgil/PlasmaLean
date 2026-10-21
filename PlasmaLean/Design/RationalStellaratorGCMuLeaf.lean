/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuInstance
public import PlasmaLean.Design.RationalStellaratorGCPoly2

/-!
# The leaves of `|B|` in product form (for the `μ > 0` family certificate)

The ball pipelines of the `μ > 0` passing family certificate (`Design/RationalStellaratorGCMu*`)
compute the expanded leaves `Q P P₄`, `E₄` and their derivatives as products of smaller
variables (`q · (P P₄)`, `R⁸ P₄² − 1`, …) instead of expanding them in monomials. The node
identities then need the leaves in product form, in terms of the tree `q` (`eq`) of
`Design/RationalStellaratorGCFlow`:

* `evalQ_eq`: `Q P P₄ = q · P · P₄`;
* `E4u_eq`: `∂_u E₄ = 8 R⁷ P₄² + 2 R⁸ P₄ ∂_u P₄`;
* `QPP4u_eq`, `QPP4z_eq`: the `u`- and `z`-derivatives of `Q P P₄` with the derivatives of the
  tree `q`;
* `P4_val`, `P4u_val`: `P₄` and `∂_u P₄` as explicit polynomials in `u`.

**Sanity.** `evalQ_eq_zero`: at the origin (`u = z = c = s = 0`) both sides are `q(0) P(0) P₄(0)`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2

/-- **`Q P P₄ = q · P · P₄`** with the tree `q`. -/
theorem evalQ_eq (x : Fin 6 → FA) :
    PolyExpr.eval x QPP4P = PolyExprS.eval x eq * PolyExpr.eval x PuP * PolyExpr.eval x P4P := by
  rw [QPP4_val]
  simp only [eq, eR, PolyExprS.eval, PolyExprS.eval_ofPoly, map_one]
  ring

/-- **Sanity**: the product form at the origin. -/
theorem evalQ_eq_zero :
    PolyExpr.eval (fun _ => (0 : FA)) QPP4P = PolyExprS.eval (fun _ => (0 : FA)) eq *
      PolyExpr.eval (fun _ => (0 : FA)) PuP * PolyExpr.eval (fun _ => (0 : FA)) P4P :=
  evalQ_eq _

/-- **`∂_u E₄ = 8 R⁷ P₄² + 2 R⁸ P₄ ∂_u P₄`.** -/
theorem E4u_eq (x : Fin 6 → FA) :
    PolyExpr.eval x E4uP = 8 * (1 + x 0) ^ 7 * PolyExpr.eval x P4P ^ 2 +
      2 * (1 + x 0) ^ 8 * PolyExpr.eval x P4P * PolyExpr.eval x P4uP := by
  rw [← E4_d0u, E4_d0, P4_d0u]

/-- **`∂_u (Q P P₄)`** in product form with the tree `q`. -/
theorem QPP4u_eq (x : Fin 6 → FA) :
    PolyExpr.eval x QPP4uP = PolyExprS.deriv x (Pi.single 0 1) eq * PolyExpr.eval x PuP *
      PolyExpr.eval x P4P + PolyExprS.eval x eq * (PolyExpr.eval x PdP * PolyExpr.eval x P4P +
        PolyExpr.eval x PuP * PolyExpr.eval x P4uP) := by
  rw [← QPP4_d0u, QPP4_d0, P4_d0u, show pd x 0 PuP = PolyExpr.eval x PdP from Pd_d0 x]
  simp only [eq, eR, PolyExprS.eval, PolyExprS.deriv, PolyExprS.eval_ofPoly,
    PolyExprS.deriv_ofPoly, map_one, pd]
  simp
  ring

/-- **`∂_z (Q P P₄)`** in product form with the tree `q`. -/
theorem QPP4z_eq (x : Fin 6 → FA) :
    PolyExpr.eval x QPP4zP = PolyExprS.deriv x (Pi.single 1 1) eq * PolyExpr.eval x PuP *
      PolyExpr.eval x P4P := by
  rw [← QPP4_d1z, QPP4_d1, P_d1, P4_d1]
  simp only [eq, eR, PolyExprS.eval, PolyExprS.deriv, PolyExprS.eval_ofPoly,
    PolyExprS.deriv_ofPoly, map_one, pd]
  simp
  ring

/-- **`P₄ = 1 − 4u + 10u² − 20u³ + 35u⁴ − 56u⁵ + 84u⁶`.** -/
theorem P4_val (x : Fin 6 → FA) :
    PolyExpr.eval x P4P = 1 - x 0 * 4 + x 0 ^ 2 * 10 - x 0 ^ 3 * 20 + x 0 ^ 4 * 35 -
      x 0 ^ 5 * 56 + x 0 ^ 6 * 84 := by
  simp only [PolyExpr.eval, P4P, sumE, monoE, PolyExpr.eval_npow, map_ofNat, map_neg, map_one,
    map_zero]
  ring

/-- **`∂_u P₄ = −4 + 20u − 60u² + 140u³ − 280u⁴ + 504u⁵`.** -/
theorem P4u_val (x : Fin 6 → FA) :
    PolyExpr.eval x P4uP = -4 + x 0 * 20 - x 0 ^ 2 * 60 + x 0 ^ 3 * 140 - x 0 ^ 4 * 280 +
      x 0 ^ 5 * 504 := by
  simp only [PolyExpr.eval, P4uP, sumE, monoE, PolyExpr.eval_npow, map_ofNat, map_neg, map_zero]
  ring

end PlasmaLean.Design.RationalStellaratorGC
