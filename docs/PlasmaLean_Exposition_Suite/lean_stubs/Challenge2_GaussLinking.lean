/-
  PlasmaLean Pure Math Bounty #2 (Algebraic & Differential Topology)
  File: lean_stubs/Challenge2_GaussLinking.lean
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

abbrev ℝ³ := EuclideanSpace ℝ (Fin 3)

def cross3 (u v : ℝ³) : ℝ³ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The Gauss linking kernel at separated points x ≠ y with tangents u, v -/
noncomputable def gaussLinkingIntegrand (x y u v : ℝ³) : ℝ :=
  ⟪cross3 u v, x - y⟫_ℝ / (‖x - y‖ ^ 3)

/-- Symmetry of the Gauss linking integrand under swapping the two curves -/
theorem gaussLinkingIntegrand_symm (x y u v : ℝ³) :
    gaussLinkingIntegrand x y u v = gaussLinkingIntegrand y x v u := by
  -- TARGET FOR TOPOLOGISTS:
  -- Use antisymmetry of cross3 (cross3 v u = -cross3 u v) and (y - x = -(x - y)).
  sorry
