/-
  PlasmaLean Pure Math Bounty #3 (Differential Geometry of Curves)
  File: lean_stubs/Challenge3_BishopFrameNearAxis.lean
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

abbrev ℝ³ := EuclideanSpace ℝ (Fin 3)

/-- A Bishop parallel frame along a unit-speed curve with normal curvatures k1, k2 -/
structure IsBishopFrame (T N1 N2 : ℝ → ℝ³) (k1 k2 : ℝ → ℝ) : Prop where
  deriv_T  : ∀ s, HasDerivAt T (k1 s • N1 s + k2 s • N2 s) s
  deriv_N1 : ∀ s, HasDerivAt N1 (-k1 s • T s) s
  deriv_N2 : ∀ s, HasDerivAt N2 (-k2 s • T s) s

/-- Conservation of orthonormality along the Bishop frame ODE -/
theorem bishop_frame_preserves_inner_products
    (T N1 N2 : ℝ → ℝ³) (k1 k2 : ℝ → ℝ)
    (hB : IsBishopFrame T N1 N2 k1 k2) :
    ∀ s, HasDerivAt (fun t => ⟪N1 t, N2 t⟫_ℝ) 0 s := by
  -- TARGET FOR DIFFERENTIAL GEOMETERS:
  -- Differentiate ⟪N1 t, N2 t⟫_ℝ and use orthogonality to T.
  sorry
