# Examples: Local Obstructions and Necessity

## Example 1: No vacuum minimum-B around a closed field line

**Problem shape:** Show that a vacuum field cannot have `|B|` increasing away from a closed field
line in every transverse direction.

**Use of technique:**
1. Localize on the closed field line (the would-be magnetic axis).
2. Curvature identity in vacuum: `∇⊥|B| = |B| κ` (`gradient_perp_norm_eq_curvature`).
3. A transverse minimum of `|B|` makes `∇⊥|B| = 0`, so `κ = 0` at every point of the line
   (`fieldCurvature_eq_zero_of_transverse_critical`).
4. A closed curve cannot have zero curvature everywhere (`not_forall_fieldCurvature_eq_zero`).
5. Conclusion: `VacuumField.not_closed_fieldLine_minB`
   (`PlasmaLean/Theory/Fields/CurvatureObstruction.lean`; source Helander 2014, §2.4, §3.3).

## Example 2: No interior maximum of |B| for a vacuum field

**Problem shape:** Bound `|B|` inside a plasma volume by its values on the boundary surface.

**Use of technique:**
1. At an interior local maximum the Laplacian is nonpositive: `laplacian_nonpos_of_isLocalMax`.
2. The field equations give the opposite sign: the Bochner identity `laplacian_normSqField`,
   `Δ|B|² = 2 ∑ (∂ⱼ Bᵢ)² ≥ 0` for a vacuum field. To make the inequality strict, add `ε ‖x‖²`
   (`laplacian_normSq`: its Laplacian is 6) and let `ε → 0`.
3. Conclusion: the weak maximum principle `weak_maximum_principle`, and
   `VacuumField.normSq_le_of_frontier`, `VacuumField.not_strict_local_max_norm`
   (`PlasmaLean/Theory/Fields/Subharmonic.lean`). The same argument bounds the error between two
   vacuum fields by its boundary values (`VacuumField.error_le_of_frontier`).

## Example 3: Quasisymmetry is not a PDE symmetry (counterexample)

**Problem shape:** Does zero scalar quasisymmetry error with `X p = 0` imply that the pressure
force commutes with the symmetry generator `X`?

**Use of technique:**
1. Localize the claim to a commutator `[X, ∇p]` and expand it with the Lie-bracket/gradient
   identity: it equals a strain term `(DX + DXᵀ) ∇p`.
2. Choose a polynomial witness making the strain term nonzero while all hypotheses hold:
   `B = e_z`, `X = (1 + y) e_x`, `p = y`.
3. Check every hypothesis exactly and the failure `[X, ∇p] = −e_x`:
   `quasisymmetry_not_pde_symmetry` (`PlasmaLean/Sanity/QuasisymmetryNotSymmetry.lean`).

## Example 4: Necessity of the Newcomb condition (Sturm)

**Problem shape:** Show that a conjugate point inside the interval destroys positivity of a
Newcomb form.

**Use of technique:**
1. From the conjugate point, take the Jacobi solution `u` vanishing at both ends (`ConjugatePoint`).
2. Integrate by parts: `energy_eq` gives `newcombForm P Q a z u u' = c * ∫ W u²`.
3. With `u ≠ 0` (`exists_ne_zero`) and positive weight (`mass_pos`), the sign of `c` decides the
   sign of the energy, giving the destabilizing test function
   (`PlasmaLean/Theory/Stability/SturmNecessity.lean`).
