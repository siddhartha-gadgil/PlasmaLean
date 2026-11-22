# Examples: Perturbation Bounds and Robust Margins

## Example 1: Field error from coil placement errors

**Problem shape:** A filament coil `c` is built as `actual`, within position error `ε` and tangent
error `η`. Bound the change of the Biot–Savart field at a point `x`.

**Use of technique:**
1. Hypotheses: separation `d + ε ≤ ‖x - c t‖`, `‖actual t - c t‖ ≤ ε`,
   `‖deriv actual t - deriv c t‖ ≤ η`, `‖deriv c t‖ ≤ V`.
2. Kernel estimate: `inverseCube_perturbation` bounds the change of `r/‖r‖³`, and
   `filamentKernel_perturbation` the change of the integrand.
3. Integrate: `filamentField_perturbation` gives
   `‖B_actual − B_c‖ ≤ |μ₀ I/(4π)| (η/d² + V·(4/d³)·ε) |b − a|`
   (`PlasmaLean/Theory/Fields/CoilPerturbation.lean`).
4. A property of `B` with margin larger than this bound holds for every built coil in tolerance.

## Example 2: Current errors

**Problem shape:** Currents are known only within `|I − J| ≤ δI`.

**Use of technique:**
1. The field is linear in the current: `filamentField_sub_current` gives
   `filamentField μ₀ I c a b x - filamentField μ₀ J c a b x = filamentField μ₀ (I - J) c a b x`.
2. Bound that field by the nominal field-magnitude bound times `δI/|I|`.
3. Add to the placement bound of Example 1.

## Example 3: Robustness over an uncertainty set

**Problem shape:** A design property is certified on a parameter set `U`; deduce it on a smaller
operating envelope `V`.

**Use of technique:**
1. `robust_mono`: `RobustDesign C d U` and `V ⊆ U` give `RobustDesign C d V`
   (`PlasmaLean/Bridge/Contracts.lean`).
2. To enlarge `U` instead, cover the larger set by boxes, certify each with a margin and a
   Lipschitz bound in the parameter (`certificate_reduction`), and combine.
