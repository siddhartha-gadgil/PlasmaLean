# Examples: Energy Principle and Coercivity

## Example 1: Suydam lower bound by Hardy's inequality

**Problem shape:** Show that the screw-pinch interchange form `∫ F ξ'² + G ξ²` (with `F ≥ 0`
constant on an interval, Dirichlet ends) is bounded below by `(G + F/4) ∫ ξ²`.

**Use of technique:**
1. Admissible class: `C1On ξ ξ' x₀ x₁`, `ξ x₀ = 0`, `ξ x₁ = 0`.
2. The indefinite part is a negative `G`; the positive part is `F ξ'²`.
3. Hardy's inequality (`hardy`, `hardy_resonant`) bounds `∫ ξ'²` below by a multiple of `∫ ξ²`.
4. Conclude `suydamForm_lower_bound`:
   `(G + F / 4) * ∫ ξ² ≤ suydamForm F G x₀ x₁ ξ ξ'`, so Suydam's criterion `G + F/4 > 0` gives
   stability (`PlasmaLean/Theory/Stability/Suydam.lean`).

## Example 2: Picone certificate for a Newcomb form

**Problem shape:** Lower-bound `newcombForm f g x₀ x₁ ξ ξ'` with variable coefficients.

**Use of technique:**
1. Choose a gauge `φ` with derivative `h`.
2. Completing the square leaves the pointwise condition
   `φ x ^ 2 ≤ f x * (g x - c - h x)` together with `h x + c ≤ g x` and `0 ≤ f x`.
3. `picone_certificate` turns these into `c * ∫ ξ² ≤ newcombForm f g x₀ x₁ ξ ξ'`
   (`PlasmaLean/Theory/Stability/Newcomb.lean`; `riccati_certificate` and `jacobi_certificate` are
   the Riccati and Jacobi-field gauges of the same argument).
4. The pointwise condition is the part a finite certificate can check cell by cell.

## Example 3: Barta certificate for ballooning

**Problem shape:** Show the ballooning energy on a finite field-line segment is at least
`c` times the mass.

**Use of technique:**
1. Package the test function and its pointwise inequality as `BartaCertificate c`.
2. `BartaCertificate.lower_bound`: `c * op.mass ξ ≤ op.energy ξ ξ'` for every admissible `ξ`
   (`PlasmaLean/Theory/Stability/Ballooning.lean`).
3. Validate the certificate data for a concrete equilibrium with exact arithmetic
   (Solov'ev ballooning cells in `PlasmaLean/Design/`).

## Example 4: From coercivity to a bounded displacement, and its failure

**Problem shape:** Bound the displacement of `m ẍ + a x = 0` for all time.

**Use of technique:**
1. Energy conservation (`energy_conserved`) and `c ‖x‖² ≤ a x x` give
   `displacement_bound`: `‖x‖^2 ≤ 2 * E₀ / c`
   (`PlasmaLean/Theory/Stability/AbstractEnergy.lean`).
2. Necessity of `c > 0`: with `a = 0` the neutral solution `x = t` has bounded energy and unbounded
   displacement (`neutral_energy_does_not_control_displacement`,
   `PlasmaLean/Sanity/NeutralMode.lean`). This is why neutral modes must be quotiented out.
