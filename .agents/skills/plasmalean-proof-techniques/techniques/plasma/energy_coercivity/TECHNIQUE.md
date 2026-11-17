# Skill: Energy Principle and Coercivity

**Pre-condition:** The claim is a stability statement, or a bound, for a linear(ised) system with
a conserved or dissipated quadratic energy: an MHD potential energy `δW`, a Newcomb, Suydam,
Mercier or ballooning form, a Sturm–Liouville quadratic form, or an abstract `m(v,v)/2 + a(x,x)/2`.
Do not use it for a genuinely nonlinear claim without first linearising or bounding the
nonlinearity, and do not use it when the form is known to have negative directions (then look for
an instability witness with `local_obstructions`).

**Goal:** Prove a quantitative lower bound `q(ξ) ≥ c · ‖ξ‖²` with explicit `c > 0` (or `c ≥ 0`
for marginal stability) on a declared admissible class, and convert it into the dynamical
conclusion.

**Instructions:**
1. **Fix the admissible class.** State the function space, regularity (`C1On ξ ξ' x₀ x₁`),
   boundary conditions (`ξ x₀ = 0`, `ξ x₁ = 0`), and the quotient by neutral directions
   (displacements that leave the energy unchanged). A form that vanishes on a neutral mode controls
   nothing in that direction (`Sanity/NeutralMode.lean`): either quotient it out or state the
   result on the complement.
2. **Separate the terms.** Write `q = ∫ f ξ'² + g ξ²` (or the analogue) and identify the
   indefinite part: usually a cross term `2 φ ξ ξ'` or a negative potential.
3. **Complete the square with a gauge.** Choose an auxiliary function `φ` (Picone), `w`
   (Riccati), a Jacobi solution `u`, or a Barta test function, so that
   `f ξ'² + g ξ² = f (ξ' + (φ/f) ξ)² + (g − φ' − φ²/f) ξ² + (φ ξ²)'`. The boundary term vanishes by
   the boundary conditions; the remainder is the potential that needs a sign.
4. **Reduce to a pointwise inequality.** The bound with constant `c` follows from
   `φ² ≤ f (g − c − φ')` pointwise. This is a one-variable inequality, often checkable exactly
   (and by a finite certificate on cells, see `certificate_reduction`).
5. **Use a Hardy-type inequality** for the singular weight at a resonant surface
   (`∫ ξ'² ≥ (1/4) ∫ ξ²/x²`); this is where the Suydam constant `F/4` comes from.
6. **Convert to dynamics.** With conservation of `E = m(v,v)/2 + a(x,x)/2` and coercivity
   `c ‖x‖² ≤ a(x,x)`, get `‖x‖² ≤ 2E₀/c` for all time.
7. **Test the edges.** Check `c` on a degenerate case (zero shear, zero pressure gradient), and
   check the constant is sharp or record by how much it is not.

**Lean:** `PlasmaLean/Theory/Stability/` (`Suydam`, `Newcomb`, `Ballooning`, `SturmNecessity`,
`AbstractEnergy`, `YoungBounds`). Statements follow the shape
`c * ∫ ξ² ≤ form ξ ξ'` under `C1On` and boundary hypotheses; name a result on a finite subspace
or a supplied reduction accordingly.
