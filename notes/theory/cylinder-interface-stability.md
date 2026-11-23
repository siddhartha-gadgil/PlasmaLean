# A fully signed free-boundary ideal-MHD benchmark and a toroidal interface criterion

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-44` |
| Title | Periodic-cylinder plasma–vacuum interface with a complete signed energy, an explicit all-mode window, a toroidal interface criterion, and the transfer problem (method note for N-12) |
| Kind | method |
| Addresses | `Q-30`, `Q-31` (new); `G-4`, `Q-3`, `Q-14`, `Q-20` |
| Depends on | N-42 (source claims S-16 to S-22); N-12, N-13 (stepped-pressure route); N-33 (certified torus A for Q-31); Lean: none yet |
| Dependency requirement | Q-30 (a) needs only real algebra, with the Bessel and impedance quantities supplied as hypotheses; Q-31 needs the certified torus A (`ExactTorusA`, on-demand) and evaluation of `g`, `II`, `ω` on it |
| Produces | Q-30, Q-31 statements; a stress example (the wall dependence) and a joint current, transform and interface screening test |
| Difficulty | routine (Q-30 a); moderate (Q-31 numerics, then certificate); research (Q-30 b) |
| Status | stated; complete proof of the cylinder window checked numerically (N-42); (a) lean-ready; toroidal screening proposed |
| Lean evidence | none yet |
| Audit evidence | not audited |
| Last updated | 23 November 2026. Added the current and transform checks for the first finite-pressure screening test. |
| Patched by / Alternatives | method for N-12 (its compiled family-1/family-2 results stand) |

## Purpose and scope

The project's ideal-MHD results so far concern the Landreman families (N-12: family 1 is
Mercier-unstable; family 2 is stable on a band but carries net current). The current-free
finite-β route (Q-14, Q-20) points to stepped-pressure equilibria, whose stability needs the
signed interface term. The source of N-42 gives the first complete example in which **every**
term of `δW` is signed, the interface curvature term included. The example is a periodic
cylinder, not an embedded torus.

**Model.**
- Plasma `r < a` with constant pressure and the uniform field `B_i e_z` (current-free core).
- Vacuum `a < r < b` with `B_e e_z + B_θ (a/r) e_θ`.
- A perfectly conducting fixed wall at `r = b`.
- Lossless ideal MHD with fixed plasma axial, vacuum axial and vacuum azimuthal fluxes.
- Force balance: `p = (B_e² + B_θ² − B_i²)/(2μ₀)`.

## Results (source §6, checked in N-42)

- **Mode coefficient (classical surface-current model).**
  `F_mn = κI_m/I_m' + ((kaB_e + mB_θ)/B_i)² n_out − B_θ²/B_i²`, with `κ = a|k|`.
- **Unstable branch.** If `B_e ≥ B_i` and `B_θ ≠ 0`, the mode `m = 1`, `k = −B_θ/(aB_e)` has
  `F < 0` for any wall.
- **Window.** Take `0 < s ≤ 1/4`, `B_θ² = sB_i²`, `B_e² = (1 − 3s/4)B_i²`, so `p = sB_i²/(8μ₀)`.
  Let `h = b/a`, `ℓ = log h`, `D = (h² − 1)/2` and `β_e² = 1 − 3s/4`, and assume
  `ℓ + sD/β_e² ≤ s/8` (for example `h ≤ 1 + s/16`). Then:
  - `F_mn ≥ s²/8` for `m ≠ 0`;
  - `F_0n ≥ 2 − s`;
  - `F_00 = 2 − s + γs/4 + β_e²/D + s/ℓ`;
  - `F_mn ≥ (s²/80)(1 + |m| + κ)`, uniformly in the period.
- **Proof ingredients** (all elementary given these hypotheses):
  - `κI_m/I_m' ≥ κ²/(m + κ²/(2(m+1)))`, from the series;
  - `n_out ≥ 1/(m²ℓ + κ²D)`, from a constant trial potential in the dual Neumann principle;
  - Cauchy's inequality `t²/A + (1−t)²/B ≥ 1/(A + B)`.

**Stress example (N-42, `check_far_wall.py`).** At `s = 0.161` (`β ≈ 0.04`), with the window's
fields, the minimum of `F` over `m ≥ 1` is `+0.013` at `h = 1.01` and `+0.005` at `h = 1.05`. It
is negative from `h = 1.1` on, and `−0.079` with no wall. The window is **wall-stabilised**: the
wall must sit within about 5% of the minor radius.

## Toroidal interface criterion (source §7)

**Setting.**
- A vacuum core field `Y` is tangent to an analytic toroidal interface, straightened so that
  `Y = ω^i∂_i`.
- The interface has induced metric `g` and second fundamental form `II`.
- Exterior fields come from KAM graphs `I = rd + o(r)` of `H = ω·I + ½Iᵀg⁻¹I` (the
  Enciso–Luque–Peralta-Salas construction), so `X = Y + rg⁻¹d + o(r)`.

**Criterion.** The conditions `ω·d > 0` and `II(Y, g⁻¹d) < 0` everywhere give `p > 0` and a
positive interface coefficient for small `r`. Then every term of `δW` is nonnegative, though the
energy is not coercive.

**One-dimensional feasibility.** Write `d = ω/|ω|² + σJω`, and put
`a₀ = II(Y, g⁻¹ω)/|ω|²` and `b₀ = II(Y, g⁻¹Jω)`. The criterion is `a₀ + σb₀ < 0` on the whole
torus. This is a sup/inf condition on `σ`, and a failure has a one- or two-point witness. The
first-order terms were re-derived in N-42.

## Transfer to a torus (source §8)

- A bent tube of radius `1/ε` has the metric `dx² + dy² + (1 + εx)²ds²` with `L = 2π/ε`.
- A sufficient certificate: after identifying boundaries and flux constraints, the reduced
  interface Hessian changes by less than half the cylinder gap (`H^{1/2} → H^{−1/2}`),
  **uniformly in `L`**.
- Open. Low axial Neumann modes make naive estimates singular.

## Barriers

- **Not a reactor configuration.** The window needs a wall almost touching the plasma, a
  substantial interface current, and a periodic cylinder.
- **No Bessel functions in Mathlib.** The special-function bounds would need a small new
  library, or must be supplied as hypotheses (the supplied-reduction pattern).
- **Q-31 depends on unproved inputs.** It needs the exterior KAM graphs (an existence theorem not
  in Lean) and the `o(r)` uniformity. On a certified torus, the computable part is the sign test
  for `a₀`, `b₀`.

## Outputs

- **Q-30.**
  - (a) Lean-ready: the window inequality chain with `X_m(κ) ≥ κ²/(m + κ²/(2(m+1)))` and
    `n_out ≥ 1/(m²ℓ + κ²D)` as hypotheses, concluding `F ≥ s²/8` and the gap bound. This is the
    algebraic core of a signed-interface stability theorem.
  - (b) Research: the uniform transfer to a bent tube or torus.
- **Q-31.** Evaluate `a₀`, `b₀` on the certified Dommaschk torus A. First as untrusted numerics
  (workstation or laptop), then, if a `σ` exists, as a certificate. Record either a uniform strict margin or a certified witness that excludes every σ in this
  sufficient criterion. An inconclusive enclosure leaves the question open.
- **Q-14 and Q-20.** On the same candidate, specify a nonzero pressure step, the allowed net
  toroidal current and the minimum transform. Estimate the sheet contribution to the current
  and the transform on the proposed equilibrium. Promote the sign test to an equilibrium
  project when these margins survive the step and its remainder. A vacuum loop current alone
  covers only the seed. The sign test can share surface derivatives with [N-50](harmonic-field-shape-variation.md).
- **Technique registry.** The dual trial-potential bound for a Neumann impedance is a worked
  example for "energy principle and coercivity" (`plasmalean-proof-techniques`).
