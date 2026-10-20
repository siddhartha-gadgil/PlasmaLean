# UNTRUSTED: oracle for the KAM-route torus certificate (stages K2′ and K2)

These scripts only *propose* a candidate torus and *predict* the kernel computations. Nothing
here is trusted. Everything used in Lean is re-checked by the kernel in

- `PlasmaLean/Certificates/Kronecker2D.lean`: exact ℓ¹ norms of bivariate integer polynomials by
  Kronecker substitution, plus digit sums.
- `PlasmaLean/Design/KamTorusAData.lean`: the torus coefficients, emitted by `emit_lean.py`.
- `PlasmaLean/Design/KamTorusAForms.lean` and `KamTorusACheck.lean`: the residual polynomial forms
  and the `decide +kernel` evaluations.
- `PlasmaLean/Design/KamTorusA.lean`: the semantic theorems (`torusA_error_le`,
  `torusA_flow_error`, `torusA_graph`).

Environment: a Python 3.14 venv in `/tmp/k2venv` with numpy, scipy, mpmath and gmpy2. Scratch files
go to `/tmp/k2work`.

## What is solved (exact form of the equation)

Torus A of `notes/theory/kam-route.md` has `ι = [0;7,3,1,1,…] = (75 + √5)/562 = 0.1374307259…`.
The unknown is the stellarator-symmetric map `(θ, φ) ↦ (R, z)` with `ψ = 2φ − π/2`:

- `R = Σ a_km cos(kθ + mψ)`;
- `z = Σ b_km sin(kθ + mψ)`;
- truncation `|k| ≤ N`, `|m| ≤ M`.

It solves the **flow form** of invariance, with the toroidal angle `φ` as field-line time,
multiplied by the polynomial denominator `D = R²(1 + ε ∂_φ h)` (here `ε = 1/4`):

    D (∂_φ R + ι ∂_θ R) − 2εR Ps = 0,      D (∂_φ z + ι ∂_θ z) − εR² Pz = 0,

with `Ps = R³ ∂_R h / 2` and `Pz = R² ∂_z h` (formulas in `field.py`). These are polynomial in
`R, z, cos 2φ, sin 2φ`. Equivalently, `∂_φ K + ι ∂_θ K = (B^R, B^z)/B^φ ∘ K`, which is
`B(K) ∥ ∂_φK + ι∂_θK` with time normalized by `B^φ`. The frequency is fixed. Stellarator symmetry
removes the phase freedom, so the Galerkin system is square and nonsingular.

## Files

| File | Purpose |
| --- | --- |
| `field.py` | `D`, `Ps`, `Pz` in `(s = R², z, ψ)`, and the field-line right-hand side (checked against the note's `fieldmap.py`). |
| `init_guess.py` | Builds the initial guess. It bisects the launch radius on the symmetric half-plane `φ = π/4` to reach `ι_A` (`r = 0.18819`), takes weighted-Birkhoff Fourier coefficients of the period-map curve, then flows to a 96 × 64 grid. |
| `flow_torus.py` | Double-precision Galerkin–Newton for the flow-form equations in the R-form ansatz, with continuation in `(N, M)`. |
| `exact.py` | Exact big-integer evaluation of the cleared residual polynomials (Kronecker substitution). It mirrors the Lean forms `Dform`, `RRform`, `RZform`. |
| `refine.py` | Refinement `x ← x − J₀⁻¹ F_exact(x)`. Here `J₀` is the double-precision Jacobian and `F_exact` is the Galerkin projection of the exact residual of the dyadic torus. Each step gains about 13 digits. |
| `emit_lean.py` | Writes `KamTorusAData.lean` (packed 96-bit fields). It predicts every kernel check: digit sums, centre coefficients `c0D` and `c0N`, a priori bounds, and the Kronecker parameters. |
| `strip_norms.py` | Weighted ℓ¹ norms of the exact residual on complex strips, as input for K3. |
| `twist.py` | ELP-S twist (Def. 6.1, the note's recipe) and the shear `dι/dΦ` from neighbouring Galerkin tori. |

Pipeline:

    python init_guess.py && python flow_torus.py && python refine.py 32 22 90 96
    python emit_lean.py && python strip_norms.py && python twist.py

## Results (numerical observations, except where certified)

**Torus A, `N = 32`, `M = 22`, coefficients over `2^90`.** There are 1463 + 1462 coefficients,
and `ι_q = Iq/2^96` with `|ι − ι_q| = 4.7e-30`.

**Exact ℓ¹ norm of the residual.** This is a sup-norm bound over all real `θ, φ`:

| Component | Exact ℓ¹ norm | Certified in Lean |
| --- | --- | --- |
| R | 1.219e-23 | ≤ 1.23e-23 |
| z | 6.93e-24 | ≤ 6.94e-24 |

**Residual at other truncations.** These used other runs of `refine.py`:

| N | M | P | R-residual | z-residual |
| --- | --- | --- | --- | --- |
| 28 | 18 | 80 | 7.6e-20 | 2.8e-20 |
| 36 | 26 | 96 | 1.1e-25 | 1.0e-25 |

**Coefficient decay (analyticity width).**
- In `θ`: `max|coeff|` is 2.4e-5 (k = 4), 4.2e-9 (8), 6.1e-12 (12), 7.3e-15 (16), 1.4e-18 (20),
  5.7e-22 (24), 1.8e-24 (28) and 8e-28 (32). The rate is `e^{-1.86 k}`, a strip of 1.86 rad, or
  0.30 turns (the note: ≈ 0.27).
- In `ψ`: 5.1e-4 (m = 2), 4.3e-6 (4), 7.5e-11 (8), 3.9e-15 (12), 2.4e-19 (16), 1.8e-23 (20) and
  1.3e-25 (22). The rate is `e^{-2.49 m}`, a strip in `φ` of 1.25 rad, or 0.40 in turns of the
  period `π`.

**Twist.**
- ELP-S twist: `𝒯 = +9.73e-4`, or `𝒯/|ω_s| = 3.1e-3`, the same as the note.
- Shear `dι/dΦ = 0.063`, where `Φ_A = 0.0568` is the toroidal flux through `φ = π/4`.

**Lean-certified graph data.**
- Winding rate `(R − 1)∂_θ z − z∂_θ R ≥ 0.015`; the oracle minimum is 0.0157.
- `0.077 ≤ rt ≤ 0.19`; the oracle range is 0.098–0.188.
- `0.59 ≤ D ≤ 1.42`.

**Strip norms of the exact residual (input for K3).** The norm is
`‖E‖_ρ = Σ |ê_km| e^{2πρ(|k|+|m|)}`, with angles in turns and `γ = 0.069`:

| ρ | ‖E_R‖_ρ | ‖E_z‖_ρ | ‖E‖_ρ/(γ⁴ρ⁴) |
| --- | --- | --- | --- |
| 0 | 1.2e-23 | 6.9e-24 | – |
| 0.01 | 7.8e-23 | 4.4e-23 | 3.5e-10 |
| 0.02 | 5.8e-22 | 3.5e-22 | 1.6e-10 |
| 0.03 | 5.0e-21 | 3.2e-21 | 2.7e-10 |
| 0.05 | 5.4e-19 | 4.0e-19 | 3.8e-9 |
| 0.10 | 3.1e-13 | 2.3e-13 | 1.4e-4 |

The Fourier truncation tail dominates the strip norms; the residual has modes up to `|k| = 192`,
`|m| = 133`. The FHL-type condition `C₁‖E‖_ρ/(γ⁴ρ^4) < 1` therefore tolerates `C₁` up to about
6e9 at `ρ ≈ 0.02`. With the low divisors treated exactly (`γ ≈ 0.27` for `k ≥ 2`), the tolerance
rises to about 1.4e12. A larger `N`, `M` shifts the optimum to larger `ρ`.
