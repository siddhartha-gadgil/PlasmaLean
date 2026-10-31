# UNTRUSTED: KAM flow-torus oracle for the Dommaschk certification target (step 2, numerics)

These scripts propose invariant tori of the certification target and estimate the quantities a KAM
certificate needs. Nothing here is trusted and there is no Lean yet. The target is the purely
rational NFP-2 field of `notes/theory/dommaschk-qa.md` §24: the candidate is
`scripts/dommaschk_qa/results/20261031T092522Z/candidate.json`, with sha256 checked at load time,
and the matching Lean field is `Design/DommaschkQA2R`. The method follows `scripts/kam_oracle/`
(torus A of the rational field) and `notes/theory/kam-route.md`.

## Files

| File | Purpose |
| --- | --- |
| `dfield.py` | Exact polynomial form of the field (below). Evaluates in numpy float/complex and in multiprecision (object arrays). Self-test against `scripts/dommaschk_qa/fieldeval.py` (agreement 1e-14). Majorant sizes. |
| `dioph.py` | Rotation numbers (noble tails), Diophantine constants, distances to the resonances ι = 2p/q. |
| `torus.py` | Field-line tracing, magnetic axis, launch radius, initial torus. Double-precision Galerkin–Newton, multiprecision refinement (gmpy2 `mpfr`), multiprecision DFT of the residual, weighted ℓ¹ strip norms. |
| `twist.py` | ELP-S twist (Def. 6.1), ported from `kam_oracle/twist.py`. Toroidal flux through φ = 0 and the shear dι/dΦ. |
| `run.py` | Driver. Restartable: stages are cached in `--work`. Writes `summary.json` and `log.txt` to `--results`. |

Workstation task: `scripts/workstation/tasks/dommaschk-kam.sh`, configured with the environment
variables `DKAM_TORI`, `DKAM_N`, `DKAM_M`, `DKAM_DPS`, `DKAM_OVER` and `DKAM_EXTRA`. Results go to
`results/<stamp>/`.

## Polynomial form

The field is `B = ∇Φ` with `Φ = φ + V`, where `V = Σ a_k V_k`.
- The 9 potentials that contain ln R have coefficient exactly 0. Every other term is
  `c R^p z^j trig(mφ)` with p and m even and `p ≥ −6`.
- So V is a polynomial in `s = R²`, `1/s`, z and the trig functions `cos nψ`, `sin nψ` for n ≤ 3,
  where `ψ = 2φ`.
- The smallest power of r₂ = s that clears V is `s³`. The denominator is `G = R B_φ = 1 + ∂_φV`,
  which makes φ the field-line time (the B^φ-type denominator). Define

      D = s³ (1 + ∂_φV) = s⁴ B^φ,   Ps = s⁴ ∂_sΦ,   Pz = s³ ∂_zΦ;   D dR/dφ = 2R Ps,   D dz/dφ = s Pz.

- D, Ps and Pz are polynomials of degree 8 in s and 5 in z (61, 56 and 45 terms).
- The torus is `R = Σ a_km cos(kθ + mψ)`, `z = Σ b_km sin(kθ + mψ)`, the stellarator-symmetric
  ansatz of `kam_oracle`, with symmetry line φ = 0, z = 0. It solves

      RR = D (∂_φR + ι ∂_θR) − 2R Ps = 0,   RZ = D (∂_φz + ι ∂_θz) − s Pz = 0

  with ι fixed. Because the frequency vector is (ι, 1), as in `KamTorusA`, the Galerkin system is
  square.
- **Sign.** ι is negative for this field.
- **Small divisors.** They are `|ιk + 2m| = 2|ωk + m|`, where `ω = ι/2` is the rotation number of
  the period map.

## Rotation numbers

| | ι | ω = \|ι\|/2 | gap | r_launch (φ = 0) | γ (τ = 1, period map; k ≥ 2) |
| --- | --- | --- | --- | --- | --- |
| **A** (main) | −(19+√5)/89 = −0.238608 | [0;8,2,1̄] | 4/17, 6/25 (margins 0.0033, 0.0014) | 0.0370 | 0.119 (k = 1); 0.365 (k = 8) |
| B | −(15−√5)/55 = −0.232071 | [0;8,1̄] | 3/13, 4/17 (0.0013, 0.0032) | 0.0566 | 0.116; 0.399 |
| C | −(85+√5)/361 = −0.241651 | [0;8,3,1̄] | 6/25, 1/4 (0.0017, 0.0083) | 0.0266 | 0.121; 0.267 |

## Results

Laptop, 31 October 2026, numerical observations. Errors are those of the polynomial residual
(RR, RZ). The flow error RR/D is at most 1/D_min ≈ 4 times larger (D ∈ [0.26, 1.04]).

| torus | N × M (unknowns) | Galerkin \|F\|, double → mp (dps 40) | true sup \|RR\|, \|RZ\| | decay θ / ψ per mode (strip, turns) | best FHL tolerance for C₁, γ / γ_{k≥2} (ρ) |
| --- | --- | --- | --- | --- | --- |
| A | 48 × 40 (7857) | 2e-16 → 1e-48 | 6.2e-16, 1.6e-16 | 0.73 / 0.89 (0.12 / 0.14) | 1.4e2 / 1.2e4 (0.015) |
| A | 64 × 52 (13545) | 2e-16 → 1e-48 | 9.5e-20, 1.1e-20 | 0.65 / 0.87 (0.10 / 0.14) | 3.7e5 / 3.2e7 (0.01) |
| B | 48 × 40 | 3e-16 → 1e-48 | 3.2e-12, 3.4e-12 | 0.47 / 0.83 (0.075 / 0.13) | 1e-2 / 1.6 |
| C | 48 × 40 | 2e-16 → 1e-48 | 1.3e-16, 3e-17 | 0.75 / 0.94 (0.12 / 0.15) | 7.7e2 / 1.9e4 |

- **Double precision** reaches its floor (true residual about 5e-15) at N ≈ 48. Beyond that, the
  multiprecision refinement is what lowers the error.
- The truncation error of A falls by about 0.24 decades per mode, with M ≈ 0.8N.
- **Extrapolation for A:** about 1e-23 at 80 × 64, and about 1e-27 at 96 × 80. The FHL tolerance
  would then be about 1e9–1e11 at 80 × 64, comparable to torus A of the rational field
  (6e9 / 1.4e12).
- **Twist** (ELP-S, field-line time, angles in turns):

  | torus | 𝒯 | 𝒯/\|ω_s\| | dι/dΦ | dι/dr_eff |
  | --- | --- | --- | --- | --- |
  | A | +5.37e-2 | +0.147 | 2.24 | 0.46 |
  | B | +3.95e-2 | +0.110 | | 0.51 |
  | C | +5.58e-2 | +0.151 | | 0.35 |

  The relative twist is about 50 times that of the rational field (3e-3), with one sign.
- **Majorants.** The large potential coefficients, up to 3e4, combine into polynomial coefficients
  of at most 156 in s.
  - In s itself, ℓ¹(D) = 1.9e3, against a value of about 0.8.
  - In local variables `u = s − R_axis²`, z, the box majorant Σ|c||u|^i|z|^j is benign:
    - for |u| ≤ 0.1 and |z| ≤ 0.1: 1.27 (D), 0.33 (Ps), 0.68 (Pz);
    - for |u| ≤ 0.25: 2.1, 0.9, 1.8.

  Lean majorants should therefore use shifted variables.

Laptop cost:
- 48 × 40, three tori: 201 s and 2.5 GB.
- 64 × 52, torus A: 66 s and 3.1 GB, after the launch radius is cached; the launch search takes
  about 45 s per torus.
- The dense Jacobian dominates memory, at about 2 × 8n² bytes.

## Plan for the Lean certificate (`KamTorusA` pattern; not done)

Emit the following, as `emit_lean.py` does for the rational field:
1. `DommaschkKamAData`: the dyadic torus coefficients (A, 80 × 64, over 2^P) and ι_q, a dyadic
   approximation of ι with an error term.
2. The residual forms. The exact D, Ps and Pz are already in `DommaschkQA2RData` (as potentials);
   they would be rederived in Lean, or emitted as `CylPoly` with an equality check.
3. Kernel ℓ¹ / weighted-ℓ¹ norms of RR and RZ. Then `torus_error_le`, plus the graph and winding
   facts used by K1 (D > 0 on the torus, and a polar graph about the axis).

**Barrier: certificate size.**
- The residual has degree 17 in the torus series (R¹⁶ from D, and R·s⁸ from Ps), against 6 for
  `KamTorusA`. For 80 × 64 the exact residual has about (34·80) × (34·64) ≈ 6e6 Fourier
  coefficients of about 17P bits. That is roughly 150 times the `KamTorusA` Kronecker
  certificate.
- The exact-Kronecker route is unlikely to fit the laptop budget. Use instead truncated ℓ¹ ball
  arithmetic with tail bounds (`Theory/KAM/StripAlgebra`, `KronBall`). Evaluate D, Ps and Pz by
  Horner in the shifted variable u, which gives the benign majorants above. Split by ψ-blocks if
  needed.
