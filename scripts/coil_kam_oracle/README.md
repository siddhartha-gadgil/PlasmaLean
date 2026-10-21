# UNTRUSTED: oracle for the coil-field KAM, stage 2 (refit and sampled residual certificate)

These scripts only *propose* data (a rational torus, an exponential table, sums) and *predict*
the kernel computations. Nothing here is trusted: every number used in Lean is recomputed by the
kernel in `PlasmaLean/Design/CoilKam*.lean`.

Environment: the Python venv `/tmp/k2venv` (numpy, scipy, mpmath, gmpy2). Scratch files go to
`/tmp/ckwork`. Torus A (start of the refit) is read from `/tmp/k2work/double_A.npz`
(`scripts/kam_oracle/flow_torus.py`).

## Files

| File | Purpose |
| --- | --- |
| `coil.py` | The coil set parsed from the Lean sources (`repKC`, `repVC`, the orbit under `{id, Rot_π, σ, Rot_π σ}`, the TF rectangle with `Λ = 10⁶`, `κ = 1/2`); real and complex closed-form segment fields. The factor `(α+β)/(αβ(αβ+a·b))` is evaluated in the stable form `(α+β)(αβ−a·b)/(αβ|a×b|²)` when `a·b < 0` (the TF legs of length `2·10⁶` lose 12 digits otherwise; the Lean evaluator uses the same split). |
| `refit.py` | Double-precision Galerkin–Newton refit of the `ι_A` torus to the coil field in `(θ, φ)` with the **full** toroidal period (the TF return legs break the 2-fold rotation and the stellarator symmetry `σ` at `O(1/Λ)`), no symmetry, phase fixed by `a'_{1,0} = 0`, least squares (one redundant equation). Flow form without division: `E_R = B^φ 𝓛R − R B^R`, `E_z = B^φ 𝓛z − R B^z`, `𝓛 = ∂_φ + ι∂_θ`. |
| `residual_norms.py` | Weighted `ℓ¹` norms of the refit residuals (FFT on a fine grid). |
| `requirement.py` | The KAM smallness requirement `e₀ ≤ δ₀⁴/(32κ)`, transcribing the `SC` formulas of `KamFlowStep.lean` (reproduces torus A: `κ = 6.0·10⁹`, `e₀,req = 5.4·10⁻¹⁹`), with the coil scalings (φ-convention `γ_eff = γ/4`, isotropic strip, analytic Taylor constant from `bd_comp_taylor`). |
| `emit_lean.py` | Exact Python mirror of the Lean integer checkers (`sqrtBr`, `segAP`, `fieldAP`, `expTableOK`, `torusAP`, `pointAP`); writes `CoilKamData.lean` (records, table, `⌊2¹⁰⁰ι_A⌋`) and, with `CK_GRID=1`, the kernel-evaluation files `CoilKamGrid0–3.lean` with the predicted chunk values. |
| `cert_numbers.py` | The rational constants of `CoilKamCert.lean` (coefficient sums at the strip weights, mapping hypothesis, `Mcoil`, sup bounds, tail) and the predicted certified bound. |

Pipeline:

    python refit.py 8x16 12x24 16x40 20x56
    python emit_lean.py 8 16 && CK_GRID=1 python emit_lean.py 8 16
    python cert_numbers.py; python residual_norms.py; python requirement.py

## Results (numerical observations unless stated)

**Refit (double precision).** Newton converges quadratically from torus A (initial `|F| = 1.4·10⁻⁶`):

| `N × M` (θ × φ) | unknowns | sup `|E_R|`, `|E_z|` | `ℓ¹_{0.063}` of `E_R` | `ℓ¹_{(0.1257, 0.063)}` |
| --- | --- | --- | --- | --- |
| 8 × 16 | 1 120 | 1.2·10⁻⁶, 1.6·10⁻⁶ | 1.4·10⁻⁵ | 1.9·10⁻⁵ |
| 12 × 24 | 2 449 | 2.8·10⁻⁷, 1.5·10⁻⁷ | 2.4·10⁻⁶ | 2.9·10⁻⁶ |
| 16 × 40 | 5 345 | 3.7·10⁻¹⁰, 2.5·10⁻¹⁰ | 1.0·10⁻⁸ | 1.4·10⁻⁸ |
| 20 × 56 | 9 225 | 4.9·10⁻¹³, 2.9·10⁻¹³ (double floor) | 6.6·10⁻¹¹ | 3.6·10⁻¹⁰ |

The φ-decay is `≈ e^{−0.42 m}` (singularity of the complexified torus at a coil,
`|Im φ| ≈ 0.25–0.3`), the θ-decay `≈ e^{−1.3 k}`. The odd-`m` (TF-asymmetry) coefficients are
`≤ 1.5·10⁻⁶`.

**Requirement** (`requirement.py`, φ-convention, `γ_eff = γ/4`, `cK ≈ 1.3·10⁵`, `cL ≈ 1.0·10⁶`):

| strip `r`, PW gap, `M`, radius `d` | `κ` | `e₀,req` |
| --- | --- | --- |
| 0.02, 0.03, `Mcoil = 3.5·10⁴`, 0.03 | 5.3·10²³ | 3.9·10⁻³⁶ |
| 0.063, 0.05, `3.5·10⁴`, 0.05 | 7.2·10²² | 2.9·10⁻³³ |
| 0.063, 0.05, sharp `M = 10`, 0.05 | 2.1·10¹⁹ | 1.0·10⁻²⁹ |
| 0.063, 0.19 (adapted neighbourhood), `M = 10`, 0.1 | 3.8·10¹⁷ | 5.4·10⁻²⁸ |

**Coarse certificate** (`N = 8`, `M = 16`, 281 records, `D = 2¹⁰⁰`, grid `16 × 32`,
`K = (7, 15)`, strips `ρ' = 1/20`, `ρ = 1/25`, `r = 1/50`, neighbourhood
`coilNbhdP (23/100) (7/100)`): sampled part `2.1·10⁻⁴` (`E_R`) and `2.5·10⁻⁴` (`E_z`);
aliasing tail `4.5·10⁹` and `2.7·10⁹`. The certified bounds are therefore `4.5·10⁹`, `2.71·10⁹`
(vacuous), entirely due to `Mcoil` and the strip margin.

**Toroidal field on the complex neighbourhood** (sampled, torus points `+ i v`, `|v| = 0.07`):
`sup |B_poly| ≈ 0.15`, `min |R B^φ| ≈ 0.976` (real points: `0.981`). The per-segment triangle
bound is `≥ 5.3` even with exact per-segment sups at real points, so no segment-wise bound can
certify `|B^φ| > 0` (see `notes/theory/coil-kam-status.md`).
