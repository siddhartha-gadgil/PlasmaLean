# Checks and examples (N-42)

All scripts are in `scripts/fcg_source/` and are independent of the source bundle. Run them with
`.venv-ws/bin/python -I <script> [args]`. Floating-point results are untrusted numerics.

## Exact checks

`check_laurent.py scripts/dommaschk_qa/results/20261031T092522Z/candidate.json` (S-1). It builds
`F₀` from the project's own basis terms and coefficients:

```
nonzero Dommaschk coefficients: 33
log terms surviving collection: 0
nonzero Laurent monomials: 121
Delta_q F == 0: True
F* == F: True
F(-u,-v,z) == F: True
F(v,u,-z) == -F: True
coefficient of u^-6: -12674582344287*I/143360000000000
```

Every number in S-1 is reproduced.

`check_algebra.py` (S-3, S-4, S-5, S-24, S-25):

```
null-conic H_{n,k} harmonic, 2n+1 nonzero (n<=5): True
sum_{n=1}^N (2n+1) == N(N+2) (N<=20): True
n_lambda annihilates dQ (line direction): True
E_pq, O_pq harmonic for -4<=p,q<=4 (not both negative): True
(Q4) C symmetric: True
(Q4) CK - KC == S: False        <- sympy failed to simplify the trigonometric entries (see below)
(Q4) ||C||_F^2 = 2|a|^2 + ||S_perp||^2/4 <= ||S||^2 (numeric): True
(Q4) R_b(v^T C v) == v^T [C,K] v: True
(Q7) cancellation -v^T S v + 2 v^T C K v == 0: False   <- same simplification failure
```

`check_q4_numeric.py` settles the two `False` lines at random unit `b` and random admissible `S`.
It reports `max|[C,K] − S| ≤ 9 × 10⁻¹⁶`, while `max|[C,K] + S|` is of order 1, so the sign is
right. The (Q7) residual is `≤ 2 × 10⁻¹⁵`. The (Q4) and (Q7) algebra is **correct**. A by-hand
derivation agrees:

- `vᵀDKv = −vᵀKDv`, so `2vᵀDKv = vᵀ[D,K]v`;
- with `D = C/β`, this is `vᵀSv/β`;
- and `v × B = βKv`.

## Numerical checks (mpmath, 30 digits)

`check_cylinder_hotcore.py` (S-17 to S-20, S-28, S-29, S-34). Normalisation `a = B_i = 1`. The
grid is `|m| ≤ 10` and `k ∈ [−20, 20]` with step `0.05`. The script uses the recurrences for
`I_m'` and `K_m'`: mpmath's `besselk` silently ignores `derivative=1`, which corrupted an
earlier run.

| check | result |
| --- | --- |
| `k → 0` limit of the wall impedance equals the `coth` formula (`m = 2`, `b/a = 1.01`) | `25.12810939116604` both |
| `min F_mn / (s²/8)` over `m ≠ 0`, at `b/a = 1 + s/16` | 15.9 (s = 0.01), 166.7 (0.05), 16.1 (0.161), 4.14 (0.25): all ≥ 1 |
| `min F_mn / ((s²/80)(1 + |m| + κ))` | 75.7, 483, 67.0, 16.2: all ≥ 1 |
| unstable branch (`B_e = 1.1`, `B_θ = 0.5`, `m = 1`, `k = −B_θ/B_e`, `b/a = 2`) | `F = −0.0535 <` the stated bound `B_θ²/B_e² − B_θ² = −0.0434 ≤ 0` |
| parameter illustration | `p = 4.00544 × 10⁵ Pa`, `s = 0.161068`, `β = 0.040267`, `B_e = 4.68828 T`, `B_θ = 2.00667 T` |
| (H3) at `c = 2.8` | `a = 0.9505632105`, ratio `0.8257712511` (source: `> 0.95056321`, `> 0.82577125`) |
| (H3) at `c = 3` | `0.8875729286` (source: `> 0.88757292`) |
| (H4) at `c = 2.8`, `δ = 0.01` | `0.807093152` (source: `> 0.80709315`) |
| (H5) at `c = 2.8`, `δ = 0` / `c = 3`, `δ = 0.01` | `0.8078673232710731` / `0.8593547807238487` (source: the same digits) |
| `a`, `b`, `d` against quadrature of the χ₃ density | agree to `10⁻³¹` |

## Stress example: the window needs the close wall

`check_far_wall.py`, at the reactor-like value `s = 0.16107` with the window's fields
(`B_θ² = s`, `B_e² = 1 − 3s/4`), varying only the wall position `h = b/a`:

| `b/a` | `min_{m ≥ 1} F_mn` | at `(m, k)` |
| --- | --- | --- |
| 1.0101 (= 1 + s/16) | +0.0127 | (1, −0.42) |
| 1.05 | +0.0049 | (1, −0.40) |
| 1.10 | −0.0033 | (1, −0.38) |
| 1.20 | −0.0160 | (1, −0.36) |
| 2 | −0.0576 | (1, −0.26) |
| ∞ | −0.0789 | (1, −0.20) |

The same equilibrium is ideal-unstable (an `m = 1` external-kink-like mode) once the wall is more
than about 5–10% of the minor radius away. The source states the close-wall hypothesis
explicitly, so this is no error. It does quantify the hypothesis: for a reactor reading, the
result is a wall-stabilised benchmark, and the wall must almost touch the plasma.

## Sanity examples for the corrected flux (S-25)

- Exact symmetry (Killing `u`): `S = 0`, so `C = D = 0` and `J = ψ − εu·v` is conserved. This is
  the compiled `canonicalMomentum_conserved` / `noetherMomentum_conserved`, up to the sign
  convention (`WeakQS`: `B × ξ = −∇ψ`; the source: `B × u = ∇ψ`).
- Without exact weak QS, `bᵀSb ≠ 0`, and the `bb` block of `S` is not in the range of
  `C ↦ [C,K]`, whose image has zero `bb` component. A secular parallel term remains. This is the
  term a QS-defect version must bound (N-29, N-34).
