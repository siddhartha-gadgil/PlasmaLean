# Checks of the closed-form equilibria of arXiv:2611.07672

Untrusted numerics for note N-43 (`notes/theory/issan-arbitrary-field-periods.md`), source
`sources/Non-AxisymmetricMHD.pdf`. Nothing here is a proof and nothing is emitted to Lean.

```bash
scripts/setup.sh --python --no-build        # once: creates .venv-ws
.venv-ws/bin/python -I scripts/issan_equilibria/check_equilibria.py [--points K] [--seed S]
cd scripts/issan_equilibria && ../../.venv-ws/bin/python check_iota.py [--n 12000]
```

- `check_equilibria.py`: the formulas (3)-(8) of the paper, exact derivatives (sympy), residuals
  at random points with 40 digits (mpmath): the Cartesian equilibrium equations, the Jacobian
  formula, the axis condition, the covariant form for Family 1 with `rho_a = rho_0`, the
  interchange-instability identities, the axis radius. Exit status 0 if every residual is below
  `1e-25`. About 5 minutes.
- `check_iota.py`: Gauss linking number of a field line with the magnetic axis (the rotational
  transform, `0` or `+-N`) and the variation of `|B|` along the axis. Double precision. About
  2 minutes and 1 GB.
