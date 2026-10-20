"""UNTRUSTED.  Weighted (complex-strip) l1 norms of the exact residual of torus A, for K3 planning.

The residual R = RRh / (2^(Q+4) sigma^6 t-phase) is an exact trigonometric polynomial; its Fourier
coefficients are the balanced Kronecker digits of RRint (same computation as the Lean kernel check).
For a strip |Im theta| <= 2 pi rho, |Im phi| <= pi rho (angles normalised to turns), the analytic
norm is bounded by the weighted l1 norm  sum |r_km| e^{2 pi rho (|k| + |m|)}.
Prints, for several rho, ||E||_rho for both components and the FHL-type ratio
||E||_rho / (gamma^4 rho^4) with gamma = 0.069 (period map, tau = 1).
"""
import json
import math
import os
import sys

from gmpy2 import mpz

sys.path.insert(0, os.path.dirname(__file__))
from emit_lean import load, grids, pack_grid, forms  # noqa: E402


def main(path='/tmp/k2work/torusA_P90_N32_M22.npz'):
    N, M, P, Q, Iq, A, B = load(path)
    cA, cB = grids(N, M, A, B)
    I, J = 2 * N + 1, 2 * M + 1
    gR = lambda i, j: cA[i][j] + cA[2 * N - i][2 * M - j]
    gZ = lambda i, j: cB[i][j] - cB[2 * N - i][2 * M - j]
    fns = {'Rh': gR, 'Zh': gZ, 'Rth': lambda i, j: (i - N) * gR(i, j), 'Rps': lambda i, j: (j - M) * gR(i, j),
           'Zth': lambda i, j: (i - N) * gZ(i, j), 'Zps': lambda i, j: (j - M) * gZ(i, j)}
    b, W = 656, 12 * N + 1
    vals = {k: pack_grid(f, I, J, b, W) for k, f in fns.items()}
    sigma = 1 << (P + 1)
    t = mpz(sigma) << (b * (N + W * M))
    v = mpz(1) << (b * W)
    Ch = (mpz(1) << (2 * b * W)) + 1
    Sv = (mpz(1) << (2 * b * W)) - 1
    D, RR, RZ = forms(vals['Rh'], vals['Zh'], vals['Rth'], vals['Rps'], vals['Zth'], vals['Zps'], t, v, Ch, Sv, Q, Iq)
    rows = 12 * M + 3
    H = 1 << (b - 1)
    nb = b // 8

    def digits(Nv):
        off = int.from_bytes(H.to_bytes(nb, 'little') * (W * rows), 'little')
        T = int(Nv + off)
        bs = T.to_bytes(W * rows * nb + 1, 'little')
        out = []
        for n in range(W * rows):
            c = int.from_bytes(bs[n * nb:(n + 1) * nb], 'little') - H
            if c:
                out.append((n % W - 6 * N, n // W - (6 * M + 1), c))
        return out
    dR, dZ = digits(RR), digits(RZ)
    kR = 2.0 ** -(Q + 4) / float(sigma) ** 6
    kZ = 2.0 ** -(Q + 5) / float(sigma) ** 6
    gamma = 0.069
    res = []
    print(" rho(turns)   ||E_R||_rho    ||E_z||_rho    max/(gamma^4 rho^4)")
    for rho in [0.0, 0.005, 0.01, 0.02, 0.03, 0.05, 0.075, 0.1]:
        w = lambda k, m: math.exp(2 * math.pi * rho * (abs(k) + abs(m)))
        eR = sum(abs(c) * kR * w(k, m) for k, m, c in dR)
        eZ = sum(abs(c) * kZ * w(k, m) for k, m, c in dZ)
        ratio = max(eR, eZ) / (gamma ** 4 * rho ** 4) if rho > 0 else float('nan')
        print(f"  {rho:6.3f}    {eR:12.3e}   {eZ:12.3e}   {ratio:12.3e}")
        res.append(dict(rho=rho, ER=eR, EZ=eZ, ratio=ratio))
    # mode support of the residual
    kmax = max(abs(k) for k, m, c in dR)
    mmax = max(abs(m) for k, m, c in dR)
    print(f"residual modes: |k| <= {kmax}, |m| <= {mmax}; {len(dR)} nonzero R-coefficients, {len(dZ)} z-coefficients")
    json.dump(res, open('/tmp/k2work/strip_norms.json', 'w'), indent=1)


if __name__ == '__main__':
    main(*sys.argv[1:])
