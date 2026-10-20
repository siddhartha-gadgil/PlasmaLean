"""UNTRUSTED.  Emit PlasmaLean/Design/KamTorusAData.lean from the refined torus and predict the
kernel computations of PlasmaLean/Design/KamTorusA.lean (exact mirror in Python big integers).

Grid convention (Lean `cA i j`, `cB i j`, i in [0, 2N], j in [0, 2M]): coefficient of
cos/sin((i - N) theta + (j - M) psi) times 2^P; nonzero only for (i - N, j - M) in Is resp. Iz.
Storage: half grid i in [N, 2N], j in [0, 2M], field index (i - N)(2M + 1) + j, 96-bit fields,
value + 2^95.
"""
import sys

import numpy as np
from fractions import Fraction
from gmpy2 import mpz

FW = 96


def load(path):
    d = np.load(path)
    N, M, P, Q = int(d['N']), int(d['M']), int(d['P']), int(d['Q'])
    A = [int(x) for x in d['A']]
    B = [int(x) for x in d['B']]
    return N, M, P, Q, int(str(d['Iq'])), A, B


def grids(N, M, A, B):
    from flow_torus import index_sets
    Is, Iz = index_sets(N, M)
    I, J = 2 * N + 1, 2 * M + 1
    cA = [[0] * J for _ in range(I)]
    cB = [[0] * J for _ in range(I)]
    for (k, m), c in zip(Is, A):
        cA[N + k][M + m] = c
    for (k, m), c in zip(Iz, B):
        cB[N + k][M + m] = c
    return cA, cB


def pack_fields(c, N, M):
    J = 2 * M + 1
    val = 0
    for i in range(N, 2 * N + 1):
        for j in range(J):
            f = (i - N) * J + j
            x = c[i][j] + (1 << (FW - 1))
            assert 0 <= x < (1 << FW)
            val |= x << (FW * f)
    return val


def decode(val, i, j, N, M):
    J = 2 * M + 1
    if i < N:
        return 0
    f = (i - N) * J + j
    return ((val >> (FW * f)) % (1 << FW)) - (1 << (FW - 1))


# ---- mirror of the Lean kernel computations ----

def pack_grid(g, I, J, b, W):
    tot = mpz(0)
    for j in range(J):
        row = mpz(0)
        for i in range(I):
            row += mpz(g(i, j)) << (b * i)
        tot += row << (b * W * j)
    return tot


def l1kron(b, d, Nv):
    H = 1 << (b - 1)
    off = mpz(H)
    for k in range(d):     # doubling, as in Lean `offs`
        off = off + (off << (b << k))
    T = int(Nv + off)
    assert T >= 0
    s = 0
    X = 1 << b
    bs = T.to_bytes((T.bit_length() + 7) // 8 + 1, 'little')
    assert b % 8 == 0
    B = b // 8
    nd = 2 ** d
    for n in range(nd):
        e = int.from_bytes(bs[n * B:(n + 1) * B], 'little')
        s += abs(e - H)
    assert (T >> (b * nd)) == 0, "overflow beyond 2^d slots"
    return s


def forms(Rh, Zh, Rth, Rps, Zth, Zps, t, v, Ch, Sv, Q, Iq):
    Q2 = mpz(2) ** Q
    E = Rh ** 2 - t ** 2
    F = Rh ** 2 - 5 * t ** 2
    T4 = 4 * (t ** 2 * Zh ** 2)
    D = 16 * (t ** 3 * v * Rh ** 2) - t * (E ** 2 + T4) * Ch - Zh * (E * F + T4) * Sv
    PR = t * (Rh ** 4 - t ** 4 - T4) * Sv + Zh * (Rh ** 4 - 5 * t ** 4 - T4) * Ch
    PZ = 8 * (t ** 3 * Zh * Sv) + (E * F + 12 * (t ** 2 * Zh ** 2)) * Ch
    LR = 2 * Q2 * Rps + Iq * Rth
    LZ = 2 * Q2 * Zps + Iq * Zth
    RR = D * LR - Q2 * (Rh * PR)
    RZ = 2 * (D * LZ) + Q2 * (Rh ** 2 * PZ)
    return D, RR, RZ


def bounds(LR, LZ, LRth, LRps, LZth, LZps, Lt, Q, Iq):
    Db = 16 * (Lt ** 3 * 1 * LR ** 2) + Lt * ((LR ** 2 + Lt ** 2) ** 2 + 4 * (Lt ** 2 * LZ ** 2)) * 2 \
        + LZ * ((LR ** 2 + Lt ** 2) * (LR ** 2 + 5 * Lt ** 2) + 4 * (Lt ** 2 * LZ ** 2)) * 2
    PRb = Lt * (LR ** 4 + Lt ** 4 + 4 * (Lt ** 2 * LZ ** 2)) * 2 + LZ * (LR ** 4 + 5 * Lt ** 4 + 4 * (Lt ** 2 * LZ ** 2)) * 2
    PZb = 8 * (Lt ** 3 * LZ * 2) + ((LR ** 2 + Lt ** 2) * (LR ** 2 + 5 * Lt ** 2) + 12 * (Lt ** 2 * LZ ** 2)) * 2
    RRb = Db * (2 ** (Q + 1) * LRps + Iq * LRth) + 2 ** Q * (LR * PRb)
    RZb = 2 * (Db * (2 ** (Q + 1) * LZps + Iq * LZth)) + 2 ** Q * (LR ** 2 * PZb)
    return Db, RRb, RZb


def main(path, out):
    N, M, P, Q, Iq, A, B = load(path)
    cA, cB = grids(N, M, A, B)
    dA, dB = pack_fields(cA, N, M), pack_fields(cB, N, M)
    I, J = 2 * N + 1, 2 * M + 1
    for i in range(I):
        for j in range(J):
            assert decode(dA, i, j, N, M) == cA[i][j] and decode(dB, i, j, N, M) == cB[i][j]
    gR = lambda i, j: cA[i][j] + cA[2 * N - i][2 * M - j]
    gZ = lambda i, j: cB[i][j] - cB[2 * N - i][2 * M - j]
    grid_fns = {
        'Rh': gR, 'Zh': gZ,
        'Rth': lambda i, j: (i - N) * gR(i, j), 'Rps': lambda i, j: (j - M) * gR(i, j),
        'Zth': lambda i, j: (i - N) * gZ(i, j), 'Zps': lambda i, j: (j - M) * gZ(i, j)}
    L1 = {k: sum(abs(f(i, j)) for i in range(I) for j in range(J)) for k, f in grid_fns.items()}
    sigma = 1 << (P + 1)
    Lt = sigma
    Db, RRb, RZb = bounds(L1['Rh'], L1['Zh'], L1['Rth'], L1['Rps'], L1['Zth'], L1['Zps'], Lt, Q, Iq)
    print("a priori bit sizes: D", Db.bit_length(), " RR", RRb.bit_length(), " RZ", RZb.bit_length())
    b = ((max(RRb, RZb).bit_length() + 2) + 7) // 8 * 8
    W = 12 * N + 1
    rows = 12 * M + 3
    d = (W * rows - 1).bit_length()
    print(f"Kronecker: b = {b}, W = {W}, rows = {rows}, slots = {W*rows}, d = {d} (2^d = {2**d})")
    vals = {k: pack_grid(f, I, J, b, W) for k, f in grid_fns.items()}
    X = 1 << b
    t = mpz(sigma) << (b * (N + W * M))
    v = mpz(1) << (b * W)
    Ch = (mpz(1) << (2 * b * W)) + 1
    Sv = (mpz(1) << (2 * b * W)) - 1
    D, RR, RZ = forms(vals['Rh'], vals['Zh'], vals['Rth'], vals['Rps'], vals['Zth'], vals['Zps'], t, v, Ch, Sv, Q, Iq)
    lRR = l1kron(b, d, RR)
    lRZ = l1kron(b, d, RZ)
    kR = Fraction(1, 2 ** (Q + 4) * sigma ** 6)
    kZ = Fraction(1, 2 ** (Q + 5) * sigma ** 6)
    print(f"l1(RRh)/(2^(Q+4) sigma^6) = {float(lRR * kR):.4e};  l1(RZh)/(2^(Q+5) sigma^6) = {float(lRZ * kZ):.4e}")
    # D lower bound: centre (5N, 5M+1), kappa = 16 sigma^5
    n0 = 5 * N + W * (5 * M + 1)
    c0D = ((D + (X >> 1) * 0) >> 0)  # placeholder
    # centre coefficient via balanced digits
    def digit(Nv, n):
        H = mpz(X >> 1)
        Xn = mpz(1) << (b * n)
        lo = Nv % Xn
        if lo >= Xn // 2:
            lo -= Xn
        q = (Nv - lo) >> (b * n)
        c = q % X
        if c >= H:
            c -= X
        return int(c)
    c0D = digit(D, n0)
    lD = l1kron(b, d, D - (mpz(c0D) << (b * n0)))
    Dmin = Fraction(c0D - lD, 16 * sigma ** 5)
    print(f"D lower bound: (c0 - l1(D - c0 mono))/(16 sigma^5) = {float(Dmin):.6f}  (c0/(16 sigma^5) = {c0D/(16*sigma**5):.6f})")
    # graph quantities (degree 2), smaller Kronecker
    W2 = 4 * N + 1
    rows2 = 4 * M + 3
    d2 = (W2 * rows2 - 1).bit_length()
    L2b = max((L1['Rh'] + Lt) ** 2 + L1['Zh'] ** 2, (L1['Rh'] + Lt) * L1['Zth'] + L1['Zh'] * L1['Rth'],
              L1['Zth'] ** 2 + L1['Rth'] ** 2)
    b2 = ((L2b.bit_length() + 2) + 7) // 8 * 8
    vals2 = {k: pack_grid(f, I, J, b2, W2) for k, f in grid_fns.items()}
    X2 = 1 << b2
    t2 = mpz(sigma) << (b2 * (N + W2 * M))
    Nf = (vals2['Rh'] - t2) * vals2['Zth'] - vals2['Zh'] * vals2['Rth']
    rt2f = (vals2['Rh'] - t2) ** 2 - vals2['Zh'] ** 2
    dK2f = vals2['Zth'] ** 2 - vals2['Rth'] ** 2
    n2 = 2 * N + W2 * (2 * M)
    X = X2

    def digit2(Nv, n):
        H = mpz(X2 >> 1)
        Xn = mpz(1) << (b2 * n)
        lo = Nv % Xn
        if lo >= Xn // 2:
            lo -= Xn
        q = (Nv - lo) >> (b2 * n)
        c = q % X2
        if c >= H:
            c -= X2
        return int(c)
    c0N = digit2(Nf, n2)
    lN = l1kron(b2, d2, Nf - (mpz(c0N) << (b2 * n2)))
    Nmin = Fraction(c0N - lN, sigma ** 2)
    lrt = l1kron(b2, d2, rt2f)
    ldK = l1kron(b2, d2, dK2f)
    print(f"graph: b2 = {b2}, W2 = {W2}, d2 = {d2}; N_min = {float(Nmin):.5f}; rt^2 <= {lrt/sigma**2:.5f} "
          f"(rt <= {np.sqrt(lrt/sigma**2):.4f}); |d_theta K|^2 <= {ldK/sigma**2:.5f}; "
          f"rho_min = N_min/|dK| >= {float(Nmin)/np.sqrt(ldK/sigma**2):.4f}")
    res = dict(N=N, M=M, P=P, Q=Q, Iq=Iq, b=b, W=W, d=d, lRR=lRR, lRZ=lRZ, c0D=c0D, lD=lD, b2=b2, W2=W2, d2=d2,
               c0N=c0N, lN=lN, lrt=lrt, ldK=ldK, L1=L1, RRb=RRb, RZb=RZb, Db=Db)
    with open(out, 'w') as f:
        f.write(DATA_TEMPLATE.format(N=N, M=M, P=P, Q=Q, Iq=Iq, hexA=hex(dA), hexB=hex(dB)))
    return res


DATA_TEMPLATE = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Data of the approximate invariant torus A (KAM route, stage K2)

Exact dyadic Fourier coefficients of the flow-form torus A of the rational stellarator
(`notes/theory/kam-route.md` §4, `ι = [0;7,3,1,1,…] = (75 + √5)/562`), produced by the untrusted
oracle `scripts/kam_oracle/` (exact-arithmetic Newton refinement, `refine.py` then
`emit_lean.py`). Nothing here is trusted: the data only *define* the torus, and every property is
proved in `Design/KamTorusA`.

Truncation `|k| ≤ N = {N}`, `|m| ≤ M = {M}` (poloidal mode `k`, mode `m` in `ψ = 2φ − π/2`), scale
`2^P`, `P = {P}`. The coefficient of `cos((i − N)θ + (j − M)ψ)` in `R(θ, φ)` is `cA i j / 2^P` and
that of `sin(…)` in `z(θ, φ)` is `cB i j / 2^P`. They are stored for `i ∈ [N, 2N]`,
`j ∈ [0, 2M]` as 96-bit fields (value `+ 2^95`) of one natural-number literal each.
-/

@[expose] public section

namespace PlasmaLean.Design.KamTorusA

/-- Poloidal truncation `N`. -/
def N : ℕ := {N}
/-- Toroidal truncation `M` (modes `e^{{imψ}}`, `ψ = 2φ − π/2`). -/
def M : ℕ := {M}
/-- Coefficient scale exponent: coefficients are integers over `2^P`. -/
def P : ℕ := {P}
/-- Exponent of the dyadic approximation `ι_q = Iq / 2^Q` of the rotational transform. -/
def Q : ℕ := {Q}
/-- Numerator of `ι_q = Iq / 2^Q ≈ (75 + √5)/562`. -/
def Iq : ℕ := {Iq}

set_option linter.style.longLine false in
/-- Packed coefficients of `R` (96-bit fields, offset `2^95`). -/
def dataA : ℕ := {hexA}

set_option linter.style.longLine false in
/-- Packed coefficients of `z` (96-bit fields, offset `2^95`). -/
def dataB : ℕ := {hexB}

/-- Decode field `f` of a packed literal (96-bit fields, offset `2^95`). -/
def field96 (data f : ℕ) : ℤ := (((data >>> (96 * f)) % 2 ^ 96 : ℕ) : ℤ) - 2 ^ 95

/-- Grid coefficient: field `(i − N)(2M + 1) + j` for `i ≥ N`, zero for `i < N`. -/
def gridCoeff (data i j : ℕ) : ℤ := if N ≤ i then field96 data ((i - N) * (2 * M + 1) + j) else 0

/-- `2^P ×` the coefficient of `cos((i − N)θ + (j − M)ψ)` in `R`. -/
def cA (i j : ℕ) : ℤ := gridCoeff dataA i j

/-- `2^P ×` the coefficient of `sin((i − N)θ + (j − M)ψ)` in `z`. -/
def cB (i j : ℕ) : ℤ := gridCoeff dataB i j

end PlasmaLean.Design.KamTorusA
'''

if __name__ == '__main__':
    sys.path.insert(0, __file__.rsplit('/', 1)[0])
    path = sys.argv[1] if len(sys.argv) > 1 else '/tmp/k2work/torusA_P90_N32_M22.npz'
    out = sys.argv[2] if len(sys.argv) > 2 else '/tmp/k2work/KamTorusAData.lean'
    r = main(path, out)
    import json
    json.dump({k: (v if not isinstance(v, int) else str(v)) for k, v in r.items() if k != 'L1'} | {'L1': {k: str(v) for k, v in r['L1'].items()}},
              open('/tmp/k2work/predict.json', 'w'), indent=1)
