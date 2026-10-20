"""UNTRUSTED.  Exact-arithmetic refinement of torus A (K2').

Starting from the double-precision Galerkin solution (flow_torus.py), iterate
    x <- x - J0^{-1} F_exact(x)
where F_exact is the Galerkin projection of the *exact* residual of the dyadic torus (computed
with big integers by exact.py) and J0 the double-precision Jacobian.  Each step gains ~13 digits
until the dyadic rounding 2^-P / truncation floor is reached.

Writes /tmp/k2work/torusA_P{P}_N{N}_M{M}.npz with the integer data and prints:
residual l1 norms (= sup bounds), coefficient decay, and the size of the iota_q error term.
"""
import os
import sys
import time

import numpy as np
from mpmath import mp, mpf, sqrt as msqrt

sys.path.insert(0, os.path.dirname(__file__))
from flow_torus import Galerkin, index_sets, resize, newton_double  # noqa: E402
from exact import Kron, residual_packed  # noqa: E402

mp.dps = 80
IOTA = (75 + msqrt(5)) / 562


def galerkin_exact(K, Rsh, Rzh, Is, Iz, P, Q):
    """Galerkin vector (sine coeffs of Rs on Iz, cosine coeffs of Rz on Is) as floats."""
    N, M = K.N, K.M
    rs = K.unpack(Rsh)
    rz = K.unpack(Rzh)
    sc = 6 * (P + 1)
    Fs = [-rs.get((6 * N + k, 6 * M + 1 + m), 0) / 2.0 ** (Q + 3 + sc) for k, m in Iz]
    Fz = [(1 if (k, m) == (0, 0) else 2) * rz.get((6 * N + k, 6 * M + 1 + m), 0) / 2.0 ** (Q + 5 + sc)
          for k, m in Is]
    return np.array(Fs + Fz), rs, rz


def l1(d):
    return sum(abs(c) for c in d.values())


def run(N, M, P, Q, a, b, iters=4, bbits=None):
    Is, Iz = index_sets(N, M)
    Iq = int(mp.nint(IOTA * mpf(2) ** Q))
    g = Galerkin(N, M, Iq / 2.0 ** Q)
    J0 = g.J(a, b)
    A = [int(round(x * 2.0 ** 52)) << (P - 52) if P > 52 else int(round(x * 2 ** P)) for x in a]
    B = [int(round(x * 2.0 ** 52)) << (P - 52) if P > 52 else int(round(x * 2 ** P)) for x in b]
    bbits = bbits or (Q + 6 * (P + 1) + 40 + 7) // 8 * 8
    K = Kron(N, M, bbits)
    na = len(A)
    for it in range(iters + 1):
        t0 = time.time()
        Rsh, Rzh, Dh, _, _ = residual_packed(K, A, B, Is, Iz, P, Q, Iq)
        F, rs, rz = galerkin_exact(K, Rsh, Rzh, Is, Iz, P, Q)
        sc = 2.0 ** (6 * (P + 1))
        Es = l1(rs) / (2.0 ** (Q + 4) * sc)
        Ez = l1(rz) / (2.0 ** (Q + 5) * sc)
        print(f"  exact step {it}: |F_galerkin|_inf = {abs(F).max():.3e}   l1(Rs) = {Es:.3e}  l1(Rz) = {Ez:.3e}"
              f"   ({time.time()-t0:.1f}s)", flush=True)
        if it == iters:
            break
        d = np.linalg.solve(J0, -F)
        A = [x + int(round(y * 2.0 ** P)) for x, y in zip(A, d[:na])]
        B = [x + int(round(y * 2.0 ** P)) for x, y in zip(B, d[na:])]
    return A, B, Iq, rs, rz, Dh, K, Es, Ez


def decay(A, B, Is, Iz, P):
    byk, bym = {}, {}
    for (k, m), c in list(zip(Is, A)) + list(zip(Iz, B)):
        v = abs(c) / 2.0 ** P
        byk[k] = max(byk.get(k, 0), v)
        bym[abs(m)] = max(bym.get(abs(m), 0), v)
    return byk, bym


if __name__ == '__main__':
    N, M, P, Q = [int(x) for x in sys.argv[1:5]] if len(sys.argv) > 4 else (28, 18, 80, 128)
    d = np.load('/tmp/k2work/double_A.npz')
    a, b = resize(d['a'], d['b'], int(d['N']), int(d['M']), N, M)
    g = Galerkin(N, M, float(IOTA))
    a, b = newton_double(g, a, b, verbose=False)
    A, B, Iq, rs, rz, Dh, K, Es, Ez = run(N, M, P, Q, a, b)
    byk, bym = decay(A, B, *index_sets(N, M), P)
    print("max |coeff| by k:", ' '.join(f"{k}:{byk[k]:.1e}" for k in sorted(byk) if k % 4 == 0 or k == N))
    print("max |coeff| by |m|:", ' '.join(f"{m}:{bym[m]:.1e}" for m in sorted(bym) if m % 2 == 0 or m == M))
    # fit decay rates (log-linear on the tail)
    ks = np.array(sorted(byk)); vk = np.array([byk[k] for k in ks])
    ms = np.array(sorted(bym)); vm = np.array([bym[m] for m in ms])
    sel = (ks >= 4) & (ks <= N - 4)
    rk = -np.polyfit(ks[sel], np.log(vk[sel]), 1)[0]
    sel = (ms >= 2) & (ms <= M - 2)
    rm = -np.polyfit(ms[sel], np.log(vm[sel]), 1)[0]
    print(f"decay rates: theta {rk:.3f}/mode (strip width {rk:.3f} rad = {rk/(2*np.pi):.3f} turns); "
          f"psi {rm:.3f}/mode (phi-strip {rm/2:.3f} rad)")
    err_iota = abs(IOTA - mpf(Iq) / mpf(2) ** Q)
    print(f"Iq = {Iq}, |iota - Iq/2^Q| = {mp.nstr(err_iota, 5)}")
    np.savez(f'/tmp/k2work/torusA_P{P}_N{N}_M{M}.npz', A=np.array([str(x) for x in A]),
             B=np.array([str(x) for x in B]), N=N, M=M, P=P, Q=Q, Iq=str(Iq), Es=Es, Ez=Ez)
