"""UNTRUSTED.  Initial guess for the flow torus A (double precision).

1. Find the launch radius r on the symmetric half-plane phi = pi/4, z = 0, R = 1 + r (outboard)
   whose rotational transform is iota_A = [0;7,3,1,1,...] = (75 + sqrt 5)/562  (bisection on
   weighted-Birkhoff iota, as in notes/theory/kam-route.md section 4).
2. Weighted-Birkhoff Fourier coefficients of the invariant curve of the period map (period pi).
3. Flow the curve to a grid of phi' = phi - pi/4 values: K(theta, phi') = Phi_{phi'}(k(theta - iota phi')),
   theta in radians; FFT of (s = R^2, z) gives the 2-D coefficients.

Output: /tmp/k2work/init_A.npz  (complex 2-D FFT arrays of s and z on an Nt x Np grid).
"""
import os
import sys
import time

import numpy as np
from mpmath import mp, sqrt as msqrt
from scipy.integrate import solve_ivp

sys.path.insert(0, os.path.dirname(__file__))
from field import rhs_phi  # noqa: E402

mp.dps = 50
IOTA = float((75 + msqrt(5)) / 562)
PHI0 = np.pi / 4


def rhs(t, y):
    n = y.size // 2
    a, b = rhs_phi(t, y[:n], y[n:])
    return np.concatenate([a, b])


def orbits(R0, z0, nper):
    n = R0.size
    sol = solve_ivp(rhs, (PHI0, PHI0 + nper * np.pi), np.concatenate([R0, z0]), method='DOP853',
                    rtol=1e-13, atol=1e-15, t_eval=PHI0 + np.pi * np.arange(nper + 1))
    return sol.y[:n], sol.y[n:]


def wba_weights(N):
    t = np.arange(1, N + 1) / (N + 1)
    w = np.exp(-1 / (t * (1 - t)))
    return w / w.sum()


def iota_of(Ro, zo):
    th = np.unwrap(np.arctan2(zo, Ro - 1), axis=1)
    d = np.diff(th, axis=1)
    w = wba_weights(d.shape[1])
    return (d * w).sum(1) / np.pi   # per full turn (2 periods)


def find_r(lo, hi, nper=1500):
    for _ in range(5):
        rs = np.linspace(lo, hi, 9)
        Ro, zo = orbits(1 + rs, 0 * rs, nper)
        io = iota_of(Ro, zo)
        i = np.searchsorted(io, IOTA)
        lo, hi = rs[max(i - 1, 0)], rs[min(i, 8)]
    return 0.5 * (lo + hi)


def main():
    os.makedirs('/tmp/k2work', exist_ok=True)
    t0 = time.time()
    r = find_r(0.16, 0.22)
    print(f"iota_A = {IOTA:.15f}, launch r = {r:.10f} ({time.time()-t0:.0f}s)", flush=True)
    nper = 8000
    Ro, zo = orbits(np.array([1 + r]), np.array([0.0]), nper)
    Ro, zo = Ro[0], zo[0]
    om = IOTA / 2 * 2 * np.pi      # rotation per period (pi) in radians of theta
    Nf = 40
    w = wba_weights(nper + 1)
    th = om * np.arange(nper + 1)
    k = np.arange(-Nf, Nf + 1)
    E = np.exp(-1j * np.outer(th, k))
    cR = (w[:, None] * E * Ro[:, None]).sum(0)
    cz = (w[:, None] * E * zo[:, None]).sum(0)
    print("map-curve |c_k| at k=1,8,16,24,32:", [f"{abs(cR[Nf+j])+abs(cz[Nf+j]):.1e}" for j in (1, 8, 16, 24, 32)])
    Nt, Np = 96, 64
    thg = 2 * np.pi * np.arange(Nt) / Nt
    phg = np.pi * np.arange(Np) / Np
    S = np.zeros((Nt, Np))
    Z = np.zeros((Nt, Np))
    for j, p in enumerate(phg):
        tt = thg - IOTA * p
        Ek = np.exp(1j * np.outer(tt, k))
        R0 = np.real(Ek @ cR)
        z0 = np.real(Ek @ cz)
        if j == 0:
            Rj, zj = R0, z0
        else:
            sol = solve_ivp(rhs, (PHI0, PHI0 + p), np.concatenate([R0, z0]), method='DOP853',
                            rtol=1e-13, atol=1e-15)
            Rj, zj = sol.y[:Nt, -1], sol.y[Nt:, -1]
        S[:, j] = Rj ** 2
        Z[:, j] = zj
    FS = np.fft.fft2(S) / S.size
    FZ = np.fft.fft2(Z) / Z.size
    np.savez('/tmp/k2work/init_A.npz', FS=FS, FZ=FZ, r=r, iota=IOTA)
    print(f"saved init (Nt={Nt}, Np={Np}); max|imag part sym check| done in {time.time()-t0:.0f}s")


if __name__ == '__main__':
    main()
