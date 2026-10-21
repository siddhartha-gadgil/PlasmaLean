"""UNTRUSTED.  Weighted l1 norms of the flow-form residual of the refitted coil tori.

For each /tmp/ckwork/coil_torus_N{N}_M{M}.npz: the residual E = (E_R, E_z) on a fine grid, its 2-D
FFT, and sum |E_km| e^{r_t |k| + r_p |m|} for isotropic and anisotropic strip pairs (r_t, r_p).
Also the sup of the residual (double precision floor ~1e-13).
"""
import glob
import sys

import numpy as np

from refit import Galerkin


def load(path):
    d = np.load(path)
    g = Galerkin(int(d['N']), int(d['M']))
    x = g.pack(d['a'], d['ap'], d['b'], d['bp'])
    return g, x


def norms(path, strips):
    g, x = load(path)
    Nt, Np = 4 * g.N + 16, 4 * g.M + 16
    h = Galerkin(g.N, g.M, Nt=Nt, Np=Np)
    ER, EZ = h.residual(x)
    out = {}
    for name, E in (('R', ER), ('z', EZ)):
        F = np.fft.fft2(E.reshape(Nt, Np)) / (Nt * Np)
        k = np.fft.fftfreq(Nt, 1 / Nt)[:, None]
        m = np.fft.fftfreq(Np, 1 / Np)[None, :]
        out[name] = {'sup': float(abs(E).max())}
        for rt, rp in strips:
            out[name][(rt, rp)] = float((abs(F) * np.exp(rt * abs(k) + rp * abs(m))).sum())
    return g, out


if __name__ == '__main__':
    strips = [(0.0, 0.0), (0.02, 0.02), (0.063, 0.063), (0.1257, 0.063), (0.12, 0.12)]
    files = sorted(glob.glob('/tmp/ckwork/coil_torus_N*_M*.npz')) if len(sys.argv) < 2 else sys.argv[1:]
    for f in files:
        g, out = norms(f, strips)
        print(f"N={g.N} M={g.M}")
        for name in 'Rz':
            o = out[name]
            print(f"  E_{name}: sup {o['sup']:.3e}  " +
                  "  ".join(f"l1{s}={o[s]:.3e}" for s in strips))
