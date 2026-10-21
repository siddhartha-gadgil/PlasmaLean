"""UNTRUSTED oracle (v_par < 0 instance): the iota_B = (161 - sqrt 5)/1178 torus of gcField(-1/256) in the
flow form, continued in the Fourier truncation from the N = 32, M = 22 solution of the robust-confinement
scan (/tmp/laneA9/tB_-1_256.npz) to N = 40, M = 30 (the box of the high-resolution certificate).
Usage: python neg_torus.py   (writes /tmp/k2work/gcneg_torus_-1_256.npz)"""
import sys, os, time
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
from flow_torus import resize
from gc_torus import GalerkinGC, newton, grid_residual, strip_norm

IOTA = (161 - 5 ** 0.5) / 1178
RHO = -1 / 256
d = np.load('/tmp/laneA9/tB_-1_256.npz')
a, b, N, M = d['a'], d['b'], 32, 22
t0 = time.time()
for N2, M2 in [(36, 26), (40, 30)]:
    a, b = resize(a, b, N, M, N2, M2)
    N, M = N2, M2
    g = GalerkinGC(N, M, IOTA, RHO)
    a, b, e = newton(g, a, b, verbose=True)
    print('N=%d M=%d |F| = %.2e (%.0fs)' % (N, M, e, time.time() - t0), flush=True)
r1, r2, R, zz = grid_residual(a, b, N, M, IOTA, RHO)
print('grid residual', r1, r2)
print('R range', R.min(), R.max(), ' z range', zz.min(), zz.max())
for rs in [0.1, 0.1257]:
    print('strip %.4f: |u|, |z| = %s' % (rs, strip_norm(a, b, N, M, rs)))
np.savez('/tmp/k2work/gcneg_torus_-1_256.npz', a=a, b=b, N=N, M=M, rho=RHO)
