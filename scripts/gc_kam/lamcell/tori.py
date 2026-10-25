"""UNTRUSTED oracle (pitch cell [LAM_LO, LAM_HI], see lc.py): invariant tori of the mu > 0 passing
guiding-centre field at the Chebyshev nodes of the cell, by scripts/gc_kam/lam_tori.py with the node
`lam = LAM_LO + (LAM_HI - LAM_LO)(1 + x)/2` and, as initial guess, the certified family torus of
Design/RationalStellaratorGCMuDataH* (cell [0, 1/16]) at its end point lam = 1/16.

Usage: python tori.py init            (writes $LAM_WORK/init.npz)
       python tori.py NT MT n k       (torus at node k of n; writes $LAM_WORK/tori/t_NT_MT_n_k.npz)
       python tori.py cheb NT MT n    (Chebyshev coefficients; writes $LAM_WORK/cheb.npz)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc
from fractions import Fraction as Fr

lc.setup_path()
TORI = os.path.join(lc.WORK, 'tori')
os.makedirs(TORI, exist_ok=True)
os.environ['LAM_TORI_DIR'] = TORI
INIT = os.path.join(lc.WORK, 'init.npz')


def make_init():
    import numpy as np
    from fam_ball import decode_slice
    from flow_torus import index_sets
    D = lc.read_slices(['RationalStellaratorGCMuDataH%d' % k for k in range(1, 7)])
    N, M, S = 36, 27, 107
    NT, MT = 28, 20
    Is, Iz = index_sets(NT, MT)
    a = [Fr(0)] * len(Is)
    b = [Fr(0)] * len(Iz)
    # the Chebyshev series of the certified cell at x' = 1 (lam = 1/16): sum of all coefficients
    for jw, (su, sz) in enumerate(zip(D['sdHM_U'], D['sdHM_Z'])):
        fac = Fr(1) if jw == 0 else Fr(1, 2)
        gu = decode_slice(su, N, M, 1)
        gz = decode_slice(sz, N, M, -1)
        for i, (k, m) in enumerate(Is):
            if (k, m) == (0, 0):
                a[i] += Fr(gu[N][M], 2 ** S) / fac + (1 if jw == 0 else 0)
            else:
                a[i] += Fr(gu[N + k][M + m], 2 ** (S - 1)) / fac
        for i, (k, m) in enumerate(Iz):
            b[i] += Fr(gz[N + k][M + m], 2 ** (S - 1)) / fac
    np.savez(INIT, a=np.array([str(x) for x in a]), b=np.array([str(x) for x in b]), NT=NT, MT=MT)
    print('init: a00 = %.12f' % float(a[0]))


if sys.argv[1] == 'init':
    make_init()
elif sys.argv[1] == 'cheb':
    NT, MT, n = sys.argv[2], sys.argv[3], sys.argv[4]
    lc.run_patched('lam_cheb.py', [
        ("sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')", "pass")],
        [NT, MT, n, os.path.join(lc.WORK, 'cheb.npz')])
else:
    NT, MT, n, k = sys.argv[1:5]
    out = os.path.join(TORI, 't_%s_%s_%s_%s.npz' % (NT, MT, n, k))
    if os.path.exists(out):
        print(k, 'exists')
        sys.exit(0)
    from gmpy2 import mpfr
    lc.run_patched('lam_tori.py', [
        ("sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')", "pass"),
        ("    L = L1 * (1 + x) / 2\n", "    L = LLO + (L1 - LLO) * (1 + x) / 2\n"),
        ("    d = np.load('/tmp/k2work/gc_torus_1_256.npz')\n"
         "    a0, b0 = resize(d['a'], d['b'], int(d['N']), int(d['M']), NT, MT)\n",
         "    d = np.load(INIT)\n"
         "    assert (int(d['NT']), int(d['MT'])) == (NT, MT)\n"
         "    a0 = np.array([float(Fr(v)) for v in d['a']]); b0 = np.array([float(Fr(v)) for v in d['b']])\n")],
        [NT, MT, n, k, str(lc.HI.numerator), str(lc.HI.denominator)],
        extra_globals=dict(LLO=mpfr(lc.LO.numerator) / lc.LO.denominator, INIT=INIT, Fr=Fr))
