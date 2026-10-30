"""UNTRUSTED numerics (Q-16, N-31).  Self-checks of the Dommaschk QA pipeline (about 15 s):

  1. basis.selftest: every Dommaschk potential is harmonic, stellarator symmetric and normalised
     (exact, sympy);
  2. the rational stellarator field of Q-19 (Phi = phi + h/4, N-30), written EXACTLY in the
     non-symmetric Dommaschk basis (nmax = 1, lmax = 3; least-squares residual ~ 1e-16), run through
     fieldeval (axis, iota, Boozer spectrum by Birkhoff averages along one line) must reproduce the
     independent results of scripts/c2_diagnostics (N-30 section 3): iota = 0.1344898, 0.1374307,
     0.1510525 at r = 0.05, 0.13073, 0.287; A10/B00 = 0.0549, A11/B00 = 0.0147 at r = 0.05; QA
     defect fraction 0.259, 0.258, 0.260.
Exits nonzero on failure.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'c2_diagnostics'))
import numpy as np
from basis import basis, selftest
import fieldeval as fe
import boozer as c2b


def main():
    n = selftest(2, 2, 5)
    print(f"basis selftest ok ({n} potentials)")
    b = basis(2, 1, 3, symmetric=False)
    tab = fe.Tables(b, 2)
    rng = np.random.default_rng(0)
    R = rng.uniform(0.6, 1.4, 300); z = rng.uniform(-.4, .4, 300); ph = rng.uniform(0, 2*np.pi, 300)
    f = ((R**2 - 1)**2 - 4*z**2)/(4*R**2); g = -z*((R**2 - 1)*(R**2 - 5) - 4*z**2)/(4*R**2)
    h = 0.25*(f*np.cos(2*ph) + g*np.sin(2*ph))
    A = np.array([[tab.eval(tab.A[:, :, [k]], np.array([[R[i]]]), ph[i], np.array([[z[i]]]), comps=(3,))[0, 0, 0]
                   for k in range(len(b))] for i in range(len(R))])
    a, *_ = np.linalg.lstsq(A, h, rcond=None)
    fit = np.abs(A @ a - h).max()
    W = tab.weights(a[None])
    Ra, za, ok, _ = fe.find_axis(tab, W, np.array([1.01]), np.array([0.0]), 64)
    rs = np.array([0.05, 0.13073386650096105, 0.287])
    sec, Bm, Jac, Phi, lost = fe.trace_surfaces(tab, W, Ra[:, None] + rs[None], za[:, None] + 0*rs[None], 64, 400)
    io, err = fe.iota_from_sections(sec, Ra, za, 2)
    c, jm = fe.boozer_coeffs(Bm, Jac, Phi, io, 2, 4, 4)
    ref_iota = np.array([0.1344898, 0.1374307, 0.1510525])
    ref_frac = np.array([0.259, 0.258, 0.260])
    frac = []
    for l in range(3):
        Am = c2b.amplitudes(fe.amplitudes_dict(c[0, l], 4))
        frac.append(c2b.qs_defect(Am, 1, 0)[1])
        if l == 0:
            a10, a11 = Am[(1, 0)]/Am[(0, 0)], Am[(1, 1)]/Am[(0, 0)]
    frac = np.array(frac)
    print(f"rational field in the Dommaschk basis: fit residual {fit:.1e}; axis ({Ra[0]:.12f}, {za[0]:.1e})")
    print(f"  iota {io[0]} (reference {ref_iota}); A10 {a10:.4f} A11 {a11:.4f}; QA fraction {frac}; "
          f"mean Jacobian {jm[0]}")
    good = (fit < 1e-12 and ok[0] and abs(Ra[0] - 1) < 1e-10 and np.abs(io[0] - ref_iota).max() < 2e-7
            and abs(a10 - 0.0549) < 2e-4 and abs(a11 - 0.0147) < 2e-4 and np.abs(frac - ref_frac).max() < 2e-3
            and np.abs(jm - 1).max() < 1e-6)
    print('validate:', 'PASS' if good else 'FAIL')
    return 0 if good else 1


if __name__ == '__main__':
    sys.exit(main())
