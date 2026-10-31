"""UNTRUSTED numerics (step 2 of the Dommaschk certification, notes/theory/dommaschk-qa.md §20).

The certification target (dommaschk-qa.md §24) as a purely rational field, in the polynomial
denominator form used by the flow-form invariance equation.

Field: B = grad Phi, Phi = phi + V, V = sum_k a_k V_k (Dommaschk potentials, scripts/dommaschk_qa/
basis.py), cylindrical (R, phi, z).  All 9 potentials with ln R terms have coefficient exactly 0
(checked at load time), and for NFP 2 every remaining term is c R^p z^j trig(m phi) with p, m even
and p >= -6.  So V is a polynomial in (s = R^2, 1/s, z, cos psi, sin psi) with psi = 2 phi (one field
period is psi in [0, 2 pi)), and the most negative power of s is s^-3 (from R^-6, m = 6).

Field-line equations with the toroidal angle as time (B^phi = (1 + d_phi V)/R^2):

    dR/dphi = R^2 d_R Phi / G,   dz/dphi = R^2 d_z Phi / G,   G := R B_phi = 1 + d_phi V.

Polynomial form (the analogue of D = s(1 + eps h_phi) of scripts/kam_oracle/field.py): multiply
numerator and denominator by s^3, the smallest power of r_2 = s that clears V:

    D  := s^3 G = s^3 (1 + d_phi V)        (= s^3 R B_phi = s^4 B^phi; positive near the axis)
    Ps := s^4 d_s Phi = s^4 d_R V / (2R)   (d_s V has s^-4 at worst)
    Pz := s^3 d_z Phi

are polynomials in (s, z, cos n psi, sin n psi), n <= 3, and

    D dR/dphi = 2 R Ps,     D dz/dphi = s Pz.

The flow-form residuals of a torus K = (R, z)(theta, phi) with frequency iota are therefore

    RR := D (d_phi R + iota d_theta R) - 2 R Ps,    RZ := D (d_phi z + iota d_theta z) - s Pz,

polynomials in the Fourier series of R and z (degrees: s up to 8 in D, i.e. R^16; z up to 5).
Choosing s^3 (and not a higher power) keeps the degree minimal; dividing out G rather than |B|
keeps the toroidal angle as time (the frequency vector is (iota, 1) exactly, as in KamTorusA).

Coefficients are exact Fractions (C[t, i, j] for trig index t, s^i, z^j).  Evaluation works on
numpy float/complex arrays and on numpy object arrays of mpmath mpf (multiprecision).
"""
import json
import os
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
TARGET = os.path.join(REPO, 'scripts', 'dommaschk_qa', 'results', '20261031T092522Z', 'candidate.json')
TARGET_SHA = 'b6d322648bc745dd40ea459c0bf19b0ddc7095683efe7f33a4a2b8b593cf1bb8'

# trig functions of psi = 2 phi: (kind, n) with value cos(n psi) or sin(n psi)
TRIG = [('c', 0), ('c', 1), ('c', 2), ('c', 3), ('s', 1), ('s', 2), ('s', 3)]
SHIFT = 3            # D = s^SHIFT G


def _add(d, k, c):
    if c:
        d[k] = d.get(k, Fr(0)) + c
        if d[k] == 0:
            del d[k]


class ExactField:
    """Exact polynomial data D, Ps, Pz of the candidate (dicts {(t, i, j): Fraction})."""

    def __init__(self, path=TARGET):
        cand = json.load(open(path))
        self.path, self.sha = path, cand.get('sha256')
        self.nfp = cand['nfp']
        assert self.nfp == 2, 'the psi = 2 phi convention assumes NFP 2'
        V = {}                                  # (p, j, kind, m) -> c    (c R^p z^j trig(m phi))
        nlog = 0
        for bk, a in zip(cand['basis'], cand['coefficients']):
            a = Fr(a)
            haslog = any(int(q) for _, _, q, _ in bk['terms'])
            nlog += haslog
            if a == 0:
                continue
            assert not haslog, f"log term with nonzero coefficient: {bk['name']}"
            kind = 'c' if bk['m'] == 0 else bk['trig'][0]
            for c, p, q, j in bk['terms']:
                _add(V, (int(p), int(j), kind, bk['m']), a*Fr(c))
        self.nlog_basis = nlog
        self.coeffs = [Fr(a) for a in cand['coefficients']]
        self.V = V
        D, Ps, Pz = {}, {}, {}
        _add(D, (0, SHIFT, 0), Fr(1))          # s^3 * 1
        for (p, j, kind, m), c in V.items():
            assert p % 2 == 0 and m % 2 == 0 and p + 2*SHIFT >= 0, (p, m)
            n = m//2
            i = (p + 2*SHIFT)//2                # R^p * s^3 = s^i
            # d_phi: cos(m phi) -> -m sin(m phi), sin -> m cos
            if m:
                if kind == 'c':
                    _add(D, (TRIG.index(('s', n)), i, j), -m*c)
                else:
                    _add(D, (TRIG.index(('c', n)), i, j), m*c)
            t = TRIG.index((kind, n))
            # Ps = s^4 * (p c R^(p-1))/(2R) = (p/2) c R^(p+6): same s-power i
            if p:
                _add(Ps, (t, i, j), Fr(p, 2)*c)
            if j:
                _add(Pz, (t, i, j - 1), j*c)
        self.polys = dict(D=D, Ps=Ps, Pz=Pz)
        self.I = 1 + max(i for P in self.polys.values() for (_, i, _) in P)
        self.J = 1 + max(j for P in self.polys.values() for (_, _, j) in P)
        self.maxcoef = max(abs(c) for P in self.polys.values() for c in P.values())

    def array(self, name, conv=float):
        C = np.zeros((len(TRIG), self.I, self.J), dtype=object if conv is not float else float)
        if conv is not float:
            C[...] = conv(0)
        for (t, i, j), c in self.polys[name].items():
            C[t, i, j] = conv(c)
        return C

    def l1(self, name):
        return float(sum(abs(c) for c in self.polys[name].values()))


def trig_values(psi, mp=None):
    """Array (7, *psi.shape) of the TRIG functions; mp: the mpmath module (object arrays)."""
    if mp is None:
        psi = np.asarray(psi, float)
        return np.array([np.cos(n*psi) if k == 'c' else np.sin(n*psi) for k, n in TRIG])
    psi = np.asarray(psi, dtype=object)
    out = np.empty((len(TRIG),) + psi.shape, dtype=object)
    for t, (k, n) in enumerate(TRIG):
        f = mp.cos if k == 'c' else mp.sin
        out[t] = np.vectorize(lambda x: f(n*x), otypes=[object])(psi) if psi.shape else f(n*psi)
    return out


class Evaluator:
    """D, Ps, Pz at points: numeric backend 'float' (numpy float/complex) or 'mp' (mpmath mpf in
    object arrays; mpf coefficients converted at the current mp precision)."""

    def __init__(self, ex, mp=None):
        self.ex, self.mp = ex, mp
        conv = float if mp is None else (lambda c: mp.mpf(c.numerator)/c.denominator)
        self.C = {k: ex.array(k, conv) for k in ('D', 'Ps', 'Pz')}

    def coeff_fields(self, T):
        """c_ij = sum_t C[t, i, j] T[t]: dict name -> nested list [i][j] of arrays shaped like T[0]."""
        out = {}
        for k, C in self.C.items():
            out[k] = [[sum(C[t, i, j]*T[t] for t in range(len(TRIG)) if C[t, i, j] != 0)
                       for j in range(self.ex.J)] for i in range(self.ex.I)]
        return out

    @staticmethod
    def horner(cij, s, z):
        val = 0
        for row in reversed(cij):
            inner = 0
            for c in reversed(row):
                inner = inner*z + c
            val = val*s + inner
        return val

    def DPP(self, s, z, T=None, cf=None):
        """D, Ps, Pz at (s, z); trig values T (7, ...) broadcastable, or precomputed coeff fields."""
        cf = cf if cf is not None else self.coeff_fields(T)
        return tuple(self.horner(cf[k], s, z) for k in ('D', 'Ps', 'Pz'))

    def rhs(self, phi, R, z):
        """dR/dphi, dz/dphi (float backend)."""
        T = trig_values(2*phi)
        D, Ps, Pz = self.DPP(R*R, z, T)
        return 2*R*Ps/D, R*R*Pz/D

    def B_cyl(self, R, phi, z):
        """Physical components (B_R, B_phi, B_z) (float backend)."""
        s = R*R
        D, Ps, Pz = self.DPP(s, z, trig_values(2*np.asarray(phi)))
        return 2*R*Ps/s**4, D/(s**3*R), Pz/s**3


def selftest(path=TARGET, npts=200, seed=1):
    """Compare with the independent evaluator scripts/dommaschk_qa/fieldeval.py (float)."""
    import sys
    sys.path.insert(0, os.path.join(REPO, 'scripts', 'dommaschk_qa'))
    import basis as bmod
    import fieldeval as fe
    cand = json.load(open(path))
    b = bmod.basis(cand['nfp'], cand['nmax'], cand['lmax'])
    assert [bk['name'] for bk in b] == [bk['name'] for bk in cand['basis']]
    x = np.array([float(Fr(c)) for c in cand['coefficients']])
    tab = fe.Tables(b, cand['nfp'])
    W = tab.weights(x[None])
    ex = ExactField(path)
    ev = Evaluator(ex)
    rng = np.random.default_rng(seed)
    err_rhs = err_B = 0.0
    for _ in range(20):
        phi = rng.uniform(0, 2*np.pi)
        R = rng.uniform(0.85, 1.05, (1, npts)); z = rng.uniform(-0.12, 0.12, (1, npts))
        a1, b1 = fe.line_rhs(tab, W, phi, R, z)
        a2, b2 = ev.rhs(phi, R, z)
        err_rhs = max(err_rhs, np.abs(a1 - a2).max(), np.abs(b1 - b2).max())
        BR, BP, BZ = tab.eval(W, R, phi, z)
        CR, CP, CZ = ev.B_cyl(R, phi, z)
        err_B = max(err_B, np.abs(BR - CR).max(), np.abs(BP - CP).max(), np.abs(BZ - CZ).max())
    return dict(rhs_maxdiff=float(err_rhs), B_maxdiff=float(err_B), log_basis=ex.nlog_basis,
                degree_s=ex.I - 1, degree_z=ex.J - 1, max_poly_coef=float(ex.maxcoef),
                terms={k: len(v) for k, v in ex.polys.items()},
                l1={k: ex.l1(k) for k in ex.polys}, sha_ok=(ex.sha == TARGET_SHA))


if __name__ == '__main__':
    print(json.dumps(selftest(), indent=1))


def majorant_report(ex, s0=1.0, zmax=0.1, du=0.1):
    """Coefficient sizes relevant for Lean majorants: l1 norms of D, Ps, Pz in the shifted variable
    u = s - s0 (and z), the majorant sum |c| du^i zmax^j over the box |u| <= du, |z| <= zmax (trig
    factors bounded by 1), against the typical size of the polynomial near the torus."""
    from math import comb
    out = {}
    for name, P in ex.polys.items():
        Q = {}
        for (t, i, j), c in P.items():           # s^i = sum_k C(i,k) s0^(i-k) u^k
            for k in range(i + 1):
                _add(Q, (t, k, j), c*comb(i, k)*Fr(s0).limit_denominator(10**6)**(i - k))
        out[name] = dict(l1_s=float(sum(abs(c) for c in P.values())),
                         l1_u=float(sum(abs(c) for c in Q.values())),
                         max_coef_u=float(max(abs(c) for c in Q.values())),
                         box_majorant=float(sum(abs(c)*du**k*zmax**j for (t, k, j), c in Q.items())),
                         value_at_s0=float(sum(c for (t, k, j), c in Q.items() if k == 0 and j == 0
                                               and TRIG[t] == ('c', 0))))
    return out
