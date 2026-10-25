"""UNTRUSTED driver: the two ball pipelines of the mu > 0 passing guiding-centre torus FAMILY
certificate: rho0 = 1/256 fixed, pitch parameter lam = mu B0 / E in [0, 1/4],
lam = (r - 63)/8 with r = 64 + cos theta' (the parameter variable of fam_cert.py), Chebyshev series
in theta'.  The flow form is that of Design/RationalStellaratorGCMuFlow.lean:
D~ = D + rho0 F (1/2) W^3 kappa_D, F = (1 - lam |B|/2)(1 - lam |B|)^(-1/2), |B| = QPP4 V V4.

* high resolution (box N_H, M_H, Chebyshev degree D_H, scale 2^-S_H): residual of the family torus K(x)
  for every x = cos theta' in [-1, 1], distances K_H(x) - K_L(x);
* low resolution (16, 12, D_L, 2^-60): admissibility balls at every torus mu-close to K(x).
The variable lists and trees of the rho = 1/256 pipelines (gc_cert.py) are kept; the rho-dependent
nodes become dummies and are re-created at the end with the parameter variable r = 2^14 rho = 64 + x.
Writes $EW_OUT/lam_cert_{H,L}.pkl.  Usage: python ew_cert.py [H|L|HL]

Energy-window variant (ew_cert.py, adapted from lam_cert.py): the gyro-length of the high-resolution
pipeline is rho_j = EW_RHO (a rational 'num/den', default 1/256), its torus is read from EW_CHEB
(default LAM_CHEB); the low-resolution input balls are enlarged by EW_EIN_ADD (a rational, default 0)
so that they contain every torus of the energy window; output directory EW_OUT (default /tmp/ew/out).
"""
import sys, os, time, pickle, math
import numpy as np, sympy as sp, gmpy2
from gmpy2 import mpfr, mpz
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kam_oracle'))
from flow_torus import index_sets
import gcmodel as G
from ballcert import up
from slp import to_tree
from fam_ball import FamPipeline, encode_slice, fam_grids, Slice

gmpy2.get_context().precision = 300
WHICH = sys.argv[1] if len(sys.argv) > 1 else 'HL'
Q, Iq = 96, 10888383889117653077957113864
MU = Fr(1, 10 ** 11)
RHOJ = Fr(os.environ.get('EW_RHO', '1/256'))
EIN_ADD = Fr(os.environ.get('EW_EIN_ADD', '0'))
OUTD = os.environ.get('EW_OUT', '/tmp/ew/out')
HN, HM, HS, HD = [int(x) for x in os.environ.get('LAM_H', '36,27,107,18').split(',')]
LN, LM, LS, LD = 16, 12, 60, int(os.environ.get('LAM_LD', '6'))
LDC = int(os.environ.get('LAM_LDC', '6'))     # Chebyshev degree of the low-resolution centres
HLBLK = int(os.environ.get('FAM_LBLK', '8'))
HRLB = int(os.environ.get('FAM_RLB', '4'))   # block length of the residual norms
HLCENT = int(os.environ.get('FAM_LCENT', '8'))   # block length of the centre norms (H)
RSH = 14            # r = 2^14 rho
LAMDEN = int(os.environ.get('LAM_DEN', '16'))   # lam = (r - 63)/LAMDEN = (1 + cos theta')/LAMDEN

import ew_leandata
LEANL = ew_leandata.read(['RationalStellaratorGCMuDataL'])   # the certified low-resolution data
NT, MT = 28, 20
Is, Iz = index_sets(NT, MT)
CA = CB = None
HDATA = pickle.load(open(os.environ['EW_HDATA'], 'rb')) if 'EW_HDATA' in os.environ else None


def slice_grids(N, M, S, jw, CA=CA, CB=CB):
    """2-D grids of the Chebyshev coefficient jw of u and z (halved for jw >= 1)."""
    fac = mpfr(1) if jw == 0 else mpfr(1) / 2
    GU = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    GZ = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for (k, m), x in zip(Is, CA[jw]):
        if abs(k) > N or abs(m) > M:
            continue
        x = x * fac
        if (k, m) == (0, 0):
            xx = x - 1 if jw == 0 else x
            GU[N][M] = int(gmpy2.rint(xx * mpfr(2) ** S / 2)) * 2
        else:
            v = int(gmpy2.rint(x * mpfr(2) ** (S - 1)))
            GU[N + k][M + m] = v
            GU[N - k][M - m] = v
    for (k, m), x in zip(Iz, CB[jw]):
        if abs(k) > N or abs(m) > M:
            continue
        v = int(gmpy2.rint(x * fac * mpfr(2) ** (S - 1)))
        GZ[N + k][M + m] = v
        GZ[N - k][M - m] = -v
    return GU, GZ


def torus_slices(N, M, S, Dd, CA=CA, CB=CB):
    su, sz = [], []
    for jw in range(Dd + 1):
        GU, GZ = slice_grids(N, M, S, jw, CA, CB)
        su.append(encode_slice(GU, N, M, 1)[0])
        sz.append(encode_slice(GZ, N, M, -1)[0])
    return su, sz


def const_slices(vals, N, M):
    """Slices of a family constant in (theta, psi): grid value vals[jw] at (N, M)."""
    out = []
    for v in vals:
        g = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
        g[N][M] = v
        out.append(encode_slice(g, N, M, 1, 0, 0)[0])
    return out


class Builder:
    def __init__(self, PL, prefix):
        self.PL = PL
        self.prefix = prefix
        self.sym = {}
        self.meta = {}
        self.norms = []

    def S(self, name, var, **meta):
        s_ = sp.Symbol(name)
        self.sym[s_] = var
        self.meta[var] = dict(name=name, **meta)
        return s_

    def const(self, kind, name, X):
        return self.S(name, self.PL.add_const(kind, name), X=X, kind='const')

    def fam(self, slices, p, name, X, kind='input', E=Fr(0), sym=(1, 0, 0), box=None, Lc=None, **kw):
        return self.S(name, self.PL.add_fam(slices, p, name, E=E, sym=sym, box=box, Lc=Lc), X=X,
                      kind=kind, sym=sym, **kw)

    def dummy(self, name, w=(1, 0, 0)):
        return self.S(name, self.PL.add_dummy(name, w), X='0', kind='dummy')

    def node(self, name, expr, X=None, norm=False, quiet=False, Erad=None, Lb=None, **meta):
        PL = self.PL
        syms = {k: v for k, v in self.sym.items() if expr.has(k)}
        st = [k for k, v in self.sym.items() if v == 0][0]
        sV = [k for k, v in self.sym.items() if v == 1][0]
        syms[st] = 0
        syms[sV] = 1
        tr, c = to_tree(expr, syms, PL.W, 0, 1)
        t0 = time.time()
        rec = PL.node(name, tr, 0 if norm else c, Erad=Erad, Lb=Lb)
        rec['cscale'] = c
        rec['expr'] = expr
        if not quiet:
            print('%s %-8s w=%s c=%s b=%d slots=%d rad=%.3e beta=%.3e dmaj=%.3e (%.1fs)' % (
                self.prefix, name, rec['w'], c, rec['b'], rec['slots'],
                float(rec['rad'] / (abs(c) if norm else 1)), float(rec['beta']), float(rec['dmaj']),
                time.time() - t0), flush=True)
        if norm:
            rec['meta'] = dict(name=name, **meta)
            self.norms.append(rec)
            return rec
        v = rec['var']
        s_ = sp.Symbol(name)
        self.sym[s_] = v
        self.meta[v] = dict(name=name, X=X, kind='node', rec=rec, **meta)
        return s_


def newton_isqrt(PL, Evar):
    """Family approximate (1 + E)^(-1/2) by Newton iterations on families (scratch pipeline)."""
    N, M, D, S = PL.N, PL.M, PL.D, PL.S
    SC = FamPipeline(N, M, D, S, 'scratch', PL.Lblk)
    ts = SC.add_const('T', 't')
    SC.add_const('V', 'V')
    Eg = SC.add_fam(PL.fam[Evar]['slices'], PL.W[Evar][2], 'E', norm=False)
    cur = SC.add_fam(const_slices([2 ** S], N, M), 0, 'V', norm=False)
    for it in range(12):
        e3 = ('mul', ('sub', ('mul', ('cst', 3), ('mul', ('var', ts), ('mul', ('var', ts), ('var', ts)))),
                      ('mul', ('add', ('var', ts), ('var', Eg)), ('mul', ('var', cur), ('var', cur)))),
              ('var', cur))
        sl = SC.node('it', e3, 2, record=False)
        old = SC.grids(cur)
        cur = SC.add_fam(sl, 0, 'V', norm=False)
        new = SC.grids(cur)
        diff = max(abs(new[k][i][j] - old[k][i][j]) for k in range(len(new)) for i in range(len(new[0]))
                   for j in range(len(new[0][0])))
        if diff <= 8:
            break
    return SC.fam[cur]['slices']


def newton_inv(PL, Fvar):
    N, M, D, S = PL.N, PL.M, PL.D, PL.S
    SC = FamPipeline(N, M, D, S, 'scratch', PL.Lblk)
    ts = SC.add_const('T', 't')
    SC.add_const('V', 'V')
    Fg = SC.add_fam(PL.fam[Fvar]['slices'], PL.W[Fvar][2], 'F', norm=False)
    g0 = PL.grids(Fvar)[D][N][M]
    q0 = int(round(2 ** S / (g0 / 2 ** S)))
    cur = SC.add_fam(const_slices([q0], N, M), 0, 'q', norm=False)
    for it in range(80):
        e2 = ('mul', ('sub', ('mul', ('cst', 2), ('mul', ('var', ts), ('var', ts))),
                      ('mul', ('var', Fg), ('var', cur))), ('var', cur))
        sl = SC.node('it', e2, 1, record=False)
        old = SC.grids(cur)
        cur = SC.add_fam(sl, 0, 'q', norm=False)
        new = SC.grids(cur)
        diff = max(abs(new[k][i][j] - old[k][i][j]) for k in range(len(new)) for i in range(len(new[0]))
                   for j in range(len(new[0][0])))
        if diff <= 1:
            break
    return SC.fam[cur]['slices']


u, z, c, s = G.u, G.z, G.c, G.s


def phiP(e):
    return sp.expand(sp.diff(e, c) * (-2 * s) + sp.diff(e, s) * (2 * c))


POL = dict(G.ALLP)
POL['PdP'] = sp.expand(sp.diff(POL['PuP'], u))
for b_ in ['D', 'nR', 'nZ']:
    X0 = G.BASE[b_ + 'p']
    for k_, ex in [('uuP', sp.diff(X0, u, 2)), ('uzP', sp.diff(X0, u, z)), ('zzP', sp.diff(X0, z, 2)),
                   ('uphP', sp.diff(phiP(X0), u)), ('zphP', sp.diff(phiP(X0), z))]:
        POL[b_ + k_] = sp.expand(ex)
import lam_gen_poly as LGP
for n_, e_ in LGP.MU.items():
    POL[n_] = e_
LEAN_LEAF = {'Dp': 'KamNewton.Dp', 'nRp': 'KamNewton.nRp', 'nZp': 'KamNewton.nZp'}


def leafname(n):
    return LEAN_LEAF.get(n, n)


def build_common(B, low):
    """As gc_cert.build_common; the rho-nodes Dt, nRt, nZt become dummies (re-created later)."""
    PL = B.PL
    sU, sZ = B.sU, B.sZ
    st, sC, sS = B.st, B.sC, B.sS
    leafs = ['Dp', 'nRp', 'nZp', 'DuP', 'DzP', 'DphP', 'nRuP', 'nRzP', 'nRphP', 'nZuP', 'nZzP', 'nZphP', 'PuP']
    if low:
        leafs += ['PdP'] + [b_ + k for b_ in ['D', 'nR', 'nZ'] for k in ['uuP', 'uzP', 'zzP', 'uphP', 'zphP']]
    need = set()
    for n in leafs:
        for (i, j, k, l), co in sp.Poly(POL[n], u, z, c, s).terms():
            need.add((i, j))
    mono = {(1, 0): sU, (0, 1): sZ}
    for (i, j) in sorted(need, key=lambda x: (x[0] + x[1], x)):
        if (i, j) in mono or (i, j) == (0, 0):
            continue
        a1, a2 = ((i - 1, j), (1, 0)) if i >= 1 and (i >= 2 or j < 2) else ((i, j - 1), (0, 1))
        mono[(i, j)] = B.node('m%d%d' % (i, j), mono[a1] * mono[a2], quiet=False, rel='mono')

    def leafexpr(n):
        tot = 0
        for (i, j, k, l), co in sp.Poly(POL[n], u, z, c, s).terms():
            tot += sp.Rational(co) * (mono[(i, j)] if (i, j) != (0, 0) else st) * sC ** k * sS ** l
        return tot
    L = {}
    for n in leafs:
        L[n] = B.node(n, leafexpr(n), rel='leaf', leaf=leafname(n))
    R = st + sU
    RD = B.node('RD', R * L['Dp'], rel='plain')
    RDu = B.node('RDu', R * L['DuP'], rel='plain')
    RDz = B.node('RDz', R * L['DzP'], rel='plain')
    RDph = B.node('RDph', R * L['DphP'], rel='plain')
    D, nR, nZ = L['Dp'], L['nRp'], L['nZp']
    q = B.node('q', nR ** 2 + RD ** 2 + nZ ** 2, rel='unfold')
    qR = B.node('qR', 2 * nR * L['nRuP'] + 2 * RD * D + 2 * RD * RDu + 2 * nZ * L['nZuP'], rel='unfold')
    qz = B.node('qz', 2 * nR * L['nRzP'] + 2 * RD * RDz + 2 * nZ * L['nZzP'], rel='unfold')
    qph = B.node('qph', 2 * nR * L['nRphP'] + 2 * RD * RDph + 2 * nZ * L['nZphP'], rel='unfold')
    P2 = B.node('P2', L['PuP'] ** 2, rel='plain')
    E = B.node('E', q * P2 - st ** 2, rel='E')
    Evar = B.sym[E]
    V0s = newton_isqrt(PL, Evar)
    sV0 = B.fam(V0s, 0, 'V0', X='V0', kind='data')
    if low:
        rVm1 = B.node('Vm1', sV0 - st, norm=True, role='Vm1')
        rV2 = B.node('V2m1', sV0 ** 2 - st ** 2, norm=True, role='V2m1')
        reta = B.node('eta', sV0 ** 2 * (st + E) - st ** 3, norm=True, role='eta')
    else:
        # high resolution: the square V0^2 as a rounding node keeps the eta node at degree 2
        sV2 = B.node('V2', sV0 ** 2, rel='plain')
        rVm1 = B.node('Vm1', sV0 - st, norm=True, role='Vm1', Lb=8)
        rV2 = B.node('V2m1', sV2 - st, norm=True, role='V2m1', Lb=8)
        reta = B.node('eta', sV2 * (st + E) - st ** 2, norm=True, role='eta', Lb=8)
    aV, n2, eta = rVm1['rad'], rV2['rad'], reta['rad']
    Ra, Rn2, Reta = up(aV, 4), up(n2, 4), up(eta, 3)
    bV = up(1 / (1 - Ra), 6)
    mE = PL.B[Evar] + PL.E[Evar]
    m = up(max(bV ** 2 * Rn2, mE), 4)
    g = up(Fr(1 / math.sqrt(1 - float(m))) * Fr(1000001, 1000000), 6)
    assert g * g * (1 - m) >= 1
    assert g ** 3 / 2 * m + Ra < 2
    epsV = up(g ** 3 / 2 * bV ** 2 * Reta, 3)
    B.vstep = dict(Ra=Ra, Rn2=Rn2, Reta=Reta, b=bV, m=m, g=g, eps=epsV, mE=mE)
    print('%s V-step: a=%s b=%s m=%s g=%s eps=%.3e' % (B.prefix, float(Ra), float(bV), float(m), float(g),
                                                       float(epsV)), flush=True)
    sVn = B.fam(V0s, 0, 'Vn', X='Vn', kind='vnode', E=epsV)
    W = B.node('W', L['PuP'] * sVn, rel='unfold')
    W2 = B.node('W2', W ** 2, rel='plain')
    W3 = B.node('W3', W2 * W, rel='unfold')
    R2 = B.node('R2', R ** 2, rel='plain')
    R3 = B.node('R3', R2 * R, rel='plain')
    A1 = B.node('A1', R * qR, rel='plain')
    A2 = B.node('A2', R * qz, rel='plain')
    K1 = B.node('K1', nZ * A1 - 8 * nZ * q - nR * A2, rel='plain')
    K2 = B.node('K2', RD * A2 - nZ * qph, rel='plain')
    K3 = B.node('K3', nR * qph - RD * A1 + 8 * RD * q, rel='plain')
    KD = B.node('KD', R2 * K1, rel='unfold')
    KR = B.node('KR', R3 * K2, rel='unfold')
    KZ = B.node('KZ', R3 * K3, rel='unfold')
    B.dummy('Dt0')
    B.dummy('nRt0', (1, 0, 3))
    B.dummy('nZt0')
    return dict(L=L, R=R, RD=RD, RDu=RDu, RDz=RDz, RDph=RDph, q=q, qR=qR, qz=qz, qph=qph, P2=P2, E=E,
                Vn=sVn, W=W, W2=W2, W3=W3, R2=R2, R3=R3, A1=A1, A2=A2, K1=K1, K2=K2, K3=K3, KD=KD, KR=KR,
                KZ=KZ, mono=mono, leafexpr=leafexpr)


def make_builder(N, M, D, S, prefix, Lblk):
    PL = FamPipeline(N, M, D, S, prefix, Lblk)
    B = Builder(PL, prefix)
    B.st = B.const('T', 't', '1')
    B.sV = B.const('V', 'V', '1')
    B.sC = B.const('C', 'c', 'cS')
    B.sS = B.const('S', 's', 'sS')
    return B


def add_r(B):
    """r = 2^14 rho = 64 + cos theta' (exact family constant, weight (1, 0, 0))."""
    PL = B.PL
    S = PL.S
    return B.fam(const_slices([64 * 2 ** S, 2 ** (S - 1)], PL.N, PL.M), 0, 'r', X='r', kind='param',
                 box=(PL.N, PL.M, PL.D + 1))


def vnode(B, Esym, pre, high):
    """A node (1 + E)^(-1/2): Newton data `pre`0, the norm nodes `pre`m1, eta`pre` and the vnode `pre`n.
    The ball comes from the step `vstep2` (RationalStellaratorGCMuCommon): with ||V0 - 1|| <= a,
    ||V0^2 (1 + E) - 1|| <= eta, ||E|| <= e, b >= 1/(1 - a), m >= e + b^2 eta: eps = g^3/2 b^2 eta."""
    PL = B.PL
    st = B.st
    Evar = B.sym[Esym]
    V0s = newton_isqrt(PL, Evar)
    sV0 = B.fam(V0s, 0, pre + '0', X=pre + '0', kind='data')
    if not high:
        rVm1 = B.node(pre + 'm1', sV0 - st, norm=True, role=pre + 'm1')
        reta = B.node('eta' + pre, sV0 ** 2 * (st + Esym) - st ** 3, norm=True, role='eta' + pre)
    else:
        sV2 = B.node(pre + '2', sV0 ** 2, rel='plain')
        rVm1 = B.node(pre + 'm1', sV0 - st, norm=True, role=pre + 'm1', Lb=8)
        reta = B.node('eta' + pre, sV2 * (st + Esym) - st ** 2, norm=True, role='eta' + pre, Lb=8)
    aV, eta = rVm1['rad'], reta['rad']
    Ra, Reta = up(aV, 4), up(eta, 3)
    bV = up(1 / (1 - Ra), 6)
    mE = PL.B[Evar] + PL.E[Evar]
    m = up(mE + bV ** 2 * Reta, 4)
    assert m < 1, ('vstep2 fails', float(m))
    g = up(Fr(1 / math.sqrt(1 - float(m))) * Fr(1000001, 1000000), 6)
    assert g * g * (1 - m) >= 1
    assert g ** 3 / 2 * m + Ra < 2, ('vstep2 smallness fails', float(g ** 3 / 2 * m + Ra))
    epsV = up(g ** 3 / 2 * bV ** 2 * Reta, 3)
    if not hasattr(B, 'vsteps'):
        B.vsteps = {}
    B.vsteps[pre] = dict(Ra=Ra, Reta=Reta, b=bV, m=m, g=g, eps=epsV, mE=mE)
    print('%s %s-step: a=%s b=%s |E|=%s m=%s g=%s eps=%.3e' % (B.prefix, pre, float(Ra), float(bV), float(mE),
                                                              float(m), float(g), float(epsV)), flush=True)
    return B.fam(V0s, 0, pre + 'n', X=pre + 'n', kind='vnode', E=epsV)


def lam_nodes(B, C, low):
    """The leaves of |B|, the nodes V4 = (1 + E4)^(-1/2), |B| = QPP4 V V4, EN = -lam |B|,
    N = (1 + EN)^(-1/2), F = (1 - lam |B|/2) N, with lam = (r - 63)/8."""
    st, r = B.st, B.sr
    mono, leafexpr = C['mono'], C['leafexpr']
    leafs = ['P4P'] + (['P4uP'] if low else [])
    need = set()
    for n in leafs:
        for (i, j, k, l), co in sp.Poly(POL[n], u, z, c, s).terms():
            need.add((i, j))

    def getmono(i, j):
        if (i, j) not in mono:
            a1, a2 = ((i - 1, j), (1, 0)) if i >= 1 and (i >= 2 or j < 2) else ((i, j - 1), (0, 1))
            m1 = getmono(*a1)
            mono[(i, j)] = B.node('mu%d_%d' % (i, j), m1 * mono[a2], quiet=True, rel='mono')
        return mono[(i, j)]
    for (i, j) in sorted(need, key=lambda x: (x[0] + x[1], x)):
        if (i, j) != (0, 0):
            getmono(i, j)
    Lq = {}
    for n in leafs:
        Lq[n] = B.node(n, leafexpr(n), rel='leaf', leaf=n)
    P4 = Lq['P4P']
    R4 = B.node('R4', C['R2'] ** 2, rel='plain')
    R8 = B.node('R8', R4 ** 2, rel='plain')
    P42 = B.node('P42', P4 ** 2, rel='plain')
    Lq['E4P'] = B.node('E4P', R8 * P42 - st ** 2, rel='lam')
    PP4 = B.node('PP4', C['L']['PuP'] * P4, rel='plain')
    Lq['QPP4P'] = B.node('QPP4P', C['q'] * PP4, rel='lam')
    Lq.update(R4=R4, R8=R8, P42=P42, PP4=PP4)
    V4n = vnode(B, Lq['E4P'], 'V4', not low)
    VV4 = B.node('VV4', C['Vn'] * V4n, rel='plain')
    Bm = B.node('Bm', Lq['QPP4P'] * VV4, rel='lam')
    lam = B.node('lamv', (r - 63 * st) / LAMDEN, rel='lam')
    EN = B.node('EN', -lam * Bm, rel='lam')
    Nn = vnode(B, EN, 'N', not low)
    Fv = B.node('Fv', (st + EN / 2) * Nn, rel='lam')
    return dict(Lq=Lq, V4n=V4n, VV4=VV4, Bm=Bm, EN=EN, Nn=Nn, Fv=Fv, lam=lam)


def lam_rho_nodes(B, C, LN, J=False):
    """Y = W3 * K and the corrections D~ = D + rho0 F Y / 2 = D + F Y / 2^9; with J (energy window)
    also the fields at rho_j: DtJ = DtF + (rho_j - rho0) F Y / 2 (nodes `DtJ`, `nRtJ`, `nZtJ`)."""
    L = C['L']
    out = {}
    dh = (RHOJ - Fr(1, 256)) / 2
    for nm, base, kk, ph in [('Dt', 'Dp', 'KD', 0), ('nRt', 'nRp', 'KR', 3), ('nZt', 'nZp', 'KZ', 0)]:
        Y = B.node('Y' + nm, C['W3'] * C[kk], rel='plain')
        out['Y' + nm] = Y
        out[nm] = B.node(nm + 'F', L[base] + LN['Fv'] * Y / 2 ** 9, rel='rho', base=base, Y='Y' + nm)
    if J:
        for nm in ['Dt', 'nRt', 'nZt']:
            out[nm] = B.node(nm + 'J', out[nm] + LN['Fv'] * out['Y' + nm] * sp.Rational(dh.numerator, dh.denominator),
                             rel='rhoJ', F=nm + 'F', Y='Y' + nm)
    return out


t0 = time.time()
res = {}
if 'H' in WHICH:
    H = make_builder(HN, HM, HD, HS, 'H', HLBLK)
    H.PL.Lcent = HLCENT
    su, sz = HDATA['su'], HDATA['sz']   # the node torus (exact grids, scale 2^-HS)
    H.su, H.sz = su, sz
    H.sU = H.fam(su, 0, 'U', X='u', Lc=1)
    H.sZ = H.fam(sz, 1, 'Z', X='z', Lc=1)
    H.sLRx = H.fam(su, 3, 'LRx', X='2^96 L u', kind='Linput', sym=(0, Iq, 2 ** (Q + 1)), Lc=1)
    H.sLZx = H.fam(sz, 0, 'LZx', X='2^96 L z', kind='Linput', sym=(0, Iq, 2 ** (Q + 1)), Lc=1)
    H.sthU = H.fam(su, 3, 'thU', X='dTh u', kind='derived', sym=(0, 1, 0), Lc=1)
    H.sthZ = H.fam(sz, 0, 'thZ', X='dTh z', kind='derived', sym=(0, 1, 0), Lc=1)
    lu, lz = LEANL['sdLM_U'], LEANL['sdLM_Z']
    # embed the low-resolution family: same slices, scale 2^(HS - LS), in the H layout
    def emb(sl):
        out = []
        for sd in sl:
            g = fam_grids([sd], LN, LM, 0, 1)[0]
            out.append(sd)
        return out
    H.lu, H.lz = lu, lz
    E2 = 2 ** (HS - LS)
    H.sUe = H.fam(lu, 0, 'Ue', X='uL', kind='embed', sym=(E2, 0, 0), box=(2 * HN, 2 * HM, 2 * HD))
    H.sZe = H.fam(lz, 1, 'Ze', X='zL', kind='embed', sym=(E2, 0, 0), box=(2 * HN, 2 * HM, 2 * HD))
    H.sthUe = H.fam(lu, 3, 'thUe', X='dTh uL', kind='derived', sym=(0, E2, 0))
    H.sthZe = H.fam(lz, 0, 'thZe', X='dTh zL', kind='derived', sym=(0, E2, 0))
    dIQ = Fr(2 ** 96, 10 ** 29)
    H.PL.E[H.sym[H.sLRx]] = up(dIQ * H.PL.B[H.sym[H.sthU]], 4)
    H.PL.E[H.sym[H.sLZx]] = up(dIQ * H.PL.B[H.sym[H.sthZ]], 4)
    print('H inputs done (%.0fs)' % (time.time() - t0), flush=True)
    rdu = H.node('dU', H.sU - H.sUe, norm=True, role='dist', Lb=8)
    rdz = H.node('dZ', H.sZ - H.sZe, norm=True, role='dist', Lb=8)
    rda = H.node('dA', H.sthU - H.sthUe, norm=True, role='dist', Lb=8)
    rdb = H.node('dB', H.sthZ - H.sthZe, norm=True, role='dist', Lb=8)
    DIST = [up(r_['rad'], 3) for r_ in (rdu, rdz, rda, rdb)]
    print('distances K_H - K_L: %s' % [float(x) for x in DIST], flush=True)
    HC = build_common(H, low=False)
    H.sr = add_r(H)
    HLN = lam_nodes(H, HC, False)
    RN = lam_rho_nodes(H, HC, HLN, J=True)
    rR = H.node('resR', RN['Dt'] * H.sLRx - 2 ** Q * RN['nRt'] * H.st, norm=True, role='resR', Lb=HRLB)
    rZ = H.node('resZ', RN['Dt'] * H.sLZx - 2 ** Q * RN['nZt'] * H.st, norm=True, role='resZ', Lb=HRLB)
    e0R, e0Z = rR['rad'] / 2 ** Q, rZ['rad'] / 2 ** Q
    print('e0: resR <= %.4e  resZ <= %.4e   (%.0fs)' % (float(e0R), float(e0Z), time.time() - t0), flush=True)
    res['H'] = H
    res['DIST'] = DIST
    res['e0'] = (e0R, e0Z)

if 'L' in WHICH:
    if 'DIST' in res:
        DIST = res['DIST']
    else:
        # the distances K_H - K_L of the high-resolution run (the norm bounds of OutH)
        DIST = [Fr(117, 10 ** 10), Fr(23, 2000000000), Fr(117, 10 ** 10), Fr(29, 2500000000)]
    L_ = make_builder(LN, LM, LDC, LS, 'L', 8)
    lu, lz = LEANL['sdLM_U'], LEANL['sdLM_Z']
    EIN = [MU + x + EIN_ADD for x in DIST]
    L_.sU = L_.fam(lu, 0, 'U', X='u', kind='torus', E=up(EIN[0], 3))
    L_.sZ = L_.fam(lz, 1, 'Z', X='z', kind='torus', E=up(EIN[1], 3))
    L_.sA = L_.fam(lu, 3, 'A', X='dTh u', kind='torus', E=up(EIN[2], 3), sym=(0, 1, 0))
    L_.sB = L_.fam(lz, 0, 'B', X='dTh z', kind='torus', E=up(EIN[3], 3), sym=(0, 1, 0))
    LC = build_common(L_, low=True)
    B = L_
    Lf = LC['L']
    R, RD, RDu, RDz, RDph = LC['R'], LC['RD'], LC['RDu'], LC['RDz'], LC['RDph']
    D, nR, nZ = Lf['Dp'], Lf['nRp'], Lf['nZp']
    Du, Dz, Dph = Lf['DuP'], Lf['DzP'], Lf['DphP']
    nRu, nRz, nRph = Lf['nRuP'], Lf['nRzP'], Lf['nRphP']
    nZu, nZz, nZph = Lf['nZuP'], Lf['nZzP'], Lf['nZphP']
    P, Pd = Lf['PuP'], Lf['PdP']
    Duu, Duz, Dzz, Duph, Dzph = (Lf['D' + k] for k in ['uuP', 'uzP', 'zzP', 'uphP', 'zphP'])
    nRuu, nRuz, nRzz, nRuph, nRzph = (Lf['nR' + k] for k in ['uuP', 'uzP', 'zzP', 'uphP', 'zphP'])
    nZuu, nZuz, nZzz, nZuph, nZzph = (Lf['nZ' + k] for k in ['uuP', 'uzP', 'zzP', 'uphP', 'zphP'])
    q, qR, qz, qph, P2 = LC['q'], LC['qR'], LC['qz'], LC['qph'], LC['P2']
    sVn, W2, W3, R2, R3 = LC['Vn'], LC['W2'], LC['W3'], LC['R2'], LC['R3']
    A1, A2, K1, K2, K3 = LC['A1'], LC['A2'], LC['K1'], LC['K2'], LC['K3']
    KD, KR, KZ = LC['KD'], LC['KR'], LC['KZ']
    qRu = B.node('qRu', 2 * nRu ** 2 + 2 * nR * nRuu + 2 * D ** 2 + 8 * RD * Du + 2 * RDu ** 2 + 2 * RD * R * Duu
                 + 2 * nZu ** 2 + 2 * nZ * nZuu, rel='deriv')
    qRz = B.node('qRz', 2 * nRz * nRu + 2 * nR * nRuz + 4 * RD * Dz + 2 * R * RDz * Du + 2 * RD * R * Duz
                 + 2 * nZz * nZu + 2 * nZ * nZuz, rel='deriv')
    qzz = B.node('qzz', 2 * nRz ** 2 + 2 * nR * nRzz + 2 * RDz ** 2 + 2 * RD * R * Dzz + 2 * nZz ** 2 + 2 * nZ * nZzz,
                 rel='deriv')
    qzu = B.node('qzu', 2 * nRu * nRz + 2 * nR * nRuz + 4 * RD * Dz + 2 * RDu * RDz + 2 * RD * R * Duz
                 + 2 * nZu * nZz + 2 * nZ * nZuz, rel='deriv')
    qphu = B.node('qphu', 2 * nRu * nRph + 2 * nR * nRuph + 4 * RD * Dph + 2 * RDu * RDph + 2 * RD * R * Duph
                  + 2 * nZu * nZph + 2 * nZ * nZuph, rel='deriv')
    qphz = B.node('qphz', 2 * nRz * nRph + 2 * nR * nRzph + 2 * RDz * RDph + 2 * RD * R * Dzph + 2 * nZz * nZph
                  + 2 * nZ * nZzph, rel='deriv')
    qu = B.node('qu', 2 * nR * nRu + 2 * RD * D + 2 * RD * RDu + 2 * nZ * nZu, rel='deriv')
    qzd = B.node('qzd', 2 * nR * nRz + 2 * RD * RDz + 2 * nZ * nZz, rel='deriv')
    Eu = B.node('Eu', qu * P2 + 2 * q * P * Pd, rel='Ed', idx=0)
    Ez = B.node('Ez', qzd * P2, rel='Ed', idx=1)
    V3 = B.node('V3', sVn ** 3, rel='plain')
    Wu = B.node('Wu', Pd * sVn - P * V3 * Eu / 2, rel='dW')
    Wz = B.node('Wz', -P * V3 * Ez / 2, rel='dW')
    W3u = B.node('W3u', 3 * W2 * Wu, rel='deriv')
    W3z = B.node('W3z', 3 * W2 * Wz, rel='deriv')
    KDu = B.node('KDu', 2 * R * K1 + R2 * (nZu * A1 + nZ * qR + nZ * R * qRu - 8 * nZu * q - 8 * nZ * qu - nRu * A2
                                           - nR * qz - nR * R * qzu), rel='deriv')
    KDz = B.node('KDz', R2 * (nZz * A1 + nZ * R * qRz - 8 * nZz * q - 8 * nZ * qzd - nRz * A2 - nR * R * qzz),
                 rel='deriv')
    KRu = B.node('KRu', 3 * R2 * K2 + R3 * (2 * RD * qz + R2 * Du * qz + R2 * D * qzu - nZu * qph - nZ * qphu),
                 rel='deriv')
    KRz = B.node('KRz', R3 * (R2 * Dz * qz + R2 * D * qzz - nZz * qph - nZ * qphz), rel='deriv')
    KZu = B.node('KZu', 3 * R2 * K3 + R3 * (nRu * qph + nR * qphu - 2 * RD * qR - R2 * Du * qR - R2 * D * qRu
                                            + 8 * D * q + 8 * RDu * q + 8 * RD * qu), rel='deriv')
    KZz = B.node('KZz', R3 * (nRz * qph + nR * qphz - R2 * Dz * qR - R2 * D * qRz + 8 * RDz * q + 8 * RD * qzd),
                 rel='deriv')
    for nm, ph in [('Dtu0', 0), ('Dtz0', 3), ('nRtu0', 3), ('nRtz0', 0), ('nZtu0', 0), ('nZtz0', 1), ('Ptor0', 0)]:
        B.dummy(nm, (1, 0, ph))
    sU, sZ, sA, sB = B.sU, B.sZ, B.sA, B.sB
    W0 = B.node('W0', sA * sZ - sB * sU, rel='W0')
    B.dummy('Dt30')
    W02 = B.node('W02', W0 ** 2, rel='plain')
    B.dummy('F0')
    B.dummy('qi0')
    B.dummy('Y0')
    # the parameter and the rho-dependent nodes
    B.sr = add_r(B)
    st, r = B.st, B.sr
    LLN = lam_nodes(B, LC, True)
    lam, Bm, Nn, Fl, EN, VV4 = LLN['lam'], LLN['Bm'], LLN['Nn'], LLN['Fv'], LLN['EN'], LLN['VV4']
    Lq, V4n = LLN['Lq'], LLN['V4n']
    # derivatives of |B| and of F
    R7 = B.node('R7', Lq['R4'] * R3, rel='plain')
    P4P4u = B.node('P4P4u', Lq['P4P'] * Lq['P4uP'], rel='plain')
    Lq['E4uP'] = B.node('E4uP', 8 * R7 * Lq['P42'] + 2 * Lq['R8'] * P4P4u, rel='lamd')
    dPP4 = B.node('dPP4', Pd * Lq['P4P'] + P * Lq['P4uP'], rel='plain')
    Lq['QPP4uP'] = B.node('QPP4uP', qu * Lq['PP4'] + q * dPP4, rel='lamd')
    Lq['QPP4zP'] = B.node('QPP4zP', qzd * Lq['PP4'], rel='lamd')
    V43 = B.node('V43', V4n ** 3, rel='plain')
    V4u = B.node('V4u', -V43 * Lq['E4uP'] / 2, rel='lamd')
    Vu = B.node('Vu', -V3 * Eu / 2, rel='lamd')
    Vz = B.node('Vz', -V3 * Ez / 2, rel='lamd')
    D4u = B.node('D4u', Vu * V4n + sVn * V4u, rel='lamd')
    D4z = B.node('D4z', Vz * V4n, rel='lamd')
    Bmu = B.node('Bmu', Lq['QPP4uP'] * VV4 + Lq['QPP4P'] * D4u, rel='lamd')
    Bmz = B.node('Bmz', Lq['QPP4zP'] * VV4 + Lq['QPP4P'] * D4z, rel='lamd')
    Nsq = B.node('Nsq', Nn ** 2, rel='plain')
    Gf = B.node('Gf', (st + EN / 2) * Nsq - st ** 2, rel='lamd')
    NG = B.node('NG', Nn * Gf, rel='plain')
    LBu = B.node('LBu', lam * Bmu, rel='lamd')
    LBz = B.node('LBz', lam * Bmz, rel='lamd')
    Fu = B.node('Fu', LBu * NG / 2, rel='lamd')
    Fz = B.node('Fz', LBz * NG / 2, rel='lamd')
    RN = lam_rho_nodes(B, LC, LLN)
    Dt, nRt, nZt = RN['Dt'], RN['nRt'], RN['nZt']
    der = {}
    for nm, base, W3d, Kb, Kd, Fd, Yb in [('Dtu', Du, W3u, KD, KDu, Fu, 'YDt'), ('Dtz', Dz, W3z, KD, KDz, Fz, 'YDt'),
                                          ('nRtu', nRu, W3u, KR, KRu, Fu, 'YnRt'), ('nRtz', nRz, W3z, KR, KRz, Fz, 'YnRt'),
                                          ('nZtu', nZu, W3u, KZ, KZu, Fu, 'YnZt'), ('nZtz', nZz, W3z, KZ, KZz, Fz, 'YnZt')]:
        Yd = B.node('Y' + nm, W3d * Kb + W3 * Kd, rel='plain')
        der[nm] = B.node(nm + 'F', base + (Fd * RN[Yb] + Fl * Yd) / 2 ** 9, rel='rho')
    Dtu, Dtz, nRtu, nRtz, nZtu, nZtz = (der[k] for k in ['Dtu', 'Dtz', 'nRtu', 'nRtz', 'nZtu', 'nZtz'])
    Ptor = B.node('PtorF', (nRt * Dt - Dt * (nRtu * sU + nRtz * sZ) + nRt * (Dtu * sU + Dtz * sZ)) * sZ
                  - (nZt * Dt - Dt * (nZtu * sU + nZtz * sZ) + nZt * (Dtu * sU + Dtz * sZ)) * sU, rel='Pof')
    Dt3 = B.node('Dt3F', Dt ** 3, rel='plain')
    Fv = B.node('FF', Dt3 * W02, rel='plain')
    qis = newton_inv(B.PL, B.sym[Fv])
    sqi = B.fam(qis, 0, 'qiF', X='qi', kind='data')
    rX = B.node('XF', sqi * Fv - B.st ** 2, norm=True, role='X')
    Y = B.node('YF', R3 * Ptor * sqi, rel='plain')
    vY, vDt, vW0 = B.sym[Y], B.sym[Dt], B.sym[W0]
    gD = B.PL.grids(vDt)
    gW = B.PL.grids(vW0)
    d0 = Fr(2126414735707981, 2 ** 51)
    w0 = -Fr(5398240620830529, 2 ** 59)
    rDd = B.node('DdevF', Dt - sp.Rational(d0.numerator, d0.denominator) * B.st, norm=True, role='Ddev')
    rWd = B.node('WdevF', W0 - sp.Rational(w0.numerator, w0.denominator) * B.st, norm=True, role='Wdev')
    gY = B.PL.grids(vY)
    Ym0 = Fr(gY[LDC][LN][LM], 2 ** LS)
    Ym1 = sum(Fr(abs(gY[LDC + k][LN][LM]), 2 ** LS) for k in range(1, LDC + 1)) * 2
    Yn, Ye, Xn = B.PL.B[vY], B.PL.E[vY], rX['rad']
    print('L: |X| <= %.3e |Y| <= %.4f <Y> >= %.6f - %.2e  |D-d0| <= %.4f  |W0-w0| <= %.5f   E(Y) = %.2e' % (
        float(Xn), float(Yn + Ye), float(Ym0), float(Ym1), float(rDd['rad'] / abs(rDd['cscale'])),
        float(rWd['rad'] / abs(rWd['cscale'])), float(Ye)), flush=True)
    # the rho = 1/256 low-resolution torus (constant in theta'), for the profile of the family
    ou, oz = LEANL['sdLM_Uo'], LEANL['sdLM_Zo']
    sUo = B.fam(ou, 0, 'Uo', X='uS', kind='old')
    sZo = B.fam(oz, 1, 'Zo', X='zS', kind='old')
    sAo = B.fam(ou, 3, 'Ao', X='dTh uS', kind='oldd', sym=(0, 1, 0))
    sBo = B.fam(oz, 0, 'Bo', X='dTh zS', kind='oldd', sym=(0, 1, 0))
    rdo = [B.node(nm, a - b, norm=True, role='old') for nm, a, b in
           [('dUo', sU, sUo), ('dZo', sZ, sZo), ('dAo', sA, sAo), ('dBo', sB, sBo)]]
    print('L: |K(x) - K_S| <= %s' % [float(r_['rad']) for r_ in rdo], flush=True)
    res['L'] = L_
    res['Lout'] = dict(d0=d0, w0=w0, Ym0=Ym0, Ym1=Ym1)

os.makedirs(OUTD, exist_ok=True)


def export(B):
    PL = B.PL
    nodes = [{k: v for k, v in r.items() if k not in ('expr',)} for r in PL.nodes]
    meta = {v: {k: x for k, x in m.items() if k != 'rec'} for v, m in B.meta.items()}
    norms = [{k: v for k, v in r.items() if k not in ('expr',)} for r in B.norms]
    return dict(N=PL.N, M=PL.M, D=PL.D, S=PL.S, nvar=PL.nvar, W=dict(PL.W), Bx=dict(PL.Bx), L=dict(PL.L),
                B=dict(PL.B), E=dict(PL.E), kind=dict(PL.kind), names=dict(PL.names), fam=dict(PL.fam),
                nodes=nodes, normrec=dict(getattr(PL, 'normrec', {})), meta=meta, norms=norms,
                vstep=getattr(B, 'vstep', None), vsteps=getattr(B, 'vsteps', None))


pickle.dump({k: (export(v) if k in ('H', 'L') else v) for k, v in res.items()},
            open(OUTD + '/lam_cert_%s.pkl' % WHICH, 'wb'))
print('total %.0fs' % (time.time() - t0))
