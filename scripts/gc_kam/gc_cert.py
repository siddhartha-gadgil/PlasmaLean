"""UNTRUSTED driver: the two ball pipelines of the guiding-centre torus certificate (rho = 1/256).

* low resolution (box |k| <= 16, |m| <= 12, scale 2^-60): balls at every torus mu-close to K0 for the
  field values, the u/z-derivatives, the torsion and the twist (admissibility of the KAM step);
* high resolution (box |k| <= 40, |m| <= 30, scale 2^-101): the residual of K0 (the e0 of KAM),
  and the distances from K0 to the low-resolution torus K_S.

Produces /tmp/gcw/gc_cert.pkl with both pipelines and the metadata of every variable (Lean true
value, relation proof hints).  Usage: python gc_cert.py
"""
import sys, os, time, pickle, math
import numpy as np, sympy as sp, gmpy2
from gmpy2 import mpfr
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
from flow_torus import index_sets
import gcmodel as G
from ballcert import Pipeline, up
from slp import to_tree

gmpy2.get_context().precision = 300
NT, MT = 32, 22
Q, Iq = 96, 10888383889117653077957113864
MU = Fr(1, 10 ** 12)
LN, LM, LS, LF = 16, 12, 60, 80
HN, HM, HS, HF = 40, 30, 101, 112

d = np.load('/tmp/k2work/gc_torus_hp_1_256.npz', allow_pickle=True)
Is, Iz = index_sets(NT, MT)
acoef = [mpfr(x) for x in d['a']]
bcoef = [mpfr(x) for x in d['b']]


def torus_grids(N, M, S):
    GU = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    GZ = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for (k, m), x in zip(Is, acoef):
        if abs(k) > N or abs(m) > M:
            continue
        if (k, m) == (0, 0):
            GU[N][M] = int(gmpy2.rint((x - 1) * mpfr(2) ** S / 2)) * 2
        else:
            v = int(gmpy2.rint(x * mpfr(2) ** (S - 1)))
            GU[N + k][M + m] = v
            GU[N - k][M - m] = v
    for (k, m), x in zip(Iz, bcoef):
        if abs(k) > N or abs(m) > M:
            continue
        v = int(gmpy2.rint(x * mpfr(2) ** (S - 1)))
        GZ[N + k][M + m] = v
        GZ[N - k][M - m] = -v
    return GU, GZ


def wgrid(Gr, N, M, f):
    return [[f(i - N, j - M) * Gr[i][j] for j in range(2 * M + 1)] for i in range(2 * N + 1)]


def embed(Gl, Nl, Ml, Nh, Mh, s):
    dN, dM = Nh - Nl, Mh - Ml
    Gh = [[0] * (2 * Mh + 1) for _ in range(2 * Nh + 1)]
    for i in range(2 * Nl + 1):
        for j in range(2 * Ml + 1):
            Gh[i + dN][j + dM] = Gl[i][j] * 2 ** s
    return Gh


class Builder:
    """A pipeline plus sympy symbols and Lean metadata of its variables."""

    def __init__(self, PL, prefix):
        self.PL = PL
        self.prefix = prefix
        self.sym = {}
        self.meta = {}          # var -> dict(X=..., kind=..., rel=...)
        self.norms = []         # norm nodes (records + meta)

    def S(self, name, var, **meta):
        s_ = sp.Symbol(name)
        self.sym[s_] = var
        self.meta[var] = dict(name=name, **meta)
        return s_

    def const(self, kind, name, X):
        return self.S(name, self.PL.add_const(kind, name), X=X, kind='const')

    def grid(self, Gr, p, name, X, kind='input', E=Fr(0), Lstatic=None, **kw):
        return self.S(name, self.PL.add_grid(Gr, p, name, E=E, Lstatic=Lstatic), X=X, kind=kind, **kw)

    def node(self, name, expr, X=None, norm=False, quiet=False, Erad=None, **meta):
        PL = self.PL
        syms = {k: v for k, v in self.sym.items() if expr.has(k)}
        st = [k for k, v in self.sym.items() if v == 0][0]
        sV = [k for k, v in self.sym.items() if v == 1][0]
        syms[st] = 0
        syms[sV] = 1
        tr, c = to_tree(expr, syms, PL.W, 0, 1)
        rec = PL.node(name, tr, 0 if norm else c, Erad=Erad)
        rec['cscale'] = c
        rec['expr'] = expr
        if not quiet:
            print('%s %-8s w=%s c=%s b=%d slots=%d rad=%.3e beta=%.3e dmaj=%.3e' % (
                self.prefix, name, rec['w'], c, rec['b'], rec['W'] * rec['R'],
                float(rec['rad'] / (abs(c) if norm else 1)), float(rec['beta']), float(rec['dmaj'])),
                flush=True)
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
    N, M, S = PL.N, PL.M, PL.S
    SC = Pipeline(N, M, S, PL.F, 'scratch')
    ts = SC.add_const('T', 't')
    SC.add_const('V', 'V')
    Eg = SC.add_grid(PL.G[Evar], PL.W[Evar][2], 'E')
    cur = SC.add_grid([[(2 ** S if (i, j) == (N, M) else 0) for j in range(2 * M + 1)]
                       for i in range(2 * N + 1)], 0, 'V')
    for it in range(12):
        e3 = ('mul', ('sub', ('mul', ('cst', 3), ('mul', ('var', ts), ('mul', ('var', ts), ('var', ts)))),
                      ('mul', ('add', ('var', ts), ('var', Eg)), ('mul', ('var', cur), ('var', cur)))),
              ('var', cur))
        Qg = SC.node('it', e3, 2, record=False)
        diff = max(abs(Qg[i][j] - SC.G[cur][i][j]) for i in range(2 * N + 1) for j in range(2 * M + 1))
        cur = SC.add_grid(Qg, 0, 'V')
        if diff == 0:
            break
    return SC.G[cur]


def newton_inv(PL, Fvar):
    N, M, S = PL.N, PL.M, PL.S
    SC = Pipeline(N, M, S, PL.F, 'scratch')
    ts = SC.add_const('T', 't')
    SC.add_const('V', 'V')
    Fg = SC.add_grid(PL.G[Fvar], PL.W[Fvar][2], 'F')
    q0 = int(round(2 ** S / (PL.G[Fvar][N][M] / 2 ** S)))
    cur = SC.add_grid([[(q0 if (i, j) == (N, M) else 0) for j in range(2 * M + 1)]
                       for i in range(2 * N + 1)], 0, 'q')
    for it in range(60):
        e2 = ('mul', ('sub', ('mul', ('cst', 2), ('mul', ('var', ts), ('var', ts))),
                      ('mul', ('var', Fg), ('var', cur))), ('var', cur))
        Qg = SC.node('it', e2, 1, record=False)
        diff = max(abs(Qg[i][j] - SC.G[cur][i][j]) for i in range(2 * N + 1) for j in range(2 * M + 1))
        cur = SC.add_grid(Qg, 0, 'q')
        if diff <= 1:
            break
    return SC.G[cur]


u, z, c, s = G.u, G.z, G.c, G.s


def phiP(e):
    return sp.expand(sp.diff(e, c) * (-2 * s) + sp.diff(e, s) * (2 * c))


POL = dict(G.ALLP)
POL['PdP'] = sp.expand(sp.diff(POL['PuP'], u))
SECOND = {}
for b_ in ['D', 'nR', 'nZ']:
    X0 = G.BASE[b_ + 'p']
    for k_, ex in [('uuP', sp.diff(X0, u, 2)), ('uzP', sp.diff(X0, u, z)), ('zzP', sp.diff(X0, z, 2)),
                   ('uphP', sp.diff(phiP(X0), u)), ('zphP', sp.diff(phiP(X0), z))]:
        POL[b_ + k_] = sp.expand(ex)
        SECOND[b_ + k_] = True
LEAN_LEAF = {'Dp': 'KamNewton.Dp', 'nRp': 'KamNewton.nRp', 'nZp': 'KamNewton.nZp'}


def leafname(n):
    return LEAN_LEAF.get(n, n)


def build_common(B, K, low):
    """Leaf polynomials, q and its derivatives, E, the node, W, the brackets, D~, n~ (true values at
    the torus point K = 'KH' or 'KL')."""
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
        X = '%s ^ %d * %s ^ %d' % (B.uname, i, B.zname, j)
        mono[(i, j)] = B.node('m%d%d' % (i, j), mono[a1] * mono[a2], X=X, quiet=True, rel='mono')

    def leafexpr(n):
        tot = 0
        for (i, j, k, l), co in sp.Poly(POL[n], u, z, c, s).terms():
            tot += sp.Rational(co) * (mono[(i, j)] if (i, j) != (0, 0) else st) * sC ** k * sS ** l
        return tot
    L = {}
    for n in leafs:
        L[n] = B.node(n, leafexpr(n), X='PolyExpr.eval %s %s' % (K, leafname(n)), quiet=True,
                      rel='leaf', leaf=leafname(n))
    R = st + sU
    Rl = '(1 + %s)' % B.uname
    ev = lambda n: 'PolyExpr.eval %s %s' % (K, leafname(n))
    evS = lambda n: 'PolyExprS.eval %s %s' % (K, n)
    RD = B.node('RD', R * L['Dp'], X='%s * %s' % (Rl, ev('Dp')), rel='plain')
    RDu = B.node('RDu', R * L['DuP'], X='%s * %s' % (Rl, ev('DuP')), rel='plain')
    RDz = B.node('RDz', R * L['DzP'], X='%s * %s' % (Rl, ev('DzP')), rel='plain')
    RDph = B.node('RDph', R * L['DphP'], X='%s * %s' % (Rl, ev('DphP')), rel='plain')
    D, nR, nZ = L['Dp'], L['nRp'], L['nZp']
    q = B.node('q', nR ** 2 + RD ** 2 + nZ ** 2, X=evS('eq'), rel='unfold', unfold=['eq', 'eR'])
    qR = B.node('qR', 2 * nR * L['nRuP'] + 2 * RD * D + 2 * RD * RDu + 2 * nZ * L['nZuP'], X=evS('eqR'),
                rel='unfold', unfold=['eqR', 'eR'])
    qz = B.node('qz', 2 * nR * L['nRzP'] + 2 * RD * RDz + 2 * nZ * L['nZzP'], X=evS('eqz'),
                rel='unfold', unfold=['eqz', 'eR'])
    qph = B.node('qph', 2 * nR * L['nRphP'] + 2 * RD * RDph + 2 * nZ * L['nZphP'], X=evS('eqph'),
                 rel='unfold', unfold=['eqph', 'eR'])
    P2 = B.node('P2', L['PuP'] ** 2, X='%s ^ 2' % ev('PuP'), rel='plain')
    E = B.node('E', q * P2 - st ** 2, X=ev('EpP'), rel='E')
    Evar = B.sym[E]
    V0g = newton_isqrt(PL, Evar)
    sV0 = B.grid(V0g, 0, 'V0', X='%s %d' % (B.xname, PL.nvar), kind='data')
    rVm1 = B.node('Vm1', sV0 - st, norm=True, role='Vm1')
    rV2 = B.node('V2m1', sV0 ** 2 - st ** 2, norm=True, role='V2m1')
    reta = B.node('eta', sV0 ** 2 * (st + E) - st ** 3, norm=True, role='eta')
    aV, n2, eta = rVm1['rad'], rV2['rad'], reta['rad']
    # rational choices (checked in Lean)
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
                                                       float(epsV)))
    sVn = B.grid(V0g, 0, 'Vn', X=evS('eV'), kind='vnode', E=epsV)
    W = B.node('W', L['PuP'] * sVn, X=evS('eW'), rel='unfold', unfold=['eW'])
    W2 = B.node('W2', W ** 2, X='%s ^ 2' % evS('eW'), rel='plain')
    W3 = B.node('W3', W2 * W, X=evS('eW3'), rel='unfold', unfold=['eW3'])
    R2 = B.node('R2', R ** 2, X='%s ^ 2' % Rl, rel='plain')
    R3 = B.node('R3', R2 * R, X='%s ^ 3' % Rl, rel='plain')
    A1 = B.node('A1', R * qR, X='%s * %s' % (Rl, evS('eqR')), rel='plain')
    A2 = B.node('A2', R * qz, X='%s * %s' % (Rl, evS('eqz')), rel='plain')
    K1 = B.node('K1', nZ * A1 - 8 * nZ * q - nR * A2,
                X='%s * (%s * %s) - 8 * %s * %s - %s * (%s * %s)' % (
                    ev('nZp'), Rl, evS('eqR'), ev('nZp'), evS('eq'), ev('nRp'), Rl, evS('eqz')), rel='plain')
    K2 = B.node('K2', RD * A2 - nZ * qph,
                X='%s * %s * (%s * %s) - %s * %s' % (Rl, ev('Dp'), Rl, evS('eqz'), ev('nZp'), evS('eqph')),
                rel='plain')
    K3 = B.node('K3', nR * qph - RD * A1 + 8 * RD * q,
                X='%s * %s - %s * %s * (%s * %s) + 8 * (%s * %s) * %s' % (
                    ev('nRp'), evS('eqph'), Rl, ev('Dp'), Rl, evS('eqR'), Rl, ev('Dp'), evS('eq')), rel='plain')
    KD = B.node('KD', R2 * K1, X=evS('eKD'), rel='unfold', unfold=['eKD', 'eR'])
    KR = B.node('KR', R3 * K2, X=evS('eKR'), rel='unfold', unfold=['eKR', 'eR'])
    KZ = B.node('KZ', R3 * K3, X=evS('eKZ'), rel='unfold', unfold=['eKZ', 'eR'])
    Dt = B.node('Dt', D + W3 * KD / 512, X=evS('(gcD (1 / 256))'), rel='corr', unfold=['gcD'],
                hint='W3 * KD')
    nRt = B.node('nRt', nR + W3 * KR / 512, X=evS('(gcNR (1 / 256))'), rel='corr', unfold=['gcNR'],
                 hint='W3 * KR')
    nZt = B.node('nZt', nZ + W3 * KZ / 512, X=evS('(gcNZ (1 / 256))'), rel='corr', unfold=['gcNZ'],
                 hint='W3 * KZ')
    return dict(L=L, R=R, RD=RD, RDu=RDu, RDz=RDz, RDph=RDph, q=q, qR=qR, qz=qz, qph=qph, P2=P2, E=E,
                Vn=sVn, W=W, W2=W2, W3=W3, R2=R2, R3=R3, A1=A1, A2=A2, K1=K1, K2=K2, K3=K3, KD=KD, KR=KR,
                KZ=KZ, Dt=Dt, nRt=nRt, nZt=nZt)


def make_builder(N, M, S, F, prefix, xname, uname, zname):
    PL = Pipeline(N, M, S, F, prefix)
    B = Builder(PL, prefix)
    B.xname, B.uname, B.zname = xname, uname, zname
    B.st = B.const('T', 't', '1')
    B.sV = B.const('V', 'V', '1')
    B.sC = B.const('C', 'c', 'cS')
    B.sS = B.const('S', 's', 'sS')
    return B


# ======================================================================== low-res grids
GUl, GZl = torus_grids(LN, LM, LS)

# ======================================================================== high resolution
t0 = time.time()
H = make_builder(HN, HM, HS, HF, 'H', 'xH', 'u₀G', 'z₀G')
GUh, GZh = torus_grids(HN, HM, HS)
H.sU = H.grid(GUh, 0, 'U', X='u₀G')
H.sZ = H.grid(GZh, 1, 'Z', X='z₀G')
LdataH = (2 * HN + 1) * (2 * HM + 1)
LdataL = (2 * LN + 1) * (2 * LM + 1)
H.sLRx = H.grid(wgrid(GUh, HN, HM, lambda k, m: Iq * k + 2 ** (Q + 1) * m), 3, 'LRx',
                X='(2 : ℂ) ^ 96 • Lt KamTorusA.iota u₀G', kind='Linput',
                Lstatic=LdataH * (Iq * HN + 2 ** 97 * HM) * 2 ** HF)
H.sLZx = H.grid(wgrid(GZh, HN, HM, lambda k, m: Iq * k + 2 ** (Q + 1) * m), 0, 'LZx',
                X='(2 : ℂ) ^ 96 • Lt KamTorusA.iota z₀G', kind='Linput',
                Lstatic=LdataH * (Iq * HN + 2 ** 97 * HM) * 2 ** HF)
# the derivatives of K0 and the embedded low-resolution torus (distances)
H.sthU = H.grid(wgrid(GUh, HN, HM, lambda k, m: k), 3, 'thU', X='dTh u₀G', kind='derived',
                Lstatic=LdataH * HN * 2 ** HF)
H.sthZ = H.grid(wgrid(GZh, HN, HM, lambda k, m: k), 0, 'thZ', X='dTh z₀G', kind='derived',
                Lstatic=LdataH * HN * 2 ** HF)
GUe = embed(GUl, LN, LM, HN, HM, HS - LS)
GZe = embed(GZl, LN, LM, HN, HM, HS - LS)
H.sUe = H.grid(GUe, 0, 'Ue', X='uSG', kind='embed', Lstatic=LdataH * 2 ** (HS - LS) * 2 ** LF)
H.sZe = H.grid(GZe, 1, 'Ze', X='zSG', kind='embed', Lstatic=LdataH * 2 ** (HS - LS) * 2 ** LF)
H.sthUe = H.grid(wgrid(GUe, HN, HM, lambda k, m: k), 3, 'thUe', X='dTh uSG', kind='derived',
                 Lstatic=LdataH * HN * 2 ** (HS - LS) * 2 ** LF)
H.sthZe = H.grid(wgrid(GZe, HN, HM, lambda k, m: k), 0, 'thZe', X='dTh zSG', kind='derived',
                 Lstatic=LdataH * HN * 2 ** (HS - LS) * 2 ** LF)
# 2^Q |iota - iota_q| <= 2^96 / 10^29
dIQ = Fr(2 ** 96, 10 ** 29)
H.PL.E[H.sym[H.sLRx]] = up(dIQ * H.PL.B[H.sym[H.sthU]], 4)
H.PL.E[H.sym[H.sLZx]] = up(dIQ * H.PL.B[H.sym[H.sthZ]], 4)
rdu = H.node('dU', H.sU - H.sUe, norm=True, role='dist')
rdz = H.node('dZ', H.sZ - H.sZe, norm=True, role='dist')
rda = H.node('dA', H.sthU - H.sthUe, norm=True, role='dist')
rdb = H.node('dB', H.sthZ - H.sthZe, norm=True, role='dist')
DIST = [up(r['rad'], 3) for r in (rdu, rdz, rda, rdb)]
print('distances K0 - K_S: %s' % [float(x) for x in DIST])
HC = build_common(H, 'KH', low=False)
rR = H.node('resR', HC['Dt'] * H.sLRx - 2 ** Q * HC['nRt'] * H.st, norm=True, role='resR')
rZ = H.node('resZ', HC['Dt'] * H.sLZx - 2 ** Q * HC['nZt'] * H.st, norm=True, role='resZ')
e0R, e0Z = rR['rad'] / 2 ** Q, rZ['rad'] / 2 ** Q
print('e0: resR <= %.4e  resZ <= %.4e   (%.0fs)' % (float(e0R), float(e0Z), time.time() - t0))

# ======================================================================== low resolution
L_ = make_builder(LN, LM, LS, LF, 'L', 'xL', 'u', 'z')
EIN = [MU + x for x in DIST]
L_.sU = L_.grid(GUl, 0, 'U', X='u', kind='torus', E=up(EIN[0], 3))
L_.sZ = L_.grid(GZl, 1, 'Z', X='z', kind='torus', E=up(EIN[1], 3))
L_.sA = L_.grid(wgrid(GUl, LN, LM, lambda k, m: k), 3, 'A', X='dTh u', kind='torus', E=up(EIN[2], 3),
                Lstatic=LdataL * LN * 2 ** LF)
L_.sB = L_.grid(wgrid(GZl, LN, LM, lambda k, m: k), 0, 'B', X='dTh z', kind='torus', E=up(EIN[3], 3),
                Lstatic=LdataL * LN * 2 ** LF)
LC = build_common(L_, 'KL', low=True)
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
KD, KR, KZ, Dt, nRt, nZt = LC['KD'], LC['KR'], LC['KZ'], LC['Dt'], LC['nRt'], LC['nZt']
dv = lambda e, i: 'PolyExprS.deriv KL (Pi.single %d 1) %s' % (i, e)
qRu = B.node('qRu', 2 * nRu ** 2 + 2 * nR * nRuu + 2 * D ** 2 + 8 * RD * Du + 2 * RDu ** 2 + 2 * RD * R * Duu
             + 2 * nZu ** 2 + 2 * nZ * nZuu, X=dv('eqR', 0), rel='deriv', unfold=['eqR', 'eR'])
qRz = B.node('qRz', 2 * nRz * nRu + 2 * nR * nRuz + 4 * RD * Dz + 2 * R * RDz * Du + 2 * RD * R * Duz
             + 2 * nZz * nZu + 2 * nZ * nZuz, X=dv('eqR', 1), rel='deriv', unfold=['eqR', 'eR'])
qzz = B.node('qzz', 2 * nRz ** 2 + 2 * nR * nRzz + 2 * RDz ** 2 + 2 * RD * R * Dzz + 2 * nZz ** 2 + 2 * nZ * nZzz,
             X=dv('eqz', 1), rel='deriv', unfold=['eqz', 'eR'])
qzu = B.node('qzu', 2 * nRu * nRz + 2 * nR * nRuz + 4 * RD * Dz + 2 * RDu * RDz + 2 * RD * R * Duz
             + 2 * nZu * nZz + 2 * nZ * nZuz, X=dv('eqz', 0), rel='deriv', unfold=['eqz', 'eR'])
qphu = B.node('qphu', 2 * nRu * nRph + 2 * nR * nRuph + 4 * RD * Dph + 2 * RDu * RDph + 2 * RD * R * Duph
              + 2 * nZu * nZph + 2 * nZ * nZuph, X=dv('eqph', 0), rel='deriv', unfold=['eqph', 'eR'])
qphz = B.node('qphz', 2 * nRz * nRph + 2 * nR * nRzph + 2 * RDz * RDph + 2 * RD * R * Dzph + 2 * nZz * nZph
              + 2 * nZ * nZzph, X=dv('eqph', 1), rel='deriv', unfold=['eqph', 'eR'])
qu = B.node('qu', 2 * nR * nRu + 2 * RD * D + 2 * RD * RDu + 2 * nZ * nZu, X=dv('eq', 0), rel='deriv',
            unfold=['eq', 'eR'])
qzd = B.node('qzd', 2 * nR * nRz + 2 * RD * RDz + 2 * nZ * nZz, X=dv('eq', 1), rel='deriv', unfold=['eq', 'eR'])
Eu = B.node('Eu', qu * P2 + 2 * q * P * Pd, X='pd KL 0 EpP', rel='Ed', idx=0)
Ez = B.node('Ez', qzd * P2, X='pd KL 1 EpP', rel='Ed', idx=1)
V3 = B.node('V3', sVn ** 3, X='PolyExprS.eval KL eV ^ 3', rel='plain')
Wu = B.node('Wu', Pd * sVn - P * V3 * Eu / 2, X=dv('eW', 0), rel='dW', unfold=['eW', 'eV'], hint='P * V3 * Eu')
Wz = B.node('Wz', -P * V3 * Ez / 2, X=dv('eW', 1), rel='dW', unfold=['eW', 'eV'], hint='P * V3 * Ez')
W3u = B.node('W3u', 3 * W2 * Wu, X=dv('eW3', 0), rel='deriv', unfold=['eW3'])
W3z = B.node('W3z', 3 * W2 * Wz, X=dv('eW3', 1), rel='deriv', unfold=['eW3'])
KDu = B.node('KDu', 2 * R * K1 + R2 * (nZu * A1 + nZ * qR + nZ * R * qRu - 8 * nZu * q - 8 * nZ * qu - nRu * A2
                                       - nR * qz - nR * R * qzu),
             X=dv('eKD', 0), rel='deriv', unfold=['eKD', 'eR'])
KDz = B.node('KDz', R2 * (nZz * A1 + nZ * R * qRz - 8 * nZz * q - 8 * nZ * qzd - nRz * A2 - nR * R * qzz),
             X=dv('eKD', 1), rel='deriv', unfold=['eKD', 'eR'])
KRu = B.node('KRu', 3 * R2 * K2 + R3 * (2 * RD * qz + R2 * Du * qz + R2 * D * qzu - nZu * qph - nZ * qphu),
             X=dv('eKR', 0), rel='deriv', unfold=['eKR', 'eR'])
KRz = B.node('KRz', R3 * (R2 * Dz * qz + R2 * D * qzz - nZz * qph - nZ * qphz),
             X=dv('eKR', 1), rel='deriv', unfold=['eKR', 'eR'])
KZu = B.node('KZu', 3 * R2 * K3 + R3 * (nRu * qph + nR * qphu - 2 * RD * qR - R2 * Du * qR - R2 * D * qRu + 8 * D * q
                                        + 8 * RDu * q + 8 * RD * qu),
             X=dv('eKZ', 0), rel='deriv', unfold=['eKZ', 'eR'])
KZz = B.node('KZz', R3 * (nRz * qph + nR * qphz - R2 * Dz * qR - R2 * D * qRz + 8 * RDz * q + 8 * RD * qzd),
             X=dv('eKZ', 1), rel='deriv', unfold=['eKZ', 'eR'])
Dtu = B.node('Dtu', Du + (W3u * KD + W3 * KDu) / 512, X='pdS KL 0 (gcD (1 / 256))', rel='dcorr',
             unfold=['gcD'], hint='W3u * KD + W3 * KDu')
Dtz = B.node('Dtz', Dz + (W3z * KD + W3 * KDz) / 512, X='pdS KL 1 (gcD (1 / 256))', rel='dcorr',
             unfold=['gcD'], hint='W3z * KD + W3 * KDz')
nRtu = B.node('nRtu', nRu + (W3u * KR + W3 * KRu) / 512, X='pdS KL 0 (gcNR (1 / 256))', rel='dcorr',
              unfold=['gcNR'], hint='W3u * KR + W3 * KRu')
nRtz = B.node('nRtz', nRz + (W3z * KR + W3 * KRz) / 512, X='pdS KL 1 (gcNR (1 / 256))', rel='dcorr',
              unfold=['gcNR'], hint='W3z * KR + W3 * KRz')
nZtu = B.node('nZtu', nZu + (W3u * KZ + W3 * KZu) / 512, X='pdS KL 0 (gcNZ (1 / 256))', rel='dcorr',
              unfold=['gcNZ'], hint='W3u * KZ + W3 * KZu')
nZtz = B.node('nZtz', nZz + (W3z * KZ + W3 * KZz) / 512, X='pdS KL 1 (gcNZ (1 / 256))', rel='dcorr',
              unfold=['gcNZ'], hint='W3z * KZ + W3 * KZz')
sU, sZ, sA, sB = B.sU, B.sZ, B.sA, B.sB
Ptor = B.node('Ptor', (nRt * Dt - Dt * (nRtu * sU + nRtz * sZ) + nRt * (Dtu * sU + Dtz * sZ)) * sZ
              - (nZt * Dt - Dt * (nZtu * sU + nZtz * sZ) + nZt * (Dtu * sU + Dtz * sZ)) * sU,
              X='(gcFlow (1 / 256)).Pof u z', rel='Pof')
W0 = B.node('W0', sA * sZ - sB * sU, X='W0of u z', rel='W0')
Dt3 = B.node('Dt3', Dt ** 3, X='PolyExprS.eval KL (gcD (1 / 256)) ^ 3', rel='plain')
W02 = B.node('W02', W0 ** 2, X='W0of u z ^ 2', rel='plain')
Fv = B.node('F', Dt3 * W02, X='PolyExprS.eval KL (gcD (1 / 256)) ^ 3 * W0of u z ^ 2', rel='plain')
qig = newton_inv(B.PL, B.sym[Fv])
sqi = B.grid(qig, 0, 'qi', X='xL %d' % B.PL.nvar, kind='data')
rX = B.node('X', sqi * Fv - B.st ** 2, norm=True, role='X')
Y = B.node('Y', R3 * Ptor * sqi, X='(1 + u) ^ 3 * (gcFlow (1 / 256)).Pof u z * xL %d' % B.sym[sqi], rel='plain')
vY, vDt, vW0 = B.sym[Y], B.sym[Dt], B.sym[W0]
d0 = Fr(B.PL.G[vDt][LN][LM], 2 ** LS)
w0 = Fr(B.PL.G[vW0][LN][LM], 2 ** LS)
rDd = B.node("Ddev", Dt - sp.Rational(d0.numerator, d0.denominator) * B.st, norm=True, role='Ddev')
rWd = B.node("Wdev", W0 - sp.Rational(w0.numerator, w0.denominator) * B.st, norm=True, role='Wdev')
Yn, Ye, Xn = B.PL.B[vY], B.PL.E[vY], rX['rad']
Ymean = Fr(B.PL.G[vY][LN][LM], 2 ** LS)
print('L: |X| <= %.3e |Y| <= %.4f <Y> = %.6f  |D-d0| <= %.4f (d0 %.5f)  |W0-w0| <= %.5f (w0 %.6f)' % (
    float(Xn), float(Yn + Ye), float(Ymean), float(rDd['rad'] / abs(rDd['cscale'])), float(d0),
    float(rWd['rad'] / abs(rWd['cscale'])), float(w0)))
print('total %.0fs' % (time.time() - t0))


def export(B):
    PL = B.PL
    nodes = []
    for r in PL.nodes:
        r2 = {k: v for k, v in r.items() if k not in ('expr',)}
        nodes.append(r2)
    meta = {}
    for v, m in B.meta.items():
        meta[v] = {k: x for k, x in m.items() if k != 'rec'}
    norms = []
    for r in B.norms:
        norms.append({k: v for k, v in r.items() if k not in ('expr',)})
    return dict(N=PL.N, M=PL.M, S=PL.S, F=PL.F, nvar=PL.nvar, W=dict(PL.W), Bx=dict(PL.Bx), L=dict(PL.L),
                G=dict(PL.G), B=dict(PL.B), E=dict(PL.E), kind=dict(PL.kind), names=dict(PL.names),
                nodes=nodes, normrec=dict(PL.normrec), meta=meta, norms=norms,
                vstep=getattr(B, 'vstep', None))


pickle.dump(dict(H=export(H), L=export(L_), DIST=DIST, e0=(e0R, e0Z), d0=d0, w0=w0, Ymean=Ymean, MU=MU),
            open('/tmp/gcw/gc_cert.pkl', 'wb'))
