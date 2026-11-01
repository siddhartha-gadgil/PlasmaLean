"""UNTRUSTED generator.  The low-resolution admissibility chain of Dommaschk torus C (N-33 plan item 8).

A KronBall chain (`Certificates/KronBall`, the guiding-centre `…TorusChainL` pattern, with the strip
weights of `Design/DommaschkKamCKronW`) evaluated at ONE fixed low-resolution surrogate torus
(xU, xZ) (the data torus `Design/DommaschkKamCData` truncated to NL x ML and rounded to 2^-SL), in the
oracle angle psi_o = 2 phi: every input is an exact centre (radius 0), so the radii are only the
truncation and rounding errors of the nodes.  The bounds at every torus mu-close to the data torus
follow from the surrogate bounds by explicit transfer lemmas (Lipschitz majorants of the u-form
polynomials, product rules, perturbed approximate inverses), in `Design/DommaschkKamCAdm`.

Chain (variables in order): constants t, V, C = cos psi_o, S = sin psi_o; data U, Z; derived
A = d_theta U, B = d_theta Z, Pu = d_psi U, Pz = d_psi Z; R = R0 + U; the powers R^a, z^b and the
monomials R^a z^b; the field polynomials D, D_u, D_z, n_R, ..., n_z,z in R-form (DkPoly lists
`dDR`, `R * dnRh`, `dnZR` of Design/DommaschkKamFieldData and their dU, dZ); the frame vectors
V0R = U - a_R, V0Z = Z - a_z; W0 = A V0Z - B V0R; the centre derivatives a_R', a_z'; the torsion
numerator P (the `Pp` formula) through D^2, G1..G3, Y_R, Y_Z; the approximate inverses qD, qW, qR
(data: rounded truncated Fourier series of 1/D, 1/W0, 1/R at the surrogate) with the norm nodes
||qD D - 1||, ||qW W0 - 1||, ||qR R - 1||; the transport norms ||2^Q Lt_{iota_q} U||, ...; the torsion
centre Y = R^7 P qD^3 qW^2.

Validation (exact, before writing): the ball engine `adm_ball.py` recomputes every node with gmpy2
integers exactly as the Lean kernel quantities (`nodeKw`, `normKw`, `centerKw`), every radius and
bound is a rational rounded outward and re-checked, the final admissibility constants are recomputed
in Fractions from the emitted rationals, and the generated trees of the sparse polynomials mirror the
Lean functions `polyT`/`termT` (the Lean kernel re-evaluates them).

(needs numpy and gmpy2, e.g. the venv /tmp/dqa-venv; run with -I)
usage: python emit_adm.py [--NL 24 --ML 28 --SL 64] [--report] [--emit] [--tag C|A] [--out-dir DIR]
"""
import argparse
import json
import math
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import adm_ball as AB                                         # noqa: E402
import dk_torus as DT                                         # noqa: E402

P_EXP, E_EXP = 68553, 16          # e^{9/200} <= 68553 / 2^16
NORING = {'W0', 'DD', 'G1', 'G2', 'G3', 'YR', 'YZ', 'P', 'qD2', 'qD3', 'qW2', 'qDW', 'Y'}
CHUNK = 4                         # distinct monomials per polynomial chunk node
R0 = Fr(29, 32)
MU = Fr(1, 10 ** 12)
IOTA_ABS_UP = Fr(2417, 10000)     # |iota_C| = (85 + sqrt 5)/361 = 0.24165... <= 0.2417 (torus A: dk_torus)


# ------------------------------------------------------------------ Lean data parsing
def lean_src(name):
    return open(os.path.join(REPO, 'PlasmaLean', 'Design', name)).read()


def parse_sp(src, name):
    i = src.index(f'def {name} : SP := [')
    j = src.index(']\n', i)
    ts = re.findall(r'⟨mkRat \((-?\d+)\)\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', src[i:j])
    return [(Fr(int(n), int(d)), int(a), int(b), int(c), int(e)) for n, d, a, b, c, e in ts]


def parse_nat(src, name):
    m = re.search(r'def %s : ℕ := (\d+)' % name, src)
    return int(m.group(1))


def parse_rows(src, name):
    i = src.index(f'def {name} : List ℕ := [')
    j = src.index(']', i)
    return [int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', src[i:j])]


def fieldW(F, data, f):
    return ((data >> (F * f)) % 2 ** F) - 2 ** (F - 1)


def full_grid_from_rows(rows, N, M, F, p):
    s = 1 if p % 2 == 0 else -1

    def h(i, j):
        if i < N:
            return 0
        r = rows[i - N] if i - N < len(rows) else 0
        return fieldW(F, r, j)
    return [[h(i, j) + s * h(max(2 * N - i, 0), max(2 * M - j, 0)) for j in range(2 * M + 1)]
            for i in range(2 * N + 1)]


# ------------------------------------------------------------------ DkPoly mirrors
def sp_dU(p):
    return [(q * a, a - 1, b, c, d) for q, a, b, c, d in p if a != 0]


def sp_dZ(p):
    return [(q * b, a, b - 1, c, d) for q, a, b, c, d in p if b != 0]


def sp_dC(p):
    return [(q * c, a, b, c - 1, d) for q, a, b, c, d in p if c != 0]


def sp_dS(p):
    return [(q * d, a, b, c, d - 1) for q, a, b, c, d in p if d != 0]


def sp_mulMono(t, p):
    tq, ta, tb, tc, td = t
    return [(tq * q, ta + a, tb + b, tc + c, td + d) for q, a, b, c, d in p]


def tm_lt(t, s):
    return t[1:] < s[1:]


def sp_merge(p, q):
    fuel = len(p) + len(q)
    out = []
    p, q = list(p), list(q)
    while True:
        if fuel == 0:
            return out + p + q
        fuel -= 1
        if not p:
            return out + q
        if not q:
            return out + p
        t, s = p[0], q[0]
        if tm_lt(t, s):
            out.append(t)
            p = p[1:]
        elif tm_lt(s, t):
            out.append(s)
            q = q[1:]
        elif t[1:] == s[1:]:
            if t[0] + s[0] != 0:
                out.append((t[0] + s[0],) + t[1:])
            p, q = p[1:], q[1:]
        else:
            out += [t, s]
            p, q = p[1:], q[1:]


def sp_phiS(p):
    return sp_merge(sp_mulMono((Fr(-2), 0, 0, 0, 1), sp_dC(p)), sp_mulMono((Fr(2), 0, 0, 1, 0), sp_dS(p)))


def sp_lcm(p):
    L = 1
    for q, *_ in p:
        L = L * q.denominator // math.gcd(L, q.denominator)
    return L


# ------------------------------------------------------------------ build
def low_grid(gfull, Nc, Mc, Sc, NL, ML, SL, p):
    """The data grid truncated to the box NL x ML and rounded to 2^-SL (symmetric)."""
    dN, dM = Nc - NL, Mc - ML
    s = 1 if p % 2 == 0 else -1
    sh = Sc - SL
    G = [[AB.round_div(gfull[i + dN][j + dM], 2 ** sh) for j in range(2 * ML + 1)] for i in range(2 * NL + 1)]
    for i in range(2 * NL + 1):
        for j in range(2 * ML + 1):
            i2, j2 = 2 * NL - i, 2 * ML - j
            if (i, j) < (i2, j2):
                avg = AB.round_div(G[i][j] + s * G[i2][j2], 2)
                G[i][j] = avg
                G[i2][j2] = s * avg
    G[NL][ML] = 2 * AB.round_div(G[NL][ML], 2) if s == 1 else 0
    return G


def build(NL, ML, SL, verbose=True):
    import numpy as np
    cdata = lean_src(DT.data_module())
    Nc, Mc, Sc, Fc = (parse_nat(cdata, x) for x in ('Nc', 'Mc', 'Sc', 'Fc'))
    Iqc, Qc = parse_nat(cdata, 'Iqc'), parse_nat(cdata, 'Qc')
    gU = full_grid_from_rows(parse_rows(cdata, 'datU'), Nc, Mc, Fc, 0)
    gZ = full_grid_from_rows(parse_rows(cdata, 'datZ'), Nc, Mc, Fc, 1)
    csrc = lean_src('DommaschkKamCData.lean')      # the moving centre (shared by tori C and A)
    cenR, cenZ = parse_sp(csrc, 'cenR'), parse_sp(csrc, 'cenZ')
    fd = lean_src('DommaschkKamFieldData.lean')
    dDR, dnRh, dnZR = parse_sp(fd, 'dDR'), parse_sp(fd, 'dnRh'), parse_sp(fd, 'dnZR')
    dD, dnR, dnZ = parse_sp(fd, 'dD'), parse_sp(fd, 'dnR'), parse_sp(fd, 'dnZ')
    nRR = sp_mulMono((Fr(1), 1, 0, 0, 0), dnRh)
    polys = [('D', dDR), ('Du', sp_dU(dDR)), ('Dz', sp_dZ(dDR)),
             ('nR', nRR), ('nRu', sp_dU(nRR)), ('nRz', sp_dZ(nRR)),
             ('nZ', dnZR), ('nZu', sp_dU(dnZR)), ('nZz', sp_dZ(dnZR))]
    upolys = {'D': dD, 'Du': sp_dU(dD), 'Dz': sp_dZ(dD), 'nR': dnR, 'nRu': sp_dU(dnR), 'nRz': sp_dZ(dnR),
              'nZ': dnZ, 'nZu': sp_dU(dnZ), 'nZz': sp_dZ(dnZ)}

    pl = AB.Pipeline(NL, ML, SL, P_EXP, E_EXP)
    t = pl.add_const('T', 't')
    V = pl.add_const('V', 'V')
    C = pl.add_const('C', 'C')
    S = pl.add_const('S', 'S')
    xU = low_grid(gU, Nc, Mc, Sc, NL, ML, SL, 0)
    xZ = low_grid(gZ, Nc, Mc, Sc, NL, ML, SL, 1)
    FU = max(AB.clog2(max(abs(v) for c in xU for v in c) + 1) + 1, 8)
    FZ = max(AB.clog2(max(abs(v) for c in xZ for v in c) + 1) + 1, 8)
    U = pl.data(xU, 0, 'U', FU)
    Z = pl.data(xZ, 1, 'Z', FZ)
    nb = (2 * NL + 1) * (2 * ML + 1)

    def wgrid(G, a, b):
        return [[(a * (i - NL) + b * (j - ML)) * G[i][j] for j in range(2 * ML + 1)] for i in range(2 * NL + 1)]
    A = pl.data(wgrid(xU, 1, 0), 3, 'A', None, Lstatic=nb * (NL * 2 ** FU), kind='derived',
                info=dict(src=U, a=1, b=0))
    B = pl.data(wgrid(xZ, 1, 0), 0, 'B', None, Lstatic=nb * (NL * 2 ** FZ), kind='derived',
                info=dict(src=Z, a=1, b=0))
    Pu = pl.data(wgrid(xU, 0, 1), 3, 'Pu', None, Lstatic=nb * (ML * 2 ** FU), kind='derived',
                 info=dict(src=U, a=0, b=1))
    Pz = pl.data(wgrid(xZ, 0, 1), 0, 'Pz', None, Lstatic=nb * (ML * 2 ** FZ), kind='derived',
                 info=dict(src=Z, a=0, b=1))
    mul = lambda i, j: ('mul', ('var', i), ('var', j))            # noqa: E731
    Rn = pl.node('R', ('add', ('mul', ('cst', 29), ('var', t)), ('mul', ('cst', 32), ('var', U))), 32,
                 rel=('R',))['var']
    # monomials
    amax = max(tm[1] for _, p in polys for tm in p)
    bmax = max(tm[2] for _, p in polys for tm in p)
    Rp = {1: Rn}
    for a in range(2, amax + 1):
        Rp[a] = pl.node('R%d' % a, mul(Rp[a - 1], Rn), 1, rel=('Rpow', a))['var']
    Zp = {1: Z}
    for b in range(2, bmax + 1):
        Zp[b] = pl.node('z%d' % b, mul(Zp[b - 1], Z), 1, rel=('Zpow', b))['var']
    pairs = sorted({(tm[1], tm[2]) for _, p in polys for tm in p if tm[1] >= 1 and tm[2] >= 1})
    if 7 not in Rp:
        raise ValueError('R^7 needed')
    Mono = {}
    for a, b in pairs:
        Mono[(a, b)] = pl.node('m%d_%d' % (a, b), mul(Rp[a], Zp[b]), 1, rel=('mono', a, b))['var']

    def mono(a, b):
        if a == 0 and b == 0:
            return t
        if b == 0:
            return Rp[a]
        if a == 0:
            return Zp[b]
        return Mono[(a, b)]
    PV = {}
    CH = {}
    for kp, (nm, p) in enumerate(polys):
        L = sp_lcm(p)
        ep = max(tm[3] + tm[4] for tm in p)
        assert ep == 3
        # contiguous chunks of at most CHUNK distinct monomials (few grid images per kernel check)
        bounds = []
        a0 = 0
        while a0 < len(p):
            seen = []
            a1 = a0
            while a1 < len(p):
                ab = (p[a1][1], p[a1][2])
                if ab not in seen:
                    if len(seen) == CHUNK:
                        break
                    seen.append(ab)
                a1 += 1
            bounds.append((a0, a1 - a0))
            a0 = a1
        prev = None
        for kc, (a, ln) in enumerate(bounds):
            final = kc == len(bounds) - 1
            nmc = nm if final else '%s_%d' % (nm, kc + 1)
            chunk = p[a:a + ln]
            e = AB.polyT(Fr(L), 3, mono, chunk)
            if prev is not None:
                e = ('add', ('mul', ('cst', L), AB.pwT(V, 3, ('var', prev))), e)
            prev = pl.node(nmc, e, L, rel=('chunk', nm, kp, a, ln, prev, final))['var']
        PV[nm] = prev
        CH[nm] = bounds
    mono0 = lambda a, b: t                                         # noqa: E731
    LcR, LcZ = sp_lcm(cenR), sp_lcm(cenZ)
    V0R = pl.node('V0R', ('sub', ('mul', ('cst', LcR), AB.pwT(V, 3, ('var', U))),
                          AB.polyT(Fr(LcR), 3, mono0, cenR)), LcR, rel=('V0R',))['var']
    V0Z = pl.node('V0Z', ('sub', ('mul', ('cst', LcZ), AB.pwT(V, 3, ('var', Z))),
                          AB.polyT(Fr(LcZ), 3, mono0, cenZ)), LcZ, rel=('V0Z',))['var']
    W0 = pl.node('W0', ('sub', mul(A, V0Z), mul(B, V0R)), 1, rel=('W0',))['var']
    aRd, aZd = sp_phiS(cenR), sp_phiS(cenZ)
    AR1 = pl.node('AR1', AB.polyT(Fr(sp_lcm(aRd)), 3, mono0, aRd), sp_lcm(aRd), rel=('AR1',))['var']
    AZ1 = pl.node('AZ1', AB.polyT(Fr(sp_lcm(aZd)), 3, mono0, aZd), sp_lcm(aZd), rel=('AZ1',))['var']
    D, Du, Dz, nR, nRu, nRz, nZ, nZu, nZz = (PV[k] for k in ('D', 'Du', 'Dz', 'nR', 'nRu', 'nRz', 'nZ', 'nZu', 'nZz'))
    DD = pl.node('DD', mul(D, D), 1, rel=('DD',))['var']
    add = lambda e, f: ('add', e, f)                               # noqa: E731
    sub = lambda e, f: ('sub', e, f)                               # noqa: E731
    G1 = pl.node('G1', add(mul(nRu, V0R), mul(nRz, V0Z)), 1, rel=('G1',))['var']
    G2 = pl.node('G2', add(mul(Du, V0R), mul(Dz, V0Z)), 1, rel=('G2',))['var']
    G3 = pl.node('G3', add(mul(nZu, V0R), mul(nZz, V0Z)), 1, rel=('G3',))['var']
    YR = pl.node('YR', sub(add(sub(mul(nR, D), mul(D, G1)), mul(nR, G2)), mul(DD, AR1)), 1, rel=('YR',))['var']
    YZ = pl.node('YZ', sub(add(sub(mul(nZ, D), mul(D, G3)), mul(nZ, G2)), mul(DD, AZ1)), 1, rel=('YZ',))['var']
    Pn = pl.node('P', sub(mul(YR, V0Z), mul(YZ, V0R)), 1, rel=('P',))['var']
    # approximate inverses (float, untrusted) at the surrogate
    n1, n2 = 4 * (2 * NL + 1), 4 * (2 * ML + 1)
    n1, n2 = 1 << AB.clog2(n1), 1 << AB.clog2(n2)
    Dv = pl.centre_values(D, n1, n2).real
    Wv = pl.centre_values(W0, n1, n2).real
    Rv = pl.centre_values(Rn, n1, n2).real
    FqD = None
    gqD = AB.grid_from_values(1.0 / Dv, NL, ML, SL, 0)
    gqW = AB.grid_from_values(1.0 / Wv, NL, ML, SL, 0)
    gqR = AB.grid_from_values(1.0 / Rv, NL, ML, SL, 0)
    fw = lambda G: max(AB.clog2(max(abs(v) for c in G for v in c) + 1) + 1, 8)   # noqa: E731
    qD = pl.data(gqD, 0, 'qD', fw(gqD))
    eD = pl.node('eD', sub(mul(qD, D), mul(t, t)), 0, rel=('eD',))
    qW = pl.data(gqW, 0, 'qW', fw(gqW))
    eW = pl.node('eW', sub(mul(qW, W0), mul(t, t)), 0, rel=('eW',))
    qR = pl.data(gqR, 0, 'qR', fw(gqR))
    eR = pl.node('eR', sub(mul(qR, Rn), mul(t, t)), 0, rel=('eR',))
    LU = pl.node('LU', sub(('mul', ('cst', 2 ** (Qc + 1)), ('var', Pu)), ('mul', ('cst', Iqc), ('var', A))), 0,
                 rel=('LU',))
    LZ = pl.node('LZ', sub(('mul', ('cst', 2 ** (Qc + 1)), ('var', Pz)), ('mul', ('cst', Iqc), ('var', B))), 0,
                 rel=('LZ',))
    PR = pl.node('PR', mul(Rp[7], Pn), 1, rel=('PR',))['var']
    qD2 = pl.node('qD2', mul(qD, qD), 1, rel=('qD2',))['var']
    qD3 = pl.node('qD3', mul(qD2, qD), 1, rel=('qD3',))['var']
    qW2 = pl.node('qW2', mul(qW, qW), 1, rel=('qW2',))['var']
    qDW = pl.node('qDW', mul(qD3, qW2), 1, rel=('qDW',))['var']
    Yn = pl.node('Y', mul(PR, qDW), 1, rel=('Y',))['var']
    idx = dict(t=t, V=V, C=C, S=S, U=U, Z=Z, A=A, B=B, Pu=Pu, Pz=Pz, R=Rn, Rp=Rp, Zp=Zp, Mono=Mono, PV=PV,
               V0R=V0R, V0Z=V0Z, W0=W0, AR1=AR1, AZ1=AZ1, DD=DD, G1=G1, G2=G2, G3=G3, YR=YR, YZ=YZ, P=Pn,
               qD=qD, qW=qW, qR=qR, PR=PR, qD2=qD2, qD3=qD3, qW2=qW2, qDW=qDW, Y=Yn)
    norms = dict(eD=eD, eW=eW, eR=eR, LU=LU, LZ=LZ)
    ctx = dict(Nc=Nc, Mc=Mc, Sc=Sc, Fc=Fc, Iqc=Iqc, Qc=Qc, gU=gU, gZ=gZ, xU=xU, xZ=xZ, cenR=cenR, cenZ=cenZ,
               polys=polys, upolys=upolys, aRd=aRd, aZd=aZd, FU=FU, FZ=FZ, nRR=nRR)
    return pl, idx, norms, ctx


# ------------------------------------------------------------------ tails (closeness of the data torus)
def tail_bound(pl, ctx, which, a, b):
    """K for the weighted norm of the grid  w * (g_data - embed(g_low)) on the full layout, w = a k + b m."""
    Nc, Mc, Sc = ctx['Nc'], ctx['Mc'], ctx['Sc']
    NL, ML, SL = pl.N, pl.M, pl.S
    dN, dM, sh = Nc - NL, Mc - ML, Sc - SL
    g, gl = (ctx['gU'], ctx['xU']) if which == 'U' else (ctx['gZ'], ctx['xZ'])
    G = []
    for i in range(2 * Nc + 1):
        col = []
        for j in range(2 * Mc + 1):
            e = 0
            if dN <= i <= dN + 2 * NL and dM <= j <= dM + 2 * ML:
                e = 2 ** sh * gl[i - dN][j - dM]
            col.append((a * (i - Nc) + b * (j - Mc)) * (g[i][j] - e))
        G.append(col)
    l1 = sum(abs(v) for c in G for v in c)
    bb = AB.clog2(l1 + 1) + 2
    Wd = 2 * Nc + 1
    R = 2 * Mc + 1
    K = pl.wl1(AB.kron_grid(G, bb, Wd), bb, Wd, R, Nc, Mc, Nc, Mc)
    val = Fr(int(K), 2 ** (E_EXP * (Nc + Mc)) * 2 ** Sc)
    return dict(b=bb, W=Wd, dc=AB.clog2(Wd), dr=AB.clog2(R), K=int(K), val=val, bound=AB.up(val, 3), l1=l1)


# ------------------------------------------------------------------ majorants and transfer
def lipQ(p, A0, A1, h0, h1, Cb):
    """sum |q| ((A0+h0)^a (A1+h1)^b - A0^a A1^b) Cb^(c+d)  (mirrors `lipQ` of DommaschkKamCAdm)."""
    s = Fr(0)
    for q, a, b, c, d in p:
        s += abs(q) * ((A0 + h0) ** a * (A1 + h1) ** b - A0 ** a * A1 ** b) * Cb ** (c + d)
    return s


def bnd(pl, i):
    return pl.B[i] + pl.E[i]


def certify(pl, idx, norms, ctx, tails, verbose=True):
    """Exact rational certified constants (mirrors the transfer lemmas of DommaschkKamCAdm)."""
    Cb = Fr(P_EXP, 2 ** E_EXP)
    EU = MU + tails['U']['bound']
    EZ = MU + tails['Z']['bound']
    EA = MU + tails['A']['bound']
    EB = MU + tails['B']['bound']
    EPu = MU + tails['Pu']['bound']
    EPz = MU + tails['Pz']['bound']
    BU, BZ = pl.B[idx['U']], pl.B[idx['Z']]
    out = dict(EU=EU, EZ=EZ, EA=EA, EB=EB, EPu=EPu, EPz=EPz)
    dlt = {}
    for k, p in ctx['upolys'].items():
        dlt[k] = AB.up(lipQ(p, BU, BZ, EU, EZ, Cb), 4)
    out['delta'] = dlt
    fb = {}
    for k in ('D', 'Du', 'Dz', 'nR', 'nRu', 'nRz', 'nZ', 'nZu', 'nZz'):
        fb[k] = AB.up(bnd(pl, idx['PV'][k]) + dlt[k], 5)
    out['field'] = fb
    # frame vectors, W0
    nV0R, nV0Z = bnd(pl, idx['V0R']), bnd(pl, idx['V0Z'])
    nA, nB = pl.B[idx['A']], pl.B[idx['B']]
    dW = EA * (nV0Z + EZ) + nA * EZ + EB * (nV0R + EU) + nB * EU
    out['dW'] = dW
    # inverses
    def inv(qi, eps_node, delta):
        nq = pl.B[qi]
        e1 = eps_node['bound'] + nq * delta
        assert e1 < 1
        return nq, e1, nq / (1 - e1)
    nqD, eD1, sD = inv(idx['qD'], norms['eD'], dlt['D'])
    nqW, eW1, sW = inv(idx['qW'], norms['eW'], dW)
    nqR, eR1, sR = inv(idx['qR'], norms['eR'], EU)
    out.update(nqD=nqD, eD1=eD1, sD=AB.up(sD, 5), nqW=nqW, eW1=eW1, sW=AB.up(sW, 5), nqR=nqR, eR1=eR1,
               sR=AB.up(sR, 5))
    # the torsion numerator: majD of the Pp structure at the surrogate norms
    yn = [bnd(pl, idx['PV'][k]) for k in ('D', 'nR', 'nZ', 'Du', 'Dz', 'nRu', 'nRz', 'nZu', 'nZz')]
    yn += [nV0R, nV0Z, bnd(pl, idx['AR1']), bnd(pl, idx['AZ1'])]
    yd = [dlt[k] for k in ('D', 'nR', 'nZ', 'Du', 'Dz', 'nRu', 'nRz', 'nZu', 'nZz')] + [EU, EZ, Fr(0), Fr(0)]
    aa = [x + y for x, y in zip(yn, yd)]
    dP = majD_Qp(aa, yd)
    out['dP'] = dP
    nR7 = bnd(pl, idx['Rp'][7])
    nRn = bnd(pl, idx['R'])
    dR7 = (nRn + EU) ** 7 - nRn ** 7
    nP = bnd(pl, idx['P'])
    dPR = dR7 * (nP + dP) + nR7 * dP
    nqDW = bnd(pl, idx['qDW'])
    dY = nqDW * dPR
    Yc = pl.G[idx['Y']][pl.N][pl.M]
    pY = pl.W[idx['Y']][2]
    assert pY in (0, 2)
    meanY = Fr(Yc, 2 ** pl.S) * (1 if pY == 0 else -1)
    EY = pl.E[idx['Y']]
    nY = pl.B[idx['Y']] + EY + dY
    mY = abs(meanY) - EY - dY
    zN = (1 / (1 - eD1)) ** 3 * (1 / (1 - eW1)) ** 2
    tT = nY * zN
    tau = mY - nY * (zN - 1)
    out.update(dR7=dR7, dPR=dPR, dY=dY, meanY=meanY, nY=nY, mY=mY, zN=zN, tT=AB.up(tT, 5), tau=AB.down(tau, 5))
    # torus norms
    IOTA_ABS_UP = Fr(*DT.cfg()['iota_abs_up'])
    io = Fr(1, 2 ** ctx['Qc'])
    LUb = norms['LU']['bound'] / 2 ** ctx['Qc'] + io * nA
    LZb = norms['LZ']['bound'] / 2 ** ctx['Qc'] + io * nB
    tor = dict(au=BU + EU, az=BZ + EZ, avR=nV0R + EU, avZ=nV0Z + EZ, aR=nRn + EU, aRt=nA + EA, azt=nB + EB,
               aLR=LUb + MU + IOTA_ABS_UP * tails['A']['bound'] + 2 * tails['Pu']['bound'],
               aLz=LZb + MU + IOTA_ABS_UP * tails['B']['bound'] + 2 * tails['Pz']['bound'])
    out['torus'] = {k: AB.up(v, 5) for k, v in tor.items()}
    return out


def majQp(a):
    """maj and majD of the torsion structure `Qp` (13 variables, the `Pp` formula); returns maj."""
    return majD_Qp(a, None)


def majD_Qp(a, b):
    """majD (a) (b) of Qp: product rule over the Pp formula (b = None: the majorant itself)."""
    # values as pairs (maj, majD)
    def var(i):
        return (a[i], b[i] if b is not None else Fr(0))

    def m(x, y):
        return (x[0] * y[0], x[1] * y[0] + x[0] * y[1])

    def ad(x, y):
        return (x[0] + y[0], x[1] + y[1])
    D, nR, nZ, Du, Dz, nRu, nRz, nZu, nZz, vR, vZ, aR, aZ = (var(i) for i in range(13))

    def Y(n, nu, nz, ap):
        return ad(ad(ad(m(n, D), m(D, ad(m(nu, vR), m(nz, vZ)))), m(n, ad(m(Du, vR), m(Dz, vZ)))), m(m(D, D), ap))
    P = ad(m(Y(nR, nRu, nRz, aR), vZ), m(Y(nZ, nZu, nZz, aZ), vR))
    return P[1] if b is not None else P[0]


# ------------------------------------------------------------------ κ with the certified bounds
def kappa(V, r=0.045):
    """SCG.kap (transcription of kam_constants.run_scg for the given bound dictionary V)."""
    sys.path.insert(0, HERE)
    import kam_constants as KC
    pol = KC.lean_polys()
    p = 7
    gam, dlow = DT.cfg()['gam'], DT.cfg()['dlow']
    E1 = 2.718
    d0 = r / 7
    e0 = 1e-28
    th = e0 / d0 ** 4
    kE = V['sD']
    keta1 = V['sW'] * (V['avZ'] + V['avR']) * kE
    keta2 = V['bD'] * V['sR'] ** p * (V['aRt'] + V['azt']) * kE
    kh = V['aR'] ** p * V['sD'] * V['sW']
    kTc = V['aR'] ** p * V['sD'] * V['sW'] ** 2 * (V['avZ'] + V['avR']) * kE
    eM = th * d0 ** 4
    tTot = V['tT'] + kTc * eM
    taup = V['tau'] - kTc * eM
    gg = 2 * E1 * gam
    k20 = keta2 / gg
    kc = (keta1 * d0 + tTot * k20) / taup
    k2 = k20 + kc
    k1 = (keta1 * d0 + tTot * k2) / gg
    mA = max(V['aRt'], V['azt'])
    mV = max(V['avR'], V['avZ'])
    cK = k1 * mA + k2 * d0 * kh * mV
    kS = (V['bDu'] + V['bDz']) * V['sD'] * kE * d0 + p * V['sR'] * kE * d0 + V['sW'] * (V['avZ'] + V['avR']) * kE / E1
    kRem = kS * k2 * kh * mV * d0 + k1 * kE / E1
    XRb = V['bnR'] * V['sD']
    XZb = V['bnZ'] * V['sD']
    kA = max((V['bnRu'] + XRb * V['bDu']) * V['sD'] + (V['bnRz'] + XRb * V['bDz']) * V['sD'],
             (V['bnZu'] + XZb * V['bDu']) * V['sD'] + (V['bnZz'] + XZb * V['bDz']) * V['sD'])
    cL = kA * cK + kE * d0 ** 2 + kRem * th * d0 ** 3
    Tq = th * d0 ** 2
    au_, az_ = V['au'] + Tq * cK, V['az'] + Tq * cK
    ac = math.exp(r)
    C2 = 0.0
    for nm, aL in (('dnR', V['aLR']), ('dnZ', V['aLz'])):
        mj = lambda P, du, dz: KC.majd(pol[P], au_, az_, ac, du, dz)  # noqa: E731
        C2 = max(C2, 0.5 * (cK ** 2 * ((mj('dD', 2, 0) + 2 * mj('dD', 1, 1) + mj('dD', 0, 2)) * (aL + Tq * cL)
                                       + mj(nm, 2, 0) + 2 * mj(nm, 1, 1) + mj(nm, 0, 2))
                             + 2 * cK * cL * (mj('dD', 1, 0) + mj('dD', 0, 1))))
    kap = V['bD'] * kRem * d0 + (V['bDu'] + V['bDz']) * cK * kE * d0 ** 2 + C2
    return dict(cK=cK, cL=cL, C2=C2, kap=kap, ereq=d0 ** 4 / (32 * kap))


SHARP = dict(au=0.1377, az=0.1187, avR=0.05317, avZ=0.0456, aR=1.044, aRt=0.05459, azt=0.05271, aLR=0.2537,
             aLz=0.2522, bD=1.151, bDu=6.476, bDz=0.5307, bnR=0.1537, bnRu=1.545, bnRz=2.227, bnZ=0.1738,
             bnZu=1.556, bnZz=1.783, sD=3.82, sR=1.238, sW=2741, tT=2747, tau=14.26)


def report(pl, idx, norms, ctx, cert):
    V = dict(cert['torus'])
    fmap = dict(bD='D', bDu='Du', bDz='Dz', bnR='nR', bnRu='nRu', bnRz='nRz', bnZ='nZ', bnZu='nZu', bnZz='nZz')
    for k, f in fmap.items():
        V[k] = cert['field'][f]
    for k in ('sD', 'sR', 'sW', 'tT', 'tau'):
        V[k] = cert[k]
    print('certified vs sharp (r = 0.045):')
    for k in SHARP:
        print('  %-5s %-12.6g sharp %-10.5g ratio %.5f' % (k, float(V[k]), SHARP[k], float(V[k]) / SHARP[k]))
    print('inputs: EU %.2e EZ %.2e EA %.2e EB %.2e; dW %.2e dP %.2e dY %.2e' % (
        float(cert['EU']), float(cert['EZ']), float(cert['EA']), float(cert['EB']), float(cert['dW']),
        float(cert['dP']), float(cert['dY'])))
    print('eps: eD %.2e (node %.2e) eW %.2e (node %.2e) eR %.2e; zN-1 %.2e; |<Y>| %.5f, ||Y|| %.2f' % (
        float(cert['eD1']), float(norms['eD']['bound']), float(cert['eW1']), float(norms['eW']['bound']),
        float(cert['eR1']), float(cert['zN'] - 1), float(cert['meanY']), float(cert['nY'])))
    Vf = {k: float(v) for k, v in V.items()}
    ks = kappa(Vf)
    ks0 = kappa(SHARP)
    print('kappa certified %.3e (sharp %.3e), required e0 %.3e (sharp %.3e); cK %.3e cL %.3e' % (
        ks['kap'], ks0['kap'], ks['ereq'], ks0['ereq'], ks['cK'], ks['cL']))
    return V, ks


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--NL', type=int, default=24)
    ap.add_argument('--ML', type=int, default=28)
    ap.add_argument('--SL', type=int, default=64)
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--pickle', default='')
    ap.add_argument('--ndata', type=int, default=4)
    ap.add_argument('--ncheck', type=int, default=8)
    ap.add_argument('--only', default='', help='comma-separated modules to write (data,env,trees,checks,rel,chain,tail,out)')
    ap.add_argument('--tag', default='C', help='torus (C, or A: modules DommaschkKamA*, see dk_torus.py)')
    ap.add_argument('--out-dir', default='', help='output directory (default PlasmaLean/Design)')
    args = ap.parse_args()
    global OUT
    DT.select(args.tag)
    if args.out_dir:
        OUT = args.out_dir
    import time
    t0 = time.time()
    pl, idx, norms, ctx = build(args.NL, args.ML, args.SL)
    print('chain built: %d variables, %d steps, %.1f s' % (pl.nvar, len(pl.steps), time.time() - t0))
    tails = {}
    for nm, which, a, b in (('U', 'U', 0, 0), ('Z', 'Z', 0, 0), ('A', 'U', 1, 0), ('B', 'Z', 1, 0),
                            ('Pu', 'U', 0, 1), ('Pz', 'Z', 0, 1)):
        if a == 0 and b == 0:
            tails[nm] = tail_bound_plain(pl, ctx, which)
        else:
            tails[nm] = tail_bound(pl, ctx, which, a, b)
    print('tails:', {k: '%.2e' % float(v['bound']) for k, v in tails.items()}, '%.1f s' % (time.time() - t0))
    cert = certify(pl, idx, norms, ctx, tails)
    report(pl, idx, norms, ctx, cert)
    mx = max((s for s in pl.steps if 'W' in s and 'R' in s), key=lambda s: s['W'] * s['R'] * s['b'])
    print('largest image: %s %.2f Mbit' % (mx['name'], mx['W'] * mx['R'] * mx['b'] / 1e6))
    if args.emit:
        em = Emit(pl, idx, norms, ctx, tails, cert)
        only = set(args.only.split(',')) if args.only else None
        want = lambda k: only is None or k in only                      # noqa: E731
        em.emit_data(args.ndata) if want('data') else em.emit_data_dry(args.ndata)
        if want('env'):
            em.emit_env()
        else:
            em.prepare_env()
        if want('trees'):
            em.emit_trees()
        em.emit_checks(args.ncheck, dry=not want('checks'))
        if want('rel'):
            em.emit_rel()
        if want('chain'):
            em.emit_chain()
        if want('tail'):
            em.emit_tail()
        if want('out'):
            em.emit_out()
        print('emitted:', em.files)
        print('check loads (Mbit):', [round(x / 1e6, 1) for x in em.checkload])
    if args.pickle:
        import pickle
        pickle.dump(dict(pl=pl, idx=idx, norms=norms, ctx=ctx, tails=tails, cert=cert), open(args.pickle, 'wb'))


def tail_bound_plain(pl, ctx, which):
    """Tail of the grid itself (weights 1): implemented as w = 1 (a = b = 0 means weight 1)."""
    Nc, Mc, Sc = ctx['Nc'], ctx['Mc'], ctx['Sc']
    NL, ML, SL = pl.N, pl.M, pl.S
    dN, dM, sh = Nc - NL, Mc - ML, Sc - SL
    g, gl = (ctx['gU'], ctx['xU']) if which == 'U' else (ctx['gZ'], ctx['xZ'])
    G = []
    for i in range(2 * Nc + 1):
        col = []
        for j in range(2 * Mc + 1):
            e = 0
            if dN <= i <= dN + 2 * NL and dM <= j <= dM + 2 * ML:
                e = 2 ** sh * gl[i - dN][j - dM]
            col.append(g[i][j] - e)
        G.append(col)
    l1 = sum(abs(v) for c in G for v in c)
    bb = AB.clog2(l1 + 1) + 2
    Wd = 2 * Nc + 1
    R = 2 * Mc + 1
    K = pl.wl1(AB.kron_grid(G, bb, Wd), bb, Wd, R, Nc, Mc, Nc, Mc)
    val = Fr(int(K), 2 ** (E_EXP * (Nc + Mc)) * 2 ** Sc)
    return dict(b=bb, W=Wd, dc=AB.clog2(Wd), dr=AB.clog2(R), K=int(K), val=val, bound=AB.up(val, 3), l1=l1)




# ======================================================================================== Lean emission
OUT = os.path.join(REPO, 'PlasmaLean', 'Design')
NS = 'PlasmaLean.Design.DommaschkKamC'
HEADER = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

"""
OPEN = """open Polynomial PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.Kron2
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Design.DommaschkKam
  WEll1Z2 Complex
"""
POLY_LEAN = {'D': 'dDR', 'Du': 'DkPoly.dU dDR', 'Dz': 'DkPoly.dZ dDR',
             'nR': 'DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh', 'nRu': 'DkPoly.dU (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)',
             'nRz': 'DkPoly.dZ (DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRh)',
             'nZ': 'dnZR', 'nZu': 'DkPoly.dU dnZR', 'nZz': 'DkPoly.dZ dnZR'}
POLY_ORDER = ['D', 'Du', 'Dz', 'nR', 'nRu', 'nRz', 'nZ', 'nZu', 'nZz']


def qlean(q):
    q = Fr(q)
    if q.denominator == 1:
        return '(%d : ℚ)' % q.numerator
    den = q.denominator
    k10, d = 0, den
    while d % 10 == 0:
        d //= 10
        k10 += 1
    if d == 1:
        return '(%d / 10 ^ %d : ℚ)' % (q.numerator, k10)
    if den & (den - 1) == 0:
        return '(%d / 2 ^ %d : ℚ)' % (q.numerator, den.bit_length() - 1)
    return '(%d / %d : ℚ)' % (q.numerator, den)


def lst(xs):
    lines, cur = [], '  ['
    for k, x in enumerate(xs):
        piece = x + (', ' if k + 1 < len(xs) else ']')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip())
            cur = '    '
        cur += piece
    lines.append(cur)
    return '\n' + '\n'.join(lines)


def wrap(text, indent):
    words = text.split(' ')
    lines, cur = [], ''
    for w in words:
        if len(cur) + len(w) + 1 + indent + 2 > 98 and cur:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w) if cur else w
    lines.append(cur)
    return ('\n' + ' ' * (indent + 2)).join(lines)


def half_grid(G, N, M, p):
    s = 1 if p % 2 == 0 else -1
    h = {}
    for i in range(N, 2 * N + 1):
        for j in range(2 * M + 1):
            if i > N or j > M:
                v = G[i][j]
            elif j < M:
                v = 0
            else:
                v = G[N][M] // 2 if s == 1 else 0
            h[(i, j)] = v
    for i in range(2 * N + 1):
        for j in range(2 * M + 1):
            a = h.get((i, j), 0) if i >= N else 0
            i2, j2 = 2 * N - i, 2 * M - j
            b = h.get((i2, j2), 0) if i2 >= N else 0
            assert a + s * b == G[i][j], (i, j)
    return h


def pack_rows(h, N, M, F):
    rows = []
    for i in range(N, 2 * N + 1):
        tot = 0
        for j in range(2 * M, -1, -1):
            v = h[(i, j)]
            assert -2 ** (F - 1) <= v < 2 ** (F - 1)
            tot = (tot << F) + (v + 2 ** (F - 1))
        rows.append(tot)
    return rows


def tree_lean(e):
    k = e[0]
    if k == 'var':
        return '.var %d' % e[1]
    if k == 'cst':
        return '.cst %d' % e[1] if e[1] >= 0 else '.cst (%d)' % e[1]
    op = {'add': '.add', 'sub': '.sub', 'mul': '.mul'}[k]
    return '%s (%s) (%s)' % (op, tree_lean(e[1]), tree_lean(e[2]))


class Emit:
    def __init__(self, pl, idx, norms, ctx, tails, cert):
        self.pl, self.idx, self.norms, self.ctx, self.tails, self.cert = pl, idx, norms, ctx, tails, cert
        self.N, self.M, self.S = pl.N, pl.M, pl.S
        self.nvar = pl.nvar
        self.nodes = {s['n']: s for s in pl.steps if s.get('kind') == 'node'}
        self.normnodes = [s for s in pl.steps if s.get('kind') == 'norm']
        self.files = []

    def nm(self, i):
        return self.pl.names[i]

    def is_grid(self, i):
        return self.pl.kind[i] in ('data', 'node', 'grid')

    def write(self, mod, text):
        mod, text = DT.out_name(mod), DT.retarget(text)
        open(os.path.join(OUT, mod + '.lean'), 'w').write(text)
        self.files.append(mod)

    # ---------------------------------------------------------------- data
    def emit_data_dry(self, nfiles):
        ids = [i for i in range(4, self.nvar) if self.is_grid(i)]
        per = -(-len(ids) // nfiles)
        self.datamods = ['DommaschkKamCAdmData%d' % (f + 1) for f in range(nfiles)]

    def prepare_env(self):
        idx = self.idx
        tab = [0] * (19 * 8)
        for a in range(19):
            for b in range(8):
                v = 0
                if a == 0 and b == 0:
                    v = idx['t']
                elif b == 0 and a in idx['Rp']:
                    v = idx['Rp'][a]
                elif a == 0 and b in idx['Zp']:
                    v = idx['Zp'][b]
                elif (a, b) in idx['Mono']:
                    v = idx['Mono'][(a, b)]
                tab[a * 8 + b] = v
        self.monotab = tab
        self.pairs = sorted(set([(0, 0)] + [(a, 0) for a in idx['Rp']] + [(0, b) for b in idx['Zp']] + list(idx['Mono'])))

    def emit_data(self, nfiles):
        ids = [i for i in range(4, self.nvar) if self.is_grid(i)]
        per = -(-len(ids) // nfiles)
        chunks = [ids[k * per:(k + 1) * per] for k in range(nfiles)]
        mods = []
        for f, ch in enumerate(chunks):
            mod = 'DommaschkKamCAdmData%d' % (f + 1)
            mods.append(mod)
            out = [HEADER, 'public import Mathlib.Data.List.Basic\n\n']
            out.append("""/-!
# Data of the torus-C admissibility chain (part %d)

Packed half grids (`Certificates/KronBallGrid`, `halfGridR`: one literal per row `i − N`,
fields of the width `F` stated per centre, offset `2^{F−1}`, rows of length `2M + 1`, `M = %d`) of
the centres of the low-resolution ball chain of Dommaschk torus C (`Design/DommaschkKamCAdmEnv`).
Generated by the untrusted oracle `scripts/dommaschk_kam/emit_adm.py`; nothing here is trusted.
-/

@[expose] public section

namespace %s

""" % (f + 1, self.M, NS))
            for i in ch:
                G = self.pl.G[i]
                p = self.pl.W[i][2]
                F = self.pl.F[i]
                h = half_grid(G, self.N, self.M, p)
                rows = pack_rows(h, self.N, self.M, F)
                out.append('set_option linter.style.longLine false in\n')
                out.append('/-- Packed half grid of the centre `%s` (field width %d). -/\n' % (self.nm(i), F))
                out.append('def datA_%s : List ℕ := [\n%s]\n\n' % (self.nm(i), ',\n'.join('  0x%x' % v for v in rows)))
            out.append('end %s\n' % NS)
            self.write(mod, ''.join(out))
        self.datamods = mods
        return mods

    # ---------------------------------------------------------------- environment
    def gdef(self, i):
        k = self.pl.kind[i]
        p = self.pl.W[i][2]
        if k == 'derived':
            inf = self.pl.info[i]
            return ('fun i j => (((%d : ℕ) : ℤ) * ((i : ℤ) - NA) + ((%d : ℕ) : ℤ) * ((j : ℤ) - MA)) * gA_%s i j'
                    % (inf['a'], inf['b'], self.nm(inf['src'])))
        return 'symGrid NA MA ((-1) ^ %d) (halfGridR %d NA datA_%s)' % (p, self.pl.F[i], self.nm(i))

    def Ldef(self, i):
        k = self.pl.kind[i]
        if k == 'derived':
            inf = self.pl.info[i]
            return 'lwdA %d %d %d' % (inf['a'], inf['b'], self.pl.F[inf['src']])
        return 'lwA %d' % self.pl.F[i]

    def l1proof(self, i):
        k = self.pl.kind[i]
        if k == 'derived':
            inf = self.pl.info[i]
            src = inf['src']
            return ('l1_gridPolyNM_le_const NA MA fun i j hi hj => abs_wgridN_le NA MA %d %d (fun i j =>\n'
                    '      abs_dataGrid_le NA MA %d datA_%s %d (by kernel_fact) i j) hi hj'
                    % (inf['a'], inf['b'], self.pl.F[src], self.nm(src), self.pl.W[src][2]))
        return 'l1_dataGrid_le NA MA %d datA_%s %d (by kernel_fact)' % (self.pl.F[i], self.nm(i), self.pl.W[i][2])

    def emit_env(self):
        N, M, S = self.N, self.M, self.S
        mod = 'DommaschkKamCAdmEnv'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCKronW\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.datamods]
        out.append("""
/-!
# The ball environment of the torus-C admissibility chain

The variables of the low-resolution ball chain of Dommaschk torus C (N-33 plan item 8): layout
`N = %d`, `M = %d`, scale `2^{−%d}`, oracle angle `ψₒ = 2φ`, strip weights `68553^s 2^{16(K − s)}`
(`e^r ≤ 68553/2^16`, `Design/DommaschkKamCKronW`); the grids `gA i` of the centres, their
polynomials `PlA i`, weights `WtA i`, degree boxes `BxA i`, `ℓ¹` bounds `LA i`, Kronecker images
`KvA b W i`, the honest centres `xA i`, the norm bounds `BA i` of the centres and the radii
`EA i` of the balls (supplied by the oracle `scripts/dommaschk_kam/emit_adm.py`, checked in
`Design/DommaschkKamCAdmCheck*`), and the monomial table `monoA a b` (the variable of `R^a z^b`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos ψₒ`, `sin ψₒ` (`xA_t`, `xA_V`, `xA_C`, `xA_S`).
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- Layout: poloidal half width. -/
def NA : ℕ := %d
/-- Layout: toroidal half width. -/
def MA : ℕ := %d
/-- Layout: scale exponent. -/
def SA : ℕ := %d

""" % (N, M, S, NS, OPEN, N, M, S))
        for i in range(4, self.nvar):
            out.append('/-- Grid of the centre `%s`. -/\ndef gA_%s : ℕ → ℕ → ℤ :=\n  %s\n\n' % (
                self.nm(i), self.nm(i), wrap(self.gdef(i), 2)))
        gl = ['fun _ _ => 0'] * 4 + ['gA_%s' % self.nm(i) for i in range(4, self.nvar)]
        out.append('/-- The grids of the variables (list; the constants `0, …, 3` have no grid). -/\n')
        out.append('def gAl : List (ℕ → ℕ → ℤ) :=%s\n\n' % lst(gl))
        out.append('/-- The grids of the variables. -/\ndef gA (i : ℕ) : ℕ → ℕ → ℤ := gAl.getD i (fun _ _ => 0)\n\n')
        out.append("""/-- The polynomials of the variables. -/
def PlA : ℕ → P2
  | 0 => Tpoly SA NA MA
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NA MA (gA (n + 4))

""")
        wts = ['(%d, %d, %d)' % self.pl.W[i] for i in range(self.nvar)]
        out.append('/-- The weights of the variables (list). -/\ndef WtAl : List (ℕ × ℕ × ℕ) :=%s\n\n' % lst(wts))
        out.append('/-- The weights of the variables. -/\ndef WtA (i : ℕ) : ℕ × ℕ × ℕ := WtAl.getD i (1, 0, 0)\n\n')
        out.append("""/-- The degree boxes of the variables. -/
def BxA : ℕ → ℕ × ℕ
  | 0 => (NA, MA)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NA, 2 * MA)

""")
        out.append('/-- The static `ℓ¹` bound of a data grid of field width `F`. -/\n'
                   'def lwA (F : ℕ) : ℕ := (2 * NA + 1) * (2 * MA + 1) * 2 ^ F\n\n'
                   '/-- The static `ℓ¹` bound of a weighted (derived) data grid. -/\n'
                   'def lwdA (a b F : ℕ) : ℕ := (2 * NA + 1) * (2 * MA + 1) * ((a * NA + b * MA) * 2 ^ F)\n\n')
        las = ['2 ^ SA', '2', '2', '2'] + [self.Ldef(i) for i in range(4, self.nvar)]
        out.append('/-- The `ℓ¹` bounds of the variable polynomials (list; static, from the field widths). -/\n'
                   'def LAl : List ℕ :=%s\n\n' % lst(las))
        out.append('/-- The `ℓ¹` bounds of the variable polynomials. -/\ndef LA (i : ℕ) : ℕ := LAl.getD i 0\n\n')
        out.append("""/-- The Kronecker images of the variable polynomials. -/
def KvA (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SA * ((1 <<< (b * (NA + W * MA)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => packGridNM b W NA (gA (n + 4)) (2 * MA + 1)

/-- The honest centres. -/
def xA (i : ℕ) : FA := ctr SA NA MA (WtA i) (PlA i)

/-- The phases are below `4`. -/
theorem hWA : ∀ i, (WtA i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxA : ∀ i, InBox (PlA i) (BxA i).1 (BxA i).2
  | 0 => InBox.monomial NA MA _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NA MA _

""")
        cst = ['l1_Tpoly SA NA MA', 'l1_Vpoly', 'l1_sPoly', 'l1_cPoly']
        out.append('/-- `ℓ¹` bounds: the empty chain. -/\n'
                   'theorem l1A_0 : ∀ i, i < 0 → l1 (PlA i) ≤ LA i := fun i h => absurd h (Nat.not_lt_zero i)\n\n')
        for i in range(self.nvar):
            pf = cst[i] if i < 4 else self.l1proof(i)
            out.append('set_option maxRecDepth 100000 in\n/-- `ℓ¹` bounds up to the variable `%s`. -/\n'
                       'theorem l1A_%d : ∀ i, i < %d → l1 (PlA i) ≤ LA i :=\n  chain_succ l1A_%d\n    (%s)\n\n'
                       % (self.nm(i), i + 1, i + 1, i, pf))
        out.append("""set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds. -/
theorem l1A (i : ℕ) : l1 (PlA i) ≤ LA i := by
  rcases lt_or_ge i %d with h | h
  · exact l1A_%d i h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact (l1_gridPolyNM_le_const NA MA (C := 0) fun i j _ _ => by rw [gA_out n]; simp).trans
      (by simp)

""" % (self.nvar, self.nvar))
        # the out-of-range lemmas must precede l1A: emit them before
        txt = ''.join(out)
        pre = """/-- The grids vanish beyond the last variable. -/
theorem gA_out (n : ℕ) : gA (n + %d) = fun _ _ => 0 := by
  unfold gA
  have h : gAl.length = %d := by rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

""" % (self.nvar, self.nvar)
        txt = txt.replace('/-- `ℓ¹` bounds: the empty chain. -/', pre + '/-- `ℓ¹` bounds: the empty chain. -/')
        out = [txt]
        out.append("""/-- The Kronecker images. -/
theorem kronA : ∀ b W i, kron b W (PlA i) = KvA b W i
  | b, W, 0 => kron_Tpoly SA NA MA b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NA MA _

/-- The centre of `t` is `1`. -/
theorem xA_t : xA 0 = 1 := ctr_Tpoly SA NA MA

/-- The centre of `V` is `1`. -/
theorem xA_V : xA 1 = 1 := ctr_Vpoly SA NA MA

/-- The centre of `C` is `cos ψₒ`. -/
theorem xA_C : xA 2 = cSo := ctr_C_o SA NA MA

/-- The centre of `S` is `sin ψₒ`. -/
theorem xA_S : xA 3 = sSo := ctr_S_o SA NA MA

""")
        out.append('/-- The norm bounds of the centres (list). -/\ndef BAl : List ℚ :=%s\n\n' % lst(
            [qlean(self.pl.B[i]) for i in range(self.nvar)]))
        out.append('/-- The norm bounds of the centres. -/\ndef BA (i : ℕ) : ℚ := BAl.getD i 0\n\n')
        out.append('/-- The radii of the balls (list). -/\ndef EAl : List ℚ :=%s\n\n' % lst(
            [qlean(self.pl.E[i]) for i in range(self.nvar)]))
        out.append('/-- The radii of the balls. -/\ndef EA (i : ℕ) : ℚ := EAl.getD i 0\n\n')
        # monomial table
        idx = self.idx
        tab = [0] * (19 * 8)
        for a in range(19):
            for b in range(8):
                v = 0
                if a == 0 and b == 0:
                    v = idx['t']
                elif b == 0 and a in idx['Rp']:
                    v = idx['Rp'][a]
                elif a == 0 and b in idx['Zp']:
                    v = idx['Zp'][b]
                elif (a, b) in idx['Mono']:
                    v = idx['Mono'][(a, b)]
                tab[a * 8 + b] = v
        self.monotab = tab
        out.append('/-- The monomial table: entry `8a + b` is the variable of `R^a z^b`. -/\ndef monoTab : List ℕ :=%s\n\n'
                   % lst([str(v) for v in tab]))
        out.append('/-- The variable of the monomial `R^a z^b`. -/\ndef monoA (a b : ℕ) : ℕ := monoTab.getD (a * 8 + b) 0\n\n')
        pairs = sorted(set([(0, 0)] + [(a, 0) for a in idx['Rp']] + [(0, b) for b in idx['Zp']] + list(idx['Mono'])))
        self.pairs = pairs
        out.append('/-- The monomials of the chain. -/\ndef pairsA : List (ℕ × ℕ) :=%s\n\n' % lst(
            ['(%d, %d)' % ab for ab in pairs]))
        out.append("""/-- The R-form polynomials of the field quantities `D, D_u, D_z, n_R, n_R,u, n_R,z, n_z, n_z,u,
n_z,z` (`R = R₀ + u`; `Design/DommaschkKamFieldData`, `DommaschkKamIdentCheck`). -/
def polyA : ℕ → DkPoly.SP
""")
        for k, nmk in enumerate(POLY_ORDER):
            out.append('  | %d => %s\n' % (k, POLY_LEAN[nmk]))
        out.append('  | _ => []\n\n')
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    # ---------------------------------------------------------------- trees
    def tree_text(self, n):
        r = self.nodes.get(n) if isinstance(n, int) else n
        rel = r['rel']
        if rel[0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = rel
            if a == 0:
                return 'polyT %s 3 monoA ((polyA %d).take %d)' % (qlean(r['c']), kp, ln)
            return ('.add (.mul (.cst %d) (pwT 1 3 (.var %d))) (polyT %s 3 monoA (((polyA %d).drop %d).take %d))'
                    % (r['c'], prev, qlean(r['c']), kp, a, ln))
        if rel[0] in ('V0R', 'V0Z'):
            src = 4 if rel[0] == 'V0R' else 5
            cen = 'cenR' if rel[0] == 'V0R' else 'cenZ'
            return '.sub (.mul (.cst %d) (pwT 1 3 (.var %d))) (polyT %s 3 (fun _ _ => 0) %s)' % (
                r['c'], src, qlean(r['c']), cen)
        if rel[0] in ('AR1', 'AZ1'):
            cen = 'cenR' if rel[0] == 'AR1' else 'cenZ'
            return 'polyT %s 3 (fun _ _ => 0) (DkPoly.phiS %s)' % (qlean(r['c']), cen)
        return tree_lean(r['tree'])

    def emit_trees(self):
        mod = 'DommaschkKamCAdmTrees'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmEnv\n']
        out.append("""
/-!
# Expression trees of the torus-C admissibility chain

The expression trees (`Certificates/KronExpr`, `Ex`) of the nodes of the low-resolution ball chain
of Dommaschk torus C: products of centres, the field polynomials as `polyT` trees of the R-form
sparse polynomials `polyA k` (`Design/DommaschkKamCKronW`), the frame vectors and centre
derivatives as `polyT` trees of the centre polynomials, and the norm nodes. Generated by
`scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section

namespace %s

%s
""" % (NS, OPEN))
        for s in self.pl.steps:
            if s.get('kind') in ('node', 'norm'):
                what = 'node `%s` (variable `%d`)' % (s['name'], s['n']) if s['kind'] == 'node' else 'norm node `%s`' % s['name']
                out.append('set_option linter.style.longLine false in\n/-- Expression tree of the %s. -/\ndef trA_%s : Ex :=\n  %s\n\n' % (
                    what, s['name'], wrap(self.tree_text(s), 2)))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    # ---------------------------------------------------------------- checks
    def center_lines(self, i):
        r = self.pl.normrec[i]
        o = []
        o.append('set_option linter.style.longLine false in\n')
        o.append('/-- Proof-term check of the norm of the centre `%s`. -/\n' % self.nm(i))
        o.append('theorem cA_%s : centerKw 68553 16 NA MA KvA %d %d %d %d %d %d %d ≤ %d := by\n  kron2_proof\n\n' % (
            self.nm(i), i, r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K']))
        o.append('/-- A priori `ℓ¹` bound of the centre `%s`. -/\n' % self.nm(i))
        o.append('theorem clA_%s : LA %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (self.nm(i), i, r['b']))
        return o

    def node_lines(self, r):
        n = r['n']
        c = r['c']
        cl = '(%d : ℤ)' % c if c >= 0 else '(-%d : ℤ)' % (-c)
        o = []
        o.append('set_option linter.style.longLine false in\n')
        o.append('/-- Proof-term check of the node `%s`: truncation norm. -/\n' % r['name'])
        o.append('theorem kA_%s : nodeKw 68553 16 SA NA MA WtA KvA trA_%s %s %d %d %d %d %d %d %d %d %d %d ≤ %d := by\n'
                 '  kron2_proof\n\n' % (r['name'], r['name'], cl, r['dd'], r['de'], n, r['b'], r['W'], r['dc'], r['dr'],
                                        r['J'], r['Ki'], r['Kj'], r['K']))
        o.append('/-- Proof-term check of the node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'])
        o.append('theorem lA_%s : nodeL1 SA LA trA_%s %s %d %d %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (
            r['name'], r['name'], cl, r['dd'], r['de'], n, r['b']))
        return o

    def norm_lines(self, r):
        o = []
        o.append('set_option linter.style.longLine false in\n')
        o.append('/-- Proof-term check of the norm node `%s`. -/\n' % r['name'])
        o.append('theorem kA_%s : normKw 68553 16 NA MA WtA KvA trA_%s (%d, %d, %d) %d %d %d %d %d %d %d ≤ %d := by\n'
                 '  kron2_proof\n\n' % (r['name'], r['name'], r['w'][0], r['w'][1], r['w'][2], r['b'], r['W'], r['dc'],
                                        r['dr'], r['J'], r['Ki'], r['Kj'], r['K']))
        o.append('/-- Proof-term check of the norm node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'])
        o.append('theorem lA_%s : Ex.majN LA trA_%s < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (r['name'], r['name'], r['b']))
        return o

    def emit_checks(self, nfiles, dry=False):
        items = []
        for i in range(4, self.nvar):
            items.append(('c', i))
        for s in self.pl.steps:
            if s.get('kind') == 'node':
                items.append(('n', s))
            elif s.get('kind') == 'norm':
                items.append(('m', s))
        # balance by image size
        def cost(it):
            k, x = it
            if k == 'c':
                r = self.pl.normrec[x]
                return r['W'] * (2 * self.M + 1) * r['b']
            return x['W'] * (x['J'] + 1) * x['b'] * (3 if x['rel'] and x['rel'][0] == 'poly' else 1)
        bins = [[] for _ in range(nfiles)]
        load = [0] * nfiles
        for it in sorted(items, key=cost, reverse=True):
            f = min(range(nfiles), key=lambda k: load[k])
            bins[f].append(it)
            load[f] += cost(it)
        mods = []
        for f, ch in enumerate(bins):
            ch.sort(key=lambda it: it[1] if it[0] == 'c' else it[1]['n'] + 0.5)
            mod = 'DommaschkKamCAdmCheck%d' % (f + 1)
            mods.append(mod)
            if dry:
                continue
            out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmTrees\n',
                   'public import PlasmaLean.Certificates.KronProof2D\n',
                   'meta import PlasmaLean.Design.DommaschkKamCAdmTrees\n']
            out.append("""
/-!
# Proof-term checks of the torus-C admissibility chain (part %d)

Each theorem is an explicit proof term (`kron2_proof` of `Certificates/KronProof2D`; `kron_lt` for
the `ℓ¹` bounds) on the data of `Design/DommaschkKamCAdmData*`: the weighted digit sums
(`nodeKw`, `normKw`, `centerKw` of `Design/DommaschkKamCKronW`, strip weights `68553^s 2^{16(K−s)}`)
of the Kronecker images of the truncation polynomials of the ball chain, and their a priori `ℓ¹`
bounds. Generated by `scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section

namespace %s

%s
""" % (f + 1, NS, OPEN))
            for kind, x in ch:
                out += self.center_lines(x) if kind == 'c' else self.node_lines(x) if kind == 'n' else self.norm_lines(x)
            out.append('end %s\n' % NS)
            self.write(mod, ''.join(out))
        self.checkmods = mods
        self.checkload = load
        return mods


    # ---------------------------------------------------------------- honest values and node identities
    def honest(self, i):
        idx = self.idx
        k = self.pl.kind[i]
        nm = self.nm(i)
        if i == 0 or i == 1:
            return '1'
        if i == 2:
            return 'cSo'
        if i == 3:
            return 'sSo'
        if k in ('data', 'derived'):
            return 'xA %d' % i
        if i == idx['R']:
            return 'RvA'
        for a, v in idx['Rp'].items():
            if v == i:
                return 'RvA ^ %d * zvA ^ 0' % a
        for b, v in idx['Zp'].items():
            if v == i:
                return 'RvA ^ 0 * zvA ^ %d' % b
        for (a, b), v in idx['Mono'].items():
            if v == i:
                return 'RvA ^ %d * zvA ^ %d' % (a, b)
        r = self.nodes.get(i)
        if r is not None and r['rel'][0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = r['rel']
            if final:
                return 'fA %d' % kp
            return 'DkPoly.ev xRo ((polyA %d).take %d)' % (kp, a + ln)
        return nm + 'a'

    def emit_rel(self):
        idx = self.idx
        mod = 'DommaschkKamCAdmRel'
        iqD, iqW = idx['qD'], idx['qW']
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmTrees\n']
        out.append("""
/-!
# Honest values of the torus-C admissibility chain

The value `XA i` of each variable of the low-resolution ball chain of Dommaschk torus C, at the
surrogate torus `(xA 4, xA 5)` (oracle angle): `R = R₀ + U` (`RvA`), the powers and monomials
`R^a z^b`, the field quantities `fA k = ev xRo (polyA k)` (R-form), the frame vectors `V0Ra`,
`V0Za`, `W₀`, the centre derivatives, the torsion numerator `Pa` (the `Pp` formula), the products of
the approximate inverses and the torsion centre `Ya = R⁷ P qD³ qW²`; and the identity of every node:
`c · X n = eval X e` (`relA_*`), by `ring` for products and by `eval_polyT` for the polynomial
trees. Generated by `scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- `R = R₀ + U` at the surrogate torus. -/
def RvA : FA := algebraMap ℂ FA ((R0q : ℚ) : ℂ) + xA 4

/-- `z` at the surrogate torus. -/
def zvA : FA := xA 5

/-- The R-form evaluation point `(R, z, cos ψₒ, sin ψₒ, 0, 0)`. -/
def xRo : Fin 6 → FA := ![RvA, zvA, cSo, sSo, 0, 0]

/-- The field quantity `k` (`polyA k`) at the surrogate torus. -/
def fA (k : ℕ) : FA := DkPoly.ev xRo (polyA k)

/-- The radial frame vector `U − a_R` at the surrogate torus. -/
def V0Ra : FA := xA 4 - DkPoly.ev xRo cenR

/-- The vertical frame vector `z − a_z` at the surrogate torus. -/
def V0Za : FA := xA 5 - DkPoly.ev xRo cenZ

/-- `W₀ = ∂_θU V₀_z − ∂_θz V₀_R` at the surrogate torus. -/
def W0a : FA := xA 6 * V0Za - xA 7 * V0Ra

/-- `a_R' = d a_R/dφ`. -/
def AR1a : FA := DkPoly.ev xRo (DkPoly.phiS cenR)

/-- `a_z' = d a_z/dφ`. -/
def AZ1a : FA := DkPoly.ev xRo (DkPoly.phiS cenZ)

/-- `D²`. -/
def DDa : FA := fA 0 * fA 0

/-- `∇n_R · V₀`. -/
def G1a : FA := fA 4 * V0Ra + fA 5 * V0Za

/-- `∇D · V₀`. -/
def G2a : FA := fA 1 * V0Ra + fA 2 * V0Za

/-- `∇n_z · V₀`. -/
def G3a : FA := fA 7 * V0Ra + fA 8 * V0Za

/-- `Y_R = n_R D − D ∇n_R·V₀ + n_R ∇D·V₀ − D² a_R'`. -/
def YRa : FA := fA 3 * fA 0 - fA 0 * G1a + fA 3 * G2a - DDa * AR1a

/-- `Y_z = n_z D − D ∇n_z·V₀ + n_z ∇D·V₀ − D² a_z'`. -/
def YZa : FA := fA 6 * fA 0 - fA 0 * G3a + fA 6 * G2a - DDa * AZ1a

/-- The torsion numerator `P = Y_R V₀_z − Y_z V₀_R` at the surrogate torus. -/
def Pa : FA := YRa * V0Za - YZa * V0Ra

/-- `R⁷ P`. -/
def PRa : FA := RvA ^ 7 * Pa

/-- `qD²`. -/
def qD2a : FA := xA %d * xA %d

/-- `qD³`. -/
def qD3a : FA := qD2a * xA %d

/-- `qW²`. -/
def qW2a : FA := xA %d * xA %d

/-- `qD³ qW²`. -/
def qDWa : FA := qD3a * qW2a

/-- The torsion centre `Y = R⁷ P qD³ qW²`. -/
def Ya : FA := PRa * qDWa

""" % (NS, OPEN, iqD, iqD, iqD, iqW, iqW))
        out.append('set_option maxHeartbeats 4000000 in\n-- elaborating a literal list of 195 strip-algebra elements\n/-- The honest values of the variables (list). -/\ndef XAl : List FA :=%s\n\n'
                   % lst([self.honest(i) for i in range(self.nvar)]))
        out.append('/-- The honest values of the variables. -/\ndef XA (i : ℕ) : FA := XAl.getD i 0\n\n')
        # the monomial table
        pairs = self.pairs
        cases = []
        for (a, b) in pairs:
            v = self.monotab[a * 8 + b]
            h = self.honest(v)
            if h == 'RvA ^ %d * zvA ^ %d' % (a, b):
                cases.append('  · rfl\n')
            else:
                cases.append('  · change %s = RvA ^ %d * zvA ^ %d\n    simp [zvA]\n' % (h, a, b))
        out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The monomial variables have the values `R^a z^b`. -/
theorem XA_mono : ∀ ab ∈ pairsA, XA (monoA ab.1 ab.2) = RvA ^ ab.1 * zvA ^ ab.2 := by
  intro ab hab
  simp only [pairsA, List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with %s
%s
""" % (wrap(' | '.join(['rfl'] * len(pairs)), 2), ''.join(cases)))
        out.append("""/-- The monomial hypothesis of `eval_polyT` from the table. -/
theorem hmonoA {p : DkPoly.SP} (h : ∀ t ∈ p, (t.a, t.b) ∈ pairsA) :
    ∀ t ∈ p, XA (monoA t.a t.b) = xRo 0 ^ t.a * xRo 1 ^ t.b := fun t ht => by
  simpa [xRo] using XA_mono (t.a, t.b) (h t ht)

/-- Table membership from a Boolean check. -/
theorem pairs_of_all {l : DkPoly.SP} (h : l.all (fun t => pairsA.contains (t.a, t.b)) = true) :
    ∀ t ∈ l, (t.a, t.b) ∈ pairsA := fun t ht => by
  have := List.all_eq_true.1 h t ht
  simpa using this

/-- `ev` of a concatenation. -/
theorem ev_appendA (x : Fin 6 → FA) (p q : DkPoly.SP) :
    DkPoly.ev x (p ++ q) = DkPoly.ev x p + DkPoly.ev x q := by
  simp [DkPoly.ev]

/-- **The identity of the first chunk node of a polynomial** from kernel-checkable facts. -/
theorem relChunk0A {n k len : ℕ} {L : ℚ} {c : ℤ} (hc : (c : ℚ) = L)
    (hn : XA n = DkPoly.ev xRo ((polyA k).take len)) (hne : 0 < ((polyA k).take len).length)
    (hint : ∀ t ∈ (polyA k).take len, (L * t.q).den = 1)
    (hp : ((polyA k).take len).all (fun t => pairsA.contains (t.a, t.b)) = true) :
    (c : ℂ) • XA n = Ex.eval XA (polyT L 3 monoA ((polyA k).take len)) := by
  rw [eval_polyT XA rfl xRo rfl rfl L 3 monoA _ (List.ne_nil_of_length_pos hne) hint
    (hmonoA (pairs_of_all hp)), hn, ← hc]
  push_cast; rfl

/-- **The identity of a later chunk node of a polynomial**: the previous partial sum plus the
next chunk of terms. -/
theorem relChunkA {n m k a len : ℕ} {L : ℚ} {c : ℤ} (hc : (c : ℚ) = L)
    (hn : XA n = DkPoly.ev xRo ((polyA k).take (a + len)))
    (hm : XA m = DkPoly.ev xRo ((polyA k).take a))
    (hne : 0 < (((polyA k).drop a).take len).length)
    (hint : ∀ t ∈ ((polyA k).drop a).take len, (L * t.q).den = 1)
    (hp : (((polyA k).drop a).take len).all (fun t => pairsA.contains (t.a, t.b)) = true) :
    (c : ℂ) • XA n = Ex.eval XA (.add (.mul (.cst c) (pwT 1 3 (.var m)))
      (polyT L 3 monoA (((polyA k).drop a).take len))) := by
  rw [Ex.eval, eval_polyT XA rfl xRo rfl rfl L 3 monoA _ (List.ne_nil_of_length_pos hne) hint
    (hmonoA (pairs_of_all hp)), hn, List.take_add, ev_appendA, Ex.eval, Ex.eval, eval_pwT, ← hm,
    ← hc]
  have h1 : XA 1 = 1 := rfl
  rw [h1, one_pow, one_mul, smul_add, Algebra.smul_def, map_intCast]
  push_cast; rfl

/-- The value of the tree of an angle-only polynomial (monomials read from `t = 1`). -/
theorem evalCenA {L : ℚ} {p : DkPoly.SP} (hne : 0 < p.length) (hint : ∀ t ∈ p, (L * t.q).den = 1)
    (hao : ∀ t ∈ p, t.a = 0 ∧ t.b = 0) :
    Ex.eval XA (polyT L 3 (fun _ _ => 0) p) = ((L : ℚ) : ℂ) • DkPoly.ev xRo p := by
  refine eval_polyT XA rfl xRo rfl rfl L 3 _ p (List.ne_nil_of_length_pos hne) hint ?_
  intro t ht
  obtain ⟨h1, h2⟩ := hao t ht
  rw [h1, h2]
  change (1 : FA) = _
  simp

""")
        def split(p):
            return '[' + ', '.join('⟨(%d : ℚ) / %d, %d, %d, %d, %d⟩' % (q.numerator, q.denominator, a, b, c, d)
                                   for q, a, b, c, d in p) + ']'
        for nmA, cen, lst_ in (('aRdA', 'cenR', self.ctx['aRd']), ('aZdA', 'cenZ', self.ctx['aZd'])):
            out.append('/-- `phiS %s` as an explicit list. -/\ndef %s : DkPoly.SP :=\n  %s\n\n' % (cen, nmA, wrap(split(lst_), 2)))
            out.append('/-- `phiS %s` (kernel check). -/\ntheorem %s_eq : DkPoly.phiS %s = %s := by kernel_fact\n\n'
                       % (cen, nmA, cen, nmA))
        for s in self.pl.steps:
            if s.get('kind') != 'node':
                continue
            out += self.rel_lines(s)
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    def rel_lines(self, r):
        n, c, rel = r['n'], r['c'], r['rel']
        cl = '((%d : ℤ) : ℂ)' % c
        o = ['set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n/-- The identity of the node `%s`. -/\n' % r['name']]
        head = 'theorem relA_%s : %s • XA %d = Ex.eval XA trA_%s := by\n' % (r['name'], cl, n, r['name'])
        if rel[0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = rel
            hn = ('(by rw [List.take_of_length_le (by kernel_fact)]; rfl)' if final else 'rfl')
            o.append(head)
            if a == 0:
                o.append('  exact relChunk0A (L := %s) (by norm_num) %s (by kernel_fact) (by kernel_fact)\n'
                         '    (by kernel_fact)\n\n' % (qlean(c), hn))
            else:
                o.append('  exact relChunkA (L := %s) (a := %d) (len := %d) (by norm_num) %s rfl (by kernel_fact)\n'
                         '    (by kernel_fact) (by kernel_fact)\n\n' % (qlean(c), a, ln, hn))
            return o
        def haves(vs):
            return ''.join('  have e%d : XA %d = %s := rfl\n' % (v, v, self.honest(v)) for v in sorted(set(vs)))
        if rel[0] in ('V0R', 'V0Z'):
            src = 4 if rel[0] == 'V0R' else 5
            o.append(head)
            o.append(haves([n, src, 1]))
            o.append('  rw [trA_%s, Ex.eval, Ex.eval, evalCenA (by kernel_fact) (by kernel_fact) (by kernel_fact), e%d, %s]\n'
                     '  simp only [Ex.eval, eval_pwT, e%d, e1, one_pow, one_mul, Algebra.smul_def, map_ofNat,\n'
                     '    Int.cast_ofNat, Rat.cast_ofNat]\n'
                     '  ring\n\n' % (r['name'], n, rel[0] + 'a', src))
            return o
        if rel[0] in ('AR1', 'AZ1'):
            o.append(head)
            o.append(haves([n]))
            ad = 'aRdA' if rel[0] == 'AR1' else 'aZdA'
            o.append('  rw [trA_%s, %s_eq, evalCenA (by kernel_fact) (by kernel_fact) (by kernel_fact), e%d, %s,\n'
                     '    %s_eq]\n  push_cast\n  rfl\n\n' % (r['name'], ad, n, rel[0] + 'a', ad))
            return o
        if rel[0] == 'R':
            o.append(head)
            o.append(haves([n, 0, 4]))
            o.append('  simp only [trA_R, Ex.eval, e%d, e0, e4, RvA, R0q]\n'
                     '  rw [smul_add, Algebra.smul_def, ← map_mul]\n'
                     '  have h : (((32 : ℤ) : ℂ) * (((29 / 32 : ℚ) : ℚ) : ℂ)) = 29 := by push_cast; norm_num\n'
                     '  rw [h]\n  simp only [Algebra.smul_def, map_ofNat, Int.cast_ofNat, mul_one]\n\n' % n)
            return o
        o.append(head)
        vs = [n] + sorted(AB.tree_vars(r['tree']))
        o.append(haves(vs))
        deps = {'Ya': ['PRa', 'qDWa'], 'PRa': ['Pa'], 'Pa': ['YRa', 'YZa'], 'YRa': ['G1a', 'G2a', 'DDa'],
                'YZa': ['G3a', 'G2a', 'DDa'], 'qDWa': ['qD3a', 'qW2a'], 'qD3a': ['qD2a']}
        allnames = ['DDa', 'G1a', 'G2a', 'G3a', 'YRa', 'YZa', 'Pa', 'PRa', 'qD2a', 'qD3a', 'qW2a', 'qDWa', 'Ya',
                    'W0a', 'zvA']
        txt = ' '.join(self.honest(v) for v in vs)
        used = set(x for x in allnames if re.search(r'\b%s\b' % x, txt))
        work = list(used)
        while work:
            x = work.pop()
            for y in deps.get(x, []):
                if y not in used:
                    used.add(y)
                    work.append(y)
        extra = (', ' + ', '.join(sorted(used))) if used else ''
        o.append('  simp only [trA_%s, Ex.eval, %s, Int.cast_one, one_smul%s]\n%s\n' % (
            r['name'], ', '.join('e%d' % v for v in sorted(set(vs))), extra,
            '' if r['name'] in NORING else '  ring\n'))
        return o

    # ---------------------------------------------------------------- the chain
    def emit_chain(self):
        mod = 'DommaschkKamCAdmChain'
        NV = self.nvar
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmRel\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.checkmods]
        out.append("""
/-!
# The low-resolution ball chain of torus C

The balls `‖X i − x i‖_r ≤ E i` of all variables of the admissibility chain of Dommaschk torus C at
the surrogate torus (`XA`, `Design/DommaschkKamCAdmRel`), on every strip `r ≥ 0` with
`e^r ≤ 68553/2^16`, built variable by variable (`ballA_k`, `chain_succ`) from the kernel checks
of `Design/DommaschkKamCAdmCheck*` (`node_fullw`, `center_fullw` of `Design/DommaschkKamCKronW`)
and the node identities `relA_*`; and the norm nodes `nA_*`. Generated by
`scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
set_option linter.unusedVariables false in
/-- Norms of the centres: the empty chain. -/
theorem normA_0 {r : ℝ} (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) :
    ∀ i, i < 0 → Bd r (xA i) (BA i) := fun i h => absurd h (Nat.not_lt_zero i)

""" % (NS, OPEN))
        cst = ['by rw [xA_t]; exact (Bd_one r).le (by exact_mod_cast (show (1 : ℚ) ≤ BA 0 by kernel_fact))',
               'by rw [xA_V]; exact (Bd_one r).le (by exact_mod_cast (show (1 : ℚ) ≤ BA 1 by kernel_fact))',
               'by rw [xA_C]; exact (Bd_cSo_q hq).le (by exact_mod_cast (show ((68553 : ℕ) / 2 ^ 16 : ℚ) ≤ BA 2 by kernel_fact))',
               'by rw [xA_S]; exact (Bd_sSo_q hq).le (by exact_mod_cast (show ((68553 : ℕ) / 2 ^ 16 : ℚ) ≤ BA 3 by kernel_fact))']
        for i in range(NV):
            if i < 4:
                pf = cst[i]
            else:
                r = self.pl.normrec[i]
                pf = ('center_fullw hq boxA l1A kronA (fun _ => rfl) %d %d %d %d %d %d %d %d %d\n'
                      '      (BA %d) rfl (by kernel_fact) clA_%s rfl cA_%s (by kernel_fact)' % (
                          i, self.pl.W[i][2], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], i,
                          self.nm(i), self.nm(i)))
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- Norms of the centres up to the variable `%s`. -/
theorem normA_%d {r : ℝ} (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) :
    ∀ i, i < %d → Bd r (xA i) (BA i) :=
  chain_succ (normA_%d hq)
    (%s)

""" % (self.nm(i), i + 1, i + 1, i, pf))
        out.append("""/-- **Norms of the centres.** -/
theorem normA {r : ℝ} (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) :
    ∀ i, i < %d → Bd r (xA i) (BA i) := normA_%d hq

""" % (NV, NV))
        hyp = '{r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16)'
        out.append("""set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- The empty chain. -/
theorem ballA_0 %s : ∀ i, i < 0 → Bd r (XA i - xA i) (EA i) :=
  fun i h => absurd h (Nat.not_lt_zero i)

""" % hyp)
        for k in range(NV):
            nmk = self.nm(k)
            if k < 4:
                step = 'step_exact_w %s.symm (by kernel_fact)' % ['xA_t', 'xA_V', 'xA_C', 'xA_S'][k]
            elif self.pl.kind[k] in ('data', 'derived'):
                step = 'step_exact_w rfl (by kernel_fact)'
            else:
                r = self.nodes[k]
                cl = '(%d : ℤ)' % r['c']
                step = ('node_fullw hr hq hWA boxA l1A kronA (fun _ => rfl)\n'
                        '      (fun i hi => normA hq i (by omega)) (ballA_%d hr hq) trA_%s %d %d %d %s\n'
                        '      %d %d %d %d %d %d %d %d %d (by kernel_fact) (by kernel_fact) (by kernel_fact)\n'
                        '      (by norm_num) (by kernel_fact) lA_%s kA_%s (by kernel_fact) relA_%s' % (
                            k, nmk, r['dd'], r['de'], r['p'], cl, r['A'], r['J'], r['b'], r['W'], r['dc'], r['dr'],
                            r['Ki'], r['Kj'], r['K'], nmk, nmk, nmk))
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The chain up to the variable `%s`. -/
theorem ballA_%d %s :
    ∀ i, i < %d → Bd r (XA i - xA i) (EA i) :=
  chain_succ (ballA_%d hr hq)
    (%s)

""" % (nmk, k + 1, hyp, k + 1, k, step))
        out.append("""set_option linter.style.longLine false in
/-- **All balls of the chain.** -/
theorem ballA_all %s : ∀ i, i < %d → Bd r (XA i - xA i) (EA i) :=
  ballA_%d hr hq

set_option linter.style.longLine false in
/-- **Value bounds**: `‖X i‖ ≤ B i + E i`. -/
theorem valA_le %s (i : ℕ) (hi : i < %d) : Bd r (XA i) ((BA i + EA i : ℚ) : ℝ) := by
  have := (normA hq i hi).add (ballA_all hr hq i hi)
  rw [add_sub_cancel] at this; push_cast; exact this

""" % (hyp, NV, NV, hyp, NV))
        for r in self.normnodes:
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The norm node `%s`. -/
theorem nA_%s %s : Bd r (Ex.eval XA trA_%s) ((%s : ℚ) : ℝ) :=
  norm_fullw hr hq hWA boxA l1A kronA (fun _ => rfl) (fun i hi => normA hq i hi) (ballA_all hr hq)
    trA_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d %s (by kernel_fact) (by kernel_fact) (by kernel_fact)
    lA_%s kA_%s (by kernel_fact)

""" % (r['name'], r['name'], hyp, r['name'], qlean(r['bound']), r['name'], r['w'][0], r['w'][1], r['w'][2], r['A'],
       r['J'], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], qlean(r['bound']), r['name'], r['name']))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))


    # ---------------------------------------------------------------- tails (closeness of the data torus)
    def tail_static(self, which, a, b):
        ctx = self.ctx
        Nc, Mc, Sc, Fc = ctx['Nc'], ctx['Mc'], ctx['Sc'], ctx['Fc']
        sh = Sc - self.S
        Fl = ctx['FU'] if which == 'U' else ctx['FZ']
        C = 2 ** Fc + 2 ** sh * 2 ** Fl
        w = (a * Nc + b * Mc) if (a, b) != (0, 0) else 1
        return (2 * Nc + 1) * (2 * Mc + 1) * w * C, C

    def emit_tail(self):
        ctx = self.ctx
        Nc, Mc, Sc, Fc = ctx['Nc'], ctx['Mc'], ctx['Sc'], ctx['Fc']
        dN, dM, sh = Nc - self.N, Mc - self.M, Sc - self.S
        FU, FZ = ctx['FU'], ctx['FZ']
        # ---- the kernel checks
        mod = 'DommaschkKamCAdmTailCheck'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmEnv\n',
               'public import PlasmaLean.Certificates.KronProof2D\n',
               'meta import PlasmaLean.Design.DommaschkKamCAdmEnv\n']
        out.append("""
/-!
# Kernel checks: closeness of the data torus C to the low-resolution surrogate

The difference grids `dGU`, `dGZ` of the data torus (`Design/DommaschkKamCTorus`, `%d × %d`, scale
`2^{−%d}`) and the embedded surrogate of the admissibility chain (`%d × %d`, scale `2^{−%d}`), in
the layout of the data, and the weighted digit sums of their Kronecker images and of the images of
their `θ`- and `ψ`-weighted versions (`kron2_proof`; strip weights `68553^s 2^{16(K − s)}`).
Generated by `scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section

namespace %s

%s
/-- The weighted grid `(a (i − N) + b (j − M)) g` of the full layout. -/
def wGc (a b : ℕ) (g : ℕ → ℕ → ℤ) : ℕ → ℕ → ℤ :=
  fun i j => (((a : ℕ) : ℤ) * ((i : ℤ) - Nc) + ((b : ℕ) : ℤ) * ((j : ℤ) - Mc)) * g i j

/-- The difference grid of `U`. -/
def dGU : ℕ → ℕ → ℤ := fun i j => gU i j - embedGrid NA MA %d %d %d (gA 4) i j

/-- The difference grid of `z`. -/
def dGZ : ℕ → ℕ → ℤ := fun i j => gZ i j - embedGrid NA MA %d %d %d (gA 5) i j

""" % (Nc, Mc, Sc, self.N, self.M, self.S, NS, OPEN, dN, dM, sh, dN, dM, sh))
        self.tailrec = {}
        Wd = 2 * Nc + 1
        R = 2 * Mc + 1
        head2 = ''.join(out[:4]).replace('public import PlasmaLean.Design.DommaschkKamCAdmEnv\n',
                                         'public import PlasmaLean.Design.DommaschkKamCAdmTailCheck\n').replace(
            'meta import PlasmaLean.Design.DommaschkKamCAdmEnv\n', 'meta import PlasmaLean.Design.DommaschkKamCAdmTailCheck\n')
        out2 = [head2, """
/-!
# Kernel checks: closeness of the data torus C to the surrogate (the `z` part)

The weighted digit sums of the Kronecker images of the `z` difference grid `dGZ` and its `θ`- and
`ψ`-weighted versions (`Design/DommaschkKamCAdmTailCheck` has the `U` part). Generated by
`scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section

namespace %s

%s
""" % (NS, OPEN)]
        for nm, which, a, b in (('U', 'U', 0, 0), ('Z', 'Z', 0, 0), ('AU', 'U', 1, 0), ('AZ', 'Z', 1, 0),
                                ('PU', 'U', 0, 1), ('PZ', 'Z', 0, 1)):
            Lst, C = self.tail_static(which, a, b)
            tb = self.tails[{'U': 'U', 'Z': 'Z', 'AU': 'A', 'AZ': 'B', 'PU': 'Pu', 'PZ': 'Pz'}[nm]]
            bb = AB.clog2(Lst + 1) + 2
            assert Lst < 2 ** (bb - 1)
            grid = 'dG%s' % which if (a, b) == (0, 0) else '(wGc %d %d dG%s)' % (a, b, which)
            K = tb['K']
            val = Fr(K, 2 ** (E_EXP * (Nc + Mc)) * 2 ** Sc)
            assert tb['bound'] >= val
            self.tailrec[nm] = dict(b=bb, K=K, bound=tb['bound'], grid=grid, a=a, b_=b, which=which)
            (out if which == 'U' else out2).append("""set_option linter.style.longLine false in
/-- Kernel check: the weighted norm of the tail grid `%s`. -/
theorem tk_%s : wl1KronP %d %d %d %d (2 * Mc + 1) (fun i => kwtS 68553 16 Nc (ndist i (1 * Nc)))
    (fun j => kwtS 68553 16 Mc (ndist j (1 * Mc + 0))) (packGridNM %d %d Nc %s (2 * Mc + 1)) ≤ %d := by
  kron2_proof

""" % (nm, nm, bb, Wd, AB.clog2(Wd), AB.clog2(R), bb, Wd, grid, K))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))
        out2.append('end %s\n' % NS)
        self.write('DommaschkKamCAdmTailCheckZ', ''.join(out2))
        # ---- the lemmas
        mod = 'DommaschkKamCAdmTail'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmTailCheckZ\n']
        out.append("""
/-!
# Closeness of the data torus C to the low-resolution surrogate

The data torus `(Uo, Zo)` (`Design/DommaschkKamCTorus`) and the surrogate `(xA 4, xA 5)` of the
admissibility chain, both in the oracle angle: the differences, and their `∂_θ`, `∂_ψ`, are grid
centres of the layout of the data (`ctr_embedGrid`, `ctr_sub_grid`, `dS_ctr_grid`), whose strip
norms (`e^r ≤ 68553/2^16`) are the kernel checks of `Design/DommaschkKamCAdmTailCheck`
(`Bd_tg_U`, …, `Bd_tg_PZ`). Generated by `scripts/dommaschk_kam/emit_adm.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- The difference of two grid centres of one layout is the centre of the difference grid. -/
theorem ctr_sub_grid (S N M p : ℕ) (f g : ℕ → ℕ → ℤ) :
    ctr S N M (1, 0, p) (gridPolyNM N M f) - ctr S N M (1, 0, p) (gridPolyNM N M g) =
      ctr S N M (1, 0, p) (gridPolyNM N M (fun i j => f i j - g i j)) := by
  refine ext_coeff fun km => ?_
  rw [coeff_sub, coeff_ctr_grid, coeff_ctr_grid, coeff_ctr_grid]
  split_ifs <;> push_cast <;> ring

set_option linter.style.longLine false in
/-- The surrogate `U` embedded in the layout of the data. -/
theorem xA4_embed : xA 4 = ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc (embedGrid NA MA %d %d %d (gA 4))) :=
  (ctr_embedGrid %d %d %d 0 %d %d %d (gA 4)).symm

set_option linter.style.longLine false in
/-- The surrogate `z` embedded in the layout of the data. -/
theorem xA5_embed : xA 5 = ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc (embedGrid NA MA %d %d %d (gA 5))) :=
  (ctr_embedGrid %d %d %d 1 %d %d %d (gA 5)).symm

/-- `Uo − xA 4` as one grid centre. -/
theorem Uo_sub_xA : Uo - xA 4 = ctr Sc Nc Mc (1, 0, 0) (gridPolyNM Nc Mc dGU) := by
  rw [xA4_embed, Uo]; exact ctr_sub_grid _ _ _ _ _ _

/-- `Zo − xA 5` as one grid centre. -/
theorem Zo_sub_xA : Zo - xA 5 = ctr Sc Nc Mc (1, 0, 1) (gridPolyNM Nc Mc dGZ) := by
  rw [xA5_embed, Zo]; exact ctr_sub_grid _ _ _ _ _ _

set_option linter.style.longLine false in
/-- Entry bound of the difference grid of `U`. -/
theorem abs_dGU (i j : ℕ) : |dGU i j| ≤ ((2 ^ Fc + 2 ^ %d * 2 ^ %d : ℕ) : ℤ) := by
  have h1 : |gU i j| ≤ ((2 ^ Fc : ℕ) : ℤ) := abs_dataGrid_le Nc Mc Fc datU 0 (by norm_num [Fc]) i j
  have h2 : |embedGrid NA MA %d %d %d (gA 4) i j| ≤ ((2 ^ %d * 2 ^ %d : ℕ) : ℤ) :=
    abs_embedGridN_le NA MA %d %d %d (fun i j => abs_dataGrid_le NA MA %d datA_U 0 (by norm_num) i j) i j
  have h3 := abs_sub (gU i j) (embedGrid NA MA %d %d %d (gA 4) i j)
  unfold dGU; push_cast at h1 h2 ⊢; linarith

set_option linter.style.longLine false in
/-- Entry bound of the difference grid of `z`. -/
theorem abs_dGZ (i j : ℕ) : |dGZ i j| ≤ ((2 ^ Fc + 2 ^ %d * 2 ^ %d : ℕ) : ℤ) := by
  have h1 : |gZ i j| ≤ ((2 ^ Fc : ℕ) : ℤ) := abs_dataGrid_le Nc Mc Fc datZ 1 (by norm_num [Fc]) i j
  have h2 : |embedGrid NA MA %d %d %d (gA 5) i j| ≤ ((2 ^ %d * 2 ^ %d : ℕ) : ℤ) :=
    abs_embedGridN_le NA MA %d %d %d (fun i j => abs_dataGrid_le NA MA %d datA_Z 1 (by norm_num) i j) i j
  have h3 := abs_sub (gZ i j) (embedGrid NA MA %d %d %d (gA 5) i j)
  unfold dGZ; push_cast at h1 h2 ⊢; linarith

""" % (NS, OPEN,
       dN, dM, sh, self.S, self.N, self.M, dN, dM, sh,
       dN, dM, sh, self.S, self.N, self.M, dN, dM, sh,
       sh, FU, dN, dM, sh, sh, FU, dN, dM, sh, FU, dN, dM, sh,
       sh, FZ, dN, dM, sh, sh, FZ, dN, dM, sh, FZ, dN, dM, sh))
        for nm in ('U', 'Z', 'AU', 'AZ', 'PU', 'PZ'):
            t = self.tailrec[nm]
            which, a, b = t['which'], t['a'], t['b_']
            p = 0 if which == 'U' else 1
            if (a, b) == (0, 0):
                l1 = ('(l1_gridPolyNM_le_const Nc Mc (C := 2 ^ Fc + 2 ^ %d * 2 ^ %d) fun i j _ _ => abs_dG%s i j).trans_lt'
                      ' (by kernel_fact)' % (sh, ctx['F' + which], which))
            else:
                l1 = ('(l1_gridPolyNM_le_const Nc Mc fun i j hi hj => abs_wgridN_le Nc Mc %d %d (C := 2 ^ Fc + 2 ^ %d * 2 ^ %d)'
                      ' (fun i j => abs_dG%s i j) hi hj).trans_lt (by kernel_fact)' % (a, b, sh, ctx['F' + which], which))
            pw = '(1, 0, %d)' % (p if (a, b) == (0, 0) else (p + 3) % 4)
            out.append("""set_option linter.style.longLine false in
/-- The norm of the tail grid `%s`. -/
theorem Bd_tg_%s {r : ℝ} (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16) :
    Bd r (ctr Sc Nc Mc %s (gridPolyNM Nc Mc %s)) ((%s : ℚ) : ℝ) := by
  have hl1 : l1 (gridPolyNM Nc Mc %s) < 2 ^ (%d - 1) :=
    %s
  have h := Bd_ctr_kronw (S := Sc) (N := Nc) (M := Mc) (w := %s) (a := 2 * Nc) (J := 2 * Mc) (W := %d) (b := %d) (dc := %d) (dr := %d) (Ki := Nc) (Kj := Mc) (K := %d) hq (by norm_num) (box_gridPolyNM Nc Mc _) (by norm_num [Nc]) (by norm_num) (by norm_num [Mc]) hl1 (kron_gridPolyNM _ _ _ _ _) tk_%s
  exact h.le (by exact_mod_cast (show ((%d : ℕ) : ℚ) / 2 ^ (16 * (Nc + Mc)) / 2 ^ (Sc * 1 + 0) ≤ %s by kernel_fact))

""" % (nm, nm, pw, t['grid'], qlean(t['bound']), t['grid'], t['b'], l1, pw, Wd, t['b'], AB.clog2(Wd), AB.clog2(R),
       t['K'], nm, t['K'], qlean(t['bound'])))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    # ---------------------------------------------------------------- out: indices and constants
    def emit_out(self):
        idx, cert = self.idx, self.cert
        mod = 'DommaschkKamCAdmOut'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmChain\n',
               'public import PlasmaLean.Design.DommaschkKamCAdmTail\n']
        out.append("""
/-!
# Indices and certified constants of the torus-C admissibility chain

The variable indices of the named quantities of the low-resolution chain
(`Design/DommaschkKamCAdmChain`), the mean of the torsion centre, and the rational constants of the
transfer to every torus close to the data torus (`Design/DommaschkKamCAdm`): the closeness radii,
the Lipschitz majorants `δ` of the field polynomials, the bounds of the approximate inverses and the
admissibility constants. Generated by `scripts/dommaschk_kam/emit_adm.py`, which validates every
inequality used in exact rational arithmetic before writing.
-/

@[expose] public section
noncomputable section

namespace %s

%s
""" % (NS, OPEN))
        names = dict(iR=idx['R'], iR7=idx['Rp'][7], iV0R=idx['V0R'], iV0Z=idx['V0Z'], iW0=idx['W0'],
                     iAR1=idx['AR1'], iAZ1=idx['AZ1'], iP=idx['P'], iqD=idx['qD'], iqW=idx['qW'], iqR=idx['qR'],
                     iqDW=idx['qDW'], iY=idx['Y'])
        for k, nmk in enumerate(POLY_ORDER):
            names['i' + nmk] = idx['PV'][nmk]
        for k, v in names.items():
            out.append('/-- Variable index. -/\nabbrev %s : ℕ := %d\n\n' % (k, v))
        # the mean of the torsion centre
        iY = idx['Y']
        g = self.pl.G[iY][self.N][self.M]
        p = self.pl.W[iY][2]
        sgn = 1 if p == 0 else -1
        meanY = Fr(sgn * g, 2 ** self.S)
        out.append("""set_option maxRecDepth 100000 in
/-- The centre grid of `Y` at the origin. -/
theorem gA_Y_centre : gA %d NA MA = %d := by kernel_fact

/-- **The mean of the torsion centre.** -/
theorem avg_xA_Y : avg (xA %d) = ((%s : ℚ) : ℂ) := by
  change coeff (ctr SA NA MA (1, 0, %d) (gridPolyNM NA MA (gA %d))) (0, 0) = _
  rw [coeff_ctr_grid]
  simp only [abs_zero, Nat.cast_nonneg, and_self, ↓reduceIte, zero_add, Int.toNat_natCast, NA, MA,
    SA]
  rw [show gA %d %d %d = %d from gA_Y_centre]
  push_cast
  %s

""" % (iY, g, iY, qlean(meanY), p, iY, iY, self.N, self.M, g,
       'ring' if p == 0 else 'simp [Complex.I_sq]; ring'))
        consts = dict(muq=MU, tU=self.tailrec['U']['bound'], tZ=self.tailrec['Z']['bound'],
                      tAU=self.tailrec['AU']['bound'], tAZ=self.tailrec['AZ']['bound'],
                      tPU=self.tailrec['PU']['bound'], tPZ=self.tailrec['PZ']['bound'],
                      epsD=self.norms['eD']['bound'], epsW=self.norms['eW']['bound'], epsR=self.norms['eR']['bound'],
                      bLU=self.norms['LU']['bound'], bLZ=self.norms['LZ']['bound'])
        for k in POLY_ORDER:
            consts['dl' + k] = cert['delta'][k]
        V = dict(cert['torus'])
        fmap = dict(bD='D', bDu='Du', bDz='Dz', bnR='nR', bnRu='nRu', bnRz='nRz', bnZ='nZ', bnZu='nZu', bnZz='nZz')
        for k, f in fmap.items():
            V[k] = cert['field'][f]
        for k in ('sD', 'sR', 'sW', 'tT', 'tau'):
            V[k] = cert[k]
        consts['dWq'] = AB.up(cert['dW'], 4)
        consts['dPq'] = AB.up(cert['dP'], 4)
        self.V = V
        for k, v in consts.items():
            out.append('/-- Certified constant `%s`. -/\ndef %s : ℚ := %s\n\n' % (k, k, qlean(v)))
        for k, v in V.items():
            out.append('/-- Admissibility constant `%s` (certified). -/\ndef %sC : ℚ := %s\n\n' % (k, k, qlean(v)))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))


if __name__ == '__main__':
    main()
