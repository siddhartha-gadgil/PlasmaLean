"""UNTRUSTED generator.  The certified QA defect of Dommaschk torus C (N-34 modules D4, D5).

Extends the low-resolution admissibility chain of torus C (`emit_adm.py`, 195 variables, surrogate
24 x 28, scale 2^-64, oracle angle psi_o = 2 phi) by the straight-line program of the QA-defect
numerator (`Design/DommaschkKamCQSPoly`, `QSLeaves`):

    Q   = n_R^2 + R^2 D^2 + n_z^2,   Q_u/2, Q_z/2, Q_phi/2 (product rule),
    P_L/2 = (Q_u/2) n_R + (Q_z/2) n_z + D (Q_phi/2),   M_L = 2 R (P_L/2) - 16 Q n_R,
    N0 = R^8 M_L,  N1 = n_R M_L - 2 Q R (Q_u/2) + 16 Q^2,  N2 = n_z M_L - 2 R Q (Q_z/2),
    N12 = N1 u_theta + N2 z_theta,

with the new leaves D_phi, n_R,phi, n_z,phi (R-form polynomials `dDRf`, `R dnRhf`, `dnZRf` of
`Design/DommaschkKamCQSData`, `polyT` chunks of <= 4 monomials), and the division by Q R^17 through an
approximate inverse qG (data, rounded truncated Fourier series of 1/(Q R^17) at the surrogate):

    qG8 = qG R^8,  G = qG8 M_L + iota_q qG N12 = qG N_g(iota_q)   (a node with c = 2^Qc; the honest
    value of qG8 is exactly qG R^8, and multiplying by qG8 instead of qG keeps the radius of G small),
    ||qG Q R^17 - 1|| (norm node eG), ||qG N12|| (norm node GI, for iota_C - iota_q),

and for |B|^2 = Q/R^16 an approximate inverse qB of R^16 (data) with the norm nodes
||qB R^16 - 1|| (eB) and ||2^K Q qB - cB|| (bB); and the D_min node ||2^K D - cD|| (dM).

The new nodes use UNIT weights (strip rho = 0, kernel weights P = 1, E = 0): the l1 norm bounds the
supremum.  The Adm balls (strip 0.045) are reused at rho = 0 by monotonicity.

Pointwise consequences (D5/D6): with eps_G = ||qG QR17 - 1|| < 1, |d_phiB |B|^2| = |G|/|qG QR17|
<= ||G|| / (1 - eps_G); |B|^2 = Q/R^16 >= cB - (e_bB + cB eps_B)/(1 - eps_B); |g| = |d_phiB|B|^2|/(2|B|).

Also the L2(J) integrand F = G^2 (R^8 qD) (nodes GG, H8, F; its mean is read off the centre).
The transfer to every mu-close torus (D5, `certify`) and all constants of the Out/Transfer modules
(`EmitQ.out_values`, templates in qsdef_tpl/) are recomputed here in exact rational arithmetic.

Torus A (`--tag A`, `dk_torus.py`): the same chain on the torus-A admissibility chain (surrogate
32 x 32, modules `DommaschkKamAQSDef*`, `DommaschkKamAQSTransfer`, namespace `DommaschkKamA`); every
generated text passes through `dk_torus.retarget` (the identity for torus C, so the C outputs are
byte-identical), with the torus-independent `QSData`/`QSPoly` modules kept.

(needs numpy and gmpy2, e.g. the venv /tmp/dqa-venv; run with -I; about 5 s)
usage: python emit_qsdef.py [--emit [--only data,env,trees,checks,rel,chain,out]] [--tag C|A] [--out-dir DIR]
"""
import argparse
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import adm_ball as AB                                         # noqa: E402
import emit_adm as EA                                         # noqa: E402
import dk_torus as DT                                         # noqa: E402

CHUNK = 4
KB = 32          # scale of the |B|^2 and D_min norm nodes: ||2^KB x - c||
NADM = 195       # number of variables of the Adm chain
# per torus: Adm surrogate size, the lower bound of |iota| used for kappa and the oracle ratio (Lean
# rational and text), and the closed acceptance thresholds of `qsd_numbers` (delta, B_min, kappa, oracle)
TQ = {
    'C': dict(NL=24, ML=28, iolo=(Fr(6, 25), '6 / 25', '6/25'), thr=('21 / 1000', '1042 / 1000', '17 / 100', '66 / 10000'),
              thr_txt=('0.021', '1.042', '0.17', '0.0066')),
    'A': dict(NL=32, ML=32, iolo=(Fr(1193, 5000), '1193 / 5000', '1193/5000'),
              thr=('32 / 1000', '1026 / 1000', '26 / 100', '1 / 100'), thr_txt=('0.032', '1.026', '0.26', '0.01')),
}


def tq():
    return TQ[DT.TAG]


def select(tag):
    """Select the torus (C or A); `QSData`/`QSPoly` are torus independent."""
    DT.select(tag)
    if 'QSData' not in DT.GENERIC:
        DT.GENERIC = DT.GENERIC + ('QSData', 'QSPoly')


def chunks_of(p):
    """Contiguous chunks of at most CHUNK distinct monomials (as in emit_adm.build)."""
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
    return bounds


def build(verbose=True):
    pl, idx, norms, ctx = EA.build(tq()['NL'], tq()['ML'], 64, verbose=False)
    assert pl.nvar == NADM
    # the new nodes: unit weights (rho = 0)
    pl.P, pl.E_EXP = 1, 0
    qsd = EA.lean_src('DommaschkKamCQSData.lean')
    dDRf, dnRhf, dnZRf = (EA.parse_sp(qsd, k) for k in ('dDRf', 'dnRhf', 'dnZRf'))
    dDf, dnRf, dnZf = (EA.parse_sp(qsd, k) for k in ('dDf', 'dnRf', 'dnZf'))
    nRfR = EA.sp_mulMono((Fr(1), 1, 0, 0, 0), dnRhf)
    fpolys = [('Df', dDRf), ('nRf', nRfR), ('nZf', dnZRf)]
    upolys = {'Df': dDf, 'nRf': dnRf, 'nZf': dnZf}
    t, V = idx['t'], idx['V']
    Rp, Zp, Mono = idx['Rp'], idx['Zp'], idx['Mono']

    def mono(a, b):
        if a == 0 and b == 0:
            return t
        if b == 0:
            return Rp[a]
        if a == 0:
            return Zp[b]
        return Mono[(a, b)]
    PV = dict(idx['PV'])
    CH = {}
    for kp, (nm, p) in enumerate(fpolys):
        for tm in p:
            mono(tm[1], tm[2])            # KeyError if a monomial is missing
        L = EA.sp_lcm(p)
        ep = max(tm[3] + tm[4] for tm in p)
        assert ep == 3, (nm, ep)
        bounds = chunks_of(p)
        prev = None
        for kc, (a, ln) in enumerate(bounds):
            final = kc == len(bounds) - 1
            nmc = nm if final else '%s_%d' % (nm, kc + 1)
            e = AB.polyT(Fr(L), 3, mono, p[a:a + ln])
            if prev is not None:
                e = ('add', ('mul', ('cst', L), AB.pwT(V, 3, ('var', prev))), e)
            prev = pl.node(nmc, e, L, rel=('chunk', nm, kp, a, ln, prev, final))['var']
        PV[nm] = prev
        CH[nm] = bounds
    v = lambda i: ('var', i)                                       # noqa: E731
    mul = lambda i, j: ('mul', ('var', i), ('var', j))             # noqa: E731
    add = lambda e, f: ('add', e, f)                               # noqa: E731
    sub = lambda e, f: ('sub', e, f)                               # noqa: E731
    cm = lambda k, e: ('mul', ('cst', k), e)                       # noqa: E731
    D, Du, Dz, Df = PV['D'], PV['Du'], PV['Dz'], PV['Df']
    nR, nRu, nRz, nRf = PV['nR'], PV['nRu'], PV['nRz'], PV['nRf']
    nZ, nZu, nZz, nZf = PV['nZ'], PV['nZu'], PV['nZz'], PV['nZf']
    R, R2, R8, R16, R17 = Rp[1], Rp[2], Rp[8], Rp[16], Rp[17]
    DD = idx['DD']
    A, B = idx['A'], idx['B']
    nd = lambda name, e, c=1: pl.node(name, e, c, rel=(name,))['var']   # noqa: E731
    DDu = nd('DDu', mul(D, Du))
    DDz = nd('DDz', mul(D, Dz))
    DDf = nd('DDf', mul(D, Df))
    Qn = nd('Qn', add(add(mul(nR, nR), mul(R2, DD)), mul(nZ, nZ)))
    Qu2 = nd('Qu2', add(add(add(mul(nR, nRu), mul(R, DD)), mul(R2, DDu)), mul(nZ, nZu)))
    Qz2 = nd('Qz2', add(add(mul(nR, nRz), mul(R2, DDz)), mul(nZ, nZz)))
    Qf2 = nd('Qf2', add(add(mul(nR, nRf), mul(R2, DDf)), mul(nZ, nZf)))
    PL2 = nd('PL2', add(add(mul(Qu2, nR), mul(Qz2, nZ)), mul(D, Qf2)))
    ML = nd('ML', sub(cm(2, mul(R, PL2)), cm(16, mul(Qn, nR))))
    RQu2 = nd('RQu2', mul(R, Qu2))
    N1 = nd('N1', add(sub(mul(nR, ML), cm(2, mul(Qn, RQu2))), cm(16, mul(Qn, Qn))))
    RQ = nd('RQ', mul(R, Qn))
    N2 = nd('N2', sub(mul(nZ, ML), cm(2, mul(RQ, Qz2))))
    N12 = nd('N12', add(mul(N1, A), mul(N2, B)))
    QR17 = nd('QR17', mul(Qn, R17))
    # approximate inverses (float, untrusted)
    NL, ML_ = pl.N, pl.M
    n1, n2 = 1 << AB.clog2(4 * (2 * NL + 1)), 1 << AB.clog2(4 * (2 * ML_ + 1))
    QRv = pl.centre_values(QR17, n1, n2).real
    R16v = pl.centre_values(R16, n1, n2).real
    fw = lambda G: max(AB.clog2(max(abs(x) for c in G for x in c) + 1) + 1, 8)   # noqa: E731
    gqG = AB.grid_from_values(1.0 / QRv, NL, ML_, pl.S, 0)
    gqB = AB.grid_from_values(1.0 / R16v, NL, ML_, pl.S, 0)
    qG = pl.data(gqG, 0, 'qG', fw(gqG))
    eG = pl.node('eG', sub(mul(qG, QR17), mul(t, t)), 0, rel=('eG',))
    Qc, Iqc = ctx['Qc'], ctx['Iqc']
    qG8 = nd('qG8', mul(qG, R8))
    G = nd('G', sub(cm(2 ** Qc, mul(qG8, ML)), cm(Iqc, mul(qG, N12))), 2 ** Qc)
    GI = pl.node('GI', mul(qG, N12), 0, rel=('GI',))
    qB = pl.data(gqB, 0, 'qB', fw(gqB))
    eB = pl.node('eB', sub(mul(qB, R16), mul(t, t)), 0, rel=('eB',))
    # the constants of the |B|^2 and D_min nodes: the means of the honest centres
    Bv = pl.centre_values(Qn, n1, n2).real * pl.centre_values(qB, n1, n2).real
    cB = round(float(Bv.mean()) * 2 ** KB)
    Dv = pl.centre_values(D, n1, n2).real
    cD = round(float(Dv.mean()) * 2 ** KB)
    # D has weight (1, 0, 2): its honest value is -grid/2^S, so the centre values above already
    # include the phase (centre_values divides by i^p)
    bB = pl.node('bB', sub(cm(2 ** KB, mul(Qn, qB)), cm(cB, mul(t, t))), 0, rel=('bB',))
    dM = pl.node('dM', sub(cm(2 ** KB, v(D)), cm(cD, v(t))), 0, rel=('dM',))
    # the L2(J) average: F = G^2 R^8 qD (= 4 g^2 J w1^2 w2)
    GG = nd('GG', mul(G, G))
    H8 = nd('H8', mul(R8, idx['qD']))
    Fn = nd('F', mul(GG, H8))
    q = dict(GG=GG, H8=H8, F=Fn, PV=PV, CH=CH, fpolys=fpolys, upolys=upolys, DDu=DDu, DDz=DDz, DDf=DDf, Qn=Qn, Qu2=Qu2,
             Qz2=Qz2, Qf2=Qf2, PL2=PL2, ML=ML, RQu2=RQu2, N1=N1, RQ=RQ, N2=N2, N12=N12, QR17=QR17,
             qG=qG, qG8=qG8, G=G, qB=qB, cB=cB, cD=cD)
    qn = dict(eG=eG, GI=GI, eB=eB, bB=bB, dM=dM)
    return pl, idx, norms, ctx, q, qn


def report(pl, idx, ctx, q, qn):
    print('variables %d (Adm %d), new nodes:' % (pl.nvar, NADM))
    for s in pl.steps:
        if s.get('kind') in ('node', 'norm') and s['n'] >= NADM:
            if s['kind'] == 'node':
                print('  %-6s n=%3d B=%-12.5g E=%-10.3g dmaj=%-10.3g beta=%-10.3g img %.2f Mbit' % (
                    s['name'], s['n'], float(pl.B[s['var']]), float(pl.E[s['var']]), float(s['dmaj']),
                    float(s['beta']), s['W'] * s['R'] * s['b'] / 1e6))
            else:
                print('  %-6s norm bound %-12.5g (dmaj %.3g beta %.3g) img %.2f Mbit' % (
                    s['name'], float(s['bound']), float(s['dmaj']), float(s['beta']),
                    s['W'] * s['R'] * s['b'] / 1e6))
    for k in ('qG', 'qB'):
        print('  data %s: B = %.6g' % (k, float(pl.B[q[k]])))
    G = q['G']
    eG = qn['eG']['bound']
    nG = pl.B[G] + pl.E[G]
    print('surrogate: ||qG Ng_q|| <= %.6g, eps_G = %.3g' % (float(nG), float(eG)))
    print('  sup |d_phiB |B|^2| <= %.6g' % float(nG / (1 - eG)))
    cB = Fr(q['cB'], 2 ** KB)
    eBn = qn['eB']['bound']
    ebB = qn['bB']['bound'] / 2 ** KB
    b2 = cB - (ebB + cB * eBn) / (1 - eBn)
    print('  |B|^2 >= %.6g (cB %.6g, e %.3g, epsB %.3g)  B_min >= %.6g' % (
        float(b2), float(cB), float(ebB), float(eBn), float(b2) ** 0.5))
    cD = Fr(q['cD'], 2 ** KB)
    edM = qn['dM']['bound'] / 2 ** KB
    print('  D >= %.6g (cD %.6g, e %.3g)' % (float(cD - edM), float(cD), float(edM)))
    print('  delta_inf (surrogate) <= %.6g' % (float(nG / (1 - eG)) / (2 * float(b2) ** 0.5)))
    F = q['F']
    mF = Fr(pl.G[F][pl.N][pl.M], 2 ** pl.S) * (1 if pl.W[F][2] == 0 else -1)
    print('  <F> centre %.6g, E_F %.3g -> delta_2 <= %.6g (eps_D %.3g)' % (
        float(mF), float(pl.E[F]), (float(mF + pl.E[F]) / 4 / (1 - float(eG)) ** 2) ** 0.5, 0))


# ------------------------------------------------------------------ polynomial expressions (D5)
# Variables (Fin 16): the 13 leaves in the order of `QSLeaves` (D, Du, Dz, Df, nR, nRu, nRz, nRf, nZ,
# nZu, nZz, nZf, R), then iota (13), u_theta (14), z_theta (15).  Trees: ('c', q) | ('v', i) |
# ('+', a, b) | ('-', a, b) | ('*', a, b); mirrored by `PolyExpr ℚ (Fin 16)` in Lean.
LEAVES = ['D', 'Du', 'Dz', 'Df', 'nR', 'nRu', 'nRz', 'nRf', 'nZ', 'nZu', 'nZz', 'nZf', 'R']


def pe_trees():
    V = {k: ('v', i) for i, k in enumerate(LEAVES)}
    io, ut, zt = ('v', 13), ('v', 14), ('v', 15)
    m = lambda a, b: ('*', a, b)                                     # noqa: E731
    a_ = lambda a, b: ('+', a, b)                                    # noqa: E731
    s_ = lambda a, b: ('-', a, b)                                    # noqa: E731
    c = lambda q: ('c', Fr(q))                                       # noqa: E731
    D, Du, Dz, Df, nR, nRu, nRz, nRf, nZ, nZu, nZz, nZf, R = (V[k] for k in LEAVES)
    T = {}
    T['Q'] = a_(a_(m(nR, nR), m(m(R, R), m(D, D))), m(nZ, nZ))
    T['Qu'] = m(c(2), a_(a_(a_(m(nR, nRu), m(R, m(D, D))), m(m(R, R), m(D, Du))), m(nZ, nZu)))
    T['Qz'] = m(c(2), a_(a_(m(nR, nRz), m(m(R, R), m(D, Dz))), m(nZ, nZz)))
    T['Qf'] = m(c(2), a_(a_(m(nR, nRf), m(m(R, R), m(D, Df))), m(nZ, nZf)))
    T['PL'] = a_(a_(m(T['Qu'], nR), m(T['Qz'], nZ)), m(D, T['Qf']))
    T['ML'] = s_(m(R, T['PL']), m(m(c(16), T['Q']), nR))
    R8 = R
    for _ in range(7):
        R8 = m(R8, R)
    T['R8'] = R8
    T['N0'] = m(R8, T['ML'])
    T['N1'] = s_(m(nR, T['ML']), m(T['Q'], s_(m(R, T['Qu']), m(c(16), T['Q']))))
    T['N2'] = s_(m(nZ, T['ML']), m(m(R, T['Q']), T['Qz']))
    T['Ng'] = a_(T['N0'], m(io, a_(m(T['N1'], ut), m(T['N2'], zt))))
    return T


def pe_mj(a, b, e):
    """(maj, majD) of a tree (mirror of `PolyExpr.maj`, `PolyExpr.majD` with rational constants)."""
    k = e[0]
    if k == 'c':
        return (abs(e[1]), Fr(0))
    if k == 'v':
        return (a[e[1]], b[e[1]])
    x, y = pe_mj(a, b, e[1]), pe_mj(a, b, e[2])
    if k in ('+', '-'):
        return (x[0] + y[0], x[1] + y[1])
    return (x[0] * y[0], x[1] * y[0] + x[0] * y[1])


def pe_size(e):
    return 1 if e[0] in ('c', 'v') else 1 + pe_size(e[1]) + pe_size(e[2])


def adm_consts():
    src = EA.lean_src(DT.out_name('DommaschkKamCAdmOut') + '.lean')
    import re
    out = {}
    for m_ in re.finditer(r'def (\w+) : ℚ := \((-?\d+)(?: / (\d+)(?: \^ (\d+))?)? : ℚ\)', src):
        nm, n, d, e = m_.group(1), int(m_.group(2)), m_.group(3), m_.group(4)
        den = 1 if d is None else (int(d) ** int(e) if e else int(d))
        out[nm] = Fr(n, den)
    return out


def certify(pl, idx, norms, ctx, q, qn, verbose=True):
    """Exact rational constants of the transfer to every mu-close torus (rho = 0); mirrors D5."""
    K = adm_consts()
    muq, tU, tZ, tAU, tAZ = K['muq'], K['tU'], K['tZ'], K['tAU'], K['tAZ']
    Cb = Fr(EA.P_EXP, 2 ** EA.E_EXP)
    hU, hZ = muq + tU, muq + tZ
    BU, BZ = pl.B[4], pl.B[5]
    out = {}
    dl = {'D': K['dlD'], 'Du': K['dlDu'], 'Dz': K['dlDz'], 'nR': K['dlnR'], 'nRu': K['dlnRu'],
          'nRz': K['dlnRz'], 'nZ': K['dlnZ'], 'nZu': K['dlnZu'], 'nZz': K['dlnZz']}
    for k in ('Df', 'nRf', 'nZf'):
        dl[k] = AB.up(EA.lipQ(q['upolys'][k], BU, BZ, hU, hZ, Cb), 4)
    dl['R'] = hU
    out['dl'] = dl
    PV = q['PV']
    var = {k: PV[k] for k in LEAVES if k != 'R'}
    var['R'] = idx['R']
    a = [pl.B[var[k]] + pl.E[var[k]] for k in LEAVES] + [Fr(*DT.cfg()['iota_abs_up']), pl.B[6], pl.B[7]]
    b = [dl[k] for k in LEAVES] + [Fr(0), muq + tAU, muq + tAZ]
    out['a'], out['b'] = a, b
    T = pe_trees()
    ab = [x + y for x, y in zip(a, b)]
    dNg = AB.up(pe_mj(ab, b, T['Ng'])[1], 4)
    dQ = AB.up(pe_mj(ab, b, T['Q'])[1], 4)
    aQ = pe_mj(a, b, T['Q'])[0]
    aR = a[12]
    hR = b[12]
    dR17 = (aR + hR) ** 17 - aR ** 17
    dQR17 = AB.up(dQ * (aR + hR) ** 17 + aQ * dR17, 4)
    dR16 = AB.up((aR + hR) ** 16 - aR ** 16, 4)
    out.update(dNg=dNg, dQ=dQ, aQ=aQ, dQR17=dQR17, dR16=dR16)
    nqG, nqB, nqD = pl.B[q['qG']], pl.B[q['qB']], pl.B[idx['qD']]
    io = Fr(1, 2 ** ctx['Qc'])
    epsG = AB.up(qn['eG']['bound'] + nqG * dQR17, 4)
    dG = AB.up(nqG * dNg + io * qn['GI']['bound'], 4)
    etaG = AB.up(pl.B[q['G']] + pl.E[q['G']] + dG, 6)
    assert epsG < 1
    d1 = AB.up(etaG / (1 - epsG), 6)
    epsB = AB.up(qn['eB']['bound'] + nqB * dR16, 4)
    cB = Fr(q['cB'], 2 ** KB)
    eB = AB.up(qn['bB']['bound'] / 2 ** KB + nqB * dQ, 4)
    b2 = cB - (eB + cB * epsB) / (1 - epsB)
    Bmin = AB.down(Fr(math.isqrt(int(b2 * 10 ** 12)), 10 ** 6), 5)
    assert Bmin ** 2 <= b2
    cD = Fr(q['cD'], 2 ** KB)
    eD = AB.up(qn['dM']['bound'] / 2 ** KB + dl['D'], 4)
    delta = AB.up(d1 / (2 * Bmin), 4)
    # L2(J): F = G^2 R^8 qD at the exact torus
    aG = pl.B[q['G']] + pl.E[q['G']]
    a8 = pl.B[idx['Rp'][8]] + pl.E[idx['Rp'][8]]
    dH8 = nqD * ((aR + hR) ** 8 - aR ** 8)
    aH8 = pl.B[q['H8']] + pl.E[q['H8']]
    dGG = dG * (2 * aG + dG)
    aGG = pl.B[q['GG']] + pl.E[q['GG']]
    dF = AB.up(dGG * (aH8 + dH8) + aGG * dH8, 4)
    F = q['F']
    mF = Fr(pl.G[F][pl.N][pl.M], 2 ** pl.S) * (1 if pl.W[F][2] == 0 else -1)
    mFb = AB.up(abs(mF) + pl.E[F] + dF, 6)
    epsD = AB.up(K['epsD'] + nqD * dl['D'], 4)
    d22 = mFb / (4 * (1 - epsG) ** 2 * (1 - epsD))
    delta2 = AB.up(Fr(math.isqrt(int(d22 * 10 ** 16)) + 1, 10 ** 8), 4)
    assert delta2 ** 2 >= d22
    out.update(epsG=epsG, dG=dG, etaG=etaG, d1=d1, epsB=epsB, cB=cB, eB=eB, b2=b2, Bmin=Bmin, cD=cD, eD=eD,
               delta=delta, dF=dF, mF=mF, mFb=mFb, epsD=epsD, delta2=delta2, d22=d22)
    if verbose:
        print('D5 transfer (rho = 0, mu = 1e-12):')
        print('  dl:', {k: '%.3g' % float(v) for k, v in dl.items()})
        print('  sizes: Ng tree %d nodes, Q tree %d' % (pe_size(T['Ng']), pe_size(T['Q'])))
        print('  dNg %.3g  dQ %.3g  dQR17 %.3g  dR16 %.3g' % (float(dNg), float(dQ), float(dQR17), float(dR16)))
        print('  eps_G %.4g  dG %.3g  eta_G %.6g  ->  sup|d_phiB|B|^2| <= d1 = %.6g' % (
            float(epsG), float(dG), float(etaG), float(d1)))
        print('  eps_B %.3g  e_B %.4g  |B|^2 >= %.6g  B_min = %s (%.6g)' % (
            float(epsB), float(eB), float(b2), Bmin, float(Bmin)))
        print('  D >= %.6g' % float(cD - eD))
        print('  delta_inf <= d1/(2 B_min) = %.6g' % float(delta))
        iota = 0.241651 if DT.TAG == 'C' else 0.2386075
        print('  kappa = 2 delta/(B_min |iota|) <= %.4g;  delta/|iota| %.4g' % (
            2 * float(delta) / (float(Bmin) * iota), float(delta) / iota))
        print('  L2: <F> %.6g (+E %.3g +dF %.3g) eps_D %.3g -> delta_2 <= %.6g' % (
            float(mF), float(pl.E[F]), float(dF), float(epsD), float(delta2)))
        print('  oracle-normalised defect/|iota| <= sqrt2/N delta_2/(B_min |iota|) = %.5g; via sup %.5g' % (
            2 ** 0.5 / 2 * float(delta2) / (float(Bmin) * iota), float(delta) / (2 ** 0.5 * float(Bmin) * iota)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--only', default='')
    ap.add_argument('--ndata', type=int, default=2)
    ap.add_argument('--ncheck', type=int, default=4)
    ap.add_argument('--tag', default='C', help='torus (C, or A: modules DommaschkKamA*, see dk_torus.py)')
    ap.add_argument('--out-dir', default='', help='output directory (default PlasmaLean/Design)')
    args = ap.parse_args()
    global OUT
    select(args.tag)
    if args.out_dir:
        OUT = args.out_dir
    import time
    t0 = time.time()
    pl, idx, norms, ctx, q, qn = build()
    print('chain built: %d variables, %.1f s' % (pl.nvar, time.time() - t0))
    report(pl, idx, ctx, q, qn)
    cert = certify(pl, idx, norms, ctx, q, qn)
    if args.emit:
        em = EmitQ(pl, idx, norms, ctx, q, qn, cert)
        only = set(args.only.split(',')) if args.only else None
        want = lambda k: only is None or k in only                      # noqa: E731
        em.emit_data(args.ndata) if want('data') else setattr(em, 'datamods', ['DommaschkKamCQSDefData%d' % (f + 1) for f in range(args.ndata)])
        if want('env'):
            em.emit_env()
        if want('trees'):
            em.emit_trees()
        if want('checks'):
            em.emit_checks(args.ncheck)
        else:
            em.checkmods = ['DommaschkKamCQSDefCheck%d' % (f + 1) for f in range(args.ncheck)]
        if want('rel'):
            em.emit_rel()
        if want('chain'):
            em.emit_chain()
        if want('out'):
            em.emit_out()
        print('emitted:', em.files)
        print('check loads (Mbit):', [round(x / 1e6, 1) for x in em.checkload])


# ======================================================================================== Lean emission
HEADER, OPEN, NS, qlean, lst, wrap = EA.HEADER, EA.OPEN, EA.NS, EA.qlean, EA.lst, EA.wrap
OUT = EA.OUT
CMD = 'lake build PlasmaLean.Design.DommaschkKamCQSTransfer'


class EmitQ:
    def __init__(self, pl, idx, norms, ctx, q, qn, cert):
        self.pl, self.idx, self.norms, self.ctx, self.q, self.qn, self.cert = pl, idx, norms, ctx, q, qn, cert
        self.N, self.M, self.S = pl.N, pl.M, pl.S
        self.nvar = pl.nvar
        self.nodes = {s['n']: s for s in pl.steps if s.get('kind') == 'node' and s['n'] >= NADM}
        self.normnodes = [s for s in pl.steps if s.get('kind') == 'norm' and s['n'] >= NADM]
        self.newvars = list(range(NADM, self.nvar))
        self.files = []
        self.checkload = []
        self.build_note = ('8 CPU-min', '3.3 GB') if DT.TAG == 'C' else ('15 CPU-min', '4.3 GB')

    def nm(self, i):
        return self.pl.names[i]

    def write(self, mod, text):
        mod, text = DT.out_name(mod), DT.retarget(text)
        if DT.TAG != 'C':     # the `Qp` clash remark is about the torus-C namespace
            text = text.replace('both declare `DommaschkKamA.Qp`', 'both declare `DommaschkKamC.Qp`')
            # longer rationals of torus A: allow the long line of `qsd_heB`
            text = text.replace('include hU in\n/-- **The approximate inverse of `R¹⁶` at the torus.** -/',
                                'set_option linter.style.longLine false in\ninclude hU in\n'
                                '/-- **The approximate inverse of `R¹⁶` at the torus.** -/')
        open(os.path.join(OUT, mod + '.lean'), 'w').write(text)
        self.files.append(mod)

    # ---------------------------------------------------------------- data
    def emit_data(self, nfiles):
        ids = self.newvars
        per = -(-len(ids) // nfiles)
        mods = []
        for f in range(nfiles):
            ch = ids[f * per:(f + 1) * per]
            mod = 'DommaschkKamCQSDefData%d' % (f + 1)
            mods.append(mod)
            out = [HEADER, 'public import Mathlib.Data.List.Basic\n\n']
            out.append('''/-!
# Data of the torus-C QA-defect chain (part %d)

Packed half grids (`Certificates/KronBallGrid`, `halfGridR`: one literal per row `i − N`, fields of
the width `F` stated per centre, offset `2^{F−1}`, rows of length `2M + 1`, `M = %d`) of the new
centres of the QA-defect chain of Dommaschk torus C (`Design/DommaschkKamCQSDefEnv`, N-34 module
D4). Generated by the untrusted oracle `scripts/dommaschk_kam/emit_qsdef.py`; nothing here is
trusted.
-/

@[expose] public section

namespace %s

''' % (f + 1, self.M, NS))
            for i in ch:
                G = self.pl.G[i]
                p = self.pl.W[i][2]
                F = self.pl.F[i]
                h = EA.half_grid(G, self.N, self.M, p)
                rows = EA.pack_rows(h, self.N, self.M, F)
                out.append('set_option linter.style.longLine false in\n')
                out.append('/-- Packed half grid of the centre `%s` (field width %d). -/\n' % (self.nm(i), F))
                out.append('def datQ_%s : List ℕ := [\n%s]\n\n' % (self.nm(i), ',\n'.join('  0x%x' % v for v in rows)))
            out.append('end %s\n' % NS)
            self.write(mod, ''.join(out))
        self.datamods = mods

    # ---------------------------------------------------------------- environment
    def emit_env(self):
        NV = self.nvar
        mod = 'DommaschkKamCQSDefEnv'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCAdmEnv\n',
               'public import PlasmaLean.Design.DommaschkKamCQSData\n',
               'public import Mathlib.Data.List.GetD\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.datamods]
        out.append('''
/-!
# The ball environment of the torus-C QA-defect chain (N-34, D4)

The QA-defect chain of Dommaschk torus C extends the low-resolution admissibility chain
(`Design/DommaschkKamCAdmEnv`, variables `0, …, %d`, layout `%d × %d`, scale `2^{−64}`, oracle
angle `ψₒ = 2φ`) by %d variables: the `φ`-derivative leaves `D_φ`, `n_{R,φ}`, `n_{z,φ}` (`polyT`
chunks of the R-form polynomials `polyQ k`), the straight-line program of the QA-defect numerator,
the approximate inverses `qG ≈ 1/(Q R¹⁷)`, `qB ≈ 1/R¹⁶` (data) and the `L²(J)` integrand. The
lists `gQl`, `WtQl`, `LQl`, `BQl`, `EQl` are the Adm lists followed by the new entries, so every
Adm variable keeps its index, grid, weight, centre, norm bound and radius (`xQ_lt`, `BQ_lt`,
`EQ_lt`). The new nodes use unit strip weights (`ρ = 0`, kernel weights `P = 1`, `E = 0`).
Generated by `scripts/dommaschk_kam/emit_qsdef.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
''' % (NADM - 1, self.N, self.M, NV - NADM, NS, OPEN))
        for i in self.newvars:
            p = self.pl.W[i][2]
            out.append('/-- Grid of the centre `%s`. -/\ndef gQ_%s : ℕ → ℕ → ℤ :=\n  symGrid NA MA ((-1) ^ %d) (halfGridR %d NA datQ_%s)\n\n'
                       % (self.nm(i), self.nm(i), p, self.pl.F[i], self.nm(i)))
        out.append('/-- The grids of the variables: the Adm grids, then the new ones. -/\n'
                   'def gQl : List (ℕ → ℕ → ℤ) := gAl ++%s\n\n' % lst(['gQ_%s' % self.nm(i) for i in self.newvars]))
        out.append('/-- The grids of the variables. -/\ndef gQ (i : ℕ) : ℕ → ℕ → ℤ := gQl.getD i (fun _ _ => 0)\n\n')
        out.append('''/-- The polynomials of the variables. -/
def PlQ : ℕ → P2
  | 0 => Tpoly SA NA MA
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NA MA (gQ (n + 4))

''')
        out.append('/-- The weights of the variables (list). -/\ndef WtQl : List (ℕ × ℕ × ℕ) := WtAl ++%s\n\n'
                   % lst(['(%d, %d, %d)' % self.pl.W[i] for i in self.newvars]))
        out.append('/-- The weights of the variables. -/\ndef WtQ (i : ℕ) : ℕ × ℕ × ℕ := WtQl.getD i (1, 0, 0)\n\n')
        out.append('/-- The `ℓ¹` bounds of the variable polynomials (list). -/\ndef LQl : List ℕ := LAl ++%s\n\n'
                   % lst(['lwA %d' % self.pl.F[i] for i in self.newvars]))
        out.append('/-- The `ℓ¹` bounds of the variable polynomials. -/\ndef LQ (i : ℕ) : ℕ := LQl.getD i 0\n\n')
        out.append('''/-- The Kronecker images of the variable polynomials. -/
def KvQ (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SA * ((1 <<< (b * (NA + W * MA)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => packGridNM b W NA (gQ (n + 4)) (2 * MA + 1)

/-- The honest centres. -/
def xQ (i : ℕ) : FA := ctr SA NA MA (WtQ i) (PlQ i)

/-- The Adm lists have %d entries. -/
theorem gAl_length : gAl.length = %d := by rfl

/-- The Adm grids are kept. -/
theorem gQ_lt {i : ℕ} (h : i < %d) : gQ i = gA i := by
  unfold gQ gQl gA
  rw [List.getD_append _ _ _ _ (by rw [gAl_length]; exact h)]

/-- The Adm weights are kept. -/
theorem WtQ_lt {i : ℕ} (h : i < %d) : WtQ i = WtA i := by
  unfold WtQ WtQl WtA
  rw [List.getD_append _ _ _ _ (by rw [show WtAl.length = %d by rfl]; exact h)]

/-- The Adm `ℓ¹` bounds are kept. -/
theorem LQ_lt {i : ℕ} (h : i < %d) : LQ i = LA i := by
  unfold LQ LQl LA
  rw [List.getD_append _ _ _ _ (by rw [show LAl.length = %d by rfl]; exact h)]

/-- The Adm polynomials are kept. -/
theorem PlQ_lt {i : ℕ} (h : i < %d) : PlQ i = PlA i := by
  match i, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | n + 4, h => simp only [PlQ, PlA, gQ_lt h]

/-- **The Adm centres are kept.** -/
theorem xQ_lt {i : ℕ} (h : i < %d) : xQ i = xA i := by
  simp only [xQ, xA, WtQ_lt h, PlQ_lt h]

/-- The phases are below `4`. -/
theorem hWQ : ∀ i, (WtQ i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxQ : ∀ i, InBox (PlQ i) (BxA i).1 (BxA i).2
  | 0 => InBox.monomial NA MA _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NA MA _

/-- The grids vanish beyond the last variable. -/
theorem gQ_out (n : ℕ) : gQ (n + %d) = fun _ _ => 0 := by
  unfold gQ
  have h : gQl.length = %d := by rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `ℓ¹` bounds of the Adm variables. -/
theorem l1Q_%d : ∀ i, i < %d → l1 (PlQ i) ≤ LQ i := fun i h => by
  rw [PlQ_lt h, LQ_lt h]; exact l1A i

''' % (NADM, NADM, NADM, NADM, NADM, NADM, NADM, NADM, NADM, NV, NV, NADM, NADM))
        for i in self.newvars:
            out.append('set_option maxRecDepth 100000 in\n/-- `ℓ¹` bounds up to the variable `%s`. -/\n'
                       'theorem l1Q_%d : ∀ i, i < %d → l1 (PlQ i) ≤ LQ i :=\n  chain_succ l1Q_%d\n'
                       '    (l1_dataGrid_le NA MA %d datQ_%s %d (by kernel_fact))\n\n'
                       % (self.nm(i), i + 1, i + 1, i, self.pl.F[i], self.nm(i), self.pl.W[i][2]))
        out.append('''set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds. -/
theorem l1Q (i : ℕ) : l1 (PlQ i) ≤ LQ i := by
  rcases lt_or_ge i %d with h | h
  · exact l1Q_%d i h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact (l1_gridPolyNM_le_const NA MA (C := 0) fun i j _ _ => by rw [gQ_out n]; simp).trans
      (by simp)

/-- The Kronecker images. -/
theorem kronQ : ∀ b W i, kron b W (PlQ i) = KvQ b W i
  | b, W, 0 => kron_Tpoly SA NA MA b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NA MA _

''' % (NV, NV))
        out.append('/-- The norm bounds of the centres (list; strip `0` for the new ones). -/\ndef BQl : List ℚ := BAl ++%s\n\n'
                   % lst([qlean(self.pl.B[i]) for i in self.newvars]))
        out.append('/-- The norm bounds of the centres. -/\ndef BQ (i : ℕ) : ℚ := BQl.getD i 0\n\n')
        out.append('/-- The radii of the balls (list; strip `0` for the new ones). -/\ndef EQl : List ℚ := EAl ++%s\n\n'
                   % lst([qlean(self.pl.E[i]) for i in self.newvars]))
        out.append('/-- The radii of the balls. -/\ndef EQ (i : ℕ) : ℚ := EQl.getD i 0\n\n')
        out.append('''/-- The Adm norm bounds are kept. -/
theorem BQ_lt {i : ℕ} (h : i < %d) : BQ i = BA i := by
  unfold BQ BQl BA
  rw [List.getD_append _ _ _ _ (by rw [show BAl.length = %d by rfl]; exact h)]

/-- The Adm radii are kept. -/
theorem EQ_lt {i : ℕ} (h : i < %d) : EQ i = EA i := by
  unfold EQ EQl EA
  rw [List.getD_append _ _ _ _ (by rw [show EAl.length = %d by rfl]; exact h)]

/-- The R-form polynomials of the new leaves `D_φ`, `n_{R,φ} = R·∂_φ(n_R/R)`, `n_{z,φ}`
(`Design/DommaschkKamCQSData`). -/
def polyQ : ℕ → DkPoly.SP
  | 0 => dDRf
  | 1 => DkPoly.mulMono ⟨1, 1, 0, 0, 0⟩ dnRhf
  | 2 => dnZRf
  | _ => []

end %s
''' % (NADM, NADM, NADM, NADM, NS))
        self.write(mod, ''.join(out))

    # ---------------------------------------------------------------- trees
    def tree_text(self, r):
        rel = r['rel']
        if rel[0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = rel
            if a == 0:
                return 'polyT %s 3 monoA ((polyQ %d).take %d)' % (qlean(r['c']), kp, ln)
            return ('.add (.mul (.cst %d) (pwT 1 3 (.var %d))) (polyT %s 3 monoA (((polyQ %d).drop %d).take %d))'
                    % (r['c'], prev, qlean(r['c']), kp, a, ln))
        return EA.tree_lean(r['tree'])

    def emit_trees(self):
        mod = 'DommaschkKamCQSDefTrees'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCQSDefEnv\n']
        out.append('''
/-!
# Expression trees of the torus-C QA-defect chain (N-34, D4)

The expression trees (`Certificates/KronExpr`, `Ex`) of the new nodes of the QA-defect chain of
Dommaschk torus C: the `polyT` chunks of the `φ`-derivative leaves, the products of the
straight-line program of the QA-defect numerator, and the norm nodes. Generated by
`scripts/dommaschk_kam/emit_qsdef.py`.
-/

@[expose] public section

namespace %s

%s
''' % (NS, OPEN))
        for s in self.pl.steps:
            if s.get('kind') in ('node', 'norm') and s['n'] >= NADM:
                what = 'node `%s` (variable `%d`)' % (s['name'], s['n']) if s['kind'] == 'node' else 'norm node `%s`' % s['name']
                out.append('set_option linter.style.longLine false in\n/-- Expression tree of the %s. -/\ndef trQ_%s : Ex :=\n  %s\n\n' % (
                    what, s['name'], wrap(self.tree_text(s), 2)))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    # ---------------------------------------------------------------- checks
    def center_lines(self, i):
        r = self.pl.normrec[i]
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm of the centre `%s` (unit weights). -/\n' % self.nm(i),
                'theorem cQ_%s : centerKw 1 0 NA MA KvQ %d %d %d %d %d %d %d ≤ %d := by\n  kron2_proof\n\n' % (
                    self.nm(i), i, r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- A priori `ℓ¹` bound of the centre `%s`. -/\n' % self.nm(i),
                'theorem clQ_%s : LQ %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (self.nm(i), i, r['b'])]

    def node_lines(self, r):
        n, c = r['n'], r['c']
        cl = '(%d : ℤ)' % c
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the node `%s`: truncation norm (unit weights). -/\n' % r['name'],
                'theorem kQ_%s : nodeKw 1 0 SA NA MA WtQ KvQ trQ_%s %s %d %d %d %d %d %d %d %d %d %d ≤ %d := by\n'
                '  kron2_proof\n\n' % (r['name'], r['name'], cl, r['dd'], r['de'], n, r['b'], r['W'], r['dc'], r['dr'],
                                       r['J'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'],
                'theorem lQ_%s : nodeL1 SA LQ trQ_%s %s %d %d %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (
                    r['name'], r['name'], cl, r['dd'], r['de'], n, r['b'])]

    def norm_lines(self, r):
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm node `%s` (unit weights). -/\n' % r['name'],
                'theorem kQ_%s : normKw 1 0 NA MA WtQ KvQ trQ_%s (%d, %d, %d) %d %d %d %d %d %d %d ≤ %d := by\n'
                '  kron2_proof\n\n' % (r['name'], r['name'], r['w'][0], r['w'][1], r['w'][2], r['b'], r['W'], r['dc'],
                                       r['dr'], r['J'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'],
                'theorem lQ_%s : Ex.majN LQ trQ_%s < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (r['name'], r['name'], r['b'])]

    def emit_checks(self, nfiles):
        items = [('c', i) for i in self.newvars]
        for s in self.pl.steps:
            if s.get('kind') == 'node' and s['n'] >= NADM:
                items.append(('n', s))
            elif s.get('kind') == 'norm' and s['n'] >= NADM:
                items.append(('m', s))

        def cost(it):
            k, x = it
            if k == 'c':
                r = self.pl.normrec[x]
                return r['W'] * (2 * self.M + 1) * r['b']
            return x['W'] * (x['J'] + 1) * x['b']
        bins = [[] for _ in range(nfiles)]
        load = [0] * nfiles
        for it in sorted(items, key=cost, reverse=True):
            f = min(range(nfiles), key=lambda k: load[k])
            bins[f].append(it)
            load[f] += cost(it)
        mods = []
        for f, ch in enumerate(bins):
            ch.sort(key=lambda it: it[1] if it[0] == 'c' else it[1]['n'] + 0.5)
            mod = 'DommaschkKamCQSDefCheck%d' % (f + 1)
            mods.append(mod)
            out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCQSDefTrees\n',
                   'public import PlasmaLean.Certificates.KronProof2D\n',
                   'meta import PlasmaLean.Design.DommaschkKamCQSDefTrees\n']
            out.append('''
/-!
# Proof-term checks of the torus-C QA-defect chain (part %d)

Each theorem is an explicit proof term (`kron2_proof` of `Certificates/KronProof2D`; `kron_lt` for
the `ℓ¹` bounds) on the data of `Design/DommaschkKamCAdmData*` and `Design/DommaschkKamCQSDefData*`:
the digit sums with unit weights (`nodeKw 1 0`, `normKw 1 0`, `centerKw 1 0` of
`Design/DommaschkKamCKronW`; strip `ρ = 0`) of the Kronecker images of the truncation polynomials of
the new nodes, and their a priori `ℓ¹` bounds. Generated by `scripts/dommaschk_kam/emit_qsdef.py`.
-/

@[expose] public section

namespace %s

%s
''' % (f + 1, NS, OPEN))
            for kind, x in ch:
                out += self.center_lines(x) if kind == 'c' else self.node_lines(x) if kind == 'n' else self.norm_lines(x)
            out.append('end %s\n' % NS)
            self.write(mod, ''.join(out))
        self.checkmods = mods
        self.checkload = load

    # ---------------------------------------------------------------- honest values and node identities
    def hname(self, i):
        """The honest value of a new variable (Lean term)."""
        k = self.pl.kind[i]
        if k in ('data', 'grid'):
            return 'xQ %d' % i
        r = self.nodes[i]
        if r['rel'][0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = r['rel']
            if final:
                return 'fQ %d' % kp
            return 'DkPoly.ev xRo ((polyQ %d).take %d)' % (kp, a + ln)
        return self.nm(i) + 'q'

    def ev_text(self, e):
        k = e[0]
        if k == 'var':
            i = e[1]
            return 'XA %d' % i if i < NADM else self.hname(i)
        if k == 'cst':
            return '((%d : ℤ) : FA)' % e[1]
        op = {'add': '+', 'sub': '-', 'mul': '*'}[k]
        return '(%s %s %s)' % (self.ev_text(e[1]), op, self.ev_text(e[2]))

    def emit_rel(self):
        NV = self.nvar
        mod = 'DommaschkKamCQSDefRel'
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCQSDefTrees\n',
               'public import PlasmaLean.Design.DommaschkKamCAdmRel\n']
        out.append('''
/-!
# Honest values of the torus-C QA-defect chain (N-34, D4)

The value `XQ i` of each variable of the QA-defect chain of Dommaschk torus C at the surrogate
torus `(xA 4, xA 5)` (oracle angle): the Adm values `XA i` for `i < %d` (`XQ_lt`), the
`φ`-derivative leaves `fQ k = ev xRo (polyQ k)` (R-form), and for every product node exactly the
evaluation of its expression tree; and the identity of every new node, `c · X n = eval X e`
(`relQ_*`): by `eval_polyT` for the chunks and by definitional unfolding for the products.
Generated by `scripts/dommaschk_kam/emit_qsdef.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- The new leaf `k` (`polyQ k`: `D_φ`, `n_{R,φ}`, `n_{z,φ}`) at the surrogate torus (R-form). -/
def fQ (k : ℕ) : FA := DkPoly.ev xRo (polyQ k)

''' % (NADM, NS, OPEN))
        for i in self.newvars:
            r = self.nodes.get(i)
            if r is None or r['rel'][0] == 'chunk':
                continue
            body = self.ev_text(r['tree'])
            if r['c'] != 1:
                body = '((2 : ℂ) ^ %d)⁻¹ • %s' % (self.ctx['Qc'], body)
                assert r['c'] == 2 ** self.ctx['Qc']
            out.append('set_option linter.style.longLine false in\n/-- The honest value of the node `%s`. -/\ndef %sq : FA :=\n  %s\n\n'
                       % (self.nm(i), self.nm(i), wrap(body, 2)))
        out.append('set_option maxHeartbeats 4000000 in\n-- elaborating a literal list of strip-algebra elements\n'
                   '/-- The honest values of the variables (list): the Adm values, then the new ones. -/\n'
                   'def XQl : List FA := XAl ++%s\n\n' % lst([self.hname(i) for i in self.newvars]))
        out.append('/-- The honest values of the variables. -/\ndef XQ (i : ℕ) : FA := XQl.getD i 0\n\n')
        out.append('''/-- **The Adm values are kept.** -/
theorem XQ_lt {i : ℕ} (h : i < %d) : XQ i = XA i := by
  unfold XQ XQl XA
  rw [List.getD_append _ _ _ _ (by rw [show XAl.length = %d by rfl]; exact h)]

/-- The monomial variables are Adm variables. -/
theorem monoA_lt : ∀ ab ∈ pairsA, monoA ab.1 ab.2 < %d := by kernel_fact

/-- The monomial hypothesis of `eval_polyT` for `XQ`. -/
theorem hmonoQ {p : DkPoly.SP} (h : ∀ t ∈ p, (t.a, t.b) ∈ pairsA) :
    ∀ t ∈ p, XQ (monoA t.a t.b) = xRo 0 ^ t.a * xRo 1 ^ t.b := fun t ht => by
  rw [XQ_lt (monoA_lt _ (h t ht))]
  exact hmonoA h t ht

/-- `XQ 1 = 1`. -/
theorem XQ_one : XQ 1 = 1 := by rw [XQ_lt (by norm_num)]; rfl

/-- **The identity of the first chunk node of a new leaf.** -/
theorem relChunk0Q {n k len : ℕ} {L : ℚ} {c : ℤ} (hc : (c : ℚ) = L)
    (hn : XQ n = DkPoly.ev xRo ((polyQ k).take len)) (hne : 0 < ((polyQ k).take len).length)
    (hint : ∀ t ∈ (polyQ k).take len, (L * t.q).den = 1)
    (hp : ((polyQ k).take len).all (fun t => pairsA.contains (t.a, t.b)) = true) :
    (c : ℂ) • XQ n = Ex.eval XQ (polyT L 3 monoA ((polyQ k).take len)) := by
  rw [eval_polyT XQ XQ_one xRo (by rw [XQ_lt (by norm_num)]; rfl) (by rw [XQ_lt (by norm_num)]; rfl)
    L 3 monoA _ (List.ne_nil_of_length_pos hne) hint (hmonoQ (pairs_of_all hp)), hn, ← hc]
  push_cast; rfl

/-- **The identity of a later chunk node of a new leaf.** -/
theorem relChunkQ {n m k a len : ℕ} {L : ℚ} {c : ℤ} (hc : (c : ℚ) = L)
    (hn : XQ n = DkPoly.ev xRo ((polyQ k).take (a + len)))
    (hm : XQ m = DkPoly.ev xRo ((polyQ k).take a))
    (hne : 0 < (((polyQ k).drop a).take len).length)
    (hint : ∀ t ∈ ((polyQ k).drop a).take len, (L * t.q).den = 1)
    (hp : (((polyQ k).drop a).take len).all (fun t => pairsA.contains (t.a, t.b)) = true) :
    (c : ℂ) • XQ n = Ex.eval XQ (.add (.mul (.cst c) (pwT 1 3 (.var m)))
      (polyT L 3 monoA (((polyQ k).drop a).take len))) := by
  rw [Ex.eval, eval_polyT XQ XQ_one xRo (by rw [XQ_lt (by norm_num)]; rfl)
    (by rw [XQ_lt (by norm_num)]; rfl) L 3 monoA _ (List.ne_nil_of_length_pos hne) hint
    (hmonoQ (pairs_of_all hp)), hn, List.take_add, ev_appendA, Ex.eval, Ex.eval, eval_pwT, ← hm,
    ← hc, XQ_one, one_pow, one_mul, smul_add, Algebra.smul_def, map_intCast]
  push_cast; rfl

''' % (NADM, NADM, NADM))
        for s in self.pl.steps:
            if s.get('kind') != 'node' or s['n'] < NADM:
                continue
            out += self.rel_lines(s)
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))

    def rel_lines(self, r):
        n, c, rel = r['n'], r['c'], r['rel']
        cl = '((%d : ℤ) : ℂ)' % c
        o = ['set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
             '/-- The identity of the node `%s`. -/\n' % r['name']]
        o.append('theorem relQ_%s : %s • XQ %d = Ex.eval XQ trQ_%s := by\n' % (r['name'], cl, n, r['name']))
        if rel[0] == 'chunk':
            _, nmp, kp, a, ln, prev, final = rel
            hn = '(by rw [List.take_of_length_le (by kernel_fact)]; rfl)' if final else 'rfl'
            if a == 0:
                o.append('  exact relChunk0Q (L := %s) (by norm_num) %s (by kernel_fact) (by kernel_fact)\n'
                         '    (by kernel_fact)\n\n' % (qlean(c), hn))
            else:
                o.append('  exact relChunkQ (L := %s) (a := %d) (len := %d) (by norm_num) %s rfl (by kernel_fact)\n'
                         '    (by kernel_fact) (by kernel_fact)\n\n' % (qlean(c), a, ln, hn))
            return o
        if c == 1:
            o.append('  rw [Int.cast_one, one_smul]\n  rfl\n\n')
            return o
        o.append('  rw [show XQ %d = %sq from rfl, %sq, smul_smul,\n'
                 '    show ((%d : ℤ) : ℂ) * ((2 : ℂ) ^ %d)⁻¹ = 1 by norm_num, one_smul]\n  rfl\n\n'
                 % (n, r['name'], r['name'], c, self.ctx['Qc']))
        return o

    # ---------------------------------------------------------------- the chain
    def emit_chain(self):
        mod = 'DommaschkKamCQSDefChain'
        NV = self.nvar
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCQSDefRel\n',
               'public import PlasmaLean.Design.DommaschkKamCAdmChain\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.checkmods]
        out.append('''
/-!
# The ball chain of the torus-C QA-defect (N-34, D4)

The balls `‖X i − x i‖₀ ≤ E i` (strip `ρ = 0`, i.e. `ℓ¹` norms of the Fourier coefficients) of all
variables of the QA-defect chain of Dommaschk torus C at the surrogate torus (`XQ`,
`Design/DommaschkKamCQSDefRel`): the Adm balls (`ballA_all`, strip `0.045`) restricted to `ρ = 0`,
then variable by variable (`ballQ_k`, `chain_succ`) from the kernel checks of
`Design/DommaschkKamCQSDefCheck*` with unit weights (`node_fullw`, `center_fullw` with `P = 1`,
`E = 0`) and the node identities `relQ_*`; and the norm nodes `nQ_*`. Generated by
`scripts/dommaschk_kam/emit_qsdef.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- The Adm weight condition at `ρ = 0`. -/
theorem hq0A : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num

/-- The unit weight condition at `ρ = 0`. -/
theorem hq0Q : Real.exp 0 ≤ ((1 : ℕ) : ℝ) / 2 ^ 0 := by simp

/-- Norms of the Adm centres at `ρ = 0`. -/
theorem normQ_%d : ∀ i, i < %d → Bd 0 (xQ i) (BQ i) := fun i h => by
  rw [xQ_lt h, BQ_lt h]; exact normA hq0A i h

''' % (NS, OPEN, NADM, NADM))
        for i in self.newvars:
            r = self.pl.normrec[i]
            out.append('''set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- Norms of the centres up to the variable `%s`. -/
theorem normQ_%d : ∀ i, i < %d → Bd 0 (xQ i) (BQ i) :=
  chain_succ normQ_%d
    (center_fullw hq0Q boxQ l1Q kronQ (fun _ => rfl) %d %d %d %d %d %d %d %d %d
      (BQ %d) rfl (by kernel_fact) clQ_%s rfl cQ_%s (by kernel_fact))

''' % (self.nm(i), i + 1, i + 1, i, i, self.pl.W[i][2], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'],
                r['K'], i, self.nm(i), self.nm(i)))
        out.append('''/-- **Norms of the centres** (strip `0`). -/
theorem normQ : ∀ i, i < %d → Bd 0 (xQ i) (BQ i) := normQ_%d

/-- The Adm balls at `ρ = 0`. -/
theorem ballQ_%d : ∀ i, i < %d → Bd 0 (XQ i - xQ i) (EQ i) := fun i h => by
  rw [XQ_lt h, xQ_lt h, EQ_lt h]; exact ballA_all le_rfl hq0A i h

''' % (NV, NV, NADM, NADM))
        for k in self.newvars:
            nmk = self.nm(k)
            if self.pl.kind[k] in ('data', 'grid'):
                step = 'step_exact_w rfl (by kernel_fact)'
            else:
                r = self.nodes[k]
                step = ('node_fullw le_rfl hq0Q hWQ boxQ l1Q kronQ (fun _ => rfl)\n'
                        '      (fun i hi => normQ i (by omega)) ballQ_%d trQ_%s %d %d %d (%d : ℤ)\n'
                        '      %d %d %d %d %d %d %d %d %d (by kernel_fact) (by kernel_fact) (by kernel_fact)\n'
                        '      (by norm_num) (by kernel_fact) lQ_%s kQ_%s (by kernel_fact) relQ_%s' % (
                            k, nmk, r['dd'], r['de'], r['p'], r['c'], r['A'], r['J'], r['b'], r['W'], r['dc'],
                            r['dr'], r['Ki'], r['Kj'], r['K'], nmk, nmk, nmk))
            out.append('''set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The chain up to the variable `%s`. -/
theorem ballQ_%d : ∀ i, i < %d → Bd 0 (XQ i - xQ i) (EQ i) :=
  chain_succ ballQ_%d
    (%s)

''' % (nmk, k + 1, k + 1, k, step))
        out.append('''/-- **All balls of the chain** (strip `0`). -/
theorem ballQ_all : ∀ i, i < %d → Bd 0 (XQ i - xQ i) (EQ i) := ballQ_%d

/-- **Value bounds**: `‖X i‖₀ ≤ B i + E i`. -/
theorem valQ_le (i : ℕ) (hi : i < %d) : Bd 0 (XQ i) ((BQ i + EQ i : ℚ) : ℝ) := by
  have := (normQ i hi).add (ballQ_all i hi)
  rw [add_sub_cancel] at this; push_cast; exact this

''' % (NV, NV, NV))
        for r in self.normnodes:
            out.append('''set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The norm node `%s` (strip `0`). -/
theorem nQ_%s : Bd 0 (Ex.eval XQ trQ_%s) ((%s : ℚ) : ℝ) :=
  norm_fullw le_rfl hq0Q hWQ boxQ l1Q kronQ (fun _ => rfl) (fun i hi => normQ i hi) ballQ_all
    trQ_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d %s (by kernel_fact) (by kernel_fact) (by kernel_fact)
    lQ_%s kQ_%s (by kernel_fact)

''' % (r['name'], r['name'], r['name'], qlean(r['bound']), r['name'], r['w'][0], r['w'][1], r['w'][2], r['A'],
       r['J'], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], qlean(r['bound']), r['name'], r['name']))
        out.append('end %s\n' % NS)
        self.write(mod, ''.join(out))


    # ---------------------------------------------------------------- surrogate summary and transfer (templates)
    def out_values(self):
        """All constants of the Out and Transfer modules, validated in exact arithmetic."""
        pl, q, qn, idx, K = self.pl, self.q, self.qn, self.idx, adm_consts()
        N, M, S = self.N, self.M, self.S
        iqG, iG, iqB, iF, iQn = q['qG'], q['G'], q['qB'], q['F'], q['Qn']
        assert (iqG, iG, iqB, iF, iQn, q['GG'], q['H8']) == (238, 240, 241, 244, 226, 242, 243)
        assert (q['PV']['Df'], q['PV']['nRf'], q['PV']['nZf'], idx['qD']) == (204, 214, 222, 186)
        B, E = pl.B, pl.E
        pG, pF = pl.W[iG][2], pl.W[iF][2]
        assert pF == 2 and pG == 1
        bnd = lambda nm: qn[nm]['bound']                                   # noqa: E731
        Gb = AB.up(B[iG] + E[iG], 6)
        Fc = pl.G[iF][N][M]
        mFc = Fr(-Fc, 2 ** S)
        mFb = AB.up(abs(mFc) + E[iF], 6)
        G06 = pl.G[iG][N][M + 6]
        assert E[iG] < Fr(abs(G06), 2 ** S)
        c = self.cert
        dl = c['dl']
        muq, tU = K['muq'], K['tU']
        a10, h = B[10] + E[10], muq + tU
        io = Fr(1, 2 ** 128)
        dNgq, dQq = c['dNg'], c['dQ']
        T = pe_trees()
        av = c['a']
        bv = c['b']
        ab = [x + y for x, y in zip(av, bv)]
        assert pe_mj(ab, bv, T['Ng'])[1] <= dNgq and pe_mj(ab, bv, T['Q'])[1] <= dQq
        etaGq = AB.up(Gb + io * bnd('GI') + B[iqG] * dNgq, 6)
        epsGq = AB.up(bnd('eG') + B[iqG] * (dQq * (a10 + h) ** 17 + (B[iQn] + E[iQn]) * ((a10 + h) ** 17 - a10 ** 17)), 4)
        eBq = AB.up(bnd('bB') / 2 ** KB + dQq * B[iqB], 4)
        epsBq = AB.up(bnd('eB') + B[iqB] * ((a10 + h) ** 16 - a10 ** 16), 4)
        eDq = AB.up(bnd('dM') / 2 ** KB + K['dlD'], 4)
        epsDq = AB.up(K['epsD'] + B[186] * K['dlD'], 4)
        dG = io * bnd('GI') + B[iqG] * dNgq
        dH = ((a10 + h) ** 8 - a10 ** 8) * B[186]
        mFq = AB.up(mFb + dG * (2 * Gb + dG) * ((B[243] + E[243]) + dH) + (B[242] + E[242]) * dH, 6)
        assert epsGq < 1 and epsBq < 1
        d1q = AB.up(etaGq / (1 - epsGq), 6)
        cB = Fr(q['cB'], 2 ** KB)
        cD = Fr(q['cD'], 2 ** KB)
        eBpq = AB.up((eBq + cB * epsBq) / (1 - epsBq), 4)
        b2 = cB - eBpq
        Bmin = AB.down(Fr(math.isqrt(int(b2 * 10 ** 12)), 10 ** 6), 5)
        assert Bmin ** 2 <= b2
        delta = AB.up(d1q / (2 * Bmin), 4)
        Dmin = AB.down(cD - eDq, 4)
        d22 = mFq / (4 * (1 - epsGq) ** 2 * (1 - epsDq))
        delta2 = AB.up(Fr(math.isqrt(int(d22 * 10 ** 16)) + 1, 10 ** 8), 4)
        assert delta2 ** 2 >= d22
        iolo = tq()['iolo'][0]
        kappa = 2 * delta / (Bmin * iolo)
        oracle = Fr(7072, 10000) * delta2 / (Bmin * iolo)
        thd, thB, thk, tho = (Fr(*map(int, x.split(' / '))) for x in tq()['thr'])
        assert delta <= thd and Bmin >= thB and kappa <= thk
        assert 0 < Dmin and oracle <= tho
        ql = qlean
        V = dict(iqG=iqG, iG=iG, iqB=iqB, iF=iF, pF=pF, pG=pG, Gb=ql(Gb), eGb=ql(bnd('eG')), GIb=ql(bnd('GI')),
                 eBb=ql(bnd('eB')), bBb=ql(bnd('bB')), dMb=ql(bnd('dM')), cBi=q['cB'], cDi=q['cD'], Fc=Fc,
                 mFc=ql(mFc), mFb=ql(mFb), c06='%.3g' % (abs(G06) / 2 ** S), EG='%.2g' % float(E[iG]), G06=G06,
                 dlDf=ql(dl['Df']), dlnRf=ql(dl['nRf']), dlnZf=ql(dl['nZf']), dNg=ql(dNgq), dQ=ql(dQq),
                 etaGq=ql(etaGq), epsGq=ql(epsGq), eBq=ql(eBq), epsBq=ql(epsBq), eDq=ql(eDq), mFq=ql(mFq),
                 epsDq=ql(epsDq), d1q=ql(d1q), eBpq=ql(eBpq), Bmin=ql(Bmin), delta=ql(delta), Dmin=ql(Dmin),
                 delta2=ql(delta2),
                 etaG='%.6g' % float(etaGq), epsG='%.3g' % float(epsGq), eB='%.4g' % float(eBq),
                 epsB='%.3g' % float(epsBq), cBf='%.6g' % float(cB), eD='%.4g' % float(eDq), cDf='%.6g' % float(cD),
                 mF='%.4g' % float(mFq), epsD='%.3g' % float(epsDq), d1='%.6g' % float(d1q),
                 Dmin_f='%.4g' % float(Dmin), Bmin_f='%.6g' % float(Bmin), delta_f='%.5g' % float(delta),
                 delta2_f='%.5g' % float(delta2), kappa='%.4g' % float(kappa),
                 dioa='%.4g' % float(delta / iolo), oracle='%.4g' % float(oracle),
                 NAv=N, MAv=M, Iqc=self.ctx['Iqc'], ioup='%d / %d' % DT.cfg()['iota_abs_up'],
                 iolo=tq()['iolo'][1], iolo_txt=tq()['iolo'][2], thd=tq()['thr'][0], thB=tq()['thr'][1],
                 thk=tq()['thr'][2], tho=tq()['thr'][3], thd_txt=tq()['thr_txt'][0], thB_txt=tq()['thr_txt'][1],
                 thk_txt=tq()['thr_txt'][2], tho_txt=tq()['thr_txt'][3],
                 BUILD=self.build_note[0], PEAK=self.build_note[1],
                 Gb_f='%.6g' % float(Gb), eGb_f='%.3g' % float(bnd('eG')), GIb_f='%.4g' % float(bnd('GI')),
                 eBb_f='%.3g' % float(bnd('eB')), mFb_f='%.4g' % float(mFb))
        self.vals = dict(Gb=Gb, etaGq=etaGq, epsGq=epsGq, d1q=d1q, Bmin=Bmin, delta=delta, Dmin=Dmin, delta2=delta2,
                         kappa=kappa, oracle=oracle, eBpq=eBpq, mFq=mFq)
        return V

    def fill(self, tpl, V):
        import re
        txt = open(os.path.join(HERE, 'qsdef_tpl', tpl)).read()

        def rep(m_):
            k = m_.group(1)
            return str(V[k])
        txt = re.sub(r'@@(\w+)@@', rep, txt)
        return txt

    def emit_out(self):
        V = self.out_values()
        V2 = dict(V)
        self.write('DommaschkKamCQSDefOut', self.fill('out.lean.tpl', V2))
        # in the transfer docstring the decimal forms are wanted
        V3 = dict(V)
        for k in ('Bmin', 'delta', 'delta2'):
            V3[k] = V[k]
        self.write('DommaschkKamCQSTransfer', self.fill('transfer.lean.tpl', V3))
        print('values:', {k: '%.6g' % float(v) for k, v in self.vals.items()})


if __name__ == '__main__':
    main()
