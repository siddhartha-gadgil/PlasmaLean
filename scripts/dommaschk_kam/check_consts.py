"""Exact rational check of the constants of Design/DommaschkKamCConsts.lean (N-33 plan item 9).

Recomputes, in `fractions.Fraction`, formula by formula from Design/KamFlowStepG.lean (`SCG.kE` ...
`SCG.kap`), the derived constants of `cDK` (certified admissibility constants parsed from
Design/DommaschkKamCAdmOut.lean), the Taylor majorants `½ PolyExpr.majD2` of `resRp`, `resZp`
(second-order jets of the DkPoly data of Design/DommaschkKamFieldData.lean, mirroring `jSP`/`c2Q`
of Design/DommaschkKamCJet.lean), and asserts every inequality the Lean module proves, for the
error budget `e0qDK` and for the largest budget claimed admissible (1.15e-23).

Torus A (`--tag A`): the same checks for Design/DommaschkKamAConsts.lean (constants parsed from
Design/DommaschkKamAAdmOut.lean, split Diophantine data of `dkIotaA_period_split`).

usage: python3 check_consts.py [--tag C|A]
"""
import argparse
import os
import re
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
DES = os.path.join(HERE, '..', '..', 'PlasmaLean', 'Design')

# the choices of Design/DommaschkKamCConsts.lean
E0Q = F(1, 10**24)
CKB, CLB, C2 = F(30496), F(930856), F(40797 * 10**8)
AC = F(68553, 2**16)
RHO, D0, GAM, DLOW, E1, P = F(9, 200), F(9, 1400), F(2671, 10000), F(1208, 10000), F(2718, 1000), 7
MUQ = F(1, 10**12)
KAPB, E0MAX, TAG = F(40798 * 10**8), F(115, 10**25), 'C'
# the choices of Design/DommaschkKamAConsts.lean (torus A)
TORUS_A = dict(E0Q=F(1, 10**25), CKB=F(33193), CLB=F(1342931), C2=F(87900 * 10**8), GAM=F(3645, 10000),
               DLOW=F(1193, 10000), KAPB=F(87901 * 10**8), E0MAX=F(55, 10**25))


def polys():
    src = open(os.path.join(DES, 'DommaschkKamFieldData.lean'), encoding='utf8').read()
    out = {}
    for name in ('dD', 'dnR', 'dnZ'):
        i = src.index(f'def {name} : SP := ['); j = src.index(']\n', i)
        ts = re.findall(r'⟨mkRat \((-?\d+)\)\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩', src[i:j])
        out[name] = [(F(int(n), int(d)), int(a), int(b), int(c), int(e)) for n, d, a, b, c, e in ts]
    assert [len(out[k]) for k in ('dD', 'dnR', 'dnZ')] == [344, 362, 328]
    return out


def certified():
    src = open(os.path.join(DES, f'DommaschkKam{TAG}AdmOut.lean'), encoding='utf8').read()
    out = {}
    for m in re.finditer(r'def (\w+) : ℚ := \((.*?) : ℚ\)', src):
        out[m.group(1)] = eval(re.sub(r'(\d+)', r'F(\1)', m.group(2).replace('^', '**')))
    return out


def jmul(x, y):
    return (x[0]*y[0], x[1]*y[0] + x[0]*y[1], x[2]*y[0] + 2*(x[1]*y[1]) + x[0]*y[2])


def jpow(x, k):
    r = (F(1), F(0), F(0))
    for _ in range(k):
        r = jmul(r, x)
    return r


def jsp(P, A0, A1, C, B0, B1):
    tot = (F(0), F(0), F(0))
    for q, a, b, c, d in P:
        j = jmul(jmul(jmul(jmul((abs(q), F(0), F(0)), jpow((C, F(0), F(0)), d)), jpow((C, F(0), F(0)), c)),
                      jpow((A1, B1, F(0)), b)), jpow((A0, B0, F(0)), a))
        tot = tuple(x + y for x, y in zip(tot, j))
    return tot


def c2q(pol, A0, A1, C, B0, B1, Aw, Bw, n):
    return (jmul(jsp(pol['dD'], A0, A1, C, B0, B1), (Aw, Bw, F(0)))[2] + jsp(pol[n], A0, A1, C, B0, B1)[2]) / 2


def check(e0, pol, K, verbose):
    au, az, avR, avZ, aR, aRt, azt, aLR, aLz = [K[k] for k in
                                                'auC azC avRC avZC aRC aRtC aztC aLRC aLzC'.split()]
    bD, bDu, bDz, bnR, bnRu, bnRz, bnZ, bnZu, bnZz = [K[k] for k in
                                                     'bDC bDuC bDzC bnRC bnRuC bnRzC bnZC bnZuC bnZzC'.split()]
    sD, sR, sW, tT, tau = [K[k] for k in 'sDC sRC sWC tTC tauC'.split()]
    th = e0 / D0**4; eM = th * D0**4
    kE = sD; keta1 = sW*(avZ + avR)*kE; keta2 = bD*sR**P*(aRt + azt)*kE
    kh = aR**P*sD*sW; kTc = aR**P*sD*sW**2*(avZ + avR)*kE
    tTot = tT + kTc*eM; taup = tau - kTc*eM; g = 2*E1*GAM
    k20 = keta2/g; kc = (keta1*D0 + tTot*k20)/taup; k2 = k20 + kc; k1 = (keta1*D0 + tTot*k2)/g
    cK = k1*max(aRt, azt) + k2*D0*kh*max(avR, avZ)
    kS = (bDu + bDz)*sD*kE*D0 + P*sR*kE*D0 + sW*(avZ + avR)*kE/E1
    kRem = kS*k2*kh*max(avR, avZ)*D0 + k1*kE/E1
    XRb = bnR*sD; XZb = bnZ*sD
    kA = max((bnRu + XRb*bDu)*sD + (bnRz + XRb*bDz)*sD, (bnZu + XZb*bDu)*sD + (bnZz + XZb*bDz)*sD)
    cL = kA*cK + kE*D0**2 + kRem*th*D0**3
    kap = bD*kRem*D0 + (bDu + bDz)*cK*kE*D0**2 + C2
    Tq = e0 / D0**4 * D0**2
    A0, A1 = au + Tq*CKB, az + Tq*CKB
    c2R = c2q(pol, A0, A1, AC, CKB, CKB, aLR + Tq*CLB, CLB, 'dnR')
    c2Z = c2q(pol, A0, A1, AC, CKB, CKB, aLz + Tq*CLB, CLB, 'dnZ')
    facts = {
        'tau_prime > 0': taup > 0, 'cK <= cKb': cK <= CKB, 'cL <= cLb': cL <= CLB,
        'C2R': c2R <= C2, 'C2Z': c2Z <= C2, 'kap <= KAPB': kap <= KAPB,
        'small': 32*kap*e0/D0**4 <= 1, 'muK': 2*cK*e0/D0**2 <= MUQ,
        'mut': 2*(cK/E1)*e0/D0**3 <= MUQ, 'muL': 2*cL*e0/D0**2 <= MUQ,
        'small fails at 1e-22': 32*kap*F(1, 10**22)/D0**4 > 1, 'rho6': 6*D0 < RHO,
    }
    if verbose:
        print(f"e0 = {float(e0):.3e}: cK {float(cK):.8g}, cL {float(cL):.8g}, C2R {float(c2R):.6e}, "
              f"C2Z {float(c2Z):.6e}, kappa {float(kap):.6e}, tau' {float(taup):.6g}, "
              f"32 kap e0/d0^4 {float(32*kap*e0/D0**4):.4g}, mu budgets {float(2*cK*e0/D0**2):.2e} "
              f"{float(2*(cK/E1)*e0/D0**3):.2e} {float(2*cL*e0/D0**2):.2e}")
        print(f"  largest admissible e0: smallness {float(D0**4/(32*kap)):.4e}, "
              f"mu_t (mu = 1e-12) {float(MUQ*E1*D0**3/(2*cK)):.4e}, mu_L {float(MUQ*D0**2/(2*cL)):.4e}")
    bad = [k for k, v in facts.items() if not v]
    assert not bad, f'failed at e0 = {e0}: {bad}'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--tag', default='C')
    args = ap.parse_args()
    if args.tag == 'A':
        global TAG
        TAG = 'A'
        globals().update(TORUS_A)
    pol, K = polys(), certified()
    for e0 in (E0Q, E0MAX):
        check(e0, pol, K, True)
    print('all checks pass')


if __name__ == '__main__':
    main()
