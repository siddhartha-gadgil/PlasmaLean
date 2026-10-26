"""UNTRUSTED: constants of the KAM step for the mu > 0 passing guiding-centre torus FAMILY
(rho0 = 1/256, lam in [0, LAM1], iota_A, gamma = 0.0687), uniform over the cell (field majorants at
the largest lam = LAM1), and the Lean file PlasmaLean/Design/RationalStellaratorGCMuMaj.lean:
computable mirrors of the expression trees of gcFlowMu (1/256) LAM1, node validity (three nodes,
one uniform bound g), the Taylor constant C2, and uniformity in lam (ConstLe).
Adapted from fam_maj.py.  Usage: python lam_maj.py"""
import sys, os, re, pickle, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gcmodel as G
import fam_ball  # noqa: F401  (pickle classes)
from fam_ball import decode_slice

ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
SRC = (open(ROOT + 'KamNewtonField.lean').read() + open(ROOT + 'RationalStellaratorGCPoly.lean').read() +
       open(ROOT + 'RationalStellaratorGCMuPoly.lean').read())
LAMDEN = int(os.environ.get('LAM_DEN', '16'))
LAM1 = Fr(2, LAMDEN)
RHO0 = Fr(1, 256)


def parse_list(name):
    m = re.search(r'def %s : PolyExpr ℂ \(Fin 6\) := (mul \(const \(1 / (\d+)\)\) \()?sumE \[(.*?)\]\)?\n' % name,
                  SRC, re.S)
    scale = int(m.group(2)) if m.group(1) else 1
    body = m.group(3)
    L = []
    for coef, mono in re.findall(r'monoE \(([^)]*)\) \[([^\]]*)\]', body):
        co = Fr(coef.replace(' ', ''))
        ms = [(int(i), int(k)) for i, k in re.findall(r'\((\d), (\d+)\)', mono)]
        L.append((co, ms))
    return scale, L


LEAVES = ['Dp', 'nRp', 'nZp', 'DuP', 'DzP', 'DphP', 'nRuP', 'nRzP', 'nRphP', 'nZuP', 'nZzP', 'nZphP', 'PuP', 'EpP',
          'E4P', 'QPP4P']
LL = {n: parse_list(n) for n in LEAVES}


def npowQ(p, k):
    t = ('c', Fr(1))
    for _ in range(k):
        t = ('m', t, p)
    return t


def monoQ(c, ms):
    def rec(l):
        if not l:
            return ('c', c)
        (i, k) = l[0]
        return ('m', rec(l[1:]), npowQ(('v', i), k))
    return rec(ms)


def sumQ(ts):
    t = ('c', Fr(0))
    for x in reversed(ts):
        t = ('a', x, t)
    return t


def leafQ(n):
    scale, L = LL[n]
    t = sumQ([monoQ(c, ms) for c, ms in L])
    if scale != 1:
        t = ('m', ('c', Fr(1, scale)), t)
    return t


LEAFQ = {n: leafQ(n) for n in LEAVES}
EpQ, E4Q, QQ = LEAFQ['EpP'], LEAFQ['E4P'], LEAFQ['QPP4P']
eV = ('n', Fr(1), EpQ)


def gtree(t):
    k = t[0]
    if k == 'const':
        v = t[1]
        return ('c', Fr(1, 2) if v == 'half' else Fr(v))
    if k == 'var':
        return ('v', t[1])
    if k in ('add', 'sub', 'mul'):
        return ({'add': 'a', 'sub': 's', 'mul': 'm'}[k], gtree(t[1]), gtree(t[2]))
    if k == 'poly':
        return LEAFQ[t[1]]
    if k == 'node':
        return eV
    if k == 'ref':
        return gtree(t[2])


W3 = gtree(G.eW3)
KD, KR, KZ = gtree(G.eKD), gtree(G.eKR), gtree(G.eKZ)
eV4 = ('n', Fr(1), E4Q)
eBm = ('m', QQ, ('m', eV, eV4))


def trees(lam):
    eN = ('n', Fr(1), ('m', ('c', -lam), eBm))
    eF = ('m', ('s', ('c', Fr(1)), ('m', ('c', lam / 2), eBm)), eN)
    Y = {k: ('m', ('c', Fr(1, 2)), ('m', W3, K)) for k, K in [('D', KD), ('R', KR), ('Z', KZ)]}
    D = ('a', LEAFQ['Dp'], ('m', ('c', RHO0), ('m', eF, Y['D'])))
    nR = ('a', LEAFQ['nRp'], ('m', ('c', RHO0), ('m', eF, Y['R'])))
    nZ = ('a', LEAFQ['nZp'], ('m', ('c', RHO0), ('m', eF, Y['Z'])))
    resR = ('s', ('m', D, ('v', 4)), nR)
    resZ = ('s', ('m', D, ('v', 5)), nZ)
    return eN, resR, resZ


def mQ(a, g, t, memo):
    key = ('m', id(t))
    if key in memo:
        return memo[key]
    k = t[0]
    if k == 'c':
        r = abs(t[1])
    elif k == 'v':
        r = a[t[1]]
    elif k in ('a', 's'):
        r = mQ(a, g, t[1], memo) + mQ(a, g, t[2], memo)
    elif k == 'm':
        r = mQ(a, g, t[1], memo) * mQ(a, g, t[2], memo)
    else:
        r = g
    memo[key] = r
    return r


def mDQ(a, b, g, t, memo):
    key = ('d', id(t))
    if key in memo:
        return memo[key]
    k = t[0]
    if k == 'c':
        r = Fr(0)
    elif k == 'v':
        r = b[t[1]]
    elif k in ('a', 's'):
        r = mDQ(a, b, g, t[1], memo) + mDQ(a, b, g, t[2], memo)
    elif k == 'm':
        r = mDQ(a, b, g, t[1], memo) * mQ(a, g, t[2], memo) + mQ(a, g, t[1], memo) * mDQ(a, b, g, t[2], memo)
    else:
        r = g ** 3 / 2 * mDQ(a, b, g, t[2], memo)
    memo[key] = r
    return r


def mD2Q(a, b, g, t, memo):
    key = ('e', id(t))
    if key in memo:
        return memo[key]
    k = t[0]
    if k in ('c', 'v'):
        r = Fr(0)
    elif k in ('a', 's'):
        r = mD2Q(a, b, g, t[1], memo) + mD2Q(a, b, g, t[2], memo)
    elif k == 'm':
        p, q = t[1], t[2]
        r = (mD2Q(a, b, g, p, memo) * mQ(a, g, q, memo) + 2 * (mDQ(a, b, g, p, memo) * mDQ(a, b, g, q, memo))
             + mQ(a, g, p, memo) * mD2Q(a, b, g, q, memo))
    else:
        r = 3 * g ** 5 / 4 * mDQ(a, b, g, t[2], memo) ** 2 + g ** 3 / 2 * mD2Q(a, b, g, t[2], memo)
    memo[key] = r
    return r


def up(x, d=4):
    x = Fr(x)
    e = math.floor(math.log10(float(x)))
    sc = Fr(10) ** (e - d + 1)
    return math.ceil(x / sc) * sc


def down(x, d=4):
    x = Fr(x)
    e = math.floor(math.log10(float(x)))
    sc = Fr(10) ** (e - d + 1)
    return math.floor(x / sc) * sc


def node_bounds(a):
    """(mE, mE4, mBm-coefficient, g): uniform node bound g with g^2 (1 - m) >= 1 for the three nodes;
    the node N has m = LAM1 * mQ(QPP4) * g^2."""
    mE = up(mQ(a, Fr(0), EpQ, {}), 4)
    mE4 = up(mQ(a, Fr(0), E4Q, {}), 4)
    mQQ = up(mQ(a, Fr(0), QQ, {}), 4)
    g = Fr(1)
    for _ in range(60):
        mN = LAM1 * mQQ * g * g
        need = max(mE, mE4, mN)
        assert need < 1, ('node invalid', float(need))
        g2 = up(Fr(1 / math.sqrt(1 - float(need))) * Fr(1000001, 1000000), 6)
        if g2 <= g and g * g * (1 - max(mE, mE4, LAM1 * mQQ * g * g)) >= 1:
            break
        g = max(g2, g)
    mN = up(LAM1 * mQQ * g * g, 4)
    assert g * g * (1 - max(mE, mE4, mN)) >= 1
    return mE, mE4, mQQ, mN, g


if __name__ == '__main__':
    H = pickle.load(open(os.environ.get('LAM_PKL_H', '/tmp/lamc/lam_cert_H.pkl'), 'rb'))['H']
    L = pickle.load(open(os.environ.get('LAM_PKL_L', '/tmp/lamc/lam_cert_L.pkl'), 'rb'))['L']
    nmH = {v: k for k, v in H['names'].items()}
    nmL = {v: k for k, v in L['names'].items()}
    MU = Fr(1, 10 ** 11)
    rA = Fr(1257, 10000)
    d0 = rA / 7
    normsH = {r['meta']['name']: r for r in H['nodes'] if r.get('var') is None}
    e0R = up(normsH['resR']['rad'], 3) / 2 ** 96
    e0Z = up(normsH['resZ']['rad'], 3) / 2 ** 96
    e0 = up(max(e0R, e0Z), 2)
    print('e0 = %s (%.4e %.4e)' % (e0, e0R, e0Z))
    ac = Fr(74315, 2 ** 16)
    BH, EH, BL, EL = H['B'], H['E'], L['B'], L['E']
    au0, az0 = BH[nmH['U']] + EH[nmH['U']], BH[nmH['Z']] + EH[nmH['Z']]
    aRt0, azt0 = BH[nmH['thU']], BH[nmH['thZ']]
    aLR0 = up((BH[nmH['LRx']] + EH[nmH['LRx']]) / 2 ** 96, 4)
    aLz0 = up((BH[nmH['LZx']] + EH[nmH['LZx']]) / 2 ** 96, 4)
    au0, az0, aRt0, azt0 = (up(x, 4) for x in (au0, az0, aRt0, azt0))
    au, az, aRt, azt, aLR, aLz = (x + MU for x in (au0, az0, aRt0, azt0, aLR0, aLz0))
    fb = {}
    for n in ['Dt', 'Dtu', 'Dtz', 'nRt', 'nRtu', 'nRtz', 'nZt', 'nZtu', 'nZtz']:
        i = nmL[n + 'F']
        fb[n] = up(BL[i] + EL[i], 5)
    norms = {r['meta']['name']: r for r in L['nodes'] if r.get('var') is None}
    RDd = up(norms['DdevF']['rad'], 4)
    RWd = up(norms['WdevF']['rad'], 4)
    RX = up(norms['XF']['rad'], 3)
    dD = RDd / abs(norms['DdevF']['cscale'])
    dW = RWd / abs(norms['WdevF']['cscale'])
    dc0, wc0 = Fr(2126414735707981, 2 ** 51), -Fr(5398240620830529, 2 ** 59)
    sD = up(1 / (dc0 - dD), 5)
    sW = up(1 / (abs(wc0) - dW), 5)
    sR = 1 / (1 - au)
    vY = nmL['YF']
    YB = BL[vY] + EL[vY]
    tT = up(YB / (1 - RX), 5)
    fY = L['fam'][vY]
    NL_, ML_, SL_ = L['N'], L['M'], L['S']
    avgs = [Fr(decode_slice(sd, NL_, ML_, fY['s'])[NL_][ML_], 2 ** SL_) for sd in fY['slices']]
    Ym0 = avgs[0]
    Ym1 = 2 * sum(abs(x) for x in avgs[1:])
    tau = down(abs(Ym0) - Ym1 - EL[vY] - YB * RX / (1 - RX), 3)
    gam, E1 = Fr(687, 10000), Fr(2718, 1000)
    th = e0 / d0 ** 4
    eM = th * d0 ** 4
    kE = sD
    keta1 = sW * (az + au) * kE
    keta2 = fb['Dt'] * sR ** 3 * (aRt + azt) * kE
    kh = (1 + au) ** 3 * sD * sW
    kTc = (1 + au) ** 3 * sD * sW ** 2 * (az + au) * kE
    tTot = tT + kTc * eM
    taup = tau - kTc * eM
    gg = 2 * E1 * gam
    k20 = keta2 / gg
    kc = (keta1 * d0 + tTot * k20) / taup
    k2 = k20 + kc
    k1 = (keta1 * d0 + tTot * k2) / gg
    mA, mV = max(aRt, azt), max(au, az)
    cK = k1 * mA + k2 * d0 * kh * mV
    kS = (fb['Dtu'] + fb['Dtz']) * sD * kE * d0 + 3 * sR * kE * d0 + sW * (az + au) * kE / E1
    kRem = kS * k2 * kh * mV * d0 + k1 * kE / E1
    XRb, XZb = fb['nRt'] * sD, fb['nZt'] * sD
    kA = max((fb['nRtu'] + XRb * fb['Dtu']) * sD + (fb['nRtz'] + XRb * fb['Dtz']) * sD,
             (fb['nZtu'] + XZb * fb['Dtu']) * sD + (fb['nZtz'] + XZb * fb['Dtz']) * sD)
    cL = kA * cK + kE * d0 ** 2 + kRem * th * d0 ** 3
    cKb, cLb = up(cK, 3), up(cL, 3)
    Tq = th * d0 ** 2
    aT = [au + Tq * cKb, az + Tq * cKb, ac, ac, aLR + Tq * cLb, aLz + Tq * cLb]
    mvec = [cKb, cKb, Fr(0), Fr(0), cLb, cLb]
    aTQ = [au0 + Fr(2, 10 ** 10), az0 + Fr(2, 10 ** 10), ac, ac, aLR0 + Fr(2, 10 ** 10), aLz0 + Fr(2, 10 ** 10)]
    assert all(aTQ[i] >= aT[i] for i in range(6))
    mE, mE4, mQQ, mN, g = node_bounds(aTQ)
    eN, resR, resZ = trees(LAM1)
    C2R = mD2Q(aTQ, mvec, g, resR, {}) / 2
    C2Z = mD2Q(aTQ, mvec, g, resZ, {}) / 2
    C2 = up(max(C2R, C2Z), 3)
    kap = fb['Dt'] * kRem * d0 + (fb['Dtu'] + fb['Dtz']) * cK * kE * d0 ** 2 + C2
    small = 32 * kap * e0 / d0 ** 4
    print('cK %.1f cL %.1f  mE %.4f mE4 %.4f mQQ %.4f mN %.4f g %s' % (cK, cL, mE, mE4, mQQ, mN, float(g)))
    print('C2R %.4e C2Z %.4e C2 %.3e kap %.4e smallness %.4e' % (C2R, C2Z, C2, kap, small))
    print('mu budgets: %.3e %.3e %.3e  (mu = %.1e)' % (2 * cK * e0 / d0 ** 2, 2 * (cK / E1) * e0 / d0 ** 3,
                                                      2 * cL * e0 / d0 ** 2, MU))
    print('sD %s sW %s tT %s tau %s fb %s' % (float(sD), float(sW), float(tT), float(tau),
                                             {k: float(v) for k, v in fb.items()}))
    CONST = dict(au0=au0, az0=az0, aRt0=aRt0, azt0=azt0, aLR0=aLR0, aLz0=aLz0, fb=fb, sD=sD, sW=sW, tT=tT,
                 tau=tau, RDd=RDd, RWd=RWd, RX=RX, cKb=cKb, cLb=cLb, C2=C2, g=g, mE=mE, mE4=mE4, mQQ=mQQ, mN=mN,
                 e0=e0, d0c=dc0, w0c=wc0, Ym0=Ym0, Ym1=Ym1, small=small, kap=kap, aTQ=aTQ, mvec=mvec,
                 LAM1=LAM1)
    for P_ in [H, L]:
        for r_ in P_['nodes']:
            if r_.get('var') is None:
                CONST['R_' + r_['meta']['name']] = up(r_['rad'], 4)
    pickle.dump(CONST, open('/tmp/lamc/lam_const.pkl', 'wb'))
    print('ok')


# ----------------------------------------------------------------------------- the Lean file
def ql(q):
    q = Fr(q)
    if q.denominator == 1:
        return '(%d : ℚ)' % q.numerator
    d = q.denominator
    k = 0
    while d % 10 == 0:
        d //= 10
        k += 1
    if d == 1:
        return '(%d / 10 ^ %d : ℚ)' % (q.numerator, k)
    if q.denominator & (q.denominator - 1) == 0:
        return '(%d / 2 ^ %d : ℚ)' % (q.numerator, q.denominator.bit_length() - 1)
    return '(%d / %d : ℚ)' % (q.numerator, q.denominator)


def leaf_int_list(n):
    scale, Lst = LL[n]
    items = []
    for c, ms in Lst:
        cc = c
        assert Fr(cc).denominator == 1
        items.append('(%d, [%s])' % (int(cc), ', '.join('(%d, %d)' % m for m in ms)))
    return '[' + ', '.join(items) + ']'


def emit_lean(CONST):
    C = CONST
    vec = lambda xs: '\n  ![' + ',\n    '.join(ql(x) for x in xs) + ']'
    lam = Fr(C['LAM1'])
    lamn, lamd = lam.numerator, lam.denominator
    sQ = LL['QPP4P'][0]
    sE4 = LL['E4P'][0]
    assert sE4 == 1
    txt = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCTorusMaj
public import PlasmaLean.Design.RationalStellaratorGCMuInstance
public import PlasmaLean.Theory.KAM.PolyExprSConstMono
public import PlasmaLean.Certificates.KernelFact
public import PlasmaLean.Certificates.EvalCert

/-!
# Majorants of the `μ > 0` passing guiding-centre field family: node validity and `C₂`

The computable mirrors (`Theory/KAM/PolyExprSMajQ`, `PQS`) of the expression trees of the
`μ > 0` passing field `gcFlowMu (1/256) λ₁` (`λ₁ = @LAM@`, the largest pitch parameter of the cell),
built from the leaf mirrors of `Design/RationalStellaratorGCTorusMaj` and of the new leaves
`E₄`, `Q P P₄`, with their embeddings (`*_toS`), and the facts of the KAM theorem that need
majorants, at the bounds `aTQ` of the family tori:

* **node validity** with one uniform node bound `g = gQ` for the three nodes
  `(1 + E)^{−1/2}`, `(1 + E₄)^{−1/2}` and `(1 − λ₁|B|)^{−1/2}` (`nodesOK_resR`, `nodesOK_resZ`);
* **the Taylor constant** (`mu_C2R`, `mu_C2Z`): `½ majD2(res) ≤ C₂ = @C2@`;
* **uniformity in the pitch parameter** (`mu_C2R_cell`, `mu_valid_cell`): `λ` enters the trees only
  through constants of modulus `≤ λ₁` (`Theory/KAM/PolyExprSConstMono`, `ConstLe`), so the bounds at
  `λ₁` hold for every `λ ∈ [0, λ₁]`.

The evaluations of the rational majorants (`mQ`, `mD2Q`, `allNodes`) are evaluation
certificates (`eval_decide`, `eval_cert`: one kernel leaf per rational operation, shared
subtrees evaluated once); the remaining closed comparisons are `kernel_fact` proof terms.
Generated by `scripts/gc_kam/lam_maj.py`.

**Sanity.** `gcDMQ_toS`: the mirror embeds to the field expression `gcDM (1/256) λ₁`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCMu

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM.PQS

/-- The largest pitch parameter of the cell. -/
def lam1 : ℝ := @LAMR@

set_option linter.style.longLine false in
/-- The (integer) monomials of `E₄`. -/
def E4PL : List (ℤ × List (Fin 6 × ℕ)) :=
  @E4L@

/-- The mirror of `E₄`. -/
def E4PQ : PQS (Fin 6) := polyQ (E4PL.map fun cm => ((cm.1 : ℚ), cm.2))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
/-- The mirror of `E₄` embeds to it. -/
theorem E4PQ_toS : E4PQ.toS = PolyExprS.ofPoly E4P := by
  rw [E4PQ, toS_polyQ]
  simp only [E4PL, List.map, E4P, Rat.cast_intCast, Int.cast_ofNat, Int.cast_neg]
  norm_num

set_option linter.style.longLine false in
/-- The (integer) monomials of `@SQ@ Q P P₄`. -/
def QPP4PL : List (ℤ × List (Fin 6 × ℕ)) :=
  @QL@

/-- The mirror of `Q P P₄`. -/
def QPP4PQ : PQS (Fin 6) :=
  .mul (.const (1 / @SQ@)) (polyQ (QPP4PL.map fun cm => ((cm.1 : ℚ), cm.2)))

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- the expanded `Q P P₄` (106 monomials) is normalised by `norm_num`
/-- The mirror of `Q P P₄` embeds to it. -/
theorem QPP4PQ_toS : QPP4PQ.toS = PolyExprS.ofPoly QPP4P := by
  rw [QPP4PQ, toS, toS_polyQ]
  simp only [toS, QPP4PL, List.map, QPP4P, PolyExprS.ofPoly, Rat.cast_intCast, Int.cast_ofNat,
    Int.cast_neg]
  norm_num

/-- The mirror of the node `(1 + E₄)^{−1/2}`. -/
def eV4Q : PQS (Fin 6) := .isqrt 1 E4PQ

/-- The mirror of the node embeds to it. -/
theorem eV4Q_toS : eV4Q.toS = eV4 := by
  simp only [eV4Q, toS, E4PQ_toS, eV4, Rat.cast_one]

/-- The mirror of `|B|`. -/
def eBmQ : PQS (Fin 6) := .mul QPP4PQ (.mul eVQ eV4Q)

/-- The mirror of `|B|` embeds to it. -/
theorem eBmQ_toS : eBmQ.toS = eBm := by
  simp only [eBmQ, toS, QPP4PQ_toS, eVQ_toS, eV4Q_toS, eBm]

/-- The mirror of the node `(1 − λ₁|B|)^{−1/2}`. -/
def eNQ : PQS (Fin 6) := .isqrt 1 (.mul (.const (-@LAMQ@)) eBmQ)

/-- The mirror of the node embeds to it. -/
theorem eNQ_toS : eNQ.toS = RationalStellaratorGC.eN lam1 := by
  simp only [eNQ, toS, eBmQ_toS, RationalStellaratorGC.eN, lam1, Rat.cast_one]
  norm_num

/-- The mirror of `F`. -/
def eFQ : PQS (Fin 6) := .mul (.sub (.const 1) (.mul (.const (@LAMQ@ / 2)) eBmQ)) eNQ

/-- The mirror of `F` embeds to it. -/
theorem eFQ_toS : eFQ.toS = eF lam1 := by
  simp only [eFQ, toS, eBmQ_toS, eNQ_toS, eF, lam1]
  norm_num

/-- The mirror of `½ W³ κ_D`. -/
def eYDQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKDQ)
/-- The mirror of `½ W³ κ_R`. -/
def eYRQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKRQ)
/-- The mirror of `½ W³ κ_z`. -/
def eYZQ : PQS (Fin 6) := .mul (.const (1 / 2)) (.mul eW3Q eKZQ)

/-- The mirror of `½ W³ κ_D` embeds to it. -/
theorem eYDQ_toS : eYDQ.toS = eYD := by
  simp only [eYDQ, toS, eW3Q_toS, eKDQ_toS, eYD]; norm_num
/-- The mirror of `½ W³ κ_R` embeds to it. -/
theorem eYRQ_toS : eYRQ.toS = eYR := by
  simp only [eYRQ, toS, eW3Q_toS, eKRQ_toS, eYR]; norm_num
/-- The mirror of `½ W³ κ_z` embeds to it. -/
theorem eYZQ_toS : eYZQ.toS = eYZ := by
  simp only [eYZQ, toS, eW3Q_toS, eKZQ_toS, eYZ]; norm_num

/-- The mirror of `D̃` at `λ₁`. -/
def gcDMQ : PQS (Fin 6) := .add DpQ (.mul (.const (1 / 256)) (.mul eFQ eYDQ))
/-- The mirror of `ñ_R` at `λ₁`. -/
def gcNRMQ : PQS (Fin 6) := .add nRpQ (.mul (.const (1 / 256)) (.mul eFQ eYRQ))
/-- The mirror of `ñ_z` at `λ₁`. -/
def gcNZMQ : PQS (Fin 6) := .add nZpQ (.mul (.const (1 / 256)) (.mul eFQ eYZQ))

/-- The mirror of `D̃` embeds to it. -/
theorem gcDMQ_toS : gcDMQ.toS = gcDM (1 / 256) lam1 := by
  simp only [gcDMQ, toS, DpQ_toS, eFQ_toS, eYDQ_toS, gcDM]; norm_num
/-- The mirror of `ñ_R` embeds to it. -/
theorem gcNRMQ_toS : gcNRMQ.toS = gcNRM (1 / 256) lam1 := by
  simp only [gcNRMQ, toS, nRpQ_toS, eFQ_toS, eYRQ_toS, gcNRM]; norm_num
/-- The mirror of `ñ_z` embeds to it. -/
theorem gcNZMQ_toS : gcNZMQ.toS = gcNZM (1 / 256) lam1 := by
  simp only [gcNZMQ, toS, nZpQ_toS, eFQ_toS, eYZQ_toS, gcNZM]; norm_num

/-- The mirror of the `R`-residual expression. -/
def resRQ : PQS (Fin 6) := .sub (.mul gcDMQ (.var 4)) gcNRMQ

/-- The mirror of the `z`-residual expression. -/
def resZQ : PQS (Fin 6) := .sub (.mul gcDMQ (.var 5)) gcNZMQ

/-- The mirror of the `R`-residual embeds to it. -/
theorem resRQ_toS : resRQ.toS = (gcFlowMu (1 / 256) lam1).resRp := by
  simp only [resRQ, toS, gcDMQ_toS, gcNRMQ_toS]; rfl

/-- The mirror of the `z`-residual embeds to it. -/
theorem resZQ_toS : resZQ.toS = (gcFlowMu (1 / 256) lam1).resZp := by
  simp only [resZQ, toS, gcDMQ_toS, gcNZMQ_toS]; rfl

/-! ## The bounds -/

/-- Rational upper bounds of the torus variables on the Taylor segments and the admissible tori. -/
def aTQ : Fin 6 → ℚ := @ATQ@

/-- The perturbation profile `(c_K, c_K, 0, 0, c_L, c_L)`. -/
def mvQ : Fin 6 → ℚ := @MVQ@

/-- The bound of the majorant of `E`. -/
def mEQ : ℚ := @MEQ@
/-- The bound of the majorant of `E₄`. -/
def mE4Q : ℚ := @ME4Q@
/-- The bound of the majorant of `Q P P₄`. -/
def mQQ : ℚ := @MQQ@
/-- The bound of the majorant under the node `(1 − λ₁|B|)^{−1/2}`. -/
def mNQ : ℚ := @MNQ@
/-- The uniform node bound. -/
def gQ : ℚ := @GQ@
/-- The Taylor constant. -/
def C2Q : ℚ := @C2Q@

/-- Expressions without nodes satisfy the node condition. -/
theorem nodesOK_ofPoly (a : Fin 6 → ℝ) (g : ℝ) (e : PolyExpr ℂ (Fin 6)) :
    NodesOK a g (PolyExprS.ofPoly e) := by
  induction e with
  | const _ => trivial
  | var _ => trivial
  | add p q hp hq => exact ⟨hp, hq⟩
  | sub p q hp hq => exact ⟨hp, hq⟩
  | mul p q hp hq => exact ⟨hp, hq⟩

/-- The bounds `aTQ` are nonnegative. -/
theorem aTQ_nonneg : ∀ i, (0 : ℝ) ≤ (aTQ i : ℝ) := fun i => by
  have := (show ∀ i, (0 : ℚ) ≤ aTQ i by kernel_fact) i
  exact_mod_cast this

set_option maxRecDepth 100000 in
/-- **The majorant of `E` at `aTQ`.** -/
theorem mu_maj_E : PolyExpr.maj (fun i => (aTQ i : ℝ)) EpP ≤ (mEQ : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← EpPQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by kernel_fact) le_rfl EpPQ (nodesOK_EpPQ _ _)).trans ?_
  exact_mod_cast (show mQ aTQ 0 EpPQ ≤ mEQ by eval_decide)

set_option maxRecDepth 100000 in
/-- **The majorant of `E₄` at `aTQ`.** -/
theorem mu_maj_E4 : PolyExpr.maj (fun i => (aTQ i : ℝ)) E4P ≤ (mE4Q : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← E4PQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by kernel_fact) le_rfl E4PQ
    (nodesOK_polyQ _ _ _)).trans ?_
  exact_mod_cast (show mQ aTQ 0 E4PQ ≤ mE4Q by eval_decide)

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
/-- **The majorant of `Q P P₄` at `aTQ`.** -/
theorem mu_maj_Q : PolyExpr.maj (fun i => (aTQ i : ℝ)) QPP4P ≤ (mQQ : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← QPP4PQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by kernel_fact) le_rfl QPP4PQ
    ⟨trivial, nodesOK_polyQ _ _ _⟩).trans ?_
  exact_mod_cast (show mQ aTQ 0 QPP4PQ ≤ mQQ by eval_decide)

/-- The uniform node bound is nonnegative. -/
theorem gQ_nonneg : (0 : ℝ) ≤ (gQ : ℝ) := by exact_mod_cast (show (0 : ℚ) ≤ gQ by kernel_fact)

/-- The node `(1 + E)^{−1/2}` at `aTQ`. -/
theorem nodesOK_eV : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eV := by
  have hm := mu_maj_E
  rw [← PolyExprS.maj_ofPoly] at hm
  have h1 : (mEQ : ℝ) < 1 := by exact_mod_cast (show mEQ < 1 by kernel_fact)
  exact ⟨hm.trans_lt h1, isqG_le_q hm h1 gQ_nonneg
    (by exact_mod_cast (show 1 ≤ gQ ^ 2 * (1 - mEQ) by kernel_fact)),
    nodesOK_ofPoly _ _ _⟩

/-- The node `(1 + E₄)^{−1/2}` at `aTQ`. -/
theorem nodesOK_eV4 : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eV4 := by
  have hm := mu_maj_E4
  rw [← PolyExprS.maj_ofPoly] at hm
  have h1 : (mE4Q : ℝ) < 1 := by exact_mod_cast (show mE4Q < 1 by kernel_fact)
  exact ⟨hm.trans_lt h1, isqG_le_q hm h1 gQ_nonneg
    (by exact_mod_cast (show 1 ≤ gQ ^ 2 * (1 - mE4Q) by kernel_fact)),
    nodesOK_ofPoly _ _ _⟩

/-- The tree `|B|` at `aTQ`. -/
theorem nodesOK_eBm : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eBm :=
  ⟨nodesOK_ofPoly _ _ _, nodesOK_eV, nodesOK_eV4⟩

set_option maxRecDepth 100000 in
/-- `maj |B| ≤ m_Q g²` at `aTQ`. -/
theorem maj_eBm_le : PolyExprS.maj (fun i => (aTQ i : ℝ)) eBm ≤ (mQQ : ℝ) * gQ * gQ := by
  rw [← eBmQ_toS]
  refine (maj_le (a := aTQ) (g := gQ) (by kernel_fact) (by kernel_fact) eBmQ
    (by rw [eBmQ_toS]; exact nodesOK_eBm)).trans ?_
  have : mQ aTQ gQ eBmQ = mQ aTQ gQ QPP4PQ * (gQ * gQ) := rfl
  have hq : mQ aTQ gQ QPP4PQ = mQ aTQ 0 QPP4PQ := rfl
  rw [this, hq]
  have h := (show mQ aTQ 0 QPP4PQ ≤ mQQ by eval_decide)
  have hg : (0 : ℚ) ≤ gQ * gQ := by have := (show (0 : ℚ) ≤ gQ by kernel_fact); positivity
  have := mul_le_mul_of_nonneg_right h hg
  have h' : ((mQ aTQ 0 QPP4PQ : ℚ) : ℝ) * ((gQ : ℝ) * gQ) ≤ (mQQ : ℝ) * ((gQ : ℝ) * gQ) := by
    exact_mod_cast this
  push_cast
  linarith [h', show (mQQ : ℝ) * gQ * gQ = mQQ * (gQ * gQ) by ring]

/-- The node `(1 − λ₁|B|)^{−1/2}` at `aTQ`. -/
theorem nodesOK_eN :
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (RationalStellaratorGC.eN lam1) := by
  have hB := maj_eBm_le
  have hm : PolyExprS.maj (fun i => (aTQ i : ℝ)) (.mul (.const (-(lam1 : ℂ))) eBm) ≤ (mNQ : ℝ) := by
    simp only [PolyExprS.maj, norm_neg, Complex.norm_real, Real.norm_eq_abs, lam1]
    have h := (show @LAMQ@ * (mQQ * gQ * gQ) ≤ mNQ by kernel_fact)
    have h' : ((@LAMQ@ * (mQQ * gQ * gQ) : ℚ) : ℝ) ≤ (mNQ : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_pos (by norm_num)]
    nlinarith [PolyExprS.maj_nonneg (fun i => aTQ_nonneg i) eBm]
  have h1 : (mNQ : ℝ) < 1 := by exact_mod_cast (show mNQ < 1 by kernel_fact)
  exact ⟨hm.trans_lt h1, isqG_le_q hm h1 gQ_nonneg
    (by exact_mod_cast (show 1 ≤ gQ ^ 2 * (1 - mNQ) by kernel_fact)), trivial, nodesOK_eBm⟩

/-- The trees of `F` and the corrections at `aTQ`. -/
theorem nodesOK_eF : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (eF lam1) :=
  ⟨⟨trivial, trivial, nodesOK_eBm⟩, nodesOK_eN⟩

/-- The old corrections `½ W³ κ` at `aTQ` (only the node `(1 + E)^{−1/2}`). -/
theorem nodesOK_eY : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eYD ∧
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eYR ∧ NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) eYZ := by
  have hm := mu_maj_E
  rw [← PolyExprS.maj_ofPoly, ← EpPQ_toS] at hm
  have h1 : (mEQ : ℝ) < 1 := by exact_mod_cast (show mEQ < 1 by kernel_fact)
  have hall := fun e he => nodesOK_of_all (a := fun i => (aTQ i : ℝ)) (g := (gQ : ℝ))
    (nodesOK_EpPQ _ _) (hm.trans_lt h1) (isqG_le_q hm h1 gQ_nonneg
      (by exact_mod_cast (show 1 ≤ gQ ^ 2 * (1 - mEQ) by kernel_fact))) e he
  refine ⟨?_, ?_, ?_⟩
  · rw [← eYDQ_toS]; exact hall _ (by eval_cert)
  · rw [← eYRQ_toS]; exact hall _ (by eval_cert)
  · rw [← eYZQ_toS]; exact hall _ (by eval_cert)

/-- **The node condition on the residual trees** at `aTQ`, `λ = λ₁`. -/
theorem nodesOK_res : NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (gcFlowMu (1 / 256) lam1).resRp ∧
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) (gcFlowMu (1 / 256) lam1).resZp := by
  obtain ⟨hD, hR, hZ⟩ := nodesOK_eY
  have hF := nodesOK_eF
  have p := nodesOK_ofPoly (fun i => (aTQ i : ℝ)) (gQ : ℝ)
  exact ⟨⟨⟨⟨p _, trivial, hF, hD⟩, trivial⟩, p _, trivial, hF, hR⟩,
    ⟨⟨⟨p _, trivial, hF, hD⟩, trivial⟩, p _, trivial, hF, hZ⟩⟩

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `R`-residual** at `aTQ`, `λ = λ₁`. -/
theorem mu_C2R : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQ i : ℝ))
    (gcFlowMu (1 / 256) lam1).resRp / 2 ≤ (C2Q : ℝ) := by
  rw [← resRQ_toS]
  have h2 := majD2_le (a := aTQ) (b := mvQ) (g := gQ) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) resRQ (by rw [resRQ_toS]; exact nodesOK_res.1)
  have h3 : (mD2Q aTQ mvQ gQ resRQ : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show mD2Q aTQ mvQ gQ resRQ / 2 ≤ C2Q by eval_decide)
  linarith

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `z`-residual** at `aTQ`, `λ = λ₁`. -/
theorem mu_C2Z : PolyExprS.majD2 (fun i => (aTQ i : ℝ)) (fun i => (mvQ i : ℝ))
    (gcFlowMu (1 / 256) lam1).resZp / 2 ≤ (C2Q : ℝ) := by
  rw [← resZQ_toS]
  have h2 := majD2_le (a := aTQ) (b := mvQ) (g := gQ) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) resZQ (by rw [resZQ_toS]; exact nodesOK_res.2)
  have h3 : (mD2Q aTQ mvQ gQ resZQ : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show mD2Q aTQ mvQ gQ resZQ / 2 ≤ C2Q by eval_decide)
  linarith

/-! ## Uniformity over the cell -/

/-- The pitch parameter enters `F` only through constants of modulus `≤ λ₁`. -/
theorem constLe_eF {lm : ℝ} (h : |lm| ≤ lam1) : PolyExprS.ConstLe (eF lm) (eF lam1) := by
  have h2 : ‖((lm : ℂ) / 2)‖ ≤ ‖((lam1 : ℂ) / 2)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    rw [abs_of_pos (show (0 : ℝ) < lam1 by norm_num [lam1])]; linarith
  have h1 : ‖(-(lm : ℂ))‖ ≤ ‖(-(lam1 : ℂ))‖ := by
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (show (0 : ℝ) < lam1 by norm_num [lam1])]; exact h
  exact .mul (.sub (.const le_rfl) (.mul (.const h2) (PolyExprS.constLe_refl _)))
    (.isqrt 1 (.mul (.const h1) (PolyExprS.constLe_refl _)))

/-- The residual trees at `λ` are `ConstLe` those at `λ₁` for `|λ| ≤ λ₁`. -/
theorem constLe_res {lm : ℝ} (h : |lm| ≤ lam1) :
    PolyExprS.ConstLe (gcFlowMu (1 / 256) lm).resRp (gcFlowMu (1 / 256) lam1).resRp ∧
    PolyExprS.ConstLe (gcFlowMu (1 / 256) lm).resZp (gcFlowMu (1 / 256) lam1).resZp := by
  have hF := constLe_eF h
  have r := PolyExprS.constLe_refl (𝕜 := ℂ) (σ := Fin 6)
  exact ⟨.sub (.mul (.add (r _) (.mul (r _) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (r _) (.mul hF (r _)))),
    .sub (.mul (.add (r _) (.mul (r _) (.mul hF (r _)))) (r _))
      (.add (r _) (.mul (r _) (.mul hF (r _))))⟩

/-- **The Taylor constants, uniform over the cell** (`|λ| ≤ λ₁`, bounds `a ≤ aTQ`). -/
theorem mu_C2_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlowMu (1 / 256) lm).resRp / 2 ≤ (C2Q : ℝ) ∧
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlowMu (1 / 256) lm).resZp / 2 ≤ (C2Q : ℝ) := by
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by kernel_fact) i
    exact_mod_cast this
  obtain ⟨cR, cZ⟩ := constLe_res hlm
  have vR := valid_of_nodesOK nodesOK_res.1
  have vZ := valid_of_nodesOK nodesOK_res.2
  have mR := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb haa
    (fun _ => le_rfl) (cR.valid aTQ_nonneg vR)
  have mZ := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb haa
    (fun _ => le_rfl) (cZ.valid aTQ_nonneg vZ)
  have kR := cR.majD2_le aTQ_nonneg hb vR
  have kZ := cZ.majD2_le aTQ_nonneg hb vZ
  exact ⟨by linarith [mu_C2R], by linarith [mu_C2Z]⟩

/-- **The three node conditions over the cell** at every bound `0 ≤ a ≤ aTQ`, `|λ| ≤ λ₁`. -/
theorem mu_node_bounds {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) : PolyExpr.maj a EpP < 1 ∧ PolyExpr.maj a E4P < 1 ∧
      |lm| * PolyExprS.maj a eBm < 1 := by
  have hE : PolyExpr.maj a EpP < 1 := ((PolyExpr.maj_mono ha haa EpP).trans mu_maj_E).trans_lt
    (by exact_mod_cast (show mEQ < 1 by kernel_fact))
  have hE4 : PolyExpr.maj a E4P < 1 := ((PolyExpr.maj_mono ha haa E4P).trans mu_maj_E4).trans_lt
    (by exact_mod_cast (show mE4Q < 1 by kernel_fact))
  have hBv := valid_of_nodesOK nodesOK_eBm
  have hB : PolyExprS.maj a eBm ≤ (mQQ : ℝ) * gQ * gQ :=
    (PolyExprS.maj_mono ha haa hBv).trans maj_eBm_le
  refine ⟨hE, hE4, ?_⟩
  have h := (show @LAMQ@ * (mQQ * gQ * gQ) ≤ mNQ by kernel_fact)
  have h' : ((@LAMQ@ * (mQQ * gQ * gQ) : ℚ) : ℝ) ≤ (mNQ : ℝ) := by exact_mod_cast h
  have h1 : (mNQ : ℝ) < 1 := by exact_mod_cast (show mNQ < 1 by kernel_fact)
  push_cast at h'
  have h0 := PolyExprS.maj_nonneg ha eBm
  have hl : |lm| ≤ @LAMR@ := hlm
  nlinarith [abs_nonneg lm]

/-- **Validity over the cell**: all expressions of `gcFlowMu (1/256) λ` and its residuals are valid
at every bound `0 ≤ a ≤ aTQ`, `|λ| ≤ λ₁`. -/
theorem mu_valid_cell {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) :
    (gcFlowMu (1 / 256) lm).Valid6 a ∧ PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resRp ∧
      PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resZp := by
  obtain ⟨hE, hE4, hN⟩ := mu_node_bounds ha haa hlm
  exact gcFlowMu_valid _ lm a hE hE4 hN

end PlasmaLean.Design.RationalStellaratorGCMu
'''
    rep = {'@LAM@': '%d/%d' % (lamn, lamd), '@LAMR@': '%d / %d' % (lamn, lamd),
           '@LAMQ@': '(%d / %d : ℚ)' % (lamn, lamd), '@E4L@': leaf_int_list('E4P'),
           '@QL@': leaf_int_list('QPP4P'), '@SQ@': str(sQ), '@ATQ@': vec(C['aTQ']),
           '@MVQ@': vec(C['mvec']), '@MEQ@': ql(C['mE']), '@ME4Q@': ql(C['mE4']), '@MQQ@': ql(C['mQQ']),
           '@MNQ@': ql(C['mN']), '@GQ@': ql(C['g']), '@C2Q@': ql(C['C2']), '@C2@': '%.4g' % float(C['C2'])}
    for k, v in rep.items():
        txt = txt.replace(k, v)
    open(ROOT + 'RationalStellaratorGCMuMaj.lean', 'w').write(txt)


if __name__ == '__main__':
    emit_lean(CONST)
    print('lean ok')
