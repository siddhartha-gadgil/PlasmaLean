"""UNTRUSTED (energy window, ew_majlib.py): the rational majorant mirrors of lam_maj.py (trees, mQ, mDQ,
mD2Q, node_bounds) as a library, reading the Lean sources relative to this file.

Original description: constants of the KAM step for the mu > 0 passing guiding-centre torus FAMILY
(rho0 = 1/256, lam in [0, LAM1], iota_A, gamma = 0.0687), uniform over the cell (field majorants at
the largest lam = LAM1), and the Lean file PlasmaLean/Design/RationalStellaratorGCMuMaj.lean:
computable mirrors of the expression trees of gcFlowMu (1/256) LAM1, node validity (three nodes,
one uniform bound g), the Taylor constant C2, and uniformity in lam (ConstLe).
Adapted from fam_maj.py.  Usage: python lam_maj.py"""
import sys, os, re, pickle, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
import gcmodel as G
import fam_ball  # noqa: F401  (pickle classes)
from fam_ball import decode_slice

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'PlasmaLean', 'Design') + '/'
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


