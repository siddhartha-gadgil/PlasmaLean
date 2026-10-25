"""UNTRUSTED: constants of the KAM step for the v_par < 0 guiding-centre torus (rho = -1/256, iota_B,
gamma = 0.0673) and the Lean file PlasmaLean/Design/RationalStellaratorGCNegTorusMaj.lean (a copy of
gc_maj.py; the leaf mirrors are reused from RationalStellaratorGCTorusMaj): computable mirrors (Theory/KAM/PolyExprSMajQ)
of the guiding-centre expression trees, node validity and the Taylor constant C2.
Usage: python neg_maj.py"""
import sys, os, re, pickle, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(__file__))
import gcmodel as G

ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
SRC = open(ROOT + 'KamNewtonField.lean').read() + open(ROOT + 'RationalStellaratorGCPoly.lean').read()


def parse_list(name):
    m = re.search(r'def %s : PolyExpr ℂ \(Fin 6\) := (mul \(const \(1 / 256\)\) \()?sumE \[(.*?)\]\)?\n' % name, SRC, re.S)
    scaled = m.group(1) is not None
    body = m.group(2)
    L = []
    for coef, mono in re.findall(r'monoE \(([^)]*)\) \[([^\]]*)\]', body):
        co = Fr(coef.replace(' ', ''))
        ms = [(int(i), int(k)) for i, k in re.findall(r'\((\d), (\d+)\)', mono)]
        L.append((co, ms))
    return scaled, L


LEAVES = ['Dp', 'nRp', 'nZp', 'DuP', 'DzP', 'DphP', 'nRuP', 'nRzP', 'nRphP', 'nZuP', 'nZzP', 'nZphP', 'PuP', 'EpP']
LL = {n: parse_list(n) for n in LEAVES}
assert LL['EpP'][0] and len(LL['EpP'][1]) == 275

# ----------------------------------------------------------- PQS trees in python
# ('c', q) ('v', i) ('a', p, q) ('s', p, q) ('m', p, q) ('n', c, d)


def npowQ(p, k):
    t = ('c', Fr(1))
    for _ in range(k):
        t = ('m', t, p)
    return t


def monoQ(c, ms):
    t = ('c', c)
    for (i, k) in reversed(ms):
        pass
    # monoE c ((i,k)::l) = mul (monoE c l) (npow (var i) k): first element outermost
    def rec(l):
        if not l:
            return ('c', c)
        (i, k) = l[0]
        return ('m', rec(l[1:]), npowQ(('v', i), k))
    return rec(ms)


def sumQ(ts):
    if not ts:
        return ('c', Fr(0))
    return ('a', ts[0], sumQ(ts[1:]))


def leafQ(n):
    scaled, L = LL[n]
    t = sumQ([monoQ(c, ms) for c, ms in L])
    if scaled:
        t = ('m', ('c', Fr(1, 256)), t)
    return t


LEAFQ = {n: leafQ(n) for n in LEAVES}
EpQ = LEAFQ['EpP']


def gtree(t):
    k = t[0]
    if k == 'const':
        v = t[1]
        return ('c', Fr(1, 256) if v == 'rho' else Fr(1, 2) if v == 'half' else Fr(v))
    if k == 'var':
        return ('v', t[1])
    if k in ('add', 'sub', 'mul'):
        return ({'add': 'a', 'sub': 's', 'mul': 'm'}[k], gtree(t[1]), gtree(t[2]))
    if k == 'poly':
        return LEAFQ[t[1]]
    if k == 'node':
        return ('n', Fr(1), EpQ)
    if k == 'ref':
        return gtree(t[2])


TQ = {k: gtree(G.TREES[k]) for k in ['gcD', 'gcNR', 'gcNZ']}


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


def gbound(m):
    g = up(Fr(1 / math.sqrt(1 - float(m))) * Fr(1000001, 1000000), 6)
    assert g * g * (1 - m) >= 1
    return g


# ----------------------------------------------------------- the constants
D = pickle.load(open('/tmp/gcwn/gc_cert.pkl', 'rb'))
H, L = D['H'], D['L']
nmH = {v: k for k, v in H['names'].items()}
nmL = {v: k for k, v in L['names'].items()}
MU = Fr(1, 10 ** 12)
rA = Fr(1257, 10000)
d0 = rA / 7
e0 = up(max(D['e0']), 2)
assert e0 >= max(D['e0'])
print('e0 = %s' % e0)
ac = Fr(74315, 2 ** 16)
BH, EH, BL, EL = H['B'], H['E'], L['B'], L['E']
au0, az0 = BH[nmH['U']], BH[nmH['Z']]
aRt0, azt0 = BH[nmH['thU']], BH[nmH['thZ']]
aLR0 = up((BH[nmH['LRx']] + EH[nmH['LRx']]) / 2 ** 96, 4)
aLz0 = up((BH[nmH['LZx']] + EH[nmH['LZx']]) / 2 ** 96, 4)
au, az, aRt, azt, aLR, aLz = (x + MU for x in (au0, az0, aRt0, azt0, aLR0, aLz0))
fb = {}
for n in ['Dt', 'Dtu', 'Dtz', 'nRt', 'nRtu', 'nRtz', 'nZt', 'nZtu', 'nZtz']:
    i = nmL[n]
    fb[n] = up(BL[i] + EL[i], 5)
norms = {r['meta']['name']: r for r in L['norms']}
RDd = up(norms['Ddev']['rad'], 4)
RWd = up(norms['Wdev']['rad'], 4)
RX = up(norms['X']['rad'], 3)
dD = RDd / abs(norms['Ddev']['cscale'])
dW = RWd / abs(norms['Wdev']['cscale'])
dc0, wc0 = D['d0'], D['w0']
sD = up(1 / (dc0 - dD), 5)
sW = up(1 / (abs(wc0) - dW), 5)
sR = 1 / (1 - au)
vY = nmL['Y']
YB = BL[vY] + EL[vY]
tT = up(YB / (1 - RX), 5)
Ym = D['Ymean']
tau = down(abs(Ym) - EL[vY] - YB * RX / (1 - RX), 3)
print('au %s az %s aRt %s azt %s aLR %s aLz %s' % tuple(float(x) for x in (au, az, aRt, azt, aLR, aLz)))
print('fields', {k: float(v) for k, v in fb.items()})
print('sD %.5f sW %.3f sR %.5f tT %.4f tau %.4f' % (sD, sW, sR, tT, tau))
gam, E1 = Fr(673, 10000), Fr(2718, 1000)
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
# node bound at aT
memo = {}
mE = mQ(aT, Fr(0), EpQ, memo)
mEb = up(mE, 4)
gT = gbound(mEb)
print('cK %.1f cL %.1f  maj E at aT %.4f g %s' % (cK, cL, mE, float(gT)))


def resQ(Dt, n, w):
    return ('s', ('m', Dt, ('v', w)), n)


resR = resQ(TQ['gcD'], TQ['gcNR'], 4)
resZ = resQ(TQ['gcD'], TQ['gcNZ'], 5)
C2R = mD2Q(aT, mvec, gT, resR, {}) / 2
C2Z = mD2Q(aT, mvec, gT, resZ, {}) / 2
C2 = up(max(C2R, C2Z), 3)
kap = fb['Dt'] * kRem * d0 + (fb['Dtu'] + fb['Dtz']) * cK * kE * d0 ** 2 + C2
small = 32 * kap * e0 / d0 ** 4
print('C2R %.4e C2Z %.4e C2 %.3e kap %.4e smallness %.4e' % (C2R, C2Z, C2, kap, small))
print('mu budgets: %.3e %.3e %.3e  (mu = %.1e)' % (2 * cK * e0 / d0 ** 2, 2 * (cK / E1) * e0 / d0 ** 3,
                                                  2 * cL * e0 / d0 ** 2, MU))
# validity at the admissibility bounds (strip torus bounds) and at avec + 2 mu mOne
aB = [au, az, ac, ac, Fr(0), Fr(0)]
print('maj E at avB %.4f' % mQ(aB, Fr(0), EpQ, {}))
CONST = dict(au0=au0, az0=az0, aRt0=aRt0, azt0=azt0, aLR0=aLR0, aLz0=aLz0, fb=fb, sD=sD, sW=sW, tT=tT, tau=tau,
             RDd=RDd, RWd=RWd, RX=RX, cKb=cKb, cLb=cLb, C2=C2, gT=gT, mEb=mEb, e0=e0, d0c=dc0, w0c=wc0)
pickle.dump(CONST, open('/tmp/gcwn/gc_const.pkl', 'wb'))

# ----------------------------------------------------------- the Lean file
HEADER = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''


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


def wrapl(text, indent=4, width=88):
    out, cur = [], ''
    for tok in text.split(' '):
        cand = (cur + ' ' + tok) if cur else tok
        if len(cand) + indent > width and cur:
            out.append(cur)
            cur = tok
        else:
            cur = cand
    out.append(cur)
    return ('\n' + ' ' * indent).join(out)


def leaf_list_lean(n):
    scaled, Lst = LL[n]
    items = []
    for c, ms in Lst:
        cs = ('%d' % c.numerator) if scaled else ql(c)
        items.append('(%s, [%s])' % (cs, ', '.join('(%d, %d)' % m for m in ms)))
    return '[' + ', '.join(items) + ']'


LEANP = {'Dp': 'KamNewton.Dp', 'nRp': 'KamNewton.nRp', 'nZp': 'KamNewton.nZp'}


def tq(t):
    k = t[0]
    if k == 'const':
        v = t[1]
        if v == 'rho':
            return '.const (-1 / 256)'
        if v == 'half':
            return '.const (1 / 2)'
        return '.const (%d)' % v
    if k == 'var':
        return '.var %d' % t[1]
    if k in ('add', 'sub', 'mul'):
        return '.%s (%s) (%s)' % (k, tq(t[1]), tq(t[2]))
    if k == 'poly':
        return '%sQ' % t[1]
    if k == 'node':
        return 'eVQ'
    if k == 'ref':
        return '%sQ' % t[1]


def collect_refs(t, acc):
    if t[0] == 'ref':
        collect_refs(t[2], acc)
        if t[1] not in [a for a, _ in acc]:
            acc.append((t[1], t[2]))
    elif t[0] in ('add', 'sub', 'mul'):
        collect_refs(t[1], acc)
        collect_refs(t[2], acc)


refs = []
for k in ['gcD', 'gcNR', 'gcNZ']:
    collect_refs(G.TREES[k], refs)
out = [HEADER, '''public import PlasmaLean.Design.RationalStellaratorGCTorusMaj
public import PlasmaLean.Certificates.KernelFact

/-!
# Majorants of the `v∥ < 0` guiding-centre field: node validity and the Taylor constant

The computable mirrors (`Theory/KAM/PolyExprSMajQ`, `PQS`) of the expression trees of the
guiding-centre field `gcFlow (−1/256)` (`ρ_s = −1/256`), built from the leaf mirrors of
`Design/RationalStellaratorGCTorusMaj` (which do not depend on `ρ`), with their embeddings
(`*_toS`), and the two numerical facts of the KAM theorem that need majorants, at the bounds of the
`ι_B` torus:

* **node validity** (`gc_maj_E_*`): the majorant of the deviation `E` under the node is below `1`
  at the bounds used by the KAM step (`gcFlow_valid`);
* **the Taylor constant** (`gc_C2R`, `gc_C2Z`): `½ majD2(resR) ≤ C₂ = %s` at the
  Taylor segment bounds `avec + T_q mvec`.

The rational majorant comparisons are explicit proof terms (`kernel_fact`, whose leaves are
kernel facts). Generated by `scripts/gc_kam/neg_maj.py`.

**Sanity.** `gcDQ_toS`: the mirror embeds to the field expression `gcD (−1/256)`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM.PQS

''' % float(C2)]
leaflemmas = ', '.join('%sQ_toS' % n for n in LEAVES)
done = ['eVQ_toS'] + ['%sQ_toS' % name for name, t in refs]
for name in ['gcD', 'gcNR', 'gcNZ']:
    out.append('/-- The mirror of `%s (−1/256)`. -/\ndef %sQ : PQS (Fin 6) :=\n  %s\n\n' % (name, name, wrapl(tq(G.TREES[name]), 2)))
    out.append('set_option linter.unusedSimpArgs false in\nset_option maxRecDepth 100000 in\n/-- The mirror of `%s (−1/256)` embeds to it. -/\ntheorem %sQ_toS : %sQ.toS = %s (-1 / 256) := by\n'
               '  simp only [%s] <;> norm_num\n\n'
               % (name, name, name, name, wrapl('%sQ, toS, ' % name + leaflemmas + ', ' + ', '.join(done) + ', %s' % name, 14)))
out.append('''/-- The mirror of the `R`-residual expression. -/
def resRQ : PQS (Fin 6) := .sub (.mul gcDQ (.var 4)) gcNRQ

/-- The mirror of the `z`-residual expression. -/
def resZQ : PQS (Fin 6) := .sub (.mul gcDQ (.var 5)) gcNZQ

/-- The mirror of the `R`-residual embeds to it. -/
theorem resRQ_toS : resRQ.toS = (gcFlow (-1 / 256)).resRp := by
  simp only [resRQ, toS, gcDQ_toS, gcNRQ_toS]; rfl

/-- The mirror of the `z`-residual embeds to it. -/
theorem resZQ_toS : resZQ.toS = (gcFlow (-1 / 256)).resZp := by
  simp only [resZQ, toS, gcDQ_toS, gcNZQ_toS]; rfl

''')
open('/tmp/gcwn/maj_part1.lean', 'w').write(''.join(out))
print('ok part1')

# ----------------------------------------------------------- part 2: the numerical facts
aTQ = [au0 + Fr(2, 10 ** 11), az0 + Fr(2, 10 ** 11), ac, ac, aLR0 + Fr(2, 10 ** 11), aLz0 + Fr(2, 10 ** 11)]
assert all(aTQ[i] >= aT[i] for i in range(6))
mE2 = mQ(aTQ, Fr(0), EpQ, {})
mEb2 = up(mE2, 4)
gT2 = gbound(mEb2)
C2b = up(max(mD2Q(aTQ, mvec, gT2, resR, {}), mD2Q(aTQ, mvec, gT2, resZ, {})) / 2, 3)
print('at aTQ: maj E %.5f (bound %s) g %s C2 %.4e' % (mE2, mEb2, gT2, C2b))
vec = lambda xs: '\n  ![' + ',\n    '.join(ql(x) for x in xs) + ']'
p2 = '''/-- Rational upper bounds of the torus variables on the Taylor segments (`avec + T_q mvec`, and the
admissible tori). -/
def aTQ : Fin 6 → ℚ := %s

/-- The perturbation profile `(c_K, c_K, 0, 0, c_L, c_L)`. -/
def mvQ : Fin 6 → ℚ := %s

/-- The bound of the node majorant. -/
def mEQ : ℚ := %s

/-- The bound of `(1 − m)^{−1/2}`. -/
def gQ : ℚ := %s

/-- The Taylor constant. -/
def C2Q : ℚ := %s

set_option maxRecDepth 100000 in
/-- **The node majorant at `aTQ`**: `maj E ≤ %s`. -/
theorem gc_maj_E_aTQ : PolyExpr.maj (fun i => (aTQ i : ℝ)) EpP ≤ (mEQ : ℝ) := by
  rw [← PolyExprS.maj_ofPoly, ← EpPQ_toS]
  refine (maj_le (a := aTQ) (g := 0) (by kernel_fact) le_rfl EpPQ (nodesOK_EpPQ _ _)).trans ?_
  exact_mod_cast (show mQ aTQ 0 EpPQ ≤ mEQ by kernel_fact)

/-- **Node validity** at every bound below `aTQ`. -/
theorem gc_maj_E_lt {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) :
    PolyExpr.maj a EpP < 1 := by
  refine ((PolyExpr.maj_mono ha haa EpP).trans gc_maj_E_aTQ).trans_lt ?_
  exact_mod_cast (show mEQ < 1 by kernel_fact)

set_option maxRecDepth 100000 in
/-- All nodes of the residual trees are the node `(1 + E)^{−1/2}`. -/
theorem allNodes_res : allNodes EpPQ resRQ = true ∧ allNodes EpPQ resZQ = true := by
  constructor <;> kernel_fact

/-- The node condition on the residual trees at `aTQ`. -/
theorem nodesOK_res {e : PQS (Fin 6)} (he : allNodes EpPQ e = true) :
    NodesOK (fun i => (aTQ i : ℝ)) (gQ : ℝ) e.toS := by
  have hm := gc_maj_E_aTQ
  rw [← PolyExprS.maj_ofPoly, ← EpPQ_toS] at hm
  refine nodesOK_of_all (nodesOK_EpPQ _ _) (hm.trans_lt ?_) ?_ e he
  · exact_mod_cast (show mEQ < 1 by kernel_fact)
  · refine isqG_le_q hm (by exact_mod_cast (show mEQ < 1 by kernel_fact))
      (by exact_mod_cast (show (0 : ℚ) ≤ gQ by kernel_fact))
      (by exact_mod_cast (show 1 ≤ gQ ^ 2 * (1 - mEQ) by kernel_fact))

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `R`-residual** at every bound below `aTQ`. -/
theorem gc_C2R {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlow (-1 / 256)).resRp / 2 ≤ (C2Q : ℝ) := by
  rw [← resRQ_toS]
  have hN := nodesOK_res allNodes_res.1
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by kernel_fact) i
    exact_mod_cast this
  have h1 := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb
    haa (fun _ => le_rfl) (valid_of_nodesOK hN)
  have h2 := majD2_le (a := aTQ) (b := mvQ) (g := gQ) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) resRQ hN
  have h3 : (mD2Q aTQ mvQ gQ resRQ : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show mD2Q aTQ mvQ gQ resRQ / 2 ≤ C2Q by kernel_fact)
  linarith

set_option maxRecDepth 100000 in
/-- **The Taylor constant of the `z`-residual** at every bound below `aTQ`. -/
theorem gc_C2Z {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) :
    PolyExprS.majD2 a (fun i => (mvQ i : ℝ)) (gcFlow (-1 / 256)).resZp / 2 ≤ (C2Q : ℝ) := by
  rw [← resZQ_toS]
  have hN := nodesOK_res allNodes_res.2
  have hb : ∀ i, (0 : ℝ) ≤ (mvQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ mvQ i by kernel_fact) i
    exact_mod_cast this
  have h1 := PolyExprS.majD2_mono (b := fun i => (mvQ i : ℝ)) (b' := fun i => (mvQ i : ℝ)) ha hb
    haa (fun _ => le_rfl) (valid_of_nodesOK hN)
  have h2 := majD2_le (a := aTQ) (b := mvQ) (g := gQ) (by kernel_fact) (by kernel_fact)
    (by kernel_fact) resZQ hN
  have h3 : (mD2Q aTQ mvQ gQ resZQ : ℝ) / 2 ≤ C2Q := by
    exact_mod_cast (show mD2Q aTQ mvQ gQ resZQ / 2 ≤ C2Q by kernel_fact)
  linarith

/-- The residual expressions are valid at every bound below `aTQ`. -/
theorem gc_valid_res {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aTQ i) :
    PolyExprS.Valid a (gcFlow (-1 / 256)).resRp ∧ PolyExprS.Valid a (gcFlow (-1 / 256)).resZp :=
  ⟨(gcFlow_valid _ a (gc_maj_E_lt ha haa)).2.1, (gcFlow_valid _ a (gc_maj_E_lt ha haa)).2.2⟩

''' % (vec(aTQ), vec(mvec), ql(mEb2), ql(gT2), ql(C2b), float(mEb2))
CONST.update(dict(aTQ=aTQ, mEQ=mEb2, gQ=gT2, C2Q=C2b))
for P_ in ['H', 'L']:
    for r_ in D[P_]['norms']:
        CONST['R_' + r_['meta']['name']] = up(r_['rad'], 4)
pickle.dump(CONST, open('/tmp/gcwn/gc_const.pkl', 'wb'))
open('/tmp/gcwn/maj_part2.lean', 'w').write(p2)
print('ok part2')
