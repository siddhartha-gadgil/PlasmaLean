"""UNTRUSTED (lamcell shim: a copy of scripts/gc_kam/gcmodel.py reading the Lean source relative to the
repository). Model of the guiding-centre flow-form expressions (PolyExprS trees) of
Design/RationalStellaratorGCFlow.lean, their atom-level evaluation, and linear_combination
certificates for the identities divFree / flux_a / flux_b / flux_c.

Atoms (FA elements at the torus point xB u z):
  U Z C S        u, z, cos 2phi, sin 2phi
  rA hA          algebraMap rho, algebraMap (1/2)
  V              the node (1 + E)^(-1/2)
  N_v, N_d{i}    value and partial derivatives (i = 0..3) of the polynomial leaf N
"""
import re, sympy as sp
import os as _os
__lamcell__ = True

U, Z, C, S, rA, hA, V = sp.symbols('U Z C S rA hA V')
u, z, c, s = sp.symbols('u z c s')

# ---------------- base polynomials (parsed from KamNewtonField.lean) ----------------
def parse_lean_poly(src, name):
    m = re.search(r'def %s : PolyExpr ℂ \(Fin 6\) := sumE \[(.*?)\]\n\n' % name, src, re.S)
    body = m.group(1)
    tot = 0
    for coef, mono in re.findall(r'monoE \(([^)]*)\) \[([^\]]*)\]', body):
        co = sp.Rational(coef.replace(' ', ''))
        t = co
        for i, k in re.findall(r'\((\d), (\d+)\)', mono):
            t *= [u, z, c, s][int(i)] ** int(k)
        tot += t
    return sp.expand(tot)

SRC = open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), '..', '..', '..', '..', 'PlasmaLean', 'Design', 'KamNewtonField.lean')).read()
BASE = {n: parse_lean_poly(SRC, n) for n in ['Dp', 'nRp', 'nZp', 'Pap', 'Pbp']}
R_ = 1 + u
def phiP(e): return sp.expand(sp.diff(e, c) * (-2 * s) + sp.diff(e, s) * (2 * c))

PNEW = {}
for b in ['Dp', 'nRp', 'nZp']:
    PNEW[b[:-1] + 'uP'] = sp.expand(sp.diff(BASE[b], u))
    PNEW[b[:-1] + 'zP'] = sp.expand(sp.diff(BASE[b], z))
    PNEW[b[:-1] + 'phP'] = phiP(BASE[b])
NP = 6
PNEW['PuP'] = sp.expand(sum((-1) ** n * sp.binomial(n + 2, 2) * u ** n for n in range(NP + 1)))
qpoly = sp.expand(BASE['nRp'] ** 2 + R_ ** 2 * BASE['Dp'] ** 2 + BASE['nZp'] ** 2)
PNEW['EpP'] = sp.expand(qpoly * PNEW['PuP'] ** 2 - 1)
ALLP = dict(BASE); ALLP.update(PNEW)

# ---------------- trees ----------------
def const(k): return ('const', k)
def var(i): return ('var', i)
def add(a, b): return ('add', a, b)
def sub(a, b): return ('sub', a, b)
def mul(*xs):
    t = xs[-1]
    for x in reversed(xs[:-1]):
        t = ('mul', x, t)
    return t
def leaf(n): return ('poly', n)
def suml(*xs):
    t = xs[-1]
    for x in reversed(xs[:-1]):
        t = ('add', x, t)
    return t

eR = ('ref', 'eR', add(const(1), var(0)))
eD, enR, enZ = leaf('Dp'), leaf('nRp'), leaf('nZp')
eq = ('ref', 'eq', suml(mul(enR, enR), mul(eR, eR, eD, eD), mul(enZ, enZ)))
eqR = ('ref', 'eqR', suml(mul(const(2), enR, leaf('nRuP')), mul(const(2), eR, eD, eD),
                          mul(const(2), eR, eR, eD, leaf('DuP')), mul(const(2), enZ, leaf('nZuP'))))
eqz = ('ref', 'eqz', suml(mul(const(2), enR, leaf('nRzP')), mul(const(2), eR, eR, eD, leaf('DzP')),
                          mul(const(2), enZ, leaf('nZzP'))))
eqph = ('ref', 'eqph', suml(mul(const(2), enR, leaf('nRphP')), mul(const(2), eR, eR, eD, leaf('DphP')),
                            mul(const(2), enZ, leaf('nZphP'))))
eV = ('node', 'eV')                    # isqrt 1 (ofPoly EpP)
eW = ('ref', 'eW', mul(leaf('PuP'), eV))
eW3 = ('ref', 'eW3', mul(eW, eW, eW))
def corr(t): return mul(const('rho'), const('half'), eW3, t)
eKD = ('ref', 'eKD', mul(eR, eR, sub(sub(mul(eR, enZ, eqR), mul(const(8), enZ, eq)), mul(eR, enR, eqz))))
eKR = ('ref', 'eKR', sub(mul(eR, eR, eR, eR, eR, eD, eqz), mul(eR, eR, eR, enZ, eqph)))
eKZ = ('ref', 'eKZ', add(sub(mul(eR, eR, eR, enR, eqph), mul(eR, eR, eR, eR, eR, eD, eqR)),
                         mul(const(8), eR, eR, eR, eR, eD, eq)))
gcD = add(eD, corr(eKD))
gcNR = add(enR, corr(eKR))
gcNZ = add(enZ, corr(eKZ))
gcPa = sub(leaf('Pap'), mul(const('rho'), eR, eW, enR))
gcPb = sub(leaf('Pbp'), mul(const('rho'), eR, eR, eW, enZ))
gcPc = sub(const(0), mul(const('rho'), eR, eR, eW, eD))
TREES = {'gcD': gcD, 'gcNR': gcNR, 'gcNZ': gcNZ, 'gcPa': gcPa, 'gcPb': gcPb, 'gcPc': gcPc}

# ---------------- atom-level semantics ----------------
XV = [U, Z, C, S]
def cval(k):
    return {'rho': rA, 'half': hA}.get(k, k)
def ev(t):
    k = t[0]
    if k == 'const': return cval(t[1])
    if k == 'var': return XV[t[1]]
    if k == 'add': return ev(t[1]) + ev(t[2])
    if k == 'sub': return ev(t[1]) - ev(t[2])
    if k == 'mul': return ev(t[1]) * ev(t[2])
    if k == 'poly': return sp.Symbol(t[1] + '_v')
    if k == 'node': return V
    if k == 'ref': return ev(t[2])
def dv(t, i):
    k = t[0]
    if k == 'const': return 0
    if k == 'var': return (1 if t[1] == i else 0) if i != 'ph' else {2: -2 * S, 3: 2 * C}.get(t[1], 0)
    if k == 'add': return dv(t[1], i) + dv(t[2], i)
    if k == 'sub': return dv(t[1], i) - dv(t[2], i)
    if k == 'mul': return dv(t[1], i) * ev(t[2]) + ev(t[1]) * dv(t[2], i)
    if k == 'poly': return sp.Symbol(t[1] + '_d%s' % i)
    if k == 'node': return -(hA * V ** 3) * sp.Symbol('EpP_d%s' % i)
    if k == 'ref': return dv(t[2], i)
def phi(t): return dv(t, 'ph')

def A(n, i=None): return sp.Symbol(n + ('_v' if i is None else '_d%s' % i))
Rv = 1 + U

# ---------------- relations (name -> polynomial that equals 0) ----------------
REL = {}
REL['half'] = 2 * hA - 1
REL['V'] = V ** 2 * (1 + A('EpP')) - 1
def phiA(n): return A(n, 'ph')
for b in ['D', 'nR', 'nZ']:
    REL[b + '_d0'] = A(b + 'p', 0) - A(b + 'uP')
    REL[b + '_d1'] = A(b + 'p', 1) - A(b + 'zP')
    REL[b + '_ph'] = phiA(b + 'p') - A(b + 'phP')
    REL[b + '_uz'] = A(b + 'uP', 1) - A(b + 'zP', 0)
    REL[b + '_uph'] = phiA(b + 'uP') - A(b + 'phP', 0)
    REL[b + '_zph'] = phiA(b + 'zP') - A(b + 'phP', 1)
REL['divB'] = Rv * A('Dp', 'ph') - 3 * A('nRp') + Rv * A('nRp', 0) + Rv * A('nZp', 1)
REL['curl1'] = Rv * A('nRzP') - Rv * A('nZuP') + 4 * A('nZp')
REL['curl2'] = A('nZphP') - Rv ** 2 * A('DzP')
REL['curl3'] = Rv ** 2 * A('DuP') - 2 * Rv * A('Dp') - A('nRphP')
qA = A('nRp') ** 2 + Rv ** 2 * A('Dp') ** 2 + A('nZp') ** 2
REL['E'] = A('EpP') - (qA * A('PuP') ** 2 - 1)
for i in [0, 1, 'ph']:
    dq = 2 * A('nRp') * A('nRp', i) + 2 * Rv ** 2 * A('Dp') * A('Dp', i) + 2 * A('nZp') * A('nZp', i)
    if i == 0: dq += 2 * Rv * A('Dp') ** 2
    REL['E_d%s' % i] = A('EpP', i) - (dq * A('PuP') ** 2 + 2 * qA * A('PuP') * A('PuP', i))
for i in [1, 'ph']:
    REL['P_d%s' % i] = A('PuP', i)
REL['fa'] = Rv * A('Pbp', 0) - 2 * A('Pbp') - Rv ** 2 * A('Pap', 1) - A('Dp')
REL['fb'] = Rv ** 2 * phiA('Pap') - A('nZp')
REL['fc'] = Rv * phiA('Pbp') + A('nRp')

# pivots: (relation, pivot atom), applied in order
PIV = [('half', hA)]
for b in ['D', 'nR', 'nZ']:
    PIV += [(b + '_d0', A(b + 'p', 0)), (b + '_d1', A(b + 'p', 1)), (b + '_ph', A(b + 'p', 'ph')),
            (b + '_uz', A(b + 'zP', 0)), (b + '_uph', A(b + 'phP', 0)), (b + '_zph', A(b + 'phP', 1))]
PIV += [('P_d1', A('PuP', 1)), ('P_dph', A('PuP', 'ph'))]
PIV += [('E_d%s' % i, A('EpP', i)) for i in [0, 1, 'ph']]
PIV += [('E', A('EpP'))]
PIV += [('curl2', A('nZphP')), ('curl3', A('nRphP')), ('curl1', A('nZp'))]

def certify(T, base=None, extra_piv=()):
    """Return dict rel -> coefficient with T == sum coef * REL[rel] (verified)."""
    coef = {}
    T = sp.expand(T)
    if base:
        for nm, k in base:
            coef[nm] = coef.get(nm, 0) + k
            T = sp.expand(T - k * REL[nm])
    # reduced relations, each tracked as (poly, {rel: coef})
    red = {}
    done = []
    for nm, p in list(PIV) + list(extra_piv):
        r = sp.expand(REL[nm]); rc = {nm: sp.Integer(1)}
        # reduce r by earlier pivots
        for nm2, p2 in done:
            r2, rc2 = red[nm2]
            if r.has(p2):
                a = sp.Poly(r2, p2).coeff_monomial(p2)
                rest = sp.expand(r2 - a * p2)
                rnew = sp.expand(r.subs(p2, -rest / a))
                q_, rem = sp.div(sp.expand(r - rnew), r2, p2)
                assert rem == 0
                for kk, vv in rc2.items():
                    rc[kk] = sp.expand(rc.get(kk, 0) - q_ * vv)
                r = rnew
        red[nm] = (r, rc)
        done.append((nm, p))
        if T.has(p):
            a = sp.Poly(r, p).coeff_monomial(p)
            assert not sp.expand(a).free_symbols, (nm, a)
            rest = sp.expand(r - a * p)
            Tnew = sp.expand(T.subs(p, -rest / a))
            q_, rem = sp.div(sp.expand(T - Tnew), r, p)
            assert rem == 0, nm
            for kk, vv in rc.items():
                coef[kk] = sp.expand(coef.get(kk, 0) + q_ * vv)
            T = Tnew
    # final: divide by reduced V relation
    rV, rcV = red['V'] if 'V' in red else (None, None)
    if T != 0:
        rV = sp.expand(REL['V'])
        rcV = {'V': sp.Integer(1)}
        for nm2, p2 in done:
            r2, rc2 = red[nm2]
            if rV.has(p2):
                a = sp.Poly(r2, p2).coeff_monomial(p2)
                rest = sp.expand(r2 - a * p2)
                rnew = sp.expand(rV.subs(p2, -rest / a))
                q_, rem = sp.div(sp.expand(rV - rnew), r2, p2)
                assert rem == 0
                for kk, vv in rc2.items():
                    rcV[kk] = sp.expand(rcV.get(kk, 0) - q_ * vv)
                rV = rnew
        gens = sorted(T.free_symbols | rV.free_symbols, key=str)
        gens.remove(V); gens = [V] + gens
        q_, rem = sp.div(sp.Poly(T, *gens), sp.Poly(rV, *gens))
        assert rem.is_zero, 'V-division failed'
        q_ = q_.as_expr()
        for kk, vv in rcV.items():
            coef[kk] = sp.expand(coef.get(kk, 0) + q_ * vv)
    return coef

def check(T, coef):
    tot = sp.expand(T - sum(v * REL[k] for k, v in coef.items()))
    return tot == 0

def targets():
    tD, tNR, tNZ, tPa, tPb, tPc = (TREES[k] for k in ['gcD', 'gcNR', 'gcNZ', 'gcPa', 'gcPb', 'gcPc'])
    T = {}
    T['divFree'] = (Rv * phi(tD) - 3 * ev(tNR) + Rv * dv(tNR, 0) + Rv * dv(tNZ, 1), [('divB', 1)])
    T['flux_a'] = (Rv * dv(tPb, 0) - 2 * ev(tPb) - Rv ** 2 * dv(tPa, 1) - ev(tD), [('fa', 1)])
    T['flux_b'] = (Rv ** 2 * phi(tPa) - Rv ** 3 * dv(tPc, 0) - ev(tNZ), [('fb', 1)])
    T['flux_c'] = (Rv * phi(tPb) - Rv ** 3 * dv(tPc, 1) + ev(tNR), [('fc', 1)])
    return T

if __name__ == '__main__':
    import time
    for nm, (T, base) in targets().items():
        t0 = time.time()
        co = certify(T, base)
        ok = check(T, co)
        sizes = {k: len(sp.Add.make_args(v)) for k, v in co.items() if v != 0}
        print(nm, ok, round(time.time() - t0, 1), 's', sizes)

# ---------------- variant: rewrite pivots, small certificate ----------------
KEEP = ['half', 'curl1']
def rewrite_map(names):
    """Oriented rewrite rules pivot -> replacement (fully reduced), in PIV order."""
    sub = {}
    rules = []
    for nm, p in PIV:
        if nm in KEEP or nm not in names: continue
        r = sp.expand(REL[nm])
        a = sp.Poly(r, p).coeff_monomial(p)
        assert a in (1, -1), (nm, a)
        repl = sp.expand(p - r / a)          # p = repl  (unreduced); p - repl = r / a
        rules.append((nm, p, repl, int(a)))
    return rules

def reduce_full(e, rules):
    e = sp.expand(e)
    for _ in range(10):
        new = e
        for nm, p, repl, _a in rules:
            new = sp.expand(new.subs(p, repl))
        if new == e: return e
        e = new
    return e

def certify2(T, base):
    names = set(REL)
    rules = rewrite_map(names)
    Tr = reduce_full(T, rules)
    keep = KEEP + ['V'] + [nm for nm, _ in base]
    RR = {k: reduce_full(REL[k], rules) for k in keep}
    coef = {}
    for nm, k in base:
        coef[nm] = sp.Integer(k)
        Tr = sp.expand(Tr - k * RR[nm])
    # pivots half (hA, coef 2), curl1 (nZp_v, coef 4)
    red = {}
    for nm, p in [('half', hA), ('curl1', A('nZp'))]:
        r = RR[nm]; a = sp.Poly(r, p).coeff_monomial(p)
        rest = sp.expand(r - a * p)
        if Tr.has(p):
            Tn = sp.expand(Tr.subs(p, -rest / a))
            q_, rem = sp.div(sp.expand(Tr - Tn), r, p)
            assert rem == 0
            coef[nm] = sp.expand(coef.get(nm, 0) + q_)
            Tr = Tn
        red[nm] = (p, rest, a)
    if Tr != 0:
        rV = RR['V']; rcV = {'V': sp.Integer(1)}
        for nm in ['half', 'curl1']:
            p, rest, a = red[nm]
            if rV.has(p):
                rn = sp.expand(rV.subs(p, -rest / a))
                q_, rem = sp.div(sp.expand(rV - rn), RR[nm], p)
                assert rem == 0
                rcV[nm] = sp.expand(rcV.get(nm, 0) - q_)
                rV = rn
        gens = sorted(Tr.free_symbols | rV.free_symbols, key=str)
        gens.remove(V); gens = [V] + gens
        q_, rem = sp.div(sp.Poly(Tr, *gens), sp.Poly(rV, *gens))
        assert rem.is_zero, 'V-division failed'
        q_ = q_.as_expr()
        for kk, vv in rcV.items():
            coef[kk] = sp.expand(coef.get(kk, 0) + q_ * vv)
    Tfull = reduce_full(T, rules)
    assert sp.expand(Tfull - sum(v * RR[k] for k, v in coef.items())) == 0
    return rules, RR, coef
