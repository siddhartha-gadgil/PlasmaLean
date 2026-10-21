"""UNTRUSTED: build expression trees (KronExpr.Ex) from sympy expressions in pipeline variables,
homogenized with t (weight (1,0,0)) and V (weight (0,1,0))."""
import sympy as sp
from fractions import Fraction as Fr
from functools import reduce


def lcd2(coeffs):
    k = 0
    for c in coeffs:
        q = sp.Rational(c).q
        assert q & (q - 1) == 0, ('non-dyadic coefficient', c)
        k = max(k, q.bit_length() - 1)
    return k


def mk_prod(fs):
    if not fs:
        return None
    t = fs[-1]
    for f in reversed(fs[:-1]):
        t = ('mul', f, t)
    return t


def mk_sum(terms):
    # terms: list of (sign, tree)
    t = None
    for sg, tr in terms:
        if t is None:
            t = tr if sg > 0 else ('sub', ('cst', 0), tr)
        else:
            t = ('add', t, tr) if sg > 0 else ('sub', t, tr)
    return t


def to_tree(expr, symvar, W, tvar, Vvar, scale=1):
    """expr: sympy polynomial in the symbols of symvar (symbol -> var index).
    Returns (tree, c) with eval(tree) = c * expr (honest values; t = V = 1), c = scale * 2^k."""
    syms = list(symvar.keys())
    P = sp.Poly(sp.expand(expr), *syms)
    k = lcd2(P.coeffs())
    c = scale * 2 ** k
    monos = []
    for mon, co in P.terms():
        ci = sp.Rational(co) * c
        assert ci.q == 1
        vs = []
        for s_, e_ in zip(syms, mon):
            vs += [symvar[s_]] * e_
        d = sum(W[v][0] for v in vs)
        ev = sum(W[v][1] for v in vs)
        p = sum(W[v][2] for v in vs) % 4
        monos.append((int(ci), vs, d, ev, p))
    if all(m[0] < 0 for m in monos):
        monos = [(-m[0],) + m[1:] for m in monos]
        c = -c
    dmax = max(m[2] for m in monos)
    emax = max(m[3] for m in monos)
    par = set(m[4] % 2 for m in monos)
    assert len(par) == 1, 'phase parity mismatch'
    terms = []
    for ci, vs, d, ev, p in monos:
        vs2 = vs + [tvar] * (dmax - d) + [Vvar] * (emax - ev)
        fs = [('var', v) for v in vs2]
        if abs(ci) != 1:
            fs = [('cst', abs(ci))] + fs
        tr = mk_prod(fs)
        if tr is None:
            raise ValueError('constant monomial without t')
        terms.append((1 if ci > 0 else -1, tr))
    # put a positive term first if possible (avoid 0 - x)
    terms.sort(key=lambda t: -t[0])
    return mk_sum(terms), c


def tree_str(e, names=None):
    k = e[0]
    if k == 'var':
        return 'v %d' % e[1]
    if k == 'cst':
        return 'k %d' % e[1]
    return '%s (%s) (%s)' % ({'add': 'a', 'sub': 's', 'mul': 'm'}[k], tree_str(e[1]), tree_str(e[2]))
