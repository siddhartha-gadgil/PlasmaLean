"""Final data generator: mirrors the Lean functions of RationalStellaratorCover / Confined exactly
(at the level of coefficient values)."""
import sys, pickle, json
from fractions import Fraction as Fr
from math import comb
import dense
from dense import shift_ax, truncate_total, deg_ax, abs_sum, const, upper, lower, absup
from plan import Searcher
from poly import reduce_circle, I_poly, field_polys
sys.setrecursionlimit(100000)

E = 40
# ---------------------------------------------------------------- sparse data
def load_P(fitfile):
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    Pi = {e: int(round(v * 2**E)) for e, v in P.items()}
    return [(v, list(e)) for e, v in sorted(Pi.items()) if v != 0]

def G4():
    G, N, Nt = field_polys(Fr(1, 4), Fr(1))
    out = []
    for g in G:
        out.append([(int(4*v), list(e)) for e, v in sorted(g.items())])
    return out

J2 = [(2, [2, 0, 0, 0]), (2, [0, 2, 0, 0]), (1, [0, 2, 0, 1]), (-1, [2, 0, 0, 1]), (2, [1, 1, 1, 0])]

# ---------------------------------------------------------------- dense (values)
def zipL(f, a, b):
    out = []
    n = max(len(a), len(b))
    for i in range(n):
        if i < len(a) and i < len(b): out.append(f(a[i], b[i]))
        elif i < len(a): out.append(a[i])
        else: out.append(b[i])
    return out
def add1(a, b): return zipL(lambda x, y: x + y, a, b)
def add2(a, b): return zipL(add1, a, b)
def add3(a, b): return zipL(add2, a, b)
def neg1(a): return [-x for x in a]
def neg2(a): return [neg1(f) for f in a]
def neg3(a): return [neg2(B) for B in a]
def smul1(k, a): return [k*x for x in a]
def mul1(a, b):
    if not a: return []
    return add1(smul1(a[0], b), [0] + mul1(a[1:], b))
def mul2(a, b):
    if not a: return []
    return add2([mul1(a[0], f) for f in b], [[]] + mul2(a[1:], b))
def mul3(a, b):
    if not a: return []
    return add3([mul2(a[0], B) for B in b], [[]] + mul3(a[1:], b))
def onePlusSq(d):
    r = [1]
    for _ in range(d): r = mul1([1, 0, 1], r)
    return r
def tbasis(a, b, d):
    """(1-t^2)^a (2t)^b (1+t^2)^(d-a-b)"""
    r = [1]
    for _ in range(a): r = mul1([1, 0, -1], r)
    for _ in range(b): r = mul1([0, 2], r)
    for _ in range(d - a - b): r = mul1([1, 0, 1], r)
    return r
def getD(e, i): return e[i] if i < len(e) else 0
def place(j, k, f):
    return [[] for _ in range(j)] + [[[] for _ in range(k)] + [f]]
def chartD(d, sg, p):
    acc = []
    for c, e in p:
        a, b = getD(e, 2), getD(e, 3)
        assert a + b <= d
        s = sg**(a+b)
        acc = add3(acc, place(getD(e, 0), getD(e, 1), smul1(c*s, tbasis(a, b, d))))
    return acc
def pderivZ(p, i):
    out = []
    for c, e in p:
        k = getD(e, i)
        if k != 0:
            f = list(e); f[i] -= 1
            out.append((c*k, f))
    return out
def scaleL(q, d, l, sm):
    return [sm(q**(d - j), x) for j, x in enumerate(l)]
def scale0(q, d, A): return scaleL(q, d, A, lambda k, B: [smul1(k, f) for f in B])
def scale1(q, d, A): return [scaleL(q, d, B, lambda k, f: smul1(k, f)) for B in A]
def evalAt0(pos, A):
    acc = []
    for B in reversed(A):
        acc = add2(B, acc if pos else neg2(acc))
    return acc
def evalAt1(pos, B):
    acc = []
    for f in reversed(B):
        acc = add1(f, acc if pos else neg1(acc))
    return acc
def restrict(ax, pos, A):
    if ax == 0: return [evalAt0(pos, A)]
    return [[evalAt1(pos, B)] for B in A]

def mainRoot(P, sg=1):
    G = G4()
    dI = max(getD(e, 2) + getD(e, 3) for c, e in P)
    ds = [dI, dI, dI - 1, dI - 1]; es = [1, 1, 2, 2]
    X = [mul3(chartD(ds[i], sg, pderivZ(P, i)), chartD(es[i], sg, G[i])) for i in range(4)]
    return add3(add3(X[0], X[1]), add3(X[2], X[3])), dI + 1

def degs(A):
    return (len(A) - 1, max((len(B) for B in A), default=0) - 1, max((len(f) for B in A for f in B), default=0) - 1)

def trim(A):
    out = []
    for B in A:
        nB = []
        for f in B:
            g = list(f)
            while g and g[-1] == 0: g.pop()
            nB.append(g)
        while nB and not nB[-1]: nB.pop()
        out.append(nB)
    while out and not out[-1]: out.pop()
    return out

def d3_str(A):
    return " | ".join(" ; ".join(" ".join(str(x) for x in f) for f in B) for B in A)
def fpoly_str(p):
    return ";\n".join(f"{c} {' '.join(map(str, e))}" for c, e in p)

# ---------------------------------------------------------------- plans
def parse_plan(s, i=0):
    c = s[i]
    if c == 'L': return ('L',), i + 1
    if c == 'D':
        j = i + 1
        while s[j].isdigit(): j += 1
        sub, k = parse_plan(s, j)
        return ('D', int(s[i+1:j]), sub), k
    if c == 'E':
        j = i + 1
        while j < len(s) and s[j].isdigit(): j += 1
        return ('E', int(s[i+1:j])), j
    l, k = parse_plan(s, i + 1)
    r, k = parse_plan(s, k)
    return ('S', 'SZT'.index(c), l, r), k
def plan_str(t):
    if t[0] == 'L': return 'L'
    if t[0] == 'E': return f'E{t[1]}'
    if t[0] == 'D': return f'D{t[1]}' + plan_str(t[2])
    return 'SZT'[t[1]] + plan_str(t[2]) + plan_str(t[3])
def checkpoint(tree, A, D, rem, dd, depth, cps):
    """replace subtrees at split-depth `depth` by ext nodes; record (A, D, rem, subplan)."""
    if tree[0] == 'L': return tree
    if depth == 0:
        cps.append((A, D, rem, plan_str(tree)))
        return ('E', len(cps) - 1)
    if tree[0] == 'D':
        A2, r2 = truncate_total(A, tree[1])
        return ('D', tree[1], checkpoint(tree[2], A2, D, rem + r2, dd, depth, cps))
    ax = tree[1]; d = dd[ax]
    l = checkpoint(tree[2], shift_ax(A, ax, -1, d), shift_ax(D, ax, -1, d), rem << d, dd, depth - 1, cps)
    r = checkpoint(tree[3], shift_ax(A, ax, 1, d), shift_ax(D, ax, 1, d), rem << d, dd, depth - 1, cps)
    return ('S', ax, l, r)
