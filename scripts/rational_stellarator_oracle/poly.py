"""Sparse polynomials in (s, z, C, S) as dicts {(i,j,k,l): coeff}; exact (Fraction) or float."""
from fractions import Fraction as Fr
import numpy as np
from collections import defaultdict

NV = 4
def padd(*ps):
    r = defaultdict(lambda: 0)
    for p in ps:
        for e, c in p.items(): r[e] += c
    return {e: c for e, c in r.items() if c != 0}
def pscale(c, p): return {e: c*v for e, v in p.items() if c*v != 0}
def pmul(p, q):
    r = defaultdict(lambda: 0)
    for e, c in p.items():
        for f, d in q.items():
            r[tuple(a+b for a, b in zip(e, f))] += c*d
    return {e: c for e, c in r.items() if c != 0}
def pder(p, i):
    r = {}
    for e, c in p.items():
        if e[i] > 0:
            f = list(e); f[i] -= 1
            r[tuple(f)] = c*e[i]
    return r
def var(i, c=1):
    e = [0]*NV; e[i] = 1; return {tuple(e): c}
def cst(c): return {(0,)*NV: c} if c != 0 else {}
def ppow(p, n):
    r = cst(1)
    for _ in range(n): r = pmul(r, p)
    return r
def peval(p, x):
    return sum(c*np.prod([x[i]**e[i] for i in range(NV)], axis=0) for e, c in p.items())

def field_polys(eps, one=1):
    s, z, C, S = var(0, one), var(1, one), var(2, one), var(3, one)
    a = padd(pmul(s, s), pscale(-1, pmul(z, z)))
    b = pscale(-1, pmul(z, padd(pmul(s, s), pscale(-2, s), pscale(-1, pmul(z, z)))))
    N = padd(pmul(a, C), pmul(b, S))
    Nt = padd(pmul(b, C), pscale(-1, pmul(a, S)))
    r2 = padd(cst(one), pscale(2, s))
    Gs = pscale(eps, pmul(r2, padd(pmul(r2, pder(N, 0)), pscale(-2, N))))
    Gz = pscale(eps, pmul(r2, pder(N, 1)))
    Gt = pscale(2, padd(r2, pscale(2*eps, Nt)))
    GC = pscale(-1, pmul(S, Gt))
    GS = pmul(C, Gt)
    return [Gs, Gz, GC, GS], N, Nt

def trig(n, one=1):
    """(cos n th, sin n th) as polynomials in C, S."""
    C, S = var(2, one), var(3, one)
    re, im = cst(one), {}
    for _ in range(n):
        re, im = padd(pmul(re, C), pscale(-1, pmul(im, S))), padd(pmul(re, S), pmul(im, C))
    return re, im

def I_poly(L, c, one=1):
    trigs = {}
    out = {}
    acc = defaultdict(lambda: 0)
    for (j, k, n, t), cc in zip(L, c):
        if n not in trigs: trigs[n] = trig(n, one)
        T = trigs[n][0 if t == 'c' else 1]
        for e, v in T.items():
            acc[(j, k, e[2], e[3])] += cc*v
    return {e: v for e, v in acc.items() if v != 0}

def lie(P, G):
    return padd(*[pmul(pder(P, i), G[i]) for i in range(NV)])

def reduce_circle(p):
    """Use C^2 + S^2 = 1 to make S-degree <= 1."""
    out = defaultdict(lambda: 0)
    stack = list(p.items())
    while stack:
        e, c = stack.pop()
        if e[3] >= 2:
            # S^2 = 1 - C^2
            f = (e[0], e[1], e[2], e[3]-2); g = (e[0], e[1], e[2]+2, e[3]-2)
            stack.append((f, c)); stack.append((g, -c))
        else:
            out[e] += c
    return {e: v for e, v in out.items() if v != 0}
