"""Exact pipeline (mirrors the Lean checker): chart transform, defect root polynomial, adaptive plan."""
import sys, pickle
from fractions import Fraction as Fr
from dense import *
import dense
from poly import reduce_circle, I_poly, field_polys
from math import comb

E = 40

def load_P(fitfile):
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    Pi = {e: int(round(v * 2**E)) for e, v in P.items()}
    return {e: v for e, v in Pi.items() if v != 0}

def G4():
    G, N, Nt = field_polys(Fr(1, 4), Fr(1))
    out = []
    for g in G:
        out.append({e: int(4*v) for e, v in g.items()})
    return out

def pderiv(p, i):
    out = {}
    for e, c in p.items():
        if e[i] > 0:
            f = list(e); f[i] -= 1; out[tuple(f)] = c*e[i]
    return out

def polymul1(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def tbasis(a, b, d, sg):
    p = [1]
    for _ in range(a): p = polymul1(p, [1, 0, -1])
    for _ in range(b): p = polymul1(p, [0, 2])
    for _ in range(d-a-b): p = polymul1(p, [1, 0, 1])
    s = sg**(a+b)
    return [s*x for x in p]

def chart(p, d, sg):
    """dense3 of (1+t^2)^d p(s, z, C(t), S(t)), chart sign sg (C = sg (1-t^2)/(1+t^2), S = sg 2t/(1+t^2))."""
    J = max(e[0] for e in p) + 1; K = max(e[1] for e in p) + 1
    A = [[[0]*(2*d+1) for _ in range(K)] for _ in range(J)]
    for e, c in p.items():
        assert e[2] + e[3] <= d
        tb = tbasis(e[2], e[3], d, sg)
        f = A[e[0]][e[1]]
        for m, x in enumerate(tb): f[m] += c*x
        dense.COST[0] += len(tb) + e[0] + e[1]
    return A

def mul3(A, B):
    J = len(A) + len(B) - 1
    out = [[[0] for _ in range(1)] for _ in range(J)]
    res = {}
    for j1, r1 in enumerate(B):
        for k1, f1 in enumerate(r1):
            for m1, c1 in enumerate(f1):
                if c1 == 0: continue
                for j2, r2 in enumerate(A):
                    for k2, f2 in enumerate(r2):
                        for m2, c2 in enumerate(f2):
                            dense.COST[0] += 1
                            if c2: res[(j1+j2, k1+k2, m1+m2)] = res.get((j1+j2, k1+k2, m1+m2), 0) + c1*c2
    return from_dict(res)

def from_dict(res):
    if not res: return []
    J = max(k[0] for k in res) + 1; K = max(k[1] for k in res) + 1; M = max(k[2] for k in res) + 1
    A = [[[0]*M for _ in range(K)] for _ in range(J)]
    for (j, k, m), v in res.items(): A[j][k][m] = v
    return A

def trim(A):
    """remove trailing zeros (for canonical shapes)."""
    out = []
    for r in A:
        nr = []
        for f in r:
            g = list(f)
            while g and g[-1] == 0: g.pop()
            nr.append(g)
        while nr and not nr[-1]: nr.pop()
        out.append(nr)
    while out and not out[-1]: out.pop()
    return out

def defect_chart(P, sg):
    G = G4()
    dI = max(e[2]+e[3] for e in P)
    total = None
    for i in range(4):
        dp = pderiv(P, i)
        di = dI if i < 2 else dI - 1
        ei = 1 if i < 2 else 2
        term = mul3(chart(dp, di, sg), chart(G[i], ei, sg))
        total = term if total is None else add3(total, term)
    return trim(total), dI + 1

def scale_root(A, a_num, a_den, Dsz):
    """B[j][k][m] = A[j][k][m] * a_num^(j+k) * a_den^(Dsz-j-k)  (s = a sigma, a = a_num/a_den)."""
    out = []
    for j, r in enumerate(A):
        nr = []
        for k, f in enumerate(r):
            fac = a_num**(j+k) * a_den**(Dsz-j-k)
            nr.append([x*fac for x in f])
        out.append(nr)
    return out
