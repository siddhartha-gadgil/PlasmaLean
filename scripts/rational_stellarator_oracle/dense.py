"""Exact integer dense 3-variable polynomials: the reference implementation of the Lean checker.
A dense poly is a list (axis 0) of lists (axis 1) of lists (axis 2) of Python ints (ragged allowed).
"""
import sys
sys.setrecursionlimit(100000)
COST = [0]

def add1(a, b):
    n = max(len(a), len(b)); COST[0] += n
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def neg1(a): return [-x for x in a]
def add2(a, b):
    n = max(len(a), len(b))
    return [add1(a[i] if i < len(a) else [], b[i] if i < len(b) else []) for i in range(n)]
def add3(a, b):
    n = max(len(a), len(b))
    return [add2(a[i] if i < len(a) else [], b[i] if i < len(b) else []) for i in range(n)]
def scal1(c, a): COST[0] += len(a); return [c*x for x in a]
def scal2(c, a): return [scal1(c, x) for x in a]
def scal3(c, a): return [scal2(c, x) for x in a]
def neg2(a): return scal2(-1, a)

def taylor(coeffs, add, neg, sgn):
    """coefficients of q(y + sgn) given those of q(y); Ruffini (repeated synthetic division)."""
    a = list(coeffs)
    n = len(a)
    out = []
    for _ in range(n):
        # one pass from the top: b_top = a_top; b_j = a_j + sgn*b_{j+1}
        b = [None]*len(a)
        b[-1] = a[-1]
        for j in range(len(a)-2, -1, -1):
            b[j] = add(a[j], b[j+1] if sgn > 0 else neg(b[j+1]))
        out.append(b[0])
        a = b[1:]
        if not a: break
    return out

def shift1(a, sgn, d):
    """2^d a((sgn + y)/2) for a univariate list a (len-1 <= d)."""
    if not a: return []
    b = scal_pow(a, d)
    return taylor(b, lambda u, v: u + v, lambda u: -u, sgn) if True else None

def scal_pow(a, d):
    COST[0] += len(a)
    return [x * (1 << (d - j)) for j, x in enumerate(a)]

def taylor_int(a, sgn):
    a = list(a); out = []
    while a:
        b = [0]*len(a); b[-1] = a[-1]
        for j in range(len(a)-2, -1, -1):
            b[j] = a[j] + (b[j+1] if sgn > 0 else -b[j+1])
        COST[0] += len(a) - 1
        out.append(b[0]); a = b[1:]
    return out

def shift_ax(A, ax, sgn, d):
    if ax == 2:
        return [[taylor_int(scal_pow(f, d), sgn) for f in row] for row in A]
    if ax == 1:
        def sh2(row):
            if not row: return []
            b = [scal1(1 << (d - k), f) for k, f in enumerate(row)]
            return taylor(b, add1, neg1, sgn)
        return [sh2(row) for row in A]
    # ax == 0
    if not A: return []
    b = [scal2(1 << (d - j), r) for j, r in enumerate(A)]
    return taylor(b, add2, neg2, sgn)

def deg_ax(A, ax):
    if ax == 0: return len(A) - 1
    if ax == 1: return max((len(r) for r in A), default=0) - 1
    return max((len(f) for r in A for f in r), default=0) - 1

def truncate_total(A, D):
    rem = 0; out = []
    for j, r in enumerate(A):
        nr = []
        for k, f in enumerate(r):
            keep = max(0, D - j - k + 1)
            rem += sum(abs(x) for x in f[keep:])
            COST[0] += len(f)
            nr.append(f[:keep])
        out.append(nr)
    return out, rem

def abs_sum(A):
    s = 0
    for r in A:
        for f in r:
            COST[0] += len(f)
            s += sum(abs(x) for x in f)
    return s
def const(A):
    return A[0][0][0] if A and A[0] and A[0][0] else 0

def upper(A, rem):  # upper bound of A on cube
    c = const(A); return c + (abs_sum(A) - abs(c)) + rem
def lower(A, rem):
    c = const(A); return c - (abs_sum(A) - abs(c)) - rem
def absup(A, rem):
    return abs_sum(A) + rem

def eval3(A, x, y, t):
    return sum(c * x**j * y**k * t**m for j, r in enumerate(A) for k, f in enumerate(r) for m, c in enumerate(f))

def neg3(a): return scal3(-1, a)
