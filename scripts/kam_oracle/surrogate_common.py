"""UNTRUSTED.  Shared data for the surrogate-torus certificates of torus A (KamTorusASurrogate*).

Reads the surrogate torus (listA, listB of KamTorusAFrameData.lean) and the polynomials Dp, Pp of
KamNewtonField.lean, and builds the compact integer grids exactly as the Lean definitions do.
"""
import re
from fractions import Fraction as Fr

ROOT = __file__.rsplit('/scripts/', 1)[0]
N, M, n1, m1, pS = 32, 22, 7, 5, 32
sig1 = 2 ** (pS + 1)


def lean_list(src, name):
    m = re.search(r'def ' + name + r' : List ℤ :=\s*\[(.*?)\]', src, re.S)
    return [int(x) for x in m.group(1).replace('\n', ' ').split(',')]


fsrc = open(ROOT + '/PlasmaLean/Design/KamTorusAFrameData.lean').read()
listA, listB = lean_list(fsrc, 'listA'), lean_list(fsrc, 'listB')


def win(l, i, j):
    if N <= i <= N + n1 and M - m1 <= j <= M + m1:
        k = (i - N) * (2 * m1 + 1) + (j - (M - m1))
        return l[k] if k < len(l) else 0
    return 0


def nsub(a, b):
    return a - b if a >= b else 0


def symC(c):
    return lambda i, j: c(i, j) + c(nsub(2 * N, i), nsub(2 * M, j))


def symS(c):
    return lambda i, j: c(i, j) - c(nsub(2 * N, i), nsub(2 * M, j))


def cpt(G):
    return lambda i, j: G(i + (N - n1), j + (M - m1))


tA = lambda i, j: win(listA, i, j)
tB = lambda i, j: win(listB, i, j)
_gR, _gZ = cpt(symC(tA)), cpt(symS(tB))
gRc = [[_gR(i, j) for j in range(2 * m1 + 1)] for i in range(2 * n1 + 1)]
gZc = [[_gZ(i, j) for j in range(2 * m1 + 1)] for i in range(2 * n1 + 1)]
gAc = [[(i - n1) * gRc[i][j] for j in range(2 * m1 + 1)] for i in range(2 * n1 + 1)]
gBc = [[(i - n1) * gZc[i][j] for j in range(2 * m1 + 1)] for i in range(2 * n1 + 1)]

# ---- polynomials of KamNewtonField (monomial form in u, z, c, s) ----
ksrc = open(ROOT + '/PlasmaLean/Design/KamNewtonField.lean').read()


def polylist(name):
    body = re.search(r'def ' + name + r' : PolyExpr ℂ \(Fin 6\) := sumE \[(.*?)\]\]', ksrc, re.S).group(1) + ']'
    out = []
    for c, vs in re.findall(r'monoE \(([-0-9/]+)\) \[(.*?)\]', body):
        e = [0, 0, 0, 0]
        for a, k in re.findall(r'\((\d), (\d+)\)', vs):
            e[int(a)] += int(k)
        out.append((Fr(c), tuple(e)))
    return out


Dmon, Pmon = polylist('Dp'), polylist('Pp')
