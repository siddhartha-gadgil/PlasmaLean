"""UNTRUSTED: ball arithmetic in the strip algebra with Kronecker certificates, for the low-resolution
admissibility chain of Dommaschk torus C (N-33 item 8).  Generalises scripts/gc_kam/ballcert.py:

* the strip weights `kwtS P E K s = P^s 2^{E(K - s)}` with `e^r <= P / 2^E` are parameters (the GC
  chain hard-codes P = 74315, E = 16, i.e. r <= 0.1258; torus C needs r = 0.045: P = 68553);
* the angle is the oracle angle psi_o = 2 phi (stellarator symmetry: U = R - R0 a cosine series, phase 0;
  z a sine series, phase 1), so the constant variables are C = cos psi_o (the GC `sPoly` v^2 + 1 with
  weight (0, 1, 0)) and S = sin psi_o (the GC `cPoly` v^2 - 1 with weight (0, 1, 1));
* every grid variable has its own field width F (static l1 bound (2N+1)(2M+1) 2^F).

It mirrors exactly the Lean checks of PlasmaLean/Design/DommaschkKamCKronW.lean (`nodeKw`, `normKw`,
`centerKw`, the trees of `Certificates/KronExpr`):

* a centre of weight (1, 0, p) is a full grid G (i in [0, 2N], j in [0, 2M]) of integers, the honest
  element x = sum G[i][j] / (2^S i^p) e^{i((i-N) theta + (j-M) psi)};
* trees: ('var', i) | ('cst', k) | ('add', e, f) | ('sub', e, f) | ('mul', e, f);
* a rounding node: tree e of weight (1 + dd, de, p), integer c, new centre Q of weight (1, 0, p):
  G = evH e - c T^dd V^de Q, radius (dmajQ + beta)/|c| with beta the weighted digit sum of kron G;
* a norm node: ||eval e|| <= dmajQ + beta.
"""
from fractions import Fraction as Fr
import math

import gmpy2
from gmpy2 import mpz


def ndist(i, i0):
    return abs(i - i0)


# ---------------------------------------------------------------- trees
def wt(W, e):
    k = e[0]
    if k == 'var':
        return W[e[1]]
    if k == 'cst':
        return (0, 0, 0)
    a, b = wt(W, e[1]), wt(W, e[2])
    if a is None or b is None:
        return None
    if k in ('add', 'sub'):
        if a[0] == b[0] and a[1] == b[1] and (a[2] + b[2]) % 2 == 0:
            return a
        return None
    return (a[0] + b[0], a[1] + b[1], (a[2] + b[2]) % 4)


def sgn(W, e, f):
    a, b = wt(W, e), wt(W, f)
    if a is None or b is None:
        return 1
    return 1 if a[2] == b[2] else -1


def evH(W, x, e):
    k = e[0]
    if k == 'var':
        return x[e[1]]
    if k == 'cst':
        return mpz(e[1])
    A = evH(W, x, e[1])
    B = evH(W, x, e[2])
    if k == 'add':
        return A + sgn(W, e[1], e[2]) * B
    if k == 'sub':
        return A - sgn(W, e[1], e[2]) * B
    return A * B


def box(Bx, e):
    k = e[0]
    if k == 'var':
        return Bx[e[1]]
    if k == 'cst':
        return (0, 0)
    a, b = box(Bx, e[1]), box(Bx, e[2])
    if k in ('add', 'sub'):
        return (max(a[0], b[0]), max(a[1], b[1]))
    return (a[0] + b[0], a[1] + b[1])


def majN(L, e):
    k = e[0]
    if k == 'var':
        return L[e[1]]
    if k == 'cst':
        return abs(e[1])
    a, b = majN(L, e[1]), majN(L, e[2])
    return a + b if k in ('add', 'sub') else a * b


def majQ(B, e):
    k = e[0]
    if k == 'var':
        return B[e[1]]
    if k == 'cst':
        return Fr(abs(e[1]))
    a, b = majQ(B, e[1]), majQ(B, e[2])
    return a + b if k in ('add', 'sub') else a * b


def dmajQ(B, E, e):
    k = e[0]
    if k == 'var':
        return E[e[1]]
    if k == 'cst':
        return Fr(0)
    if k in ('add', 'sub'):
        return dmajQ(B, E, e[1]) + dmajQ(B, E, e[2])
    de, df = dmajQ(B, E, e[1]), dmajQ(B, E, e[2])
    return de * (majQ(B, e[2]) + df) + majQ(B, e[1]) * df


def tree_vars(e, acc=None):
    if acc is None:
        acc = set()
    if e[0] == 'var':
        acc.add(e[1])
    elif e[0] != 'cst':
        tree_vars(e[1], acc)
        tree_vars(e[2], acc)
    return acc


def below(n, e):
    return all(i < n for i in tree_vars(e))


# ---------------------------------------------------------------- trees of sparse polynomials
# Mirrors `pwT`, `termT`, `polyT` of Design/DommaschkKamCKronW.lean.
def pwT(v, n, acc):
    """acc multiplied n times by the variable v: .mul (.var v) (pwT v (n-1) acc)."""
    for _ in range(n):
        acc = ('mul', ('var', v), acc)
    return acc


def termT(L, ep, mono, t):
    """(L q) * (C^c (S^d (V^(ep - c - d) (var mono(a, b))))), t = (q, a, b, c, d)."""
    q, a, b, c, d = t
    k = L * q
    assert k.denominator == 1, 'non-integral coefficient'
    assert c + d <= ep
    return ('mul', ('cst', int(k)), pwT(2, c, pwT(3, d, pwT(1, ep - c - d, ('var', mono(a, b))))))


def polyT(L, ep, mono, p):
    """The sum of the terms, right-nested: t0 + (t1 + (... + t_last))."""
    assert p, 'empty polynomial'
    if len(p) == 1:
        return termT(L, ep, mono, p[0])
    return ('add', termT(L, ep, mono, p[0]), polyT(L, ep, mono, p[1:]))


# ---------------------------------------------------------------- Kronecker
def kron_grid(G, b, Wd):
    """sum G[i][j] 2^{b(i + W j)} for a full grid (list of columns i, rows j)."""
    tot = mpz(0)
    nI = len(G)
    nJ = len(G[0])
    for j in range(nJ - 1, -1, -1):
        row = mpz(0)
        for i in range(nI - 1, -1, -1):
            row = (row << b) + G[i][j]
        tot = (tot << (b * Wd)) + row
    return tot


def balanced_digits(Nv, b, count):
    out = []
    half = mpz(1) << (b - 1)
    mod = mpz(1) << b
    x = mpz(Nv)
    for _ in range(count):
        r = gmpy2.f_mod(x, mod)
        if r >= half:
            r -= mod
        out.append(r)
        x = (x - r) >> b
    assert x == 0, 'digit overflow'
    return out


def digits_fast(Nv, b, count):
    if count <= 64:
        return balanced_digits(Nv, b, count)
    h = count // 2
    mod = mpz(1) << (b * h)
    lo = gmpy2.f_mod(Nv, mod)
    if lo >= (mod >> 1):
        lo -= mod
    hi = (Nv - lo) >> (b * h)
    return digits_fast(lo, b, h) + digits_fast(hi, b, count - h)


def clog2(x):
    dc = 0
    while (1 << dc) < x:
        dc += 1
    return dc


def up(x, digits=5):
    """A rational upper bound of x >= 0 with `digits` significant decimal digits."""
    x = Fr(x)
    if x <= 0:
        return Fr(0)
    e = len(str(x.numerator)) - len(str(x.denominator))
    sc = Fr(10) ** (e - digits)
    k = -((-x) // sc)
    r = k * sc
    assert r >= x
    return r


def down(x, digits=5):
    """A rational lower bound of x with `digits` significant decimal digits (x > 0)."""
    x = Fr(x)
    assert x > 0
    e = len(str(x.numerator)) - len(str(x.denominator))
    sc = Fr(10) ** (e - digits)
    r = (x // sc) * sc
    assert r <= x
    return r


def round_div(v, den):
    v, den = mpz(v), mpz(den)
    if den < 0:
        v, den = -v, -den
    return int(gmpy2.f_div(2 * v + den, 2 * den))


# ---------------------------------------------------------------- the engine
class Pipeline:
    def __init__(self, N, M, S, P, E):
        self.N, self.M, self.S, self.P, self.E_EXP = N, M, S, P, E
        self.W, self.Bx, self.L, self.G, self.B, self.E = {}, {}, {}, {}, {}, {}
        self.F = {}
        self.names, self.kind, self.info = {}, {}, {}
        self.steps = []          # one record per variable / norm node, in order
        self.normrec = {}
        self.nvar = 0

    def kwtS(self, K, s):
        return mpz(self.P) ** s * (mpz(2) ** (self.E_EXP * (K - s)))

    def wl1(self, Nv, b, Wd, R, i0, j0, Ki, Kj):
        dg = digits_fast(Nv, b, Wd * R)
        wA = [self.kwtS(Ki, ndist(i, i0)) for i in range(Wd)]
        wB = [self.kwtS(Kj, ndist(j, j0)) for j in range(R)]
        tot = mpz(0)
        for j in range(R):
            s = mpz(0)
            for i in range(Wd):
                g = dg[i + Wd * j]
                if g:
                    s += wA[i] * abs(g)
            tot += wB[j] * s
        return tot

    # -- variables
    def add_const(self, kind, name):
        i = self.nvar
        self.nvar += 1
        N, M = self.N, self.M
        eb = Fr(self.P, 2 ** self.E_EXP)
        if kind == 'T':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (1, 0, 0), (N, M), 2 ** self.S, Fr(1)
        elif kind == 'V':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 0), (0, 1), 2, Fr(1)
        elif kind == 'C':      # cos psi_o: sPoly = v^2 + 1, weight (0, 1, 0)
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 0), (0, 2), 2, eb
        elif kind == 'S':      # sin psi_o: cPoly = v^2 - 1, weight (0, 1, 1)
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 1), (0, 2), 2, eb
        self.E[i] = Fr(0)
        self.kind[i] = kind
        self.names[i] = name
        self.steps.append(dict(kind='const', var=i, name=name))
        return i

    def add_grid(self, G, p, name, F, E=Fr(0), Lstatic=None, kind='grid', info=None):
        i = self.nvar
        self.nvar += 1
        N, M = self.N, self.M
        self.W[i] = (1, 0, p)
        self.Bx[i] = (2 * N, 2 * M)
        self.G[i] = G
        self.F[i] = F
        self.L[i] = Lstatic if Lstatic is not None else (2 * N + 1) * (2 * M + 1) * 2 ** F
        assert sum(abs(v) for col in G for v in col) <= self.L[i]
        if Lstatic is None:
            assert all(abs(v) <= 2 ** F for col in G for v in col), name
        self.kind[i] = kind
        self.names[i] = name
        self.info[i] = info or {}
        self.E[i] = E
        self.B[i] = self.center_norm(i)
        return i

    def kron_var(self, i, b, Wd):
        k = self.kind[i]
        N, M, S = self.N, self.M, self.S
        if k == 'T':
            return (mpz(2) ** S) << (b * (N + Wd * M))
        if k == 'V':
            return mpz(2) << (b * Wd)
        if k == 'C':
            return (mpz(1) << (b * 2 * Wd)) + 1
        if k == 'S':
            return (mpz(1) << (b * 2 * Wd)) - 1
        return kron_grid(self.G[i], b, Wd)

    def center_norm(self, i):
        N, M, S = self.N, self.M, self.S
        b = clog2(self.L[i] + 1) + 2
        Wd = 2 * N + 1
        R = 2 * M + 1
        K = self.wl1(kron_grid(self.G[i], b, Wd), b, Wd, R, N, M, N, M)
        Bq = up(Fr(int(K), 2 ** (self.E_EXP * (N + M)) * 2 ** S), 6)
        self.normrec[i] = dict(b=b, W=Wd, dc=clog2(Wd), dr=clog2(R), K=int(K), Ki=N, Kj=M, Bq=Bq)
        return Bq

    # -- a node
    def node(self, name, e, c, F=None, rel=None, info=None):
        """Evaluate tree e; c != 0: round to a new centre (weight (1, 0, p), field width F);
        c == 0: a norm node."""
        N, M, S = self.N, self.M, self.S
        n = self.nvar
        assert below(n, e), ('variables not below', name)
        w = wt(self.W, e)
        assert w is not None, ('inhomogeneous', name)
        d, ee, p = w
        if c != 0:
            assert d >= 1
            dd, de = d - 1, ee
        else:
            dd, de = 0, 0
        a, J = box(self.Bx, e)
        aQ, JQ = (dd * N + 2 * N, dd * M + de + 2 * M) if c != 0 else (0, 0)
        A = max(a, aQ)
        JJ = max(J, JQ)
        Wd = A + 1
        R = JJ + 1
        i0, j0 = d * N, d * M + ee
        Ki, Kj = max(i0, A - i0), max(j0, JJ - j0)
        lmaj = majN(self.L, e)
        Q = None
        if c != 0:
            b0 = clog2(lmaj + 1) + 2
            x = {i: self.kron_var(i, b0, Wd) for i in tree_vars(e)}
            dg = digits_fast(evH(self.W, x, e), b0, Wd * R)
            den = c * (2 ** (S * dd)) * (2 ** de)
            s = 1 if p % 2 == 0 else -1
            Q = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    Q[ii][jj] = round_div(dg[(ii + dd * N) + Wd * (jj + dd * M + de)], den)
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    i2, j2 = 2 * N - ii, 2 * M - jj
                    if (ii, jj) < (i2, j2):
                        avg = round_div(Q[ii][jj] + s * Q[i2][j2], 2)
                        Q[ii][jj] = avg
                        Q[i2][j2] = s * avg
            Q[N][M] = 2 * round_div(Q[N][M], 2) if s == 1 else 0
            mx = max(abs(v) for col in Q for v in col)
            if F is None:
                F = max(8, clog2(mx + 1) + 1)
            assert mx < 2 ** (F - 1), ("field width", name)
            LQ = (2 * N + 1) * (2 * M + 1) * 2 ** F
            lG = lmaj + abs(c) * (2 ** (S * dd)) * (2 ** de) * LQ
        else:
            lG = lmaj
        b = clog2(lG + 1) + 2
        x = {i: self.kron_var(i, b, Wd) for i in tree_vars(e)}
        Gv = evH(self.W, x, e)
        if c != 0:
            TK = (mpz(2) ** S) << (b * (N + Wd * M))
            VK = mpz(2) << (b * Wd)
            Gv -= c * TK ** dd * VK ** de * kron_grid(Q, b, Wd)
        K = self.wl1(Gv, b, Wd, R, i0, j0, Ki, Kj)
        beta = Fr(int(K), 2 ** (self.E_EXP * (Ki + Kj)) * 2 ** (S * d + ee))
        dm = dmajQ(self.B, self.E, e)
        rec = dict(name=name, n=n, tree=e, c=c, w=w, dd=dd, de=de, p=p, A=A, J=JJ, W=Wd, R=R, b=b,
                   dc=clog2(Wd), dr=clog2(R), i0=i0, j0=j0, Ki=Ki, Kj=Kj, K=int(K), lmaj=lmaj,
                   beta=beta, dmaj=dm, rel=rel, info=info or {})
        if c != 0:
            rad = (dm + beta) / abs(c)
            Erad = up(rad, 3) if rad > 0 else Fr(0)
            v = self.add_grid(Q, p, name, F, E=Erad, kind='node', info=info)
            assert v == n
            rec['var'] = v
            rec['rad'] = rad
            rec['F'] = F
            rec['kind'] = 'node'
        else:
            rec['rad'] = dm + beta
            rec['bound'] = up(dm + beta, 6)
            rec['var'] = None
            rec['kind'] = 'norm'
        self.steps.append(rec)
        return rec

    def data(self, G, p, name, F, Lstatic=None, kind='data', info=None):
        v = self.add_grid(G, p, name, F, Lstatic=Lstatic, kind=kind, info=info)
        self.steps.append(dict(kind=kind, var=v, name=name, info=info or {}))
        return v

    # -- evaluation of a centre on a grid (floats, for the approximate inverses)
    def centre_values(self, i, n1, n2):
        """Values of the honest centre of grid variable i on the n1 x n2 uniform grid."""
        import numpy as np
        N, M, S = self.N, self.M, self.S
        p = self.W[i][2]
        C = np.zeros((n1, n2), dtype=complex)
        G = self.G[i]
        fac = 1.0 / (2.0 ** S) / (1j ** p)
        for ii in range(2 * N + 1):
            for jj in range(2 * M + 1):
                if G[ii][jj]:
                    C[(ii - N) % n1, (jj - M) % n2] = float(G[ii][jj]) * fac
        return np.fft.ifft2(C) * (n1 * n2)


def grid_from_values(F, N, M, S, p):
    """Round the values F (n1 x n2, real) to a symmetric grid of phase p (box N x M, scale 2^S)."""
    import numpy as np
    n1, n2 = F.shape
    C = np.fft.fft2(F) / (n1 * n2)
    s = 1 if p % 2 == 0 else -1
    G = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for ii in range(2 * N + 1):
        for jj in range(2 * M + 1):
            v = C[(ii - N) % n1, (jj - M) % n2] * (1j ** p) * (2.0 ** S)
            G[ii][jj] = int(round(v.real))
    for ii in range(2 * N + 1):
        for jj in range(2 * M + 1):
            i2, j2 = 2 * N - ii, 2 * M - jj
            if (ii, jj) < (i2, j2):
                avg = round_div(G[ii][jj] + s * G[i2][j2], 2)
                G[ii][jj] = avg
                G[i2][j2] = s * avg
    G[N][M] = 2 * round_div(G[N][M], 2) if s == 1 else 0
    return G
