"""UNTRUSTED oracle: ball arithmetic in the strip algebra with Kronecker certificates.

Mirrors exactly the Lean checks of PlasmaLean/Certificates/KronBall.lean and
Design/RationalStellaratorGCTorus*.lean:

* a centre of weight (1, 0, p) is a full grid G (i in [0, 2N], j in [0, 2M]) of integers, representing
  the honest element  x = sum_{i,j} G[i][j] / (2^S i^p) e^{i((i-N) th + (j-M) ps)};
* variables: centres, and the constants t (weight (1,0,0), value 1), V (weight (0,1,0), value 1),
  C = cos 2phi (weight (0,1,3)), S = sin 2phi (weight (0,1,0));
* expression trees: ('var', i) | ('cst', k) | ('add', e, f) | ('sub', e, f) | ('mul', e, f),
  with KronExpr.Ex semantics (wt, sgn, evH, box, majN, majQ, dmajQ);
* a node: tree e of weight (dq + dd, eq + de, p), integer c, new centre Q of weight (dq, eq, p):
  G = evH e - c T^dd V^de Q, its separable weighted digit sum wl1KronP (weights 74315^s 2^{16(K-s)}).
"""
from fractions import Fraction as Fr
import gmpy2
from gmpy2 import mpz

P_EXP, E_EXP = 74315, 16          # e^{r_A} <= 74315 / 2^16


def ndist(i, i0):
    return abs(i - i0)


def kwtS(K, s):
    return mpz(P_EXP) ** s * (mpz(2) ** (E_EXP * (K - s)))


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


def evH(W, x, e, cache=None):
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
    """digits g_n with Nv = sum g_n 2^{bn}, |g_n| < 2^{b-1} (count digits)."""
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
    """balanced digits by binary splitting (fast for large numbers)."""
    if count <= 64:
        return balanced_digits(Nv, b, count)
    h = count // 2
    mod = mpz(1) << (b * h)
    lo = gmpy2.f_mod(Nv, mod)
    if lo >= (mod >> 1):
        lo -= mod
    hi = (Nv - lo) >> (b * h)
    return digits_fast(lo, b, h) + digits_fast(hi, b, count - h)


def wl1(Nv, b, Wd, R, i0, j0, Ki, Kj):
    """separable weighted digit sum (wl1KronP) of Nv: sum_j wB_j sum_i wA_i |g_{i + W j}|."""
    dg = digits_fast(Nv, b, Wd * R)
    wA = [kwtS(Ki, ndist(i, i0)) for i in range(Wd)]
    wB = [kwtS(Kj, ndist(j, j0)) for j in range(R)]
    tot = mpz(0)
    for j in range(R):
        s = mpz(0)
        for i in range(Wd):
            g = dg[i + Wd * j]
            if g:
                s += wA[i] * abs(g)
        tot += wB[j] * s
    return tot, dg


def clog2(x):
    """least dc with x <= 2^dc."""
    dc = 0
    while (1 << dc) < x:
        dc += 1
    return dc


# ---------------------------------------------------------------- the engine
class Pipeline:
    def __init__(self, N, M, S, F, name):
        self.N, self.M, self.S, self.F, self.name = N, M, S, F, name
        self.W = {}       # var -> weight
        self.Bx = {}      # var -> box
        self.L = {}       # var -> l1 bound (int)
        self.G = {}       # var -> full grid (centres only)
        self.B = {}       # var -> Fraction norm bound of the honest centre
        self.E = {}       # var -> Fraction radius of the ball
        self.names = {}
        self.kind = {}    # var -> 'T' | 'V' | 'C' | 'S' | 'grid'
        self.nodes = []   # node records
        self.nvar = 0

    # -- variables
    def add_const(self, kind, name):
        i = self.nvar
        self.nvar += 1
        N, M = self.N, self.M
        if kind == 'T':
            self.W[i], self.Bx[i], self.L[i] = (1, 0, 0), (N, M), 2 ** self.S
            self.B[i] = Fr(1)
        elif kind == 'V':
            self.W[i], self.Bx[i], self.L[i] = (0, 1, 0), (0, 1), 2
            self.B[i] = Fr(1)
        elif kind == 'C':
            self.W[i], self.Bx[i], self.L[i] = (0, 1, 3), (0, 2), 2
            self.B[i] = Fr(74315, 2 ** 16)
        elif kind == 'S':
            self.W[i], self.Bx[i], self.L[i] = (0, 1, 0), (0, 2), 2
            self.B[i] = Fr(74315, 2 ** 16)
        self.E[i] = Fr(0)
        self.kind[i] = kind
        self.names[i] = name
        return i

    def add_grid(self, G, p, name, E=Fr(0), Lstatic=None):
        i = self.nvar
        self.nvar += 1
        self.W[i] = (1, 0, p)
        self.Bx[i] = (2 * self.N, 2 * self.M)
        self.G[i] = G
        # static l1 bound (Lean: l1_dataGrid_le etc.), checked against the actual values
        self.L[i] = Lstatic if Lstatic is not None else (2 * self.N + 1) * (2 * self.M + 1) * 2 ** self.F
        assert sum(abs(v) for col in G for v in col) <= self.L[i]
        assert all(abs(v) <= self.L[i] // ((2 * self.N + 1) * (2 * self.M + 1)) for col in G for v in col)
        self.kind[i] = 'grid'
        self.names[i] = name
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
            return (mpz(1) << (b * 2 * Wd)) - 1
        if k == 'S':
            return (mpz(1) << (b * 2 * Wd)) + 1
        return kron_grid(self.G[i], b, Wd)

    def center_norm(self, i):
        """Lean: Bd r (ctr (1,0,p) G) (K / 2^{16(N+M)} / 2^S), K = wl1 of kron G at (b, 2N+1)."""
        N, M, S = self.N, self.M, self.S
        b = clog2(self.L[i] + 1) + 2
        Wd = 2 * N + 1
        R = 2 * M + 1
        K, _ = wl1(kron_grid(self.G[i], b, Wd), b, Wd, R, N, M, N, M)
        Bq = up(Fr(int(K), 2 ** (E_EXP * (N + M)) * 2 ** S), 4)
        rec = dict(b=b, W=Wd, dc=clog2(Wd), dr=clog2(R), R=R, K=int(K), Ki=N, Kj=M, Bq=Bq)
        self.normrec = getattr(self, 'normrec', {})
        self.normrec[i] = rec
        return Bq

    # -- a node
    def node(self, name, e, c, newp=None, store=True, Erad=None, record=True):
        """Evaluate tree e; if c != 0 round to a new centre of phase newp (weight (1,0,p))."""
        N, M, S = self.N, self.M, self.S
        w = wt(self.W, e)
        assert w is not None, ('inhomogeneous', name)
        d, ee, p = w
        if c != 0:
            dq, eq = 1, 0
            assert d >= 1
            dd, de = d - 1, ee
        else:
            dq, eq, dd, de = d, ee, 0, 0
        a, J = box(self.Bx, e)
        aQ, JQ = (dd * N + 2 * N, dd * M + de + 2 * M) if c != 0 else (0, 0)
        A = max(a, aQ)
        JJ = max(J, JQ)
        Wd = A + 1
        R = JJ + 1
        i0, j0 = d * N, d * M + ee
        Ki, Kj = max(i0, A - i0), max(j0, JJ - j0)
        # exact product: choose b from the a priori bound (Q unknown yet: bound its l1 later)
        lmaj = majN(self.L, e)
        b0 = clog2(lmaj + 1) + 2
        x = {i: self.kron_var(i, b0, Wd) for i in tree_vars(e)}
        Ev = evH(self.W, x, e)
        dg = digits_fast(Ev, b0, Wd * R)
        Q = None
        if c != 0:
            # round: Q[i][j] ~ G_exact[i + dd N][j + dd M + de] / (c 2^{S dd} 2^{de})
            den = c * (2 ** (S * dd)) * (2 ** de)
            s = 1 if p % 2 == 0 else -1
            Q = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    v = dg[(ii + dd * N) + Wd * (jj + dd * M + de)]
                    Q[ii][jj] = round_div(v, den)
            # symmetrize exactly (G(-n) = s G(n)); centre for odd: 0, even: an even integer
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    i2, j2 = 2 * N - ii, 2 * M - jj
                    if (ii, jj) < (i2, j2):
                        avg = round_div(Q[ii][jj] + s * Q[i2][j2], 2)
                        Q[ii][jj] = avg
                        Q[i2][j2] = s * avg
            Q[N][M] = 2 * round_div(Q[N][M], 2) if s == 1 else 0
            LQ = sum(abs(v) for col in Q for v in col)
        else:
            LQ = 0
        lG = lmaj + abs(c) * (2 ** (S * dd)) * (2 ** de) * LQ
        b = clog2(lG + 1) + 2
        x = {i: self.kron_var(i, b, Wd) for i in tree_vars(e)}
        Gv = evH(self.W, x, e)
        if c != 0:
            TK = (mpz(2) ** S) << (b * (N + Wd * M))
            VK = mpz(2) << (b * Wd)
            Gv -= c * TK ** dd * VK ** de * kron_grid(Q, b, Wd)
        K, _ = wl1(Gv, b, Wd, R, i0, j0, Ki, Kj)
        beta = Fr(int(K), 2 ** (E_EXP * (Ki + Kj)) * 2 ** (S * d + ee))
        dm = dmajQ(self.B, self.E, e)
        rec = dict(name=name, n=self.nvar, tree=e, c=c, w=w, dq=dq, eq=eq, dd=dd, de=de, box=(a, J), A=A, JJ=JJ,
                   W=Wd, R=R, b=b, dc=clog2(Wd), dr=clog2(R), i0=i0, j0=j0, Ki=Ki, Kj=Kj, K=int(K),
                   lmaj=lmaj, LQ=LQ, beta=beta, dmaj=dm, newp=p)
        if not record:
            return Q
        if c != 0:
            rad = (dm + beta) / abs(c)
            Erad = up(rad) if Erad is None else Erad
            assert Erad >= rad
            v = self.add_grid(Q, p, name, E=Erad)
            rec['var'] = v
            rec['rad'] = rad
        else:
            rec['rad'] = dm + beta
            rec['var'] = None
        self.nodes.append(rec)
        return rec


def round_div(v, den):
    """nearest integer to v / den (den > 0 or < 0)."""
    v, den = mpz(v), mpz(den)
    if den < 0:
        v, den = -v, -den
    q = gmpy2.f_div(2 * v + den, 2 * den)
    return int(q)


def up(x, digits=3):
    """a rational upper bound of x > 0 with `digits` significant decimal digits."""
    if x <= 0:
        return Fr(0)
    import math
    e = math.floor(math.log10(float(x))) if float(x) > 0 else -300
    if float(x) == 0.0:
        # very small: use exact exponent via numerator/denominator lengths
        e = len(str(x.numerator)) - len(str(x.denominator))
    sc = Fr(10) ** (e - digits + 1)
    k = math.ceil(x / sc)
    return k * sc
