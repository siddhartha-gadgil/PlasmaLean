"""UNTRUSTED oracle: ball arithmetic for one-parameter families (Chebyshev series in w = e^{i theta'}),
mirroring exactly the Lean checks of PlasmaLean/Certificates/KronBallCheb*.lean:

* a family centre of weight (1, 0, p) is a w-symmetric list of slices (Chebyshev coefficients)
  g_0, ..., g_D' (2-D integer grids, stellarator symmetric with sign s = (-1)^p), representing
  famCtr = sum_k (c^k + c^-k) ctr(g_k) (k = 0 once), stored as SliceData
  (right halves of the rows i > N of the band |j - M| <= Mj, and the centre column i = N, j >= M);
* the Kronecker image at (b, W, R): sum_{k, i, j} G[k][i][j] 2^{b (i + W (j + R k))} with the Laurent
  index k in [0, 2D] (offset D carried by T3 = 2^S u^N v^M w^D);
* chebK: absolute digits, rows j < R Kw weighted kwtS(Kj, |j mod R - j0|), blocks of L digits along a
  row weighted by the larger end weight kwtS(Ki, |i - i0|).
"""
from fractions import Fraction as Fr
import gmpy2
from gmpy2 import mpz
from ballcert import (wt, sgn, evH, majN, majQ, dmajQ, tree_vars, digits_fast, clog2, round_div, up,
                      P_EXP, E_EXP, kwtS)


def box3(Bx, e):
    k = e[0]
    if k == 'var':
        return Bx[e[1]]
    if k == 'cst':
        return (0, 0, 0)
    a, b = box3(Bx, e[1]), box3(Bx, e[2])
    if k in ('add', 'sub'):
        return (max(a[0], b[0]), max(a[1], b[1]), max(a[2], b[2]))
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2])


def pack3(G, b, W, R):
    """G[k][i][j] (lists) -> sum G 2^{b(i + W(j + R k))}."""
    tot = mpz(0)
    nK = len(G)
    for k in range(nK - 1, -1, -1):
        Gk = G[k]
        nI = len(Gk)
        nJ = len(Gk[0])
        sl = mpz(0)
        for j in range(R - 1, -1, -1):
            row = mpz(0)
            if j < nJ:
                for i in range(nI - 1, -1, -1):
                    row = (row << b) + Gk[i][j]
            sl = (sl << (b * W)) + row
        tot = (tot << (b * W * R)) + sl
    return tot


def chebK(Nv, b, W, R, Kw, L, i0, j0, Ki, Kj):
    """The Lean chebK (exact integer)."""
    n = W * R * Kw
    H = mpz(1) << (b - 1)
    dg = digits_fast(Nv, b, n)
    wA = [kwtS(Ki, abs(i - i0)) for i in range(W)]
    tot = mpz(0)
    for jj in range(R * Kw):
        wB = kwtS(Kj, abs(jj % R - j0))
        rs = mpz(0)
        base = W * jj
        i = 0
        while i < W:
            ln = min(L, W - i)
            s = 0
            for t in range(ln):
                g = dg[base + i + t]
                s += g if g >= 0 else -g
            if s:
                rs += s * max(wA[i], wA[i + ln - 1])
            i += ln
        tot += wB * rs
    return tot


def field_bits(vals):
    m = max((abs(v) for v in vals), default=0)
    return max(2, int(m).bit_length() + 2)


class Slice:
    """A stored Chebyshev coefficient (mirror of Lean SliceData): blk = all right halves (row r, field
    r Nj + t), col = centre column."""

    def __init__(self, Nj, Mj, Fj, rows, col):
        self.Nj, self.Mj, self.Fj, self.rows, self.col = Nj, Mj, Fj, rows, col
        blk = 0
        for r in range(len(rows) - 1, -1, -1):
            blk = (blk << (Fj * Nj)) + rows[r]
        self.blk = blk
        self.k1 = clog2((2 * Mj + 1) * Nj)
        self.k2 = clog2(2 * Mj + 1)


def min_box(g, N, M):
    nk = max([abs(i - N) for i in range(2 * N + 1) for j in range(2 * M + 1) if g[i][j] != 0] + [0])
    nm = max([abs(j - M) for i in range(2 * N + 1) for j in range(2 * M + 1) if g[i][j] != 0] + [0])
    return nk, nm


def encode_slice(g, N, M, s, Nj=None, Mj=None):
    """Store a stellarator-symmetric 2-D grid g[i][j] (box N, M) truncated to (Nj, Mj) (default: the
    minimal box of the nonzero entries).  Returns (Slice, truncated grid)."""
    if Nj is None:
        Nj, Mj = min_box(g, N, M)
    vals = []
    for r in range(2 * Mj + 1):
        j = M - Mj + r
        for t in range(Nj):
            vals.append(g[N + 1 + t][j])
    for t in range(Mj + 1):
        v = g[N][M + t]
        vals.append(v // 2 if t == 0 else v)
    F = field_bits(vals)
    off = 1 << (F - 1)
    rows = []
    for r in range(2 * Mj + 1):
        j = M - Mj + r
        x = 0
        for t in range(Nj - 1, -1, -1):
            x = (x << F) + g[N + 1 + t][j] + off
        rows.append(x)
    col = 0
    for t in range(Mj, -1, -1):
        v = g[N][M + t]
        if t == 0:
            assert v % 2 == 0 or s == -1
            v = v // 2 if s == 1 else 0
        col = (col << F) + v + off
    sd = Slice(Nj, Mj, F, rows, col)
    return sd, decode_slice(sd, N, M, s)


def fieldW(F, data, f):
    return ((data >> (F * f)) % (1 << F)) - (1 << (F - 1))


def sliceH(N, M, sd, i, j):
    if N < i <= N + sd.Nj and M <= j + sd.Mj and j <= M + sd.Mj:
        idx = j + sd.Mj - M
        return fieldW(sd.Fj, sd.rows[idx] if idx < len(sd.rows) else 0, i - N - 1)
    if i == N and M <= j <= M + sd.Mj:
        return fieldW(sd.Fj, sd.col, j - M)
    return 0


def decode_slice(sd, N, M, s, c0=1, a=0, bb=0):
    """The Lean sliceG grid (box 2N x 2M)."""
    g = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for i in range(2 * N + 1):
        for j in range(2 * M + 1):
            v = sliceH(N, M, sd, i, j) + s * sliceH(N, M, sd, 2 * N - i, 2 * M - j)
            g[i][j] = (c0 + a * (i - N) + bb * (j - M)) * v
    return g


def fam_grids(slices, N, M, D, s, c0=1, a=0, bb=0):
    """The Laurent grids G[k] (k in [0, 2D]) of famPoly from the stored slices."""
    G = [[[0] * (2 * M + 1) for _ in range(2 * N + 1)] for _ in range(2 * D + 1)]
    for jw, sd in enumerate(slices):
        g = decode_slice(sd, N, M, s, c0, a, bb)
        for k in ([D] if jw == 0 else [D + jw, D - jw]):
            G[k] = [row[:] for row in g]
    return G


def famL1(slices, N, M, c0=1, a=0, bb=0):
    tot = 0
    for jw, sd in enumerate(slices):
        sl1 = (2 * N + 1) * (2 * M + 1) * ((abs(c0) + abs(a) * N + abs(bb) * M) * 2 ** sd.Fj)
        tot += (1 if jw == 0 else 2) * sl1
    return tot


class FamPipeline:
    """Ball chain of families.  Variables: kinds 'T', 'V', 'C', 'S' (constants), 'fam' (stored family
    with symbol), 'dummy' (zero)."""

    def __init__(self, N, M, D, S, name, Lblk=8, Lnorm=1):
        self.N, self.M, self.D, self.S, self.name = N, M, D, S, name
        self.Lblk = Lblk
        self.Lnorm = Lnorm
        self.Lcent = Lnorm
        self.Lc = {}
        self.W, self.Bx, self.L, self.B, self.E = {}, {}, {}, {}, {}
        self.kind, self.names, self.fam = {}, {}, {}
        self.nodes = []
        self.nvar = 0

    def add_const(self, kind, name):
        i = self.nvar
        self.nvar += 1
        N, M, D = self.N, self.M, self.D
        if kind == 'T':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (1, 0, 0), (N, M, D), 2 ** self.S, Fr(1)
        elif kind == 'V':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 0), (0, 1, 0), 2, Fr(1)
        elif kind == 'C':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 3), (0, 2, 0), 2, Fr(74315, 2 ** 16)
        elif kind == 'S':
            self.W[i], self.Bx[i], self.L[i], self.B[i] = (0, 1, 0), (0, 2, 0), 2, Fr(74315, 2 ** 16)
        self.E[i] = Fr(0)
        self.kind[i] = kind
        self.names[i] = name
        return i

    def add_dummy(self, name, w=(1, 0, 0)):
        i = self.nvar
        self.nvar += 1
        self.W[i], self.Bx[i], self.L[i], self.B[i], self.E[i] = w, (0, 0, 0), 0, Fr(0), Fr(0)
        self.kind[i] = 'dummy'
        self.names[i] = name
        return i

    def add_fam(self, slices, p, name, E=Fr(0), sym=(1, 0, 0), box=None, norm=True, Lc=None):
        """A stored family (weight (1, 0, p)); sym = (c0, a, b) multiplies the grids; the sign of the
        completion is (-1)^p0 where p0 is the phase before the symbol."""
        i = self.nvar
        self.nvar += 1
        N, M, D = self.N, self.M, self.D
        self.W[i] = (1, 0, p)
        c0, a, bb = sym
        p0 = p if (a == 0 and bb == 0) else (p + 1) % 4
        s = (-1) ** p0
        self.fam[i] = dict(slices=slices, s=s, sym=sym)
        self.Bx[i] = box if box is not None else (2 * N, 2 * M, 2 * D)
        self.L[i] = famL1(slices, N, M, c0, a, bb)
        self.kind[i] = 'fam'
        self.names[i] = name
        self.E[i] = E
        self.Lc[i] = self.Lcent if Lc is None else Lc
        self.B[i] = self.center_norm(i) if norm else None
        return i

    def grids(self, i):
        f = self.fam[i]
        c0, a, bb = f['sym']
        return fam_grids(f['slices'], self.N, self.M, self.D, f['s'], c0, a, bb)

    def kron_var(self, i, b, W, R):
        k = self.kind[i]
        N, M, D, S = self.N, self.M, self.D, self.S
        if k == 'T':
            return (mpz(2) ** S) << (b * (N + W * (M + R * D)))
        if k == 'V':
            return mpz(2) << (b * W)
        if k == 'C':
            return (mpz(1) << (b * 2 * W)) - 1
        if k == 'S':
            return (mpz(1) << (b * 2 * W)) + 1
        if k == 'dummy':
            return mpz(0)
        return pack3(self.grids(i), b, W, R)

    def layout(self, A, J, K, lG, Lb=None):
        b = clog2(lG + 1) + 2
        W, R, Kw = A + 1, J + 1, K + 1
        dr = clog2(R * Kw)
        L = self.Lblk if Lb is None else Lb
        fuel = -(-W // L)
        return b, W, R, Kw, dr, L, fuel

    def center_norm(self, i):
        N, M, D, S = self.N, self.M, self.D, self.S
        A, J, K = self.Bx[i]
        b, W, R, Kw, dr, L, fuel = self.layout(A, J, K, self.L[i], self.Lc.get(i, self.Lnorm))
        Kb = chebK(self.kron_var(i, b, W, R), b, W, R, Kw, L, N, M, N, M)
        Bq = up(Fr(int(Kb), 2 ** (E_EXP * (N + M)) * 2 ** S), 4)
        self.normrec = getattr(self, 'normrec', {})
        self.normrec[i] = dict(b=b, W=W, R=R, Kw=Kw, dr=dr, L=L, fuel=fuel, K=int(Kb), Ki=N, Kj=M,
                               Bq=Bq)
        return Bq

    def node(self, name, e, c, newp=None, Erad=None, record=True, extra=None, slicebox=None, Lb=None):
        """Evaluate tree e; if c != 0 round to a new stored family of phase p."""
        N, M, D, S = self.N, self.M, self.D, self.S
        w = wt(self.W, e)
        assert w is not None, ('inhomogeneous', name)
        d, ee, p = w
        if c != 0:
            dd, de = d - 1, ee
        else:
            dd, de = 0, 0
        A0, J0, K0 = box3(self.Bx, e)
        if c != 0:
            A = max(A0, dd * N + 2 * N)
            J = max(J0, dd * M + de + 2 * M)
            K = max(K0, dd * D + 2 * D)
        else:
            A, J, K = A0, J0, K0
        i0, j0 = d * N, d * M + ee
        Ki, Kj = max(i0, A - i0), max(j0, J - j0)
        lmaj = majN(self.L, e)
        # exact product at a provisional width
        b0, W, R, Kw, dr, L, fuel = self.layout(A, J, K, lmaj)
        x = {i: self.kron_var(i, b0, W, R) for i in tree_vars(e)}
        Ev = evH(self.W, x, e)
        dg = digits_fast(Ev, b0, W * R * Kw)
        if c != 0:
            den = c * (2 ** (S * dd)) * (2 ** de)
            s = 1 if p % 2 == 0 else -1
            # Laurent slices k in [0, 2D] of the new centre
            Q = [[[0] * (2 * M + 1) for _ in range(2 * N + 1)] for _ in range(2 * D + 1)]
            for k in range(2 * D + 1):
                for ii in range(2 * N + 1):
                    for jj in range(2 * M + 1):
                        v = dg[(ii + dd * N) + W * ((jj + dd * M + de) + R * (k + dd * D))]
                        Q[k][ii][jj] = round_div(v, den)
            # w-symmetrize and stellarator-symmetrize, encode slices
            slices = []
            for jw in range(D + 1):
                g = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
                for ii in range(2 * N + 1):
                    for jj in range(2 * M + 1):
                        g[ii][jj] = round_div(Q[D + jw][ii][jj] + Q[D - jw][ii][jj], 2) if jw else Q[D][ii][jj]
                for ii in range(2 * N + 1):
                    for jj in range(2 * M + 1):
                        i2, j2 = 2 * N - ii, 2 * M - jj
                        if (ii, jj) < (i2, j2):
                            avg = round_div(g[ii][jj] + s * g[i2][j2], 2)
                            g[ii][jj] = avg
                            g[i2][j2] = s * avg
                g[N][M] = 2 * round_div(g[N][M], 2) if s == 1 else 0
                if slicebox is None:
                    sd, _ = encode_slice(g, N, M, s)
                else:
                    Nj, Mj = slicebox(jw)
                    sd, _ = encode_slice(g, N, M, s, Nj, Mj)
                slices.append(sd)
            LQ = famL1(slices, N, M)
        else:
            LQ = 0
            slices = None
        lG = lmaj + abs(c) * (2 ** (S * dd)) * (2 ** de) * LQ
        b, W, R, Kw, dr, L, fuel = self.layout(A, J, K, lG, Lb if Lb is not None else (self.Lnorm if c == 0 else None))
        x = {i: self.kron_var(i, b, W, R) for i in tree_vars(e)}
        Gv = evH(self.W, x, e)
        if c != 0:
            TK = (mpz(2) ** S) << (b * (N + W * (M + R * D)))
            VK = mpz(2) << (b * W)
            QG = fam_grids(slices, N, M, D, (1 if p % 2 == 0 else -1))
            Gv -= c * TK ** dd * VK ** de * pack3(QG, b, W, R)
        Kb = chebK(Gv, b, W, R, Kw, L, i0, j0, Ki, Kj)
        beta = Fr(int(Kb), 2 ** (E_EXP * (Ki + Kj)) * 2 ** (S * d + ee))
        if not record:
            return slices
        dm = dmajQ(self.B, self.E, e)
        rec = dict(name=name, n=self.nvar, tree=e, c=c, w=w, dd=dd, de=de, A=A, J=J, K=K, b=b, W=W,
                   R=R, Kw=Kw, dr=dr, L=L, fuel=fuel, i0=i0, j0=j0, Ki=Ki, Kj=Kj, K_=int(Kb), lmaj=lmaj,
                   LQ=LQ, beta=beta, dmaj=dm, newp=p, slots=W * R * Kw)
        if c != 0:
            rad = (dm + beta) / abs(c)
            if extra is not None:
                rad += extra
            Er = up(rad) if Erad is None else Erad
            assert Er >= rad
            v = self.add_fam(slices, p, name, E=Er)
            rec['var'] = v
            rec['rad'] = rad
        else:
            rec['rad'] = dm + beta
            rec['var'] = None
        self.nodes.append(rec)
        return rec
