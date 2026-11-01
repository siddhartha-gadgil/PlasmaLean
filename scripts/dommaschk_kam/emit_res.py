"""UNTRUSTED generator.  The high-resolution residual chain of Dommaschk torus C (N-33 plan item 7).

Certifies the initial invariance error of the 96 x 80 data torus C (`Design/DommaschkKamCData`,
`Design/DommaschkKamCTorus`) for the field `dkFieldTC` in the weighted strip norm r = 9/200:
`Bd r (resR iota_C u0C z0C) e0q` and `Bd r (resZ ...) e0q` (`Design/DommaschkKamCRes`).

A KronBall chain (`Certificates/KronBall`, general strip weights `68553^s 2^{16(K - s)}`,
`Design/DommaschkKamCKronW`) in the oracle angle psi_o = 2 phi, layout N x M = 96 x 80 (the data box),
scale 2^-128.  Inputs (exact, radius 0): U = R - R0, Z (the data torus, re-encoded), LUx = 2^Q Lt_{iota_q} U
and LZx = 2^Q Lt_{iota_q} Z (exact weighted grids, iota_q = -Iqc/2^Q the dyadic transform of the data
module); their identity with the data module is checked entry by entry (`Design/DommaschkKamCResEq`).
Chain: R = R0 + U (exact), s = R^2, z^2 .. z^5, LU = LUx/2^Q, LZ = LZx/2^Q (rounded); the three
R-form field polynomials D = dDR, G = dnRh (n_R = R G), F = dnZR / R^2 (n_z = s F) by Horner in s:
coefficient nodes Pc_k = h_k(z, cos psi_o, sin psi_o) (polyT trees, no product) and product nodes
H_k = s H_{k+1} + Pc_k.  Two norm nodes: NR = D LU - R G and NZ = D LZ - s F (the residuals at
iota_q in the oracle frame).  Node centre norms are crude tree majorants (`Bd_ctr_of_node`); the data
centre norms come from centre checks.

Grids are stored as salted packed rows (`Design/DommaschkKamCResKron`: `RowR = (lo, cnt, F, x)`, per-row
field width, trimmed to the nonzero entries, a random 64-bit salt in the low word) and their Kronecker
images are built by divide-and-conquer spreads (`imgR`), mirrored exactly here by the full-grid
images of `adm_ball.py`.

Validation (exact, before writing): every row encoding is decoded back and compared; the ball engine
recomputes every node with gmpy2 integers exactly as the Lean kernel quantities (`nodeKw`, `normKw`,
`centerKw`); every radius and bound is a rational rounded outward; the final e0q is recomputed in
Fractions from the emitted rationals.

(needs numpy and gmpy2, e.g. the venv /tmp/dqa-venv; run with -I)
usage: python emit_res.py [--emit] [--only data,env,trees,checks,eq,rel,chain,top] [--ncheck 12] [--tag C|A]
       [--out-dir DIR]
"""
import argparse
import os
import random
import sys
import time
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import adm_ball as AB                                         # noqa: E402
import emit_adm as EA                                         # noqa: E402
import dk_torus as DT                                         # noqa: E402

P_EXP, E_EXP = 68553, 16          # e^{9/200} <= 68553 / 2^16
P1_EXP = 68897                    # e^{1/20}  <= 68897 / 2^16 (the strip of the derivative bound)
EQ_BLOCK = 23                     # rows per equality-check declaration
OUT = os.path.join(REPO, 'PlasmaLean', 'Design')
NS = 'PlasmaLean.Design.DommaschkKamC'
HEADER = EA.HEADER
OPEN = EA.OPEN
qlean = EA.qlean
POLYS = [('D', 'dDR', 0), ('G', 'dnRh', 0), ('F', 'dnZR', 2)]


# ------------------------------------------------------------------ salted rows
def encode_rows(G, N, M, rng):
    """Salted packed rows (lo, cnt, F, x) of the full grid G (columns i in [0, 2N], rows j in [0, 2M])."""
    rows = []
    for j in range(2 * M + 1):
        nz = [i for i in range(2 * N + 1) if G[i][j]]
        salt = rng.getrandbits(64)
        if not nz:
            rows.append((0, 0, 1, salt))
            continue
        lo, hi = min(nz), max(nz)
        mx = max(abs(G[i][j]) for i in range(lo, hi + 1))
        F = AB.clog2(mx + 1) + 1
        x = 0
        for i in range(hi, lo - 1, -1):
            v = G[i][j] + 2 ** (F - 1)
            assert 0 <= v < 2 ** F
            x = (x << F) + v
        rows.append((lo, hi - lo + 1, F, (x << 64) | salt))
    return rows


def decode_rows(rows, N, M):
    G = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    for j, (lo, cnt, F, x) in enumerate(rows):
        y = x >> 64
        for k in range(cnt):
            G[lo + k][j] = ((y >> (F * k)) % 2 ** F) - 2 ** (F - 1)
    return G


def rows_l1(rows):
    return sum(cnt * 2 ** (F - 1) for (_, cnt, F, _) in rows)


# ------------------------------------------------------------------ the pipeline (salted rows, static l1)
class RPipe(AB.Pipeline):
    def __init__(self, N, M, S, P, E, seed=20261101):
        super().__init__(N, M, S, P, E)
        self.rows = {}
        self.rng = random.Random(seed)

    def add_rows_grid(self, G, p, name, E=Fr(0), kind='grid', center=True, info=None):
        i = self.nvar
        self.nvar += 1
        N, M = self.N, self.M
        rows = encode_rows(G, N, M, self.rng)
        assert decode_rows(rows, N, M) == G, name
        self.rows[i] = rows
        self.W[i] = (1, 0, p)
        self.Bx[i] = (2 * N, 2 * M)
        self.G[i] = G
        self.F[i] = max(r[2] for r in rows)
        self.L[i] = rows_l1(rows)
        assert sum(abs(v) for col in G for v in col) <= self.L[i]
        self.kind[i] = kind
        self.names[i] = name
        self.info[i] = info or {}
        self.E[i] = E
        if center:
            self.B[i] = self.center_norm(i)
        return i

    def data(self, G, p, name, info=None):
        v = self.add_rows_grid(G, p, name, kind='data', info=info)
        self.steps.append(dict(kind='data', var=v, name=name, info=info or {}))
        return v

    def center_check(self, i, P):
        """centerKw at the strip weights P (for the derivative bound at r = 1/20)."""
        N, M, S = self.N, self.M, self.S
        b = AB.clog2(self.L[i] + 1) + 2
        Wd, R = 2 * N + 1, 2 * M + 1
        dg = AB.digits_fast(AB.kron_grid(self.G[i], b, Wd), b, Wd * R)
        wA = [mpz_pow(P, AB.ndist(ii, N)) * 2 ** (E_EXP * (N - AB.ndist(ii, N))) for ii in range(Wd)]
        wB = [mpz_pow(P, AB.ndist(jj, M)) * 2 ** (E_EXP * (M - AB.ndist(jj, M))) for jj in range(R)]
        K = 0
        for jj in range(R):
            s = 0
            for ii in range(Wd):
                g = dg[ii + Wd * jj]
                if g:
                    s += wA[ii] * abs(int(g))
            K += wB[jj] * s
        Bq = AB.up(Fr(int(K), 2 ** (E_EXP * (N + M)) * 2 ** S), 6)
        return dict(b=b, W=Wd, dc=AB.clog2(Wd), dr=AB.clog2(R), K=int(K), Ki=N, Kj=M, Bq=Bq, P=P)

    def node(self, name, e, c, rel=None, info=None):
        N, M, S = self.N, self.M, self.S
        n = self.nvar
        assert AB.below(n, e), ('variables not below', name)
        w = AB.wt(self.W, e)
        assert w is not None, ('inhomogeneous', name)
        d, ee, p = w
        if c != 0:
            assert d >= 1
            dd, de = d - 1, ee
        else:
            dd, de = 0, 0
        a, J = AB.box(self.Bx, e)
        aQ, JQ = (dd * N + 2 * N, dd * M + de + 2 * M) if c != 0 else (0, 0)
        A = max(a, aQ)
        JJ = max(J, JQ)
        Wd = A + 1
        R = JJ + 1
        i0, j0 = d * N, d * M + ee
        Ki, Kj = max(i0, A - i0), max(j0, JJ - j0)
        lmaj = AB.majN(self.L, e)
        Q = None
        if c != 0:
            b0 = AB.clog2(lmaj + 1) + 2
            x = {i: self.kron_var(i, b0, Wd) for i in AB.tree_vars(e)}
            dg = AB.digits_fast(AB.evH(self.W, x, e), b0, Wd * R)
            den = c * (2 ** (S * dd)) * (2 ** de)
            s = 1 if p % 2 == 0 else -1
            Q = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    Q[ii][jj] = AB.round_div(dg[(ii + dd * N) + Wd * (jj + dd * M + de)], den)
            for ii in range(2 * N + 1):
                for jj in range(2 * M + 1):
                    i2, j2 = 2 * N - ii, 2 * M - jj
                    if (ii, jj) < (i2, j2):
                        avg = AB.round_div(Q[ii][jj] + s * Q[i2][j2], 2)
                        Q[ii][jj] = avg
                        Q[i2][j2] = s * avg
            Q[N][M] = 2 * AB.round_div(Q[N][M], 2) if s == 1 else 0
            LQ = rows_l1(encode_rows(Q, N, M, random.Random(0)))
            lG = lmaj + abs(c) * (2 ** (S * dd)) * (2 ** de) * LQ
        else:
            lG = lmaj
        b = AB.clog2(lG + 1) + 2
        x = {i: self.kron_var(i, b, Wd) for i in AB.tree_vars(e)}
        Gv = AB.evH(self.W, x, e)
        if c != 0:
            TK = (AB.mpz(2) ** S) << (b * (N + Wd * M))
            VK = AB.mpz(2) << (b * Wd)
            Gv -= c * TK ** dd * VK ** de * AB.kron_grid(Q, b, Wd)
        K = self.wl1(Gv, b, Wd, R, i0, j0, Ki, Kj)
        beta = Fr(int(K), 2 ** (self.E_EXP * (Ki + Kj)) * 2 ** (S * d + ee))
        dm = AB.dmajQ(self.B, self.E, e)
        rec = dict(name=name, n=n, tree=e, c=c, w=w, dd=dd, de=de, p=p, A=A, J=JJ, W=Wd, R=R, b=b,
                   dc=AB.clog2(Wd), dr=AB.clog2(R), i0=i0, j0=j0, Ki=Ki, Kj=Kj, K=int(K), lmaj=lmaj, lG=lG,
                   beta=beta, dmaj=dm, rel=rel, info=info or {})
        if c != 0:
            rad = (dm + beta) / abs(c)
            Erad = AB.up(rad, 3) if rad > 0 else Fr(0)
            v = self.add_rows_grid(Q, p, name, E=Erad, kind='node', center=False, info=info)
            assert v == n
            # crude centre norm from the tree majorants (Bd_ctr_of_node)
            mq = AB.majQ(self.B, e)
            self.B[v] = AB.up((mq + dm) / abs(c) + Erad, 6)
            assert self.L[v] == LQ
            rec.update(var=v, rad=rad, kind='node', E=Erad, B=self.B[v], mq=mq)
        else:
            rec['rad'] = dm + beta
            rec['bound'] = AB.up(dm + beta, 6)
            rec['var'] = None
            rec['kind'] = 'norm'
        self.steps.append(rec)
        return rec


def mpz_pow(P, s):
    return AB.mpz(P) ** s


# ------------------------------------------------------------------ build
def wgrid(g, N, M, a, b):
    return [[(a * (i - N) + b * (j - M)) * g[i][j] for j in range(2 * M + 1)] for i in range(2 * N + 1)]


def hcoef(p, a):
    return [(q, 0, b, c, d) for (q, aa, b, c, d) in p if aa == a]


def build(verbose=True):
    cdata = EA.lean_src(DT.data_module())
    Nc, Mc, Sc, Fc = (EA.parse_nat(cdata, x) for x in ('Nc', 'Mc', 'Sc', 'Fc'))
    Iqc, Qc = EA.parse_nat(cdata, 'Iqc'), EA.parse_nat(cdata, 'Qc')
    gU = EA.full_grid_from_rows(EA.parse_rows(cdata, 'datU'), Nc, Mc, Fc, 0)
    gZ = EA.full_grid_from_rows(EA.parse_rows(cdata, 'datZ'), Nc, Mc, Fc, 1)
    fd = EA.lean_src('DommaschkKamFieldData.lean')
    polys = {k: EA.parse_sp(fd, k) for k in ('dDR', 'dnRh', 'dnZR')}
    N, M, S = Nc, Mc, Sc
    pl = RPipe(N, M, S, P_EXP, E_EXP)
    T0 = time.time()

    def rep(r):
        if verbose:
            v = r.get('var')
            print('  %-5s b=%d W=%d R=%d img=%.1fMbit E=%.3e B=%s %.1fs' % (
                r['name'], r['b'], r['W'], r['R'], r['W'] * r['R'] * r['b'] / 1e6, float(r['rad']),
                '%.4g' % float(pl.B[v]) if v is not None else '-', time.time() - T0))
            sys.stdout.flush()
        return r.get('var')
    t = pl.add_const('T', 't')
    V = pl.add_const('V', 'V')
    pl.add_const('C', 'C')
    pl.add_const('S', 'S')
    U = pl.data(gU, 0, 'U')
    Z = pl.data(gZ, 1, 'Z')
    LUx = pl.data(wgrid(gU, N, M, -Iqc, 2 ** (Qc + 1)), 3, 'LUx')
    LZx = pl.data(wgrid(gZ, N, M, -Iqc, 2 ** (Qc + 1)), 0, 'LZx')
    assert (U, Z, LUx, LZx) == (4, 5, 6, 7)
    mul = lambda i, j: ('mul', ('var', i), ('var', j))            # noqa: E731
    R = rep(pl.node('R', ('add', ('mul', ('cst', 29), ('var', t)), ('mul', ('cst', 32), ('var', U))), 32))
    s = rep(pl.node('s', mul(R, R), 1))
    Zp = {0: t, 1: Z}
    for b in range(2, 6):
        Zp[b] = rep(pl.node('z%d' % b, mul(Zp[b - 1], Z), 1))
    LU = rep(pl.node('LU', ('var', LUx), 2 ** Qc))
    LZ = rep(pl.node('LZ', ('var', LZx), 2 ** Qc))
    assert (R, s, Zp[2], Zp[5], LU, LZ) == (8, 9, 10, 13, 14, 15)
    mono = lambda a, b: Zp[b]                                      # noqa: E731
    chains = {}
    for key, pname, sh in POLYS:
        p = polys[pname]
        ks = sorted({(tm[1] - sh) // 2 for tm in p})
        assert all((tm[1] - sh) % 2 == 0 and tm[1] >= sh for tm in p)
        top = max(ks)
        H = None
        recs = []
        for k in range(top, -1, -1):
            h = hcoef(p, 2 * k + sh)
            Ph = None
            if h:
                L = EA.sp_lcm(h)
                Ph = rep(pl.node('%sc%d' % (key, k), AB.polyT(Fr(L), 3, mono, h), L,
                                 rel=('coef', key, k, L)))
                recs.append(Ph)
            if H is None:
                assert Ph is not None
                H = Ph
                continue
            e = mul(H, s)
            if Ph is not None:
                e = ('add', e, mul(Ph, t))
            H = rep(pl.node('%s%d' % (key, k), e, 1, rel=('hor', key, k, Ph is not None)))
        chains[key] = dict(top=top, final=H, pname=pname, sh=sh)
    D, G, F = chains['D']['final'], chains['G']['final'], chains['F']['final']
    nr = pl.node('NR', ('sub', mul(D, LU), mul(R, G)), 0)
    nz = pl.node('NZ', ('sub', mul(D, LZ), mul(s, F)), 0)
    if verbose:
        print('  NR %.3e  NZ %.3e (b %d, %d)' % (float(nr['rad']), float(nz['rad']), nr['b'], nz['b']))
    idx = dict(t=t, V=V, U=U, Z=Z, LUx=LUx, LZx=LZx, R=R, s=s, Zp=Zp, LU=LU, LZ=LZ, chains=chains, D=D, G=G,
               F=F)
    ctx = dict(Nc=Nc, Mc=Mc, Sc=Sc, Fc=Fc, Iqc=Iqc, Qc=Qc, gU=gU, gZ=gZ, polys=polys)
    return pl, idx, dict(NR=nr, NZ=nz), ctx


def certify(pl, idx, norms, ctx):
    """e0q: the norm-node bounds plus the iota - iota_q correction 2^-Q ||D|| ||d_theta x||, with
    ||d_theta x||_{9/200} <= 75 ||x||_{1/20} (Cauchy, delta = 1/200, 1/(e delta) <= 75)."""
    c1 = {k: pl.center_check(idx[k], P1_EXP) for k in ('U', 'Z')}
    D = idx['D']
    bD = pl.B[D] + pl.E[D]
    corr = {k: Fr(1, 2 ** ctx['Qc']) * bD * 75 * c1[k]['Bq'] for k in ('U', 'Z')}
    eR = norms['NR']['bound'] + corr['U']
    eZ = norms['NZ']['bound'] + corr['Z']
    e0q = AB.up(max(eR, eZ), 2)
    assert e0q >= eR and e0q >= eZ
    return dict(c1=c1, corr=corr, eR=eR, eZ=eZ, e0q=e0q, bD=bD)


# ======================================================================================== Lean emission
def tree_lean(e):
    return EA.tree_lean(e)


def wrap_list(items, width=98):
    lines, cur = [], ''
    for it in items:
        piece = it if not cur else ', ' + it
        if len(cur) + len(piece) > width:
            lines.append(cur + ',')
            cur = it
        else:
            cur += piece
    lines.append(cur)
    return '\n'.join(lines)


def hexrows(rows):
    return ',\n'.join('  (%d, %d, %d, 0x%x)' % r for r in rows)


class Emit:
    def __init__(self, pl, idx, norms, ctx, cert):
        self.pl, self.idx, self.norms, self.ctx, self.cert = pl, idx, norms, ctx, cert
        self.N, self.M, self.S = pl.N, pl.M, pl.S
        self.nvar = pl.nvar
        self.nodes = {s['n']: s for s in pl.steps if s.get('kind') == 'node'}
        self.files = []
        self.datamods, self.checkmods, self.eqmods = [], [], []
        self.ltree = {}
        for n, r in self.nodes.items():
            rel = r['rel']
            if rel and rel[0] == 'coef':
                key, k, L = rel[1], rel[2], rel[3]
                pk = [x[0] for x in POLYS].index(key)
                sh = POLYS[pk][2]
                self.ltree[n] = 'polyT (%d : ℚ) 3 monoH (hcoefH (polyH %d) %d)' % (L, pk, 2 * k + sh)
            else:
                self.ltree[n] = tree_lean(r['tree'])

    def nm(self, i):
        return self.pl.names[i]

    def write(self, mod, text):
        mod, text = DT.out_name(mod), DT.retarget(text)
        open(os.path.join(OUT, mod + '.lean'), 'w').write(text)
        self.files.append(mod)

    # ---------------------------------------------------------------- data
    def emit_data(self, per=7, write=True):
        ids = [i for i in range(4, self.nvar)]
        groups = [ids[k:k + per] for k in range(0, len(ids), per)]
        self.datamods = ['DommaschkKamCResData%d' % (f + 1) for f in range(len(groups))]
        if not write:
            return
        for f, grp in enumerate(groups):
            out = [HEADER, 'public import Mathlib.Data.List.Basic\n', """
/-!
# Data of the torus-C residual chain (part %d)

Salted packed rows (`Design/DommaschkKamCResKron`, `RowR = (lo, cnt, F, x)`: the entries
`lo, …, lo + cnt − 1` of row `j` as fields of width `F` with offset `2^{F−1}`, above a
random `64`-bit salt) of the centres of the high-resolution ball chain of Dommaschk torus C
(`Design/DommaschkKamCResEnv`; layout `N × M = 96 × 80`, scale `2^{−128}`). Generated by
the untrusted oracle `scripts/dommaschk_kam/emit_res.py`; nothing here is trusted.
-/

@[expose] public section

namespace %s

""" % (f + 1, NS)]
            for i in grp:
                out.append('set_option linter.style.longLine false in\n/-- Salted rows of the centre `%s`. -/\n'
                           'def rowsH_%s : List (ℕ × ℕ × ℕ × ℕ) := [\n%s]\n\n' % (
                               self.nm(i), self.nm(i), hexrows(self.pl.rows[i])))
            out.append('end %s\n' % NS)
            self.write(self.datamods[f], ''.join(out))

    # ---------------------------------------------------------------- env
    def emit_env(self):
        pl = self.pl
        NV = self.nvar
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResKron\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.datamods]
        out.append("""
/-!
# The ball environment of the torus-C residual chain

The variables of the high-resolution ball chain of Dommaschk torus C (N-33 plan item 7): layout
`N = 96`, `M = 80` (the box of the data torus), scale `2^{−128}`, oracle angle `ψₒ = 2φ`, strip
weights `68553^s 2^{16(K − s)}` (`e^r ≤ 68553/2^16`, `Design/DommaschkKamCKronW`). The grids are
salted packed rows (`rowsH i`, `Design/DommaschkKamCResKron`); their polynomials `PlH i`,
weights `WtH i`, boxes `BxH i`, static `ℓ¹` bounds `LH i = rowsL1 (rowsH i)`, Kronecker images
`KvH b W i` (`imgR` for `b ≥ 1`), the honest centres `xH i`, the norm bounds `BH i` and radii
`EH i` (supplied by the oracle `scripts/dommaschk_kam/emit_res.py`, checked in
`Design/DommaschkKamCResCheck*` and `Design/DommaschkKamCResChain`), and the monomial table
`monoH` (`z^b`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos ψₒ`, `sin ψₒ`; `4 … 7` the data `U`, `Z`,
`LUx`, `LZx`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- Layout: poloidal half width. -/
def NH : ℕ := %d
/-- Layout: toroidal half width. -/
def MH : ℕ := %d
/-- Layout: scale exponent. -/
def SH : ℕ := %d

""" % (NS, OPEN, self.N, self.M, self.S))
        names = ['[]'] * 4 + ['rowsH_%s' % self.nm(i) for i in range(4, NV)]
        out.append('/-- The salted rows of the variables (list; the constants have none). -/\n'
                   'def rowsHl : List (List RowR) :=%s\n\n' % EA.lst(names))
        out.append("""/-- The salted rows of variable `i`. -/
def rowsH (i : ℕ) : List RowR := rowsHl.getD i []

/-- The polynomials of the variables. -/
def PlH : ℕ → P2
  | 0 => Tpoly SH NH MH
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NH MH (gridR (rowsH (n + 4)))

""")
        out.append('/-- The weights of the variables (list). -/\ndef WtHl : List (ℕ × ℕ × ℕ) :=%s\n\n' %
                   EA.lst(['(%d, %d, %d)' % pl.W[i] for i in range(NV)]))
        out.append("""/-- The weights of the variables. -/
def WtH (i : ℕ) : ℕ × ℕ × ℕ := WtHl.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def BxH : ℕ → ℕ × ℕ
  | 0 => (NH, MH)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * NH, 2 * MH)

/-- The static `ℓ¹` bounds of the variable polynomials. -/
def LH : ℕ → ℕ
  | 0 => 2 ^ SH
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | n + 4 => rowsL1 (rowsH (n + 4))

/-- The Kronecker images of the variable polynomials (fast row images for `b ≥ 1`). -/
def KvH (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SH * ((1 <<< (b * (NH + W * MH)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => cond (Nat.ble 1 b) (imgR b W (rowsH (n + 4)) (2 * MH + 1))
      (packGridNM b W NH (gridR (rowsH (n + 4))) (2 * MH + 1))

/-- The honest centres. -/
def xH (i : ℕ) : FA := ctr SH NH MH (WtH i) (PlH i)

/-- The phases are below `4`. -/
theorem hWH : ∀ i, (WtH i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxH : ∀ i, InBox (PlH i) (BxH i).1 (BxH i).2
  | 0 => InBox.monomial NH MH _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NH MH _

/-- `ℓ¹` bounds. -/
theorem l1H : ∀ i, l1 (PlH i) ≤ LH i
  | 0 => l1_Tpoly SH NH MH
  | 1 => l1_Vpoly
  | 2 => l1_sPoly
  | 3 => l1_cPoly
  | _ + 4 => l1_gridR_le NH MH _

/-- All rows lie in the box. -/
theorem rowsH_ok : ∀ rs ∈ rowsHl, rowsOK NH rs = true := by kernel_fact

/-- The rows of every variable lie in the box. -/
theorem rowsH_ok' (i : ℕ) : rowsOK NH (rowsH i) = true :=
  getD_prop (Pr := fun rs => rowsOK NH rs = true) rowsH_ok rfl i

/-- The Kronecker images. -/
theorem kronH : ∀ b W i, kron b W (PlH i) = KvH b W i
  | b, W, 0 => kron_Tpoly SH NH MH b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, n + 4 => by
    change kron b W (gridPolyNM NH MH (gridR (rowsH (n + 4)))) =
      cond (Nat.ble 1 b) (imgR b W (rowsH (n + 4)) (2 * MH + 1))
        (packGridNM b W NH (gridR (rowsH (n + 4))) (2 * MH + 1))
    rcases Nat.lt_or_ge b 1 with hb | hb
    · have h : Nat.ble 1 b = false := Bool.eq_false_iff.2 fun h => by
        have := Nat.le_of_ble_eq_true h; omega
      rw [h, Bool.cond_false, kron_gridPolyNM]
    · rw [Nat.ble_eq_true_of_le hb, Bool.cond_true]
      exact kron_gridR b W NH MH hb (by norm_num [MH]) _ (rowsH_ok' _)

/-- The centre of `t` is `1`. -/
theorem xH_t : xH 0 = 1 := ctr_Tpoly SH NH MH

/-- The centre of `V` is `1`. -/
theorem xH_V : xH 1 = 1 := ctr_Vpoly SH NH MH

/-- The centre of `C` is `cos ψₒ`. -/
theorem xH_C : xH 2 = cSo := ctr_C_o SH NH MH

/-- The centre of `S` is `sin ψₒ`. -/
theorem xH_S : xH 3 = sSo := ctr_S_o SH NH MH

""")
        out.append('/-- The norm bounds of the centres (list). -/\ndef BHl : List ℚ :=%s\n\n' %
                   EA.lst([qlean(pl.B[i]) for i in range(NV)]))
        out.append('/-- The norm bounds of the centres. -/\ndef BH (i : ℕ) : ℚ := BHl.getD i 0\n\n')
        out.append('/-- The radii of the balls (list). -/\ndef EHl : List ℚ :=%s\n\n' %
                   EA.lst([qlean(pl.E[i]) for i in range(NV)]))
        out.append("""/-- The radii of the balls. -/
def EH (i : ℕ) : ℚ := EHl.getD i 0

/-- The monomial table: the variable of `z^b` (`b ≤ 5`; `t` for `b = 0`). -/
def monoH (_a b : ℕ) : ℕ := [0, 5, 10, 11, 12, 13].getD b 0

end %s
""" % NS)
        self.write('DommaschkKamCResEnv', ''.join(out))

    # ---------------------------------------------------------------- trees
    def emit_trees(self):
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResEnv\n', """
/-!
# Expression trees of the torus-C residual chain

The trees of the nodes of the high-resolution ball chain of Dommaschk torus C: the coefficient nodes
are `polyT` trees (`Design/DommaschkKamCKronW`) of the `s`-coefficients `hcoefH p a` of the `R`-form
field polynomials `dDR`, `dnRh`, `dnZR` (the terms with `R^a`, `a` set to `0`), the Horner nodes are
`s H + Pc t`; `horH p sh n k` is the polynomial of the Horner value `H_k` (top index `k + n`).
Generated by `scripts/dommaschk_kam/emit_res.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- The `R`-form polynomials of the residual: `D = dDR`, `G = dnRh` (`n_R = R G`), `dnZR`. -/
def polyH : ℕ → DkPoly.SP
  | 0 => dDR
  | 1 => dnRh
  | 2 => dnZR
  | _ => []

/-- The coefficient of `R^a` (the terms with exponent `a`, exponent set to `0`). -/
def hcoefH (p : DkPoly.SP) (a : ℕ) : DkPoly.SP :=
  (p.filter fun t => t.a == a).map fun t => ⟨t.q, 0, t.b, t.c, t.d⟩

/-- The Horner polynomial `∑_{m ≤ n} R^{2m} hcoefH p (2(k + m) + sh)`. -/
def horH (p : DkPoly.SP) (sh : ℕ) : ℕ → ℕ → DkPoly.SP
  | 0, k => hcoefH p (2 * k + sh)
  | n + 1, k => hcoefH p (2 * k + sh) ++ DkPoly.mulMono ⟨1, 2, 0, 0, 0⟩ (horH p sh n (k + 1))

""" % (NS, OPEN)]
        for n in sorted(self.nodes):
            out.append('set_option linter.style.longLine false in\n/-- Expression tree of the node `%s` '
                       '(variable `%d`). -/\ndef trH_%s : Ex :=\n  %s\n\n' % (
                           self.nm(n), n, self.nm(n), self.ltree[n]))
        for k in ('NR', 'NZ'):
            out.append('/-- Expression tree of the norm node `%s`. -/\ndef trH_%s : Ex :=\n  %s\n\n' % (
                k, k, tree_lean(self.norms[k]['tree'])))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamCResTrees', ''.join(out))

    # ---------------------------------------------------------------- checks
    def check_items(self):
        pl = self.pl
        items = []
        for i in (4, 5, 6, 7):
            r = pl.normrec[i]
            items.append(('center', i, r, 'cH_%s' % self.nm(i), 'clH_%s' % self.nm(i), 2.0))
        for key in ('U', 'Z'):
            i = self.idx[key]
            r = self.cert['c1'][key]
            items.append(('center1', i, r, 'c1H_%s' % key, None, 2.0))
        for n in sorted(self.nodes):
            r = self.nodes[n]
            cost = r['W'] * r['R'] / 1e4
            items.append(('node', n, r, 'kH_%s' % self.nm(n), 'lH_%s' % self.nm(n), cost))
        for k in ('NR', 'NZ'):
            r = self.norms[k]
            items.append(('norm', k, r, 'nH_%s' % k, 'nlH_%s' % k, r['W'] * r['R'] / 1e4 * 1.3))
        return items

    def item_text(self, it):
        kind, i, r, nmK, nmL, _ = it
        if kind == 'center':
            return ("""set_option linter.style.longLine false in
/-- Proof-term check of the norm of the centre `%s`. -/
theorem %s : centerKw %d %d NH MH KvH %d %d %d %d %d %d %d ≤ %d := by
  kron2_proof

/-- A priori `ℓ¹` bound of the centre `%s`. -/
theorem %s : LH %d < 2 ^ (%d - 1) := by
  kron_lt

""" % (self.nm(i), nmK, P_EXP, E_EXP, i, r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'],
                self.nm(i), nmL, i, r['b']))
        if kind == 'center1':
            return ("""set_option linter.style.longLine false in
/-- Proof-term check of the norm of the centre `%s` on the strip `e^r ≤ %d/2^16`. -/
theorem %s : centerKw %d %d NH MH KvH %d %d %d %d %d %d %d ≤ %d := by
  kron2_proof

""" % (self.nm(i), r['P'], nmK, r['P'], E_EXP, i, r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K']))
        if kind == 'node':
            return ("""set_option linter.style.longLine false in
/-- Proof-term check of the node `%s`: truncation norm. -/
theorem %s : nodeKw %d %d SH NH MH WtH KvH trH_%s (%d : ℤ) %d %d %d %d %d %d %d %d %d %d ≤ %d := by
  kron2_proof

set_option linter.style.longLine false in
/-- Proof-term check of the node `%s`: a priori `ℓ¹` bound. -/
theorem %s : nodeL1 SH LH trH_%s (%d : ℤ) %d %d %d < 2 ^ (%d - 1) := by
  kron_lt

""" % (self.nm(i), nmK, P_EXP, E_EXP, self.nm(i), r['c'], r['dd'], r['de'], i, r['b'], r['W'], r['dc'], r['dr'],
                r['J'], r['Ki'], r['Kj'], r['K'], self.nm(i), nmL, self.nm(i), r['c'], r['dd'], r['de'], i, r['b']))
        return ("""set_option linter.style.longLine false in
/-- Proof-term check of the norm node `%s`. -/
theorem %s : normKw %d %d NH MH WtH KvH trH_%s (%d, %d, %d) %d %d %d %d %d %d %d ≤ %d := by
  kron2_proof

/-- A priori `ℓ¹` bound of the norm node `%s`. -/
theorem %s : Ex.majN LH trH_%s < 2 ^ (%d - 1) := by
  kron_lt

""" % (i, nmK, P_EXP, E_EXP, i, r['w'][0], r['w'][1], r['w'][2], r['b'], r['W'], r['dc'], r['dr'], r['J'],
            r['Ki'], r['Kj'], r['K'], i, nmL, i, r['b']))

    def emit_checks(self, ncheck, write=True):
        items = self.check_items()
        tot = sum(it[5] for it in items)
        target = tot / ncheck
        groups, cur, acc = [], [], 0.0
        for it in items:
            if cur and acc + it[5] > target * 1.05 and len(groups) < ncheck - 1:
                groups.append(cur)
                cur, acc = [], 0.0
            cur.append(it)
            acc += it[5]
        if cur:
            groups.append(cur)
        self.checkmods = ['DommaschkKamCResCheck%d' % (f + 1) for f in range(len(groups))]
        self.checkgroups = groups
        if not write:
            return
        for f, grp in enumerate(groups):
            out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResTrees\n',
                   'public import PlasmaLean.Certificates.KronProof2D\n',
                   'meta import PlasmaLean.Design.DommaschkKamCResTrees\n', """
/-!
# Proof-term checks of the torus-C residual chain (part %d)

Each theorem is an explicit proof term (`kron2_proof` of `Certificates/KronProof2D`; `kron_lt` for
the `ℓ¹` bounds) on the salted rows of `Design/DommaschkKamCResData*`: the weighted digit sums
(`nodeKw`, `normKw`, `centerKw` of `Design/DommaschkKamCKronW`, strip weights `68553^s 2^{16(K−s)}`)
of the Kronecker images (`imgR`, `Design/DommaschkKamCResKron`) of the truncation polynomials of the
ball chain, and their a priori `ℓ¹` bounds. Generated by `scripts/dommaschk_kam/emit_res.py`.
Checks:
%s.
-/

@[expose] public section

namespace %s

%s
""" % (f + 1, wrap_list(['`%s`' % it[3] for it in grp]), NS, OPEN)]
            for it in grp:
                out.append(self.item_text(it))
            out.append('end %s\n' % NS)
            self.write(self.checkmods[f], ''.join(out))

    # ---------------------------------------------------------------- equality checks
    def emit_eq(self, write=True):
        M = self.M
        blocks = [(j0, min(EQ_BLOCK, 2 * M + 1 - j0)) for j0 in range(0, 2 * M + 1, EQ_BLOCK)]
        self.eqblocks = blocks
        self.eqmods = ['DommaschkKamCResEqU', 'DommaschkKamCResEqZ']
        if not write:
            return
        for which, g, nmU, nmL in (('U', 'gU', 'U', 'LUx'), ('Z', 'gZ', 'Z', 'LZx')):
            out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResEnv\n', """
/-!
# Identity of the residual-chain data `%s`, `%s` with the data torus C

Kernel checks, by blocks of rows, that the salted rows `rowsH_%s` and `rowsH_%s`
(`Design/DommaschkKamCResData*`) are the grid `%s` of the data torus
(`Design/DommaschkKamCTorus`) and its weighted grid `(−Iqc (i − N) + 2^{Qc+1} (j − M)) %s`
(the derivative `2^{Qc} 𝓛_{ι_q}`, `dS_ctr_grid`). Generated by
`scripts/dommaschk_kam/emit_res.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- The weighted grid of `%s`: `2^{Qc} 𝓛_{ι_q}` (`ι_q = −Iqc/2^{Qc}`). -/
def wg%s : ℕ → ℕ → ℤ :=
  fun i j => ((-(Iqc : ℤ)) * ((i : ℤ) - NH) + (2 : ℤ) ^ (Qc + 1) * ((j : ℤ) - MH)) * %s i j

""" % (nmU, nmL, nmU, nmL, g, g, NS, OPEN, g, which, g)]
            for k, (j0, nj) in enumerate(blocks):
                out.append("""set_option linter.style.longLine false in
/-- Rows `%d … %d` of `%s` and `%s`. -/
theorem eqH_%s_%d : chkGrid NH (gridR rowsH_%s) %s %d %d = true ∧
    chkGrid NH (gridR rowsH_%s) wg%s %d %d = true := by
  kernel_fact

""" % (j0, j0 + nj - 1, nmU, nmL, which, k, nmU, g, j0, nj, nmL, which, j0, nj))
            # combination
            cases = []
            for k, (j0, nj) in enumerate(blocks):
                cases.append((k, j0, nj))
            body = []
            body.append('  intro j hj i hi')
            body.append('  have hj\' : j < %d := by simpa [MH] using hj' % (2 * M + 1))
            body.append('  rcases (show %s by omega) with %s' % (
                ' ∨ '.join('(%d ≤ j ∧ j < %d)' % (j0, j0 + nj) for _, j0, nj in cases),
                ' | '.join('h' for _ in cases)))
            for k, j0, nj in cases:
                body.append('  · obtain ⟨dj, rfl⟩ : ∃ dj, j = %d + dj := ⟨j - %d, by omega⟩' % (j0, j0))
                body.append('    exact ⟨chkGrid_sound eqH_%s_%d.1 dj (by omega) i hi, '
                            'chkGrid_sound eqH_%s_%d.2 dj (by omega) i hi⟩' % (which, k, which, k))
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- **The rows of `%s` and `%s` are the data grids.** -/
theorem eqH_%s : ∀ j < 2 * MH + 1, ∀ i < 2 * NH + 1,
    gridR rowsH_%s i j = %s i j ∧ gridR rowsH_%s i j = wg%s i j := by
%s

""" % (nmU, nmL, which, nmU, g, nmL, which, '\n'.join(body)))
            out.append('end %s\n' % NS)
            self.write('DommaschkKamCResEq%s' % which, ''.join(out))

    # ---------------------------------------------------------------- honest values and relations
    def honest(self, i):
        pl = self.pl
        nm = self.nm(i)
        fixed = {0: '1', 1: '1', 2: 'cSo', 3: 'sSo', 4: 'Uo', 5: 'Zo', 6: 'LUv', 7: 'LZv', 8: 'RvH',
                 9: 'RvH * RvH', 10: 'Zo ^ 2', 11: 'Zo ^ 3', 12: 'Zo ^ 4', 13: 'Zo ^ 5',
                 14: '((2 : ℂ) ^ Qc)⁻¹ • LUv', 15: '((2 : ℂ) ^ Qc)⁻¹ • LZv'}
        if i in fixed:
            return fixed[i]
        rel = self.nodes[i]['rel']
        key, k = rel[1], rel[2]
        pk = [x[0] for x in POLYS].index(key)
        sh = POLYS[pk][2]
        top = self.idx['chains'][key]['top']
        if rel[0] == 'coef' and k == top:
            return 'DkPoly.ev xRH (horH (polyH %d) %d 0 %d)' % (pk, sh, k)
        if rel[0] == 'coef':
            return 'DkPoly.ev xRH (hcoefH (polyH %d) %d)' % (pk, 2 * k + sh)
        return 'DkPoly.ev xRH (horH (polyH %d) %d %d %d)' % (pk, sh, top - k, k)

    def rel_text(self, n):
        r = self.nodes[n]
        nm = self.nm(n)
        rel = r['rel']
        head = ('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
                '/-- The identity of the node `%s`. -/\ntheorem relH_%s : ((%d : ℤ) : ℂ) • XH %d = '
                'Ex.eval XH trH_%s := by\n' % (nm, nm, r['c'], n, nm))
        if nm == 'R':
            return head + """  have e0 : XH 0 = 1 := rfl
  have e4 : XH 4 = Uo := rfl
  have e8 : XH 8 = RvH := rfl
  simp only [trH_R, Ex.eval, e8, e0, e4, RvH, R0q]
  rw [smul_add, Algebra.smul_def, ← map_mul]
  have h : (((32 : ℤ) : ℂ) * (((29 / 32 : ℚ) : ℚ) : ℂ)) = 29 := by push_cast; norm_num
  rw [h]
  simp only [Algebra.smul_def, map_ofNat, Int.cast_ofNat, mul_one]

"""
        if nm == 's':
            return head + """  have e8 : XH 8 = RvH := rfl
  have e9 : XH 9 = RvH * RvH := rfl
  simp only [trH_s, Ex.eval, e8, e9, Int.cast_one, one_smul]

"""
        if nm in ('z2', 'z3', 'z4', 'z5'):
            b = int(nm[1])
            prev = {2: (5, 'Zo'), 3: (10, 'Zo ^ 2'), 4: (11, 'Zo ^ 3'), 5: (12, 'Zo ^ 4')}[b]
            if b == 2:
                return head + """  have e5 : XH 5 = Zo := rfl
  have en : XH %d = Zo ^ 2 := rfl
  simp only [trH_%s, Ex.eval, e5, en, Int.cast_one, one_smul]
  ring

""" % (n, nm)
            return head + """  have e5 : XH 5 = Zo := rfl
  have ep : XH %d = %s := rfl
  have en : XH %d = Zo ^ %d := rfl
  simp only [trH_%s, Ex.eval, e5, ep, en, Int.cast_one, one_smul]
  ring

""" % (prev[0], prev[1], n, b, nm)
        if nm in ('LU', 'LZ'):
            src = 6 if nm == 'LU' else 7
            v = 'LUv' if nm == 'LU' else 'LZv'
            return head + """  have es : XH %d = %s := rfl
  have en : XH %d = ((2 : ℂ) ^ Qc)⁻¹ • %s := rfl
  simp only [trH_%s, Ex.eval, es, en, smul_smul]
  rw [show (((%d : ℤ) : ℂ) * ((2 : ℂ) ^ Qc)⁻¹) = 1 by norm_num [Qc], one_smul]

""" % (src, v, n, v, nm, r['c'])
        key, k = rel[1], rel[2]
        pk = [x[0] for x in POLYS].index(key)
        sh = POLYS[pk][2]
        top = self.idx['chains'][key]['top']
        if rel[0] == 'coef':
            L = rel[3]
            a = 2 * k + sh
            if k == top:
                hn = 'rfl'
            else:
                hn = 'rfl'
            return head + ('  exact relCoefH (L := (%d : ℚ)) (p := polyH %d) (a := %d) (by norm_num) %s '
                           '(by kernel_fact)\n    (by kernel_fact) (by kernel_fact)\n\n' % (L, pk, a, hn))
        # Horner node
        Hn = self.nodes[n]['tree']
        # tree: ('add', mul(H, s), mul(Ph, t)) or mul(H, s)
        if Hn[0] == 'add':
            iH = Hn[1][1][1]
            iP = Hn[2][1][1]
            return head + ('  exact relHorH (p := polyH %d) (sh := %d) (n := %d) (k := %d) (iH := %d) (iP := %d) '
                           'rfl rfl rfl\n\n' % (pk, sh, top - k - 1, k, iH, iP))
        iH = Hn[1][1]
        return head + ('  exact relHor0H (p := polyH %d) (sh := %d) (n := %d) (k := %d) (iH := %d) rfl rfl '
                       '(by kernel_fact)\n\n' % (pk, sh, top - k - 1, k, iH))

    def emit_rel(self):
        NV = self.nvar
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResTrees\n', """
/-!
# Honest values of the torus-C residual chain

The value `XH i` of each variable of the high-resolution ball chain of Dommaschk torus C, at
the data torus `(Uo, Zo)` (oracle angle, `Design/DommaschkKamCTorus`): `R = R₀ + U` (`RvH`),
`s = R²`, `z^b`, `LUv = 2^{Qc} 𝓛_{ι_q} U` and `LZv` (exact), `LU = LUv/2^{Qc}`, the coefficient
values `ev xRH (hcoefH p a)` and the Horner values `ev xRH (horH p sh n k)`
(`xRH = (R, z, cos ψₒ, sin ψₒ)`); and the identity of every node `c · X n = eval X e` (`relH_*`):
by `ring`, by `eval_polyT` for the coefficient trees (`relCoefH`) and by the Horner step of
`horH` (`relHorH`, `relHor0H`). Generated by `scripts/dommaschk_kam/emit_res.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- `R = R₀ + U` at the data torus (oracle angle). -/
def RvH : FA := algebraMap ℂ FA ((R0q : ℚ) : ℂ) + Uo

/-- The `R`-form evaluation point `(R, z, cos ψₒ, sin ψₒ, 0, 0)`. -/
def xRH : Fin 6 → FA := ![RvH, Zo, cSo, sSo, 0, 0]

/-- `2^{Qc} 𝓛_{ι_q} U = dS (−Iqc) 2^{Qc+1} U` (exact). -/
def LUv : FA := dS ((-(Iqc : ℤ) : ℤ) : ℂ) (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) Uo

/-- `2^{Qc} 𝓛_{ι_q} z` (exact). -/
def LZv : FA := dS ((-(Iqc : ℤ) : ℤ) : ℂ) (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) Zo

""" % (NS, OPEN)]
        out.append('set_option maxHeartbeats 4000000 in\n-- elaborating a literal list of strip-algebra '
                   'elements\n/-- The honest values of the variables (list). -/\ndef XHl : List FA :=%s\n\n' %
                   EA.lst([self.honest(i) for i in range(NV)]))
        out.append("""/-- The honest values of the variables. -/
def XH (i : ℕ) : FA := XHl.getD i 0

set_option maxRecDepth 100000 in
/-- The monomial variables have the values `z^b`. -/
theorem XH_mono : ∀ b ≤ 5, XH (monoH 0 b) = xRH 0 ^ 0 * xRH 1 ^ b := by
  intro b hb
  interval_cases b
  · change (1 : FA) = _; simp
  · change Zo = _; simp [xRH]
  · change Zo ^ 2 = _; simp [xRH]
  · change Zo ^ 3 = _; simp [xRH]
  · change Zo ^ 4 = _; simp [xRH]
  · change Zo ^ 5 = _; simp [xRH]

/-- The terms of a coefficient polynomial have `a = 0`. -/
theorem hcoefH_a (p : DkPoly.SP) (a : ℕ) :
    ∀ t ∈ hcoefH p a, t.a = 0 ∧ t.b ≤ p.foldr (fun s m => max s.b m) 0 := by
  intro t ht
  simp only [hcoefH, List.mem_map, List.mem_filter] at ht
  obtain ⟨s, ⟨hs, _⟩, rfl⟩ := ht
  refine ⟨rfl, ?_⟩
  clear * - hs
  induction p with
  | nil => simp at hs
  | cons u p ih =>
    simp only [List.mem_cons] at hs
    simp only [List.foldr_cons]
    rcases hs with rfl | hs
    · exact le_max_left _ _
    · exact (ih hs).trans (le_max_right _ _)

/-- **The identity of a coefficient node** (`polyT` tree of `hcoefH p a`). -/
theorem relCoefH {n : ℕ} {L : ℚ} {c : ℤ} {p : DkPoly.SP} {a : ℕ} (hc : (c : ℚ) = L)
    (hn : XH n = DkPoly.ev xRH (hcoefH p a)) (hne : 0 < (hcoefH p a).length)
    (hint : ∀ t ∈ hcoefH p a, (L * t.q).den = 1) (hb : p.foldr (fun s m => max s.b m) 0 ≤ 5) :
    (c : ℂ) • XH n = Ex.eval XH (polyT L 3 monoH (hcoefH p a)) := by
  rw [eval_polyT XH rfl xRH rfl rfl L 3 monoH _ (List.ne_nil_of_length_pos hne) hint ?_, hn, ← hc]
  · push_cast; rfl
  · intro t ht
    obtain ⟨h1, h2⟩ := hcoefH_a p a t ht
    rw [h1]
    exact XH_mono t.b (h2.trans hb)

/-- The Horner polynomial: one step. -/
theorem ev_horH_succ (p : DkPoly.SP) (sh n k : ℕ) :
    DkPoly.ev xRH (horH p sh (n + 1) k) =
      DkPoly.ev xRH (hcoefH p (2 * k + sh)) + RvH * RvH * DkPoly.ev xRH (horH p sh n (k + 1)) := by
  rw [horH, DkPoly.ev_append, DkPoly.ev_mulMono]
  congr 1
  simp [DkPoly.Tm.ev, xRH, sq]

/-- **The identity of a Horner node** `H_k = s H_{k+1} + Pc_k t`. -/
theorem relHorH {p : DkPoly.SP} {sh n k iH iP m : ℕ}
    (hH : XH iH = DkPoly.ev xRH (horH p sh n (k + 1)))
    (hP : XH iP = DkPoly.ev xRH (hcoefH p (2 * k + sh)))
    (hm : XH m = DkPoly.ev xRH (horH p sh (n + 1) k)) :
    ((1 : ℤ) : ℂ) • XH m =
      Ex.eval XH (.add (.mul (.var iH) (.var 9)) (.mul (.var iP) (.var 0))) := by
  have e9 : XH 9 = RvH * RvH := rfl
  have e0 : XH 0 = 1 := rfl
  simp only [Ex.eval, hH, hP, hm, e9, e0, ev_horH_succ, Int.cast_one, one_smul, mul_one]
  ring

/-- **The identity of a Horner node without coefficient** `H_k = s H_{k+1}`. -/
theorem relHor0H {p : DkPoly.SP} {sh n k iH m : ℕ}
    (hH : XH iH = DkPoly.ev xRH (horH p sh n (k + 1)))
    (hm : XH m = DkPoly.ev xRH (horH p sh (n + 1) k)) (h0 : hcoefH p (2 * k + sh) = []) :
    ((1 : ℤ) : ℂ) • XH m = Ex.eval XH (.mul (.var iH) (.var 9)) := by
  have e9 : XH 9 = RvH * RvH := rfl
  simp only [Ex.eval, hH, hm, e9, ev_horH_succ, h0, DkPoly.ev_nil, zero_add, Int.cast_one, one_smul]
  ring

""")
        for n in sorted(self.nodes):
            out.append(self.rel_text(n))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamCResRel', ''.join(out))

    # ---------------------------------------------------------------- chain
    def emit_chain(self):
        pl = self.pl
        NV = self.nvar
        out = [HEADER, 'public import PlasmaLean.Design.DommaschkKamCResRel\n',
               'public import PlasmaLean.Design.DommaschkKamCResEqU\n',
               'public import PlasmaLean.Design.DommaschkKamCResEqZ\n']
        out += ['public import PlasmaLean.Design.%s\n' % m for m in self.checkmods]
        hyp = '{r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (68553 : ℕ) / 2 ^ 16)'
        out.append("""
/-!
# The high-resolution ball chain of torus C

The norms of the centres and the balls `‖X i − x i‖_r ≤ E i` of all variables of the residual
chain of Dommaschk torus C at the data torus (`XH`, `Design/DommaschkKamCResRel`), on every strip
`r ≥ 0` with `e^r ≤ 68553/2^16`, built variable by variable (`ballH_k`, `chain_succ`) from the
kernel checks of `Design/DommaschkKamCResCheck*` (`node_fullw`, `center_fullw` of
`Design/DommaschkKamCKronW`), the identity of the data with the data torus
(`Design/DommaschkKamCResEqU`, `…EqZ`), the node identities `relH_*` and the tree majorants of the
node centres (`Bd_ctr_of_node`); and the two norm nodes `nH_NR`, `nH_NZ` (the residuals at `ι_q`
in the oracle frame). Generated by `scripts/dommaschk_kam/emit_res.py`.
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- **The data centre `U` is the data torus.** -/
theorem xH_U : xH 4 = Uo := by
  change ctr SH NH MH (1, 0, 0) (gridPolyNM NH MH (gridR rowsH_U)) = Uo
  rw [Uo, gridPolyNM_congr (fun j hj i hi => (eqH_U j hj i hi).1)]
  rfl

/-- **The data centre `Z` is the data torus.** -/
theorem xH_Z : xH 5 = Zo := by
  change ctr SH NH MH (1, 0, 1) (gridPolyNM NH MH (gridR rowsH_Z)) = Zo
  rw [Zo, gridPolyNM_congr (fun j hj i hi => (eqH_Z j hj i hi).1)]
  rfl

/-- **The data centre `LUx` is `2^{Qc} 𝓛_{ι_q} U`.** -/
theorem xH_LUx : xH 6 = LUv := by
  change ctr SH NH MH (1, 0, 3) (gridPolyNM NH MH (gridR rowsH_LUx)) = _
  rw [gridPolyNM_congr (fun j hj i hi => (eqH_U j hj i hi).2), LUv, Uo, dS_ctr_grid]
  rfl

/-- **The data centre `LZx` is `2^{Qc} 𝓛_{ι_q} z`.** -/
theorem xH_LZx : xH 7 = LZv := by
  change ctr SH NH MH (1, 0, 0) (gridPolyNM NH MH (gridR rowsH_LZx)) = _
  rw [gridPolyNM_congr (fun j hj i hi => (eqH_Z j hj i hi).2), LZv, Zo, dS_ctr_grid]
  rfl

set_option linter.unusedVariables false in
/-- The empty chain. -/
theorem ballH_0 %s :
    ∀ i, i < 0 → Bd r (xH i) (BH i) ∧ Bd r (XH i - xH i) (EH i) :=
  fun i h => absurd h (Nat.not_lt_zero i)

""" % (NS, OPEN, hyp))
        cst = ['⟨by rw [xH_t]; exact (Bd_one r).le (by exact_mod_cast (show (1 : ℚ) ≤ BH 0 by kernel_fact)),\n'
               '      step_exact_w (X := XH 0) xH_t.symm (by kernel_fact)⟩',
               '⟨by rw [xH_V]; exact (Bd_one r).le (by exact_mod_cast (show (1 : ℚ) ≤ BH 1 by kernel_fact)),\n'
               '      step_exact_w (X := XH 1) xH_V.symm (by kernel_fact)⟩',
               '⟨by rw [xH_C]; exact (Bd_cSo_q hq).le (by exact_mod_cast (show ((68553 : ℕ) / 2 ^ 16 : ℚ) ≤ BH 2 '
               'by kernel_fact)),\n      step_exact_w (X := XH 2) xH_C.symm (by kernel_fact)⟩',
               '⟨by rw [xH_S]; exact (Bd_sSo_q hq).le (by exact_mod_cast (show ((68553 : ℕ) / 2 ^ 16 : ℚ) ≤ BH 3 '
               'by kernel_fact)),\n      step_exact_w (X := XH 3) xH_S.symm (by kernel_fact)⟩']
        dataeq = {4: 'xH_U', 5: 'xH_Z', 6: 'xH_LUx', 7: 'xH_LZx'}
        for k in range(NV):
            nmk = self.nm(k)
            prev = 'ballH_%d hr hq' % k
            if k < 4:
                step = cst[k]
            elif k in dataeq:
                r = pl.normrec[k]
                step = ('⟨center_fullw hq boxH l1H kronH (fun _ => rfl) %d %d %d %d %d %d %d %d %d\n'
                        '      (BH %d) rfl (by kernel_fact) clH_%s rfl cH_%s (by kernel_fact),\n'
                        '      step_exact_w %s.symm (by kernel_fact)⟩' % (
                            k, pl.W[k][2], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], k, nmk, nmk,
                            dataeq[k]))
            else:
                r = self.nodes[k]
                cl = '(%d : ℤ)' % r['c']
                step = ("""by
      have hE := node_fullw hr hq hWH boxH l1H kronH (fun _ => rfl)
        (fun i hi => (%s i hi).1) (fun i hi => (%s i hi).2) trH_%s %d %d %d %s
        %d %d %d %d %d %d %d %d %d (by kernel_fact) (by kernel_fact) (by kernel_fact)
        (by norm_num) (by kernel_fact) lH_%s kH_%s (by kernel_fact) relH_%s
      exact ⟨Bd_ctr_of_node hr (fun i hi => (%s i hi).1) (fun i hi => (%s i hi).2) trH_%s
        (by kernel_fact) %s (by norm_num) relH_%s hE (BH %d) (by kernel_fact), hE⟩""" % (
                    prev, prev, nmk, r['dd'], r['de'], r['p'], cl, r['A'], r['J'], r['b'], r['W'], r['dc'], r['dr'],
                    r['Ki'], r['Kj'], r['K'], nmk, nmk, nmk, prev, prev, nmk, cl, nmk, k))
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The chain up to the variable `%s`. -/
theorem ballH_%d %s :
    ∀ i, i < %d → Bd r (xH i) (BH i) ∧ Bd r (XH i - xH i) (EH i) :=
  chain_succ (%s)
    (%s)

""" % (nmk, k + 1, hyp, k + 1, prev, step))
        out.append("""/-- **All balls of the chain.** -/
theorem ballH_all %s :
    ∀ i, i < %d → Bd r (xH i) (BH i) ∧ Bd r (XH i - xH i) (EH i) :=
  ballH_%d hr hq

set_option linter.style.longLine false in
/-- **Value bounds**: `‖X i‖ ≤ B i + E i`. -/
theorem valH_le %s (i : ℕ) (hi : i < %d) : Bd r (XH i) ((BH i + EH i : ℚ) : ℝ) := by
  have := (ballH_all hr hq i hi).1.add (ballH_all hr hq i hi).2
  rw [add_sub_cancel] at this; push_cast; exact this

""" % (hyp, NV, NV, hyp, NV))
        for k in ('NR', 'NZ'):
            r = self.norms[k]
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The norm node `%s`. -/
theorem nH_%s_bd %s : Bd r (Ex.eval XH trH_%s) ((%s : ℚ) : ℝ) :=
  norm_fullw hr hq hWH boxH l1H kronH (fun _ => rfl) (fun i hi => (ballH_all hr hq i hi).1)
    (fun i hi => (ballH_all hr hq i hi).2) trH_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d %s
    (by kernel_fact) (by kernel_fact) (by kernel_fact) nlH_%s nH_%s (by kernel_fact)

""" % (k, k, hyp, k, qlean(r['bound']), k, r['w'][0], r['w'][1], r['w'][2], r['A'], r['J'], r['b'], r['W'],
            r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], qlean(r['bound']), k, k))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamCResChain', ''.join(out))

    # ---------------------------------------------------------------- top
    def emit_top(self):
        pl, idx, cert = self.pl, self.idx, self.cert
        D, G, F = idx['D'], idx['G'], idx['F']
        chD, chG, chF = idx['chains']['D'], idx['chains']['G'], idx['chains']['F']
        c1U, c1Z = cert['c1']['U'], cert['c1']['Z']
        text = HEADER + """public import PlasmaLean.Design.DommaschkKamCResChain
public import PlasmaLean.Design.DommaschkKamCAdmFrame

/-!
# The initial invariance error of Dommaschk torus C (N-33 plan item 7)

**Result.** `dk_e0R`, `dk_e0Z`: the flow-form residuals of the `96 × 80` data torus C
(`u₀C`, `z₀C`, `Design/DommaschkKamCTorus`) for the Dommaschk field with the moving frame centre
(`dkFieldTC`) at the rotational transform `ι_C = −(85 + √5)/361` satisfy
`Bd (9/200) (dkFieldTC.resR ι_C u₀C z₀C) e0q` and the same for `resZ`, with
`e0q = %s`
(`≈ %.2e`; the oracle value of `‖E‖_{0.045}` is `%s`): exactly the fields
`e0R`, `e0Z` of `FlowFieldG.KamHG` (`Design/KamFlowIterationG`) for strips `c.ρ = 9/200`.

**Proof.** The residuals are `rotψ` of the oracle-frame residuals `D 𝓛U − n_R`, `D 𝓛z − n_z`
(`resR_eq`, `Dof_rot`, `evPE_rot`, `Lt_rot`; `rotψ` is an isometry). In the oracle frame,
`𝓛_{ι_C} = 𝓛_{ι_q} + (ι_C − ι_q) ∂_θ` with `|ι_C − ι_q| ≤ 2^{−128}` (`iotaqC_close`); the `ι_q` part
is the value of the norm nodes `NR = D LU − R G`, `NZ = D LZ − s F` of the high-resolution ball
chain (`Design/DommaschkKamCResChain`; the `R`-form field polynomials are identified with `dD`,
`dnR`, `dnZ` by `subst_D`, `subst_nR`, `subst_nZ` and the Horner regrouping `horH`), and the
correction is bounded by `2^{−128} ‖D‖ ‖∂_θ x‖` with the Cauchy estimate
`‖∂_θ x‖_{9/200} ≤ ‖x‖_{1/20}/(e/200) ≤ 75 ‖x‖_{1/20}` (centre checks on the strip
`e^r ≤ 68897/2^16`).

**Sanity.** `e0q_pos`, `e0q_small` (the KAM constants need `e₀ ≲ 1.3e-23`), `horH_D` (the
Horner regrouping of `dDR` is `dDR` itself, as a list), `e0q_not_tiny` (rejected fixture: the
certificate does not give `e₀ ≤ 10⁻³⁰`, below the chain's rounding level).
-/

@[expose] public section
noncomputable section

namespace %s

%s
/-- **The certified initial invariance error** `e₀` of torus C on the strip `r = 9/200`. -/
def e0q : ℚ := %s

/-- `e₀ > 0`. -/
theorem e0q_pos : 0 < e0q := by norm_num [e0q]

/-- **Sanity**: `e₀ ≤ 10⁻²⁴`, far below the `≈ 1.3·10⁻²³` the KAM constants need. -/
theorem e0q_small : e0q ≤ 1 / 10 ^ 24 := by norm_num [e0q]

/-- **Rejected fixture**: `e₀` is not below `10⁻³⁰` (the rounding level of the chain). -/
theorem e0q_not_tiny : ¬ e0q ≤ 1 / 10 ^ 30 := by norm_num [e0q]

/-- `e^{1/20} ≤ 68897/2^16` (the strip of the derivative bound). -/
theorem exp_dk1_le : Real.exp (1 / 20) ≤ (68897 : ℕ) / 2 ^ 16 := by
  have h := Real.exp_bound' (x := 1 / 20) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- The Horner regrouping of `dDR` is `dDR`. -/
theorem horH_D : horH (polyH 0) 0 %d 0 = dDR := by kernel_fact

/-- The Horner regrouping of `dnRh` is `dnRh`. -/
theorem horH_G : horH (polyH 1) 0 %d 0 = dnRh := by kernel_fact

/-- The Horner regrouping of `dnZR` is `R² ·` the `F` polynomial. -/
theorem horH_F : DkPoly.mulMono ⟨1, 2, 0, 0, 0⟩ (horH (polyH 2) 2 %d 0) = dnZR := by kernel_fact

/-- The oracle-frame point of the data torus is the `R`-form point after substitution. -/
theorem xRH_eq : ![algebraMap ℂ FA ((R0q : ℚ) : ℂ) + xBo Uo Zo 0, xBo Uo Zo 1, xBo Uo Zo 2,
    xBo Uo Zo 3, 0, 0] = xRH := by
  funext i; fin_cases i <;> rfl

/-- `D` at the data torus is the chain value of `D`. -/
theorem Fo_D : Fo dD Uo Zo = XH %d := by
  rw [Fo, ← subst_D, ev_substR_H, xRH_eq]
  change DkPoly.ev xRH dDR = DkPoly.ev xRH (horH (polyH 0) 0 %d 0)
  rw [horH_D]

/-- `n_R` at the data torus is `R G`. -/
theorem Fo_nR : Fo dnR Uo Zo = XH 8 * XH %d := by
  rw [Fo, ← subst_nR, ev_substR_H, xRH_eq, DkPoly.ev_mulMono]
  change _ = RvH * DkPoly.ev xRH (horH (polyH 1) 0 %d 0)
  rw [horH_G]
  simp [DkPoly.Tm.ev, xRH]

/-- `n_z` at the data torus is `s F`. -/
theorem Fo_nZ : Fo dnZ Uo Zo = XH 9 * XH %d := by
  rw [Fo, ← subst_nZ, ev_substR_H, xRH_eq, ← horH_F, DkPoly.ev_mulMono]
  change _ = RvH * RvH * DkPoly.ev xRH (horH (polyH 2) 2 %d 0)
  simp [DkPoly.Tm.ev, xRH, sq]

/-- `LU` is `𝓛_{ι_q} U`. -/
theorem XH_LU : XH 14 = Lt iotaqC Uo := by
  change ((2 : ℂ) ^ Qc)⁻¹ • LUv = _
  rw [LUv, Lt, show ((-(Iqc : ℤ) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * ((iotaqC : ℝ) : ℂ) by
      rw [iotaqC]; push_cast; field_simp,
    show (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * 2 by push_cast; ring,
    dS_smul_symbol _ _ _ ana_Uo, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/-- `LZ` is `𝓛_{ι_q} z`. -/
theorem XH_LZ : XH 15 = Lt iotaqC Zo := by
  change ((2 : ℂ) ^ Qc)⁻¹ • LZv = _
  rw [LZv, Lt, show ((-(Iqc : ℤ) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * ((iotaqC : ℝ) : ℂ) by
      rw [iotaqC]; push_cast; field_simp,
    show (((2 : ℤ) ^ (Qc + 1) : ℤ) : ℂ) = (2 : ℂ) ^ Qc * 2 by push_cast; ring,
    dS_smul_symbol _ _ _ ana_Zo, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]

/-- `𝓛_ι − 𝓛_{ι_q} = (ι − ι_q) ∂_θ`. -/
theorem Lt_sub_Lt (ι ι' : ℝ) {x : FA} (hx : Ana x) :
    Lt ι x - Lt ι' x = ((ι - ι' : ℝ) : ℂ) • dTh x := by
  rw [Lt, Lt, dTh, sub_eq_iff_eq_add, ← dS_smul_symbol _ _ _ hx, ← dS_add_symbol _ _ _ _ hx]
  congr 1 <;> push_cast <;> ring

/-- The Cauchy bound of `∂_θ` from a bound on the wider strip `1/20`. -/
theorem Bd_dTh_of {x : FA} {B : ℝ} (hB : 0 ≤ B) (hx : Bd (1 / 20) x B) :
    Bd (9 / 200) (dTh x) (75 * B) := by
  have h := hx.dS (δ := 1 / 200) (by norm_num) (by norm_num) 1 0
  rw [show (1 / 20 : ℝ) - 1 / 200 = 9 / 200 by norm_num] at h
  refine h.le ?_
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9; linarith
  have hm : max ‖(1 : ℂ)‖ ‖(0 : ℂ)‖ = 1 := by simp
  rw [hm]
  have : 1 / (Real.exp 1 * (1 / 200)) ≤ 75 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  nlinarith

set_option linter.style.longLine false in
/-- `‖U‖_{1/20}` (centre check on the wider strip). -/
theorem bU1 : Bd (1 / 20) Uo ((%s : ℚ) : ℝ) := by
  rw [← xH_U]
  exact center_fullw exp_dk1_le boxH l1H kronH (fun _ => rfl) 4 0 %d %d %d %d %d %d %d (%s) rfl
    (by kernel_fact) (by kron_lt) rfl c1H_U (by kernel_fact)

set_option linter.style.longLine false in
/-- `‖z‖_{1/20}` (centre check on the wider strip). -/
theorem bZ1 : Bd (1 / 20) Zo ((%s : ℚ) : ℝ) := by
  rw [← xH_Z]
  exact center_fullw exp_dk1_le boxH l1H kronH (fun _ => rfl) 5 1 %d %d %d %d %d %d %d (%s) rfl
    (by kernel_fact) (by kron_lt) rfl c1H_Z (by kernel_fact)

/-- The value of the norm node `NR`. -/
theorem eval_NR : Ex.eval XH trH_NR = Fo dD Uo Zo * Lt iotaqC Uo - Fo dnR Uo Zo := by
  rw [Fo_D, Fo_nR, ← XH_LU]; rfl

/-- The value of the norm node `NZ`. -/
theorem eval_NZ : Ex.eval XH trH_NZ = Fo dD Uo Zo * Lt iotaqC Zo - Fo dnZ Uo Zo := by
  rw [Fo_D, Fo_nZ, ← XH_LZ]; rfl

/-- The `ι − ι_q` correction. -/
theorem Bd_corr {x : FA} (hx : Ana x) {B : ℚ} (hB0 : 0 ≤ B) (hB : Bd (1 / 20) x (B : ℝ)) :
    Bd (9 / 200) (Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC x - Lt iotaqC x))
      (((BH %d + EH %d : ℚ) : ℝ) * ((1 / 2 ^ Qc : ℝ) * (75 * (B : ℝ)))) := by
  have hD : Bd (9 / 200) (Fo dD Uo Zo) ((BH %d + EH %d : ℚ) : ℝ) := by
    rw [Fo_D]; exact valH_le (by norm_num) exp_dk_le %d (by norm_num)
  rw [Lt_sub_Lt _ _ hx]
  refine hD.mul (by norm_num) ?_
  have h1 := (Bd_dTh_of (by exact_mod_cast hB0) hB).smul
    (((DommaschkKamDio.dkIotaC - iotaqC : ℝ) : ℂ))
  refine h1.le ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have := iotaqC_close
  have h75 : (0 : ℝ) ≤ 75 * (B : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right this h75

set_option linter.style.longLine false in
/-- **The oracle-frame `R`-residual.** -/
theorem resO_R : Bd (9 / 200) (Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Uo - Fo dnR Uo Zo)
    ((e0q : ℚ) : ℝ) := by
  have h1 := nH_NR_bd (by norm_num) exp_dk_le
  rw [eval_NR] at h1
  have h2 := Bd_corr ana_Uo (by norm_num) bU1
  have h3 := h1.add h2
  rw [show Fo dD Uo Zo * Lt iotaqC Uo - Fo dnR Uo Zo +
      Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC Uo - Lt iotaqC Uo) =
      Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Uo - Fo dnR Uo Zo by ring] at h3
  refine h3.le ?_
  have := (show (%s : ℚ) + (BH %d + EH %d) * (1 / 2 ^ Qc * (75 * %s)) ≤ e0q by kernel_fact)
  have := (Rat.cast_le (K := ℝ)).2 this
  push_cast at this ⊢
  linarith

set_option linter.style.longLine false in
/-- **The oracle-frame `z`-residual.** -/
theorem resO_Z : Bd (9 / 200) (Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Zo - Fo dnZ Uo Zo)
    ((e0q : ℚ) : ℝ) := by
  have h1 := nH_NZ_bd (by norm_num) exp_dk_le
  rw [eval_NZ] at h1
  have h2 := Bd_corr ana_Zo (by norm_num) bZ1
  have h3 := h1.add h2
  rw [show Fo dD Uo Zo * Lt iotaqC Zo - Fo dnZ Uo Zo +
      Fo dD Uo Zo * (Lt DommaschkKamDio.dkIotaC Zo - Lt iotaqC Zo) =
      Fo dD Uo Zo * Lt DommaschkKamDio.dkIotaC Zo - Fo dnZ Uo Zo by ring] at h3
  refine h3.le ?_
  have := (show (%s : ℚ) + (BH %d + EH %d) * (1 / 2 ^ Qc * (75 * %s)) ≤ e0q by kernel_fact)
  have := (Rat.cast_le (K := ℝ)).2 this
  push_cast at this ⊢
  linarith

/-- **The `R`-residual of torus C** (`KamHG.e0R`, strip `9/200`). -/
theorem dk_e0R :
    Bd (9 / 200) (dkFieldTC.resR DommaschkKamDio.dkIotaC u₀C z₀C) ((e0q : ℚ) : ℝ) := by
  rw [FlowFieldG.resR_eq, u₀C, z₀C, Dof_rot, Lt_rot _ ana_Uo,
    show dkFieldTC.nRp = DkPoly.toPE dnR from rfl, evPE_rot, ← rotψ_mul, ← rotψ_sub]
  exact Bd_rotψ resO_R

/-- **The `z`-residual of torus C** (`KamHG.e0Z`, strip `9/200`). -/
theorem dk_e0Z :
    Bd (9 / 200) (dkFieldTC.resZ DommaschkKamDio.dkIotaC u₀C z₀C) ((e0q : ℚ) : ℝ) := by
  rw [FlowFieldG.resZ_eq, u₀C, z₀C, Dof_rot, Lt_rot _ ana_Zo,
    show dkFieldTC.nZp = DkPoly.toPE dnZ from rfl, evPE_rot, ← rotψ_mul, ← rotψ_sub]
  exact Bd_rotψ resO_Z

end %s
""" % (qlean(cert['e0q']), float(cert['e0q']), DT.cfg()['oracle_e'], NS, OPEN, qlean(cert['e0q']),
            chD['top'], chG['top'], chF['top'], D, chD['top'], G, chG['top'], F, chF['top'],
            qlean(c1U['Bq']), c1U['b'], c1U['W'], c1U['dc'], c1U['dr'], c1U['Ki'], c1U['Kj'], c1U['K'],
            qlean(c1U['Bq']),
            qlean(c1Z['Bq']), c1Z['b'], c1Z['W'], c1Z['dc'], c1Z['dr'], c1Z['Ki'], c1Z['Kj'], c1Z['K'],
            qlean(c1Z['Bq']),
            D, D, D, D, D,
            qlean(self.norms['NR']['bound']), D, D, qlean(c1U['Bq']),
            qlean(self.norms['NZ']['bound']), D, D, qlean(c1Z['Bq']), NS)
        self.write('DommaschkKamCRes', text)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--only', default='', help='comma-separated: data,env,trees,checks,eq,rel,chain,top')
    ap.add_argument('--ncheck', type=int, default=12)
    ap.add_argument('--perdata', type=int, default=7)
    ap.add_argument('--plan', default='', help='write the module list (dependency order) to this file')
    ap.add_argument('--tag', default='C', help='torus (C, or A: modules DommaschkKamA*, see dk_torus.py)')
    ap.add_argument('--out-dir', default='', help='output directory (default PlasmaLean/Design)')
    args = ap.parse_args()
    global OUT
    DT.select(args.tag)
    if args.out_dir:
        OUT = args.out_dir
    t0 = time.time()
    pl, idx, norms, ctx = build()
    print('chain built: %d variables, %d steps, %.1f s' % (pl.nvar, len(pl.steps), time.time() - t0))
    cert = certify(pl, idx, norms, ctx)
    print('NR bound %.4e, NZ bound %.4e; corrections %.2e, %.2e; e0q = %s (%.3e)' % (
        float(norms['NR']['bound']), float(norms['NZ']['bound']), float(cert['corr']['U']),
        float(cert['corr']['Z']), cert['e0q'], float(cert['e0q'])))
    print('margin against the required 1.3e-23: %.0f' % (1.3e-23 / float(cert['e0q'])))
    mx = max((s for s in pl.steps if 'W' in s and 'R' in s), key=lambda s: s['W'] * s['R'] * s['b'])
    print('largest image: %s %.2f Mbit' % (mx['name'], mx['W'] * mx['R'] * mx['b'] / 1e6))
    print('data: %.2f MB of row bits' % (sum(sum(r[1] * r[2] + 64 for r in pl.rows[i]) for i in pl.rows) / 8e6))
    em = Emit(pl, idx, norms, ctx, cert)
    only = set(args.only.split(',')) if args.only else None
    want = lambda k: args.emit and (only is None or k in only)     # noqa: E731
    em.emit_data(args.perdata, write=want('data'))
    em.emit_checks(args.ncheck, write=want('checks'))
    em.emit_eq(write=want('eq'))
    if want('env'):
        em.emit_env()
    if want('trees'):
        em.emit_trees()
    if want('rel'):
        em.emit_rel()
    if want('chain'):
        em.emit_chain()
    if want('top'):
        em.emit_top()
    mods = (['DommaschkKamCResKron'] + em.datamods + ['DommaschkKamCResEnv', 'DommaschkKamCResTrees'] +
            em.eqmods + em.checkmods + ['DommaschkKamCResRel', 'DommaschkKamCResChain', 'DommaschkKamCRes'])
    mods = [DT.out_name(m) for m in mods]
    print('modules:', ' '.join(mods))
    if args.plan:
        open(args.plan, 'w').write('\n'.join('PlasmaLean.Design.' + m for m in mods) + '\n')
    if args.emit:
        print('emitted:', em.files)


if __name__ == '__main__':
    main()
