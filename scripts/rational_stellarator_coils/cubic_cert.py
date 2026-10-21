"""UNTRUSTED exact-integer replica of the cubic-interpolation frontier checker
(`PlasmaLean/Design/PolygonCoilCubicCheck.lean`) and grid generator.

* `load_design` / `full_filaments` / `offsets` / `all_segs`: as in `polygon_cert.py` (the coil
  data at scale 2^-32, the symmetry orbits, the checker offsets and segment constants);
* `corner4`, `rem_p4`, `line_out4`: bit-for-bit replicas of `cornerEval4`, `remP4`, `lineOut4`;
* `cell_total4`, `cells_row4`, `cell_ok_full`: replicas of the cell checks (`cellOK4`, `cellsRow4`);
* `face_wgrid`, `line_params`, `eval_face`: the w-nodes of a face, the t-neighbours of a grid
  line, and the evaluation of all lines and cells of a face.

`corner_xyz4` carries the extra factor `2^10` of `cornerXYZ4` in the common denominator (this
makes the square-root rounding of the vertex distances negligible).

Nothing here is trusted: the Lean kernel re-runs the checker on the emitted data.
"""
import math, pickle, sys, time
from fractions import Fraction as Fr
from polygon_cert import (load_design, full_filaments, offsets, all_segs, vert_step, cold_start,
                          hel_q, KT, TWO32, TWO40, TWO64, TWO136, sq, nst)

QT = 4096
TWO30 = 1 << 30
TWO24 = 1 << 24


def cdiv(a, b):
    if b <= 0:
        return 0
    return (a + b - 1) // b


def nstK(n, k, x):
    for _ in range(k):
        x = (x + n // x) // 2 if x > 0 else 0
    return x


def sqrt_up_from(N, x0):
    return nstK(N, 6, x0) + 1


def nmax(a, b):
    return b if a <= b else a


def nmin2(a, b):
    return a if a <= b else b


def nsub(a, b):
    return a - b if a >= b else 0


# ------------------------------------------------------------------ faces
def cylR(kind):
    return 199 if kind == 0 else 161


class Face4:
    def __init__(s, kind, wd, wn, htn, htd, hwn, hwd):
        s.kind, s.wd, s.wn, s.htn, s.htd, s.hwn, s.hwd = kind, wd, wn, htn, htd, hwn, hwd


def face_rz4(F, wn):
    if F.kind < 2:
        return (cylR(F.kind), 181), (wn, F.wd)
    return (wn, F.wd), ((3420 if F.kind == 2 else -3420), 32761)


def corner_xyz4(F, m, wn):
    q = QT
    cd = q * q + m * m
    cn = q * q - m * m
    sn = 2 * m * q
    (rn, rd), (zn, zd) = face_rz4(F, wn)
    D = rd * cd * zd * 1024
    X = -(rn * sn * zd * 1024) + 4 * D
    Y = rn * cn * zd * 1024 + 4 * D
    Z = zn * rd * cd * 1024 + 4 * D
    return (max(X, 0), max(Y, 0), max(Z, 0), D), (X >= 0 and Y >= 0 and Z >= 0)


def hel_at4(F, m, wn):
    q = QT
    cd = q * q + m * m
    (rn, rd), (zn, zd) = face_rz4(F, wn)
    return hel_q(Fr(rn, rd), Fr(zn, zd), Fr(-2 * m * q, cd), Fr(q * q - m * m, cd))


# ------------------------------------------------------------------ the corner
def d2_low(na, nb, dvv):
    if na + dvv <= nb:
        return na
    if nb + dvv <= na:
        return nb
    return nsub(na, cdiv(sq(nsub(na + dvv, nb)), 4 * dvv))


def cell_L(rBD, s0l, d2):
    return nsub(nsub(d2, cdiv(rBD * d2, s0l)), rBD * s0l)


def floor_mul(x, S):
    return (x.numerator * S) // x.denominator


def ceil_mul(x, S):
    return -((-(x.numerator * S)) // x.denominator)


def corner4(o, nS, segs, Xt, Yt, Zt, D, h, P, gs):
    """replica of cornerEval4: returns (ok, (fok, e, ex, ey, ez, rho), rw, rt, gs')."""
    D2 = D * D
    Xs, Ys, Zs = Xt * TWO32, Yt * TWO32, Zt * TWO32
    lam = D * TWO32
    c = (D, D2, Xs, Ys, Zs, sq(Xs) + sq(Ys) + sq(Zs), lam)
    vs = []
    for fi, f in enumerate(segs):
        row = []
        for k, s in enumerate(f):
            g0 = gs[fi][k] if gs is not None else cold_start(c, s)
            row.append(vert_step(c, s, g0))
        vs.append(row)
    D3S = D2 * D * TWO136
    sx = sy = sz = tx = ty = tz = sf = 0
    ok = True
    for fi, f in enumerate(segs):
        row = vs[fi]
        for k, s in enumerate(f):
            a = row[k]
            b = row[(k + 1) % len(row)]
            ab = a[1] * b[1]
            dvv = D2 * s['vv']
            tc = a[0] + b[0]
            den = ab * nsub(2 * ab + tc, dvv)
            fv = (2 * (a[1] + b[1]) * D3S) // den if den > 0 else 0
            sx += fv * s['w1'][0]; sy += fv * s['w1'][1]; sz += fv * s['w1'][2]
            tx += fv * s['w2'][0]; ty += fv * s['w2'][1]; tz += fv * s['w2'][2]
            sf += fv
            ok = ok and a[2] and b[2] and dvv <= ab + tc
    # cornerFinalV
    S1 = (sx - o[0] * sf, sy - o[1] * sf, sz - o[2] * sf)
    S2 = (tx - o[3] * sf, ty - o[4] * sf, tz - o[5] * sf)
    T = (D * S1[0] - TWO32 * (Yt * S2[2] - Zt * S2[1]), D * S1[1] - TWO32 * (Zt * S2[0] - Xt * S2[2]),
         D * S1[2] - TWO32 * (Xt * S2[1] - Yt * S2[0]))
    E1 = cdiv(70 * KT * o[6] * sf, lam) + nS * o[6]
    E2 = cdiv(70 * KT * o[7] * sf, lam) + nS * o[7]
    R = (D * E1 + TWO32 * (Yt + Zt) * E2, D * E1 + TWO32 * (Zt + Xt) * E2, D * E1 + TWO32 * (Xt + Yt) * E2)
    SE = D * TWO136
    m = []
    for k in range(3):
        fl = floor_mul(h[k], SE)
        ce = ceil_mul(h[k], SE)
        m.append(nmax(abs(T[k] - R[k] - ce), abs(T[k] + R[k] - fl)))
    N = (sq(m[0]) + sq(m[1]) + sq(m[2])) * sq(TWO40)
    sN = sqrt_up_from(N, (m[0] + m[1] + m[2]) * TWO40)
    fok = N <= sq(sN)
    e = cdiv(sN, SE)
    ev = [((T[k] * h[k].denominator - h[k].numerator * SE) * TWO40) // (SE * h[k].denominator)
          for k in range(3)]
    rho = cdiv(nmax(nmax(R[0], R[1]), R[2]) * TWO40, SE) + 1
    # remainder
    rw = rt = 0
    rok = True
    if P is not None:
        (rBW, s0lW), (rBT, s0lT), w6, t6, t4, t2, lam2, nt = P
        rok = rBW <= s0lW and rBT <= s0lT and nt <= sq(rBT)
        for fi, f in enumerate(segs):
            row = vs[fi]
            for k, s in enumerate(f):
                a = row[k]
                b = row[(k + 1) % len(row)]
                d2 = d2_low(a[0], b[0], D2 * s['vv'])
                Lw = cell_L(rBW, s0lW, d2)
                Lt = cell_L(rBT, s0lT, d2)
                rw += cdiv(s['kv'] * w6, Lw * Lw * Lw * TWO24)
                rt += cdiv(s['kv'] * (t6 + Lt * (t4 + Lt * t2)), Lt * Lt * Lt * TWO24)
                rok = rok and 0 < Lw and 0 < Lt and lam2 <= 25 * Lt
    okall = ok and fok and 1000 * KT <= lam and rok
    return okall, (fok, e, ev[0], ev[1], ev[2], rho), rw, rt, [[v[3] for v in row] for row in vs]


def rem_p4(F, mp, m, mn2, wp, wn, wn1, wn2, D):
    q = QT
    lam = D * TWO32
    dW = nmax(abs(wn - wp), abs(wn2 - wn))
    rBW = cdiv(lam * dW, F.wd)
    rhon = cylR(F.kind) if F.kind < 2 else abs(wn1)
    rhod = 181 if F.kind < 2 else F.wd
    dm = nmax(abs(m - mp), abs(mn2 - m))
    dw = abs(wn1 - wn)
    Nt = cdiv(sq(lam) * (4 * (sq(rhon) * (sq(dm) * sq(F.wd))) + sq(dw) * (sq(rhod) * sq(q))),
              sq(rhod) * (sq(q) * sq(F.wd)))
    g0 = cdiv(lam * (2 * (rhon * dm)), rhod * q) + cdiv(lam * dw, F.wd)
    rBT = sqrt_up_from(Nt, g0)
    mlo, mhi = mp, mn2
    mmin = 0 if (mlo <= 0 and 0 <= mhi) else nmin2(abs(mlo), abs(mhi))
    mmax = nmax(abs(mlo), abs(mhi))
    Tn = sq(q)
    Td = sq(q) + sq(mmin)
    T4n = sq(sq(Tn))
    T4d = sq(sq(Td))
    aT = 2304 * mmax + 2309 * q
    c6n = T4n * (11520 * (sq(sq(rhon)) * q) + aT * (sq(rhon) * (rhon * rhod)))
    c6d = 6 * (T4d * (sq(sq(rhod)) * q))
    c4n = 3 * (T4n * (aT * (sq(rhon) * rhon))) + (2 * T4d) * (q * (864 * (sq(rhon) * rhod) + 16 * (rhon * sq(rhod))))
    c4d = 2 * (T4d * (q * (sq(rhod) * rhod)))
    lam2 = sq(lam)
    lam4 = sq(lam2)
    lam6 = lam4 * lam2
    s0l = D * TWO30
    return ((rBW, s0l), (rBT, s0l), 120 * lam6, cdiv(c6n * lam6, c6d), cdiv(c4n * lam4, c4d),
            cdiv(144 * rhon * lam2, rhod), lam2, Nt)


def rwC(F, w0, w1, w2, w3, rw):
    return cdiv((rw + cdiv(F.hwn * TWO40, F.hwd)) * (sq(abs(w2 - w1)) * (abs(w2 - w0) * abs(w3 - w1))),
                96 * sq(sq(F.wd)))


def rtC(F, m0, m1, m2, m3, rt):
    return cdiv((rt + cdiv(F.htn * TWO40, F.htd)) * (sq(abs(m2 - m1)) * (abs(m2 - m0) * abs(m3 - m1))),
                96 * sq(sq(QT)))


def line_out4(o, nS, segs, F, mp, m, mn, mn2):
    out = []
    gs = None
    ws = F.wn
    for j, wn in enumerate(ws):
        xyz, xok = corner_xyz4(F, m, wn)
        h = hel_at4(F, m, wn)
        win = (ws[j - 1], ws[j + 1], ws[j + 2]) if (j >= 1 and j + 2 < len(ws)) else None
        P = rem_p4(F, mp, m, mn2, win[0], wn, win[1], win[2], xyz[3]) if win else None
        ok, fin, rw, rt, gs = corner4(o, nS, segs, xyz[0], xyz[1], xyz[2], xyz[3], h, P, gs)
        if win:
            rr = (rwC(F, win[0], wn, win[1], win[2], rw), rtC(F, mp, m, mn, mn2, rt))
        else:
            rr = (0, 0)
        out.append((ok and xok, fin[1], fin[2], fin[3], fin[4], fin[5], rr[0], rr[1]))
    return out


# ------------------------------------------------------------------ cells
def l1(x, y, z):
    return abs(x) + abs(y) + abs(z)


def corrA(X0, X1, X2, v0, v1, v2):
    a, b, ac = X1 - X0, X2 - X1, X2 - X0
    k = (b, -ac, a)
    vs = (v0, v1, v2)
    n = [sum(k[i] * vs[i][2 + c] for i in range(3)) for c in range(3)]
    r = 3 * sum(abs(k[i]) * vs[i][5] for i in range(3))
    return cdiv(abs(b) * (l1(*n) + r), 4 * abs(a * ac))


def corrB(X0, X1, X2, X3, v0, v1, v2, v3):
    a, b, c = X1 - X0, X2 - X1, X3 - X2
    ac, bc, abc = X2 - X0, X3 - X1, X3 - X0
    k = (-(c * bc * b), a * ac * c + c * bc * ac, -(a * ac * bc + c * bc * a), a * ac * b)
    vs = (v0, v1, v2, v3)
    n = [sum(k[i] * vs[i][2 + cc] for i in range(4)) for cc in range(3)]
    r = 3 * sum(abs(k[i]) * vs[i][5] for i in range(4))
    return cdiv(abs(b) * (l1(*n) + r), 4 * abs(a * c * bc * abc))


def corr4(X0, X1, X2, X3, v0, v1, v2, v3):
    return corrA(X0, X1, X2, v0, v1, v2) + corrB(X0, X1, X2, X3, v0, v1, v2, v3)


def leb4(X0, X1, X2, X3, C):
    n0 = sq(abs(X2 - X1)) * abs(X3 - X1)
    d0 = 4 * abs((X1 - X0) * (X2 - X0) * (X3 - X0))
    n3 = sq(abs(X2 - X1)) * abs(X2 - X0)
    d3 = 4 * abs((X3 - X0) * (X3 - X1) * (X3 - X2))
    return cdiv(C * (d0 * d3 + 2 * (n0 * d3 + n3 * d0)), d0 * d3)


def cell_total4(M, W, A, B, C, Dd):
    """the total of cellOK4 (without the comparison); A..Dd are 4-lists of records."""
    E = max(B[1][1], B[2][1], C[1][1], C[2][1])
    Cw = max(corr4(*W, *B), corr4(*W, *C))
    Cs = max(corr4(*M, A[k], B[k], C[k], Dd[k]) for k in range(4))
    RW = max(A[1][6], B[1][6], C[1][6], Dd[1][6])
    oks = all(r[0] for L in (A, B, C, Dd) for r in L)
    return oks, E + Cw + leb4(*W, Cs) + leb4(*M, RW) + B[1][7], (E, Cw, leb4(*W, Cs), leb4(*M, RW), B[1][7])


def cells_row4(eta, M, L0, L1, L2, L3, ws):
    worst = 0
    for j in range(len(ws) - 3):
        oks, tot, parts = cell_total4(M, ws[j:j + 4], L0[j:j + 4], L1[j:j + 4], L2[j:j + 4], L3[j:j + 4])
        if not oks or tot > eta:
            return False, tot, parts, j
        worst = max(worst, tot)
    return True, worst, None, None


# ------------------------------------------------------------------ grids
def cell_ok_full(F, eta, M, W, A, B, C, Dd):
    """replica of cellOK4 including cellCond."""
    def in_face(w):
        if F.kind < 2:
            return abs(w) * 32761 <= 3420 * F.wd
        return 161 * F.wd <= 181 * w and 181 * w <= 199 * F.wd
    cond = (M[0] < M[1] < M[2] < M[3]) and (W[0] < W[1] < W[2] < W[3]) and -2048 <= M[0] and M[3] <= 2048 \
        and (F.kind < 2 or 17 * F.wd <= 20 * W[0]) and in_face(W[1]) and in_face(W[2])
    oks, tot, parts = cell_total4(M, W, A, B, C, Dd)
    return cond and oks and tot <= eta, tot, parts


def face_wgrid(kind, n):
    """w-grid with n cells over the face and one extra node beyond each end."""
    if kind < 2:
        wd = 32761 * n
        lo, hi = -3420 * n, 3420 * n
    else:
        wd = 181 * n
        lo, hi = 161 * n, 199 * n
    step = (hi - lo) / n
    wn = [lo + round(j * step) for j in range(n + 1)]
    wn = [lo - round(step)] + wn + [hi + round(step)]
    return wd, wn


def line_params(g, k):
    if 1 <= k <= len(g) - 3:
        return g[k - 1], g[k], g[k + 1], g[k + 2]
    if k == 0:
        return g[0] - (g[1] - g[0]), g[0], g[1], g[2]
    if k == len(g) - 2:
        return g[k - 1], g[k], g[k + 1], g[k + 1] + (g[k + 1] - g[k])
    d = g[k] - g[k - 1]
    return g[k - 1], g[k], g[k] + d, g[k] + 2 * d


def eval_face(o, nS, segs, F, g, eta, pool=None):
    args = [(o, nS, segs, F) + line_params(g, k) for k in range(len(g))]
    if pool is None:
        Ls = [line_out4(*a) for a in args]
    else:
        Ls = pool.starmap(line_out4, args)
    worst = 0
    bad = []
    for i in range(1, len(g) - 2):
        M = g[i - 1:i + 3]
        for j in range(len(F.wn) - 3):
            W = F.wn[j:j + 4]
            ok, tot, parts = cell_ok_full(F, eta, M, W, Ls[i - 1][j:j + 4], Ls[i][j:j + 4], Ls[i + 1][j:j + 4],
                                          Ls[i + 2][j:j + 4])
            worst = max(worst, tot)
            if not ok:
                bad.append((i, j, tot, parts))
    return Ls, worst, bad
