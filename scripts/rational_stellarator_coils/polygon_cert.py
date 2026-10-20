"""UNTRUSTED generator and exact-integer replica of the Lean checker for the polygonal-coil
frontier certificate (`PlasmaLean/Design/PolygonCoilCheck.lean`).

* `load_design` rounds a symmetric design of `polygon_design.py` (2 representative filaments of
  16 vertices, currents) to integers at scale 2^-32;
* `full_filaments` applies the symmetry group {id, rotPi, sigma, rotPi.sigma} (currents
  +,+,-,-), exactly as `PolygonCoilData.fils`;
* `line_out` / `check_chunk` replicate `lineOut` / `checkChunk` bit for bit (same constants,
  same floor/ceiling divisions, same Newton steps);
* `gen_face` marches the grid lines of one face adaptively so that every cell passes.

Nothing here is trusted: the Lean kernel re-runs the checker on the emitted data.
"""
import numpy as np, pickle, sys, math, time
from fractions import Fraction as Fr

TWO32 = 1 << 32; TWO30 = 1 << 30; TWO40 = 1 << 40; TWO64 = 1 << 64; TWO136 = 1 << 136
KT = 1 << 47; QT = 4096; NSEG = 128; ETAFP = 714682558

def sq(a): return a * a
def cdiv(a, b): return (a + b - 1) // b
def nst(n, x): return (x + n // x) // 2
def nstK(n, k, x):
    for _ in range(k): x = nst(n, x)
    return x
def tr(x): return x + 4 * TWO32

# ------------------------------------------------------------------ data
def load_design(fn):
    d = pickle.load(open(fn, 'rb'))
    Z, Ir = d['Z'], d['Ir']
    reps = []
    for r in range(len(Z)):
        verts = [tuple(int(round(c * TWO32)) for c in v) for v in Z[r]]
        K = int(round(Ir[r] / (4 * math.pi) * TWO32))
        reps.append((K, verts))
    return reps

def gR(p): return (-p[0], -p[1], p[2])
def gS(p): return (p[1], p[0], -p[2])
def gRS(p): return gR(gS(p))
GROUP = [(lambda p: p, 1), (gR, 1), (gS, -1), (gRS, -1)]

def full_filaments(reps):
    out = []
    for (K, verts) in reps:
        for (g, eps) in GROUP:
            out.append((eps * K, [g(v) for v in verts]))
    return out

def pairs_wrap(vs): return [(vs[i], vs[(i + 1) % len(vs)]) for i in range(len(vs))]

def sqrt_up(n): return nstK(n, 80, n + 1) + 1

def weights(K, p, q):
    Px, Py, Pz = tr(p[0]), tr(p[1]), tr(p[2])
    Vx, Vy, Vz = q[0] - p[0], q[1] - p[1], q[2] - p[2]
    return (Px, Py, Pz), (Vx, Vy, Vz), (K * (Py * Vz - Pz * Vy), K * (Pz * Vx - Px * Vz), K * (Px * Vy - Py * Vx)), (K * Vx, K * Vy, K * Vz)

def offsets(fils):
    m1 = [0, 0, 0]; m2 = [0, 0, 0]
    for (K, vs) in fils:
        for p, q in pairs_wrap(vs):
            _, _, a1, a2 = weights(K, p, q)
            for i in range(3): m1[i] = max(m1[i], abs(a1[i])); m2[i] = max(m2[i], abs(a2[i]))
    return (m1[0], m1[1], m1[2], m2[0], m2[1], m2[2], max(m1), max(m2))

def mk_seg(o, K, p, q):
    P, V, a1, a2 = weights(K, p, q)
    vv = V[0] ** 2 + V[1] ** 2 + V[2] ** 2
    return dict(px=P[0], py=P[1], pz=P[2], pp=P[0] ** 2 + P[1] ** 2 + P[2] ** 2, vv=vv,
                w1=(a1[0] + o[0], a1[1] + o[1], a1[2] + o[2]), w2=(a2[0] + o[3], a2[1] + o[4], a2[2] + o[5]),
                kv=abs(K) * sqrt_up(vv))

def all_segs(o, fils): return [[mk_seg(o, K, p, q) for p, q in pairs_wrap(vs)] for (K, vs) in fils]

# ------------------------------------------------------------------ hel (exact)
def hel_q(rho, zeta, c, s):
    r2 = rho * rho; z2 = zeta * zeta
    a8 = r2 * (r2 - 1); b8 = r2 * zeta * (3 - r2); g8 = (r2 - 1) + 4 * z2; d8 = zeta * ((5 - 3 * r2) - 4 * z2)
    c3 = 4 * c ** 3 - 3 * c; s3 = 3 * s - 4 * s ** 3
    i8 = 1 / (8 * r2 * rho); e16 = ((6 * r2 - r2 * r2) - 5) + 12 * z2; i16 = 1 / (16 * r2)
    return ((a8 * c + b8 * s + g8 * c3 + d8 * s3) * i8, (-a8 * s + b8 * c + g8 * s3 - d8 * c3) * i8,
            (e16 * (2 * c * s) - 8 * zeta * (c * c - s * s)) * i16)

# ------------------------------------------------------------------ corner
def vert_n(c, s):
    D, D2, Xs, Ys, Zs, XX, lam = c
    a = D2 * s['pp'] + XX; b = 2 * D * (s['px'] * Xs + s['py'] * Ys + s['pz'] * Zs)
    return max(a - b, 0)

def vert_step(c, s, g0):
    n = vert_n(c, s); r = nst(n, nst(n, nst(n, g0))); al = max(r - KT, 0)
    ok = c[6] <= 5 * al and sq(al) <= n and n <= sq(r + KT)
    return (n, al, ok, r)

def cold_start(c, s): return nstK(vert_n(c, s), 7, 4 * c[6])

def d2_low(na, nb, dvv):
    if na + dvv <= nb: return na
    if nb + dvv <= na: return nb
    return max(na - cdiv(sq(na + dvv - nb), 4 * dvv), 0)

def cell_L(rc, d2):
    return max(max(d2 - cdiv(rc['rBD'] * d2, rc['s0l']), 0) - rc['rBD'] * rc['s0l'], 0)

def rem_term(rc, na, nb, dvv, kv):
    L = cell_L(rc, d2_low(na, nb, dvv))
    den = rc['K3'] * sq(L)
    t = cdiv(kv * rc['K1'] * (rc['K2'] + rc['Cbn'] * L), den) if den > 0 else 0
    return t, (0 < L and rc['lam2'] <= 25 * L)

def corner_eval(o, segs, ci, rc, gs):
    Xt, Yt, Zt, D, rho, zeta, cc, ss = ci
    D2 = D * D; Xs, Ys, Zs = Xt * TWO32, Yt * TWO32, Zt * TWO32
    c = (D, D2, Xs, Ys, Zs, sq(Xs) + sq(Ys) + sq(Zs), D * TWO32)
    vs = []
    for fi, f in enumerate(segs):
        row = []
        for k, s in enumerate(f):
            g0 = gs[fi][k] if gs is not None else cold_start(c, s)
            row.append(vert_step(c, s, g0))
        vs.append(row)
    D3S = D2 * D * TWO136
    sx = sy = sz = tx = ty = tz = sf = rem = 0; ok = True
    for fi, f in enumerate(segs):
        row = vs[fi]
        for k, s in enumerate(f):
            a = row[k]; b = row[(k + 1) % len(row)]
            ab = a[1] * b[1]; dvv = D2 * s['vv']; tc = a[0] + b[0]
            den = ab * max(2 * ab + tc - dvv, 0)
            fv = (2 * (a[1] + b[1]) * D3S) // den if den > 0 else 0
            if rc is not None: rt = rem_term(rc, a[0], b[0], dvv, s['kv'])
            else: rt = (0, True)
            sx += fv * s['w1'][0]; sy += fv * s['w1'][1]; sz += fv * s['w1'][2]
            tx += fv * s['w2'][0]; ty += fv * s['w2'][1]; tz += fv * s['w2'][2]
            sf += fv; rem += rt[0]
            ok = ok and a[2] and b[2] and dvv <= ab + tc and rt[1]
    S1 = (sx - o[0] * sf, sy - o[1] * sf, sz - o[2] * sf); S2 = (tx - o[3] * sf, ty - o[4] * sf, tz - o[5] * sf)
    T = (D * S1[0] - TWO32 * (Yt * S2[2] - Zt * S2[1]), D * S1[1] - TWO32 * (Zt * S2[0] - Xt * S2[2]),
         D * S1[2] - TWO32 * (Xt * S2[1] - Yt * S2[0]))
    lam = D * TWO32
    E1 = cdiv(70 * KT * o[6] * sf, lam) + NSEG * o[6]; E2 = cdiv(70 * KT * o[7] * sf, lam) + NSEG * o[7]
    R = (D * E1 + TWO32 * (Yt + Zt) * E2, D * E1 + TWO32 * (Zt + Xt) * E2, D * E1 + TWO32 * (Xt + Yt) * E2)
    SE = D * TWO136
    h = hel_q(rho, zeta, cc, ss)
    m = []
    for k in range(3):
        fl = math.floor(h[k] * SE); ce = math.ceil(h[k] * SE)
        m.append(max(abs(T[k] - R[k] - ce), abs(T[k] + R[k] - fl)))
    N = (sq(m[0]) + sq(m[1]) + sq(m[2])) * sq(TWO40)
    sN = nstK(N, 6, (m[0] + m[1] + m[2]) * TWO40) + 1
    ok = ok and N <= sq(sN) and 1000 * KT <= lam and (rc is None or rc['rBD'] <= rc['s0l'])
    return ok, cdiv(sN, SE), rem, [[v[3] for v in row] for row in vs]

# ------------------------------------------------------------------ faces
HELH = {0: (19, 25, 223, 100), 1: (3, 2, 19, 5), 2: (147, 100, 17, 2), 3: (147, 100, 17, 2)}

def cyl_r(kind): return 199 if kind == 0 else 161

def face_rz(kind, wd, wn):
    if kind < 2: return Fr(cyl_r(kind), 181), (cyl_r(kind), 181), (wn, wd)
    return None, (wn, wd), ((3420 if kind == 2 else -3420), 32761)

def corner_in(kind, wd, m, wn):
    q = QT; cd = q * q + m * m; cn = q * q - m * m; sn = 2 * m * q
    _, (rn, rd), (zn, zd) = face_rz(kind, wd, wn)
    D = rd * cd * zd
    return (rn * cn * zd + 4 * D, rn * sn * zd + 4 * D, zn * rd * cd + 4 * D, D,
            Fr(rn, rd), Fr(zn, zd), Fr(cn, cd), Fr(sn, cd))

def cell_rc(kind, wd, m, m1, wn, wn1, D):
    a1 = 2 * (m1 - m) * QT; b1 = QT * QT + m * m
    a2 = cyl_r(kind) if kind < 2 else wn1; b2 = 181 if kind < 2 else wd
    a3 = wn1 - wn; b3 = wd
    rB = cdiv((a2 * a1 * b3 + a3 * b1 * b2) * TWO32, b1 * b2 * b3)
    Cd = b1 * b1 * b2 * b2 * b3 * b3
    Can = 6 * (a1 * a1 * a2 * a2 * b3 * b3 + a3 * a3 * b1 * b1 * b2 * b2)
    Cbn = 10 * a1 * a1 * a2 * b2 * b3 * b3
    h = HELH[kind]
    hterm = cdiv((a1 * a1 * h[0] * h[3] * b3 * b3 + a3 * a3 * h[2] * h[1] * b1 * b1) * TWO40,
                 8 * b1 * b1 * b3 * b3 * h[1] * h[3])
    rc = dict(s0l=D * TWO30, rBD=rB * D, lam2=sq(D * TWO32), K1=D * D * TWO40, K2=Can * D * D * TWO64, K3=8 * Cd, Cbn=Cbn)
    return rc, hterm

def line_out(o, segs, kind, wd, wns, m, m1):
    out = []; gs = None
    for j, wn in enumerate(wns):
        ci = corner_in(kind, wd, m, wn)
        if m1 is not None and j + 1 < len(wns): rc, ht = cell_rc(kind, wd, m, m1, wn, wns[j + 1], ci[3])
        else: rc, ht = None, 0
        ok, e, rem, gs = corner_eval(o, segs, ci, rc, gs)
        out.append((ok, e, rem + ht))
    return out

def cells_ok(prev, cur):
    worst = None
    for j in range(len(prev) - 1):
        a, a1, b, b1 = prev[j], prev[j + 1], cur[j], cur[j + 1]
        tot = max(a[1], a1[1], b[1], b1[1]) + a[2]
        okc = a[0] and a1[0] and b[0] and b1[0] and tot <= ETAFP
        if not okc: return False, None
        worst = ETAFP - tot if worst is None else min(worst, ETAFP - tot)
    return True, worst

def w_grid(kind, n, profile=None):
    """w-grid numerators over a common denominator wd (endpoints exact)."""
    M = 64 * n
    if kind < 2: wd = 32761 * M; lo, hi = -3420 * M, 3420 * M
    else: wd = 181 * M; lo, hi = 161 * M, 199 * M
    if profile is None:
        return wd, [lo + (hi - lo) * j // n for j in range(n + 1)]
    xs, dens = profile
    cum = np.concatenate([[0], np.cumsum((dens[1:] + dens[:-1]) / 2 * np.diff(xs))]); cum /= cum[-1]
    pts = np.interp(np.linspace(0, 1, n + 1), cum, xs)
    wn = [lo] + [int(round(lo + (hi - lo) * p)) for p in pts[1:-1]] + [hi]
    return wd, wn

# ------------------------------------------------------------------ adaptive grid
def gen_face(o, segs, kind, wd, wns, verbose=True):
    q = QT
    m0 = math.floor((math.sqrt(2) - 1) * q); mN = math.ceil((math.sqrt(2) + 1) * q)
    ms = [m0]; worst = None; step = 8; t0 = time.time()
    while ms[-1] < mN:
        m = ms[-1]
        st = step
        def rem_ok(st):
            m1 = min(m + st, mN)
            prev = line_out(o, segs, kind, wd, wns, m, m1)
            emax = max(p[1] for p in prev)
            return all(p[0] for p in prev) and max(p[2] for p in prev[:-1]) + emax * 1.15 + 3e-6 * TWO40 <= ETAFP, prev
        okr, prev = rem_ok(st)
        if okr:
            while True:
                ok2, prev2 = rem_ok(int(st * 1.15) + 1)
                if ok2 and m + st < mN: st = int(st * 1.15) + 1; prev = prev2
                else: break
        else:
            while st > 1:
                st = max(1, int(st * 0.8)); okr, prev = rem_ok(st)
                if okr: break
        while True:
            m1 = min(m + st, mN)
            prev = line_out(o, segs, kind, wd, wns, m, m1)
            cur = line_out(o, segs, kind, wd, wns, m1, None)
            good, w = cells_ok(prev, cur)
            if good or st == 1: break
            st = max(1, int(st * 0.85))
        if not good: print('FAIL at', m); return None
        worst = w if worst is None else min(worst, w)
        ms.append(m1); step = st
        if verbose and len(ms) % 25 == 0:
            print(' face', kind, 'line', len(ms), 't', m1 / q, 'step', st, 'worst', worst / TWO40, 'time', round(time.time() - t0), flush=True)
    return ms, worst

def check_chunk(o, segs, kind, wd, wns, ms):
    prev = line_out(o, segs, kind, wd, wns, ms[0], ms[1]); worst = None
    for i in range(1, len(ms)):
        cur = line_out(o, segs, kind, wd, wns, ms[i], ms[i + 1] if i + 1 < len(ms) else None)
        good, w = cells_ok(prev, cur)
        if not good: return False, i
        worst = w if worst is None else min(worst, w)
        prev = cur
    return True, worst

def m_profile(o, segs, kind, wd, nsamp=60):
    """crude density profile along w: sqrt of the per-cell remainder weight (float)."""
    wd0, wn0 = w_grid(kind, nsamp)
    q = QT
    ms = [int(t * q) for t in np.linspace(math.sqrt(2) - 1, math.sqrt(2) + 1, 9)]
    dens = np.zeros(nsamp + 1)
    for m in ms:
        out = line_out(o, segs, kind, wd0, wn0, m, m + 1)
        for j in range(nsamp):
            dens[j] = max(dens[j], out[j][2])
    dens[-1] = dens[-2]
    xs = np.array([(w - wn0[0]) / (wn0[-1] - wn0[0]) for w in wn0])
    return xs, np.sqrt(np.maximum(dens, 1))

if __name__ == "__main__":
    reps = load_design(sys.argv[1]); fils = full_filaments(reps); o = offsets(fils); segs = all_segs(o, fils)
    kind = int(sys.argv[2]); nw = int(sys.argv[3]); nonu = len(sys.argv) > 4 and sys.argv[4] == 'nonuniform'
    prof = None
    if nonu:
        xs, d = m_profile(o, segs, kind, None)
        prof = (xs, d)
    wd, wns = w_grid(kind, nw, prof)
    r = gen_face(o, segs, kind, wd, wns)
    if r:
        ms, worst = r
        print('RESULT face', kind, 'nw', nw, 'nonu', nonu, 'lines', len(ms), 'cells', (len(ms) - 1) * nw, 'corners', len(ms) * (nw + 1), 'worst', worst / TWO40)
        pickle.dump(dict(face=kind, nw=nw, wd=wd, wn=wns, ms=ms, reps=reps), open(f'/tmp/pd/grid2_{kind}_{nw}_{int(nonu)}.pkl', 'wb'))
