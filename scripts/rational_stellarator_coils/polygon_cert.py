"""UNTRUSTED generator and exact-integer simulator for the polygonal-coil frontier certificate.

It (1) rounds a symmetric design from polygon_design.py to dyadic data, (2) builds per-face
(t, w) grids, and (3) runs an exact Python-integer replica of the Lean checker
`PlasmaLean/Design/PolygonCoilCheck.lean` (same formulas, same rounding), reporting the margin of
every cell.  Nothing here is trusted: the Lean kernel re-runs the checker.
"""
import numpy as np, pickle, sys, math, time
from fractions import Fraction as Fr

B = 32            # vertex scale 2^-B
OFF = 4           # translation of all coordinates (makes them positive)
KTOL = 1 << 20    # sqrt tolerance
Q = 40            # scale of f
Q2 = 40           # scale of final bounds
TQ = 12           # t = m / 2^TQ
AN, AD = 3420, 32761          # a = 3420/32761 (1 +- 2a are squares of 199/181, 161/181)
RO, RI, RD = 199, 161, 181
S0SH = B - 2      # s0 = 1/4  -> s0*lambda = 2^(B-2) * D
DGLOB = Fr(1, 5)  # global lower bound for coil distances (checked per segment via L)

def isqrt_floor(n):
    return math.isqrt(n)

# ---------------------------------------------------------------- data
def load_design(fn):
    d = pickle.load(open(fn, 'rb'))
    Z, Ir = d['Z'], d['Ir']
    reps = []
    for r in range(len(Z)):
        verts = [tuple(int(round(c * 2 ** B)) for c in v) for v in Z[r]]
        K = int(round(abs(Ir[r]) / (4 * math.pi) * 2 ** B))
        sgn = 1 if Ir[r] > 0 else -1
        reps.append((sgn * K, verts))
    return reps

def gR(p): return (-p[0], -p[1], p[2])
def gS(p): return (p[1], p[0], -p[2])
GROUP = [(lambda p: p, 1), (gR, 1), (gS, -1), (lambda p: gR(gS(p)), -1)]

def full_segments(reps):
    segs = []
    for (K, verts) in reps:
        for (g, eps) in GROUP:
            gv = [g(v) for v in verts]
            n = len(gv)
            for j in range(n):
                segs.append((eps * K, gv[j], gv[(j + 1) % n]))
    return segs

def seg_consts(segs):
    """per segment: translated P', V, VV, W1 (signed), W2 (signed), W1max, W2max, KV."""
    out = []
    for (Ks, p, q) in segs:
        Pt = tuple(c + OFF * 2 ** B for c in p)
        V = tuple(q[i] - p[i] for i in range(3))
        VV = sum(v * v for v in V)
        cr = (Pt[1] * V[2] - Pt[2] * V[1], Pt[2] * V[0] - Pt[0] * V[2], Pt[0] * V[1] - Pt[1] * V[0])
        W1 = tuple(Ks * c for c in cr); W2 = tuple(Ks * v for v in V)
        Vup = isqrt_floor(VV) + 1
        out.append(dict(P=Pt, V=V, VV=VV, W1=W1, W2=W2, W1m=max(abs(c) for c in W1),
                        W2m=max(abs(c) for c in W2), KV=abs(Ks) * Vup))
    return out

# ---------------------------------------------------------------- hel (exact)
def hel_polar(rho, zeta, c, s):
    al = rho / 8 - 1 / (8 * rho); be = -rho * zeta / 8 + 3 * zeta / (8 * rho)
    ga = 1 / (8 * rho) + zeta ** 2 / (2 * rho ** 3) - 1 / (8 * rho ** 3)
    de = -3 * zeta / (8 * rho) - zeta ** 3 / (2 * rho ** 3) + 5 * zeta / (8 * rho ** 3)
    ep = -rho ** 2 / 16 + Fr(3, 8) + 3 * zeta ** 2 / (4 * rho ** 2) - 5 / (16 * rho ** 2)
    ze = -zeta / (2 * rho ** 2)
    c3 = 4 * c ** 3 - 3 * c; s3 = 3 * s - 4 * s ** 3; c2 = c * c - s * s; s2 = 2 * c * s
    return (al * c + be * s + ga * c3 + de * s3, -al * s + be * c + ga * s3 - de * c3, ep * s2 + ze * c2)

def hel_cart(x, y, z):
    r2 = x * x + y * y; w = 1 / r2
    Aq = (r2 - 1) ** 2 - 4 * z * z; Bq = (r2 - 1) * (r2 - 5) - 4 * z * z; Xd = x * x - y * y; Yp = 2 * x * y * z
    Hnum = Aq * Xd - Bq * Yp
    H0 = 4 * x * (r2 - 1) * Xd + 2 * x * Aq - 4 * x * (r2 - 3) * Yp - 2 * y * z * Bq
    H1 = 4 * y * (r2 - 1) * Xd - 2 * y * Aq - 4 * y * (r2 - 3) * Yp - 2 * x * z * Bq
    H2 = -8 * z * Xd + 8 * z * Yp - 2 * x * y * Bq
    return ((H0 * w ** 2 - 4 * x * Hnum * w ** 3) / 16, (H1 * w ** 2 - 4 * y * Hnum * w ** 3) / 16, H2 * w ** 2 / 16)

# ---------------------------------------------------------------- faces
A_ = Fr(AN, AD)
def face_info(face, nw):
    """returns function corner(m, j) -> (X, Y, Z, D, rho, zeta), and rho_max(j)."""
    q = 1 << TQ
    def corner(m, j):
        cd = q * q + m * m; cn = q * q - m * m; sn = 2 * m * q
        if face < 2:
            Rn = RO if face == 0 else RI
            zd = AD * nw; zn = AN * (2 * j - nw)
            D = RD * cd * zd
            return (Rn * cn * zd, Rn * sn * zd, zn * RD * cd, D, Fr(Rn, RD), Fr(zn, zd))
        else:
            wd = RD * nw; wn = RI * nw + (RO - RI) * j
            zn = AN if face == 2 else -AN
            D = wd * cd * AD
            return (wn * cn * AD, wn * sn * AD, zn * wd * cd, D, Fr(wn, wd), Fr(zn, AD))
    return corner

HEL = {0: (Fr(4, 5), Fr(23, 10)), 1: (Fr(13, 10), Fr(19, 5)), 2: (Fr(13, 10), Fr(77, 10)), 3: (Fr(13, 10), Fr(77, 10))}
def hel_consts(face):
    """(H_phi, H_w): upper bounds for |d^2/dphi^2 <n,hel>|, |d^2/dw^2 <n,hel>| on the face (proved in Lean)."""
    return HEL[face]

def ceil_div(a, b): return -((-a) // b)

# ---------------------------------------------------------------- corner evaluation (exact replica)
def newton(n, x, fuel=60):
    for _ in range(fuel):
        y = (x + n // x) // 2
        if y < x: x = y
        else: break
    return x

def corner_eval(SC, X, Y, Z, D, guesses):
    """returns (ok, e_fp, nlist, slist) ; e_fp upper bound of |Bh(y)-hel(y)|*2^Q2 needs hel separately"""
    lam = (1 << B) * D
    Xt = (X + OFF * D, Y + OFF * D, Z + OFF * D)
    Xs = tuple(c << B for c in Xt)
    D2 = D * D; D3 = D2 * D
    ok = True
    S1 = [0, 0, 0]; S2 = [0, 0, 0]; G1 = 0; G2 = 0; amin = None
    ns = []; ss = []
    # vertex quantities (each segment start vertex; end vertex = next segment's start within filament)
    newg = []
    for idx, sc in enumerate(SC):
        P = sc['P']
        A = [P[i] * D - Xs[i] for i in range(3)]
        n = A[0] * A[0] + A[1] * A[1] + A[2] * A[2]
        g = guesses[idx] if guesses is not None else 4 * lam
        s = newton(n, g)
        al = s - KTOL // 2
        if not (al > 0 and al * al <= n and n <= (al + KTOL) ** 2): ok = False
        ns.append(n); ss.append(al); newg.append(s + s // 16 + 1)
        amin = al if amin is None else min(amin, al)
    nseg = len(SC)
    per = 16
    for idx, sc in enumerate(SC):
        f0 = (idx // per) * per; nxt = f0 + ((idx - f0 + 1) % per)
        na, nb = ns[idx], ns[nxt]; a_, b_ = ss[idx], ss[nxt]
        two_c = na + nb - D2 * sc['VV']
        ab = a_ * b_
        if not (ab + two_c >= 0): ok = False    # 2ab + 2c >= ab  (cos >= -1/2)
        den = ab * (2 * ab + two_c)
        if den <= 0: ok = False; den = 1
        f = (2 * (a_ + b_) * D3 << (3 * B + Q)) // den
        for i in range(3):
            S1[i] += f * sc['W1'][i]; S2[i] += f * sc['W2'][i]
        G1 += f * sc['W1m']; G2 += f * sc['W2m']
    C1 = sum(sc['W1m'] for sc in SC); C2 = sum(sc['W2m'] for sc in SC)
    E1 = ceil_div(7 * KTOL * G1, amin) + C1 + G1 // (1 << 50) + 1   # crude extra slack
    E2 = ceil_div(7 * KTOL * G2, amin) + C2 + G2 // (1 << 50) + 1
    T = [D * S1[0] - ((Xt[1] * S2[2] - Xt[2] * S2[1]) << B),
         D * S1[1] - ((Xt[2] * S2[0] - Xt[0] * S2[2]) << B),
         D * S1[2] - ((Xt[0] * S2[1] - Xt[1] * S2[0]) << B)]
    R = [D * E1 + ((Xt[1] + Xt[2]) * E2 << B), D * E1 + ((Xt[2] + Xt[0]) * E2 << B), D * E1 + ((Xt[0] + Xt[1]) * E2 << B)]
    return ok, T, R, ns, ss, newg

def simulate_face(SC, face, ms, nw, eta, verbose=False, maxlines=None):
    corner = face_info(face, nw)
    Hphi, Hw = hel_consts(face)
    q = 1 << TQ
    SE_sh = 3 * B + Q
    nt = len(ms) - 1
    worst = 1e9; fails = []
    prev = None
    lines = range(len(ms)) if maxlines is None else range(min(maxlines, len(ms)))
    t0 = time.time()
    for i in lines:
        m = ms[i]
        res = []
        guesses = None
        for j in range(nw + 1):
            X, Y, Z, D, rho, zeta = corner(m, j)
            ok, T, R, ns, ss, guesses = corner_eval(SC, X, Y, Z, D, guesses)
            # hel exact
            cd = q * q + m * m
            c = Fr(q * q - m * m, cd); s = Fr(2 * m * q, cd)
            h = hel_polar(rho, zeta, c, s)
            SE = D << SE_sh
            mm = []
            for k in range(3):
                hl = math.floor(h[k] * SE); hh = math.ceil(h[k] * SE)
                lo = T[k] - R[k] - hh; hi = T[k] + R[k] - hl
                mm.append(max(abs(lo), abs(hi)))
            N = sum(x * x for x in mm) << (2 * Q2)
            sN = isqrt_floor(N) + 1
            e = ceil_div(sN, SE)
            # remainder for cell (i, j)
            rem = None
            if i < nt and j < nw:
                m1 = ms[i + 1]
                dphi = Fr(2 * (m1 - m) * q, q * q + m * m)     # 2*(t1-t0)/(1+t0^2)
                if face < 2:
                    rmax = Fr(RO if face == 0 else RI, RD); dw = 2 * A_ / nw
                else:
                    rmax = Fr(RI * nw + (RO - RI) * (j + 1), RD * nw); dw = Fr(RO - RI, RD * nw)
                rcell = rmax * dphi + dw
                rB = math.ceil(rcell * (1 << B))
                Ca = 6 * dphi ** 2 * rmax ** 2 + 6 * dw ** 2
                Cb = 2 * dphi ** 2 * rmax / DGLOB
                # common denominator
                Cd = math.lcm(Ca.denominator, Cb.denominator)
                Can = Ca.numerator * (Cd // Ca.denominator); Cbn = Cb.numerator * (Cd // Cb.denominator)
                D2 = D * D; Tsum = 0
                per = 16
                for idx, sc in enumerate(SC):
                    f0 = (idx // per) * per; nxt = f0 + ((idx - f0 + 1) % per)
                    na, nb = ns[idx], ns[nxt]; dvv = D2 * sc['VV']
                    if nb >= na + dvv: d2 = na
                    elif na >= nb + dvv: d2 = nb
                    else:
                        mq = na + dvv - nb
                        d2 = na - ceil_div(mq * mq, 4 * dvv)
                    s0l = D << S0SH
                    L = d2 - ceil_div(rB * D * d2, s0l) - rB * D * s0l
                    # also need d >= DGLOB on the cell: L >= (DGLOB*lambda)^2
                    lam = D << B
                    if not (L > 0 and 25 * L >= lam * lam): ok = False; L = max(L, 1)
                    num = sc['KV'] * D2 * (Can * D2 * (1 << (2 * B)) + Cbn * L) << Q2
                    Tsum += ceil_div(num, 8 * Cd * L * L)
                hterm = math.ceil((dphi ** 2 * Hphi + dw ** 2 * Hw) / 8 * (1 << Q2))
                rem = Tsum + hterm
            res.append((ok, e, rem))
        if prev is not None:
            for j in range(nw):
                emax = max(prev[j][1], prev[j + 1][1], res[j][1], res[j + 1][1])
                tot = emax + prev[j][2]
                okc = prev[j][0] and prev[j + 1][0] and res[j][0] and res[j + 1][0]
                marg = eta * 2 ** Q2 - tot
                worst = min(worst, marg / 2 ** Q2)
                if marg < 0 or not okc: fails.append((i - 1, j, tot / 2 ** Q2, emax / 2 ** Q2, okc))
        prev = res
        if verbose and i % 20 == 0: print('line', i, 'worst margin', worst, 'fails', len(fails), 't', round(time.time() - t0), flush=True)
    return worst, fails

if __name__ == "__main__":
    reps = load_design(sys.argv[1])
    segs = full_segments(reps); SC = seg_consts(segs)
    print('segments', len(SC))
    face = int(sys.argv[2]); nw = int(sys.argv[3]); dt = float(sys.argv[4]); eta = float(sys.argv[5])
    t_lo, t_hi = math.sqrt(2) - 1, math.sqrt(2) + 1
    q = 1 << TQ
    m0 = math.floor(t_lo * q); mN = math.ceil(t_hi * q)
    # uniform-in-phi spacing: dt_i = dt*(1+t^2)/2
    ms = [m0]
    while ms[-1] < mN:
        t = ms[-1] / q; step = max(1, int(dt * (1 + t * t) / 2 * q))
        ms.append(min(ms[-1] + step, mN))
    print('face', face, 'lines', len(ms), 'nw', nw)
    worst, fails = simulate_face(SC, face, ms, nw, eta, verbose=True, maxlines=int(sys.argv[6]) if len(sys.argv) > 6 else None)
    print('worst margin', worst, 'fails', len(fails), fails[:5])

# ---------------------------------------------------------------- adaptive grid generation
def line_corners(SC, face, m, nw):
    corner = face_info(face, nw); q = 1 << TQ
    out = []; guesses = None
    for j in range(nw + 1):
        X, Y, Z, D, rho, zeta = corner(m, j)
        ok, T, R, ns, ss, guesses = corner_eval(SC, X, Y, Z, D, guesses)
        cd = q * q + m * m
        h = hel_polar(rho, zeta, Fr(q * q - m * m, cd), Fr(2 * m * q, cd))
        SE = D << (3 * B + Q)
        mm = []
        for k in range(3):
            hl = math.floor(h[k] * SE); hh = math.ceil(h[k] * SE)
            mm.append(max(abs(T[k] - R[k] - hh), abs(T[k] + R[k] - hl)))
        N = sum(x * x for x in mm) << (2 * Q2)
        e = ceil_div(math.isqrt(N) + 1, SE)
        out.append(dict(ok=ok, e=e, ns=ns, D=D))
    return out

def cell_rem(SC, face, m, m1, j, nw, cd_):
    q = 1 << TQ
    dphi = Fr(2 * (m1 - m) * q, q * q + m * m)
    if face < 2:
        rmax = Fr(RO if face == 0 else RI, RD); dw = 2 * A_ / nw
    else:
        rmax = Fr(RI * nw + (RO - RI) * (j + 1), RD * nw); dw = Fr(RO - RI, RD * nw)
    rB = math.ceil((rmax * dphi + dw) * (1 << B))
    Ca = 6 * dphi ** 2 * rmax ** 2 + 6 * dw ** 2
    Cb = 2 * dphi ** 2 * rmax / DGLOB
    Cd = math.lcm(Ca.denominator, Cb.denominator)
    Can = Ca.numerator * (Cd // Ca.denominator); Cbn = Cb.numerator * (Cd // Cb.denominator)
    D = cd_['D']; ns = cd_['ns']; D2 = D * D; lam = D << B; s0l = D << S0SH
    Tsum = 0; ok = True
    for idx, sc in enumerate(SC):
        nxt = (idx // 16) * 16 + ((idx % 16) + 1) % 16
        na, nb = ns[idx], ns[nxt]; dvv = D2 * sc['VV']
        if nb >= na + dvv: d2 = na
        elif na >= nb + dvv: d2 = nb
        else:
            mq = na + dvv - nb; d2 = na - ceil_div(mq * mq, 4 * dvv)
        L = d2 - ceil_div(rB * D * d2, s0l) - rB * D * s0l
        if not (L > 0 and 25 * L >= lam * lam): ok = False; L = max(L, 1)
        Tsum += ceil_div(sc['KV'] * D2 * (Can * D2 * (1 << (2 * B)) + Cbn * L) << Q2, 8 * Cd * L * L)
    Hphi, Hw = hel_consts(face)
    return ok, Tsum + math.ceil((dphi ** 2 * Hphi + dw ** 2 * Hw) / 8 * (1 << Q2))

def gen_face(SC, face, nw, eta, verbose=True):
    q = 1 << TQ
    m0 = math.floor((math.sqrt(2) - 1) * q); mN = math.ceil((math.sqrt(2) + 1) * q)
    etaf = int(eta * 2 ** Q2)
    ms = [m0]; cur = line_corners(SC, face, m0, nw); worst = 1e9; ncells = 0
    step = 8; t0 = time.time()
    while ms[-1] < mN:
        m = ms[-1]
        emax_cur = max(c['e'] for c in cur)
        def okstep(st):
            m1 = min(m + st, mN)
            for j in range(nw):
                okr, rem = cell_rem(SC, face, m, m1, j, nw, cur[j])
                e_est = max(cur[j]['e'], cur[j + 1]['e']) * 1.15 + int(3e-6 * 2 ** Q2)
                if not okr or e_est + rem > etaf: return False
            return True
        st = max(1, step)
        while st > 1 and not okstep(st): st = int(st * 0.85)
        while okstep(int(st * 1.1) + 1) and m + st < mN: st = int(st * 1.1) + 1
        while True:
            m1 = min(m + st, mN)
            nxt = line_corners(SC, face, m1, nw)
            good = True; wl = 1e9
            for j in range(nw):
                okr, rem = cell_rem(SC, face, m, m1, j, nw, cur[j])
                emax = max(cur[j]['e'], cur[j + 1]['e'], nxt[j]['e'], nxt[j + 1]['e'])
                okc = okr and cur[j]['ok'] and cur[j + 1]['ok'] and nxt[j]['ok'] and nxt[j + 1]['ok']
                marg = etaf - emax - rem
                wl = min(wl, marg)
                if marg < 0 or not okc: good = False
            if good or st == 1: break
            st = max(1, int(st * 0.8))
        if not good: print('FAIL at line', len(ms), flush=True); return None
        worst = min(worst, wl / 2 ** Q2)
        ms.append(m1); cur = nxt; step = st; ncells += nw
        if verbose and len(ms) % 25 == 0:
            print(' face', face, 'line', len(ms), 't', m1 / q, 'step', st, 'worst', worst, 'time', round(time.time() - t0), flush=True)
    return ms, worst, ncells
