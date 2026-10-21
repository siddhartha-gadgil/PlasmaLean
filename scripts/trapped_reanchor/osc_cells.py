#!/usr/bin/env python3
"""Untrusted prototype of the oscillatory-kick cell enclosure (Phase 12c, trapped alphas).

Mirrors the planned Lean checker (`NearAxisQATrappedOscCells`): for a parameter box
(psi0, Bt) it encloses, per exact-QA bounce,

  C/(q iota0) = kg * int w cos(2(phi - phi0)) dt * A ... (see the module docstring),
  S/(q iota0) likewise with sin, the precession Delta = phi(P) - phi0 and the period P,

by cells: x-cells of width h on the flanks (|sin theta| >= 3/5, coordinate x = |psi - psi0|),
u-cells (u = sin theta) at the bottom (|u| <= 3/5).  The phase phi - phi0 is accumulated by
cumulative cell sums of dphi/dx (flank) and dphi/du (bottom).  Plain float intervals (no outward
rounding): numbers only guide the choice of grids.

Usage: python3 -I osc_cells.py psi_lo psi_hi Bt_lo Bt_hi [nx] [nsub] [nu]
"""
import math
import sys

LAM = 6408800 * 44521 / (465129 * 843902500)
QM = 2 * 1.6022e-19 / 6.6447e-27
KINV = 211 / 29050
G = 58.1
KPHI = QM * KINV / G / 1e6        # dphi/dt in 1e6/s = KPHI * x * B^2 (sign by leg)
IOTA = 211 / 500
KG = 2 * 43e-5 / IOTA             # -2 b1 / iota0


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        self.lo = lo
        self.hi = lo if hi is None else hi
        assert self.lo <= self.hi + 1e-15, (lo, hi)

    def __add__(s, o):
        o = o if isinstance(o, I) else I(o)
        return I(s.lo + o.lo, s.hi + o.hi)

    __radd__ = __add__

    def __sub__(s, o):
        o = o if isinstance(o, I) else I(o)
        return I(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return I(o) - s

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        p = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(min(p), max(p))

    __rmul__ = __mul__

    def inv(s):
        assert s.lo > 0 or s.hi < 0, (s.lo, s.hi)
        return I(1 / s.hi, 1 / s.lo)

    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        return s * o.inv()

    def __rtruediv__(s, o):
        return I(o) * s.inv()

    def sq(s):
        if s.lo >= 0:
            return I(s.lo ** 2, s.hi ** 2)
        if s.hi <= 0:
            return I(s.hi ** 2, s.lo ** 2)
        return I(0, max(s.lo ** 2, s.hi ** 2))

    def sqrt(s):
        assert s.lo >= -1e-15
        return I(math.sqrt(max(s.lo, 0)), math.sqrt(s.hi))

    def meet(s, lo=None, hi=None):
        a = s.lo if lo is None else max(s.lo, lo)
        b = s.hi if hi is None else min(s.hi, hi)
        return I(a, max(a, b))

    def w(s):
        return s.hi - s.lo


def cosI(X):
    # exact range of cos over X
    lo, hi = X.lo, X.hi
    vals = [math.cos(lo), math.cos(hi)]
    k0 = math.ceil(lo / math.pi)
    k = k0
    while k * math.pi <= hi:
        vals.append(1.0 if k % 2 == 0 else -1.0)
        k += 1
    return I(min(vals), max(vals))


def sinI(X):
    return cosI(X - math.pi / 2)


def psiI(inner, X, P):
    return P - X if inner else P + X


def BsI(X, T):
    return 2 * T / (1 + (1 + 4 * LAM * (T.sq() * X.sq())).sqrt())


def cI(inner, X, P, T):
    w = (20 / 57) * psiI(inner, X, P)
    cc = 5.7 - 0.0302 * w - BsI(X, T)
    return 2 * cc / (w.sqrt() * (0.399 + (0.159201 - 0.132 * cc).sqrt()))


def numI(inner, X, P, c):
    w = (20 / 57) * psiI(inner, X, P)
    return 0.07 * c / w.sqrt() + (20 / 57) * (0.0302 - 0.033 * c.sq())


def denI(inner, X, P, c, s):
    w = (20 / 57) * psiI(inner, X, P)
    return s * (0.399 * w.sqrt() - 0.066 * w * c)


def AmI(X, T):
    B = BsI(X, T)
    return 1.75 * (2 * T - B) / (T * B)


def ratI(inner, X, P, T, c):
    B = BsI(X, T)
    R = 2 * LAM * (T * X) * (B * B.sq()) / ((2 * T - B) * numI(inner, X, P, c))
    return (1 + R).inv() if inner else (R - 1).inv()


CD = math.cos(0.6)   # flank/bottom split at |theta| = 3/5


def KRI(X, T):
    """K = 2 lam Bt x B^3/(2 Bt - B): ratR = num/(K + num) (inner), num/(K - num) (outer)."""
    B = BsI(X, T)
    return 2 * LAM * (T * X) * (B * B.sq()) / (2 * T - B)


def flank_cells(inner, P, T, nx, h):
    """Per x-cell: None (dead) or (Omega/xdot, |dphi/dx|, w/den, dt/dx, c)."""
    out = []
    for i in range(nx):
        X = I(i * h, (i + 1) * h)
        c = cI(inner, X, P, T)
        if c.lo > CD:
            out.append(None)
            continue
        c = c.meet(0.0, CD)
        s = (1 - c.sq()).sqrt().meet(math.sin(0.6), None)
        den = denI(inner, X, P, c, s)
        A = AmI(X, T)
        B = BsI(X, T)
        w = (20 / 57) * psiI(inner, X, P)
        num = numI(inner, X, P, c)
        dphi = KPHI * X * B.sq() / (A * den)
        out.append((num / den, dphi, w / den, 1 / (A * den), cI(inner, X, P, T)))
    return out


def bottom_cells(inner, P, T, nx, h, nsub, nb):
    subs = []
    for i in range(nx):
        X = I(i * h, (i + 1) * h)
        c = cI(inner, X, P, T)
        if c.hi < CD:
            continue
        for k in range(nsub):
            Xs = I(i * h + k * h / nsub, i * h + (k + 1) * h / nsub)
            subs.append((Xs, cI(inner, Xs, P, T)))
    hb = 1.2 / nb
    out = []
    for j in range(nb):
        # theta cell (in |theta|): cells ordered by theta from +3/5 down (inner) / -3/5 up (outer)
        a, b = 0.6 - (j + 1) * hb, 0.6 - j * hb      # theta range (inner orientation)
        th = I(a, b)
        aa = 0 if a < 0 < b else min(abs(a), abs(b))
        bb = max(abs(a), abs(b))
        cu = I(math.cos(bb), math.cos(aa))
        comp = [Xs for Xs, cx in subs if not (cx.hi < cu.lo or cx.lo > cu.hi)]
        assert comp, "no compatible subcell"
        X = I(min(q.lo for q in comp), max(q.hi for q in comp))
        c = cu
        num = numI(inner, X, P, c)
        K = KRI(X, T)
        A = AmI(X, T)
        w = (20 / 57) * psiI(inner, X, P)
        den = (K + num) if inner else (K - num)
        rat = num / den
        out.append((rat, th, w / den, 1 / (A * den), X))
    return out


def theta0I(P, T):
    c0 = cI(True, I(0.0), P, T)
    return I(math.acos(min(c0.hi, 1)), math.acos(c0.lo))


def flank_sum(fc, h, nlast, nfull, phase_of, Isum0, forward):
    """Contributions of one flank piece.  phase_of(i, acc_lo, acc_hi) gives Phi in cell i given
    the accumulated int |dphi| from the tip over full cells below i (lo) and up to i (hi)."""
    Cs = I(0.0)
    Ss = I(0.0)
    ts = I(0.0)
    acc_lo = acc_hi = 0.0
    for i in range(nlast + 1):
        if fc[i] is None:
            continue
        om, dphi, gx, tx, _ = fc[i]
        ph = phase_of(acc_lo, acc_hi + h * dphi.hi)
        full = i < nfull
        cterm = gx * cosI(ph) * h
        sterm = gx * sinI(ph) * h
        if not full:
            cterm = I(min(cterm.lo, 0), max(cterm.hi, 0))
            sterm = I(min(sterm.lo, 0), max(sterm.hi, 0))
        Cs += cterm
        Ss += sterm
        ts += (tx * h if full else I(0, (tx * h).hi))
        acc_lo += h * dphi.lo
        acc_hi += h * dphi.hi
    return Cs, Ss, ts


def run(P, T, nx=100, nsub=8, nb=48, verbose=True):
    h = 2.5 / nx
    hb = 1.2 / nb
    Csum = I(0.0)
    Ssum = I(0.0)
    tsum = I(0.0)
    th0 = theta0I(P, T)
    Iacc = I(0.0)        # cumulative precession integral I(t)
    Phi_tip = I(0.0)     # Phi at the leg's starting tip
    for inner in (True, False):
        sgn = -1 if inner else 1
        fc = flank_cells(inner, P, T, nx, h)
        bc = bottom_cells(inner, P, T, nx, h, nsub, nb)
        alive = [i for i in range(nx) if fc[i] is not None]
        nlast = max(alive)
        nfull = 0
        while fc[nfull] is not None and fc[nfull][4].hi < CD:
            nfull += 1
        Iflank = I(sum(h * fc[i][0].lo for i in range(nfull)),
                   sum(h * fc[i][0].hi for i in alive))
        # first flank (forward from the tip): Phi = Phi_tip + 2 sgn int |dphi|
        cs, ss, ts = flank_sum(fc, h, nlast, nfull,
                               lambda lo, hi: Phi_tip + 2 * sgn * I(lo, hi), None, True)
        Csum += cs; Ssum += ss; tsum += ts
        Iacc = Iacc + Iflank
        # bottom: theta-based phase, Phi = 2(theta - theta0 + I)/iota
        lo_acc = hi_acc = 0.0
        for j in range(nb):
            rat, th, gy, ty, _ = bc[j]
            thv = th if inner else -th
            Icur = Iacc + I(lo_acc, hi_acc + hb * rat.hi)
            ph = (2 / IOTA) * (thv - th0 + Icur)
            Csum += gy * cosI(ph) * hb
            Ssum += gy * sinI(ph) * hb
            tsum += ty * hb
            lo_acc += hb * rat.lo
            hi_acc += hb * rat.hi
        Iacc = Iacc + I(lo_acc, hi_acc)
        Iacc = Iacc + Iflank
        # tip at the end of the leg
        if inner:
            Phi_end = (2 / IOTA) * (-2 * th0 + Iacc)
        else:
            Phi_end = (2 / IOTA) * Iacc
        # second flank (backward from the end tip): Phi = Phi_end - 2 sgn int |dphi|
        cs, ss, ts = flank_sum(fc, h, nlast, nfull,
                               lambda lo, hi: Phi_end - 2 * sgn * I(lo, hi), None, False)
        Csum += cs; Ssum += ss; tsum += ts
        Phi_tip = Phi_end
    C = KG * Csum
    S = KG * Ssum
    Delta = Iacc * (1 / IOTA)
    sinD = sinI(Delta)
    sabs = min(abs(sinD.lo), abs(sinD.hi)) if sinD.lo * sinD.hi > 0 else 0.0
    cmax = max(abs(C.lo), abs(C.hi))
    smax = max(abs(S.lo), abs(S.hi))
    Meff = math.sqrt(cmax ** 2 + smax ** 2) / sabs if sabs > 0 else float("inf")
    if verbose:
        print(f"box psi0=[{P.lo},{P.hi}] Bt=[{T.lo},{T.hi}]  theta0 in [{th0.lo:.4f},{th0.hi:.4f}]")
        print(f"  C/(q i0) in [{C.lo:.5f},{C.hi:.5f}]  S/(q i0) in [{S.lo:.5f},{S.hi:.5f}]")
        print(f"  Delta in [{Delta.lo:.4f},{Delta.hi:.4f}]  period (us) in [{tsum.lo:.2f},{tsum.hi:.2f}]")
        print(f"  M_eff = {Meff:.4f}")
    return C, S, Delta, tsum, Meff


if __name__ == "__main__":
    a = [float(v) for v in sys.argv[1:5]]
    nx = int(sys.argv[5]) if len(sys.argv) > 5 else 100
    nsub = int(sys.argv[6]) if len(sys.argv) > 6 else 8
    nb = int(sys.argv[7]) if len(sys.argv) > 7 else 48
    run(I(a[0], a[1]), I(a[2], a[3]), nx, nsub, nb)
