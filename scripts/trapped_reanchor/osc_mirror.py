#!/usr/bin/env python3
"""Exact integer mirror of the Lean checker `Design/NearAxisQATrappedOscCells.oscBoxOk`.

Untrusted: it reproduces bit for bit (scaled integers, `2^32` fixed point, the same rounding)
the computations of `FIv` (`Certificates/ValidatedQuadrature`), `FIvX` and the cell pipeline of
`Design/NearAxisQATrappedCells`, `Design/NearAxisQATrappedTimeCells`,
`Design/NearAxisQATrappedOscTrig`, `Design/NearAxisQATrappedOscCells`, with memoisation, so that
box results (enclosures of C-hat, S-hat, iota0 Delta, the bounce time) can be computed in a
fraction of a second.  It is used to choose the oracle data of the kernel checks (theta0
bounds, the box grid, the amplitude targets) and to predict the outcome of each check.

All divisors in the checker are positive, so Lean's `Int./` (Euclidean) agrees with `//`.
"""
import math
import sys
from functools import lru_cache

S = 4294967296


class F:
    __slots__ = ("lo", "hi", "ok")

    def __init__(self, lo, hi, ok=True):
        self.lo, self.hi, self.ok = lo, hi, ok

    def __repr__(self):
        return f"F({self.lo},{self.hi},{self.ok})"

    def val(self):
        return (self.lo / S, self.hi / S)

    def key(self):
        return (self.lo, self.hi, self.ok)


def ediv(a, d):
    assert d > 0
    return a // d


def ofInt(n):
    return F(n * S, n * S, True)


def ofFrac(p, q):
    if q > 0:
        return F(ediv(p * S, q), -ediv(-(p * S), q), True)
    return F(0, 0, False)


C = ofFrac


def add(I, J):
    return F(I.lo + J.lo, I.hi + J.hi, I.ok and J.ok)


def neg(I):
    return F(-I.hi, -I.lo, I.ok)


def sub(I, J):
    return F(I.lo - J.hi, I.hi - J.lo, I.ok and J.ok)


def mul(I, J):
    a, b, c, d = I.lo * J.lo, I.lo * J.hi, I.hi * J.lo, I.hi * J.hi
    return F(ediv(min(min(a, b), min(c, d)), S), -ediv(-(max(max(a, b), max(c, d))), S),
             I.ok and J.ok)


def sq(I):
    if 0 <= I.lo:
        return F(ediv(I.lo * I.lo, S), -ediv(-(I.hi * I.hi), S), I.ok)
    if I.hi <= 0:
        return F(ediv(I.hi * I.hi, S), -ediv(-(I.lo * I.lo), S), I.ok)
    return F(0, -ediv(-(max(I.lo * I.lo, I.hi * I.hi)), S), I.ok)


def inv(I):
    if 0 < I.lo:
        return F(ediv(S * S, I.hi), -ediv(-(S * S), I.lo), I.ok)
    return F(0, 0, False)


def natdiv(a, b):
    return 0 if b == 0 else a // b


def isqrtAux(k, n, g):
    while k > 0:
        ng = (g + natdiv(n, g)) // 2
        if ng < g:
            g = ng
            k -= 1
        else:
            return g
    return g


def isqrt(n):
    return isqrtAux(64, n, n // 4294967296 + 4294967296)


def toNat(x):
    return x if x > 0 else 0


def sqrt(I):
    a = isqrt(toNat(I.lo * S))
    lo = a if a * a <= I.lo * S else 0
    b = isqrt(toNat(I.hi * S))
    return F(lo, b + 1, I.ok and (I.hi * S <= (b + 1) * (b + 1)))


def dv(I, J):
    return mul(I, inv(J))


def meetHi(I, b):
    return F(I.lo, min(I.hi, b), I.ok)


def meetLo(I, b):
    return F(max(I.lo, b), I.hi, I.ok)


def hull(p1, q1, p2, q2):
    return F(ofFrac(p1, q1).lo, ofFrac(p2, q2).hi, True)


# ---------------------------------------------------------------- cells (NearAxisQATrappedCells)
lamI = C(6408800 * 44521, 465129 * 843902500)
cdLo = C(8248, 10000).lo
cdHi = C(8254, 10000).hi
sdLo = C(564, 1000).lo


def psiI(inner, X, P):
    return sub(P, X) if inner else add(P, X)


def wI(inner, X, P):
    return mul(C(20, 57), psiI(inner, X, P))


def BsI(X, T):
    return dv(mul(C(2, 1), T), add(C(1, 1), sqrt(add(C(1, 1), mul(mul(C(4, 1), lamI),
                                                                  mul(sq(T), sq(X)))))))


def ccI(inner, X, P, T):
    return sub(sub(C(57, 10), mul(C(302, 10000), wI(inner, X, P))), BsI(X, T))


def cI(inner, X, P, T):
    cc = ccI(inner, X, P, T)
    return dv(mul(C(2, 1), cc), mul(sqrt(wI(inner, X, P)),
                                    add(C(399, 1000), sqrt(sub(C(159201, 1000000),
                                                               mul(C(132, 1000), cc))))))


def numI(inner, X, P, c):
    return add(dv(mul(C(7, 100), c), sqrt(wI(inner, X, P))),
               mul(C(20, 57), sub(C(302, 10000), mul(C(33, 1000), sq(c)))))


def denI(inner, X, P, c, s):
    return mul(s, sub(mul(C(399, 1000), sqrt(wI(inner, X, P))),
                      mul(mul(C(66, 1000), wI(inner, X, P)), c)))


def cellX(i):
    return hull(i, 40, i + 1, 40)


# ---------------------------------------------------------------- time cells
def AmI(X, T):
    return dv(mul(C(7, 4), sub(mul(C(2, 1), T), BsI(X, T))), mul(T, BsI(X, T)))


def flankC(inner, X, P, T):
    return meetLo(meetHi(cI(inner, X, P, T), cdHi), 0)


def flankS(inner, X, P, T):
    return meetLo(sqrt(sub(C(1, 1), sq(flankC(inner, X, P, T)))), sdLo)


def flankDen(inner, X, P, T):
    return denI(inner, X, P, flankC(inner, X, P, T), flankS(inner, X, P, T))


# ---------------------------------------------------------------- trig
def meetI(I, J):
    return F(max(I.lo, J.lo), min(I.hi, J.hi), I.ok and J.ok)


unitI = F(-S, S, True)


def pmI(R):
    return F(-R.hi, R.hi, R.ok)


def magI(I):
    return F(0, max(-I.lo, I.hi), I.ok)


def okT(Y):
    return Y.ok and (max(-Y.lo, Y.hi) <= S)


def taylorC(Y):
    return add(sub(C(1, 1), mul(C(1, 2), sq(Y))), pmI(mul(sq(sq(magI(Y))), C(5, 96))))


def taylorS(Y):
    return add(sub(Y, mul(C(1, 6), mul(Y, sq(Y)))),
               pmI(mul(mul(sq(sq(magI(Y))), magI(Y)), C(1, 100))))


def taylorCS(Y):
    c, s = taylorC(Y), taylorS(Y)
    return (F(c.lo, c.hi, c.ok and okT(Y)), F(s.lo, s.hi, s.ok and okT(Y)))


halfPiI = F(6746518852, 6746518853, True)


def dblQ(p):
    return (sub(C(1, 1), mul(C(2, 1), sq(p[1]))), mul(C(2, 1), mul(p[1], p[0])))


def dbl4(p):
    return dblQ(dblQ(dblQ(dblQ(p))))


def rotQ(r, p):
    if r == 0:
        return p
    if r == 1:
        return (neg(p[1]), p[0])
    if r == 2:
        return (neg(p[0]), neg(p[1]))
    return (p[1], neg(p[0]))


@lru_cache(maxsize=None)
def cosSinQ(n):
    q = ediv(2 * n + 6746518852, 2 * 6746518852)
    Y = mul(sub(F(n, n, True), mul(ofInt(q), halfPiI)), C(1, 16))
    return rotQ(q % 4, dbl4(taylorCS(Y)))


def midI(P):
    return ediv(P.lo + P.hi, 2)


def radI(P):
    return max(midI(P) - P.lo, P.hi - midI(P))


def cosSmall(D):
    return F(sub(C(1, 1), mul(C(1, 2), sq(D))).lo, S, D.ok)


def cosSinC(P):
    D = F(-radI(P), radI(P), P.ok)
    Pc, Ps = cosSinQ(midI(P))
    return (meetI(unitI, sub(mul(Pc, cosSmall(D)), mul(Ps, D))),
            meetI(unitI, add(mul(Ps, cosSmall(D)), mul(Pc, D))))


# ---------------------------------------------------------------- osc cells
def KI(X, T):
    B = BsI(X, T)
    return dv(mul(mul(mul(C(2, 1), lamI), mul(T, X)), mul(B, sq(B))), sub(mul(C(2, 1), T), B))


zeroI = F(0, 0, True)


class OCell:
    __slots__ = ("om", "ph", "g", "tt", "ok", "dead", "full")

    def __init__(self, om, ph, g, tt, ok, dead, full):
        self.om, self.ph, self.g, self.tt, self.ok, self.dead, self.full = \
            om, ph, g, tt, ok, dead, full


def flankCellO(inner, X, P, T):
    c = cI(inner, X, P, T)
    if c.ok and cdHi < c.lo:
        return OCell(zeroI, zeroI, zeroI, zeroI, True, True, False)
    fd = flankDen(inner, X, P, T)
    om = dv(numI(inner, X, P, flankC(inner, X, P, T)), fd)
    ph = dv(KI(X, T), mul(C(211, 500), fd))
    g = dv(wI(inner, X, P), fd)
    tt = dv(C(1, 1), mul(AmI(X, T), fd))
    ok = om.ok and ph.ok and g.ok and tt.ok and (0 <= om.lo) and (0 <= ph.lo)
    return OCell(om, ph, g, tt, ok, False, c.ok and (c.hi < cdLo))


def kOf(j):
    return 23 - j if j <= 23 else j - 24


@lru_cache(maxsize=None)
def CTI_(k):
    a = cosSinC(C(k + 1, 40))[0]
    b = cosSinC(C(k, 40))[0]
    return (a.lo, b.hi, a.ok and b.ok)


def CTI(k):
    return F(*CTI_(k))


def bcI(k):
    return meetHi(meetLo(CTI(k), cdLo), S)


def subList(inner, P, T):
    out = []
    for i in range(100):
        c = cI(inner, cellX(i), P, T)
        if c.ok and c.hi < cdLo:
            continue
        out.append((cellX(i), c))
    return out


def hullScan(CT, L):
    if not L:
        return (False, 0, 0)
    p = L[0]
    r = hullScan(CT, L[1:])
    if p[1].ok and CT.ok and ((p[1].hi < CT.lo) or (CT.hi < p[1].lo)):
        return r
    return (p[0].ok, min(p[0].lo, r[1]) if r[0] else p[0].lo,
            max(p[0].hi, r[2]) if r[0] else p[0].hi)


def bDenI(inner, X, P, T, c):
    return add(KI(X, T), numI(inner, X, P, c)) if inner else sub(KI(X, T), numI(inner, X, P, c))


def bottomCellO(inner, P, T, k, sl):
    h = hullScan(CTI(k), sl)
    X = F(h[1], h[2], h[0])
    c = bcI(k)
    bd = bDenI(inner, X, P, T, c)
    om = dv(numI(inner, X, P, c), bd)
    g = dv(wI(inner, X, P), bd)
    tt = dv(C(1, 1), mul(AmI(X, T), bd))
    ok = om.ok and g.ok and tt.ok and (0 <= om.lo)
    return OCell(om, zeroI, g, tt, ok, False, True)


def accI(D, i):
    lo = sum(D[j].lo for j in range(i)) + min(D[i].lo, 0)
    hi = sum(D[j].hi for j in range(i)) + max(D[i].hi, 0)
    return mul(F(lo, hi, True), C(1, 40))


def totI(D, Fl, n):
    lo = sum((D[i].lo if Fl[i] else min(D[i].lo, 0)) for i in range(n))
    hi = sum((D[i].hi if Fl[i] else max(D[i].hi, 0)) for i in range(n))
    return mul(F(lo, hi, True), C(1, 40))


def thI(inner, j):
    return hull(23 - j, 40, 24 - j, 40) if inner else hull(j - 24, 40, j - 23, 40)


class Leg:
    def __init__(self, inner, P, T):
        self.inner = inner
        self.fc = [flankCellO(inner, cellX(i), P, T) for i in range(100)]
        sl = subList(inner, P, T)
        self.bc = [bottomCellO(inner, P, T, kOf(j), sl) for j in range(48)]
        fp = []
        acc = True
        for i in range(100):
            acc = (self.fc[i].full if i == 0 else (acc and self.fc[i].full))
            fp.append(acc)
        self.full = fp
        self.ok = all(c.ok for c in self.fc) and all(c.ok for c in self.bc)
        phs = [c.ph for c in self.fc]
        self.acc = [accI(phs, i) for i in range(100)]
        oms = [c.om for c in self.bc]
        self.accB = [accI(oms, j) for j in range(48)]
        self.flankI = totI([c.om for c in self.fc], self.full, 100)
        self.botI = totI(oms, [True] * 48, 48)
        self.flankTm = totI([c.tt for c in self.fc], self.full, 100)
        self.botTm = totI([c.tt for c in self.bc], [True] * 48, 48)

    def phF(self, A, sigma, i):
        a = mul(C(2, 1), self.acc[i])
        return add(A, a) if sigma else sub(A, a)

    def flankCS(self, A, sigma):
        Dc, Ds, ok = [], [], True
        for i in range(100):
            if self.fc[i].dead:
                Dc.append(zeroI)
                Ds.append(zeroI)
                continue
            cs = cosSinC(self.phF(A, sigma, i))
            dc, ds = mul(self.fc[i].g, cs[0]), mul(self.fc[i].g, cs[1])
            ok = ok and dc.ok and ds.ok
            Dc.append(dc)
            Ds.append(ds)
        return totI(Dc, self.full, 100), totI(Ds, self.full, 100), ok

    def phB(self, Th0, Is, j):
        return mul(C(1000, 211), add(sub(thI(self.inner, j), Th0), add(Is, self.accB[j])))

    def botCS(self, Th0, Is):
        Dc, Ds, ok = [], [], True
        for j in range(48):
            cs = cosSinC(self.phB(Th0, Is, j))
            dc, ds = mul(self.bc[j].g, cs[0]), mul(self.bc[j].g, cs[1])
            ok = ok and dc.ok and ds.ok
            Dc.append(dc)
            Ds.append(ds)
        return totI(Dc, [True] * 48, 48), totI(Ds, [True] * 48, 48), ok


def c0I(P, T):
    return cI(True, C(0, 1), P, T)


def theta0Ok(P, T, Th0):
    c0 = c0I(P, T)
    a = cosSinC(F(Th0.hi, Th0.hi, True))[0]
    b = cosSinC(F(Th0.lo, Th0.lo, True))[0]
    return (Th0.ok and 0 <= Th0.lo and Th0.lo <= Th0.hi and Th0.hi <= 3 * S and c0.ok and a.ok and b.ok
            and a.hi <= c0.lo and c0.hi <= b.lo)


def theta0_oracle(P, T, margin=64):
    c0 = c0I(P, T)
    lo = math.floor(math.acos(min(c0.hi / S, 1.0)) * S) - margin
    hi = math.ceil(math.acos(c0.lo / S) * S) + margin
    return F(lo, hi, True)


def oscBox(P, T, Th0):
    Li, Lo = Leg(True, P, T), Leg(False, P, T)
    Is1 = Li.flankI
    Iz1 = add(add(Is1, Li.botI), Li.flankI)
    Is3 = add(Iz1, Lo.flankI)
    Iz2 = add(add(Is3, Lo.botI), Lo.flankI)
    phZ1 = mul(C(1000, 211), add(mul(Th0, C(-2, 1)), Iz1))
    phZ2 = mul(C(1000, 211), Iz2)
    pieces = [Li.flankCS(zeroI, False), Li.botCS(Th0, Is1), Li.flankCS(phZ1, True),
              Lo.flankCS(phZ1, True), Lo.botCS(Th0, Is3), Lo.flankCS(phZ2, False)]
    Cs = [p[0] for p in pieces]
    Ss = [p[1] for p in pieces]
    CIv = add(add(add(add(Cs[0], Cs[1]), Cs[2]), Cs[3]), add(Cs[4], Cs[5]))
    SIv = add(add(add(add(Ss[0], Ss[1]), Ss[2]), Ss[3]), add(Ss[4], Ss[5]))
    Tm = add(add(mul(Li.flankTm, C(2, 1)), Li.botTm), add(mul(Lo.flankTm, C(2, 1)), Lo.botTm))
    sinD = cosSinC(mul(Iz2, C(500, 211)))[1]
    ok = Li.ok and Lo.ok and theta0Ok(P, T, Th0) and all(p[2] for p in pieces) and sinD.ok \
        and sinD.lo > 0
    return dict(ok=ok, C=CIv, S=SIv, Iz2=Iz2, Tm=Tm, sinD=sinD, Iz1=Iz1, pieces=pieces)


def oscBoxOk(P, T, Th0, Kn, Kd, Pmin):
    r = oscBox(P, T, Th0)
    Cm = max(-r["C"].lo, r["C"].hi)
    Sm = max(-r["S"].lo, r["S"].hi)
    return (r["ok"] and Kd * Kd * (Cm * Cm + Sm * Sm) <= Kn * Kn * (r["sinD"].lo * r["sinD"].lo)
            and Pmin * S <= r["Tm"].lo)


def K_needed(r):
    """The smallest real K with sqrt(Cm^2 + Sm^2) <= K sinD.lo (scaled units cancel)."""
    Cm = max(-r["C"].lo, r["C"].hi)
    Sm = max(-r["S"].lo, r["S"].hi)
    return math.sqrt(Cm * Cm + Sm * Sm) / r["sinD"].lo


def PBI(a, b):
    return hull(4864 + 9 * a, 1024, 4864 + 9 * b, 1024)


def TBI(c, d):
    return hull(6912 + c, 1280, 6912 + d, 1280)


if __name__ == "__main__":
    a, b, c, d = (int(v) for v in sys.argv[1:5])
    P, T = PBI(a, b), TBI(c, d)
    Th0 = theta0_oracle(P, T)
    r = oscBox(P, T, Th0)
    print("Th0", Th0, "ok", r["ok"])
    for k in ("C", "S", "Iz2", "Tm", "sinD"):
        print(k, r[k], r[k].val())
    K = K_needed(r)
    print("K", K, "M_eff", K * 2 * 43e-5 / (211 / 500))


def legs(P, T, Th0):
    """Literal data of the split checks `legAOk` / `legBOk` (all enclosures exact)."""
    Li, Lo = Leg(True, P, T), Leg(False, P, T)
    Is1 = Li.flankI
    Iz1 = add(add(Is1, Li.botI), Li.flankI)
    phZ1 = mul(C(1000, 211), add(mul(Th0, C(-2, 1)), Iz1))
    p0, p1, p2 = Li.flankCS(zeroI, False), Li.botCS(Th0, Is1), Li.flankCS(phZ1, True)
    Cin = add(add(p0[0], p1[0]), p2[0])
    Sin = add(add(p0[1], p1[1]), p2[1])
    Tin = add(mul(Li.flankTm, C(2, 1)), Li.botTm)
    okA = Li.ok and theta0Ok(P, T, Th0) and p0[2] and p1[2] and p2[2]
    Is3 = add(Iz1, Lo.flankI)
    Iz2 = add(add(Is3, Lo.botI), Lo.flankI)
    phZ2 = mul(C(1000, 211), Iz2)
    q0, q1, q2 = Lo.flankCS(phZ1, True), Lo.botCS(Th0, Is3), Lo.flankCS(phZ2, False)
    Cout = add(add(q0[0], q1[0]), q2[0])
    Sout = add(add(q0[1], q1[1]), q2[1])
    Tout = add(mul(Lo.flankTm, C(2, 1)), Lo.botTm)
    okB = Lo.ok and q0[2] and q1[2] and q2[2]
    return dict(okA=okA, okB=okB, Cin=Cin, Sin=Sin, J1=Iz1, Tin=Tin, Cout=Cout, Sout=Sout,
                J2=Iz2, Tout=Tout)


def finalOk(d, Kn, Kd, Pmin, Pmax, DlS, DhS):
    Ct, St = add(d["Cin"], d["Cout"]), add(d["Sin"], d["Sout"])
    sD = cosSinC(mul(d["J2"], C(500, 211)))[1]
    Cm, Sm = max(-Ct.lo, Ct.hi), max(-St.lo, St.hi)
    Tt = add(d["Tin"], d["Tout"])
    oks = all(d[k].ok for k in ("Cin", "Sin", "Cout", "Sout", "Tin", "Tout", "J2"))
    return (oks and Kn >= 0 and sD.ok and sD.lo > 0
            and Kd * Kd * (Cm * Cm + Sm * Sm) <= Kn * Kn * sD.lo * sD.lo
            and Pmin * S <= Tt.lo and Tt.hi <= Pmax * S and DlS <= d["J2"].lo
            and d["J2"].hi <= DhS)


def lit(Fv):
    return f"⟨{Fv.lo}, {Fv.hi}, {'true' if Fv.ok else 'false'}⟩"
