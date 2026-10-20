"""Simulate the stage1(angle) + evalB(s,z) adaptive cover with float ball arithmetic."""
import numpy as np, pickle, sys
from collections import defaultdict
from poly import *

def bmul(a, b): return (a[0]*b[0], abs(a[0])*b[1] + abs(b[0])*a[1] + a[1]*b[1])
def bpow(a, n):
    r = (1.0, 0.0)
    for _ in range(n): r = bmul(r, a)
    return r
def stage_angle(p, Cb, Sb):
    """p: dict over (j,k,a,b) -> BPoly dict (j,k) -> ball"""
    out = defaultdict(lambda: [0.0, 0.0])
    cp = [bpow(Cb, n) for n in range(12)]; sp = [bpow(Sb, n) for n in range(12)]
    for e, c in p.items():
        m = bmul((c, 0.0), bmul(cp[e[2]], sp[e[3]]))
        o = out[(e[0], e[1])]; o[0] += m[0]; o[1] += m[1]
    return dict(out)
def evalB2(bp, sb, zb):
    spw = [bpow(sb, n) for n in range(20)]; zpw = [bpow(zb, n) for n in range(20)]
    c = 0.0; r = 0.0
    for (j, k), b in bp.items():
        m = bmul(tuple(b), bmul(spw[j], zpw[k]))
        c += m[0]; r += m[1]
    return c, r

def run(K, M, fitfile, deltaQ, Ib, Ia, rho, a=0.1, maxdepth=30):
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    G, N, Nt = field_polys(0.25, 1.0)
    Q = reduce_circle(lie(P, G))
    print('P', len(P), 'Q', len(Q))
    stats = defaultdict(int)
    # angle boxes: bisect (C,S) square, prune boxes missing circle
    def meets_circle(c0, c1, s0, s1):
        lo = (0 if c0 <= 0 <= c1 else min(c0*c0, c1*c1)) + (0 if s0 <= 0 <= s1 else min(s0*s0, s1*s1))
        hi = max(c0*c0, c1*c1) + max(s0*s0, s1*s1)
        return lo <= 1 <= hi
    def sz_ok(Pb, Qb, s0, s1, z0, z1):
        sb = ((s0+s1)/2, (s1-s0)/2); zb = ((z0+z1)/2, (z1-z0)/2)
        Ic, Ir = evalB2(Pb, sb, zb)
        # start check
        cl = (0 if s0 <= 0 <= s1 else min(s0*s0, s1*s1)) + (0 if z0 <= 0 <= z1 else min(z0*z0, z1*z1))
        startok = cl > rho*rho or Ic + Ir <= Ia
        if Ic - Ir > Ib: return startok
        interior = s0 > -a and s1 < a and z0 > -a and z1 < a
        if not interior: return False
        Qc, Qr = evalB2(Qb, sb, zb)
        r2lo = 1 + 2*s0
        return startok and abs(Qc) + Qr <= deltaQ*r2lo*r2lo
    def sz_cover(Pb, Qb, s0, s1, z0, z1, d):
        if sz_ok(Pb, Qb, s0, s1, z0, z1):
            stats['leaves'] += 1; return True
        if d > maxdepth:
            sb=((s0+s1)/2,(s1-s0)/2); zb=((z0+z1)/2,(z1-z0)/2)
            print('FAIL',s0,s1,z0,z1,evalB2(Pb,sb,zb),evalB2(Qb,sb,zb)); return False
        if s1 - s0 >= z1 - z0:
            m = (s0+s1)/2
            return sz_cover(Pb, Qb, s0, m, z0, z1, d+1) and sz_cover(Pb, Qb, m, s1, z0, z1, d+1)
        m = (z0+z1)/2
        return sz_cover(Pb, Qb, s0, s1, z0, m, d+1) and sz_cover(Pb, Qb, s0, s1, m, z1, d+1)
    def ang_cover(c0, c1, s0, s1, w):
        if not meets_circle(c0, c1, s0, s1):
            stats['angle_pruned'] += 1; return True
        if c1 - c0 <= w and s1 - s0 <= w:
            Cb = ((c0+c1)/2, (c1-c0)/2); Sb = ((s0+s1)/2, (s1-s0)/2)
            Pb = stage_angle(P, Cb, Sb); Qb = stage_angle(Q, Cb, Sb)
            n0 = stats['leaves']
            ok = sz_cover(Pb, Qb, -a, a, -a, a, 0)
            stats['angle_cells'] += 1
            return ok
        if c1 - c0 >= s1 - s0:
            m = (c0+c1)/2
            return ang_cover(c0, m, s0, s1, w) and ang_cover(m, c1, s0, s1, w)
        m = (s0+s1)/2
        return ang_cover(c0, c1, s0, m, w) and ang_cover(c0, c1, m, s1, w)
    return ang_cover, stats

if __name__ == "__main__":
    K, M = int(sys.argv[1]), int(sys.argv[2])
    fitfile = sys.argv[3]
    deltaQ = float(sys.argv[4]); Ib = float(sys.argv[5]); Ia = float(sys.argv[6]); rho = float(sys.argv[7])
    w = float(sys.argv[8])
    ang_cover, stats = run(K, M, fitfile, deltaQ, Ib, Ia, rho)
    import time; t = time.time()
    ok = ang_cover(-1.0, 1.0, -1.0, 1.0, w)
    print('ok', ok, dict(stats), time.time()-t)
