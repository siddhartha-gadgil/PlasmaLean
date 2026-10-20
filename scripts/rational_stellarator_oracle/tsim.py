"""Simulate a Taylor-shift adaptive cover in (s, z, t) (rational angle chart)."""
import numpy as np, pickle, sys
from math import comb
from poly import *

def to_chart(p, chart, d):
    """p: dict (j,k,a,b) over (s,z,C,S); return dense array A[j,k,m] of p*(1+t^2)^d in chart."""
    js = max(e[0] for e in p) + 1; ks = max(e[1] for e in p) + 1
    A = np.zeros((js, ks, 2*d+1))
    sg = 1 if chart == 1 else -1
    # C = sg (1-t^2)/(1+t^2), S = sg 2t/(1+t^2)
    P1 = np.polynomial.polynomial
    for e, c in p.items():
        a, b = e[2], e[3]
        assert a + b <= d
        poly = np.array([1.0])
        for _ in range(a): poly = P1.polymul(poly, sg*np.array([1.0, 0, -1.0]))
        for _ in range(b): poly = P1.polymul(poly, sg*np.array([0, 2.0]))
        for _ in range(d - a - b): poly = P1.polymul(poly, np.array([1.0, 0, 1.0]))
        A[e[0], e[1], :len(poly)] += c*poly
    return A

def shift_axis(A, axis, c):
    """coefficients of p(x + c) along axis."""
    n = A.shape[axis]
    T = np.zeros((n, n))
    for i in range(n):
        for j in range(i, n):
            T[i, j] = comb(j, i)*c**(j-i)
    return np.moveaxis(np.tensordot(T, np.moveaxis(A, axis, 0), axes=(1, 0)), 0, axis)

def enclose(A, h):
    hs = [np.array([hh**i for i in range(n)]) for hh, n in zip(h, A.shape)]
    W = np.abs(A)*hs[0][:, None, None]*hs[1][None, :, None]*hs[2][None, None, :]
    return A[0, 0, 0], W.sum() - abs(A[0, 0, 0])

def pad(A, shape):
    B = np.zeros(shape); B[:A.shape[0], :A.shape[1], :A.shape[2]] = A; return B

if __name__ == "__main__":
    fitfile = sys.argv[1]; delta = float(sys.argv[2]); Ibf = float(sys.argv[3]); Iaf = float(sys.argv[4]); rho = float(sys.argv[5])
    a = 0.1
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    G, N, Nt = field_polys(0.25, 1.0)
    Q = reduce_circle(lie(P, G))
    dI = max(e[2]+e[3] for e in P); dQ = max(e[2]+e[3] for e in Q)
    print('P', len(P), 'Q', len(Q), 'dI', dI, 'dQ', dQ)
    stats = {'leaves': 0, 'nodes': 0, 'maxdepth': 0}
    from collections import Counter
    reasons = Counter(); depths = Counter()
    for chart in (1, 2):
        It = to_chart(P, chart, dI); Qt = to_chart(Q, chart, dQ)
        # (1+t^2)^d polys
        def opt(d):
            p = np.polynomial.polynomial.polypow([1.0, 0, 1.0], d); return p
        Jb = It.copy(); Jb[0, 0, :] -= Ibf*opt(dI)
        Ja = It.copy(); Ja[0, 0, :] -= Iaf*opt(dI)
        # delta*(1+2s)^2*(1+t^2)^dQ
        Dl = np.zeros((3, 1, 2*dQ+1)); Dl[0, 0, :] = delta*opt(dQ); Dl[1, 0, :] = 4*delta*opt(dQ); Dl[2, 0, :] = 4*delta*opt(dQ)
        sh = (max(Qt.shape[0], 3), Qt.shape[1], Qt.shape[2])
        Rp = pad(Qt, sh) - pad(Dl, sh); Rm = -pad(Qt, sh) - pad(Dl, sh)
        print('terms (nonzero) Jb', np.count_nonzero(np.abs(Jb) > 0), 'R', np.count_nonzero(np.abs(Rp) > 0))
        polys = [Jb, Ja, Rp, Rm]
        def face_enc(p, ax, side, h):
            q = shift_axis(p, ax, side*h[ax]); hh = list(h); hh[ax] = 0.0
            return enclose(q, hh)
        def ok(ps, cen, h):
            s0, s1 = cen[0]-h[0], cen[0]+h[0]; z0, z1 = cen[1]-h[1], cen[1]+h[1]
            eps_ = 1e-12
            inside_start = s0 >= -rho-eps_ and s1 <= rho+eps_ and z0 >= -rho-eps_ and z1 <= rho+eps_
            outside_start = s0 >= rho-eps_ or s1 <= -rho+eps_ or z0 >= rho-eps_ or z1 <= -rho+eps_
            if not (inside_start or outside_start):
                reasons['startsplit'] += 1; return False
            if inside_start:
                ja = enclose(ps[1], h)
                if ja[0] + ja[1] > 0:
                    reasons['start'] += 1; return False
            # faces
            for ax, lo, hi in ((0, s0, s1), (1, z0, z1)):
                if lo <= -a + eps_:
                    e = face_enc(ps[0], ax, -1, h)
                    if e[0] - e[1] <= 0: reasons['front'] += 1; return False
                if hi >= a - eps_:
                    e = face_enc(ps[0], ax, 1, h)
                    if e[0] - e[1] <= 0: reasons['front'] += 1; return False
            jb = enclose(ps[0], h)
            if jb[0] - jb[1] > 0: return True
            rp = enclose(ps[2], h); rm = enclose(ps[3], h)
            r = rp[0] + rp[1] < 0 and rm[0] + rm[1] < 0
            if not r: reasons['Q'] += 1
            return r
        def cover(ps, cen, h, d):
            stats['nodes'] += 1
            stats['maxdepth'] = max(stats['maxdepth'], d)
            if ok(ps, cen, h):
                stats['leaves'] += 1; depths[d] += 1; return True
            if d > 40: print('FAIL', cen, h); return False
            # split widest relative dimension: weights
            wts = [h[0]/0.1, h[1]/0.1, h[2]/0.5]
            ax = int(np.argmax(wts))
            res = True
            for sgn in (-1, 1):
                nc = list(cen); nh = list(h); nh[ax] = h[ax]/2; nc[ax] = cen[ax] + sgn*h[ax]/2
                nps = [shift_axis(p, ax, sgn*h[ax]/2) for p in ps]
                res = res and cover(nps, nc, nh, d+1)
                if not res: return False
            return res
        r = cover(polys, [0, 0, 0], [a, a, 1.0], 0)
        print('chart', chart, r, stats, reasons, sorted(depths.items()))
        break
