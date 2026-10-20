"""Taylor-shift cover, T = {J <= c} (rotating-ellipse tube); cost accounting."""
import numpy as np, pickle, sys
from math import comb
from collections import Counter
from poly import *
from tsim import to_chart, shift_axis
from tsim2 import enclose, truncate, nnz

def Jpoly():
    # J = s^2 + z^2 + (1/2)(z^2 - s^2) S + s z C
    return {(2,0,0,0):1.0,(0,2,0,0):1.0,(0,2,0,1):0.5,(2,0,0,1):-0.5,(1,1,1,0):1.0}

def main(fitfile, delta, cJ, Ibf, tolQ_frac=0.3, tolI=5e-5, charts=(1,), split_w=(0.1,0.1,0.25), verbose=True):
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    G, N, Nt = field_polys(0.25, 1.0)
    Q = reduce_circle(lie(P, G))
    dI = max(e[2]+e[3] for e in P); dQ = max(e[2]+e[3] for e in Q)
    a = np.sqrt(2*cJ)*1.0001
    opt = lambda d: np.polynomial.polynomial.polypow([1.0, 0, 1.0], d)
    tot = Counter()
    for chart in charts:
        It = to_chart(P, chart, dI); Qt = to_chart(Q, chart, dQ)
        Jt = to_chart(Jpoly(), chart, 1); Jt[0,0,:] -= cJ*opt(1)
        Jb = It.copy(); Jb[0, 0, :] -= Ibf*opt(dI)
        Dl = np.zeros((3, 1, 2*dQ+1)); Dl[0, 0, :] = delta*opt(dQ); Dl[1, 0, :] = 4*delta*opt(dQ); Dl[2, 0, :] = 4*delta*opt(dQ)
        stats = Counter(); reasons = Counter(); depth_cost = Counter()
        tolQ = tolQ_frac*delta
        def ok(ps, rems, h):
            j = enclose(ps[0], h); stats['cost'] += nnz(ps[0])
            if j[0] - j[1] > 0: stats['outT'] += 1; return True
            ib = enclose(ps[1], h, rems[1]); stats['cost'] += nnz(ps[1])
            if ib[0] - ib[1] > 0: stats['outI'] += 1; return True
            if j[0] + j[1] >= 0: reasons['front'] += 1; return False
            q = enclose(ps[2], h, rems[2]); dd = enclose(ps[3], h, rems[3]); stats['cost'] += nnz(ps[2]) + nnz(ps[3])
            r = abs(q[0]) + q[1] <= dd[0] - dd[1]
            if not r: reasons['Q'] += 1
            return r
        def cover(ps, rems, cen, h, d):
            stats['nodes'] += 1
            tols = [0.0, tolI, tolQ, 0.0]
            nps = []; nrems = []
            for p, r, t in zip(ps, rems, tols):
                if t > 0 and r < t:
                    q, dr = truncate(p, h, (t - r)/3)
                    nps.append(q); nrems.append(r + dr)
                else:
                    nps.append(p); nrems.append(r)
            ps, rems = nps, nrems
            if ok(ps, rems, h):
                stats['leaves'] += 1; return True
            if d > 40: print('FAIL', cen, h); return False
            wts = [h[i]/split_w[i] for i in range(3)]
            ax = int(np.argmax(wts))
            for sgn in (-1, 1):
                nc = list(cen); nh = list(h); nh[ax] = h[ax]/2; nc[ax] = cen[ax] + sgn*h[ax]/2
                chs = []
                for p in ps:
                    cst = nnz(p)*(p.shape[ax]-1)/2
                    stats['cost'] += cst; depth_cost[d] += cst
                    chs.append(shift_axis(p, ax, sgn*h[ax]/2))
                if not cover(chs, rems, nc, nh, d+1): return False
            return True
        r = cover([Jt, Jb, Qt, Dl], [0.0]*4, [0, 0, 0], [a, a, 1.0], 0)
        if verbose:
            print('chart', chart, r, dict(stats), dict(reasons))
            print(sorted(depth_cost.items()))
        tot += stats
    return tot

if __name__ == "__main__":
    fitfile = sys.argv[1]; delta = float(sys.argv[2]); cJ = float(sys.argv[3]); Ibf = float(sys.argv[4])
    sw = float(sys.argv[5]) if len(sys.argv) > 5 else 0.25
    main(fitfile, delta, cJ, Ibf, split_w=(0.1, 0.1, sw))
