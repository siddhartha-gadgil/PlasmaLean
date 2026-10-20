"""Taylor-shift cover with progressive truncation; cost accounting."""
import numpy as np, pickle, sys
from math import comb
from collections import Counter
from poly import *
from tsim import to_chart, shift_axis

def enclose(A, h, rem=0.0):
    hs = [np.array([hh**i for i in range(n)]) for hh, n in zip(h, A.shape)]
    W = np.abs(A)*hs[0][:, None, None]*hs[1][None, :, None]*hs[2][None, None, :]
    return A[0, 0, 0], W.sum() - abs(A[0, 0, 0]) + rem

def truncate(A, h, tol):
    hs = [np.array([hh**i for i in range(n)]) for hh, n in zip(h, A.shape)]
    W = np.abs(A)*hs[0][:, None, None]*hs[1][None, :, None]*hs[2][None, None, :]
    W[0, 0, 0] = np.inf
    flat = W.ravel(); order = np.argsort(flat)
    cs = np.cumsum(flat[order])
    k = np.searchsorted(cs, tol, side='right')
    B = A.copy().ravel(); B[order[:k]] = 0.0
    dropped = cs[k-1] if k > 0 else 0.0
    return B.reshape(A.shape), dropped

def nnz(A): return int(np.count_nonzero(A))

def main(fitfile, delta, Ibf, Iaf, rho, tolQ_frac=0.1, tolI=5e-5, a=0.1, charts=(1,), split_w=(0.1, 0.1, 0.5), faces=True, useI=True):
    L, c = pickle.load(open(fitfile, 'rb'))
    P = reduce_circle(I_poly(L, c, 1.0))
    G, N, Nt = field_polys(0.25, 1.0)
    Q = reduce_circle(lie(P, G))
    dI = max(e[2]+e[3] for e in P); dQ = max(e[2]+e[3] for e in Q)
    print('P', len(P), 'Q', len(Q), 'dI', dI, 'dQ', dQ)
    opt = lambda d: np.polynomial.polynomial.polypow([1.0, 0, 1.0], d)
    tot = Counter()
    for chart in charts:
        It = to_chart(P, chart, dI); Qt = to_chart(Q, chart, dQ)
        Jb = It.copy(); Jb[0, 0, :] -= Ibf*opt(dI)
        Ja = It.copy(); Ja[0, 0, :] -= Iaf*opt(dI)
        Dl = np.zeros((3, 1, 2*dQ+1)); Dl[0, 0, :] = delta*opt(dQ); Dl[1, 0, :] = 4*delta*opt(dQ); Dl[2, 0, :] = 4*delta*opt(dQ)
        stats = Counter(); reasons = Counter(); depth_terms = {}; depth_cost = {}
        tolQ = tolQ_frac*delta
        def face_enc(p, rem, ax, side, h):
            q = shift_axis(p, ax, side*h[ax]); hh = list(h); hh[ax] = 0.0
            stats['cost'] += nnz(p)*p.shape[ax]/2
            return enclose(q, hh, rem)
        def ok(ps, rems, cen, h):
            s0, s1 = cen[0]-h[0], cen[0]+h[0]; z0, z1 = cen[1]-h[1], cen[1]+h[1]
            e_ = 1e-12
            ins = s0 >= -rho-e_ and s1 <= rho+e_ and z0 >= -rho-e_ and z1 <= rho+e_
            outs = s0 >= rho-e_ or s1 <= -rho+e_ or z0 >= rho-e_ or z1 <= -rho+e_
            if rho > 0 and not (ins or outs): reasons['startsplit'] += 1; return False
            if rho > 0 and ins:
                ja = enclose(ps[1], h, rems[1]); stats['cost'] += nnz(ps[1])
                if ja[0] + ja[1] > 0: reasons['start'] += 1; return False
            for ax, lo, hi in (((0, s0, s1), (1, z0, z1)) if faces else ()):
                for side, touch in ((-1, lo <= -a + e_), (1, hi >= a - e_)):
                    if touch:
                        e = face_enc(ps[0], rems[0], ax, side, h)
                        if e[0] - e[1] <= 0: reasons['front'] += 1; return False
            jb = enclose(ps[0], h, rems[0]); stats['cost'] += nnz(ps[0])
            if jb[0] - jb[1] > 0: stats['outside'] += 1; return True
            q = enclose(ps[2], h, rems[2]); dd = enclose(ps[3], h, rems[3]); stats['cost'] += nnz(ps[2]) + nnz(ps[3])
            r = abs(q[0]) + q[1] <= dd[0] - dd[1]
            if not r: reasons['Q'] += 1
            return r
        def cover(ps, rems, cen, h, d):
            stats['nodes'] += 1
            # truncate
            tols = [tolI, tolI, tolQ, 0.0]
            nps = []; nrems = []
            for p, r, t in zip(ps, rems, tols):
                if t > 0 and r < t:
                    q, dr = truncate(p, h, (t - r)/3)   # spend a third of remaining budget
                    nps.append(q); nrems.append(r + dr)
                else:
                    nps.append(p); nrems.append(r)
            ps, rems = nps, nrems
            stats['terms_sum'] += sum(nnz(p) for p in ps)
            depth_terms[d] = depth_terms.get(d, []) + [sum(nnz(p) for p in ps)]
            depth_cost[d] = depth_cost.get(d, 0) + sum(nnz(p) for p in ps)*5
            if ok(ps, rems, cen, h):
                stats['leaves'] += 1; return True
            if d > 40: print('FAIL', cen, h); return False
            wts = [h[i]/split_w[i] for i in range(3)]
            ax = int(np.argmax(wts))
            for sgn in (-1, 1):
                nc = list(cen); nh = list(h); nh[ax] = h[ax]/2; nc[ax] = cen[ax] + sgn*h[ax]/2
                chs = []
                for p in ps:
                    stats['cost'] += nnz(p)*p.shape[ax]/2
                    chs.append(shift_axis(p, ax, sgn*h[ax]/2))
                if not cover(chs, rems, nc, nh, d+1): return False
            return True
        r = cover([Jb if useI else np.full((1,1,1),-1.0), np.zeros((1,1,1)), Qt, Dl], [0.0]*4, [0, 0, 0], [a, a, 1.0], 0)
        print('chart', chart, r, dict(stats), dict(reasons))
        print([(d, len(v), int(np.mean(v))) for d, v in sorted(depth_terms.items())])
        print([(d,int(c)) for d,c in sorted(depth_cost.items())])
        tot += stats
    return tot

if __name__ == "__main__":
    fitfile = sys.argv[1]; delta = float(sys.argv[2]); Ibf = float(sys.argv[3]); Iaf = float(sys.argv[4]); rho = float(sys.argv[5])
    tq = float(sys.argv[6]) if len(sys.argv) > 6 else 0.1
    main(fitfile, delta, Ibf, Iaf, rho, tolQ_frac=tq)
