"""Coefficient-weighted fit: minimize the weighted coefficient norm of the defect polynomial."""
import numpy as np, pickle, sys
from poly import *
from fit import basis_list, eval_basis, defect_matrix

def basis_polys(L):
    trigs = {}
    out = []
    for (j, k, n, t) in L:
        if n not in trigs: trigs[n] = trig(n, 1.0)
        T = trigs[n][0 if t == 'c' else 1]
        p = {}
        for e, v in T.items():
            p[(j, k, e[2], e[3])] = v
        out.append(reduce_circle(p))
    return out

def build(K, M, mode):
    L = basis_list(K, M)
    G, N, Nt = field_polys(0.25, 1.0)
    Bp = basis_polys(L)
    Qs = [reduce_circle(lie(b, G)) for b in Bp]
    keys = sorted(set(e for q in Qs for e in q))
    idx = {e: i for i, e in enumerate(keys)}
    A = np.zeros((len(keys), len(L)))
    for j, q in enumerate(Qs):
        for e, v in q.items(): A[idx[e], j] = v
    return L, Bp, keys, A

if __name__ == "__main__":
    K, M, a, mode = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    lam = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
    L, Bp, keys, A = build(K, M, mode)
    # weights: a^(deg in s,z) * angular weight
    w = np.array([a**(e[0]+e[1]) * (2.0 if mode == 'cheb' else 1.0) for e in keys])
    Aw = A*w[:, None]
    # sampled I normalization + sampled defect (to also keep sup small)
    rng = np.random.default_rng(0)
    npts = 20000
    s = a*(2*rng.random(npts)-1); z = a*(2*rng.random(npts)-1); th = 2*np.pi*rng.random(npts)
    r = np.sqrt(s*s+z*z)
    V, Ad = defect_matrix(L, s, z, th)
    wr = 1/np.maximum(r, 1e-3)**2
    Vw = V*wr[:, None]
    Adw = Ad*wr[:, None]/np.sqrt(npts)
    Q_, Rm = np.linalg.qr(Vw/np.sqrt(npts))
    # objective: lam*||Adw c||^2 + ||Aw c||^2 / (scale)
    obj = np.vstack([Aw/(a**2), np.sqrt(lam)*Adw]) if lam > 0 else Aw/(a**2)
    B = np.linalg.solve(Rm.T, obj.T).T
    U, S, VT = np.linalg.svd(B, full_matrices=False)
    c = np.linalg.solve(Rm, VT[-1])
    i0 = L.index((0, 2, 0, 'c'))
    c = c/c[i0]
    pickle.dump((L, c), open(f'/tmp/rsc/cfit_{K}_{M}_{a}_{lam}.pkl', 'wb'))
    q = A@c
    print('coef abs-sum (weighted)', np.sum(np.abs(q)*w/(2.0 if mode=='cheb' else 1.0)))
    # evaluate sup on grid region I<=Ib
    ns = 61; nt = 64
    sg = np.linspace(-a, a, ns); tg = np.linspace(0, 2*np.pi, nt, endpoint=False)
    S_, Z_, T_ = np.meshgrid(sg, sg, tg, indexing='ij')
    V, Ad = defect_matrix(L, S_.ravel(), Z_.ravel(), T_.ravel())
    I = (V@c).reshape(S_.shape); Qv = (Ad@c).reshape(S_.shape)
    bd = np.zeros(S_.shape, bool); bd[0] = bd[-1] = True; bd[:, 0] = bd[:, -1] = True
    Ib = I[bd].min(); m = I <= Ib
    mx = np.abs(Qv[m]).max()
    # abs-sum on region
    x = [S_.ravel(), Z_.ravel(), np.cos(T_.ravel()), np.sin(T_.ravel())]
    absQ = np.zeros(len(x[0]))
    for e, v in zip(keys, q):
        absQ += abs(v)*np.abs(x[0]**e[0]*x[1]**e[1]*x[2]**e[2]*x[3]**e[3])
    absQ = absQ.reshape(S_.shape)
    print(f'K={K} lam={lam} Ib={Ib:.4e} max|Q|={mx:.3e} absmax={absQ[m].max():.3e} F={absQ[m].max()/mx:.1f} Imin={I.min():.2e}')
