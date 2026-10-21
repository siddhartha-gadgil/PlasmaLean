"""UNTRUSTED design refinement: near-minimax fit of a symmetric polygonal coil set.

Starts from a pickle of `polygon_design.py` (or from the pure helix) and refits vertices and
currents by Levenberg-Marquardt with iteratively reweighted residuals (Lawson-type weights that
push the fit towards the minimax error) on a denser sample of the frontier of Omega_a for the
given `a` (default the certified box a = 3420/32761).  A soft penalty keeps every vertex at
distance >= dmin from the box.  Nothing here is trusted.

usage: polygon_design_minimax.py K Ns aw iters out.pkl [start.pkl] [dmin]
"""
import numpy as np, sys, pickle, time
from polygon_design import Sym, coil_field, helix, jac, frontier_fd
from common import hel

A_BOX = 3420 / 32761

def box_dist(Z):
    """distance (in the (s, z) metric approx) of vertices from the box |s|,|z| <= a."""
    R = np.sqrt(Z[..., 0] ** 2 + Z[..., 1] ** 2)
    dr = np.maximum(np.maximum(R - np.sqrt(1 + 2 * A_BOX), np.sqrt(1 - 2 * A_BOX) - R), 0)
    dz = np.maximum(np.abs(Z[..., 2]) - A_BOX, 0)
    return np.sqrt(dr ** 2 + dz ** 2)

if __name__ == "__main__":
    K, Ns, aw, iters, out = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    start = sys.argv[6] if len(sys.argv) > 6 and sys.argv[6] != '-' else None
    dmin = float(sys.argv[7]) if len(sys.argv) > 7 else 0.2
    sym = Sym(K, Ns)
    x = frontier_fd(A_BOX, 49, 15); tgt = hel(x)
    if start:
        d = pickle.load(open(start, 'rb')); Z, Ir = d['Z'], d['Ir']
    else:
        Z = helix(K, Ns, aw, sym.reps)
        Ir = np.array([np.sin(2 * 2 * np.pi * (k + 0.5) / K) for k in sym.reps])
        V, I = sym.full(Z, Ir); f = coil_field(V, I, x); Ir *= np.sum(f * tgt) / np.sum(f * f)
    Z0 = Z.copy(); reg = 1e-5; lam = 1e-3
    wts = np.ones(len(x))
    def resid(Z, Ir, wts):
        V, I = sym.full(Z, Ir)
        e = (coil_field(V, I, x) - tgt) * np.sqrt(wts)[:, None]
        pen = 1e-2 * np.maximum(dmin - box_dist(Z), 0).ravel()
        return np.concatenate([e.ravel(), reg * (Z - Z0).ravel(), pen])
    t0 = time.time()
    for it in range(iters):
        V, I = sym.full(Z, Ir)
        err = np.linalg.norm(coil_field(V, I, x) - tgt, axis=1)
        if it > 0:
            wts = wts * (err / err.max()) ** 0.5; wts = wts / wts.mean() + 0.05
        r = resid(Z, Ir, wts)
        J = jac(sym, Z, Ir, x) * np.repeat(np.sqrt(wts), 3)[:, None]
        nz = Z.size
        Jr = np.zeros((nz, J.shape[1])); Jr[:, :nz] = reg * np.eye(nz)
        # penalty rows: finite-difference free approximation (ignored in Jacobian, acts via line search)
        JJ = np.vstack([J, Jr])
        rr = r[:JJ.shape[0]]
        g = JJ.T @ rr; H = JJ.T @ JJ
        for _ in range(30):
            dp = -np.linalg.solve(H + lam * np.diag(np.diag(H) + 1e-12), g)
            Zn = Z + dp[:nz].reshape(Z.shape); In = Ir + dp[nz:]
            rn = resid(Zn, In, wts)
            if rn @ rn < r @ r:
                Z, Ir = Zn, In; lam = max(lam / 3, 1e-9); break
            lam *= 4
        V, I = sym.full(Z, Ir)
        err = np.linalg.norm(coil_field(V, I, x) - tgt, axis=1)
        print(it, 'max', err.max(), 'rms', np.sqrt((err ** 2).mean()), 'dmin', box_dist(Z).min(), 'lam', lam, 't', round(time.time() - t0), flush=True)
    V, I = sym.full(Z, Ir)
    xt = frontier_fd(A_BOX, 257, 65); e = np.linalg.norm(coil_field(V, I, xt) - hel(xt), axis=1)
    print('TEST max', e.max(), 'rms', np.sqrt((e ** 2).mean()), 'dmin', box_dist(Z).min(), 'currents', Ir)
    pickle.dump(dict(K=K, Ns=Ns, aw=aw, a=A_BOX, Z=Z, Ir=Ir, V=V, I=I), open(out, 'wb'))
