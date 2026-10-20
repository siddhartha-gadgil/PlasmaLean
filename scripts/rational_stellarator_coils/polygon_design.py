"""UNTRUSTED design search: closed polygonal helical filaments for the rational stellarator.

K filaments (K divisible by 8), Ns vertices each (Ns divisible by 4).  The filament set is
invariant under rotPi (x,y,z) -> (-x,-y,z) and, with reversed currents, under the stellarator
symmetry sigma (x,y,z) -> (y,x,-z).  Only the 4 representative filaments are free.  The initial
guess is the pure helix theta = phi + u_k on the torus of minor radius aw.  Vertex positions and
currents are fitted by Levenberg-Marquardt (finite-difference Jacobian per vertex) to hel on the
frontier of Omega_a (restricted to the fundamental domain y >= |x|).
Nothing here is trusted; the Lean certificate re-checks everything it uses.
"""
import numpy as np, sys, pickle, time
from common import hel

def seg_field(A, B, x):
    """field (mu0 = 1, unit current) of segments A->B at points x; returns (P, S, 3)."""
    a = A[None] - x[:, None]; b = B[None] - x[:, None]
    na = np.linalg.norm(a, axis=-1); nb = np.linalg.norm(b, axis=-1)
    cr = np.cross(a, b)
    f = (na + nb) / (na * nb * (na * nb + np.sum(a * b, -1)))
    return cr * f[..., None] / (4 * np.pi)

def frontier_fd(a, nphi, nside):
    """frontier points of {|s|<=a,|z|<=a} with phi in [pi/4, 3pi/4] (fundamental domain)."""
    ph = np.linspace(np.pi / 4, 3 * np.pi / 4, nphi)
    u = np.linspace(-a, a, nside)
    pts = []
    for sv in (-a, a):
        R = np.sqrt(1 + 2 * sv); P, U = np.meshgrid(ph, u, indexing='ij')
        pts.append(np.stack([R * np.cos(P), R * np.sin(P), U], -1).reshape(-1, 3))
    for zv in (-a, a):
        P, U = np.meshgrid(ph, u, indexing='ij'); R = np.sqrt(1 + 2 * U)
        pts.append(np.stack([R * np.cos(P), R * np.sin(P), zv + 0 * U], -1).reshape(-1, 3))
    return np.concatenate(pts)

class Sym:
    def __init__(s, K, Ns):
        s.K, s.Ns = K, Ns
        reps, seen = [], set()
        for k in range(K):
            if k in seen: continue
            orb = s.orbit(k); reps.append(k); seen |= set(o[0] for o in orb)
        s.reps = reps
    def orbit(s, k):
        """list of (k', jmap, M) : V[k', jmap(j)] = M V[k, j]."""
        K, Ns = s.K, s.Ns
        R = np.diag([-1., -1., 1.]); S = np.array([[0, 1., 0], [1., 0, 0], [0, 0, -1.]])
        m = (-k - 1 - K // 4) % K
        return [(k, lambda j: j, np.eye(3)), ((k - K // 2) % K, lambda j: (j + Ns // 2) % Ns, R),
                (m, lambda j: (Ns // 4 - j) % Ns, S), ((m - K // 2) % K, lambda j: (Ns // 4 - j + Ns // 2) % Ns, R @ S)]
    def full(s, Z, Ir):
        V = np.zeros((s.K, s.Ns, 3)); I = np.zeros(s.K)
        for r, k in enumerate(s.reps):
            for (k2, jm, M) in s.orbit(k):
                for j in range(s.Ns): V[k2, jm(j)] = M @ Z[r, j]
                I[k2] = Ir[r]
        return V, I

def coil_field(V, I, x):
    A = V.reshape(-1, 3); B = np.roll(V, -1, axis=1).reshape(-1, 3); Is = np.repeat(I, V.shape[1])
    out = np.zeros_like(x)
    for i0 in range(0, len(x), 256):
        out[i0:i0 + 256] = np.einsum('psk,s->pk', seg_field(A, B, x[i0:i0 + 256]), Is)
    return out

def helix(K, Ns, aw, reps):
    phi = 2 * np.pi * np.arange(Ns) / Ns
    Z = []
    for k in reps:
        u = 2 * np.pi * (k + 0.5) / K; th = phi + u; R = 1 + aw * np.cos(th)
        Z.append(np.stack([R * np.cos(phi), R * np.sin(phi), aw * np.sin(th)], -1))
    return np.array(Z)

def jac(sym, Z, Ir, x, eps=1e-6):
    V, I = sym.full(Z, Ir)
    cols = []
    for r, k in enumerate(sym.reps):
        for j in range(sym.Ns):
            for c in range(3):
                d = np.zeros(3); d[c] = eps
                tot = np.zeros((len(x), 3))
                for (k2, jm, M) in sym.orbit(k):
                    jj = jm(j); dd = M @ d
                    Vp = V[k2]; jm1 = (jj - 1) % sym.Ns; jp1 = (jj + 1) % sym.Ns
                    A = np.array([Vp[jm1], Vp[jj]]); B = np.array([Vp[jj], Vp[jp1]])
                    A2 = A.copy(); B2 = B.copy(); A2[1] += dd; B2[0] += dd
                    f0 = seg_field(A, B, x).sum(1); f1 = seg_field(A2, B2, x).sum(1)
                    tot += I[k2] * (f1 - f0) / eps
                cols.append(tot.ravel())
    for r, k in enumerate(sym.reps):
        Ie = np.zeros_like(Ir); Ie[r] = 1.0
        V1, I1 = sym.full(Z, Ie)
        cols.append(coil_field(V1, I1, x).ravel())
    return np.stack(cols, 1)

if __name__ == "__main__":
    K, Ns, aw, a, iters = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    sym = Sym(K, Ns)
    x = frontier_fd(a, 33, 9); tgt = hel(x)
    Z = helix(K, Ns, aw, sym.reps)
    Ir = np.array([np.sin(2 * 2 * np.pi * (k + 0.5) / K) for k in sym.reps])
    V, I = sym.full(Z, Ir); f = coil_field(V, I, x); Ir *= np.sum(f * tgt) / np.sum(f * f)
    Z0 = Z.copy(); lam = 1e-3; reg = float(sys.argv[6]) if len(sys.argv) > 6 else 1e-4
    def resid(Z, Ir):
        V, I = sym.full(Z, Ir)
        return np.concatenate([(coil_field(V, I, x) - tgt).ravel(), reg * (Z - Z0).ravel()])
    r = resid(Z, Ir); t0 = time.time()
    for it in range(iters):
        J = jac(sym, Z, Ir, x)
        nz = Z.size
        Jr = np.zeros((nz, J.shape[1])); Jr[:, :nz] = reg * np.eye(nz)
        JJ = np.vstack([J, Jr])
        g = JJ.T @ r; H = JJ.T @ JJ
        while True:
            dp = -np.linalg.solve(H + lam * np.diag(np.diag(H) + 1e-12), g)
            Zn = Z + dp[:nz].reshape(Z.shape); In = Ir + dp[nz:]
            rn = resid(Zn, In)
            if rn @ rn < r @ r:
                Z, Ir, r = Zn, In, rn; lam = max(lam / 3, 1e-9); break
            lam *= 4
            if lam > 1e8: break
        e = np.linalg.norm(r[:3 * len(x)].reshape(-1, 3), axis=1)
        print(it, 'max', e.max(), 'rms', np.sqrt((e ** 2).mean()), 'lam', lam, 'disp', np.abs(Z - Z0).max(), 't', round(time.time() - t0), flush=True)
    V, I = sym.full(Z, Ir)
    xt = frontier_fd(a, 129, 33); e = np.linalg.norm(coil_field(V, I, xt) - hel(xt), axis=1)
    print('TEST max', e.max(), 'rms', np.sqrt((e ** 2).mean()), 'currents', Ir)
    pickle.dump(dict(K=K, Ns=Ns, aw=aw, a=a, Z=Z, Ir=Ir, V=V, I=I), open(f'/tmp/pd/sym_{K}_{Ns}_{aw}.pkl', 'wb'))
