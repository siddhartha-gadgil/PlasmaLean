import numpy as np, sys, pickle
eps = 0.25
# variables s=(R^2-1)/2, z, th=2 phi.  N = (s^2-z^2) cos th - z(s^2-2s-z^2) sin th
def Nfun(s, z, th):
    a = s*s - z*z; b = -z*(s*s - 2*s - z*z)
    c, d = np.cos(th), np.sin(th)
    N = a*c + b*d
    Ns = 2*s*c + (-z*(2*s - 2))*d
    Nz = -2*z*c + (-(s*s - 2*s - z*z) + 2*z*z)*d
    Nt = -a*d + b*c
    return N, Ns, Nz, Nt
def rates(s, z, th):
    N, Ns, Nz, Nt = Nfun(s, z, th)
    r2 = 1 + 2*s
    Gs = eps*r2*(r2*Ns - 2*N)
    Gz = eps*r2*Nz
    Gt = 2*(r2 + 2*eps*Nt)
    return Gs, Gz, Gt
SYM = [False]
def basis_list(K, M):
    L = []
    for n in range(0, M+1):
        for d in range(2 if n == 0 else 0, K+1):
            for k in range(d+1):
                if not SYM[0] or (k + n) % 2 == 0: L.append((d-k, k, n, 'c'))
                if n > 0 and (not SYM[0] or (k + n) % 2 == 1): L.append((d-k, k, n, 's'))
    return L
def eval_basis(L, s, z, th):
    V = []; Vs = []; Vz = []; Vt = []
    for (j, k, n, t) in L:
        sj = s**j; dsj = j*s**(j-1) if j > 0 else 0*s
        zk = z**k; dzk = k*z**(k-1) if k > 0 else 0*z
        if t == 'c': T = np.cos(n*th); dT = -n*np.sin(n*th)
        else: T = np.sin(n*th); dT = n*np.cos(n*th)
        V.append(sj*zk*T); Vs.append(dsj*zk*T); Vz.append(sj*dzk*T); Vt.append(sj*zk*dT)
    return [np.array(a).T for a in (V, Vs, Vz, Vt)]
def defect_matrix(L, s, z, th):
    V, Vs, Vz, Vt = eval_basis(L, s, z, th)
    Gs, Gz, Gt = rates(s, z, th)
    return V, Gs[:, None]*Vs + Gz[:, None]*Vz + Gt[:, None]*Vt
def fit(K, M, a, npts=None, seed=0, shape='square'):
    L = basis_list(K, M)
    npts = npts or max(20000, 40*len(L))
    rng = np.random.default_rng(seed)
    if shape == 'square':
        s = a*(2*rng.random(npts)-1); z = a*(2*rng.random(npts)-1)
    else:
        r = a*np.sqrt(rng.random(npts)); ang = 2*np.pi*rng.random(npts)
        s = r*np.cos(ang); z = r*np.sin(ang)
    th = 2*np.pi*rng.random(npts)
    r = np.sqrt(s*s+z*z)
    V, A = defect_matrix(L, s, z, th)
    w = 1/np.maximum(r, 1e-3)**2
    A = A*w[:, None]; Vw = V*w[:, None]
    Q, Rm = np.linalg.qr(Vw)
    B = np.linalg.solve(Rm.T, A.T).T
    U, S, VT = np.linalg.svd(B, full_matrices=False)
    c = np.linalg.solve(Rm, VT[-1])
    i0 = L.index((0, 2, 0, 'c'))
    return L, c/c[i0]
if __name__ == "__main__":
    K, M, a = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    if len(sys.argv) > 4 and sys.argv[4] == 'sym': SYM[0] = True
    L, c = fit(K, M, a)
    pickle.dump((L, c), open(f'/tmp/rsc/fit_{K}_{M}_{a}' + ('_sym' if SYM[0] else '') + '.pkl', 'wb'))
    # evaluate on grid
    ns = 81; nt = 64
    sg = np.linspace(-a, a, ns); th = np.linspace(0, 2*np.pi, nt, endpoint=False)
    S_, Z_, T_ = np.meshgrid(sg, sg, th, indexing='ij')
    s = S_.ravel(); z = Z_.ravel(); t = T_.ravel()
    V, A = defect_matrix(L, s, z, t)
    I = (V@c).reshape(S_.shape); Q = (A@c).reshape(S_.shape)
    bd = np.zeros(S_.shape, bool); bd[0] = bd[-1] = True; bd[:, 0] = bd[:, -1] = True
    Ib = I[bd].min()
    m = I <= Ib
    print('nb', len(L), 'Ib', Ib, 'max|Q| on I<=Ib', np.abs(Q[m]).max(), 'Imin', I.min())
    # dI/dphi
    _, _, _, Nt = Nfun(s, z, t)
    dIdphi = (A@c)/((1+2*s)+2*eps*Nt)
    print('max dI/dphi', np.abs(dIdphi.reshape(S_.shape)[m]).max())
    d = np.abs(Q[m]).max()
    # transits: dI/ds = Q/r2^2 ; s-parameter; phi advance per s = B.grad phi = (r2+2eps Nt)/r2^2
    for frac in (0.25, 0.5):
        print(frac, 'transits(phi-based) ~', (1-frac)*Ib/(2*np.pi*np.abs(dIdphi.reshape(S_.shape)[m]).max()))
