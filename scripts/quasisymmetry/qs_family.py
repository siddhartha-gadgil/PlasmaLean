# Quasisymmetry test for Landreman families 1 and 2 (untrusted numerics).
# QS for an MHS field with flux function psi (J.grad psi = 0) <=> on each surface
#   g2 := (B x grad psi).grad|B|  =  F(psi) * g1,   g1 := B.grad|B|,   F constant on the surface.
# We sample a long field line on one surface, fit F by least squares, report the relative residual.
import sys, numpy as np, sympy as sp
from scipy.integrate import solve_ivp
x, y, z = sp.symbols('x y z', real=True)

def family2(eps, S, lam):
    r2 = x**2 + y**2
    Zr = r2**2 + eps*(x**2 - y**2); Zi = 2*eps*x*y
    Mo = sp.sqrt(Zr**2 + Zi**2)
    sg = sp.sqrt((Mo + Zr)/2); nu = eps*x*y/sg
    cz, sz = sp.cos(lam*z), sp.sin(lam*z)
    uR = cz*sp.cos(sg-S)*sp.cosh(nu) - sz*sp.sin(sg-S)*sp.sinh(nu)
    uI = -(sz*sp.cos(sg-S)*sp.cosh(nu) + cz*sp.sin(sg-S)*sp.sinh(nu))
    vR = cz*sp.sin(sg-S)*sp.cosh(nu) + sz*sp.cos(sg-S)*sp.sinh(nu)
    al = sg*x + nu*y; be = sg*y - nu*x; Mq = sg**2 + nu**2
    B = sp.Matrix([-(uR*be + uI*al)/(2*Mq), (uR*al - uI*be)/(2*Mq), -vR/lam])
    psi = (sz**2 + vR**2)/2
    return B, psi

def family1(eps):
    a, b = sp.sqrt(1+eps), sp.sqrt(1-eps)
    s = x**2/a**2 + y**2/b**2
    F = sp.sqrt(1 - (1-s)**2 - 4*z**2)
    B = sp.Matrix([(2*z*x - (a/b)*F*y)/s, (2*z*y + (b/a)*F*x)/s, 1 - s])
    psi = (x**2 + y**2 + 4*z**2 + (B.T*B)[0] - 2 + eps**2)/4
    return B, psi

def build(B, psi):
    X = sp.Matrix([x, y, z])
    Bm = sp.sqrt((B.T*B)[0])
    gB = sp.Matrix([sp.diff(Bm, v) for v in X])
    gp = sp.Matrix([sp.diff(psi, v) for v in X])
    g1 = (B.T*gB)[0]
    g2 = (B.cross(gp).T*gB)[0]
    f = sp.lambdify((x, y, z), [B[0], B[1], B[2], Bm, psi, g1, g2], 'numpy')
    return f

def test(f, p0, T, label, n=20000):
    rhs = lambda t, p: f(*p)[:3]
    sol = solve_ivp(rhs, (0, T), p0, rtol=1e-11, atol=1e-13, dense_output=True)
    ts = np.linspace(0, T, n); P = sol.sol(ts)
    vals = np.array([f(*P[:, i]) for i in range(n)], dtype=float)
    Bm, psi, g1, g2 = vals[:, 3], vals[:, 4], vals[:, 5], vals[:, 6]
    Fbest = np.dot(g1, g2)/np.dot(g1, g1)
    res = np.linalg.norm(g2 - Fbest*g1)/np.linalg.norm(g2)
    print(f"{label}: psi drift {psi.max()-psi.min():.2e} (psi={psi[0]:.5f}); |B| in [{Bm.min():.4f},{Bm.max():.4f}];"
          f" F_fit={Fbest:.4g}; rel. residual |g2-F g1|/|g2| = {res:.3f}")
    return res

if __name__ == '__main__':
    eps = 0.25; S = 4.0
    for lam in [15.0, 200.0]:
        f = build(*family2(eps, S, lam))
        for k in [0.1, 0.4, 0.7]:
            d = np.arcsin(k)
            xs = np.sqrt((-eps + np.sqrt(eps**2 + 4*(S+d)**2))/2)   # x*sqrt(x^2+eps) = S+d
            test(f, [xs, 0.0, 0.0], 60.0, f"family2 eps=1/4 S=4 lam={lam} k={k}")
    # paper example (3.27): eps=2, S=1
    f = build(*family2(2.0, 1.0, 1.0))
    for k in [0.1, 0.3]:
        d = np.arcsin(k); e = 2.0; S1 = 1.0
        xs = np.sqrt((-e + np.sqrt(e**2 + 4*(S1+d)**2))/2)
        test(f, [xs, 0.0, 0.0], 60.0, f"family2 paper example eps=2 S=1 lam=1 k={k}")
    f = build(*family1(0.3))
    for r in [0.05, 0.15]:
        # axis of family 1 has radius sqrt(1-eps^2) (constant); start off-axis in z
        R0 = np.sqrt(1-0.09)
        test(f, [R0, 0.0, r], 40.0, f"family1 eps=0.3 offset z={r}")
