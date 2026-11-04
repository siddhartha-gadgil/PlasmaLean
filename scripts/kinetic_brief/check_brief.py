"""Exact re-derivations for the kinetic/coil research brief (N-36).

Source: sources/PlasmaLean_Kinetic_Coil_Research_Brief.pdf (3 November 2026,
SHA-256 0ab99948d7937c11ffaa9442d2604ff7d2b413399aec10c57c8a7de328d2ecdd).
Each check prints PASS or FAIL. Run: .venv-ws/bin/python -I scripts/kinetic_brief/check_brief.py
"""
import itertools
import sympy as sp

results = []


def report(name, ok):
    results.append((name, bool(ok)))
    print(("PASS " if ok else "FAIL ") + name)


# 1. Landau kernel U(z) = (I - z z^T/|z|^2)/|z|  (eq. 3.2; App. B item 1)
z = sp.Matrix(sp.symbols("z1:4", real=True))
nz2 = (z.T * z)[0]
U = (sp.eye(3) - z * z.T / nz2) / sp.sqrt(nz2)
report("Landau U(z) z = 0", sp.simplify(U * z) == sp.zeros(3, 1))
a = sp.Matrix(sp.symbols("a1:4", real=True))
quad = sp.simplify((a.T * U * a)[0] * sp.sqrt(nz2) * nz2)
# |z|^3 a.U a = |a|^2|z|^2 - (a.z)^2 >= 0 (Cauchy-Schwarz / Lagrange identity)
lag = sum((a[i] * z[j] - a[j] * z[i]) ** 2 for i in range(3) for j in range(i + 1, 3))
report("Landau a.U(z)a = |a x z|^2/|z|^3 >= 0", sp.expand(quad - lag) == 0)

# 2. Energy-flux decomposition (5.5) on a random discrete velocity distribution
m = sp.Rational(3, 2)
pts = [sp.Matrix(p) for p in [(1, 0, 2), (-1, 3, 1), (2, -2, 0), (0, 1, -3), (4, 1, 1)]]
wts = [sp.Rational(k, 7) for k in (1, 2, 3, 1, 5)]
n = sum(wts)
u = sum((w * v for w, v in zip(wts, pts)), sp.zeros(3, 1)) / n
Pi = sum((m * w * (v - u) * (v - u).T for w, v in zip(wts, pts)), sp.zeros(3, 3))
T = Pi.trace() / (3 * n)
F = sum((sp.Rational(1, 2) * m * (v.T * v)[0] * v * w for w, v in zip(wts, pts)), sp.zeros(3, 1))
q = sum((sp.Rational(1, 2) * m * ((v - u).T * (v - u))[0] * (v - u) * w for w, v in zip(wts, pts)), sp.zeros(3, 1))
rhs = (sp.Rational(1, 2) * m * n * (u.T * u)[0] + sp.Rational(3, 2) * n * T) * u + Pi * u + q
report("energy flux F = (m n|u|^2/2 + 3nT/2) u + Pi u + q  (5.5)", sp.simplify(F - rhs) == sp.zeros(3, 1))

# 3. Nonconstant Maxwellian is not a zero-flow stationary solution (Sec. 7.4, App. B item 6)
x, y, w3 = sp.symbols("x y w3", real=True)
v1, v2, v3 = sp.symbols("v1 v2 v3", real=True)
qs, ms = sp.symbols("q m", positive=True)
nf = sp.Function("n")(x, y, w3)
Tf = sp.Function("T")(x, y, w3)
E = [sp.Function(f"E{i}")(x, y, w3) for i in range(3)]
B = [sp.Function(f"B{i}")(x, y, w3) for i in range(3)]
X = [x, y, w3]
V = [v1, v2, v3]
v2sum = v1**2 + v2**2 + v3**2
f = nf * (ms / (2 * sp.pi * Tf)) ** sp.Rational(3, 2) * sp.exp(-ms * v2sum / (2 * Tf))
vxB = [V[1] * B[2] - V[2] * B[1], V[2] * B[0] - V[0] * B[2], V[0] * B[1] - V[1] * B[0]]
L = sum(V[i] * sp.diff(f, X[i]) for i in range(3)) + sum(
    qs / ms * (E[i] + vxB[i]) * sp.diff(f, V[i]) for i in range(3))
bracket = sum(V[i] * (sp.diff(sp.log(nf), X[i]) + (ms * v2sum / (2 * Tf) - sp.Rational(3, 2))
                       * sp.diff(sp.log(Tf), X[i]) - qs * E[i] / Tf) for i in range(3))
report("Vlasov operator on local Maxwellian = f * v.[grad log n + (m|v|^2/2T - 3/2) grad log T - qE/T]",
       sp.simplify(sp.expand(L / f - bracket)) == 0)
# cubic coefficient in v is (m/2T) |v|^2 v.grad log T: vanishes for all v iff grad T = 0
cubic = sp.Poly(sp.expand(bracket), v1, v2, v3)
c300 = cubic.coeff_monomial(v1**3)
report("cubic coefficient of v1^3 is (m/2T) d_x log T", sp.simplify(c300 - ms / (2 * Tf) * sp.diff(sp.log(Tf), x)) == 0)

# 4. Gyrotropic Jacobian d^3v = 2 pi B0 dv_par dmu / m  (Sec. 6.2)
vperp, B0, mu = sp.symbols("v_perp B0 mu", positive=True)
mu_of = ms * vperp**2 / (2 * B0)
# d^3v = v_perp dv_perp dtheta dv_par ; dmu = (m v_perp / B0) dv_perp
jac = 2 * sp.pi * vperp / sp.diff(mu_of, vperp)
report("d^3v = 2 pi B0 dv_par dmu / m", sp.simplify(jac - 2 * sp.pi * B0 / ms) == 0)

# 5. Electrostatic free energy (8.3): the two forms agree under quasineutrality.
#    Per species s: A_s = int |eta|^2/F0, c_s = int J0 eta (real case), int F0 J0^2 = n Gamma0.
#    h = eta + q F0 J0 phi / T.  Quasineutrality: sum q int J0 h = sum n q^2 phi / T.
S = 2
Ts = sp.symbols("T1:3", positive=True)
qq = sp.symbols("q1:3", real=True)
ns = sp.symbols("n1:3", positive=True)
G0 = sp.symbols("G1:3", positive=True)
A = sp.symbols("A1:3", nonnegative=True)
c = sp.symbols("c1:3", real=True)
phi = sp.symbols("phi", real=True)
int_h2_over_F0 = [A[s] + 2 * qq[s] * phi * c[s] / Ts[s] + qq[s] ** 2 * phi**2 * ns[s] * G0[s] / Ts[s] ** 2 for s in range(S)]
W1 = sp.Rational(1, 2) * sum(Ts[s] * int_h2_over_F0[s] - ns[s] * qq[s] ** 2 / Ts[s] * phi**2 for s in range(S))
W2 = sp.Rational(1, 2) * sum(Ts[s] * A[s] + ns[s] * qq[s] ** 2 / Ts[s] * (1 - G0[s]) * phi**2 for s in range(S))
qn = sum(qq[s] * (c[s] + qq[s] * phi * ns[s] * G0[s] / Ts[s]) for s in range(S)) - sum(ns[s] * qq[s] ** 2 * phi / Ts[s] for s in range(S))
# eliminate c1 using quasineutrality
c1_sol = sp.solve(qn, c[0])[0]
report("free energy W: |h|^2 form = |eta|^2 + (1-Gamma0)|phi|^2 form (8.3)", sp.simplify((W1 - W2).subs(c[0], c1_sol)) == 0)
# Gamma0 = I0(b) e^{-b} in (0, 1] for b >= 0 (gives W >= 0): check numerically on a grid
ok = all(0 < sp.N(sp.besseli(0, b) * sp.exp(-b)) <= 1 for b in [0, sp.Rational(1, 10), 1, 5, 50])
report("Gamma0(b) = I0(b) e^{-b} in (0, 1] on sample points", ok)

# 6. Inward-pointing radius (10.1): exists r > 0 with -lam r + L r^2 + eps <= 0  iff  lam^2 >= 4 L eps
lam, Lc, eps, r = sp.symbols("lam L eps r", positive=True)
roots = sp.solve(sp.Eq(-lam * r + Lc * r**2 + eps, 0), r)
disc = sp.discriminant(Lc * r**2 - lam * r + eps, r)
report("discriminant of L r^2 - lam r + eps is lam^2 - 4 L eps", sp.expand(disc - (lam**2 - 4 * Lc * eps)) == 0)
rmin = lam / (2 * Lc)
report("value at r = lam/(2L) is eps - lam^2/(4L)", sp.simplify((-lam * r + Lc * r**2 + eps).subs(r, rmin) - (eps - lam**2 / (4 * Lc))) == 0)

# 7. Hodge star in R^4, orientation dtau ^ dx1 ^ dx2 ^ dx3 (Sec. 7.3, App. B item 5)
#    2-forms as antisymmetric 4x4 matrices; (*F)_{ab} = 1/2 eps_{abcd} F_{cd}.
def levi(*idx):
    return sp.LeviCivita(*idx)


def hodge(Fm):
    out = sp.zeros(4, 4)
    for a_, b_ in itertools.product(range(4), repeat=2):
        out[a_, b_] = sp.Rational(1, 2) * sum(levi(a_, b_, c_, d_) * Fm[c_, d_] for c_ in range(4) for d_ in range(4))
    return out


Bv = sp.symbols("b1:4", real=True)
dtau_alpha = sp.zeros(4, 4)  # dtau ^ alpha, alpha = sum B_i dx_i ; index 0 = tau
for i in range(3):
    dtau_alpha[0, i + 1] = Bv[i]
    dtau_alpha[i + 1, 0] = -Bv[i]
beta = sp.zeros(4, 4)  # beta = i_B vol3 = B1 dx2^dx3 + B2 dx3^dx1 + B3 dx1^dx2
for (i, j, k) in [(1, 2, 0), (2, 0, 1), (0, 1, 2)]:
    beta[i + 1, j + 1] = Bv[k]
    beta[j + 1, i + 1] = -Bv[k]
Fb = dtau_alpha - beta  # brief: F = dtau ^ alpha - *3 alpha, and *3 alpha = beta
report("brief (7.3): *4 F = -F for F = dtau^alpha - beta (orientation dtau^vol3)", sp.simplify(hodge(Fb) + Fb) == sp.zeros(4, 4))
Fn = dtau_alpha + beta  # N-32: F = beta + dt ^ alpha
report("N-32 form beta + dt^alpha is SELF-dual for orientation dt^vol3", sp.simplify(hodge(Fn) - Fn) == sp.zeros(4, 4))

print()
print(f"{sum(ok for _, ok in results)}/{len(results)} checks passed")
