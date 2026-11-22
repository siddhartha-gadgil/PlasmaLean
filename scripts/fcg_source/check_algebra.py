"""Independent sympy checks (N-42) of algebraic claims in
sources/fusion_complex_geometry_and_stability.pdf: null conic (3.2), E/O Laurent basis
(Prop. 2), homological equation (Q4), full-orbit identity (Q7), commutator (C1)."""
import sympy as sp
from sympy import Rational as Q

u, v, z, lam = sp.symbols('u v z lambda')
lapq = lambda F: sp.expand(4*sp.diff(F, u, v) + sp.diff(F, z, 2))
# null conic: Q_lambda^n harmonic, coefficients H_{n,k} independent, dim count
Ql = u + 2*lam*z - lam**2*v
ok = True
for n in range(1, 6):
    Hs = sp.Poly(sp.expand(Ql**n), lam).all_coeffs()
    ok &= all(lapq(H) == 0 for H in Hs) and len(Hs) == 2*n + 1 and all(H != 0 for H in Hs)
print('null-conic H_{n,k} harmonic, 2n+1 nonzero (n<=5):', ok)
print('sum_{n=1}^N (2n+1) == N(N+2) (N<=20):', all(sum(2*n+1 for n in range(1, N+1)) == N*(N+2) for N in range(1, 21)))
# real direction of the line Q_lambda = a
a_, b_ = sp.symbols('a b', real=True)
x, y, zz = sp.symbols('x y zz', real=True)
L = a_ + sp.I*b_
Qr = sp.expand((x + sp.I*y) + 2*L*zz - L**2*(x - sp.I*y))
grads = [sp.diff(Qr, s) for s in (x, y, zz)]
n_l = sp.Matrix([-2*a_, -2*b_, 1 - a_**2 - b_**2])
print('n_lambda annihilates dQ (line direction):', all(sp.simplify(sum(g*c for g, c in zip(grads, n_l))) == 0 for _ in [0]))
# Prop 2: E_pq, O_pq harmonic
def ff(p, j):
    r = 1
    for i in range(j): r *= (p - i)
    return r
def E(p, q, odd):
    M = min(t for t in (p, q) if t >= 0)
    return sum(Q((-4)**j*ff(p, j)*ff(q, j), sp.factorial(2*j + odd))*u**(p-j)*v**(q-j)*z**(2*j+odd) for j in range(M + 1))
print('E_pq, O_pq harmonic for -4<=p,q<=4 (not both negative):',
      all(lapq(E(p, q, o)) == 0 for p in range(-4, 5) for q in range(-4, 5) if not (p < 0 and q < 0) for o in (0, 1)))
# (Q4): b unit, S symmetric with tr S=0, b^T S b=0  =>  C symmetric, [C,K]=S
th, ph = sp.symbols('theta phi', real=True)
b = sp.Matrix([sp.sin(th)*sp.cos(ph), sp.sin(th)*sp.sin(ph), sp.cos(th)])
K = sp.Matrix([[0, b[2], -b[1]], [-b[2], 0, b[0]], [b[1], -b[0], 0]])   # K v = v x b
w = sp.Matrix([sp.Symbol(f'w{i}') for i in range(3)])
assert sp.simplify(K*w - w.cross(b)) == sp.zeros(3, 1)
s = sp.symbols('s0:6')
S0 = sp.Matrix([[s[0], s[1], s[2]], [s[1], s[3], s[4]], [s[2], s[4], s[5]]])
P = sp.eye(3) - b*b.T
# project S0 onto the admissible set: remove trace and the bb component
S1 = S0 - (b.T*S0*b)[0]*b*b.T
S = S1 - (S1.trace()/2)*P   # P has trace 2 and b^T P b = 0
S = sp.simplify(S)
assert sp.simplify(S.trace()) == 0 and sp.simplify((b.T*S*b)[0]) == 0
a = S*b; Sp = P*S*P
C = b*(K*a).T + (K*a)*b.T - Q(1, 2)*Sp*K
print('(Q4) C symmetric:', sp.simplify(C - C.T) == sp.zeros(3, 3))
print('(Q4) CK - KC == S:', sp.simplify(C*K - K*C - S) == sp.zeros(3, 3))
# Frobenius identity ||C||^2 = 2|a|^2 + ||S_perp||^2/4 at random numeric points
import random
okF = True
for _ in range(5):
    sub = {th: random.random()*3, ph: random.random()*6, **{si: random.uniform(-1, 1) for si in s}}
    Cn = C.subs(sub).evalf(); an = a.subs(sub).evalf(); Spn = Sp.subs(sub).evalf(); Sn = S.subs(sub).evalf()
    lhs = sum(c**2 for c in Cn); rhs = 2*an.dot(an) + sum(c**2 for c in Spn)/4
    okF &= abs(lhs - rhs) < 1e-9 and rhs <= sum(c**2 for c in Sn) + 1e-9
print('(Q4) ||C||_F^2 = 2|a|^2 + ||S_perp||^2/4 <= ||S||^2 (numeric):', okF)
# R_b(v^T C v) = v^T (CK-KC) v for symmetric C
vv = sp.Matrix(sp.symbols('v0:3'))
quad = (vv.T*C*vv)[0]
Rb = sum(((vv.cross(b))[i])*sp.diff(quad, vv[i]) for i in range(3))
print('(Q4) R_b(v^T C v) == v^T [C,K] v:', sp.simplify(Rb - (vv.T*(C*K - K*C)*vv)[0]) == 0)
# (Q7) pointwise: dJ/dt with Lorentz force, given B x u = grad psi, D = C/beta
# d/dt(psi - eps u.v + eps^2 v^T D v) = v.grad psi - eps v^T (grad u) v - u.(v x B) + eps^2 v v v dD + 2 eps v^T D (v x B)
# Check the algebraic cancellation: -eps v^T S v + 2 eps v^T D (beta K v) == 0  with D = C/beta
print('(Q7) cancellation -v^T S v + 2 v^T C K v == 0:', sp.simplify(-(vv.T*S*vv)[0] + 2*(vv.T*C*K*vv)[0]) == 0)
