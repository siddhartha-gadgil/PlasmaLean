"""Exact jet data for the QS jet obstruction of RationalStellarator.field (1/4) at p0 = (1, 0, 1/4).

Untrusted generator for PlasmaLean/Design/RationalStellaratorJetObstruction.lean (Q-25 (c)).
Everything is exact (sympy rationals / fractions.Fraction). It
  * expands the field coordinates b_i as polynomials in (x, y, z, w), w = 1/(x^2+y^2), with the
    exact coefficients used in Lean (`Pb0`, `Pb1`, `Pb2`), and checks them against the
    rational-function definition of the field (Hnum, H = Hnum/r2^2, B = grad phi + eps/4 grad H);
  * computes the partial derivatives of b up to order 3 at p0 (tables `bt`, `Jt`, `Kt`, `Lt`,
    `Jt i j = d_j b_i`, `Kt i j l = d_l d_j b_i`, `Lt i j l m = d_m d_l d_j b_i`);
  * evaluates the Lean jet formulas (gqF, YF, YdF, ZF, ZdF, hF, hdF, kF, kdF, ...) on these tables,
    cross-checks them against direct symbolic differentiation of Y = B x grad Q, Z = [B, Y],
    h = B . grad Q, k = B . grad h, and solves for eta(p0) = w0 and D eta(p0) = S;
  * asserts every identity checked in Lean (JetSolution equations, det, curl S != 0) exactly;
  * prints the Lean data (`--lean`).
Run: python rational_stellarator_jet.py [--lean]
"""
import sys
from fractions import Fraction as F
import sympy as sp

x, y, z, w = sp.symbols('x y z w')
X3 = [x, y, z]
EPS = sp.Rational(1, 4)
P0 = (sp.Integer(1), sp.Integer(0), sp.Rational(1, 4))

# --- the field, as in RationalStellarator.lean -------------------------------------------
r2 = x**2 + y**2
Aq = (r2 - 1)**2 - 4*z**2
Bq = (r2 - 1)*(r2 - 5) - 4*z**2
Hnum = sp.expand(Aq*(x**2 - y**2) - Bq*(2*x*y*z))
Hd = [sp.diff(Hnum, v) for v in X3]
cv = [x, y, 0]
G = [Hd[i]*w**2 - 4*cv[i]*Hnum*w**3 for i in range(3)]
tor = [-y*w, x*w, 0]
bpoly = [sp.expand(tor[i] + EPS/4*G[i]) for i in range(3)]

# check the polynomial form against the rational field
Hrat = Hnum / r2**2
Brat = [-y/r2 + EPS/4*sp.diff(Hrat, x), x/r2 + EPS/4*sp.diff(Hrat, y), EPS/4*sp.diff(Hrat, z)]
for i in range(3):
    assert sp.simplify(bpoly[i].subs(w, 1/r2) - Brat[i]) == 0

def monos(p):
    P = sp.Poly(p, x, y, z, w)
    return [(F(int(c.p), int(c.q)), *e) for e, c in zip(P.monoms(), P.coeffs())]

Pb = [monos(bpoly[i]) for i in range(3)]

# --- tables of partial derivatives at p0 --------------------------------------------------
sub = dict(zip(X3, P0))
def val(e):
    v = sp.Rational(e.subs(sub))
    return F(int(v.p), int(v.q))
R = range(3)
bt = [val(Brat[i]) for i in R]
D1 = [[sp.diff(Brat[i], X3[j]) for j in R] for i in R]
Jt = [[val(D1[i][j]) for j in R] for i in R]
D2 = [[[sp.diff(D1[i][j], X3[l]) for l in R] for j in R] for i in R]
Kt = [[[val(D2[i][j][l]) for l in R] for j in R] for i in R]
Lt = [[[[val(sp.diff(D2[i][j][l], X3[m])) for m in R] for l in R] for j in R] for i in R]
# the polynomial form evaluates to the same base values (w = 1 at p0)
assert all(val(bpoly[i].subs(w, 1)) == bt[i] for i in R)

# --- the Lean jet formulas ---------------------------------------------------------------
def dot3(u, v): return u[0]*v[0] + u[1]*v[1] + u[2]*v[2]
def crossF(u, v): return [u[1]*v[2] - u[2]*v[1], u[2]*v[0] - u[0]*v[2], u[0]*v[1] - u[1]*v[0]]
col = lambda M, j: [M[i][j] for i in R]
def gq(j): return 2*dot3(bt, col(Jt, j))
def gqd(j, l): return 2*(dot3([Jt[i][l] for i in R], col(Jt, j)) + dot3(bt, [Kt[i][j][l] for i in R]))
def gqdd(j, l, m):
    return 2*((dot3([Kt[i][l][m] for i in R], col(Jt, j)) + dot3(col(Jt, l), [Kt[i][j][m] for i in R]))
              + (dot3(col(Jt, m), [Kt[i][j][l] for i in R]) + dot3(bt, [Lt[i][j][l][m] for i in R])))
GQ = [gq(j) for j in R]
Yv = crossF(bt, GQ)
def Yd(l): return [a + b for a, b in zip(crossF(col(Jt, l), GQ), crossF(bt, [gqd(a, l) for a in R]))]
def Ydd(l, m):
    t1 = crossF([Kt[a][l][m] for a in R], GQ)
    t2 = crossF(col(Jt, l), [gqd(a, m) for a in R])
    t3 = crossF(col(Jt, m), [gqd(a, l) for a in R])
    t4 = crossF(bt, [gqdd(a, l, m) for a in R])
    return [(t1[i] + t2[i]) + (t3[i] + t4[i]) for i in R]
hv = dot3(bt, GQ)
def hd(l): return dot3(col(Jt, l), GQ) + dot3(bt, [gqd(a, l) for a in R])
def hdd(l, m):
    return ((dot3([Kt[a][l][m] for a in R], GQ) + dot3(col(Jt, l), [gqd(a, m) for a in R]))
            + (dot3(col(Jt, m), [gqd(a, l) for a in R]) + dot3(bt, [gqdd(a, l, m) for a in R])))
YD = [Yd(l) for l in R]
Zv = [dot3([YD[l][i] for l in R], bt) - dot3(Jt[i], Yv) for i in R]
def Zd(i, m):
    return ((dot3([Ydd(l, m)[i] for l in R], bt) + dot3([YD[l][i] for l in R], col(Jt, m)))
            - (dot3([Kt[i][l][m] for l in R], Yv) + dot3(Jt[i], YD[m])))
kv = dot3([hd(l) for l in R], bt)
def kd(m): return dot3([hdd(l, m) for l in R], bt) + dot3([hd(l) for l in R], col(Jt, m))

MX = Jt
MY = [[YD[l][i] for l in R] for i in R]
MZ = [[Zd(i, m) for m in R] for i in R]
dh = [hd(l) for l in R]
dk = [kd(m) for m in R]

# --- cross-check against direct symbolic differentiation ---------------------------------
Bm = sp.Matrix(Brat)
Q = (Bm.T*Bm)[0]
gQ = sp.Matrix([sp.diff(Q, v) for v in X3])
Ys = Bm.cross(gQ)
hs = (Bm.T*gQ)[0]
jac = lambda V: sp.Matrix(3, 3, lambda i, j: sp.diff(V[i], X3[j]))
Zs = jac(Ys)*Bm - jac(Bm)*Ys
ks = sum(sp.diff(hs, X3[j])*Bm[j] for j in R)
assert [val(Ys[i]) for i in R] == Yv and [val(Zs[i]) for i in R] == Zv
assert val(hs) == hv and val(ks) == kv
assert [[val(sp.diff(Ys[i], X3[j])) for j in R] for i in R] == MY
assert [[val(sp.diff(Zs[i], X3[j])) for j in R] for i in R] == MZ
assert [val(sp.diff(hs, v)) for v in X3] == dh and [val(sp.diff(ks, v)) for v in X3] == dk

# --- eta(p0) and D eta(p0) ----------------------------------------------------------------
Mrows = sp.Matrix([bt, Yv, Zv])
w0 = Mrows.LUsolve(sp.Matrix([0, -hv, -kv]))
wq = [F(int(sp.Rational(c).p), int(sp.Rational(c).q)) for c in w0]
S = [[None]*3 for _ in R]
for j in R:
    rhs = sp.Matrix([-dot3(col(MX, j), wq), -dh[j] - dot3(col(MY, j), wq),
                     -dk[j] - dot3(col(MZ, j), wq)])
    sol = Mrows.LUsolve(rhs)
    for i in R:
        c = sp.Rational(sol[i]); S[i][j] = F(int(c.p), int(c.q))
# exact checks (the Lean `jetCheck`)
assert dot3(bt, wq) == 0 and dot3(Yv, wq) == -hv and dot3(Zv, wq) == -kv
for j in R:
    Sj = col(S, j)
    assert dot3(bt, Sj) == -dot3(col(MX, j), wq)
    assert dot3(Yv, Sj) == -dh[j] - dot3(col(MY, j), wq)
    assert dot3(Zv, Sj) == -dk[j] - dot3(col(MZ, j), wq)
det = dot3(bt, crossF(Yv, Zv))
assert det != 0
curl = [S[2][1] - S[1][2], S[0][2] - S[2][0], S[1][0] - S[0][1]]
assert curl[1] != 0

def nrm(v): return float(sum(c*c for c in v))**0.5
print('p0 =', P0, ' B(p0) =', bt)
print('Q =', dot3(bt, bt), ' h =', hv, ' k =', kv)
print('Y =', Yv); print('Z =', Zv)
print('det(X,Y,Z) =', det, '=', float(det), ' normalized:', float(det)/(nrm(bt)*nrm(Yv)*nrm(Zv)))
print('eta(p0) =', wq)
print('curl S =', curl, '~', [float(c) for c in curl])
print('monomials per coordinate:', [len(p) for p in Pb])

def lq(c):
    c = F(c)
    if c.denominator == 1: return f'({c.numerator})' if c.numerator < 0 else f'{c.numerator}'
    return f'({c.numerator}/{c.denominator})'
def tokens(t):
    """Tokens of a nested `![...]` literal; commas stay attached to the preceding token."""
    if not isinstance(t, list): return [lq(t)]
    out = ['![']
    for k, s in enumerate(t):
        ts = tokens(s)
        if k < len(t) - 1: ts[-1] += ','
        out += ts
    out[-1] += ']'
    return out
def wrap(head, toks, indent='    ', width=100):
    lines, cur = [], head
    for tk in toks:
        sep = '' if cur.endswith('[') or cur == indent else ' '
        if len(cur) + len(sep) + len(tk) > width:
            lines.append(cur.rstrip()); cur = indent + tk
        else:
            cur += sep + tk
    lines.append(cur)
    return '\n'.join(lines)
if '--lean' in sys.argv:
    for i in R:
        ms = [f'({lq(m[0])}, {m[1]}, {m[2]}, {m[3]}, {m[4]})' for m in Pb[i]]
        ms = [m + ',' for m in ms[:-1]] + [ms[-1] + ']']
        ms[0] = '[' + ms[0]
        print(wrap(f'Pb{i} :=', ['\n  '] if False else ms, indent='    '))
    for name, t in [('bt', bt), ('Jt', Jt), ('Kt', Kt), ('Lt', Lt), ('wt', wq), ('St', S)]:
        print(wrap(f'{name} :=', tokens(t)))
    print('det :=', lq(det)); print('curl1 :=', lq(curl[1]))
