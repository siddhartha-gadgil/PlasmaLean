"""UNTRUSTED. Symbolic derivation of the flow form of the guiding-centre field
B~ = B + rho curl b  (b = B/|B|, B = field(1/4)) used by Design/RationalStellaratorGCFlow.lean.

Variables u = R - 1, z, c = cos 2phi, s = sin 2phi, W = q^{-1/2},
q = nR^2 + R^2 D^2 + nZ^2 = R^8 |B|^2.  Formal derivations: d/du, d/dz, phiD = -2s d/dc + 2c d/ds,
extended to W by dW = -1/2 W^3 dq.  Identities are checked modulo W^2 q = 1.
"""
import sympy as sp

u, z, c, s, W, rho = sp.symbols('u z c s W rho')
R = 1 + u
eps = sp.Rational(1, 4)
Rr, ph = sp.symbols('Rr ph', positive=True)

# h = f cos2phi + g sin2phi in cylindrical (R, z)
f = ((R**2 - 1)**2 - 4*z**2) / (4*R**2)
g = -z*((R**2 - 1)*(R**2 - 5) - 4*z**2) / (4*R**2)
h = f*c + g*s

def dU(e): return sp.diff(e, u) + sp.diff(e, W) * (-sp.Rational(1, 2) * W**3 * dU(qq) if False else 0)

# base field polynomials
D = sp.expand(R**2 * (1 + eps * (sp.diff(h, c) * (-2*s) + sp.diff(h, s) * (2*c))))
D = sp.expand(sp.cancel(D))
nR = sp.expand(sp.cancel(eps * R**4 * sp.diff(h, u)))
nZ = sp.expand(sp.cancel(eps * R**4 * sp.diff(h, z)))
print('D poly?', D.is_polynomial(u, z, c, s), nR.is_polynomial(u, z, c, s), nZ.is_polynomial(u, z, c, s))

q = sp.expand(nR**2 + R**2 * D**2 + nZ**2)

def d_u(e):
    return sp.expand(sp.diff(e, u) + sp.diff(e, W) * (-sp.Rational(1, 2) * W**3 * sp.diff(q, u)))
def d_z(e):
    return sp.expand(sp.diff(e, z) + sp.diff(e, W) * (-sp.Rational(1, 2) * W**3 * sp.diff(q, z)))
def phiDp(e):  # formal phi derivative of a polynomial in u z c s
    return sp.expand(sp.diff(e, c) * (-2*s) + sp.diff(e, s) * (2*c))
def d_phi(e):
    return sp.expand(phiDp(e).subs(W, W) if not e.has(W) else
                     sp.diff(e, c) * (-2*s) + sp.diff(e, s) * (2*c) +
                     sp.diff(e, W) * (-sp.Rational(1, 2) * W**3 * phiDp(q)))

qR, qz, qphi = sp.diff(q, u), sp.diff(q, z), phiDp(q)
# B~ flow form (D~ = R^3 B~_phi, n~ = R^4 (B~^R, B~^z))
Dt = D + rho/2 * W**3 * R**2 * (R*nZ*qR - 8*nZ*q - R*nR*qz)
nRt = nR + rho/2 * W**3 * (R**5 * D * qz - R**3 * nZ * qphi)
nZt = nZ + rho/2 * W**3 * (R**3 * nR * qphi - R**5 * D * qR + 8 * R**4 * D * q)

# numerical check against direct vector calculus of B + rho curl(B/|B|)
import random, math
Rs, Zs, Ps = sp.symbols('Rs Zs Ps', real=True)
cs = {u: Rs - 1, c: sp.cos(2*Ps), s: sp.sin(2*Ps), z: Zs}
BR = (nR / R**4).subs(cs); Bph = (D / R**3).subs(cs); BZ = (nZ / R**4).subs(cs)
Bn = sp.sqrt(BR**2 + Bph**2 + BZ**2)
bR, bph, bZ = BR/Bn, Bph/Bn, BZ/Bn
# curl in cylindrical (physical components)
cR = sp.diff(bZ, Ps)/Rs - sp.diff(bph, Zs)
cph = sp.diff(bR, Zs) - sp.diff(bZ, Rs)
cZ = (sp.diff(Rs*bph, Rs) - sp.diff(bR, Ps))/Rs
rv = sp.Rational(3, 1000)
for _ in range(3):
    pt = {Rs: 1 + random.uniform(-.2, .2), Zs: random.uniform(-.2, .2), Ps: random.uniform(0, 3)}
    Wv = 1/sp.sqrt(q.subs(cs).subs(pt))
    sub = lambda e: sp.N(e.subs(rho, rv).subs(W, Wv).subs(cs).subs(pt), 20)
    direct = [sp.N((BR + rv*cR).subs(pt), 20), sp.N((Bph + rv*cph).subs(pt), 20), sp.N((BZ + rv*cZ).subs(pt), 20)]
    Rv = pt[Rs]
    mine = [sub(nRt)/Rv**4, sub(Dt)/Rv**3, sub(nZt)/Rv**4]
    print('check', [float(a - b) for a, b in zip(direct, mine)])

rel = sp.expand(W**2 * q - 1)
def red(e):
    """reduce modulo W^2 q - 1 (as polynomial in W: replace W^2 -> 1/q is not polynomial;
    instead test e == 0 mod rel by polynomial division in W after multiplying by q powers)."""
    e = sp.expand(e)
    # e = sum_k a_k W^k ; use W^2 = 1/q  ->  e*q^K is a polynomial in (u,z,c,s) + W*poly
    P = sp.Poly(e, W)
    deg = P.degree()
    K = deg // 2 + 1
    even = 0; odd = 0
    for (k,), a in P.terms():
        if k % 2 == 0:
            even += a * q**(K - k//2)
        else:
            odd += a * q**(K - (k-1)//2)
    return sp.expand(even), sp.expand(odd)

div = R*d_phi(Dt) - 3*nRt + R*d_u(nRt) + R*d_z(nZt)
ev, od = red(div)
print('divFree mod rel:', ev == 0, od == 0)

# flux primitive: base Pa, Pb from Lean (check), then Pa~ = Pa + sA*rho*R*W*nR etc.
Pa = sp.Rational(1,32)*u**4*c + sp.Rational(1,8)*u**3*c - sp.Rational(1,4)*u*c - sp.Rational(3,8)*z**2*c - sp.Rational(1,4)*z*s - z
Pb = (-sp.Rational(1,16)*u**4*z*c - sp.Rational(1,16)*u**4*s - sp.Rational(1,4)*u**3*z*c - sp.Rational(1,4)*u**3*s
      - sp.Rational(3,8)*u**2*z*c - sp.Rational(3,8)*u**2*s - sp.Rational(1,4)*u*z*c - sp.Rational(1,4)*u*s
      - sp.Rational(1,4)*z**3*c - sp.Rational(1,4)*z**2*s + sp.Rational(1,4)*z*c)
print('base flux_a', sp.expand(R*sp.diff(Pb,u) - 2*Pb - R**2*sp.diff(Pa,z) - D) == 0)
print('base flux_b', sp.expand(R**2*phiDp(Pa) - nZ) == 0, 'flux_c', sp.expand(R*phiDp(Pb) + nR) == 0)
for sA in [1, -1]:
    Pat = Pa + sA*rho*R*W*nR
    Pbt = Pb + sA*rho*R**2*W*nZ
    Pct = sA*rho*R**2*W*D
    fa = R*d_u(Pbt) - 2*Pbt - R**2*d_z(Pat) - Dt
    fb = R**2*d_phi(Pat) - R**3*d_u(Pct) - nZt
    fc = R*d_phi(Pbt) - R**3*d_z(Pct) + nRt
    print('sign', sA, [all(x == 0 for x in red(e)) for e in (fa, fb, fc)])
