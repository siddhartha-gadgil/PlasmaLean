"""UNTRUSTED generator (N-33 plan item 5): the Dommaschk certification target in flow form for the
generalised KAM interface `FlowFieldG` (`PlasmaLean/Design/KamFlowFieldG.lean`).

Writes `PlasmaLean/Design/DommaschkKamFieldData.lean` (sparse polynomial data, `DkPoly.SP`: the
u-form data, the R-form data and common denominators for the identification, and the obstruction
data `dQ`, `Kq`). The kernel checks are in the hand-written `DommaschkKamFieldCheck.lean` and
`DommaschkKamIdentCheck.lean`. Every identity is validated here first, in exact rational arithmetic,
by Python mirrors of the Lean checkers (`DommaschkKamPoly.lean`: `merge`, `mulMono`, `dvar`, `phi`;
`CylAlgebra.nf`/`sliceCheck` and the conversions of `DommaschkKamIdentCheck.lean`), so that a wrong
polynomial fails in Python and not in a Lean build. Independent check: D = R^7 B_phi,
n_R = R^8 B_R, n_z = R^8 B_z at rational points against the Cartesian potentials parsed from
`DommaschkQA2RData.lean`.

Model (`scripts/dommaschk_kam/README.md`, N-31 section 24): B = grad(phi + V), V = sum_k a_k V_k,
the 9 log potentials exactly 0, so V = sum c R^p z^j T(m phi) with p, m even, p >= -6.

Variables of the interface: (u, z, c, s) with u = R - R0, c = cos 2 phi, s = sin 2 phi (phi the
cylindrical angle; the strip algebra writes c = -sin psi_L, s = cos psi_L with psi_L = 2 phi - pi/2,
`KamFlowField.cS/sS`). The harmonics m = 2k are represented by the *homogeneous* harmonic
polynomials Re/Im (c + i s)^k (cos 2phi = c, cos 4phi = c^2 - s^2, cos 6phi = c^3 - 3 c s^2, ...).
The formal phi-derivative of the interface, phiD = -2 s d_c + 2 c d_s, maps (c + i s)^k to
2 i k (c + i s)^k exactly, so all identities below hold as polynomial identities in independent
(u, z, c, s) (no use of c^2 + s^2 = 1 is needed).

Flow form (density exponent p = ka = kb = 7):
    D   = R^6 (1 + d_phi V)     = R^7 B_phi                 (B_phi the physical component)
    n_R = R^8 d_R V              = R^8 B_R
    n_z = R^8 d_z V              = R^8 B_z
so X = n/D = (R B_R/B_phi, R B_z/B_phi) = (dR/dphi, dz/dphi), and w = D/R^7 = R B^phi.

Flux primitive alpha = (P_a/R^7) dR + (P_b/R^7) dz + P_c dphi:
    V = c0 z + V~ (c0 = coefficient of D_{0,1} = z; every other m = 0 potential has coefficient 0),
    W = the zero-mean phi-antiderivative of V~ (cos m phi -> sin m phi/m, sin -> -cos/m),
    P_a = R^8 d_z W - z R^6,  P_b = -R^8 d_R W,  P_c = -c0 R^2/2.
Identities (cleared of R-powers):
    divFree : R phiD D - 7 n_R + R d_u n_R + R d_z n_z = 0
    flux_a  : R d_u P_b - 7 P_b - R d_z P_a - R D = 0          (d R b - d z a = w)
    flux_b' : phiD P_a - R^7 d_u P_c - n_z = 0                  (d phi a - d R e = w X_z)
    flux_c' : phiD P_b - R^7 d_z P_c + n_R = 0                  (d phi b - d z e = -w X_R)
**Obstruction.** The phi-mean of n_z is c0 R^8 != 0 (c0 = -0.0239...), while every phiD P has zero
phi-mean, so `FlowFieldG.flux_b` (no dphi-component, P_c = 0) is impossible for this field: the
vertical flux of B through the annulus swept by a horizontal segment is pi c0 (R2^2 - R1^2) != 0.
The script checks this (`mean_nz`).
"""
import argparse
import json
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
TARGET = os.path.join(REPO, 'scripts', 'dommaschk_qa', 'results', '20261031T092522Z',
                      'candidate.json')
TARGET_SHA = 'b6d322648bc745dd40ea459c0bf19b0ddc7095683efe7f33a4a2b8b593cf1bb8'
R0 = Fr(29, 32)
P_EXP = 7

# ----------------------------------------------------------------------------------------------
# dict polynomials {(a, b, c, d): Fraction}, a = exponent of R (or u), b of z, c of cos, d of sin


def padd(*ps, scale=None):
    out = {}
    for i, p in enumerate(ps):
        k = Fr(1) if scale is None else scale[i]
        for e, q in p.items():
            v = out.get(e, Fr(0)) + k*q
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    return out


def pscale(p, k):
    return {e: k*q for e, q in p.items()} if k else {}


def pmul(p, q):
    out = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = tuple(x + y for x, y in zip(e1, e2))
            v = out.get(e, Fr(0)) + c1*c2
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    return out


def pdiff(p, i):
    out = {}
    for e, q in p.items():
        if e[i] > 0:
            e2 = list(e); e2[i] -= 1
            out[tuple(e2)] = out.get(tuple(e2), Fr(0)) + e[i]*q
    return {e: q for e, q in out.items() if q}


def mono(a=0, b=0, c=0, d=0, q=Fr(1)):
    return {(a, b, c, d): Fr(q)}


def pphi(p):
    """phiD = -2 s d_c + 2 c d_s."""
    return padd(pmul(mono(d=1, q=-2), pdiff(p, 2)), pmul(mono(c=1, q=2), pdiff(p, 3)))


def harm(k):
    """(Re, Im) of (c + i s)^k as dict polynomials in (c, s) (exponents in slots 2, 3)."""
    re, im = mono(), {}
    for _ in range(k):
        # (re + i im)(c + i s) = (re c - im s) + i (re s + im c)
        re, im = padd(pmul(re, mono(c=1)), pmul(im, mono(d=1)), scale=[1, -1]), \
            padd(pmul(re, mono(d=1)), pmul(im, mono(c=1)))
    return re, im


def subst_R(p, R0):
    """Substitute R = R0 + u (slot 0); all R-exponents must be >= 0."""
    out = {}
    binom_cache = {}
    for (a, b, c, d), q in p.items():
        assert a >= 0, (a, b, c, d)
        if a not in binom_cache:
            poly = mono()
            for _ in range(a):
                poly = pmul(poly, padd(mono(q=R0), mono(a=1)))
            binom_cache[a] = poly
        for (a2, _, _, _), q2 in binom_cache[a].items():
            e = (a2, b, c, d)
            v = out.get(e, Fr(0)) + q*q2
            if v:
                out[e] = v
            else:
                out.pop(e, None)
    return out


# ----------------------------------------------------------------------------------------------
# the field

def load(path=TARGET):
    import hashlib
    cand = json.load(open(path))
    assert cand.get('sha256') == TARGET_SHA, 'unexpected candidate'
    assert cand['nfp'] == 2
    V = {}     # (p, j, kind, m) -> coefficient, value c R^p z^j trig(m phi)
    for bk, a in zip(cand['basis'], cand['coefficients']):
        a = Fr(a)
        haslog = any(int(q) for _, _, q, _ in bk['terms'])
        if a == 0:
            continue
        assert not haslog, bk['name']
        kind = 'c' if bk['m'] == 0 else bk['trig'][0]
        for c, p, q, j in bk['terms']:
            key = (int(p), int(j), kind, bk['m'])
            V[key] = V.get(key, Fr(0)) + a*Fr(c)
    V = {k: v for k, v in V.items() if v}
    return cand, V


def trig_poly(kind, m):
    if m == 0:
        assert kind == 'c'
        return mono()
    assert m % 2 == 0
    re, im = harm(m//2)
    return re if kind == 'c' else im


def build(V):
    """The polynomials in (R, z, c, s) (R-exponents may be checked >= 0 afterwards)."""
    # V0 = c0 z
    m0 = {k: v for k, v in V.items() if k[3] == 0}
    assert set(m0) == {(0, 1, 'c', 0)}, m0
    c0 = m0[(0, 1, 'c', 0)]
    Vt = {k: v for k, v in V.items() if k[3] != 0}
    # V as a Laurent polynomial: store R-exponent p (may be negative) in slot 0
    Vpoly = padd(*[pmul(mono(a=p, b=j, q=c), trig_poly(kind, m)) for (p, j, kind, m), c in
                   V.items()]) if False else None
    Dl, nR, nZ, Wl = {}, {}, {}, {}
    D = mono(a=6)
    terms_V = []
    for (p, j, kind, m), c in V.items():
        T = trig_poly(kind, m)
        terms_V.append((p, j, kind, m, c, T))
    # D = R^6 + R^6 d_phi V; phiD on T is exact (homogeneous harmonics)
    for p, j, kind, m, c, T in terms_V:
        D = padd(D, pmul(mono(a=p + 6, b=j, q=c), pphi(T)))
        if p:
            nR = padd(nR, pmul(mono(a=p + 7, b=j, q=c*p), T))
        if j:
            nZ = padd(nZ, pmul(mono(a=p + 8, b=j - 1, q=c*j), T))
    # W: phi-antiderivative of V~ ; cos m phi -> sin m phi / m, sin m phi -> -cos m phi / m
    Pa = mono(a=6, b=1, q=-1)
    Pb = {}
    for p, j, kind, m, c, T in terms_V:
        if m == 0:
            continue
        re, im = harm(m//2)
        Wt = pscale(im, Fr(1, m)) if kind == 'c' else pscale(re, Fr(-1, m))
        assert pphi(Wt) == T, (kind, m)
        if j:
            Pa = padd(Pa, pmul(mono(a=p + 8, b=j - 1, q=c*j), Wt))
        if p:
            Pb = padd(Pb, pmul(mono(a=p + 7, b=j, q=-c*p), Wt))
    Pc = mono(a=2, q=-c0/2)
    for P in (D, nR, nZ, Pa, Pb, Pc):
        assert all(e[0] >= 0 for e in P), 'negative R power'
    return dict(D=D, nR=nR, nZ=nZ, Pa=Pa, Pb=Pb, Pc=Pc), c0


def identities(P, Rpoly):
    """The four cleared identities; Rpoly = R as a polynomial (mono(a=1) in R-form,
    R0 + u in u-form)."""
    D, nR, nZ, Pa, Pb, Pc = (P[k] for k in ('D', 'nR', 'nZ', 'Pa', 'Pb', 'Pc'))
    R7 = mono()
    for _ in range(7):
        R7 = pmul(R7, Rpoly)
    div = padd(pmul(Rpoly, pphi(D)), pscale(nR, -7), pmul(Rpoly, pdiff(nR, 0)),
               pmul(Rpoly, pdiff(nZ, 1)))
    fa = padd(pmul(Rpoly, pdiff(Pb, 0)), pscale(Pb, -7), pscale(pmul(Rpoly, pdiff(Pa, 1)), -1),
              pscale(pmul(Rpoly, D), -1))
    fb = padd(pphi(Pa), pscale(pmul(R7, pdiff(Pc, 0)), -1), pscale(nZ, -1))
    fc = padd(pphi(Pb), pscale(pmul(R7, pdiff(Pc, 1)), -1), nR)
    return dict(divFree=div, flux_a=fa, flux_b=fb, flux_c=fc)


# ----------------------------------------------------------------------------------------------
# Python mirror of the Lean checker (DommaschkKamPoly): sorted lists of (q, a, b, c, d)

def key(t):
    return t[1:]


def l_merge(p, q):
    out = []
    i = j = 0
    while i < len(p) and j < len(q):
        if key(p[i]) < key(q[j]):
            out.append(p[i]); i += 1
        elif key(q[j]) < key(p[i]):
            out.append(q[j]); j += 1
        else:
            v = p[i][0] + q[j][0]
            if v:
                out.append((v,) + key(p[i]))
            i += 1; j += 1
    return out + p[i:] + q[j:]


def l_scale(k, p):
    return [(k*t[0],) + key(t) for t in p] if k else []


def l_mulMono(t, p):
    return [(t[0]*s[0],) + tuple(x + y for x, y in zip(key(t), key(s))) for s in p if t[0]*s[0]]


def l_mul(p, q):
    acc = []
    for t in reversed(p):
        acc = l_merge(l_mulMono(t, q), acc)
    return acc


def l_dvar(i, p):
    out = []
    for t in p:
        e = list(key(t))
        if e[i] > 0:
            n = e[i]; e[i] -= 1
            out.append((t[0]*n,) + tuple(e))
    return out


def l_phi(p):
    return l_merge(l_mulMono((Fr(-2), 0, 0, 0, 1), l_dvar(2, p)),
                   l_mulMono((Fr(2), 0, 0, 1, 0), l_dvar(3, p)))


def to_list(P):
    return sorted(((q,) + e for e, q in P.items()), key=key)


def is_sorted(p):
    return all(key(p[i]) < key(p[i + 1]) for i in range(len(p) - 1))


def l_identities(L, R0):
    """Exactly the combinations computed by the Lean checks (`DommaschkKamField.lean`)."""
    Rl = [(R0, 0, 0, 0, 0), (Fr(1), 1, 0, 0, 0)]
    R7 = [(Fr(1), 0, 0, 0, 0)]
    for _ in range(7):
        R7 = l_mul(Rl, R7)
    D, nR, nZ, Pa, Pb, Pc = (L[k] for k in ('D', 'nR', 'nZ', 'Pa', 'Pb', 'Pc'))
    div = l_merge(l_merge(l_mul(Rl, l_phi(D)), l_scale(Fr(-7), nR)),
                  l_merge(l_mul(Rl, l_dvar(0, nR)), l_mul(Rl, l_dvar(1, nZ))))
    fa = l_merge(l_merge(l_mul(Rl, l_dvar(0, Pb)), l_scale(Fr(-7), Pb)),
                 l_merge(l_scale(Fr(-1), l_mul(Rl, l_dvar(1, Pa))), l_scale(Fr(-1), l_mul(Rl, D))))
    fb = l_merge(l_merge(l_phi(Pa), l_scale(Fr(-1), l_mul(R7, l_dvar(0, Pc)))), l_scale(Fr(-1), nZ))
    fc = l_merge(l_merge(l_phi(Pb), l_scale(Fr(-1), l_mul(R7, l_dvar(1, Pc)))), nR)
    return dict(divFree=div, flux_a=fa, flux_b=fb, flux_c=fc)


# ----------------------------------------------------------------------------------------------
# independent cross-check against the Lean field `DommaschkQA2R.field candidate` (exact, at
# rational points): parse the Cartesian potentials `P k` and `scale` from DommaschkQA2RData.lean

def parse_cart():
    src = open(os.path.join(REPO, 'PlasmaLean', 'Design', 'DommaschkQA2RData.lean')).read()
    P = {}
    for m in re.finditer(r'def P(\d+) : CylPoly :=\s*\[(.*?)\]\n', src, re.S):
        monos = re.findall(r'⟨\(?(-?\d+)\)?, (\d+), (\d+), (\d+), \(?(-?\d+)\)?, (\d+)⟩',
                           m.group(2))
        P[int(m.group(1))] = [tuple(int(x) for x in t) for t in monos]
    sc = re.search(r'def scale : Fin 42 → ℚ :=\s*!\[(.*?)\]', src, re.S).group(1)
    scale = [Fr(int(a), int(b)) for a, b in re.findall(r'(\d+) / (\d+)', sc)]
    assert len(P) == 42 and len(scale) == 42
    return P, scale


def cart_d(m, i):
    c, a, b, j, s, q = m
    if i == 0:
        return [(c*a, a - 1, b, j, s, q), (c*2*s, a + 1, b, j, s - 1, q),
                (c*2*q, a + 1, b, j, s - 1, q - 1)]
    if i == 1:
        return [(c*b, a, b - 1, j, s, q), (c*2*s, a, b + 1, j, s - 1, q),
                (c*2*q, a, b + 1, j, s - 1, q - 1)]
    return [(c*j, a, b, j - 1, s, q)]


def cart_eval(f, x, y, z):
    r2 = x*x + y*y
    tot = Fr(0)
    for c, a, b, j, s, q in f:
        if c == 0:
            continue
        assert q == 0, 'log term'
        tot += c * x**a * y**b * z**j * r2**s
    return tot


def crosscheck_cart(P_R, cand, npts=8):
    P, scale = parse_cart()
    a = [Fr(c) for c in cand['coefficients']]
    import random
    rnd = random.Random(7)
    for _ in range(npts):
        R = Fr(rnd.randint(80, 105), 100); z = Fr(rnd.randint(-12, 12), 100)
        t = Fr(rnd.randint(-50, 50), 37)
        C, S = (1 - t*t)/(1 + t*t), 2*t/(1 + t*t)        # cos phi, sin phi
        x, y = R*C, R*S
        r2 = R*R
        B = [Fr(0), Fr(0), Fr(0)]
        B[0] += -y/r2; B[1] += x/r2                         # toroidal: grad phi
        for k in range(42):
            if a[k] == 0:
                continue
            for i in range(3):
                B[i] += a[k]*scale[k]*cart_eval([m for mm in P[k] for m in cart_d(mm, i)], x, y, z)
        BR = C*B[0] + S*B[1]; Bphi = -S*B[0] + C*B[1]; Bz = B[2]
        c, s = C*C - S*S, 2*S*C

        def ev(Pd):
            return sum(q*R**aa*z**b*c**cc*s**d for (aa, b, cc, d), q in Pd.items())
        assert ev(P_R['D']) == R**7*Bphi, 'D'
        assert ev(P_R['nR']) == R**8*BR, 'nR'
        assert ev(P_R['nZ']) == R**8*Bz, 'nZ'
    return True


# ----------------------------------------------------------------------------------------------
# Python mirror of the identification checks (`DommaschkKamIdent*.lean`): the R-form data, the
# substitution R = R0 + u, and the Cartesian normal-form check against `field candidate`
# (CylAlgebra `nf`, `sliceCheck`, monomials (c, a, b, j, s, q) = c x^a y^b z^j r2^s log^q)

def l_Rpow(n, R0):
    acc = [(Fr(1), 0, 0, 0, 0)]
    for _ in range(n):
        acc = l_mul([(R0, 0, 0, 0, 0), (Fr(1), 1, 0, 0, 0)], acc)
    return acc


def l_substR(p, R0):
    acc = []
    for t in reversed(p):
        acc = l_merge(l_mulMono((t[0], 0, t[2], t[3], t[4]), l_Rpow(t[1], R0)), acc)
    return acc


def c_mulMono(m, f):
    return [(m[0]*n[0],) + tuple(x + y for x, y in zip(m[1:], n[1:])) for n in f]


def c_mul(f, g):
    return [t for m in f for t in c_mulMono(m, g)]


def c_pow(f, n):
    acc = [(1, 0, 0, 0, 0, 0)]
    for _ in range(n):
        acc = c_mul(f, acc)
    return acc


def c_scale(k, f):
    return [(k*m[0],) + m[1:] for m in f]


X2 = [(1, 2, 0, 0, 0, 0), (-1, 0, 2, 0, 0, 0)]
XY = [(2, 1, 1, 0, 0, 0)]


def c_trig(c, d):
    return c_mul(c_pow(X2, c), c_pow(XY, d))


def c_convT(N, t):
    q, a, b, c, d = t
    k = N*q
    assert k.denominator == 1 and a % 2 == 0
    return c_scale(k.numerator, c_mulMono((1, 0, 0, b, a//2 - c - d, 0), c_trig(c, d)))


def c_convAll(N, p):
    return [m for t in p for m in c_convT(N, t)]


def c_redY(n, m):
    if n == 0:
        return [m]
    c, a, b, j, s, q = m
    if b >= 2:
        return c_redY(n - 1, (c, a, b - 2, j, s + 1, q)) + c_redY(n - 1, (-c, a + 2, b - 2, j, s, q))
    return [m]


def c_nf(f):
    acc = []
    for m in reversed([t for m in f for t in c_redY(m[2], m)]):
        for i, n in enumerate(acc):
            if n[1:] == m[1:]:
                acc[i] = (n[0] + m[0],) + n[1:]
                break
        else:
            acc.append(m)
    return [m for m in acc if m[0] != 0]


def c_sliceCheck(js, f):
    rest = f
    for j in js:
        if c_nf([m for m in rest if m[3] == j]):
            return False
        rest = [m for m in rest if m[3] != j]
    return not c_nf(rest)


def lcm_den(qs):
    from math import lcm
    out = 1
    for q in qs:
        out = lcm(out, Fr(q).denominator)
    return out


def ident_checks(P_R, L_u, cand, R0):
    P, scale = parse_cart()
    a = [Fr(c) for c in cand['coefficients']]
    W = [a[k]*scale[k] for k in range(42)]
    Lw = lcm_den(W)
    LW = [Lw*w for w in W]
    assert all(x.denominator == 1 for x in LW)
    DR = to_list(P_R['D'])
    nRh = to_list({(e[0] - 1,) + e[1:]: q for e, q in P_R['nR'].items()})
    nZR = to_list(P_R['nZ'])
    # substitution checks
    assert l_substR(DR, R0) == L_u['D']
    assert l_substR(l_mulMono((Fr(1), 1, 0, 0, 0), nRh), R0) == L_u['nR']
    assert l_substR(nZR, R0) == L_u['nZ']
    ND, NR, NZ = lcm_den(t[0] for t in DR), lcm_den(t[0] for t in nRh), lcm_den(t[0] for t in nZR)

    def d(i, f):       # Lean: nz (d i f) (zero coefficients dropped)
        return [t for m in f for t in cart_d(m, i) if t[0] != 0]

    def gpart(fk):
        out = []
        for k in range(42):
            if LW[k] != 0:
                out += c_scale(LW[k].numerator, fk(k))
        return out
    Gphi = c_mulMono((1, 0, 0, 0, 3, 0), [(Lw, 0, 0, 0, 0, 0)] + gpart(
        lambda k: c_mulMono((1, 1, 0, 0, 0, 0), d(1, P[k])) + c_mulMono((-1, 0, 1, 0, 0, 0), d(0, P[k]))))
    GRh = c_mulMono((1, 0, 0, 0, 3, 0), gpart(
        lambda k: c_mulMono((1, 1, 0, 0, 0, 0), d(0, P[k])) + c_mulMono((1, 0, 1, 0, 0, 0), d(1, P[k]))))
    GZ = c_mulMono((1, 0, 0, 0, 4, 0), gpart(lambda k: d(2, P[k])))
    js = list(range(7))
    chkD = c_scale(Lw, c_convAll(ND, DR)) + c_scale(-ND, Gphi)
    chkR = c_scale(Lw, c_convAll(NR, nRh)) + c_scale(-NR, GRh)
    chkZ = c_scale(Lw, c_convAll(NZ, nZR)) + c_scale(-NZ, GZ)
    for nm, chk in (('D', chkD), ('nR', chkR), ('nZ', chkZ)):
        assert c_sliceCheck(js, chk), nm
        print(f'  identification {nm}: {len(chk)} Cartesian monomials, normal form empty')
    # rejected (Lean `ident_nZ_bad`): dropping the first term of n_z,R fails
    bad = c_scale(Lw, c_convAll(NZ, nZR[1:])) + c_scale(-NZ, GZ)
    assert not c_sliceCheck(js, bad)
    return dict(DR=DR, nRh=nRh, nZR=nZR, ND=ND, NR=NR, NZ=NZ, Lw=Lw)


# ----------------------------------------------------------------------------------------------
# Lean emission

def lean_q(q):
    if q.denominator == 1:
        return f'mkRat ({q.numerator}) 1'
    return f'mkRat ({q.numerator}) {q.denominator}'


def lean_sp(name, doc, L):
    items = []
    for t in L:
        one = f'    ⟨{lean_q(t[0])}, {t[1]}, {t[2]}, {t[3]}, {t[4]}⟩'
        if len(one) <= 98:
            items.append(one)
        else:
            q = t[0]
            items.append(f'    ⟨mkRat ({q.numerator})\n      {q.denominator}, {t[1]}, {t[2]}, {t[3]}, {t[4]}⟩')
    body = ',\n'.join(items)
    return f'/-- {doc}. -/\ndef {name} : SP := [\n{body}]\n'


DOCS = dict(
    D='`D = R⁶(1 + ∂_φV) = R⁷B_φ` in monomial form in `u = R − R₀, z, c = cos 2φ,\ns = sin 2φ`',
    nR='`n_R = R⁸ ∂_R V = R⁸ B_R` in monomial form',
    nZ='`n_z = R⁸ ∂_z V = R⁸ B_z` in monomial form',
    Pa='`P_a = R⁸ ∂_z W − z R⁶` (numerator of the `dR`-coefficient `P_a/R⁷` of the flux\nprimitive)',
    Pb='`P_b = −R⁸ ∂_R W` (numerator of the `dz`-coefficient `P_b/R⁷` of the flux\nprimitive)',
    Pc='`P_c = −c₀R²/2` (the `dφ`-coefficient of the flux primitive;\n`c₀` the coefficient of `z` in `V`)',
)


def obstruction_data(L, c0):
    """nZ(u = 0, z = 0) = K + phiS Q with K = c0 R0^8 and Q angle-only (the phi-antiderivative of
    the oscillating part, degree by degree: Re/Im (c + i s)^k -> Im/(2k), -Re/(2k))."""
    nz0 = {key(t)[2:]: t[0] for t in L['nZ'] if t[1] == 0 and t[2] == 0}
    K = nz0.pop((0, 0))
    assert K == c0*R0**8
    Q = {}
    for k in range(1, 4):
        hk = {e: q for e, q in nz0.items() if sum(e) == k}
        re, im = harm(k)
        alpha = hk.get((k, 0), Fr(0))
        beta = hk.get((k - 1, 1), Fr(0))/k
        recon = padd(pscale({e[2:]: q for e, q in re.items()}, alpha),
                     pscale({e[2:]: q for e, q in im.items()}, beta))
        assert recon == hk, k
        Q = padd(Q, pscale(im, alpha/(2*k)), pscale(re, -beta/(2*k)))
    assert all(sum(e) in (1, 2, 3) for e in nz0)
    Ql = to_list(Q)
    # the Lean check: merge (atZero nZ) (scale (-1) (merge [K] (phiS Q))) = []
    at0 = [t for t in L['nZ'] if t[1] == 0 and t[2] == 0]
    chk = l_merge(at0, l_scale(Fr(-1), l_merge([(K, 0, 0, 0, 0)], l_phi(Ql))))
    assert chk == [], chk
    return K, Ql


def emit_data(L, c0, out, ID):
    hdr = f'''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamPoly

/-!
# The Dommaschk QA target in flow form: polynomial data (generated file)

**Generated** by `scripts/dommaschk_kam/emit_flowfield.py` from
`scripts/dommaschk_qa/results/20261031T092522Z/candidate.json` (do not edit by hand).

Sparse polynomials (`DkPoly.SP`, exact rational coefficients) in the variables
`(u, z, c, s)`, `u = R − R₀` with `R₀ = {R0.numerator}/{R0.denominator}`, `c = cos 2φ`, `s = sin 2φ`, of the
flow form of `B = ∇(φ + V)` (`Design/DommaschkQA2R`, `field candidate`) with density exponent
`7` (`w = D/R⁷ = R B^φ`). The harmonics `cos 2kφ`, `sin 2kφ` are written as the homogeneous
harmonic polynomials `Re`, `Im (c + i s)^k`. Terms are sorted by exponent `(u, z, c, s)`
(lexicographic), which the merge-based checker of `DommaschkKamPoly` relies on for completeness
(not for soundness).

The generator validates in exact arithmetic that these satisfy the divergence-free identity and the
flux identities (with the `dφ`-component `P_c`), and that `D = R⁷B_φ`, `n_R = R⁸B_R`,
`n_z = R⁸B_z` for `B = DommaschkQA2R.field candidate` exactly at rational points.
Term counts: `D` {len(L['D'])}, `n_R` {len(L['nR'])}, `n_z` {len(L['nZ'])}, `P_a` {len(L['Pa'])}, `P_b` {len(L['Pb'])}, `P_c` {len(L['Pc'])}.
-/

@[expose] public section

namespace PlasmaLean.Design.DommaschkKam

open DkPoly

/-- The radial centre `R₀ = {R0.numerator}/{R0.denominator}` of the variable `u = R − R₀`. -/
def R0q : ℚ := {R0.numerator}/{R0.denominator}

/-- The coefficient `c₀` of the axisymmetric potential `z` in `V` (`B_z` has `φ`-mean `c₀`). -/
def c0q : ℚ := {lean_q(c0)}

'''
    K, Ql = obstruction_data(L, c0)
    body = ''
    for k, nm in (('D', 'dD'), ('nR', 'dnR'), ('nZ', 'dnZ'), ('Pa', 'dPa'), ('Pb', 'dPb'),
                  ('Pc', 'dPc')):
        body += lean_sp(nm, DOCS[k], L[k]) + '\n'
    body += lean_sp('dQ', 'The angle-only `Q` with `n_z(u = 0, z = 0) = c₀R₀⁸ + ∂_φQ` (the\nobstruction ' +
                    'to a flux primitive without `dφ`-component)', Ql) + '\n'
    body += f'/-- The `φ`-mean `c₀R₀⁸` of `n_z` at `u = z = 0`. -/\ndef Kq : ℚ := {lean_q(K)}\n\n'
    body += '/-! ## R-form data for the identification with `field candidate` (`DommaschkKamIdent`) -/\n\n'
    body += lean_sp('dDR', '`D` in the variables `(R, z, c, s)` (slot `0` is `R`; even powers)', ID['DR']) + '\n'
    body += lean_sp('dnRh', '`n_R / R` in the variables `(R, z, c, s)` (even powers of `R`)', ID['nRh']) + '\n'
    body += lean_sp('dnZR', '`n_z` in the variables `(R, z, c, s)` (even powers of `R`)', ID['nZR']) + '\n'
    body += f'/-- Common denominator of `dDR`. -/\ndef NDn : ℕ := {ID["ND"]}\n\n'
    body += f'/-- Common denominator of `dnRh`. -/\ndef NRn : ℕ := {ID["NR"]}\n\n'
    body += f'/-- Common denominator of `dnZR`. -/\ndef NZn : ℕ := {ID["NZ"]}\n\n'
    body += (f'/-- Common denominator of the weights `a_k · scale k` of `field candidate`. -/\n'
             f'def Lw : ℕ := {ID["Lw"]}\n\n')
    body += 'end PlasmaLean.Design.DommaschkKam\n'
    open(out, 'w').write(hdr + body)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--no-write', action='store_true')
    args = ap.parse_args()
    cand, V = load()
    P_R, c0 = build(V)
    # identities in R-form (independent of R0)
    for k, v in identities(P_R, mono(a=1)).items():
        assert v == {}, (k, len(v))
    # obstruction: phi-mean of n_z
    mean_nz = {e: q for e, q in P_R['nZ'].items() if e[2] == 0 and e[3] == 0}
    assert mean_nz == {(8, 0, 0, 0): c0} and c0 != 0, mean_nz
    print('identities hold in R-form; phi-mean of n_z =', c0, '* R^8 (nonzero: P_c needed)')
    crosscheck_cart(P_R, cand)
    print('agrees exactly with DommaschkQA2R.field candidate (R^7 B_phi, R^8 B_R, R^8 B_z) at rational points')
    P_u = {k: subst_R(v, R0) for k, v in P_R.items()}
    Ru = padd(mono(q=R0), mono(a=1))
    for k, v in identities(P_u, Ru).items():
        assert v == {}, (k, len(v))
    L = {k: to_list(v) for k, v in P_u.items()}
    LI = l_identities(L, R0)
    for k, v in LI.items():
        assert v == [], (k, len(v))
    for k, v in L.items():
        assert is_sorted(v)
    print('identities hold in u-form (R0 = %s), and in the Lean-mirror checker' % R0)
    ID = ident_checks(P_R, L, cand, R0)
    print('identification checks pass:', {k: ID[k] for k in ('ND', 'NR', 'NZ', 'Lw')})
    print('term counts:', {k: len(v) for k, v in L.items()})
    print('max u/z degree:', {k: (max(t[1] for t in v), max(t[2] for t in v)) for k, v in L.items()})
    print('max denominators bits:', {k: max(t[0].denominator.bit_length() for t in v)
                                     for k, v in L.items()})
    if not args.no_write:
        emit_data(L, c0, os.path.join(REPO, 'PlasmaLean', 'Design',
                                       'DommaschkKamFieldData.lean'), ID)
        print('wrote DommaschkKamFieldData.lean')
    return P_R, P_u, L, c0


if __name__ == '__main__':
    main()
