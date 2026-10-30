"""UNTRUSTED numerics (Q-16, N-31).  Exact Dommaschk-potential basis for vacuum stellarator fields.

Cylindrical (R, phi, z), units R0 = 1 and B0 R0 = 1.  The field is

    B = grad Phi,   Phi = phi + sum_k a_k V_k(R, phi, z),

and every V_k is harmonic, so div B = 0 and curl B = 0 hold identically (vacuum, J = 0, no net
toroidal current: the covariant toroidal component integrates to G = 1 on every toroidal loop).

Dommaschk potentials (W. Dommaschk, Comput. Phys. Commun. 40 (1986) 203; structure as in that paper,
normalisation reconstructed here and checked symbolically by `selftest`).  For m >= 0, l >= 0:

    D_{m,l}(R, z) = sum_{k=0}^{floor(l/2)} z^(l-2k)/(l-2k)!  C^D_{m,k}(R),
    N_{m,l}(R, z) = same with C^N_{m,k},

with L_m = d^2/dR^2 + (1/R) d/dR - m^2/R^2 and

    L_m C_{m,0} = 0,   L_m C_{m,k} = -C_{m,k-1}  (k >= 1)       (=> Laplacian of cos/sin(m phi) D = 0)
    C^D_{m,0}(1) = 1, C^D_{m,0}'(1) = 0;   C^N_{m,0}(1) = 0, C^N_{m,0}'(1) = 1;
    C_{m,k}(1) = C_{m,k}'(1) = 0 for k >= 1.

So C^D_{m,0} = (R^m + R^-m)/2, C^N_{m,0} = (R^m - R^-m)/(2m) (m > 0), C^D_{0,0} = 1, C^N_{0,0} = ln R,
and every C_{m,k} is an exact rational combination of R^p (ln R)^q.  Each basis element is
cos(m phi) or sin(m phi) times D_{m,l} or N_{m,l}; the field has NFP periods (m in NFP*Z) and
stellarator symmetry Phi(R, -phi, -z) = -Phi(R, phi, z), which keeps

    sin(m phi) x (l even)   and   cos(m phi) x (l odd).

Basis order: m = NFP*i with 0 <= i <= nmax and 0 <= l <= lmax (the constant m = l = 0 excluded).

A basis element is stored as a list of exact terms (c, p, q, j): c * R^p (ln R)^q z^j, with its trig
factor ('cos' | 'sin', m).  Everything here is exact (fractions.Fraction); floats appear only in
fieldeval.py.
"""
from fractions import Fraction as Fr
from math import factorial


# ---------------------------------------------------------------- radial functions R^p (ln R)^q
def _add(f, key, c):
    if c:
        f[key] = f.get(key, Fr(0)) + c
        if f[key] == 0:
            del f[key]


def L_op(f, m):
    """L_m applied to f = {(p, q): c}:  L_m R^p L^q = (p^2-m^2) R^{p-2} L^q + 2pq R^{p-2} L^{q-1}
    + q(q-1) R^{p-2} L^{q-2}."""
    out = {}
    for (p, q), c in f.items():
        _add(out, (p - 2, q), c*(p*p - m*m))
        if q >= 1:
            _add(out, (p - 2, q - 1), c*2*p*q)
        if q >= 2:
            _add(out, (p - 2, q - 2), c*q*(q - 1))
    return out


def L_inv(rhs, m):
    """A particular solution g of L_m g = rhs (exact, triangular in the log power)."""
    g = {}
    for s in sorted({p for p, _ in rhs}):
        p = s + 2
        Q = max(q for (pp, q) in rhs if pp == s)
        r = [rhs.get((s, q), Fr(0)) for q in range(Q + 1)]
        x = [Fr(0)]*(Q + 3)
        if p*p != m*m:
            for q in range(Q, -1, -1):
                x[q] = (r[q] - 2*p*(q + 1)*x[q + 1] - (q + 2)*(q + 1)*x[q + 2])/(p*p - m*m)
        elif p != 0:
            for q in range(Q, -1, -1):
                x[q + 1] = (r[q] - (q + 2)*(q + 1)*x[q + 2])/(2*p*(q + 1))
        else:  # p = m = 0
            for q in range(Q, -1, -1):
                x[q + 2] = r[q]/((q + 2)*(q + 1))
        for q, c in enumerate(x):
            _add(g, (p, q), c)
    assert L_op(g, m) == {k: v for k, v in rhs.items() if v}, "L_inv failed"
    return g


def _val1(f):
    return sum((c for (p, q), c in f.items() if q == 0), Fr(0))


def _der1(f):
    return sum((c*p for (p, q), c in f.items() if q == 0), Fr(0)) + \
        sum((c for (p, q), c in f.items() if q == 1), Fr(0))


def _homog(m):
    return ({(m, 0): Fr(1)}, {(-m, 0): Fr(1)}) if m > 0 else ({(0, 0): Fr(1)}, {(0, 1): Fr(1)})


def _normalise(f, m):
    """Add a homogeneous solution so that f(1) = f'(1) = 0."""
    v, d = _val1(f), _der1(f)
    h1, h2 = _homog(m)
    if m > 0:   # alpha R^m + beta R^-m: value alpha + beta, derivative m(alpha - beta)
        al = (-v - d/m)/2
        be = (-v + d/m)/2
    else:       # alpha + beta ln R: value alpha, derivative beta
        al, be = -v, -d
    out = dict(f)
    for (k, c) in h1.items():
        _add(out, k, al*c)
    for (k, c) in h2.items():
        _add(out, k, be*c)
    assert _val1(out) == 0 and _der1(out) == 0
    return out


def C_seq(m, kind, kmax):
    if m > 0:
        c0 = ({(m, 0): Fr(1, 2), (-m, 0): Fr(1, 2)} if kind == 'D'
              else {(m, 0): Fr(1, 2*m), (-m, 0): Fr(-1, 2*m)})
    else:
        c0 = {(0, 0): Fr(1)} if kind == 'D' else {(0, 1): Fr(1)}
    seq = [c0]
    for _ in range(kmax):
        seq.append(_normalise(L_inv({k: -v for k, v in seq[-1].items()}, m), m))
    return seq


def dommaschk_RZ(m, l, kind):
    """D_{m,l} or N_{m,l} as exact terms [(c, p, q, j)]  (c R^p (ln R)^q z^j)."""
    seq = C_seq(m, kind, l//2)
    terms = {}
    for k in range(l//2 + 1):
        j = l - 2*k
        for (p, q), c in seq[k].items():
            _add(terms, (p, q, j), c/factorial(j))
    return [(c, p, q, j) for (p, q, j), c in sorted(terms.items())]


def basis(nfp, nmax, lmax, symmetric=True):
    """Dommaschk basis, stellarator-symmetric by default (symmetric=False keeps both trig factors;
    used only to validate the pipeline on the rational field of Q-19).  Returns a list of dicts
    {name, kind, m, l, trig, terms}."""
    out = []
    for i in range(nmax + 1):
        m = nfp*i
        for l in range(lmax + 1):
            trigs = [('sin' if l % 2 == 0 else 'cos')] if symmetric else ['cos', 'sin']
            for trig in trigs:
                if m == 0 and (trig == 'sin' or l == 0):
                    continue
                for kind in ('D', 'N'):
                    out.append(dict(name=f"{trig}({m}phi)*{kind}_{m},{l}", kind=kind, m=m, l=l,
                                    trig=trig, terms=dommaschk_RZ(m, l, kind)))
    return out


def term_str(c, p, q, j):
    s = f"({c})"
    if p:
        s += f"*R**({p})"
    if q:
        s += f"*log(R)**{q}"
    if j:
        s += f"*z**{j}"
    return s


def potential_str(b, coeffs):
    """Phi = phi + sum a_k V_k as an explicit sympy-parsable string (exact rationals)."""
    parts = ["phi"]
    for bk, a in zip(b, coeffs):
        if a == 0:
            continue
        inner = " + ".join(term_str(*t) for t in bk['terms'])
        parts.append(f"({a})*{bk['trig']}({bk['m']}*phi)*({inner})")
    return " + ".join(parts)


def selftest(nfp=2, nmax=2, lmax=5):
    """Symbolic check: every basis element is harmonic and stellarator symmetric; normalisation."""
    import sympy as sp
    R = sp.symbols('R', positive=True)
    ph, z = sp.symbols('phi z', real=True)
    b = basis(nfp, nmax, lmax)
    for bk in b:
        rz = sum(sp.Rational(c.numerator, c.denominator)*R**p*sp.log(R)**q*z**j
                 for c, p, q, j in bk['terms'])
        V = (sp.cos if bk['trig'] == 'cos' else sp.sin)(bk['m']*ph)*rz
        lap = sp.diff(R*sp.diff(V, R), R)/R + sp.diff(V, ph, 2)/R**2 + sp.diff(V, z, 2)
        assert sp.simplify(sp.expand(lap)) == 0, bk['name']
        assert sp.simplify(V.subs({ph: -ph, z: -z}, simultaneous=True) + V) == 0, bk['name']
        # normalisation on R = 1: D(1, z) = z^l/l!, dD/dR(1, z) = 0 (and swapped for N)
        v1 = sp.simplify(rz.subs(R, 1)); d1 = sp.simplify(sp.diff(rz, R).subs(R, 1))
        lead = z**bk['l']/sp.factorial(bk['l'])
        assert sp.simplify(v1 - (lead if bk['kind'] == 'D' else 0)) == 0, bk['name']
        assert sp.simplify(d1 - (0 if bk['kind'] == 'D' else lead)) == 0, bk['name']
    return len(b)


if __name__ == '__main__':
    n = selftest()
    print(f"selftest: {n} basis potentials harmonic, stellarator-symmetric, normalised (exact)")
    for bk in basis(2, 1, 2):
        print(bk['name'], '=', ' + '.join(term_str(*t) for t in bk['terms']))
