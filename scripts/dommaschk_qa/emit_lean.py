"""Emit the exact Dommaschk QA candidate as Lean `CylPoly` data (certification step 1, N-31).

Usage:
    /tmp/dqa-venv/bin/python -I scripts/dommaschk_qa/emit_lean.py \
        scripts/dommaschk_qa/results/20261031T044845Z/candidate.json \
        PlasmaLean/Design/DommaschkQA3Data.lean [NAMESPACE]
NAMESPACE (default DommaschkQA3) names `PlasmaLean.Design.NAMESPACE`; the basis size and the
parameters are read from the candidate. An optional fifth argument K moves the kernel checks to
K modules `<out>Check0.lean` … (keeps each Lean process within the memory budget); a sixth
argument `slice` checks harmonicity slice by slice in the z-degree (`sliceCheck`, less kernel memory).

Each basis potential V_k = trig(m phi) * sum c R^p (ln R)^q z^j is rewritten in Cartesian
coordinates (r2 = x^2 + y^2) as a sum of monomials  c' x^a y^b z^j r2^s (log r2)^q  using
R^m cos(m phi) = Re (x + i y)^m, R^m sin(m phi) = Im (x + i y)^m, R^p = R^m r2^((p - m)/2),
ln R = (1/2) log r2.  The rational monomial coefficients are cleared by their lcm D_k, so the Lean
data are integer polynomials P_k with V_k = P_k / D_k (`scale k = 1 / D_k`).

Before writing anything the script checks, exactly:
  1. V_k(cylindrical) == P_k / D_k (Cartesian) as sympy expressions (after substituting
     x = R cos phi, y = R sin phi, and also at random rational points to 60 digits);
  2. the Cartesian Laplacian of P_k simplifies to 0 (sympy);
  3. a Python mirror of the Lean normal form `nf (lap P_k)` is empty (the Lean check
     `basis_harmonic` must then succeed);
  4. the coefficient vector is exact (Fractions from the candidate strings).
It also prints the Cartesian field B = grad(phi + sum a_k V_k) at a sample point, evaluated from the
emitted data and by fieldeval.Tables, for the sanity comment in DommaschkQA3.lean.
"""
import json
import os
import sys
from fractions import Fraction as Fr
from math import comb, lcm, gcd

HERE = os.path.dirname(os.path.abspath(__file__))


# ------------------------------------------------------------------ Cartesian monomials
def cart_terms(bk):
    """Rational monomials {(a, b, j, s, q): c} of V_k."""
    m, trig = bk['m'], bk['trig']
    out = {}
    for cs, p, q, j in bk['terms']:
        c = Fr(cs)
        assert (p - m) % 2 == 0 and q in (0, 1)
        s = (p - m) // 2
        c *= Fr(1, 2) ** q                     # ln R = (1/2) log r2
        if m == 0:
            assert trig == 'cos'
            parts = [(0, 0, Fr(1))]
        else:
            parts = []
            for k in range(m + 1):             # (x + i y)^m = sum C(m,k) x^(m-k) (i y)^k
                if trig == 'cos' and k % 2 == 0:
                    parts.append((m - k, k, Fr(comb(m, k) * (-1) ** (k // 2))))
                if trig == 'sin' and k % 2 == 1:
                    parts.append((m - k, k, Fr(comb(m, k) * (-1) ** ((k - 1) // 2))))
        for a, b, w in parts:
            key = (a, b, j, s, q)
            out[key] = out.get(key, 0) + c * w
    return {k: v for k, v in out.items() if v != 0}


def integerise(terms):
    D = 1
    for v in terms.values():
        D = lcm(D, v.denominator)
    P = {k: int(v * D) for k, v in terms.items()}
    assert all(Fr(P[k], D) == terms[k] for k in terms)
    return P, D


# ------------------------------------------------------------------ Python mirror of the Lean nf
def d_mono(i, mono):
    c, a, b, j, s, q = mono
    if i == 0:
        return [(c * a, max(a - 1, 0), b, j, s, q), (c * 2 * s, a + 1, b, j, s - 1, q),
                (c * 2 * q, a + 1, b, j, s - 1, max(q - 1, 0))]
    if i == 1:
        return [(c * b, a, max(b - 1, 0), j, s, q), (c * 2 * s, a, b + 1, j, s - 1, q),
                (c * 2 * q, a, b + 1, j, s - 1, max(q - 1, 0))]
    return [(c * j, a, b, max(j - 1, 0), s, q)]


def d(i, f):
    return [m for mono in f for m in d_mono(i, mono)]


def lap(f):
    return d(0, d(0, f)) + d(1, d(1, f)) + d(2, d(2, f))


def red_y(n, mono):
    c, a, b, j, s, q = mono
    if n == 0 or b < 2:
        return [mono]
    return red_y(n - 1, (c, a, b - 2, j, s + 1, q)) + red_y(n - 1, (-c, a + 2, b - 2, j, s, q))


def nf(f):
    acc = {}
    for mono in f:
        for c, a, b, j, s, q in red_y(mono[2], mono):
            acc[(a, b, j, s, q)] = acc.get((a, b, j, s, q), 0) + c
    return [(c,) + k for k, c in acc.items() if c != 0]


# ------------------------------------------------------------------ sympy checks
def sympy_checks(b, polys):
    import sympy as sp
    x, y, z = sp.symbols('x y z', real=True)
    R = sp.symbols('R', positive=True)
    ph = sp.symbols('phi', real=True)
    r2 = x**2 + y**2
    exprs = []
    for bk, (P, D) in zip(b, polys):
        Pc = sum(c * x**a * y**bb * z**j * r2**s * sp.log(r2)**q
                 for (a, bb, j, s, q), c in P.items())
        exprs.append((Pc, D))
        # 2. Laplacian
        L = sp.diff(Pc, x, 2) + sp.diff(Pc, y, 2) + sp.diff(Pc, z, 2)
        assert sp.simplify(sp.together(sp.expand(L))) == 0, bk['name']
        # 1. agreement with the cylindrical potential
        rz = sum(sp.Rational(Fr(c).numerator, Fr(c).denominator) * R**p * sp.log(R)**q * z**j
                 for c, p, q, j in bk['terms'])
        V = (sp.cos if bk['trig'] == 'cos' else sp.sin)(bk['m'] * ph) * rz
        Vc = (Pc / D).subs({x: R * sp.cos(ph), y: R * sp.sin(ph)}, simultaneous=True)
        diff = sp.simplify(sp.expand_log(sp.expand_trig(sp.simplify(Vc - V)), force=True))
        assert diff == 0, (bk['name'], diff)
        for (Rv, pv, zv) in [(Fr(9, 10), Fr(3, 10), Fr(1, 7)), (Fr(13, 10), Fr(-2, 3), Fr(-1, 5))]:
            vals = {R: sp.Rational(Rv.numerator, Rv.denominator),
                    ph: sp.Rational(pv.numerator, pv.denominator),
                    z: sp.Rational(zv.numerator, zv.denominator)}
            e = sp.N((Vc - V).subs(vals), 60)
            assert abs(e) < sp.Float('1e-50'), (bk['name'], e)
    return exprs, (x, y, z)


def sample_field(b, exprs, xyz, a, pt):
    """Cartesian B at pt from the emitted data, and from fieldeval.Tables."""
    import sympy as sp
    import numpy as np
    x, y, z = xyz
    vals = {x: sp.Rational(pt[0]), y: sp.Rational(pt[1]), z: sp.Rational(pt[2])}
    r2v = vals[x]**2 + vals[y]**2
    B = [-vals[y] / r2v, vals[x] / r2v, sp.Integer(0)]
    for ak, (Pc, D) in zip(a, exprs):
        for i, v in enumerate((x, y, z)):
            B[i] += sp.Rational(ak.numerator, ak.denominator) / D * sp.diff(Pc, v).subs(vals)
    Bl = [float(sp.N(t, 30)) for t in B]
    sys.path.insert(0, HERE)
    import fieldeval as fe
    bf = [dict(bk, terms=[(Fr(c), p, q, j) for c, p, q, j in bk["terms"]]) for bk in b]
    tab = fe.Tables(bf, 3)
    W = tab.weights(np.array([[float(t) for t in a]]))
    Rv = float(sp.sqrt(r2v)); phv = float(sp.atan2(vals[y], vals[x]))
    BR, BP, BZ = tab.eval(W, np.array([[Rv]]), phv, np.array([[float(vals[z])]]))
    BR, BP, BZ = float(BR[0, 0]), float(BP[0, 0]), float(BZ[0, 0])
    Bf = [BR * np.cos(phv) - BP * np.sin(phv), BR * np.sin(phv) + BP * np.cos(phv), BZ]
    return Bl, Bf


# ------------------------------------------------------------------ Lean output
def lean_int(c):
    return f"({c})" if c < 0 else str(c)


def emit(cand_path, b, polys, a, out, name='DommaschkQA3', params='NFP 3, nmax 2, lmax 4', nsplit=0, slices=False):
    n = len(b)
    rel = os.path.relpath(cand_path, os.path.join(HERE, '..', '..'))
    L = []
    L.append("""/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.CylAlgebra
public import PlasmaLean.Certificates.KernelFact

/-!
# Data of the Dommaschk QA candidate (""" + params + """): generated file

**Generated** by `scripts/dommaschk_qa/emit_lean.py` from
`""" + rel + """` (do not edit by hand).

The """ + str(n) + """ Dommaschk basis potentials `V_k = trig(m φ) Σ c R^p (ln R)^q z^j` (`basis.py`), rewritten in
Cartesian coordinates as integer cylindrical potentials `P k : CylPoly` with
`V_k = scale k · eval (P k)` (`scale k = 1 / D_k`, `D_k` the lcm of the rational monomial
coefficients), and the exact fitted coefficient vector `candidate`. The generator checks
in sympy, before writing, that `P k / D_k` equals the cylindrical potential and that its
Laplacian vanishes, and that a Python mirror of `nf (lap (P k))` is empty. In Lean,
`nf_lap_P{k}` re-checks the harmonicity of each `P k` by kernel evaluation of the normal form
(`kernel_fact`: the proof is `Eq.refl`, checked only by the kernel), and `parity_P{k}` checks that
each `P k` is odd under the stellarator symmetry `(x, y, z) ↦ (x, −y, −z)`.
-/

public section
namespace PlasmaLean.Design.""" + name + """
open PlasmaLean.Fields.CylAlgebra
""")
    for k, (bk, (P, D)) in enumerate(zip(b, polys)):
        items = [f"⟨{lean_int(c)}, {a_}, {bb}, {j}, {lean_int(s)}, {q}⟩"
                 for (a_, bb, j, s, q), c in sorted(P.items())]
        lines, cur = [], ""
        for it in items:
            if cur and len(cur) + len(it) + 2 > 92:
                lines.append(cur + ",")
                cur = it
            else:
                cur = it if not cur else cur + ", " + it
        lines.append(cur)
        monos = "\n    ".join(lines)
        L.append(f"/-- Basis potential {k}: `{bk['name']}` times `{D}` "
                 f"({len(P)} monomials). -/")
        L.append(f"@[expose] def P{k} : CylPoly :=")
        L.append(f"  [{monos}]")
        L.append("")
    L.append(f"/-- The {n} basis potentials (integer forms `D_k V_k`). -/")
    L.append(f"@[expose] def P : Fin {n} → CylPoly :=")
    L.append("  ![" + ",\n    ".join(", ".join(f"P{k}" for k in range(i, min(i + 12, len(b))))
                                      for i in range(0, len(b), 12)) + "]")
    L.append("")
    checks = []
    for k, bk in enumerate(b):
        C = []
        lp = lap([(c,) + key for key, c in polys[k][0].items()])
        if slices:   # z-degree slices: each normal form is smaller (kernel memory)
            js = sorted({m[3] for m in lp})
            C.append(f"/-- Harmonicity check for `P{k}` (`{bk['name']}`): the formal Laplacian\n"
                     f"normalises to zero slice by slice in the `z`-degree (kernel evaluation). -/")
            C.append(f"theorem slice_P{k} : sliceCheck {js} (lap P{k}) = true := by kernel_fact")
        else:
            if len(lp) > 700:   # the kernel evaluation of the largest normal forms recurses deeply
                C.append("set_option maxRecDepth 8000 in")
            C.append(f"/-- Harmonicity check for `P{k}` (`{bk['name']}`): the formal Laplacian\n"
                     f"normalises to zero (kernel evaluation). -/")
            C.append(f"theorem nf_lap_P{k} : nf (lap P{k}) = [] := by kernel_fact")
        C.append("")
        C.append(f"/-- Stellarator-symmetry check for `P{k}`: every monomial is odd under\n"
                 f"`(x, y, z) ↦ (x, −y, −z)`. -/")
        C.append(f"theorem parity_P{k} : parityCheck 1 P{k} = true := by kernel_fact")
        C.append("")
        checks.append(C)
    if not nsplit:
        for C in checks:
            L += C
    L.append("/-- `scale k = 1 / D_k`: `V_k = scale k · eval (P k)`. -/")
    L.append(f"@[expose] def scale : Fin {n} → ℚ :=")
    L.append("  ![" + ",\n    ".join(", ".join(f"1 / {D}" for _, D in polys[i:i + 8])
                                      for i in range(0, len(polys), 8)) + "]")
    L.append("")
    L.append("/-- The exact fitted coefficients `a_k` of the candidate (`candidate.json`). -/")
    L.append(f"@[expose] def candidate : Fin {n} → ℚ :=")
    L.append("  ![" + ",\n    ".join(f"{ak.numerator} / {ak.denominator}" for ak in a) + "]")
    L.append("")
    L.append(f"end PlasmaLean.Design.{name}")
    L.append("")
    with open(out, 'w') as fh:
        fh.write("\n".join(L))
    if nsplit:   # the kernel checks go to separate modules (memory: each module < 6 GB)
        mod = os.path.relpath(out, os.path.join(HERE, '..', '..'))[:-5].replace(os.sep, '.')
        per = -(-len(checks) // nsplit)
        for i in range(nsplit):
            part = checks[i*per:(i+1)*per]
            ks = range(i*per, i*per + len(part))
            H = ["/-", "Copyright (c) 2026 PlasmaLean contributors. All rights reserved.",
                 "Released under Apache 2.0 license as described in the file LICENSE.",
                 "Authors: PlasmaLean contributors", "-/", "module", "",
                 f"public import {mod}", "public import PlasmaLean.Certificates.KernelFact", "",
                 "/-!", f"# Kernel checks {ks.start}–{ks.stop - 1} of `{mod}` (generated file)", "",
                 "Harmonicity (`nf_lap_P*`) and stellarator parity (`parity_P*`) of the basis potentials,",
                 "by kernel evaluation (`kernel_fact`). Generated by `scripts/dommaschk_qa/emit_lean.py`;",
                 "split from the data module to keep each Lean process under the laptop memory budget.",
                 "-/", "", "public section", f"namespace PlasmaLean.Design.{name}",
                 "open PlasmaLean.Fields.CylAlgebra", ""]
            for C in part:
                H += C
            H += [f"end PlasmaLean.Design.{name}", ""]
            with open(out[:-5] + f"Check{i}.lean", 'w') as fh:
                fh.write("\n".join(H))


def main():
    cand_path, out = sys.argv[1], sys.argv[2]
    name = sys.argv[3] if len(sys.argv) > 3 else 'DommaschkQA3'
    nsplit = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    slices = len(sys.argv) > 5 and sys.argv[5] == 'slice'
    with open(cand_path) as fh:
        cand = json.load(fh)
    b = cand['basis']
    params = f"NFP {cand['nfp']}, nmax {cand['nmax']}, lmax {cand['lmax']}"
    a = [Fr(s) for s in cand['coefficients']]
    polys = [integerise(cart_terms(bk)) for bk in b]
    for bk, (P, D) in zip(b, polys):
        f = [(c,) + key for key, c in P.items()]
        assert nf(lap(f)) == [], bk['name']
        g = 0
        for c in P.values():
            g = gcd(g, c)
        print(f"{bk['name']:18s} D={D:6d} monomials={len(P):3d} lap terms={len(lap(f)):5d} "
              f"gcd={g}")
    exprs, xyz = sympy_checks(b, polys)
    print(f"sympy: all {len(b)} potentials match the cylindrical form and are harmonic")
    pt = ('21/20', '1/10', '1/50')
    Bl, Bf = sample_field(b, exprs, xyz, a, pt)
    print("B at", pt, "from emitted data:", Bl)
    print("B at", pt, "from fieldeval   :", Bf)
    assert max(abs(u - v) for u, v in zip(Bl, Bf)) < 1e-10
    emit(cand_path, b, polys, a, out, name, params, nsplit, slices)
    print("wrote", out)


if __name__ == '__main__':
    main()
