"""Exact algebraic checks for the published Dommaschk seed and null-polynomial family.

This checks field identities over Q(i). It does not rebuild the project's Lean KAM certificate.
"""
from pathlib import Path
import hashlib
import json
import re
import sympy as s

HERE = Path(__file__).resolve().parent
SOURCE_COMMIT = "6312f1cc9c30b32798ad7b7540766152ef03e76f"
u, v, z, lam = s.symbols("u v z lam")
candidate_raw = (HERE / "candidate.json").read_bytes()
lean_raw = (HERE / "DommaschkQA2RData.lean").read_bytes()

def git_blob_hash(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()

assert git_blob_hash(candidate_raw) == "1e70104e57660e4605439f12d6e06a9fea76d48a"
assert git_blob_hash(lean_raw) == "dbca1daa8ddbf4e1405c55395f4842ece396f2c8"
data = json.loads(candidate_raw)
terms = []
for b, aq in zip(data["basis"], data["coefficients"]):
    a = s.Rational(aq)
    if not a:
        continue
    m = b["m"]
    for cq, p, log_power, j in b["terms"]:
        assert log_power == 0, (b["name"], p, log_power, j)
        assert (p + m) % 2 == (p - m) % 2 == 0
        plus = u ** ((p + m) // 2) * v ** ((p - m) // 2)
        minus = u ** ((p - m) // 2) * v ** ((p + m) // 2)
        trig_radial = (plus + minus) / 2 if b["trig"] == "cos" else (plus - minus) / (2 * s.I)
        terms.append(a * s.Rational(cq) * z**j * trig_radial)
F = s.expand(sum(terms))

# Independently identify the candidate with the Cartesian rational potential in the
# pinned Lean source. Mono.eval there is c*x^a*y^b*z^j*(x^2+y^2)^r*log(x^2+y^2)^q.
lean_text = lean_raw.decode()
def rational_vector(name):
    body = re.search(r"def " + name + r" : Fin 42 → ℚ :=\s*!\[(.*?)\]", lean_text, re.S)[1]
    values = [s.Rational(t.replace(" ", "").replace("\n", "")) for t in body.split(",")]
    assert len(values) == 42
    return values

lean_coeffs, lean_scales = rational_vector("candidate"), rational_vector("scale")
assert lean_coeffs == [s.Rational(a) for a in data["coefficients"]]
lean_polys = dict((int(k), body) for k, body in re.findall(
    r"def P(\d+) : CylPoly :=\s*\[(.*?)\]", lean_text, re.S))
assert len(lean_polys) == 42
x_cart, y_cart = (u + v) / 2, (u - v) / (2 * s.I)
lean_terms = []
for k, (a, scale) in enumerate(zip(lean_coeffs, lean_scales)):
    if not a:
        continue
    for tup in re.findall(r"⟨([^⟩]+)⟩", lean_polys[k]):
        c, p, q, j, r, log_power = [int(t.strip().strip("()")) for t in tup.split(",")]
        assert log_power == 0
        lean_terms.append(a * scale * c * x_cart**p * y_cart**q * z**j * (u*v)**r)
assert s.expand(sum(lean_terms) - F) == 0

def lap(f):
    return s.expand(4 * s.diff(f, u, v) + s.diff(f, z, 2))

def star(f):
    # Conjugate coefficients, exchange u and v, leave z fixed.
    return s.conjugate(f).subs({s.conjugate(u): v, s.conjugate(v): u, s.conjugate(z): z})

assert lap(F) == 0
assert s.expand(star(F) - F) == 0
assert s.expand(F.subs({u: -u, v: -v}, simultaneous=True) - F) == 0
assert s.expand(F.subs({u: v, v: u, z: -z}, simultaneous=True) + F) == 0

Q = u + 2 * lam * z - lam**2 * v
for n in range(11):
    assert lap(Q**n) == 0
    cs = s.Poly(s.expand(Q**n), lam).all_coeffs()
    assert len(cs) == 2 * n + 1 and all(c != 0 for c in cs)
for p in range(-4, 5):
    for q in range(-4, 5):
        if p < 0 and q < 0:
            continue
        nmax = min(t for t in (p, q) if t >= 0)
        E = sum((-4)**j * s.ff(p, j) * s.ff(q, j) * u**(p-j) * v**(q-j) * z**(2*j)
                / s.factorial(2*j) for j in range(nmax + 1))
        O = sum((-4)**j * s.ff(p, j) * s.ff(q, j) * u**(p-j) * v**(q-j) * z**(2*j+1)
                / s.factorial(2*j+1) for j in range(nmax + 1))
        assert lap(E) == lap(O) == 0

out = []
for term in s.Add.make_args(F):
    powers = term.as_powers_dict()
    p, q, j = [int(powers.get(t, 0)) for t in (u, v, z)]
    coefficient = s.simplify(term / (u**p * v**q * z**j))
    out.append({"u": p, "v": q, "z": j,
                "real": str(s.re(coefficient)), "imag": str(s.im(coefficient))})
out.sort(key=lambda t: (t["u"], t["v"], t["z"]))
(HERE / "dommaschk_complex_laurent.json").write_text(json.dumps({
    "definition": "F=sum((real+i*imag)*u^u*v^v*z^z); B^flat=(du/u-dv/v)/(2i)+dF",
    "source": "candidate.json, exact rational coefficients only",
    "source_commit": SOURCE_COMMIT,
    "source_reported_hash": data["sha256"],
    "laplacian": "4*d_u*d_v+d_z^2",
    "reality": "F(u,v,z)=conjugate(F(conjugate(v),conjugate(u),conjugate(z)))",
    "terms": out
}, indent=2) + "\n")
print(json.dumps({"active_basis_coefficients": sum(s.Rational(a) != 0 for a in data["coefficients"]),
                  "laurent_monomials": len(out), "seed_harmonic": True, "seed_real": True,
                  "matches_pinned_Lean_rational_potential": True,
                  "source_commit": SOURCE_COMMIT,
                  "two_field_periods": True, "stellarator_symmetry": True,
                  "null_powers_checked_through": 10,
                  "laurent_Cauchy_basis_exponents_checked": [-4, 4],
                  "Lean_certificate_rebuilt": False}, indent=2))
