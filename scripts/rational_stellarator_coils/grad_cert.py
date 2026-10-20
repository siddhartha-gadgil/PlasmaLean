"""UNTRUSTED generator for PlasmaLean/Design/RationalStellaratorCoilsGrad.lean (data + checks).

For each partial derivative dP_i of the certified first integral P(s,z,C,S) (read from
RationalStellaratorConfinedData.lean), reduce S^2 -> 1 - C^2 to p0(s,z,C) + S p1(s,z,C), rescale
s = sigma/10, z = zeta/10, and search Taylor-shift cover plans (mirror of Cover.check) proving
|p_par| <= bound * 2^40 on the cube.  Emits the Lean data/check block to stdout-file.
Run from the repository root:  python scripts/rational_stellarator_coils/grad_cert.py out.lean
Requires the oracle helpers in scripts/rational_stellarator_oracle (dense.py, plan.py, pipeline.py).
"""
import sys, re, os
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'rational_stellarator_oracle'))
import dense
from plan import Searcher
from pipeline import pderiv, trim

src = open(os.path.join(HERE, '..', '..', 'PlasmaLean', 'Design',
                        'RationalStellaratorConfinedData.lean')).read()
m = re.search(r'def Pz : FPoly :=\s*fpoly% "([^"]*)"', src, re.S)
rows = [r.split() for r in m.group(1).replace('\n', ' ').split(';') if r.strip()]
P = {tuple(map(int, r[1:])): int(r[0]) for r in rows}
SC = 2**40

def degs(p): return max(e[0] for e in p), max(e[1] for e in p)

def reduceS(p):
    p0 = {}; p1 = {}
    for (j, k, a, b), c in p.items():
        q, r = b // 2, b % 2
        for i in range(q + 1):
            key = (j, k, a + 2 * i)
            tgt = p0 if r == 0 else p1
            tgt[key] = tgt.get(key, 0) + c * comb(q, i) * (-1)**i
    return {k: v for k, v in p0.items() if v}, {k: v for k, v in p1.items() if v}

def dense3(p, ds, dz):
    M = max(k[2] for k in p) + 1
    A = [[[0] * M for _ in range(dz + 1)] for _ in range(ds + 1)]
    for (j, k, mm), v in p.items(): A[j][k][mm] = v * 10**((ds - j) + (dz - k))
    return A

# (bound for p0, bound for p1, truncation budget fraction) per derivative (physical units)
CFG = {0: (0.29, 0.115, 0.0), 1: (0.22, 0.12, 0.0), 2: (0.0105, 0.001, 0.1), 3: (0.006, 0.001, 0.1)}

def d3_str(A):
    return " | ".join(" ; ".join(" ".join(str(x) for x in f) for f in B) for B in A)
def wrap(s, n=90):
    out = []; line = ''
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > n: out.append(line); line = tok
        else: line = (line + ' ' + tok) if line else tok
    out.append(line); return '\n'.join(out)
def plan_lit(s): return 'plan% "' + '\n'.join(s[i:i + 80] for i in range(0, len(s), 80)) + '"'

cert = []
for i in range(4):
    dp = pderiv(P, i); ds, dz = degs(dp)
    for par, q in enumerate(reduceS(dp)):
        c = int(CFG[i][par] * SC)
        if q:
            dm = max(k[2] for k in q)
            A = dense3(q, ds, dz)
            S = Searcher('abs', (1.0, 1.0, 1.0), rem_frac=CFG[i][2], maxdepth=30, dd=(ds, dz, dm))
            pl = S.search(A, [[[c * 10**(ds + dz)]]], 0, [1.0, 1.0, 1.0], 0)
            assert pl, (i, par)
            A = trim(A)
        else:
            dm, A, pl = 0, [], 'L'
        cert.append(dict(i=i, par=par, ds=ds, dz=dz, dm=dm, c=c, A=A, plan=pl))
        print(i, par, 'bound', c, 'plan length', len(pl), file=sys.stderr)

L = []
for x in cert:
    nm = f"gA{x['i']}{x['par']}"
    body = ('d3% "' + wrap(d3_str(x['A'])) + '"') if x['A'] else '[]'
    L.append(f"/-- Rescaled circle part `{x['par']}` of `∂{x['i']}P` (value `10^{x['ds']+x['dz']} q(σ/10, ζ/10, τ)`). -/\n@[expose] def {nm} : D3 :=\n  {body}\n")
for x in cert:
    nm = f"gA{x['i']}{x['par']}"; i, par, ds, dz = x['i'], x['par'], x['ds'], x['dz']
    L.append(f"""set_option maxRecDepth 100000 in
/-- The literal `{nm}` is the rescaled circle part (kernel check). -/
theorem {nm}_eq : (lenOK 0 {ds} (circD {par} (pderivZ Pz {i})) &&
    lenOK 1 {dz} (circD {par} (pderivZ Pz {i})) &&
    beq3 (scale0 10 {ds} (scale1 10 {dz} (circD {par} (pderivZ Pz {i})))) {nm}) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Cover check: `|{nm}| ≤ {x['c']} · 10^{ds + dz}` on the cube. -/
theorem {nm}_check : check true ({ds}, {dz}, {x['dm']}) [] (
    {plan_lit(x['plan'])})
    {nm} [[[{x['c']} * 10 ^ {ds + dz}]]] 0 = true := by
  decide +kernel
""")
open(sys.argv[1] if len(sys.argv) > 1 else 'grad_data.lean', 'w').write('\n'.join(L))
