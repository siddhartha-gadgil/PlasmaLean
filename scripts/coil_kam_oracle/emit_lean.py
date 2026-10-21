"""UNTRUSTED.  Emit the data of the coarse sampled coil-KAM certificate and predict every kernel
computation (exact Python mirror of the integer checkers of PlasmaLean/Design/CoilKam*.lean).

Mirrored definitions: isqrtF/sqrtBr (CoilKamArith), guess/facBr/compAP/segAP/sumSegAP/fieldAP
(CoilKamSeg), tget/stepErr/tableErr/twoAddBr (CoilKamArith), gidx/recAP/recLAP/torusAP
(CoilKamTorus), tubeOK/pointAP (CoilKamPoint).

Usage: python emit_lean.py N M  (torus /tmp/ckwork/coil_torus_N{N}_M{M}.npz)
Writes PlasmaLean/Design/CoilKamData.lean and /tmp/ckwork/predict.json.
"""
import json
import math
import os
import sys
import time

import numpy as np
from mpmath import mp, mpf, cos as mcos, sin as msin, pi as mpi, sqrt as msqrt

from coil import SEGS, ROOT

mp.dps = 80
P = 100
D0 = 2 ** 68
D = 2 ** 32 * D0
N1, L = 16, 32
Q = L // N1
WN = D // 5            # tube half-width w0 = wN/D <= 1/5
DN = D // 100          # displacement bound 1/100
LIP = 2_000_000


def cdivN(a, b):
    return (a + (b - 1)) // b


def isqrtF(fuel, n, g):
    for _ in range(fuel):
        nx = (g + n // g) // 2
        if nx < g:
            g = nx
        else:
            return g
    return g


def sqrtBr(g, n):
    A = isqrtF(300, n, g + 1)
    if A * A <= n < (A + 1) * (A + 1):
        return A, A + 1
    return 0, n + 1


def guess(Dv, n):
    return 8 * Dv if n < 64 * Dv * Dv else 4194304 * Dv


def facBr(Dv, Al, Ah, Bl, Bh, C, CC):
    if Al == 0 or Bl == 0:
        return None
    if C >= 0:
        return ((Al + Bl) * Dv ** 5 // (Ah * Bh * max(Ah * Bh + C, 0)),
                cdivN((Ah + Bh) * Dv ** 5, Al * Bl * max(Al * Bl + C, 0)))
    if CC == 0:
        return None
    return ((Al + Bl) * (Al * Bl + (-C)) * Dv ** 5 // (Ah * Bh * CC),
            cdivN((Ah + Bh) * (Ah * Bh + (-C)) * Dv ** 5, Al * Bl * CC))


def compAP(Dv, K, x, FL, FH):
    M = 4294967296 * Dv ** 3
    return (K * x * FL) // M, cdivN(abs(K * x) * max(FH - FL, 0), M) + 1


def segAP(Dv, K, p, q, y):
    a = tuple(p[i] - y[i] for i in range(3))
    b = tuple(q[i] - y[i] for i in range(3))
    na = sum(t * t for t in a)
    nb = sum(t * t for t in b)
    X = (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])
    A = sqrtBr(guess(Dv, na), na)
    B = sqrtBr(guess(Dv, nb), nb)
    C = sum(a[i] * b[i] for i in range(3))
    CC = sum(t * t for t in X)
    F = facBr(Dv, A[0], A[1], B[0], B[1], C, CC)
    if F is None:
        return None
    return tuple(compAP(Dv, K, X[i], F[0], F[1]) for i in range(3))


def allSegsD():
    Lm = 1000000 * D
    tf = [(2147483648, (0, 0, -Lm), (0, 0, Lm)), (2147483648, (0, 0, Lm), (Lm, 0, Lm)),
          (2147483648, (Lm, 0, Lm), (Lm, 0, -Lm)), (2147483648, (Lm, 0, -Lm), (0, 0, -Lm))]
    poly = [(k, tuple(D0 * t for t in p), tuple(D0 * t for t in q)) for k, p, q in SEGS]
    return tf + poly


SEGSD = allSegsD()


def fieldAP(Y):
    acc = [(0, 0), (0, 0), (0, 0)]
    for K, p, q in SEGSD:
        r = segAP(D, K, p, q, Y)
        if r is None:
            return None
        acc = [(acc[i][0] + r[i][0], acc[i][1] + r[i][1]) for i in range(3)]
    return acc


def apAdd(p, q):
    return p[0] + q[0], p[1] + q[1]


def apMul(p, q):
    return ((p[0] * q[0]) // D,
            cdivN(abs(p[0]) * q[1] + abs(q[0]) * p[1] + p[1] * q[1], D) + 1)


def apSmul(n, p):
    return n * p[0], abs(n) * p[1]


def apNeg(p):
    return -p[0], p[1]


def apSub(p, q):
    return p[0] - q[0], p[1] + q[1]


def apAbs(p):
    return abs(p[0]) + p[1]


def table():
    tbl = []
    for t in range(L):
        ang = 2 * mpi * t / L
        tbl.append((int(mp.nint(mcos(ang) * D)), int(mp.nint(msin(ang) * D))))
    return tbl


def stepErr(e1, w, w2, w1, e):
    return (e + cdivN((abs(w[0]) + abs(w[1])) * e1, D) +
            cdivN(abs(w[0] * w1[0] - w[1] * w1[1] - w2[0] * D) + abs(w[0] * w1[1] + w[1] * w1[0] - w2[1] * D), D))


def tableErr(e1, w1, ws, e):
    mx = e
    for i in range(len(ws) - 1):
        e = stepErr(e1, ws[i], ws[i + 1], w1, e)
        mx = max(mx, e)
    return mx


def twoAddBr(n):
    lo, hi = 0, 0
    for _ in range(n):
        lo, hi = sqrtBr(2 * D, (2 * D + lo) * D)[0], sqrtBr(2 * D, (2 * D + hi) * D)[1]
    return lo, hi


def base_errors(tbl):
    """eC, eS for base_exp_approx with L = 2^(n+3), n = 2."""
    n = 2
    lo3, hi3 = twoAddBr(n + 1)
    lo2, hi2 = twoAddBr(n)
    C, S = tbl[1]
    # |x/2 - C| <= eC for x in [lo3, hi3]  <=  max(|lo3/2 - C|, |hi3/2 - C|)
    eC = math.ceil(max(abs(mpf(lo3) / 2 - C), abs(mpf(hi3) / 2 - C)))
    sl = sqrtBr(2 * D, (2 * D - hi2) * D)[0]
    sh = sqrtBr(2 * D, (2 * D - lo2) * D)[1]
    eS = math.ceil(max(abs(mpf(sl) / 2 - S), abs(mpf(sh) / 2 - S)))
    return eC, eS, (lo3, hi3, lo2, hi2, sl, sh)


def iota_q():
    io = (75 + msqrt(5)) / 562
    Iq = int(mp.floor(io * D))
    assert 75 * D <= 562 * Iq
    assert (562 * Iq - 75 * D) ** 2 <= 5 * D * D <= (562 * (Iq + 1) - 75 * D) ** 2
    return Iq


def records(N, M):
    d = np.load(f'/tmp/ckwork/coil_torus_N{N}_M{M}.npz')
    H = [tuple(int(v) for v in km) for km in d['H']]
    recs = []
    # high-precision rounding of the double coefficients
    for (k, m), a, ap, b, bp in zip(H, d['a'], d['ap'], d['b'], d['bp']):
        R = lambda v: int(round(mpf(float(v)) * D))  # noqa: E731
        recs.append((k, m, R(a), R(ap), R(b), R(bp)))
    assert recs[0][0] == 0 and recs[0][1] == 0
    return recs


def gidx(k, m, j, l):
    return (k * Q * j + m * l) % L


def torusAP(Iq, tbl, E, recs, j, l):
    R = (0, 0); Z = (0, 0); LR = (0, 0); LZ = (0, 0)
    for (k, m, a, ap, b, bp) in reversed(recs):     # apSum folds from the right
        c, s = tbl[gidx(k, m, j, l)]
        cs = ((c, E), (s, E))
        R = apAdd(apAdd(apMul((a, 0), cs[0]), apMul((ap, 0), cs[1])), R)
        Z = apAdd(apAdd(apMul((b, 0), cs[0]), apMul((bp, 0), cs[1])), Z)
        lam = apAdd((m * D, 0), apSmul(k, (Iq, 1)))
        LR = apAdd(apMul(lam, apAdd(apMul((-a, 0), cs[1]), apMul((ap, 0), cs[0]))), LR)
        LZ = apAdd(apMul(lam, apAdd(apMul((-b, 0), cs[1]), apMul((bp, 0), cs[0]))), LZ)
    return R, Z, LR, LZ


def tubeOK(Y0, Y1, Y2):
    return WN < D and (D - WN) ** 2 <= Y0 ** 2 + Y1 ** 2 <= (D + WN) ** 2 and abs(Y2) <= WN


def pointAP(Iq, tbl, E, recs, j, l):
    R, Z, LR, LZ = torusAP(Iq, tbl, E, recs, j, l)
    c, s = tbl[l % L]
    cphi, sphi = (c, E), (s, E)
    Y0 = apMul(R, cphi)
    Y1 = apMul(R, sphi)
    eY = Y0[1] + Y1[1] + Z[1]
    if not (tubeOK(Y0[0], Y1[0], Z[0]) and eY <= DN):
        return None
    B = fieldAP((Y0[0], Y1[0], Z[0]))
    if B is None:
        return None
    B0, B1, B2 = [(B[i][0], B[i][1] + LIP * eY) for i in range(3)]
    Bphi = apAdd(apNeg(apMul(sphi, B0)), apMul(cphi, B1))
    BR = apAdd(apMul(cphi, B0), apMul(sphi, B1))
    return (apAbs(apSub(apMul(Bphi, LR), apMul(R, BR))),
            apAbs(apSub(apMul(Bphi, LZ), apMul(R, B2))))


def lean_int(v):
    return f"({v})" if v < 0 else str(v)


def emit(recs, tbl, Iq, E, e1, eC, eS, br, rows, path):
    lines = []
    lines.append("""/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.CoilKamResidual

/-!
# Data of the coarse sampled coil-KAM certificate (emitted)

Literal data produced by the untrusted oracle `scripts/coil_kam_oracle/emit_lean.py`
(refit `refit.py`, truncation `N = 8`, `M = 16`, scale `D = 2¹⁰⁰`); every use is checked by the
kernel in `Design/CoilKamCert*`:

* `ckRecs`: the 281 torus records `(k, m, a, a', b, b')` (`R = Σ (a cos + a' sin)/D`, etc.);
* `ckTbl`: the table of `D e^{2πit/32}` (Gaussian integers);
* `ckIq`: `⌊D ι_A⌋`; `ckE`, `ckE1`: the table and base errors (units `1/D`).
-/

@[expose] public section

namespace PlasmaLean.Design.CoilKam
""")
    lines.append("set_option linter.style.longLine false in")
    lines.append("/-- The torus records of the coarse coil torus (scale `2¹⁰⁰`). -/")
    lines.append("def ckRecs : List TRec := [")
    body = [f"  ⟨{lean_int(k)}, {lean_int(m)}, {lean_int(a)}, {lean_int(ap)}, {lean_int(b)}, {lean_int(bp)}⟩"
            for (k, m, a, ap, b, bp) in recs]
    lines.append(",\n".join(body) + "]\n")
    lines.append("set_option linter.style.longLine false in")
    lines.append("/-- The exponential table `D e^{2πit/32}`, `t < 32`. -/")
    lines.append("def ckTbl : List (ℤ × ℤ) := [")
    lines.append(",\n".join(f"  ({lean_int(c)}, {lean_int(s)})" for c, s in tbl) + "]\n")
    lines.append(f"/-- `⌊2¹⁰⁰ ι_A⌋`. -/\ndef ckIq : ℤ := {Iq}\n")
    lines.append(f"/-- The error of the exponential table (units `2⁻¹⁰⁰`). -/\ndef ckE : ℕ := {E}\n")
    lines.append(f"/-- The error of the base entry (units `2⁻¹⁰⁰`). -/\ndef ckE1 : ℕ := {e1}\n")
    lines.append("end PlasmaLean.Design.CoilKam\n")
    open(path, 'w').write("\n".join(lines))


if __name__ == '__main__':
    N, M = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (8, 16)
    recs = records(N, M)
    tbl = table()
    eC, eS, br = base_errors(tbl)
    e1 = eC + eS
    E = tableErr(e1, tbl[1], tbl, 0)
    Iq = iota_q()
    print(f"records {len(recs)}, table error E = {E}, base e1 = {e1} (eC {eC}, eS {eS})")
    t0 = time.time()
    rows = []
    tot1 = tot2 = 0
    for j in range(N1):
        r1 = r2 = 0
        for l in range(L):
            res = pointAP(Iq, tbl, E, recs, j, l)
            assert res is not None, (j, l)
            r1 += res[0]; r2 += res[1]
        rows.append((r1, r2))
        tot1 += r1; tot2 += r2
    print(f"grid {N1}x{L}: sum s1 = {tot1} ({tot1 / D:.4e}), sum s2 = {tot2} ({tot2 / D:.4e}); "
          f"mean {tot1 / D / (N1 * L):.3e}, {tot2 / D / (N1 * L):.3e}  ({time.time() - t0:.1f}s)")
    out = os.path.join(ROOT, 'PlasmaLean/Design/CoilKamData.lean')
    emit(recs, tbl, Iq, E, e1, eC, eS, br, rows, out)
    # numerical quantities for the hmap and sup bounds
    rest = recs[1:]
    a0, b0 = recs[0][2], recs[0][4]
    s1 = (abs(a0 - D) + sum(abs(r[2]) + abs(r[3]) for r in rest)) / D
    s2 = (abs(b0) + sum(abs(r[4]) + abs(r[5]) for r in rest)) / D
    json.dump({'N': N, 'M': M, 'E': E, 'e1': e1, 'eC': eC, 'eS': eS, 'br': [str(b) for b in br],
               'Iq': str(Iq), 'rows': [[str(a), str(b)] for a, b in rows], 'tot1': str(tot1),
               'tot2': str(tot2), 's1': s1, 's2': s2},
              open('/tmp/ckwork/predict.json', 'w'), indent=1)
    print(f"s1 = {s1:.6f}, s2 = {s2:.6f}")


HDR = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

"""


def emit_points(Iq, tbl, E, recs):
    """Write CoilKamPts{0..7}.lean (one kernel evaluation per grid point) and CoilKamRows.lean."""
    vals = {(j, l): pointAP(Iq, tbl, E, recs, j, l) for j in range(N1) for l in range(L)}
    for k in range(8):
        out = [HDR + f"""public import PlasmaLean.Design.CoilKamGrid

/-!
# Kernel evaluations of the coarse sampled certificate, rows {2 * k} and {2 * k + 1}

Each theorem is one kernel evaluation (`decide +kernel`) of the grid-point checker `ckPt j l`
(values predicted by the untrusted `scripts/coil_kam_oracle/emit_lean.py`); the residual bounds
are computed once, here.
-/

public section

namespace PlasmaLean.Design.CoilKam
"""]
        for j in (2 * k, 2 * k + 1):
            for l in range(L):
                a, b = vals[(j, l)]
                out.append(f"/-- Kernel evaluation of the grid point `({j}, {l})`. -/\n"
                           f"theorem ckPt_{j}_{l} : ckPt {j} {l} = some ({a}, {b}) := by\n"
                           f"  decide +kernel\n")
        out.append("end PlasmaLean.Design.CoilKam\n")
        open(os.path.join(ROOT, f'PlasmaLean/Design/CoilKamPts{k}.lean'), 'w').write("\n".join(out))
    imports = "\n".join(f"public import PlasmaLean.Design.CoilKamPts{k}" for k in range(8))
    out = [HDR + imports + """

/-!
# The rows of the coarse sampled certificate

Each row lemma assembles the 32 point evaluations of `Design/CoilKamPts0`–`7` with `row_bound`
(given the analytic inputs `CkHyp`).
-/

@[expose] public section

namespace PlasmaLean.Design.CoilKam
"""]
    totA = totB = 0
    for j in range(N1):
        vs = [vals[(j, l)] for l in range(L)]
        A = sum(v[0] for v in vs); B = sum(v[1] for v in vs)
        totA += A; totB += B
        lst = ",\n    ".join(f"({a}, {b})" for a, b in vs)
        cases = "\n".join(f"      | {l}, _ => ckPt_{j}_{l}" for l in range(L))
        out.append(f"""/-- The point values of row `{j}`. -/
def ckRow{j} : List (ℕ × ℕ) := [
    {lst}]

/-- Row `{j}` of the grid. -/
theorem ck_row_{j} (H : CkHyp) :
    ∑ l ∈ Finset.range 32, rowR {j} l ≤ ({A} : ℝ) / ckD ∧
      ∑ l ∈ Finset.range 32, rowZ {j} l ≤ ({B} : ℝ) / ckD := by
  have h := row_bound H {j} ckRow{j} rfl fun l hl =>
    match l, hl with
{cases}
      | n + 32, h => absurd h (by omega)
  have e1 : ((ckRow{j}.map Prod.fst).sum : ℝ) = {A} := by norm_num [ckRow{j}]
  have e2 : ((ckRow{j}.map Prod.snd).sum : ℝ) = {B} := by norm_num [ckRow{j}]
  rw [e1, e2] at h
  exact h
""")
    out.append("end PlasmaLean.Design.CoilKam\n")
    open(os.path.join(ROOT, 'PlasmaLean/Design/CoilKamRows.lean'), 'w').write("\n".join(out))
    return totA, totB


if __name__ == '__main__' and os.environ.get('CK_GRID'):
    N, M = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (8, 16)
    recs = records(N, M)
    tbl = table()
    eC, eS, br = base_errors(tbl)
    E = tableErr(eC + eS, tbl[1], tbl, 0)
    totA, totB = emit_points(iota_q(), tbl, E, recs)
    json.dump({'totA': str(totA), 'totB': str(totB)}, open('/tmp/ckwork/grid.json', 'w'), indent=1)
    print("point files written; totals", totA, totB)
