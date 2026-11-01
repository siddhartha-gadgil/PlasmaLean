"""UNTRUSTED generator.  Torus data of a Dommaschk KAM torus for the Lean certificate (N-33 items 6, 7).

Input: an exported refined torus `torus_<tag>_N<N>_M<M>.json` of run.py (R = sum a cos(k theta + m psi_o),
z = sum b sin(k theta + m psi_o), psi_o = 2 phi; decimal strings).  Output (Lean, generated, do not edit):

  PlasmaLean/Design/DommaschkKamCData.lean   the packed half grids `datU` (U = R - R0, R0 = 29/32) and
                                             `datZ` in the oracle angle psi_o = 2 phi, the dyadic iota_q,
                                             the moving frame centre (cenR, cenZ : DkPoly.SP, angle only).

Format (the GC ball-chain format of Certificates/KronBallGrid, so a KronBall residual chain can consume
the grids unchanged):
  * grid g on [0, 2N] x [0, 2M], g(k + N, m + M) = 2^S * (complex coefficient of e^{i(k theta + m psi_o)})
    times i^p, p = 0 for U (cosine series, g even) and p = 1 for Z (sine series, g odd);
  * stored as the half grid h (rows i = N..2N, one packed literal per row, 2M + 1 fields of width F,
    offset 2^(F-1)), completed by `symGrid N M ((-1)^p) h`; h(k, m) = round(a_km 2^(S-1)) (resp. b_km),
    h(0, m) = 0 for m < 0, so g(0, 0) = 2 h(0, 0) for U and 0 for Z.
The Lean module `Design/DommaschkKamCTorus` turns these into `u0C z0C : FA` in the Lean angle
psi_L = 2 phi - pi/2 by the rotation c_km -> i^m c_km (`rotPsi`, `eval_rotPsi`).

Validation (exact, before writing): index sets; the rounding error of every coefficient; a Python
mirror of `fieldW`/`halfGridR`/`symGrid` decodes every packed field back to the rounded value and every
complex coefficient back to a_q/2, b_q/(2i); iota_q is within 2^-Q of the exact noble value
-(85 + sqrt 5)/361 (integer square inequalities, the same that the Lean proof checks); the centre
polynomials are angle only, sorted, nonzero, and give a one-signed winding form W0 = d_theta K x (K - A)
on the torus (float check on a 256 x 256 grid of the rounded torus, margin asserted).

usage: python emit_torus.py --torus FILE [--S 128] [--out-dir PlasmaLean/Design] [--check-only]
"""
import argparse
import hashlib
import json
import math
import os
import sys
import textwrap
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import numpy as np                                   # noqa: E402

R0 = Fraction(29, 32)

# The moving frame centre A(psi_o) = (R0 + aR, aZ), psi_o = 2 phi (stellarator symmetric, NFP 2):
# A_R = sum_n alpha_n cos(n psi_o), A_Z = sum_n beta_n sin(n psi_o): the first three harmonics of
# the traced magnetic axis (scripts/dommaschk_kam/torus.py find_axis + flow over half a turn),
# rounded to 10^-4 (`fit_centre` recomputes them; `--refit` checks agreement).
CENTRE_ALPHA = [Fraction(9187, 10000), Fraction(592, 10000), Fraction(-108, 10000), Fraction(-30, 10000)]
CENTRE_BETA = [Fraction(0), Fraction(-604, 10000), Fraction(107, 10000), Fraction(29, 10000)]

# The exact rotation number of torus C: iota_C = -(85 + sqrt 5)/361, |iota|/2 = [0; 8, 3, 1, 1, ...].
IOTA_A, IOTA_B = 85, 361


# ----------------------------------------------------------------------------------------- input
def load_torus(path):
    import torus as T
    d = json.load(open(path))
    N, M = d['N'], d['M']
    Is, Iz = T.index_sets(N, M)
    assert [list(x) for x in d['idx_R']] == Is.tolist(), 'idx_R differs from torus.index_sets'
    assert [list(x) for x in d['idx_z']] == Iz.tolist(), 'idx_z differs from torus.index_sets'
    a = {tuple(k): Fraction(s) for k, s in zip(d['idx_R'], d['a'])}
    b = {tuple(k): Fraction(s) for k, s in zip(d['idx_z'], d['b'])}
    raw = open(path, 'rb').read()
    return dict(N=N, M=M, a=a, b=b, iota=Fraction(d['iota']), dps=d['dps'], tag=d['tag'],
                sha=d['candidate_sha256'], file_sha=hashlib.sha256(raw).hexdigest(), path=path,
                af=np.array([float(x) for x in d['a']]), bf=np.array([float(x) for x in d['b']]))


# ------------------------------------------------------------------------------------ half grids
def half_grids(t, S):
    N, M = t['N'], t['M']
    hU, hZ = {}, {}
    for i in range(N, 2 * N + 1):
        for j in range(2 * M + 1):
            k, m = i - N, j - M
            if k == 0 and m < 0:
                hU[(i, j)] = hZ[(i, j)] = 0
                continue
            av = t['a'][(k, m)] - (R0 if (k, m) == (0, 0) else 0)
            bv = t['b'].get((k, m), Fraction(0))
            hU[(i, j)] = round(av * 2 ** (S - 1))
            hZ[(i, j)] = round(bv * 2 ** (S - 1))
    assert hZ[(N, M)] == 0
    return hU, hZ


def pack_rows(h, N, M, F):
    rows = []
    for i in range(N, 2 * N + 1):
        tot = 0
        for j in range(2 * M, -1, -1):
            v = h[(i, j)]
            assert -2 ** (F - 1) <= v < 2 ** (F - 1)
            tot = (tot << F) + (v + 2 ** (F - 1))
        rows.append(tot)
    return rows


# Python mirror of Certificates/KronBallGrid (fieldW, halfGridR, symGrid; Nat subtraction truncates)
def fieldW(F, data, f):
    return ((data >> (F * f)) % 2 ** F) - 2 ** (F - 1)


def halfGridR(F, N, rows, i, j):
    return fieldW(F, rows[i - N] if i - N < len(rows) else 0, j) if N <= i else 0


def symGrid(N, M, s, h, i, j):
    return h(i, j) + s * h(max(2 * N - i, 0), max(2 * M - j, 0))


def validate_grids(t, S, F, rowsU, rowsZ, hU, hZ, r_list=(0.0, 0.045, 0.06)):
    """Decode the packed data as Lean does and compare with the rounded and the exact coefficients."""
    N, M = t['N'], t['M']
    gU = lambda i, j: symGrid(N, M, 1, lambda a, b: halfGridR(F, N, rowsU, a, b), i, j)   # noqa: E731
    gZ = lambda i, j: symGrid(N, M, -1, lambda a, b: halfGridR(F, N, rowsZ, a, b), i, j)  # noqa: E731
    err = {r: [0.0, 0.0] for r in r_list}
    maxerr = Fraction(0)
    for i in range(2 * N + 1):
        for j in range(2 * M + 1):
            k, m = i - N, j - M
            if i >= N:
                assert halfGridR(F, N, rowsU, i, j) == hU[(i, j)]
                assert halfGridR(F, N, rowsZ, i, j) == hZ[(i, j)]
            # exact complex coefficients of U = R - R0 (cos series) and Z (sine series, times i)
            kk, mm, sg = (k, m, 1) if (k > 0 or (k == 0 and m >= 0)) else (-k, -m, -1)
            if (kk, mm) == (0, 0):
                cU, cZ = t['a'][(0, 0)] - R0, Fraction(0)
            else:
                cU = t['a'][(kk, mm)] / 2
                cZ = sg * t['b'][(kk, mm)] / 2       # coefficient of e^{i x} in b sin x is b/(2i)
            # Lean: coeff = (2^S i^p)^{-1} g, so 2^S * coeff * i^p = g
            eU = abs(Fraction(gU(i, j), 2 ** S) - cU)
            eZ = abs(Fraction(gZ(i, j), 2 ** S) - cZ)
            maxerr = max(maxerr, eU, eZ)
            for r in r_list:
                w = math.exp(r * (abs(k) + abs(m)))
                err[r][0] += float(eU) * w
                err[r][1] += float(eZ) * w
    assert maxerr <= Fraction(1, 2 ** S), maxerr
    # symmetry of the completed grids
    for i in range(2 * N + 1):
        for j in range(2 * M + 1):
            assert gU(2 * N - i, 2 * M - j) == gU(i, j)
            assert gZ(2 * N - i, 2 * M - j) == -gZ(i, j)
    return err, maxerr


def grid_floats(t, S, hU, hZ):
    """The rounded torus as oracle coefficient arrays (for float checks)."""
    import torus as T
    N, M = t['N'], t['M']
    Is, Iz = T.index_sets(N, M)
    a = np.array([float(Fraction(2 * hU[(k + N, m + M)], 2 ** S) + (R0 if (k, m) == (0, 0) else 0))
                  for k, m in Is])
    b = np.array([float(Fraction(2 * hZ[(k + N, m + M)], 2 ** S)) for k, m in Iz])
    return a, b


# -------------------------------------------------------------------------------------- iota_q
def iota_q(Q):
    """Iq with |Iq/2^Q - (85 + sqrt 5)/361| <= 2^-Q, checked by integer squares:
    t = 361 Iq - 85 2^Q satisfies (t - 361)^2 <= 5 4^Q <= (t + 361)^2 and t >= 361."""
    s5 = math.isqrt(5 * 4 ** Q)
    Iq = (IOTA_A * 2 ** Q + s5 + IOTA_B // 2) // IOTA_B
    tq = IOTA_B * Iq - IOTA_A * 2 ** Q
    assert tq >= IOTA_B and (tq - IOTA_B) ** 2 <= 5 * 4 ** Q <= (tq + IOTA_B) ** 2
    return Iq, tq


# -------------------------------------------------------------------------------------- centre
def harmonic_poly(n, kind):
    """Re (c + i s)^n (kind 'c') or Im (c + i s)^n (kind 's') as {(c_exp, s_exp): int}."""
    out = {}
    for j in range(n + 1):
        if (kind == 'c' and j % 2 == 0) or (kind == 's' and j % 2 == 1):
            sign = (-1) ** (j // 2)
            out[(n - j, j)] = out.get((n - j, j), 0) + sign * math.comb(n, j)
    return out


def centre_polys(alpha, beta):
    """aR = A_R - R0 and aZ as sorted angle-only DkPoly terms (q, 0, 0, c, d)."""
    pR, pZ = {}, {}
    for n, al in enumerate(alpha):
        if n == 0:
            pR[(0, 0)] = pR.get((0, 0), 0) + al - R0
        else:
            for e, c in harmonic_poly(n, 'c').items():
                pR[e] = pR.get(e, 0) + al * c
    for n, be in enumerate(beta):
        if n > 0:
            for e, c in harmonic_poly(n, 's').items():
                pZ[e] = pZ.get(e, 0) + be * c
    tR = sorted((e, Fraction(q)) for e, q in pR.items() if q != 0)
    tZ = sorted((e, Fraction(q)) for e, q in pZ.items() if q != 0)
    return [(q, 0, 0, e[0], e[1]) for e, q in tR], [(q, 0, 0, e[0], e[1]) for e, q in tZ]


def eval_sp(terms, c, s):
    return sum(float(q) * c ** cc * s ** dd for (q, _, _, cc, dd) in terms)


def fit_centre(H=3, den=10 ** 4):
    import dfield
    import torus as T
    ev = dfield.Evaluator(dfield.ExactField())
    tr = T.Tracer(ev)
    Ra, za, _ = T.find_axis(tr)
    phs = np.pi * np.arange(257) / 256
    AR, AZ = tr.flow(np.array([Ra]), np.array([za]), phs)
    cR = np.fft.rfft(AR[0, :-1]) / 256
    cZ = np.fft.rfft(AZ[0, :-1]) / 256
    alpha = [Fraction(round((1 if n == 0 else 2) * cR[n].real * den), den) for n in range(H + 1)]
    beta = [Fraction(0)] + [Fraction(round(-2 * cZ[n].imag * den), den) for n in range(1, H + 1)]
    return alpha, beta


def winding_check(t, a, b, cR, cZ, grid=256):
    """W0 = d_theta R (z - aZ) - d_theta z (R - R0 - aR) on a grid of the (rounded) torus."""
    import dfield
    import torus as T
    ev = dfield.Evaluator(dfield.ExactField())
    g = T.Galerkin(ev, t['N'], t['M'], float(t['iota']), Nt=grid, Np=grid)
    R, z, Rth, Rps, zth, zps = g.fields(a, b)
    c, s = np.cos(g.ps)[None, :], np.sin(g.ps)[None, :]
    AR = float(R0) + eval_sp(cR, c, s)
    AZ = eval_sp(cZ, c, s)
    W0 = Rth * (z - AZ) - zth * (R - AR)
    return float(W0.min()), float(W0.max()), dict(R=(float(R.min()), float(R.max())),
                                                  z=(float(z.min()), float(z.max())))


# ---------------------------------------------------------------------------------------- Lean
HEADER = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

"""


def wrap_doc(text, width=100):
    """Re-wrap every paragraph of a module docstring to the line limit (code spans stay on a line)."""
    out = []
    tail = ''
    if text.rstrip().endswith('-/'):
        text, tail = text.rstrip()[:-2].rstrip(), '\n-/\n\n'
    for par in text.split('\n\n'):
        if par.startswith('#') or par.startswith('/-!') or par.strip() == '-/':
            out.append(par)
            continue
        lead = '* ' if par.startswith('* ') else ''
        out.append(textwrap.fill(' '.join(par.split()), width=width, break_long_words=False,
                                 break_on_hyphens=False, subsequent_indent='  ' if lead else ''))
    res = '\n\n'.join(out)
    assert all(len(line) <= width for line in res.split('\n')), 'docstring line too long'
    return res + tail


def q_lean(q):
    q = Fraction(q)
    return f'mkRat ({q.numerator}) {q.denominator}'


def sp_lean(terms):
    if not terms:
        return '[]'
    return '[\n' + ',\n'.join(f'    ⟨{q_lean(q)}, {a}, {b}, {c}, {d}⟩' for (q, a, b, c, d) in terms) + ']'


def trig_terms(coef, fn):
    out = []
    for n, x in enumerate(coef):
        if x == 0:
            continue
        sgn = '−' if x < 0 else '+'
        body = f'{abs(float(x)):g}' + (f' {fn} {n}ψₒ' if n else '')
        out.append((sgn if out or x < 0 else '') + (' ' if out else '') + body)
    return out


def emit_data(t, S, F, Q, Iq, rowsU, rowsZ, cR, cZ, alpha, beta, info, out):
    N, M = t['N'], t['M']
    src = os.path.relpath(os.path.abspath(t['path']), REPO)
    if src.startswith('..'):
        src = os.path.basename(t['path']) + ' (development torus, outside the repository)'
    lines = [HEADER, 'public import PlasmaLean.Design.DommaschkKamPoly\n\n']
    lines.append(wrap_doc(f'''/-!
# Data of Dommaschk torus C for the KAM certificate (generated file)

**Generated** by `scripts/dommaschk_kam/emit_torus.py` from `{src}`
(sha256 `{t['file_sha'][:16]}…`; candidate sha256 `{t['sha'][:16]}…`; oracle `{N} × {M}` modes, refined
to {t['dps']} digits). Do not edit by hand. Nothing here is trusted: the data only *define* the
approximate torus; its properties are proved elsewhere (`Design/DommaschkKamCTorus`, and the
residual and admissibility chains of N-33 items 7, 8).

**Torus** (oracle angle `ψₒ = 2φ`, `φ` the cylindrical angle): `R = Σ a_km cos(kθ + mψₒ)`,
`z = Σ b_km sin(kθ + mψₒ)`, `|k| ≤ {N}`, `|m| ≤ {M}`, rotational transform
`ι_C = −(85 + √5)/361 ≈ −0.2416512`. Stored in the ball-chain format of `Certificates/KronBallGrid`:
packed half grids (`halfGridR`: one literal per row `i − N`, `i = N … 2N`, rows of `2M + 1` fields of
width `{F}` bits, offset `2^{F - 1}`), to be completed by `symGrid N M ((-1) ^ p)` with `p = 0` for
`U = R − R₀` (`R₀ = 29/32`) and `p = 1` for `z`; the centre `g(N + k, M + m)` is `2^{S}` times the
complex coefficient of `e^{{i(kθ + mψₒ)}}` times `iᵖ`. Coefficients are rounded to `2^{{−{S}}}`
(error at most `2^{{−{S}}}` per complex coefficient; weighted `ℓ¹` rounding error
`{info['err045'][0]:.1e}` (`U`), `{info['err045'][1]:.1e}` (`z`) at `r = 0.045`).

**Rotational transform**: `ι_q = −Iqc/2^Qc`, `|ι_q − ι_C| ≤ 2^{{−Qc}}` (checked by the generator;
proved in `Design/DommaschkKamCTorus`, `iotaqC_close`).

**Moving frame centre** (N-33 (O1)): `A(ψₒ) = (R₀ + a_R, a_z)` with
`A_R = {' '.join(trig_terms(alpha, 'cos'))}`, `A_z = {' '.join(trig_terms(beta, 'sin'))}`: the first three
harmonics of the traced magnetic axis, rounded to `10⁻⁴`, written in `c = cos 2φ`, `s = sin 2φ` as the
harmonic polynomials `Re`, `Im (c + i s)ⁿ` (`cenR`, `cenZ`: angle-only `DkPoly.SP`, the arguments
`aR aZ` of `DommaschkKam.dkFieldC`). On the torus the winding form `W₀ = ∂_θK × (K − A)` lies in
`[{info['W0'][0]:.3e}, {info['W0'][1]:.3e}]` (generator, float check on a 256 × 256 grid; untrusted).
-/
''') + f'''
@[expose] public section

namespace PlasmaLean.Design.DommaschkKamC

open PlasmaLean.Design.DommaschkKam.DkPoly

/-- Poloidal truncation `N` (modes `|k| ≤ N`). -/
def Nc : ℕ := {N}
/-- Toroidal truncation `M` (modes `|m| ≤ M` in `ψₒ = 2φ`). -/
def Mc : ℕ := {M}
/-- Scale exponent: grid entries are `2^Sc` times the coefficients. -/
def Sc : ℕ := {S}
/-- Field width of the packed half grids. -/
def Fc : ℕ := {F}
/-- Exponent of the dyadic rotational transform `ι_q = −Iqc/2^Qc`. -/
def Qc : ℕ := {Q}
/-- Numerator of `|ι_q| = Iqc/2^Qc ≈ (85 + √5)/361`. -/
def Iqc : ℕ := {Iq}

''')
    for nm, rows, what in (('datU', rowsU, '`U = R − R₀`'), ('datZ', rowsZ, '`z`')):
        lines.append('set_option linter.style.longLine false in\n')
        lines.append(f'/-- Packed half grid of {what} (one literal per row `i − N`). -/\n')
        lines.append(f'def {nm} : List ℕ := [\n' + ',\n'.join('  0x%x' % v for v in rows) + ']\n\n')
    lines.append('/-- The radial part `a_R = A_R − R₀` of the moving frame centre (angle only). -/\n')
    lines.append(f'def cenR : SP := {sp_lean(cR)}\n\n')
    lines.append('/-- The vertical part `a_z = A_z` of the moving frame centre (angle only). -/\n')
    lines.append(f'def cenZ : SP := {sp_lean(cZ)}\n\n')
    lines.append('end PlasmaLean.Design.DommaschkKamC\n')
    path = os.path.join(out, 'DommaschkKamCData.lean')
    open(path, 'w').write(''.join(lines))
    return path


# ---------------------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--torus', required=True)
    ap.add_argument('--S', type=int, default=0, help='scale exponent (default min(128, bits of dps - 8))')
    ap.add_argument('--out-dir', default=os.path.join(REPO, 'PlasmaLean', 'Design'))
    ap.add_argument('--check-only', action='store_true')
    ap.add_argument('--refit', action='store_true', help='re-trace the axis and compare the centre')
    args = ap.parse_args()
    t = load_torus(args.torus)
    import dfield
    assert t['sha'] == dfield.ExactField().sha, 'candidate hash mismatch'
    S = args.S or min(128, int(t['dps'] * math.log2(10)) - 8)
    N, M = t['N'], t['M']
    print(f"torus {t['tag']} {N} x {M}, dps {t['dps']}, S = {S}")
    # iota
    Q = S
    Iq, tq = iota_q(Q)
    # the oracle iota is the exact noble value to its printed precision (exact bracket of sqrt 5)
    P2 = 400
    s5 = math.isqrt(5 * 4 ** P2)
    lo, hi = Fraction(-(IOTA_A * 2 ** P2 + s5 + 1), IOTA_B * 2 ** P2), Fraction(-(IOTA_A * 2 ** P2 + s5), IOTA_B * 2 ** P2)
    dev = max(abs(t['iota'] - lo), abs(t['iota'] - hi))
    assert dev < Fraction(1, 10 ** (t['dps'])), float(dev)
    print(f"iota_q = -Iq/2^{Q}, |iota_q - iota_C| <= 2^-{Q} (t = {tq}); |oracle iota - iota_C| <= {float(dev):.1e}")
    # grids
    hU, hZ = half_grids(t, S)
    F = max(abs(v).bit_length() for h in (hU, hZ) for v in h.values()) + 2
    rowsU, rowsZ = pack_rows(hU, N, M, F), pack_rows(hZ, N, M, F)
    err, maxerr = validate_grids(t, S, F, rowsU, rowsZ, hU, hZ)
    print(f"F = {F}; max coefficient rounding error {float(maxerr):.2e} (<= 2^-S); weighted rounding "
          + ', '.join(f"r={r}: {e[0]:.1e}/{e[1]:.1e}" for r, e in err.items()))
    # centre
    alpha, beta = CENTRE_ALPHA, CENTRE_BETA
    if args.refit:
        fa, fb = fit_centre()
        print('refit centre:', [str(x) for x in fa], [str(x) for x in fb])
        assert all(abs(x - y) <= Fraction(2, 10 ** 4) for x, y in zip(fa + fb, alpha + beta))
    cR, cZ = centre_polys(alpha, beta)
    for terms in (cR, cZ):
        assert all(a == 0 and b == 0 and q != 0 for (q, a, b, _, _) in terms)
        keys = [(a, b, c, d) for (_, a, b, c, d) in terms]
        assert keys == sorted(keys) and len(set(keys)) == len(keys)
    # the polynomials reproduce the trigonometric centre
    for ps in np.linspace(0, 2 * np.pi, 37):
        c, s = math.cos(ps), math.sin(ps)
        AR = sum(float(x) * math.cos(n * ps) for n, x in enumerate(alpha))
        AZ = sum(float(x) * math.sin(n * ps) for n, x in enumerate(beta))
        assert abs(float(R0) + eval_sp(cR, c, s) - AR) < 1e-12 and abs(eval_sp(cZ, c, s) - AZ) < 1e-12
    a, b = grid_floats(t, S, hU, hZ)
    w0min, w0max, rng = winding_check(t, a, b, cR, cZ)
    print(f"centre: W0 in [{w0min:.4e}, {w0max:.4e}] (ratio {w0max / w0min:.3f}); torus R in "
          f"[{rng['R'][0]:.4f}, {rng['R'][1]:.4f}], z in [{rng['z'][0]:.4f}, {rng['z'][1]:.4f}]")
    assert w0max < 0 and w0max / w0min > 0.5, 'winding form not one-signed with margin'
    info = dict(err045=err[0.045], W0=(w0min, w0max))
    if args.check_only:
        return
    path = emit_data(t, S, F, Q, Iq, rowsU, rowsZ, cR, cZ, alpha, beta, info, args.out_dir)
    print(f"wrote {path} ({os.path.getsize(path) / 1e6:.2f} MB)")


if __name__ == '__main__':
    main()
