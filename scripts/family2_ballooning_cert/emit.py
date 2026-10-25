#!/usr/bin/env python3
"""UNTRUSTED emitter: certificate JSON (from search.py) -> Lean DATA modules (NOT trusted).

The emitted modules contain only data: the secular constant c0 and the coefficient arrays of
the certificate F(x, s) = sum_j f_j(theta, zeta) r_j(s) of `model.Model`, each number rounded
to a dyadic rational m / 2^P (P = `--prec`, default 40) and stored as its integer numerator m
in `List Int` literals.  Nothing in them is a claim: a future kernel checker (not yet
implemented, see notes/theory/finite-beta-stellarator.md section 9) has to read these lists
and verify the surface inequality box by box.  Each module carries a length sanity theorem
proved by `rfl` (kernel evaluation of `List.length`).

Layout for a surface with tag T (e.g. k0900):
  LandremanFamily2BallooningDataT<i>.lean   chunks of <= --chunk integers (default 20000),
                                            split into defs of <= --per-def integers;
  LandremanFamily2BallooningDataT.lean      header data (k, eps_m, NT, NZ, widths, c0) and
                                            the list of chunk names (imports the chunks).
The modules need no imports beyond Lean core, so a chunk can be checked with
`lake env lean FILE`.

Usage:
  emit.py CERT.json [CERT2.json ...] --outdir DIR [--prec 40] [--chunk 20000] [--per-def 2000]
"""
import argparse
import json
import os
from fractions import Fraction

HEADER = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module
"""
NS = 'PlasmaLean.Design.LandremanFamily2BallooningData'


def dyadic(x, prec):
    return int(round(x * (1 << prec)))


def zigzag(m):
    """Int -> Nat bijection 0, -1, 1, -2, ... -> 0, 1, 2, 3, ... (Nat literals elaborate fast)."""
    return 2 * m if m >= 0 else -2 * m - 1


def tag_of(k):
    return 'k%04d' % int(round(k * 1000))


def lean_list(vals, per_line=12):
    lines = []
    for i in range(0, len(vals), per_line):
        lines.append('  ' + ', '.join(str(v) for v in vals[i:i + per_line]))
    return '[\n' + ',\n'.join(lines) + ']'


def frac_lit(x):
    f = Fraction(x).limit_denominator(10 ** 9)
    return '(%d : Int) / %d' % (f.numerator, f.denominator) if f.denominator != 1 else str(f.numerator)


def emit_cert(res, outdir, prec, chunk, per_def, imports_prefix='PlasmaLean.Design.'):
    k = res['k']
    tag = tag_of(k)
    ints = [zigzag(dyadic(v, prec)) for row in res['C'] for v in row]
    files = []
    chunks = [ints[i:i + chunk] for i in range(0, len(ints), chunk)]
    for ci, ch in enumerate(chunks):
        name = 'LandremanFamily2BallooningData%sC%d' % (tag, ci)
        defs = []
        parts = [ch[i:i + per_def] for i in range(0, len(ch), per_def)]
        for pi, part in enumerate(parts):
            defs.append('/-- Zigzag-coded coefficient numerators (scale `2^%d`), chunk %d, part %d of surface\n'
                        '`k = %g`. -/\n@[expose] def part%d : List Nat := %s\n\n'
                        'set_option maxRecDepth 8000 in\n/-- Length of part %d. -/\ntheorem part%d_length : part%d.length = %d := by\n  rfl\n'
                        % (prec, ci, pi, k, pi, lean_list(part), pi, pi, pi, len(part)))
        allp = ' ++ '.join('part%d' % i for i in range(len(parts)))
        body = (HEADER + '\n/-!\n# Family-2 ballooning certificate data, surface `k = %g`, chunk %d\n\n'
                'UNTRUSTED data emitted by `scripts/family2_ballooning_cert/emit.py` from the search of\n'
                '`scripts/family2_ballooning_cert/search.py`: %d coefficient numerators `m` of the\n'
                'certificate functions (value `m / 2^%d`), in the order `C[j][i_theta * NZ + i_zeta]`.\n'
                'No claim is made here; a kernel checker must verify the surface inequality.\n-/\n\n'
                'public section\n\nnamespace %s.%s.c%d\n\n' % (k, ci, len(ch), prec, NS, tag, ci)
                + '\n'.join(defs) +
                '\n/-- Zigzag decoding `2m ↦ m`, `2m + 1 ↦ -(m + 1)`. -/\n'
                '@[expose] def unzig (n : Nat) : Int := if n %% 2 = 0 then (n / 2 : Nat) else -((n / 2 : Nat) + 1 : Int)\n\n'
                '/-- Zigzag-coded numerators of this chunk. -/\n@[expose] def codes : List Nat := %s\n\n'
                '/-- All coefficient numerators of this chunk. -/\n@[expose] def coeffs : List Int := codes.map unzig\n\n'
                '/-- Sanity check: the chunk has %d entries. -/\ntheorem coeffs_length : coeffs.length = %d := by\n'
                '  simp only [coeffs, codes, List.length_map, List.length_append, %s]\n\nend %s.%s.c%d\n'
                % (allp, len(ch), len(ch), ', '.join('part%d_length' % i for i in range(len(parts))), NS, tag, ci))
        path = os.path.join(outdir, name + '.lean')
        with open(path, 'w') as f:
            f.write(body)
        files.append((name, path, len(ch)))
    # header module
    name = 'LandremanFamily2BallooningData%s' % tag
    imps = ''.join('public import %s%s\n' % (imports_prefix, n) for n, _, _ in files)
    sig = ', '.join(frac_lit(v) for v in res['sig'])
    sab = ', '.join(frac_lit(v) for v in res['sigabs'])
    body = (HEADER + '\n' + imps + '\n/-!\n# Family-2 ballooning certificate data, surface `k = %g`: header\n\n'
            'UNTRUSTED parameters of the certificate ansatz of `scripts/family2_ballooning_cert/model.py`\n'
            '(search margin %.4g, dense-check minimum %.4g; both untrusted floats).\n-/\n\npublic section\n\n'
            'namespace %s.%s\n\n'
            '/-- Surface label `k` (flux surface `ψ = k²/2`). -/\n@[expose] def k : Rat := %s\n\n'
            '/-- Tip-clustering parameter `ε_m` of the poloidal angle. -/\n@[expose] def epsm : Rat := %s\n\n'
            '/-- Numbers of B-spline cells in `θ` and `ζ`. -/\n@[expose] def grid : Nat × Nat := (%d, %d)\n\n'
            '/-- Scaled widths (`u = s/(σ |B|/|∇ψ|²)`). -/\n@[expose] def sig : List Rat := [%s]\n\n'
            '/-- Absolute widths. -/\n@[expose] def sigabs : List Rat := [%s]\n\n'
            '/-- Secular constant `c₀` as the numerator over `2^%d`. -/\n@[expose] def c0num : Int := %d\n\n'
            '/-- Numbers of entries of the chunks. -/\n@[expose] def chunkSizes : List Nat := [%s]\n\n'
            '/-- Sanity check: the chunks hold `nf · NT · NZ` coefficients. -/\n'
            'theorem chunkSizes_sum : chunkSizes.sum = %d * %d := by\n  rfl\n\nend %s.%s\n'
            % (k, res['margin'], res['dense']['min_defect'], NS, tag, frac_lit(k), frac_lit(res['epsm']),
               res['NT'], res['NZ'], sig, sab, prec, dyadic(res['c0'], prec),
               ', '.join(str(n) for _, _, n in files), res['nf'], res['nb'], NS, tag))
    path = os.path.join(outdir, name + '.lean')
    with open(path, 'w') as f:
        f.write(body)
    return [path for _, path, _ in files] + [path]


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('certs', nargs='+')
    p.add_argument('--outdir', default=None)
    p.add_argument('--prec', type=int, default=40)
    p.add_argument('--chunk', type=int, default=20000)
    p.add_argument('--per-def', type=int, default=500)
    a = p.parse_args()
    out = a.outdir
    if out is None:
        import tempfile
        out = tempfile.mkdtemp(prefix='f2b_emit_')
    os.makedirs(out, exist_ok=True)
    for c in a.certs:
        for path in emit_cert(json.load(open(c)), out, a.prec, a.chunk, a.per_def):
            print(path)


if __name__ == '__main__':
    main()
