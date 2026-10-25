"""UNTRUSTED: emit the Lean files of the guiding-centre torus FAMILY certificate (Chebyshev series in
rho over the cell rho in [63/16384, 65/16384]) from /tmp/famw/fam_cert_{H,L}.pkl (fam_cert.py).

Light modules (import only Certificates/KronChebCompute; kernel checks in small processes):
  RationalStellaratorGCFamData{H1..Hk,L}  stored Chebyshev coefficients (SliceData)
  RationalStellaratorGCFamKv{H,L}         layouts, weights, boxes, l1 bounds, Kronecker images
  RationalStellaratorGCFamTrees{H,L}      light expression trees (ExN)
  RationalStellaratorGCFamCheck{H,L}{k}   kernel checks (converted to proof terms by
                                          lowmem/lowmem_emit.py, proofterm/proofterm_emit.py)
The side conditions of the other modules are emitted as `kernel_fact` proof terms.
Heavy modules:
  RationalStellaratorGCFamEnv{H,L}        polynomials, boxes, l1 bounds, Kronecker images (proofs)
  ... (relations, chains, outputs: later stages)
Usage: python fam_emit_lean.py data|checks|...
"""
import sys, os, pickle
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'proofterm'))
from proofterm_emit import kernel_fact_text  # side conditions as `kernel_fact` proof terms
from fam_ball import decode_slice, encode_slice, famL1
from ballcert import majN

OUT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
PRE = 'RationalStellaratorGCFam'
NS = 'PlasmaLean.Design.RationalStellaratorGC'
HEADER = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''


def qlean(q):
    q = Fr(q)
    if q.denominator == 1:
        return '(%d : ℚ)' % q.numerator
    den = q.denominator
    k10, d = 0, den
    while d % 10 == 0:
        d //= 10
        k10 += 1
    if d == 1:
        return '(%d / 10 ^ %d : ℚ)' % (q.numerator, k10)
    if den & (den - 1) == 0:
        return '(%d / 2 ^ %d : ℚ)' % (q.numerator, den.bit_length() - 1)
    return '(%d / %d : ℚ)' % (q.numerator, den)


def tree_lean(e):
    k = e[0]
    if k == 'var':
        return '.var %d' % e[1]
    if k == 'cst':
        return '.cst %d' % e[1] if e[1] >= 0 else '.cst (%d)' % e[1]
    op = {'add': '.add', 'sub': '.sub', 'mul': '.mul'}[k]
    return '%s (%s) (%s)' % (op, tree_lean(e[1]), tree_lean(e[2]))


def tree_vars(e, acc=None):
    acc = set() if acc is None else acc
    if e[0] == 'var':
        acc.add(e[1])
    elif e[0] != 'cst':
        tree_vars(e[1], acc)
        tree_vars(e[2], acc)
    return acc


def wrap(text, indent):
    words = text.split(' ')
    lines, cur = [], ''
    for w in words:
        if len(cur) + len(w) + 1 + indent + 2 > 98 and cur:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w) if cur else w
    lines.append(cur)
    return ('\n' + ' ' * (indent + 2)).join(lines)


def lst(xs):
    lines, cur = [], '  ['
    for k, x in enumerate(xs):
        piece = x + (', ' if k + 1 < len(xs) else ']')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip())
            cur = '    '
        cur += piece
    lines.append(cur)
    return '\n' + '\n'.join(lines)


def clog2(n):
    k = 0
    while (1 << k) < n:
        k += 1
    return k


def hexwrap(x, indent=4):
    """a hex literal, split into lines with a trailing `\\` is not allowed in Lean: keep one line."""
    return '0x%x' % x


def lean_slice(sd):
    return '⟨%d, %d, %d,\n    0x%x,\n    0x%x, %d, %d⟩' % (sd.Nj, sd.Mj, sd.Fj, sd.blk, sd.col, sd.k1, sd.k2)


def same_slices(a, b):
    return len(a) == len(b) and all((x.Nj, x.Mj, x.Fj, x.blk, x.col) == (y.Nj, y.Mj, y.Fj, y.blk, y.col)
                                    for x, y in zip(a, b))


class FP:
    """One family pipeline (H or L) as emitted."""

    def __init__(self, P, tag):
        self.P, self.tag = P, tag
        self.N, self.M, self.S, self.D = P['N'], P['M'], P['S'], P['D']
        self.nvar = P['nvar']
        self.W, self.Bx, self.B, self.E = P['W'], P['Bx'], P['B'], P['E']
        self.kind, self.names, self.fam, self.meta = P['kind'], P['names'], P['fam'], P['meta']
        self.nodes = {r['n']: r for r in P['nodes'] if r.get('var') is not None}
        self.norms = [r for r in P['nodes'] if r.get('var') is None]
        self.normrec = P['normrec']
        self.vstep = P['vstep']
        self.dd = clog2(self.N + 1)
        self.dr = clog2(2 * self.M + 1)
        self.dw = clog2(2 * self.D + 1)
        self.T = tag + 'F'
        # special (non-stored) variables
        self.rIdx = [i for i in range(self.nvar) if self.meta.get(i, {}).get('kind') == 'param']
        self.rIdx = self.rIdx[0] if self.rIdx else None
        self.special = set(i for i in range(self.nvar) if self.kind[i] in ('T', 'V', 'C', 'S', 'dummy'))
        if self.rIdx is not None:
            self.special.add(self.rIdx)
        self.dummies = [i for i in range(self.nvar) if self.kind[i] == 'dummy']
        # stored slices (derivatives stored as data), symbols, parities
        self.stored, self.c0, self.odd, self.derived = {}, {}, {}, {}
        for i in range(self.nvar):
            if i in self.special:
                continue
            f = self.fam[i]
            c0, a, bb = f['sym']
            p = self.W[i][2]
            s_new = 1 if p % 2 == 0 else -1
            if a == 0 and bb == 0:
                self.stored[i] = f['slices']
                self.c0[i] = c0
                assert f['s'] == s_new
            else:
                st = []
                for sd in f['slices']:
                    g = decode_slice(sd, self.N, self.M, f['s'], c0, a, bb)
                    sd2, g2 = encode_slice(g, self.N, self.M, s_new)
                    assert g2 == g
                    st.append(sd2)
                self.stored[i] = st
                self.c0[i] = 1
                self.derived[i] = (f['s'], c0, a, bb)
            self.odd[i] = (p % 2 == 1)
        # static l1 bounds of the stored families
        self.L = {}
        for i in range(self.nvar):
            k = self.kind[i]
            if i == self.rIdx:
                self.L[i] = 2 ** (self.S + 6) + 2 * 2 ** (self.S - 1)
            elif k == 'T':
                self.L[i] = 2 ** self.S
            elif k in ('V', 'C', 'S'):
                self.L[i] = 2
            elif k == 'dummy':
                self.L[i] = 0
            else:
                self.L[i] = famL1(self.stored[i], self.N, self.M, self.c0[i], 0, 0)
        # minimal widths of the fast images
        self.bmin, self.wmin = {}, {}
        for i in self.stored:
            c0 = self.c0[i]
            lc = clog2(2 * c0)
            self.bmin[i] = max([max(sd.Fj, sd.Fj + lc) for sd in self.stored[i]] + [1])
            self.wmin[i] = max([sd.Nj for sd in self.stored[i]] + [1])
        self.dataname = {}

    def nm(self, i):
        return self.names[i].replace("'", "p")

    def check_apriori(self):
        """re-check the a priori l1 bounds with the static bounds of the stored families."""
        bad = []
        for r in self.P['nodes']:
            lm = majN(self.L, r['tree'])
            if r.get('var') is not None:
                n = r['n']
                lm += abs(r['c']) * (2 ** self.S) ** r['dd'] * 2 ** r['de'] * self.L[n]
            if not lm < 2 ** (r['b'] - 1):
                bad.append((r['name'], lm.bit_length(), r['b']))
            for v in tree_vars(r['tree']) | ({r['n']} if r.get('var') is not None else set()):
                if v in self.bmin and (self.bmin[v] > r['b'] or self.wmin[v] > r['W']):
                    bad.append(('width', r['name'], v, self.bmin[v], r['b'], self.wmin[v], r['W']))
        for i, nr in self.normrec.items():
            if i in self.special:
                continue
            if not self.L[i] < 2 ** (nr['b'] - 1):
                bad.append(('centre', self.nm(i), self.L[i].bit_length(), nr['b']))
            if self.bmin[i] > nr['b'] or self.wmin[i] > nr['W']:
                bad.append(('centre width', self.nm(i)))
        return bad


H = FP(pickle.load(open('/tmp/famw/fam_cert_H.pkl', 'rb'))['H'], 'H')
L = FP(pickle.load(open('/tmp/famw/fam_cert_L.pkl', 'rb'))['L'], 'L')


def emit_data(p, files, shared=None):
    """the stored coefficients, in `files` modules; families equal to an earlier one (or to a family
    of `shared`) reuse its definition."""
    T = p.T
    order = [i for i in range(p.nvar) if i in p.stored]
    defs = []
    for i in order:
        reuse = None
        for j in order:
            if j >= i:
                break
            if same_slices(p.stored[j], p.stored[i]) and j in p.dataname:
                reuse = p.dataname[j]
                break
        if reuse is None and shared is not None:
            for j, nmj in shared.dataname.items():
                if same_slices(shared.stored[j], p.stored[i]):
                    reuse = nmj
                    break
        if reuse is not None:
            p.dataname[i] = reuse
        else:
            p.dataname[i] = 'sd%s_%s' % (T, p.nm(i))
            defs.append(i)
    chunks = [defs[k::files] for k in range(files)]
    mods = []
    for f, ch in enumerate(chunks):
        mod = '%sData%s%s' % (PRE, p.tag, (str(f + 1) if files > 1 else ''))
        mods.append(mod)
        out = [HEADER, 'public import PlasmaLean.Certificates.KronChebCompute\n\n']
        out.append('''/-!
# Data of the guiding-centre torus family certificate (%s resolution, part %d)

Stored Chebyshev coefficients (`SliceData`, `Certificates/KronChebCompute`) of the centres of the
%s-resolution family ball pipeline (`Design/%sEnv%s`): layout `N = %d`, `M = %d`,
Chebyshev degree `D = %d`, scale `2^{−%d}`. Generated by the untrusted oracle
`scripts/gc_kam/fam_cert.py`, `fam_emit_lean.py`; nothing here is trusted.
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb

''' % ({'H': 'high', 'L': 'low'}[p.tag], f + 1, {'H': 'high', 'L': 'low'}[p.tag], PRE, p.tag,
            p.N, p.M, p.D, p.S, NS))
        for i in ch:
            out.append('/-- Stored coefficients of the family centre `%s`. -/\n' % p.nm(i))
            out.append('def %s : List SliceData := [\n  %s]\n\n' % (
                p.dataname[i], ',\n  '.join(lean_slice(sd) for sd in p.stored[i])))
        out.append('end %s\n' % NS)
        open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mods


def kindcode(p, i):
    k = p.kind[i]
    if i == p.rIdx:
        return 4
    return {'T': 0, 'V': 1, 'C': 2, 'S': 3, 'dummy': 5}.get(k, 6)


def emit_kv(p, datamods, extra=()):
    T = p.T
    mod = '%sKv%s' % (PRE, p.tag)
    nv = p.nvar
    out = [HEADER, 'public import PlasmaLean.Certificates.KronChebCompute\n']
    out += ['public import PlasmaLean.Design.%s\n' % m for m in datamods]
    out += ['public import PlasmaLean.Design.%s\n' % m for m in extra]
    sp_list = sorted(i for i in p.special if i not in (0, 1, 2, 3))
    rI = p.rIdx
    out.append('''
/-!
# The %s-resolution layout and Kronecker images of the guiding-centre torus family certificate

Layout `N = %d`, `M = %d`, Chebyshev degree `D = %d`, scale `2^{−%d}`; for every variable: the
stored coefficients `fam%s i` (with symbol `c0%s i` and parity `odd%s i`), the weight `Wt%s i`, the
degree box `Bx%s i`, the static `ℓ¹` bound `L%s i`, the minimal widths `bMin%s i`, `wMin%s i` of
the fast images, and the Kronecker image `Kv%s b W R i` (fast: `famTB − famO`; generic: `famPack`).
Variables `0, 1, 2, 3` are `t`, `V`, `cos 2φ`, `sin 2φ`; variable `%s` is the parameter
`r = 64 + cos ϑ`; the special variables are %s. Light module (kernel checks only).
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb

/-- Layout: poloidal half width. -/
def N%s : Nat := %d
/-- Layout: toroidal half width. -/
def M%s : Nat := %d
/-- Layout: Chebyshev degree. -/
def D%s : Nat := %d
/-- Layout: scale exponent. -/
def S%s : Nat := %d
/-- Reading levels of the stored coefficients (`N_j ≤ 2^dd`, `2M_j + 1 ≤ 2^dr`, `2D + 1 ≤ 2^dw`). -/
def dd%s : Nat := %d
/-- Reading levels. -/
def dr%s : Nat := %d
/-- Reading levels. -/
def dw%s : Nat := %d

/-- The kinds of the variables: `0` = `t`, `1` = `V`, `2` = `cos 2φ`, `3` = `sin 2φ`, `4` = the
parameter `r`, `5` = zero (dummies and beyond the last variable), `6` = stored family (list). -/
def kind%sl : List Nat :=%s

/-- The kinds of the variables. -/
def kind%s (i : Nat) : Nat := kind%sl.getD i 5

''' % ({'H': 'high', 'L': 'low'}[p.tag], p.N, p.M, p.D, p.S, T, T, T, T, T, T, T, T, T,
       str(rI), ', '.join(str(i) for i in sorted(p.special)), NS,
       T, p.N, T, p.M, T, p.D, T, p.S, T, p.dd, T, p.dr, T, p.dw,
       T, lst([str(kindcode(p, i)) for i in range(nv)]), T, T))
    fl = ['[]' if i not in p.stored else p.dataname[i] for i in range(nv)]
    out.append('/-- The stored coefficients of the variables (list). -/\ndef fam%sl : List (List SliceData) :=%s\n\n'
               % (T, lst(fl)))
    out.append('/-- The stored coefficients of the variables. -/\ndef fam%s (i : Nat) : List SliceData := fam%sl.getD i []\n\n'
               % (T, T))
    out.append('/-- The symbols of the stored families (list). -/\ndef c0%sl : List Nat :=%s\n\n'
               % (T, lst([str(p.c0.get(i, 1)) for i in range(nv)])))
    out.append('/-- The symbols of the stored families. -/\ndef c0%s (i : Nat) : Nat := c0%sl.getD i 1\n\n' % (T, T))
    out.append('/-- The parities of the stored families (list). -/\ndef odd%sl : List Bool :=%s\n\n'
               % (T, lst(['true' if p.odd.get(i, False) else 'false' for i in range(nv)])))
    out.append('/-- The parities of the stored families. -/\ndef odd%s (i : Nat) : Bool := odd%sl.getD i false\n\n' % (T, T))
    out.append('/-- The weights of the variables (list). -/\ndef Wt%sl : List (Nat × Nat × Nat) :=%s\n\n'
               % (T, lst(['(%d, %d, %d)' % p.W[i] for i in range(nv)])))
    out.append('/-- The weights of the variables. -/\ndef Wt%s (i : Nat) : Nat × Nat × Nat := Wt%sl.getD i (1, 0, 0)\n\n' % (T, T))
    out.append('/-- The degree boxes of the variables (list). -/\ndef Bx%sl : List (Nat × Nat × Nat) :=%s\n\n'
               % (T, lst(['(%d, %d, %d)' % p.Bx[i] for i in range(nv)])))
    out.append('/-- The degree boxes of the variables. -/\ndef Bx%s (i : Nat) : Nat × Nat × Nat := Bx%sl.getD i (0, 0, 0)\n\n' % (T, T))
    out.append('/-- The static `ℓ¹` bounds of the variables (list). -/\ndef L%sl : List Nat :=%s\n\n'
               % (T, lst([str(p.L[i]) for i in range(nv)])))
    out.append('/-- The static `ℓ¹` bounds of the variables. -/\ndef L%s (i : Nat) : Nat := L%sl.getD i 0\n\n' % (T, T))
    out.append('/-- The minimal widths `b` of the fast images (list). -/\ndef bMin%sl : List Nat :=%s\n\n'
               % (T, lst([str(p.bmin.get(i, 0)) for i in range(nv)])))
    out.append('/-- The minimal widths `b` of the fast images. -/\ndef bMin%s (i : Nat) : Nat := bMin%sl.getD i 0\n\n' % (T, T))
    out.append('/-- The minimal widths `W` of the fast images (list). -/\ndef wMin%sl : List Nat :=%s\n\n'
               % (T, lst([str(p.wmin.get(i, 0)) for i in range(nv)])))
    out.append('/-- The minimal widths `W` of the fast images. -/\ndef wMin%s (i : Nat) : Nat := wMin%sl.getD i 0\n\n' % (T, T))
    out.append('''/-- **The Kronecker images of the variable polynomials** (`w ↦ 2^{b W R}`). -/
def Kv@T@ (b W R : Nat) (i : Nat) : Int :=
  match kind@T@ i with
  | 0 => ((1 <<< S@T@ : Nat) : Int) * ((1 <<< (b * (N@T@ + W * (M@T@ + R * D@T@))) : Nat) : Int)
  | 1 => 2 * ((1 <<< (b * W) : Nat) : Int)
  | 2 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : Nat) : Int) + 1
  | 4 =>
    ((1 <<< (S@T@ + 6) : Nat) : Int) * ((1 <<< (b * (N@T@ + W * (M@T@ + R * D@T@))) : Nat) : Int) +
      ((1 <<< (S@T@ - 1) : Nat) : Int) * (((1 <<< (b * (N@T@ + W * (M@T@ + R * (D@T@ + 1)))) : Nat) : Int) +
        ((1 <<< (b * (N@T@ + W * (M@T@ + R * (D@T@ - 1)))) : Nat) : Int))
  | 5 => 0
  | _ =>
    if bMin@T@ i ≤ b ∧ wMin@T@ i ≤ W then
      ((famTB b W R N@T@ M@T@ D@T@ (c0@T@ i) (odd@T@ i) dr@T@ dw@T@ (fam@T@ i) : Nat) : Int) -
        ((famO b W R N@T@ M@T@ D@T@ dw@T@ (fam@T@ i) : Nat) : Int)
    else famPack b W R N@T@ M@T@ D@T@ (if odd@T@ i then -1 else 1) (c0@T@ i : Int) 0 0 dd@T@ dr@T@ 0
      (fam@T@ i)

end @NS@
'''.replace('@T@', T).replace('@RI@', str(rI)).replace('@NS@', NS))
    open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mod


def emit_trees(p, kvmod):
    T = p.T
    mod = '%sTrees%s' % (PRE, p.tag)
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % kvmod]
    out.append('''
/-!
# Light expression trees of the guiding-centre torus family certificate (%s resolution)

The expression trees (`ExN`, `Certificates/KronChebCompute`) of the nodes of the
%s-resolution family ball pipeline. Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb

''' % ({'H': 'high', 'L': 'low'}[p.tag], {'H': 'high', 'L': 'low'}[p.tag], NS))
    for r in p.P['nodes']:
        if r.get('var') is not None:
            nm = 'tr%sN_%s' % (T, p.nm(r['n']))
            out.append('/-- Light tree of the node `%s` (variable `%d`). -/\n' % (p.nm(r['n']), r['n']))
        else:
            nm = 'tr%sN_%s' % (T, r['meta']['name'])
            out.append('/-- Light tree of the norm node `%s`. -/\n' % r['meta']['name'])
        out.append('def %s : ExN :=\n  %s\n\n' % (nm, wrap(tree_lean(r['tree']), 2)))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mod


def cl(c):
    return '(%d : Int)' % c if c >= 0 else '(-%d : Int)' % (-c)


def node_lines(p, r):
    T = p.T
    n = r['n']
    nm = p.nm(n)
    out = ['set_option maxRecDepth 100000 in\n',
           '/-- Kernel check of the node `%s`: truncation norm. -/\n' % nm,
           'theorem k%s_%s : node3KN S%s N%s M%s D%s Wt%s Kv%s tr%sN_%s %s %d %d %d %d %d %d %d %d %d %d %d %d ≤\n    %d := by\n  decide +kernel\n\n'
           % (T, nm, T, T, T, T, T, T, T, nm, cl(r['c']), r['dd'], r['de'], n, r['b'], r['W'], r['R'],
              r['Kw'], r['dr'], r['L'], r['fuel'], r['Ki'], r['Kj'], r['K_']),
           '/-- Kernel check of the node `%s`: a priori `ℓ¹` bound. -/\n' % nm,
           'theorem l%s_%s : nodeL1N S%s L%s tr%sN_%s %s %d %d %d < 2 ^ (%d - 1) := by\n  decide +kernel\n\n'
           % (T, nm, T, T, T, nm, cl(r['c']), r['dd'], r['de'], n, r['b'])]
    return out


def norm_lines(p, r):
    T = p.T
    tag = r['meta']['name']
    w = r['w']
    return ['set_option maxRecDepth 100000 in\n',
            '/-- Kernel check of the norm node `%s`. -/\n' % tag,
            'theorem k%s_%s : norm3KN Wt%s Kv%s N%s M%s tr%sN_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d ≤\n    %d := by\n  decide +kernel\n\n'
            % (T, tag, T, T, T, T, T, tag, w[0], w[1], w[2], r['b'], r['W'], r['R'], r['Kw'], r['dr'],
               r['L'], r['fuel'], r['Ki'], r['Kj'], r['K_']),
            '/-- Kernel check of the norm node `%s`: a priori `ℓ¹` bound. -/\n' % tag,
            'theorem l%s_%s : ExN.majN L%s tr%sN_%s < 2 ^ (%d - 1) := by\n  decide +kernel\n\n'
            % (T, tag, T, T, tag, r['b'])]


def center_lines(p, i):
    T = p.T
    r = p.normrec[i]
    nm = p.nm(i)
    return ['set_option maxRecDepth 100000 in\n',
            '/-- Kernel check of the norm of the centre `%s`. -/\n' % nm,
            'theorem c%s_%s : center3KN Kv%s N%s M%s %d %d %d %d %d %d %d %d %d %d ≤\n    %d := by\n  decide +kernel\n\n'
            % (T, nm, T, T, T, i, r['b'], r['W'], r['R'], r['Kw'], r['dr'], r['L'], r['fuel'], r['Ki'],
               r['Kj'], r['K']),
            '/-- A priori `ℓ¹` bound of the centre `%s`. -/\n' % nm,
            'theorem cl%s_%s : L%s %d < 2 ^ (%d - 1) := by\n  decide +kernel\n\n' % (T, nm, T, i, r['b'])]


def check_items(p):
    items = []
    for i in range(p.nvar):
        if i in p.stored and i in p.normrec and p.kind[i] == 'fam':
            items.append(('c', i))
    for r in p.P['nodes']:
        items.append(('n' if r.get('var') is not None else 'm', r))
    return items


def emit_checks(p, treemod, groups):
    """groups: list of lists of items (one module each)."""
    T = p.T
    mods = []
    for f, ch in enumerate(groups):
        mod = '%sCheck%s%d' % (PRE, p.tag, f + 1)
        mods.append(mod)
        out = [HEADER, 'public import PlasmaLean.Design.%s\n' % treemod]
        out.append('''
/-!
# Kernel checks of the guiding-centre torus family certificate (%s resolution, part %d)

Each theorem is one kernel evaluation (`decide +kernel`) of exact integer arithmetic on the stored
Chebyshev coefficients of `Design/%sData%s*`: the weighted digit sums (`node3KN`, `norm3KN`,
`center3KN` of `Certificates/KronChebCompute`) of the Kronecker images of the truncation polynomials
of the family ball pipeline, and their a priori `ℓ¹` bounds. Light module. Generated by
`scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section

-- check the theorems one at a time (bounded memory per process)
set_option Elab.async false

namespace %s

open PlasmaLean.Certificates.KronBallCheb

''' % ({'H': 'high', 'L': 'low'}[p.tag], f + 1, PRE, p.tag, NS))
        for kind, x in ch:
            out += center_lines(p, x) if kind == 'c' else node_lines(p, x) if kind == 'n' else norm_lines(p, x)
        out.append('end %s\n' % NS)
        open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mods


if __name__ == '__main__':
    what = sys.argv[1] if len(sys.argv) > 1 else 'data'
    for p in (H, L):
        bad = p.check_apriori()
        print(p.tag, 'a priori problems:', bad[:20])
    if what == 'data':
        dL = emit_data(L, 1)
        dH = emit_data(H, 6, shared=L)
        kL = emit_kv(L, dL)
        kH = emit_kv(H, dH, extra=dL)
        tL = emit_trees(L, kL)
        tH = emit_trees(H, kH)
        print(dL, dH, kL, kH, tL, tH)


def emit_env(p, kvmod, extra=()):
    T = p.T
    nv = p.nvar
    rI = p.rIdx
    mod = '%sEnv%s' % (PRE, p.tag)
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % kvmod,
           'public import PlasmaLean.Certificates.KronBallChebEnv\n']
    out += ['public import PlasmaLean.Design.%s\n' % m for m in extra]
    body = """
/-!
# The @RES@-resolution environment of the guiding-centre torus family certificate

The variable polynomials `P@T@ i` (three variables: `θ`-, `ψ`-modes and the Chebyshev variable
`w`), their degree boxes (`box@T@`), static `ℓ¹` bounds (`l1@T@`) and Kronecker images (`kron@T@`);
the family centres `x@T@ c i` at the parameter `w = c`; the norm bounds `B@T@ i` of the centres and
the radii `E@T@ i` of the balls (supplied by the oracle, checked in
`Design/@PRE@Check@TAG@*`).
Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace @NS@

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb PlasmaLean.Theory.KAM

/-- **The variable polynomials** of the family pipeline (by kind, `kind@T@`). -/
def P@T@ (i : ℕ) : P3 :=
  match kind@T@ i with
  | 0 => T3 S@T@ N@T@ M@T@ D@T@
  | 1 => V3
  | 2 => C cPoly
  | 3 => C sPoly
  | 4 => Pr3 S@T@ N@T@ M@T@ D@T@
  | 5 => 0
  | _ => famPoly N@T@ M@T@ D@T@ (if odd@T@ i then -1 else 1) (c0@T@ i : ℤ) 0 0 0 (fam@T@ i)

/-- The kinds are at most `6`. -/
theorem kind@T@_le (i : ℕ) : kind@T@ i ≤ 6 :=
  getD_prop (Pr := fun k : ℕ => k ≤ 6) (by decide +kernel) (by decide +kernel) i

/-- The variables beyond the last have kind `5` (zero). -/
theorem kind@T@_ge {i : ℕ} (h : @NV@ ≤ i) : kind@T@ i = 5 := by
  unfold kind@T@
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [kind@T@l]; omega)]
  rfl

/-- Stored families are below the last variable. -/
theorem lt_of_kind@T@ {i : ℕ} (h : kind@T@ i = 6) : i < @NV@ := by
  by_contra h'
  rw [kind@T@_ge (by omega)] at h
  exact absurd h (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The static conditions of the stored families. -/
theorem static@T@ : ∀ i, i < @NV@ → kind@T@ i = 6 →
    FamStatic N@T@ M@T@ D@T@ dd@T@ dr@T@ dw@T@ (fam@T@ i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The minimal widths of the fast images. -/
theorem dyn@T@ : ∀ i, i < @NV@ → kind@T@ i = 6 →
    FamDyn (bMin@T@ i) (wMin@T@ i) (c0@T@ i) (fam@T@ i) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The static `ℓ¹` bounds of the stored families. -/
theorem l1fam@T@ : ∀ i, i < @NV@ → kind@T@ i = 6 →
    famL1 N@T@ M@T@ (c0@T@ i : ℤ) 0 0 0 (fam@T@ i) ≤ L@T@ i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree boxes of the stored families. -/
theorem bx6@T@ : ∀ i, i < @NV@ → kind@T@ i = 6 → Bx@T@ i = (2 * N@T@, 2 * M@T@, 2 * D@T@) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree box and bound of `t`. -/
theorem bx0@T@ : ∀ i, i < @NV@ → kind@T@ i = 0 → Bx@T@ i = (N@T@, M@T@, D@T@) ∧ 2 ^ S@T@ ≤ L@T@ i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree box and bound of `V`. -/
theorem bx1@T@ : ∀ i, i < @NV@ → kind@T@ i = 1 → Bx@T@ i = (0, 1, 0) ∧ 2 ≤ L@T@ i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree box and bound of `cos 2φ`. -/
theorem bx2@T@ : ∀ i, i < @NV@ → kind@T@ i = 2 → Bx@T@ i = (0, 2, 0) ∧ 2 ≤ L@T@ i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree box and bound of `sin 2φ`. -/
theorem bx3@T@ : ∀ i, i < @NV@ → kind@T@ i = 3 → Bx@T@ i = (0, 2, 0) ∧ 2 ≤ L@T@ i := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The degree box and bound of the parameter. -/
theorem bx4@T@ : ∀ i, i < @NV@ → kind@T@ i = 4 →
    Bx@T@ i = (N@T@, M@T@, D@T@ + 1) ∧ 2 ^ (S@T@ + 6) + 2 * 2 ^ (S@T@ - 1) ≤ L@T@ i := by
  decide +kernel

/-- The polynomial of `t`. -/
theorem P@T@_k0 {i : ℕ} (h : kind@T@ i = 0) : P@T@ i = T3 S@T@ N@T@ M@T@ D@T@ := by
  unfold P@T@; rw [h]; rfl
/-- The polynomial of `V`. -/
theorem P@T@_k1 {i : ℕ} (h : kind@T@ i = 1) : P@T@ i = V3 := by unfold P@T@; rw [h]; rfl
/-- The polynomial of `cos 2φ`. -/
theorem P@T@_k2 {i : ℕ} (h : kind@T@ i = 2) : P@T@ i = C cPoly := by unfold P@T@; rw [h]; rfl
/-- The polynomial of `sin 2φ`. -/
theorem P@T@_k3 {i : ℕ} (h : kind@T@ i = 3) : P@T@ i = C sPoly := by unfold P@T@; rw [h]; rfl
/-- The polynomial of the parameter. -/
theorem P@T@_k4 {i : ℕ} (h : kind@T@ i = 4) : P@T@ i = Pr3 S@T@ N@T@ M@T@ D@T@ := by
  unfold P@T@; rw [h]; rfl
/-- The polynomial of a dummy variable. -/
theorem P@T@_k5 {i : ℕ} (h : kind@T@ i = 5) : P@T@ i = 0 := by unfold P@T@; rw [h]; rfl

/-- The polynomial of a stored family. -/
theorem P@T@_fam {i : ℕ} (h : kind@T@ i = 6) :
    P@T@ i = famPoly N@T@ M@T@ D@T@ (if odd@T@ i then -1 else 1) (c0@T@ i : ℤ) 0 0 0 (fam@T@ i) := by
  unfold P@T@; rw [h]; rfl

/-- The image of `t`. -/
theorem Kv@T@_k0 {b W R i : ℕ} (h : kind@T@ i = 0) : Kv@T@ b W R i =
    ((1 <<< S@T@ : ℕ) : ℤ) * ((1 <<< (b * (N@T@ + W * (M@T@ + R * D@T@))) : ℕ) : ℤ) := by
  unfold Kv@T@; rw [h]; rfl
/-- The image of `V`. -/
theorem Kv@T@_k1 {b W R i : ℕ} (h : kind@T@ i = 1) :
    Kv@T@ b W R i = 2 * ((1 <<< (b * W) : ℕ) : ℤ) := by
  unfold Kv@T@; rw [h]; rfl
/-- The image of `cos 2φ`. -/
theorem Kv@T@_k2 {b W R i : ℕ} (h : kind@T@ i = 2) :
    Kv@T@ b W R i = ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1 := by
  unfold Kv@T@; rw [h]; rfl
/-- The image of `sin 2φ`. -/
theorem Kv@T@_k3 {b W R i : ℕ} (h : kind@T@ i = 3) :
    Kv@T@ b W R i = ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1 := by
  unfold Kv@T@; rw [h]; rfl
/-- The image of the parameter. -/
theorem Kv@T@_k4 {b W R i : ℕ} (h : kind@T@ i = 4) : Kv@T@ b W R i =
    ((1 <<< (S@T@ + 6) : ℕ) : ℤ) * ((1 <<< (b * (N@T@ + W * (M@T@ + R * D@T@))) : ℕ) : ℤ) +
      ((1 <<< (S@T@ - 1) : ℕ) : ℤ) * (((1 <<< (b * (N@T@ + W * (M@T@ + R * (D@T@ + 1)))) : ℕ) : ℤ) +
        ((1 <<< (b * (N@T@ + W * (M@T@ + R * (D@T@ - 1)))) : ℕ) : ℤ)) := by
  unfold Kv@T@; rw [h]; rfl
/-- The image of a dummy variable. -/
theorem Kv@T@_k5 {b W R i : ℕ} (h : kind@T@ i = 5) : Kv@T@ b W R i = 0 := by unfold Kv@T@; rw [h]; rfl
/-- The image of a stored family (fast or generic). -/
theorem Kv@T@_k6 {b W R i : ℕ} (h : kind@T@ i = 6) : Kv@T@ b W R i =
    if bMin@T@ i ≤ b ∧ wMin@T@ i ≤ W then
      ((famTB b W R N@T@ M@T@ D@T@ (c0@T@ i) (odd@T@ i) dr@T@ dw@T@ (fam@T@ i) : ℕ) : ℤ) -
        ((famO b W R N@T@ M@T@ D@T@ dw@T@ (fam@T@ i) : ℕ) : ℤ)
    else famPack b W R N@T@ M@T@ D@T@ (if odd@T@ i then -1 else 1) (c0@T@ i : ℤ) 0 0 dd@T@ dr@T@ 0
      (fam@T@ i) := by
  unfold Kv@T@; rw [h]; rfl

/-- The kinds of a variable. -/
theorem kinds@T@ (i : ℕ) : kind@T@ i = 0 ∨ kind@T@ i = 1 ∨ kind@T@ i = 2 ∨ kind@T@ i = 3 ∨
    kind@T@ i = 4 ∨ kind@T@ i = 5 ∨ kind@T@ i = 6 := by
  have := kind@T@_le i; omega

/-- **The Kronecker images of the variable polynomials.** -/
theorem kron@T@ (b W R i : ℕ) : kron b W (flat R (P@T@ i)) = Kv@T@ b W R i := by
  rcases kinds@T@ i with h | h | h | h | h | h | h
  · rw [P@T@_k0 h, Kv@T@_k0 h, kron_flat_T3, two_pow_eq_shift]
  · rw [P@T@_k1 h, Kv@T@_k1 h]; exact kron_flat_V3 b W R
  · rw [P@T@_k2 h, Kv@T@_k2 h, flat_C]; exact kron_cPoly b W
  · rw [P@T@_k3 h, Kv@T@_k3 h, flat_C]; exact kron_sPoly b W
  · rw [P@T@_k4 h, Kv@T@_k4 h]; exact kron_flat_Pr3 S@T@ N@T@ M@T@ D@T@ b W R
  · rw [P@T@_k5 h, Kv@T@_k5 h]; simp
  · have hi := lt_of_kind@T@ h
    rw [P@T@_fam h, Kv@T@_k6 h]
    by_cases hw : bMin@T@ i ≤ b ∧ wMin@T@ i ≤ W
    · rw [ite_eq_left hw]
      exact kron_famTB (static@T@ i hi h) ((dyn@T@ i hi h).mono hw.1 hw.2) (odd@T@ i) R
    · rw [ite_eq_right hw]
      exact (famPack_eq b W R N@T@ M@T@ D@T@ _ _ 0 0 0 (fam@T@ i)
        fun sd hsd => ((static@T@ i hi h).2.2.2 sd hsd).1).symm

/-- **Degree boxes** of the variable polynomials. -/
theorem box@T@ (i : ℕ) : InBox3 (P@T@ i) (Bx@T@ i).1 (Bx@T@ i).2.1 (Bx@T@ i).2.2 := by
  by_cases hi : i < @NV@
  · rcases kinds@T@ i with h | h | h | h | h | h | h
    · rw [P@T@_k0 h, (bx0@T@ i hi h).1]; exact inBox3_T3 S@T@ N@T@ M@T@ D@T@
    · rw [P@T@_k1 h, (bx1@T@ i hi h).1]; exact inBox3_V3
    · rw [P@T@_k2 h, (bx2@T@ i hi h).1]; exact InBox3.C box_cPoly
    · rw [P@T@_k3 h, (bx3@T@ i hi h).1]; exact InBox3.C box_sPoly
    · rw [P@T@_k4 h, (bx4@T@ i hi h).1]; exact inBox3_Pr3 S@T@ N@T@ M@T@ D@T@
    · rw [P@T@_k5 h]; exact inBox3_zero _ _ _
    · rw [P@T@_fam h, bx6@T@ i hi h]
      exact inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by have := (static@T@ i hi h).2.1; omega)
  · rw [P@T@_k5 (kind@T@_ge (by omega))]
    exact inBox3_zero _ _ _

/-- **Static `ℓ¹` bounds** of the flattened variable polynomials. -/
theorem l1@T@ (R i : ℕ) : l1 (flat R (P@T@ i)) ≤ L@T@ i := by
  by_cases hi : i < @NV@
  · rcases kinds@T@ i with h | h | h | h | h | h | h
    · rw [P@T@_k0 h]; exact (l1_flat_T3 S@T@ N@T@ M@T@ D@T@ R).trans (bx0@T@ i hi h).2
    · rw [P@T@_k1 h]; exact (l1_flat_V3 R).trans (bx1@T@ i hi h).2
    · rw [P@T@_k2 h, flat_C]; exact l1_cPoly.trans (bx2@T@ i hi h).2
    · rw [P@T@_k3 h, flat_C]; exact l1_sPoly.trans (bx3@T@ i hi h).2
    · rw [P@T@_k4 h]; exact (l1_flat_Pr3 S@T@ N@T@ M@T@ D@T@ R).trans (bx4@T@ i hi h).2
    · rw [P@T@_k5 h]; simp [l1, liftN]
    · rw [P@T@_fam h]
      refine (l1_flat_famPoly_le R N@T@ M@T@ D@T@ (by split_ifs <;> simp) _ 0 0 0 (fam@T@ i)
        fun sd hsd => ((static@T@ i hi h).2.2.2 sd hsd).1.2.2.2.2).trans (l1fam@T@ i hi h)
  · rw [P@T@_k5 (kind@T@_ge (by omega))]
    simp [l1, liftN]

/-- The phases are below `4`. -/
theorem hW@T@ : ∀ i, (Wt@T@ i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by decide +kernel) (by decide +kernel)

/-- **The family centres** at the parameter `w = c`. -/
def x@T@ (c : ℂ) (i : ℕ) : FA := ctr3 S@T@ N@T@ M@T@ D@T@ c (Wt@T@ i) (P@T@ i)

/-- The centre of a stored family. -/
theorem x@T@_fam {c : ℂ} (hc : c ≠ 0) {i : ℕ} (h : kind@T@ i = 6) {p : ℕ}
    (hp : Wt@T@ i = (1, 0, p)) :
    x@T@ c i = famCtr S@T@ N@T@ M@T@ p (if odd@T@ i then -1 else 1) (c0@T@ i : ℤ) 0 0 c 0
      (fam@T@ i) := by
  have hi := lt_of_kind@T@ h
  rw [x@T@, hp, P@T@_fam h]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by have := (static@T@ i hi h).2.1; omega)

/-- The centre of `t` is `1`. -/
theorem x@T@_t {c : ℂ} (hc : c ≠ 0) : x@T@ c 0 = 1 := by
  rw [x@T@, show Wt@T@ 0 = (1, 0, 0) from rfl, show P@T@ 0 = T3 S@T@ N@T@ M@T@ D@T@ from rfl]
  exact ctr3_T3 _ _ _ _ hc

/-- The centre of `V` is `1`. -/
theorem x@T@_V (c : ℂ) : x@T@ c 1 = 1 := by
  rw [x@T@, show Wt@T@ 1 = (0, 1, 0) from rfl, show P@T@ 1 = V3 from rfl]
  exact ctr3_V3 _ _ _ _ c

/-- The centre of `cos 2φ`. -/
theorem x@T@_c (c : ℂ) : x@T@ c 2 = ctr S@T@ N@T@ M@T@ (0, 1, 3) cPoly := by
  rw [x@T@, show Wt@T@ 2 = (0, 1, 3) from rfl, show P@T@ 2 = C cPoly from rfl]
  exact ctr3_C_w0 _ _ _ _ c 1 3 cPoly

/-- The centre of `sin 2φ`. -/
theorem x@T@_s (c : ℂ) : x@T@ c 3 = ctr S@T@ N@T@ M@T@ (0, 1, 0) sPoly := by
  rw [x@T@, show Wt@T@ 3 = (0, 1, 0) from rfl, show P@T@ 3 = C sPoly from rfl]
  exact ctr3_C_w0 _ _ _ _ c 1 0 sPoly

/-- The centre of the parameter `r` is `64 + (c + c⁻¹)/2`. -/
theorem x@T@_r {c : ℂ} (hc : c ≠ 0) : x@T@ c @RI@ = algebraMap ℂ FA (64 + (c + c⁻¹) / 2) := by
  rw [x@T@, show Wt@T@ @RI@ = (1, 0, 0) from rfl, show P@T@ @RI@ = Pr3 S@T@ N@T@ M@T@ D@T@ from rfl]
  exact ctr3_Pr3 _ _ _ _ (by decide +kernel) (by decide +kernel) hc

/-- The centres of the variables of kind `5` (dummies) vanish. -/
theorem x@T@_zero (c : ℂ) {i : ℕ} (h : kind@T@ i = 5) : x@T@ c i = 0 := by
  rw [x@T@, P@T@_k5 h]
  simp [ctr3]

"""
    body = (body.replace('@T@', T).replace('@RI@', str(rI)).replace('@NS@', NS).replace('@NV@', str(nv))
            .replace('@RES@', {'H': 'high', 'L': 'low'}[p.tag]).replace('@PRE@', PRE).replace('@TAG@', p.tag))
    out.append(body)
    Bl = [qlean(p.B[i]) for i in range(nv)]
    El = [qlean(p.E[i]) for i in range(nv)]
    out.append("""/-- The norm bounds of the centres (list). -/
def B%sl : List ℚ :=%s

/-- The norm bounds of the centres. -/
def B%s (i : ℕ) : ℚ := B%sl.getD i 0

/-- The radii of the balls (list). -/
def E%sl : List ℚ :=%s

/-- The radii of the balls. -/
def E%s (i : ℕ) : ℚ := E%sl.getD i 0

end %s
""" % (T, lst(Bl), T, T, T, lst(El), T, T, NS))
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


if __name__ == '__main__' and 'env' in sys.argv:
    emit_data(L, 1)
    emit_data(H, 6, shared=L)
    print(emit_env(L, '%sKvL' % PRE), emit_env(H, '%sKvH' % PRE))


if __name__ == '__main__' and 'checktest' in sys.argv:
    names = sys.argv[sys.argv.index('checktest') + 1].split(',')
    p = H if sys.argv[sys.argv.index('checktest') + 2] == 'H' else L
    items = []
    for nmx in names:
        if nmx.startswith('c:'):
            items.append(('c', [i for i in range(p.nvar) if p.nm(i) == nmx[2:]][0]))
        else:
            r = [r for r in p.P['nodes'] if (r['name'] == nmx)][0]
            items.append(('n' if r.get('var') is not None else 'm', r))
    T = p.T
    out = [HEADER, 'public import PlasmaLean.Design.%sTrees%s\n\n@[expose] public section\n\nnamespace %s\n\nopen PlasmaLean.Certificates.KronBallCheb\n\n' % (PRE, p.tag, NS)]
    for kind, x in items:
        lines = center_lines(p, x) if kind == 'c' else node_lines(p, x) if kind == 'n' else norm_lines(p, x)
        out += [l.replace('set_option maxRecDepth 100000 in\n', 'set_option maxRecDepth 100000 in\nset_option profiler true in\n') for l in lines]
    out.append('end %s\n' % NS)
    open(OUT + 'TestFamCheck.lean', 'w').write(''.join(out))


# ---------------------------------------------------------------- relations
DPDL = ', '.join(['dpd0_D', 'dpd1_D', 'dpd0_nR', 'dpd1_nR', 'dpd0_nZ', 'dpd1_nZ'] +
                 ['dpd_%s_%s' % (b, k) for b in ['D', 'nR', 'nZ'] for k in ['uu', 'uz', 'zu', 'zz', 'phu', 'phz']] +
                 ['dpd0_P', 'dpd1_P'])
S0 = ('Ex.eval, toEx, XL, Int.cast_ofNat, Int.cast_one, Int.cast_neg, pdS, pd, KL, xB, Matrix.cons_val_zero, '
      'Matrix.cons_val_one, Matrix.head_cons, PolyExprS.eval, PolyExprS.eval_ofPoly, PolyExprS.deriv, '
      'PolyExprS.deriv_ofPoly, deriv_eV, single_00, single_10, map_one, ' + DPDL)
EVALS = ("eval_add', eval_sub', eval_mul, eval_neg', eval_pow', eval_one, eval_ofNat', eval_zero', "
         "eval_algebraMap, eval_smul', eval_polyExpr, Complex.ofReal_div, Complex.ofReal_one, "
         "Complex.ofReal_ofNat, Complex.ofReal_mul")

# new low-resolution values (index -> Lean expression in c u z)
XNEW_L = {
    'r': 'algebraMap ℂ FA (((16384 * ρF c : ℝ)) : ℂ)',
    'YDt': 'PolyExprS.eval (KL u z) eW3 * PolyExprS.eval (KL u z) eKD',
    'DtF': 'PolyExprS.eval (KL u z) (gcD (ρF c))',
    'YnRt': 'PolyExprS.eval (KL u z) eW3 * PolyExprS.eval (KL u z) eKR',
    'nRtF': 'PolyExprS.eval (KL u z) (gcNR (ρF c))',
    'YnZt': 'PolyExprS.eval (KL u z) eW3 * PolyExprS.eval (KL u z) eKZ',
    'nZtF': 'PolyExprS.eval (KL u z) (gcNZ (ρF c))',
    'PtorF': '(gcFlow (ρF c)).Pof u z',
    'Dt3F': 'PolyExprS.eval (KL u z) (gcD (ρF c)) ^ 3',
    'FF': 'PolyExprS.eval (KL u z) (gcD (ρF c)) ^ 3 * W0of u z ^ 2',
    'qiF': 'xLF c 136',
    'YF': '(1 + u) ^ 3 * (gcFlow (ρF c)).Pof u z * xLF c 136',
    'V0': 'xLF c 62',
    'Uo': 'xL 4', 'Zo': 'xL 5', 'Ao': 'dTh (xL 4)', 'Bo': 'dTh (xL 5)',
}
for nm, ph, K in [('Dtu', 0, 'KD'), ('Dtz', 1, 'KD'), ('nRtu', 0, 'KR'), ('nRtz', 1, 'KR'), ('nZtu', 0, 'KZ'),
                  ('nZtz', 1, 'KZ')]:
    XNEW_L['Y' + nm] = ('PolyExprS.deriv (KL u z) (Pi.single %d 1) eW3 * PolyExprS.eval (KL u z) e%s + '
                        'PolyExprS.eval (KL u z) eW3 * PolyExprS.deriv (KL u z) (Pi.single %d 1) e%s' % (ph, K, ph, K))
    base = {'Dt': 'gcD', 'nRt': 'gcNR', 'nZt': 'gcNZ'}[nm[:-1]]
    XNEW_L[nm + 'F'] = 'pdS (KL u z) %d (%s (ρF c))' % (ph, base)
EXTRA_L = {'DtF': ['gcD'], 'nRtF': ['gcNR'], 'nZtF': ['gcNZ'], 'Dt3F': ['gcD'], 'FF': ['gcD', 'W0of'],
           'PtorF': ['FlowFieldS.Pof', 'FlowFieldS.Dof', 'gcFlow'], 'YF': ['FlowFieldS.Pof', 'FlowFieldS.Dof', 'gcFlow'],
           'DtuF': ['gcD'], 'DtzF': ['gcD'], 'nRtuF': ['gcNR'], 'nRtzF': ['gcNR'], 'nZtuF': ['gcNZ'], 'nZtzF': ['gcNZ']}

OLDL = pickle.load(open('/tmp/gcw/gc_cert.pkl', 'rb'))['L']
OLDL_NODES = {r['n']: r for r in OLDL['nodes'] if r.get('var') is not None}


def emit_rel_L(p, treemod, envmod):
    T = p.T
    mod = '%sRel%s' % (PRE, p.tag)
    nv = p.nvar
    spl = sorted(p.dummies + [i for i in range(nv) if p.nm(i) == 'V0'] +
                 [i for i in range(nv) if i >= 114])
    spl_short = sorted(i for i in spl if i < 114)
    out = [HEADER, 'public import PlasmaLean.Certificates.BoolCert\n', 'public import PlasmaLean.Design.%s\n' % treemod, 'public import PlasmaLean.Design.%s\n' % envmod,
           'public import PlasmaLean.Design.RationalStellaratorGCTorusRelL\n']
    out.append('''
/-!
# True values of the low-resolution family pipeline of the guiding-centre torus

The value `XLF c u z i` of each variable of the low-resolution family ball pipeline at the
parameter `w = c` (`ρ = ρF c = (64 + Re c)/2^14`) and a torus `(u, z)`: the values `XL u z i` of
the `ρ = 1/256` pipeline (`Design/RationalStellaratorGCTorusRelL`) for the variables that do not
depend on `ρ`, and the parameter `r = 2^14 ρ`, the guiding-centre corrections and the
guiding-centre flow form at `ρF c` for the new variables. The identity of every node,
`c' · X n = eval X e` (`relLF_*`): by congruence from `relL_*` for the `ρ`-independent nodes
(`rel_congr`), proved pointwise on the torus (`ext_eval`) by `ring` for the new ones.
Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb WEll1Z2 Complex PolyExpr
  PlasmaLean.Certificates.BoolCert

/-- **The parameter of the family** at `w = c`: `ρ = (64 + Re c)/2^14` (for `c = e^{iϑ}`:
`ρ = (64 + cos ϑ)/16384`, in `[63/16384, 65/16384]`). -/
def ρF (c : ℂ) : ℝ := (64 + c.re) / 16384

/-- `c ≠ 0` on the unit circle. -/
theorem ne_zero_of_norm_one {c : ℂ} (hc : ‖c‖ = 1) : c ≠ 0 := by
  rintro rfl; simp at hc

/-- **The parameter at `w = c`** (`|c| = 1`): `2^14 ρF c = 64 + (c + c⁻¹)/2`. -/
theorem param_eq {c : ℂ} (hc : ‖c‖ = 1) : (((16384 * ρF c : ℝ)) : ℂ) = 64 + (c + c⁻¹) / 2 := by
  have h1 : c⁻¹ = (starRingEnd ℂ) c := by
    rw [Complex.inv_def, ← Complex.sq_norm, hc]; simp
  rw [h1, Complex.add_conj, ρF]
  push_cast
  ring

/-- The variables of the family pipeline whose values differ from the `ρ = 1/256` pipeline. -/
def sp%s (j : ℕ) : Bool :=
  decide (j ∈ (%s : List ℕ)) || decide (114 ≤ j)

/-- The values of the new variables. -/
def X%snew (c : ℂ) (u z : FA) : ℕ → FA
''' % (NS, T, wrap('[' + ', '.join(str(i) for i in spl_short) + ']', 2), T))
    for i in range(nv):
        if i in spl and p.kind[i] != 'dummy':
            out.append('  | %d => %s\n' % (i, wrap(XNEW_L[p.nm(i)], 8)))
    out.append('  | _ => 0\n\n')
    out.append('''/-- **The true values of the low-resolution family pipeline** at the parameter `w = c` and the
torus `(u, z)`. -/
def X@T@ (c : ℂ) (u z : FA) (j : ℕ) : FA := if sp@T@ j = true then X@T@new c u z j else XL u z j

/-- The values of the `ρ`-independent variables. -/
theorem X@T@_old (c : ℂ) (u z : FA) {j : ℕ} (h : sp@T@ j = false) : X@T@ c u z j = XL u z j := by
  simp [X@T@, h]

/-- The values of the new variables. -/
theorem X@T@_new (c : ℂ) (u z : FA) {j : ℕ} (h : sp@T@ j = true) : X@T@ c u z j = X@T@new c u z j := by
  simp [X@T@, h]

/-- Congruence with the `ρ = 1/256` values. -/
theorem X@T@_congr (c : ℂ) (u z : FA) : ∀ j, (!sp@T@ j) = true → X@T@ c u z j = XL u z j :=
  fun _ h => X@T@_old c u z (by simpa using h)

'''.replace('@T@', T))
    # relations
    for r in p.P['nodes']:
        if r.get('var') is None:
            continue
        n = r['n']
        nm = p.nm(n)
        c = r['c']
        cl = '((%d : ℤ) : ℂ)' % c if c >= 0 else '((-%d : ℤ) : ℂ)' % (-c)
        o = OLDL_NODES.get(n)
        if o is not None and o['tree'] == r['tree'] and o['c'] == c and n not in spl:
            out.append('''set_option maxRecDepth 100000 in
/-- The identity of the node `%s` (from the `ρ = 1/256` pipeline). -/
theorem rel%s_%s (c : ℂ) (u z : FA) :
    %s • X%s c u z %d = Ex.eval (X%s c u z) (toEx tr%sN_%s) :=
  rel_congr (X%s_congr c u z) (by bool_cert) (X%s_old c u z (j := %d) rfl) (relL_%s u z)

''' % (nm, T, nm, cl, T, n, T, T, nm, T, T, n, OLDL['names'][n].replace("'", "p")))
        else:
            vs = sorted(tree_vars(r['tree']) | {n})
            facts = []
            for v in vs:
                if v in spl:
                    facts.append('X%s_new c u z (j := %d) rfl' % (T, v))
                else:
                    facts.append('X%s_old c u z (j := %d) rfl' % (T, v))
            extra = EXTRA_L.get(nm, [])
            out.append('''set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
/-- The identity of the node `%s`. -/
theorem rel%s_%s (c : ℂ) (u z : FA) :
    %s • X%s c u z %d = Ex.eval (X%s c u z) (toEx tr%sN_%s) := by
  simp only [%s]
  simp only [%s]
  refine ext_eval fun θ ψ => ?_
  simp only [%s]
  ring

''' % (nm, T, nm, cl, T, n, T, T, nm,
       wrap('tr%sN_%s, toEx, Ex.eval, ' % (T, nm) + ', '.join(facts), 13),
       wrap('X%snew, ' % T + S0 + ''.join(', ' + x for x in extra), 13),
       wrap(EVALS, 13)))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


if __name__ == '__main__' and 'relL' in sys.argv:
    print(emit_rel_L(L, '%sTreesL' % PRE, '%sEnvL' % PRE))


XSPEC_H = {'LRx': '(2 : ℂ) ^ 96 • Lt KamTorusA.iota (xHF c 4)', 'LZx': '(2 : ℂ) ^ 96 • Lt KamTorusA.iota (xHF c 5)',
           'thU': 'dTh (xHF c 4)', 'thZ': 'dTh (xHF c 5)', 'Ue': 'xLF c 4', 'Ze': 'xLF c 5',
           'thUe': 'dTh (xLF c 4)', 'thZe': 'dTh (xLF c 5)', 'V0': 'xHF c 52', 'V2': 'xHF c 52 ^ 2'}


def hl_maps(ph, pl):
    Ln = {pl.names[i]: i for i in range(pl.nvar)}
    lmap = {}
    for i in range(ph.nvar):
        nm = ph.names[i]
        if nm in Ln and ph.kind[i] != 'dummy' and nm != 'V0':
            lmap[i] = Ln[nm]
    hmap = {v: k for k, v in lmap.items()}
    return lmap, hmap


def emit_rel_H(p, pl, treemod, extra):
    T = p.T
    mod = '%sRel%s' % (PRE, p.tag)
    nv = p.nvar
    lmap, hmap = hl_maps(p, pl)
    out = [HEADER, 'public import PlasmaLean.Certificates.BoolCert\n', 'public import PlasmaLean.Design.%s\n' % treemod]
    out += ['public import PlasmaLean.Design.%s\n' % m for m in extra]
    out.append('''
/-!
# True values of the high-resolution family pipeline of the guiding-centre torus

The value `XHF c i` of each variable of the high-resolution family ball pipeline at the parameter
`w = c`: for the variables shared with the low-resolution pipeline, the low-resolution values
`XLF c u z (lmapHF i)` at the family torus `(u, z) = (xHF c 4, xHF c 5)`; for the others, the
transport inputs `2^96 𝓛u`, the derivatives, the embedded low-resolution torus and the node data.
The identity of every node (`relHF_*`) is the identity of the low-resolution node with renamed
variables (`rel_rename`). Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb WEll1Z2 Complex PolyExpr
  PlasmaLean.Certificates.BoolCert

/-- The low-resolution index of a shared variable (list). -/
def lmap%sl : List ℕ :=%s

/-- The low-resolution index of a shared variable. -/
def lmap%s (i : ℕ) : ℕ := lmap%sl.getD i 0

/-- The high-resolution index of a low-resolution variable (list). -/
def hmap%sl : List ℕ :=%s

/-- The high-resolution index of a low-resolution variable. -/
def hmap%s (j : ℕ) : ℕ := hmap%sl.getD j 0

/-- The shared variables (list). -/
def rel%sl : List Bool :=%s

/-- The shared variables. -/
def rel%s (i : ℕ) : Bool := rel%sl.getD i false

/-- The values of the variables of the high-resolution pipeline only. -/
def X%sspec (c : ℂ) : ℕ → FA
''' % (NS, T, lst([str(lmap.get(i, 0)) for i in range(nv)]), T, T,
       T, lst([str(hmap.get(j, 0)) for j in range(pl.nvar)]), T, T,
       T, lst(['true' if i in lmap else 'false' for i in range(nv)]), T, T, T))
    for i in range(nv):
        if i not in lmap and p.kind[i] != 'dummy':
            out.append('  | %d => %s\n' % (i, XSPEC_H[p.nm(i)]))
    out.append('  | _ => 0\n\n')
    out.append('''/-- **The true values of the high-resolution family pipeline** at the parameter `w = c`. -/
def X@T@ (c : ℂ) (i : ℕ) : FA :=
  if rel@T@ i = true then XLF c (x@T@ c 4) (x@T@ c 5) (lmap@T@ i) else X@T@spec c i

/-- The values of the shared variables. -/
theorem X@T@_rel (c : ℂ) {i : ℕ} (h : rel@T@ i = true) :
    X@T@ c i = XLF c (x@T@ c 4) (x@T@ c 5) (lmap@T@ i) := by
  simp [X@T@, h]

/-- The values of the other variables. -/
theorem X@T@_spec (c : ℂ) {i : ℕ} (h : rel@T@ i = false) : X@T@ c i = X@T@spec c i := by
  simp [X@T@, h]

/-- The low-resolution variables whose renaming is shared. -/
def p@T@ (j : ℕ) : Bool := rel@T@ (hmap@T@ j) && (lmap@T@ (hmap@T@ j) == j)

/-- The values at renamed variables. -/
theorem X@T@_hmap (c : ℂ) :
    ∀ j, p@T@ j = true → X@T@ c (hmap@T@ j) = XLF c (x@T@ c 4) (x@T@ c 5) j := by
  intro j h
  simp only [p@T@, Bool.and_eq_true, beq_iff_eq] at h
  rw [X@T@_rel c h.1, h.2]

'''.replace('@T@', T))
    Lnodes = {r['n']: r for r in pl.P['nodes'] if r.get('var') is not None}
    for r in p.P['nodes']:
        if r.get('var') is None:
            continue
        n = r['n']
        nm = p.nm(n)
        c = r['c']
        cl = '((%d : ℤ) : ℂ)' % c if c >= 0 else '((-%d : ℤ) : ℂ)' % (-c)
        if n in lmap:
            m = lmap[n]
            lnm = pl.nm(m)
            out.append('''set_option maxRecDepth 100000 in
/-- The identity of the node `%s` (renamed from the low-resolution node `%s`). -/
theorem rel%s_%s (c : ℂ) :
    %s • X%s c %d = Ex.eval (X%s c) (toEx tr%sN_%s) :=
  rel_rename (X%s_hmap c) (eL := trLFN_%s) rfl (by bool_cert) (X%s_rel c (i := %d) rfl)
    (relLF_%s c (x%s c 4) (x%s c 5))

''' % (nm, lnm, T, nm, cl, T, n, T, T, nm, T, lnm, T, n, lnm, T, T))
        else:
            vs = sorted(tree_vars(r['tree']) | {n})
            facts = ['X%s_spec c (i := %d) rfl' % (T, v) for v in vs]
            out.append('''/-- The identity of the node `%s`. -/
theorem rel%s_%s (c : ℂ) :
    %s • X%s c %d = Ex.eval (X%s c) (toEx tr%sN_%s) := by
  simp only [%s]
  simp only [X%sspec, Int.cast_one, one_smul]
  ring

''' % (nm, T, nm, cl, T, n, T, T, nm, wrap('tr%sN_%s, toEx, Ex.eval, ' % (T, nm) + ', '.join(facts), 13), T))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


if __name__ == '__main__' and 'relH' in sys.argv:
    print(emit_rel_H(H, L, '%sTreesH' % PRE, ['%sEnvH' % PRE, '%sRelL' % PRE, 'KamTorusA']))


# ---------------------------------------------------------------- chains
def derived_info(p):
    """i -> (j, alpha, beta) for the derivatives stored as data."""
    info = {}
    for i, (s_, c0, a, bb) in p.derived.items():
        cand = [j for j in range(p.nvar) if j in p.stored and j not in p.derived and
                same_slices(p.fam[j]['slices'], p.fam[i]['slices']) and p.fam[j]['sym'][1] == 0]
        j = cand[0]
        c0j = p.c0[j]
        assert a % c0j == 0 and bb % c0j == 0
        assert (p.W[j][2] + 3) % 4 == p.W[i][2], (i, j)
        assert p.fam[j]['s'] == s_
        info[i] = (j, a // c0j, bb // c0j)
    return info


def derived_lines(p):
    T = p.T
    out = []
    for i, (j, al, be) in sorted(derived_info(p).items()):
        nm, src = p.nm(i), p.nm(j)
        s_, c0, a, bb = p.derived[i]
        W = 2 * p.N + 1
        R = 2 * p.M + 1
        d = clog2(W * (2 * p.M + R * 2 * p.D + 1))
        lsym = famL1(p.fam[i]['slices'], p.N, p.M, 0, a, bb)
        b = max(clog2(p.L[i] + lsym + 1) + 2, p.bmin[i])
        assert p.wmin[i] <= W
        fam = 'famPoly N%s M%s D%s (if odd%s %d then -1 else 1) 0\n    ((c0%s %d : ℤ) * %d) ((c0%s %d : ℤ) * %d) 0 (fam%s %d)' % (
            T, T, T, T, j, T, j, al, T, j, be, T, j)
        out.append('''set_option maxRecDepth 100000 in
/-- Kernel check: the stored derivative `%s` and the symbol family of `%s` have the same
Kronecker image. -/
theorem kder%s_%s : Kv%s %d %d %d %d = famPack %d %d %d N%s M%s D%s (if odd%s %d then -1 else 1) 0
    ((c0%s %d : ℤ) * %d) ((c0%s %d : ℤ) * %d) dd%s dr%s 0 (fam%s %d) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The stored derivative `%s` is the symbol family of `%s` (equal Kronecker images). -/
theorem P%s_der_%s : P%s %d = %s := by
  have hk : kron %d %d (flat %d (P%s %d)) = kron %d %d (flat %d (%s)) := by
    rw [kron%s, ← famPack_eq %d %d %d N%s M%s D%s _ _ _ _ 0 (fam%s %d)
      fun sd h => ((static%s %d (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1]
    exact kder%s_%s
  have hbox := box%s %d
  rw [bx6%s %d (by decide +kernel) (by decide +kernel)] at hbox
  refine eq_of_kron_flat (b := %d) (W := %d) (R := %d) (d := %d) (by norm_num) hbox
    (inBox3_famPoly _ _ _ _ _ _ _ 0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ?_ hk
  refine lt_of_le_of_lt (add_le_add (l1%s %d %d) (l1_flat_famPoly_le %d N%s M%s D%s
    (by decide +kernel) _ _ _ 0 _
    fun sd h => ((static%s %d (by decide +kernel) (by decide +kernel)).2.2.2 sd h).1.2.2.2.2))
    (by decide +kernel)

/-- The centre `%s` is a derivative of the centre `%s`. -/
theorem x%s_der_%s {c : ℂ} (hc : c ≠ 0) :
    x%s c %d = dS ((%d : ℤ) : ℂ) ((%d : ℤ) : ℂ) (x%s c %d) := by
  rw [x%s_fam hc (i := %d) rfl (p := %d) rfl, dS_famCtr, x%s, P%s_der_%s,
    show Wt%s %d = (1, 0, (%d + 3) %% 4) from rfl]
  exact ctr3_famPoly _ _ _ _ _ _ _ _ _ hc 0 _ (by decide +kernel)

''' % (nm, src, T, nm, T, b, W, R, i, b, W, R, T, T, T, T, j, T, j, al, T, j, be, T, T, T, j,
       nm, src, T, nm, T, i, fam, b, W, R, T, i, b, W, R, fam, T, b, W, R, T, T, T, T, j, T, j, T, nm,
       T, i, T, i, b, W, R, d, T, R, i, R, T, T, T, T, j,
       nm, src, T, nm, T, i, al, be, T, j, T, j, p.W[j][2], T, T, nm, T, i, p.W[j][2]))
    return out


def tq_args(p):
    T = p.T
    t = '{r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1)'
    use = 'hr hq hc'
    if p.tag == 'L':
        t += (' {u z : FA}\n    (hU : Bd r (u - xLF c 4) (ELF 4)) (hZ : Bd r (z - xLF c 5) (ELF 5))\n'
              '    (hA : Bd r (dTh u - xLF c 6) (ELF 6)) (hB : Bd r (dTh z - xLF c 7) (ELF 7))')
        use += ' hU hZ hA hB'
    X = 'XHF c' if p.tag == 'H' else 'XLF c u z'
    return t, use, X


def rq(x):
    from ballcert import up
    return up(Fr(x), 4)


def norm_call(p, r, Rq, hn, hE):
    T = p.T
    tag = r['meta']['name']
    w = r['w']
    return ('norm3_fullN hr hq hc hW%s box%s (l1%s %d) (fun _ => rfl) %s %s tr%sN_%s (%d, %d, %d)\n'
            '      %d %d %d %d %d %d %d %d %d %d %d %d\n      %s (kron%s %d %d %d) (by decide +kernel)\n'
            '      (by decide +kernel) (by decide +kernel) l%s_%s k%s_%s (by decide +kernel)'
            % (T, T, T, r['R'], hn, hE, T, tag, w[0], w[1], w[2], r['A'], r['J'], r['K'], r['b'], r['W'],
               r['Kw'], r['dr'], r['L'], r['fuel'], r['Ki'], r['Kj'], r['K_'], qlean(Rq), T, r['b'], r['W'],
               r['R'], T, tag, T, tag))


def emit_chain(p, checkmods, relmod, extra=()):
    T = p.T
    nv = p.nvar
    targs, use, X = tq_args(p)
    mod = '%sChain%s' % (PRE, p.tag)
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % relmod]
    out += ['public import PlasmaLean.Design.%s\n' % m for m in checkmods]
    out += ['public import PlasmaLean.Design.%s\n' % m for m in extra]
    out.append('public import PlasmaLean.Design.RationalStellaratorGCTorusCommon\n')
    out.append('''
/-!
# The %s-resolution ball chain of the guiding-centre torus family

The balls `‖X c i − x c i‖_r ≤ E i` of all variables of the %s-resolution family pipeline,
for every parameter `|c| = 1` and every strip `r ≥ 0` with `e^r ≤ 74315/2^16`%s, built
variable by variable (`ball%s_k`, `chain_succ`) from the kernel checks of
`Design/%sCheck%s*` (`node3_fullN`), the node identities of
`Design/%s` and the node step `vstep`.
Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

''' % ({'H': 'high', 'L': 'low'}[p.tag], {'H': 'high', 'L': 'low'}[p.tag],
       ',\nand every torus `(u, z)` within the input radii of the family torus' if p.tag == 'L' else '',
       T, PRE, p.tag, relmod, NS))
    out += derived_lines(p)
    dinfo = derived_info(p)
    hc0 = '(ne_zero_of_norm_one hc)'
    # equalities X = x for the exact variables
    eqs = {}
    for i in range(nv):
        k = p.kind[i]
        mk = p.meta.get(i, {}).get('kind')
        nm = p.nm(i)
        pf = None
        if i == 0:
            pf = 'rw [x%s_t %s]; rfl' % (T, hc0)
        elif i == 1:
            pf = 'rw [x%s_V]; rfl' % T
        elif i == 2:
            pf = 'rw [x%s_c, ctr_cPoly]; rfl' % T
        elif i == 3:
            pf = 'rw [x%s_s, ctr_sPoly]; rfl' % T
        elif k == 'dummy':
            pf = 'rw [x%s_zero c (i := %d) rfl]; rfl' % (T, i)
        elif i == p.rIdx:
            if p.tag == 'H':
                pf = ('rw [XHF_rel c (i := %d) rfl]\n  change XLF c (xHF c 4) (xHF c 5) 114 = _\n'
                      '  rw [XLF_new c _ _ (j := 114) rfl]\n'
                      '  change algebraMap ℂ FA (((16384 * ρF c : ℝ)) : ℂ) = _\n  rw [xHF_r %s, param_eq hc]' % (i, hc0))
            else:
                pf = ('rw [XLF_new c _ _ (j := 114) rfl]\n'
                      '  change algebraMap ℂ FA (((16384 * ρF c : ℝ)) : ℂ) = _\n  rw [xLF_r %s, param_eq hc]' % hc0)
        elif mk in ('input', 'data'):
            pf = 'rfl' if p.tag == 'H' else 'rw [XLF_new c _ _ (j := %d) rfl]; rfl' % i
        elif mk == 'derived' and p.tag == 'H':
            j, al, be = dinfo[i]
            if p.nm(j) in ('Ue', 'Ze'):
                pf = ('rw [XHF_spec c (i := %d) rfl, xHF_der_%s %s, xHF_embed_%s %s]\n'
                      '  simp [XHFspec, dTh]' % (i, nm, hc0, p.nm(j), hc0))
            else:
                pf = 'rw [XHF_spec c (i := %d) rfl, xHF_der_%s %s]\n  simp [XHFspec, dTh]' % (i, nm, hc0)
        elif mk == 'embed':
            pf = 'rw [XHF_spec c (i := %d) rfl, xHF_embed_%s %s]; rfl' % (i, nm, hc0)
        elif mk == 'old':
            pf = 'rw [XLF_new c _ _ (j := %d) rfl, xLF_old_%s %s]; rfl' % (i, nm, hc0)
        elif mk == 'oldd':
            j, al, be = dinfo[i]
            pf = ('rw [XLF_new c _ _ (j := %d) rfl, xLF_der_%s %s, xLF_old_%s %s]\n  simp [XLFnew, dTh]'
                  % (i, nm, hc0, p.nm(j), hc0))
        if pf is not None:
            eqs[i] = pf
    if p.tag == 'H':
        for nm, i, j in [('Ue', 10, 4), ('Ze', 11, 5)]:
            out.append('''/-- The embedded low-resolution family centre `%s`. -/
theorem xHF_embed_%s {c : ℂ} (hc : c ≠ 0) : xHF c %d = xLF c %d := by
  rw [xHF_fam hc (i := %d) rfl (p := %d) rfl, xLF_fam hc (i := %d) rfl (p := %d) rfl]
  exact famCtr_embed SLF NLF MLF %d (NHF - NLF) (MHF - MLF) (SHF - SLF) _ c 0 (famLF %d)
    (by decide +kernel)

''' % (nm, nm, i, j, i, H.W[i][2], j, L.W[j][2], H.W[i][2], j))
    if p.tag == 'L':
        for nm, i, src in [('Uo', 138, 'gL_U'), ('Zo', 139, 'gL_Z')]:
            pp = p.W[i][2]
            out.append('''set_option maxRecDepth 100000 in
/-- The stored `ρ = 1/256` low-resolution centre `%s` is the old centre. -/
theorem xLF_old_%s {c : ℂ} (hc : c ≠ 0) : xLF c %d = xL %d := by
  rw [xLF_fam hc (i := %d) rfl (p := %d) rfl,
    show famLF %d = [(famLF %d).getD 0 SliceData.zero] from rfl, famCtr_single]
  have hg : ∀ i, i ≤ 2 * NLF → ∀ j, j ≤ 2 * MLF → sliceG NLF MLF (if oddLF %d then -1 else 1)
      (c0LF %d : ℤ) 0 0 ((famLF %d).getD 0 SliceData.zero) i j = %s i j := by
    decide +kernel
  rw [gridPolyNM_congr fun i j hi hj => hg i hi j hj]
  rfl

''' % (nm, nm, i, i - 134, i, pp, i, i, i, i, i, src))
    for i, pf in sorted(eqs.items()):
        out.append('set_option linter.unusedVariables false in\n/-- The variable `%s` is exact. -/\ntheorem %s_eq_%s %s :\n    %s %d = x%s c %d := by\n  %s\n\n'
                   % (p.nm(i), 'X' + T, p.nm(i), '{c : ℂ} (hc : ‖c‖ = 1)' + (' (u z : FA)' if p.tag == 'L' else ''),
                      X, i, T, i, pf))
    # norms of the centres
    out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
               'set_option exponentiation.threshold 4096 in\n/-- **Norms of the centres.** -/\ntheorem norm%s {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) '
               '{c : ℂ} (hc : ‖c‖ = 1) :\n    ∀ i, i < %d → Bd r (x%s c i) (B%s i)\n' % (T, nv, T, T))
    for i in range(nv):
        k = p.kind[i]
        if i == 0:
            out.append('  | 0, _ => by rw [x%s_t %s]; exact (Bd_one r).le (by norm_num [B%s, B%sl])\n' % (T, hc0, T, T))
        elif i == 1:
            out.append('  | 1, _ => by rw [x%s_V]; exact (Bd_one r).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
        elif i == 2:
            out.append('  | 2, _ => by rw [x%s_c, ctr_cPoly]; exact (Bd_cS_q hq).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
        elif i == 3:
            out.append('  | 3, _ => by rw [x%s_s, ctr_sPoly]; exact (Bd_sS_q hq).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
        elif k == 'dummy':
            out.append('  | %d, _ => by rw [x%s_zero c (i := %d) rfl]; exact (Bd_zero r).le (by norm_num [B%s, B%sl])\n'
                       % (i, T, i, T, T))
        else:
            r = p.normrec[i]
            out.append('  | %d, _ => center3_fullN hq hc box%s (l1%s %d) (fun _ => rfl) %d %d %d %d %d %d %d %d %d %d\n'
                       '      %d (B%s %d) (kron%s %d %d %d) rfl (by decide +kernel) cl%s_%s c%s_%s (by decide +kernel)\n'
                       % (i, T, T, r['R'], i, p.W[i][2], r['b'], r['W'], r['Kw'], r['dr'], r['L'], r['fuel'],
                          r['Ki'], r['Kj'], r['K'], T, i, T, r['b'], r['W'], r['R'], T, p.nm(i), T, p.nm(i)))
    out.append('  | n + %d, h => absurd h (by omega)\n\n' % nv)
    # the node step
    vk = [k_ for k_ in range(nv) if p.meta.get(k_, {}).get('kind') == 'vnode'][0]
    v0 = [k_ for k_ in range(nv) if p.nm(k_) == 'V0'][0]
    Ei = [k_ for k_ in range(nv) if p.nm(k_) == 'E'][0]
    nn = {r['meta']['name']: r for r in p.norms}
    vs = p.vstep
    hyps = '(hE : ∀ i, i < %d → Bd r (%s i - x%s c i) (E%s i))' % (vk, X, T, T)
    out.append('set_option linter.unusedVariables false in\nset_option linter.style.longLine false in\n'
               'set_option maxRecDepth 100000 in\nset_option exponentiation.threshold 4096 in\n'
               '/-- The node step: the ball of `(1 + E)^{−1/2}`. -/\n'
               'theorem vnode%s %s\n    %s :\n    Bd r (%s %d - x%s c %d) (E%s %d) := by\n' % (T, targs, hyps, X, vk, T, vk, T, vk))
    out.append('  have hn : ∀ i, i < %d → Bd r (x%s c i) (B%s i) := fun i hi => norm%s hq hc i (by omega)\n' % (vk, T, T, T))
    for nmn, R_, h in [('Vm1', vs['Ra'], 'h1'), ('V2m1', vs['Rn2'], 'h2'), ('eta', vs['Reta'], 'h3')]:
        out.append('  have %s := %s\n' % (h, norm_call(p, nn[nmn], R_, 'hn', 'hE')))
    xe = lambda i: ('X%s_eq_%s hc' % (T, p.nm(i))) + (' u z' if p.tag == 'L' else '')
    one = 'x%s_t %s' % (T, hc0)
    if p.tag == 'H':
        v2 = 53
        out.append('  have e1 : Ex.eval (XHF c) (toEx trHFN_Vm1) = xHF c %d - 1 := by\n'
                   '    simp only [trHFN_Vm1, toEx, Ex.eval, %s, %s, %s]\n' % (v0, xe(v0), xe(0), one))
        out.append('  have e2 : Ex.eval (XHF c) (toEx trHFN_V2m1) = xHF c %d ^ 2 - 1 := by\n'
                   '    simp only [trHFN_V2m1, toEx, Ex.eval, XHF_spec c (i := %d) rfl, XHFspec, %s, %s]\n'
                   % (v0, v2, xe(0), one))
        out.append('  have e3 : Ex.eval (XHF c) (toEx trHFN_eta) = xHF c %d ^ 2 * (1 + XHF c %d) - 1 := by\n'
                   '    simp only [trHFN_eta, toEx, Ex.eval, XHF_spec c (i := %d) rfl, XHFspec, %s, %s]\n'
                   '    ring\n' % (v0, Ei, v2, xe(0), one))
    else:
        out.append('  have e1 : Ex.eval (XLF c u z) (toEx trLFN_Vm1) = xLF c %d - 1 := by\n'
                   '    simp only [trLFN_Vm1, toEx, Ex.eval, %s, %s, %s]\n' % (v0, xe(v0), xe(0), one))
        out.append('  have e2 : Ex.eval (XLF c u z) (toEx trLFN_V2m1) = xLF c %d ^ 2 - 1 := by\n'
                   '    simp only [trLFN_V2m1, toEx, Ex.eval, %s, %s, %s]\n    ring\n' % (v0, xe(v0), xe(0), one))
        out.append('  have e3 : Ex.eval (XLF c u z) (toEx trLFN_eta) = xLF c %d ^ 2 * (1 + XLF c u z %d) - 1 := by\n'
                   '    simp only [trLFN_eta, toEx, Ex.eval, %s, %s, %s]\n    ring\n' % (v0, Ei, xe(v0), xe(0), one))
    out.append('  rw [e1] at h1\n  rw [e2] at h2\n  rw [e3] at h3\n')
    out.append('  have hEb : Bd r (%s %d) ((B%s %d + E%s %d : ℚ) : ℝ) := by\n'
               '    have := (hn %d (by norm_num)).add (hE %d (by norm_num))\n    rw [add_sub_cancel] at this; push_cast; exact this\n'
               % (X, Ei, T, Ei, T, Ei, Ei, Ei))
    a, n2, eta, b, mm, g = (qlean(vs[k_]) for k_ in ['Ra', 'Rn2', 'Reta', 'b', 'm', 'g'])
    out.append('  have hv := vstep (a := ((%s : ℚ) : ℝ)) (n2 := ((%s : ℚ) : ℝ)) (η := ((%s : ℚ) : ℝ))\n'
               '    (b := ((%s : ℚ) : ℝ)) (m := ((%s : ℚ) : ℝ)) (g := ((%s : ℚ) : ℝ)) (ε := ((E%s %d : ℚ) : ℝ))\n'
               '    hr h1 h2 h3 hEb\n' % (a, n2, eta, b, mm, g, T, vk))
    facts = ['%s < 1' % a, '1 / (1 - %s) ≤ %s' % (a, b), '%s ^ 2 * %s ≤ %s' % (b, n2, mm),
             'B%s %d + E%s %d ≤ %s' % (T, Ei, T, Ei, mm), '%s < 1' % mm, '(0 : ℚ) ≤ %s' % g,
             '1 ≤ %s ^ 2 * (1 - %s)' % (g, mm), '%s ^ 3 / 2 * %s + %s < 2' % (g, mm, a),
             '%s ^ 3 / 2 * (%s ^ 2 * %s) ≤ E%s %d' % (g, b, eta, T, vk)]
    for f in facts:
        out.append('    (by exact_mod_cast (show %s by decide +kernel))\n' % f)
    if p.tag == 'H':
        out.append('  have eX : XHF c %d = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XHF c %d) := by\n'
                   '    rw [XHF_rel c (i := %d) rfl, XHF_rel c (i := %d) rfl]\n'
                   '    change XLF c _ _ %d = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLF c _ _ %d)\n'
                   '    rw [XLF_old c _ _ (j := %d) rfl, XLF_old c _ _ (j := %d) rfl]\n'
                   '    simp only [XL, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]\n    rfl\n'
                   % (vk, Ei, vk, Ei, hl_maps(H, L)[0][vk], hl_maps(H, L)[0][Ei], hl_maps(H, L)[0][vk],
                      hl_maps(H, L)[0][Ei]))
    else:
        out.append('  have eX : XLF c u z %d = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + XLF c u z %d) := by\n'
                   '    rw [XLF_old c _ _ (j := %d) rfl, XLF_old c _ _ (j := %d) rfl]\n'
                   '    simp only [XL, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]\n    rfl\n' % (vk, Ei, vk, Ei))
    out.append('  rw [eX, show x%s c %d = x%s c %d from rfl]\n  exact hv\n\n' % (T, vk, T, v0))
    # transport inputs (H)
    if p.tag == 'H':
        for nm, i, src, th in [('LRx', 6, 4, 8), ('LZx', 7, 5, 9)]:
            out.append('''/-- The transport input `%s`. -/
theorem stepHF_%s {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd r (XHF c %d - xHF c %d) (EHF %d) := by
  have hc0 := ne_zero_of_norm_one hc
  have hth : Bd r (dTh (xHF c %d)) ((BHF %d : ℚ) : ℝ) := by
    have h := normHF hq hc %d (by norm_num)
    rwa [xHF_der_%s hc0, show dS ((1 : ℤ) : ℂ) ((0 : ℤ) : ℂ) (xHF c %d) = dTh (xHF c %d) by simp [dTh]] at h
  have hana : Ana (xHF c %d) := by
    rw [xHF_fam hc0 (i := %d) rfl (p := %d) rfl]; exact ana_famCtr _ _ _ _ _ _ _ _ c _ _
  rw [XHF_spec c (i := %d) rfl]
  exact step_Linput hana (by rw [xHF_der_%s hc0]; norm_num [KamTorusA.Iq]) hth (by decide +kernel)

''' % (nm, nm, i, i, i, src, th, th, p.nm(th), src, src, src, src, p.W[src][2], i, nm))
    # the chain
    out.append('set_option linter.unusedVariables false in\n/-- The empty chain. -/\ntheorem ball%s_0 %s :\n'
               '    ∀ i, i < 0 → Bd r (%s i - x%s c i) (E%s i) :=\n  fun i h => absurd h (Nat.not_lt_zero i)\n\n'
               % (T, targs, X, T, T))
    for k_ in range(nv):
        mk = p.meta.get(k_, {}).get('kind')
        nm = p.nm(k_)
        if k_ in eqs:
            step = 'step_exact (X%s_eq_%s hc%s) (by decide +kernel)' % (T, nm, ' u z' if p.tag == 'L' else '')
        elif mk == 'torus':
            step = {'U': 'hU', 'Z': 'hZ', 'A': 'hA', 'B': 'hB'}[nm]
        elif mk == 'Linput':
            step = 'stepHF_%s hq hc' % nm
        elif mk == 'vnode':
            step = 'vnode%s %s (ball%s_%d %s)' % (T, use, T, k_, use)
        elif k_ in p.nodes:
            rr = p.nodes[k_]
            c = rr['c']
            cl_ = '(%d : ℤ)' % c if c >= 0 else '(-%d : ℤ)' % (-c)
            step = ('node3_fullN hr hq hc hW%s box%s (l1%s %d) (fun _ => rfl)\n      (fun i hi => norm%s hq hc i (by omega)) '
                    '(ball%s_%d %s) tr%sN_%s %d %d %d %s\n      %d %d %d %d %d %d %d %d %d %d %d %d\n'
                    '      (kron%s %d %d %d) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by norm_num) (by decide +kernel)\n'
                    '      l%s_%s k%s_%s (by decide +kernel) (rel%s_%s c%s)'
                    % (T, T, T, rr['R'], T, T, k_, use, T, nm, rr['dd'], rr['de'], rr['w'][2], cl_,
                       rr['A'], rr['J'], rr['K'], rr['b'], rr['W'], rr['Kw'], rr['dr'], rr['L'], rr['fuel'],
                       rr['Ki'], rr['Kj'], rr['K_'], T, rr['b'], rr['W'], rr['R'], T, nm, T, nm, T, nm,
                       ' u z' if p.tag == 'L' else ''))
        else:
            raise Exception((p.tag, k_, nm, mk))
        out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\nset_option exponentiation.threshold 4096 in\n'
                   '/-- The chain up to the variable `%s`. -/\ntheorem ball%s_%d %s :\n'
                   '    ∀ i, i < %d → Bd r (%s i - x%s c i) (E%s i) :=\n  chain_succ (ball%s_%d %s)\n    (%s)\n\n'
                   % (nm, T, k_ + 1, targs, k_ + 1, X, T, T, T, k_, use, step))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


def emit_out(p, chainmod):
    T = p.T
    nv = p.nvar
    targs, use, X = tq_args(p)
    Xf = '(XHF c)' if p.tag == 'H' else '(XLF c u z)'
    mod = '%sOut%s' % (PRE, p.tag)
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % chainmod]
    out.append('''
/-!
# Results of the %s-resolution ball chain of the guiding-centre torus family

The full chain, the value bounds `‖X c i‖ ≤ B i + E i` and the norm nodes
(%s),
for every parameter `|c| = 1`. Generated by `scripts/gc_kam/fam_emit_lean.py`.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

/-- The full chain. -/
theorem ball%s_all %s :
    ∀ i, i < %d → Bd r (%s i - x%s c i) (E%s i) :=
  ball%s_%d %s

/-- A value is bounded by its centre norm plus its radius. -/
theorem val%s_le %s
    (i : ℕ) (hi : i < %d) :
    Bd r (%s i) ((B%s i + E%s i : ℚ) : ℝ) := by
  have := (norm%s hq hc i hi).add (ball%s_all %s i hi)
  rw [add_sub_cancel] at this
  push_cast
  exact this

''' % ({'H': 'high', 'L': 'low'}[p.tag],
       'distances to the low-resolution family and residuals' if p.tag == 'H' else
       'torsion, deviations of the field and of the winding form,\ndistances to the `ρ = 1/256` torus',
       NS, T, targs, nv, X, T, T, T, nv, use, T, targs, nv, X, T, T, T, T, use))
    for r in p.norms:
        tag = r['meta']['name']
        if tag in ('Vm1', 'V2m1', 'eta'):
            continue
        n = r['n']
        Rq = rq(r['rad'])
        out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
                   'set_option exponentiation.threshold 4096 in\n'
                   '/-- The norm node `%s`. -/\ntheorem norm%s_%s %s :\n    Bd r (Ex.eval %s (toEx tr%sN_%s)) ((%s : ℚ) : ℝ) :=\n'
                   '  %s\n\n' % (tag, T, tag, targs, Xf, T, tag, qlean(Rq),
                                 norm_call(p, r, Rq, '(fun i hi => norm%s hq hc i (by omega))' % T,
                                           '(ball%s_%d %s)' % (T, n, use))))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


def item_cost(p, it):
    kind, x = it
    if kind == 'c':
        r = p.normrec[x]
        return r['W'] * r['R'] * r['Kw'] * (1 + r['W'] / max(r['L'], 1) / 8)
    r = x
    nf = len([v for v in tree_vars(r['tree']) if v in p.stored or v == p.rIdx])
    return r['W'] * r['R'] * r['Kw'] * (2 + nf) * (1 + r['W'] / max(r['L'], 1) / 16)


def lpt_groups(p, items, G):
    items = sorted(items, key=lambda it: -item_cost(p, it))
    groups = [[] for _ in range(G)]
    load = [0.0] * G
    for it in items:
        k = load.index(min(load))
        groups[k].append(it)
        load[k] += item_cost(p, it)
    # keep the original order inside a group
    order = {id(it): n for n, it in enumerate(check_items_all(p))}
    return [sorted(g, key=lambda it: order.get(id(it), 0)) for g in groups]


def check_items_all(p):
    if not hasattr(p, '_items'):
        items = []
        for i in range(p.nvar):
            if (i in p.stored or i == p.rIdx) and i in p.normrec:
                items.append(('c', i))
        for r in p.P['nodes']:
            items.append(('n' if r.get('var') is not None else 'm', r))
        p._items = items
    return p._items


if __name__ == '__main__' and 'all' in sys.argv:
    GH, GL = 22, 4
    dL = emit_data(L, 1)
    dH = emit_data(H, 6, shared=L)
    kL = emit_kv(L, dL)
    kH = emit_kv(H, dH, extra=dL)
    tL = emit_trees(L, kL)
    tH = emit_trees(H, kH)
    eL = emit_env(L, kL)
    eH = emit_env(H, kH)
    rL = emit_rel_L(L, tL, eL)
    rH = emit_rel_H(H, L, tH, [eH, rL, 'KamTorusA'])
    cL = emit_checks(L, tL, lpt_groups(L, check_items_all(L), GL))
    cH = emit_checks(H, tH, lpt_groups(H, check_items_all(H), GH))
    chL = emit_chain(L, cL, rL)
    chH = emit_chain(H, cH, rH)
    oL = emit_out(L, chL)
    oH = emit_out(H, chH)
    print(cL, cH, chL, chH, oL, oH)
