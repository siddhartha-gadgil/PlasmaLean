"""UNTRUSTED: emit the Lean files of the guiding-centre torus certificate from /tmp/gcw/gc_cert.pkl.

Files (PlasmaLean/Design/):
  RationalStellaratorGCTorusDataL.lean, ...DataH{k}.lean     packed half grids of the centres
  RationalStellaratorGCTorusEnvL.lean, ...EnvH.lean          the environments (weights, polynomials,
                                                              Kronecker images, norms, radii)
  RationalStellaratorGCTorusCheckL{k}.lean, ...CheckH{k}.lean kernel facts (converted to proof terms by
                                                              proofterm/proofterm_emit.py)
The side conditions of the other modules are emitted as `kernel_fact` proof terms.
Usage: python emit_lean.py
"""
import sys, os, pickle
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'proofterm'))
from proofterm_emit import kernel_fact_text  # side conditions as `kernel_fact` proof terms

OUT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
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
    # prefer powers of ten / two
    k10 = 0
    d = den
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
        return '.cst %d' % e[1]
    op = {'add': '.add', 'sub': '.sub', 'mul': '.mul'}[k]
    return '%s (%s) (%s)' % (op, tree_lean(e[1]), tree_lean(e[2]))


def half_grid(G, N, M, p):
    s = 1 if p % 2 == 0 else -1
    h = {}
    for i in range(N, 2 * N + 1):
        for j in range(2 * M + 1):
            if i > N or j > M:
                v = G[i][j]
            elif j < M:
                v = 0
            else:
                v = G[N][M] // 2 if s == 1 else 0
            h[(i, j)] = v
    # check the completion
    for i in range(2 * N + 1):
        for j in range(2 * M + 1):
            a = h.get((i, j), 0) if i >= N else 0
            i2, j2 = 2 * N - i, 2 * M - j
            b = h.get((i2, j2), 0) if i2 >= N else 0
            assert a + s * b == G[i][j], (i, j)
    return h


def pack(h, N, M, F):
    tot = 0
    for i in range(2 * N, N - 1, -1):
        for j in range(2 * M, -1, -1):
            v = h[(i, j)]
            assert -2 ** (F - 1) <= v < 2 ** (F - 1)
            tot = (tot << F) + (v + 2 ** (F - 1))
    return tot


def wrap(text, indent):
    """wrap a long Lean term at spaces (continuation lines indented by indent + 2)."""
    words = text.split(' ')
    lines = []
    cur = ''
    for w in words:
        if len(cur) + len(w) + 1 + indent + 2 > 98 and cur:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w) if cur else w
    lines.append(cur)
    return ('\n' + ' ' * (indent + 2)).join(lines)


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


def lean_name(prefix, name):
    return prefix + name.replace("'", "p")


D = pickle.load(open('/tmp/gcw/gc_cert.pkl', 'rb'))
PH_, PL_ = D['H'], D['L']


class Pipe:
    def __init__(self, P, tag, other=None):
        self.P, self.tag = P, tag
        self.N, self.M, self.S, self.F = P['N'], P['M'], P['S'], P['F']
        self.nvar = P['nvar']
        self.meta = P['meta']
        self.names = P['names']
        self.nodes = {r['n']: r for r in P['nodes'] if r['var'] is not None}
        self.normnodes = [r for r in P['nodes'] if r['var'] is None]
        self.other = other

    def nm(self, i):
        return self.names[i].replace("'", "p")

    def gname(self, i):
        return 'g%s_%s' % (self.tag, self.nm(i))

    def dname(self, i):
        return 'dat%s_%s' % (self.tag, self.nm(i))

    def has_data(self, i):
        k = self.meta[i]['kind']
        return k in ('input', 'node', 'data', 'torus') and not (self.tag == 'L' and self.nm(i) in ('A', 'B'))


H = Pipe(PH_, 'H')
L = Pipe(PL_, 'L')
H.other = L


def grid_def(p, i):
    T = p.tag
    N, M = 'N' + T, 'M' + T
    k = p.meta[i]['kind']
    nm = p.nm(i)
    w = p.P['W'][i]
    if p.has_data(i):
        return 'symGrid %s %s ((-1) ^ %d) (halfGridR F%s %s %s)' % (N, M, w[2], T, N, p.dname(i))
    if k == 'Linput':
        src = 'gH_U' if nm == 'LRx' else 'gH_Z'
        return ('fun i j => (((KamTorusA.Iq : ℕ) : ℤ) * ((i : ℤ) - %s) +\n    ((2 ^ 97 : ℕ) : ℤ) * ((j : ℤ) - %s)) * %s i j'
                % (N, M, src))
    if k == 'derived' or (T == 'L' and nm in ('A', 'B')):
        src = {'thU': 'gH_U', 'thZ': 'gH_Z', 'thUe': 'gH_Ue', 'thZe': 'gH_Ze', 'A': 'gL_U', 'B': 'gL_Z'}[nm]
        return 'fun i j => (((1 : ℕ) : ℤ) * ((i : ℤ) - %s) + ((0 : ℕ) : ℤ) * ((j : ℤ) - %s)) * %s i j' % (N, M, src)
    if k == 'embed':
        src = {'Ue': 'gL_U', 'Ze': 'gL_Z'}[nm]
        return 'embedGrid NL ML (NH - NL) (MH - ML) (SH - SL) %s' % src
    if k == 'vnode':
        return 'g%s_V0' % T
    raise Exception((T, nm, k))


def data_bound(p, src_idx):
    """(value, proof of |g i j| <= value for all i j) of a data grid."""
    T = p.tag
    w = p.P['W'][src_idx]
    return ('2 ^ F%s' % T, 'fun i j => abs_dataGrid_le N%s M%s F%s %s %d (by decide +kernel) i j' % (
        T, T, T, p.dname(src_idx), w[2]))


def l1_entry(p, i):
    """(LH value, l1 proof term) of variable i >= 4."""
    T = p.tag
    N, M = 'N' + T, 'M' + T
    box = '(2 * %s + 1) * (2 * %s + 1)' % (N, M)
    k = p.meta[i]['kind']
    nm = p.nm(i)
    idx = {p.nm(j): j for j in range(p.nvar)}
    if p.has_data(i) or k == 'vnode':
        src = idx['V0'] if k == 'vnode' else i
        v, pr = data_bound(p, src)
        return ('%s * %s' % (box, v),
                'l1_dataGrid_le %s %s F%s %s %d (by decide +kernel)' % (N, M, T, p.dname(src), p.P['W'][src][2]))
    if k == 'embed':
        src = L.nm({'Ue': 4, 'Ze': 5}[nm])
        Lsrc = {'Ue': 4, 'Ze': 5}[nm]
        cv = '(2 ^ (SH - SL) * 2 ^ FL)'
        inner = 'fun i j => abs_dataGrid_le NL ML FL %s %d (by decide +kernel) i j' % (L.dname(Lsrc), L.P['W'][Lsrc][2])
        return ('%s * %s' % (box, cv), 'l1_gridPolyNM_le_const %s %s fun i j _ _ => abs_embedGridN_le NL ML '
                '(NH - NL) (MH - ML) (SH - SL) (%s) i j' % (N, M, inner))
    if k == 'Linput':
        src = idx['U'] if nm == 'LRx' else idx['Z']
        v, pr = data_bound(p, src)
        return ('%s * ((KamTorusA.Iq * %s + 2 ^ 97 * %s) * %s)' % (box, N, M, v),
                'l1_gridPolyNM_le_const %s %s fun i j hi hj => abs_wgridN_le %s %s KamTorusA.Iq (2 ^ 97) (%s) hi hj'
                % (N, M, N, M, pr))
    if k == 'derived' or (T == 'L' and nm in ('A', 'B')):
        srcn = {'thU': 'U', 'thZ': 'Z', 'thUe': 'Ue', 'thZe': 'Ze', 'A': 'U', 'B': 'Z'}[nm]
        src = idx[srcn]
        if p.meta[src]['kind'] == 'embed':
            Lsrc = {'Ue': 4, 'Ze': 5}[srcn]
            cv = '(2 ^ (SH - SL) * 2 ^ FL)'
            inner = 'fun i j => abs_dataGrid_le NL ML FL %s %d (by decide +kernel) i j' % (L.dname(Lsrc), L.P['W'][Lsrc][2])
            pr = 'fun i j => abs_embedGridN_le NL ML (NH - NL) (MH - ML) (SH - SL) (%s) i j' % inner
            v = cv
        else:
            v, pr = data_bound(p, src)
        return ('%s * ((1 * %s + 0 * %s) * %s)' % (box, N, M, v),
                'l1_gridPolyNM_le_const %s %s fun i j hi hj => abs_wgridN_le %s %s 1 0 (%s) hi hj' % (N, M, N, M, pr))
    raise Exception((T, nm, k))


def emit_data(p, files):
    """split the data literals into `files` modules."""
    ids = [i for i in range(p.nvar) if p.meta[i]['kind'] != 'const' and p.has_data(i)]
    chunks = [ids[k::files] for k in range(files)]
    mods = []
    for f, ch in enumerate(chunks):
        mod = 'RationalStellaratorGCTorusData%s%s' % (p.tag, (str(f + 1) if files > 1 else ''))
        mods.append(mod)
        out = [HEADER, 'public import Mathlib.Data.List.Basic\n\n']
        out.append('''/-!
# Data of the guiding-centre torus certificate (%s resolution, part %d)

Packed half grids (`Certificates/KronBallGrid`, `halfGridR`: one literal per row, fields of
width %d bits, offset `2^%d`, rows of length `2M + 1`, `M = %d`) of the centres of the
%s-resolution ball pipeline of the guiding-centre torus
(`Design/RationalStellaratorGCTorusEnv%s`). Generated by the untrusted oracle
`scripts/gc_kam/gc_cert.py`, `emit_lean.py`; nothing here is trusted.
-/

@[expose] public section

namespace %s

''' % ({'H': 'high', 'L': 'low'}[p.tag], f + 1, p.F, p.F - 1, p.M, {'H': 'high', 'L': 'low'}[p.tag],
            p.tag, NS))
        for i in ch:
            h = half_grid(p.P['G'][i], p.N, p.M, p.P['W'][i][2])
            rows = pack_rows(h, p.N, p.M, p.F)
            out.append('set_option linter.style.longLine false in\n')
            out.append('/-- Packed half grid of the centre `%s` (one literal per row `i − N`). -/\n' % p.nm(i))
            out.append('def %s : List ℕ := [\n%s]\n\n' % (p.dname(i), ',\n'.join('  0x%x' % v for v in rows)))
        out.append('end %s\n' % NS)
        open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mods


def lst(xs, ty):
    """a Lean list literal, wrapped at 100 characters."""
    lines = []
    cur = '  ['
    for k, x in enumerate(xs):
        piece = x + (', ' if k + 1 < len(xs) else ']')
        if len(cur) + len(piece.rstrip()) > 98:
            lines.append(cur.rstrip())
            cur = '    '
        cur += piece
    lines.append(cur)
    return '\n' + '\n'.join(lines)


def emit_env(p, datamods, extra_imports):
    T = p.tag
    N, M, S, F = p.N, p.M, p.S, p.F
    out = [HEADER, 'public import PlasmaLean.Certificates.KronBallGrid\n']
    out += ['public import PlasmaLean.Design.%s\n' % m for m in datamods]
    out += ['public import %s\n' % m for m in extra_imports]
    out.append('''
/-!
# The %s-resolution ball environment of the guiding-centre torus certificate

The variables of the %s-resolution ball pipeline (`Certificates/KronBall`): layout
`N = %d`, `M = %d`, scale `2^{−%d}`; the grids `g%s i` of the centres, their polynomials `P%s i`,
weights `Wt%s i`, degree boxes `Bx%s i`, `ℓ¹` bounds `L%s i`, Kronecker images `Kv%s b W i`, and the
honest centres `x%s i`; the norm bounds `B%s i` of the centres and the radii `E%s i` of the balls
(supplied by the oracle, checked in `Design/RationalStellaratorGCTorusCheck%s*`).

Variables `0, 1, 2, 3` are `t = 1`, `V = 1`, `cos 2φ`, `sin 2φ` (`x%s_t`, `x%s_V`, `x%s_c`, `x%s_s`).
-/

@[expose] public section
noncomputable section

namespace %s

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton

/-- Layout: poloidal half width. -/
def N%s : ℕ := %d
/-- Layout: toroidal half width. -/
def M%s : ℕ := %d
/-- Layout: scale exponent. -/
def S%s : ℕ := %d
/-- Layout: field width of the packed data. -/
def F%s : ℕ := %d

''' % ({'H': 'high', 'L': 'low'}[T], {'H': 'high', 'L': 'low'}[T], N, M, S, T, T, T, T, T, T, T, T, T, T,
       T, T, T, T, NS, T, N, T, M, T, S, T, F))
    for i in range(4, p.nvar):
        if p.meta[i]['kind'] == 'vnode':
            continue
        out.append('/-- Grid of the centre `%s`. -/\ndef %s : ℕ → ℕ → ℤ :=\n  %s\n\n' % (p.nm(i), p.gname(i), grid_def(p, i)))
    for i in range(4, p.nvar):
        if p.meta[i]['kind'] == 'vnode':
            out.append('/-- Grid of the centre `%s` (the centre `V0`). -/\ndef %s : ℕ → ℕ → ℤ :=\n  %s\n\n' % (
                p.nm(i), p.gname(i), grid_def(p, i)))
    out.append('/-- The grids of the variables (list; the constants `0, …, 3` have no grid). -/\n'
               'def g%sl : List (ℕ → ℕ → ℤ) :=%s\n\n' % (T, lst(['fun _ _ => 0'] * 4 + [p.gname(i) for i in range(4, p.nvar)], 'g')))
    out.append('/-- The grids of the variables. -/\ndef g%s (i : ℕ) : ℕ → ℕ → ℤ := g%sl.getD i (fun _ _ => 0)\n\n' % (T, T))
    out.append('''/-- The grids vanish beyond the last variable. -/
theorem g@T@_out (n : ℕ) : g@T@ (n + @NV@) = fun _ _ => 0 := by
  unfold g@T@
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [g@T@l])]
  rfl

/-- The polynomials of the variables. -/
def P@T@ : ℕ → P2
  | 0 => Tpoly S@T@ N@T@ M@T@
  | 1 => Vpoly
  | 2 => cPoly
  | 3 => sPoly
  | n + 4 => gridPolyNM N@T@ M@T@ (g@T@ (n + 4))

/-- The weights of the variables (list). -/
def Wt@T@l : List (ℕ × ℕ × ℕ) := @WL@

/-- The weights of the variables. -/
def Wt@T@ (i : ℕ) : ℕ × ℕ × ℕ := Wt@T@l.getD i (1, 0, 0)

/-- The degree boxes of the variables. -/
def Bx@T@ : ℕ → ℕ × ℕ
  | 0 => (N@T@, M@T@)
  | 1 => (0, 1)
  | 2 => (0, 2)
  | 3 => (0, 2)
  | _ + 4 => (2 * N@T@, 2 * M@T@)

/-- The `ℓ¹` bounds of the variable polynomials (static: from the field width of the data). -/
def L@T@ : ℕ → ℕ
  | 0 => 2 ^ S@T@
  | 1 => 2
  | 2 => 2
  | 3 => 2
@LARMS@  | _ => 0

/-- The Kronecker images of the variable polynomials. -/
def Kv@T@ (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ S@T@ * ((1 <<< (b * (N@T@ + W * M@T@)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | n + 4 => packGridNM b W N@T@ (g@T@ (n + 4)) (2 * M@T@ + 1)

/-- The honest centres. -/
def x@T@ (i : ℕ) : FA := ctr S@T@ N@T@ M@T@ (Wt@T@ i) (P@T@ i)

/-- The phases are below `4`. -/
theorem hW@T@ : ∀ i, (Wt@T@ i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by decide +kernel) (by decide +kernel)

/-- Degree boxes. -/
theorem box@T@ : ∀ i, InBox (P@T@ i) (Bx@T@ i).1 (Bx@T@ i).2
  | 0 => InBox.monomial N@T@ M@T@ _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_cPoly
  | 3 => box_sPoly
  | _ + 4 => box_gridPolyNM N@T@ M@T@ _

/-- `ℓ¹` bounds. -/
theorem l1@T@ : ∀ i, l1 (P@T@ i) ≤ L@T@ i
  | 0 => l1_Tpoly S@T@ N@T@ M@T@
  | 1 => l1_Vpoly
  | 2 => l1_cPoly
  | 3 => l1_sPoly
@L1ARMS@  | n + @NV@ =>
    (l1_gridPolyNM_le_const N@T@ M@T@ (C := 0) fun i j _ _ => by rw [g@T@_out n]; simp).trans
      (by simp)

/-- Kronecker images. -/
theorem kron@T@ : ∀ b W i, kron b W (P@T@ i) = Kv@T@ b W i
  | b, W, 0 => kron_Tpoly S@T@ N@T@ M@T@ b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_cPoly b W
  | b, W, 3 => kron_sPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W N@T@ M@T@ _

/-- The centre of `t` is `1`. -/
theorem x@T@_t : x@T@ 0 = 1 := ctr_Tpoly S@T@ N@T@ M@T@

/-- The centre of `V` is `1`. -/
theorem x@T@_V : x@T@ 1 = 1 := ctr_Vpoly S@T@ N@T@ M@T@

'''.replace('@WL@', lst(['(%d, %d, %d)' % p.P['W'][i] for i in range(p.nvar)], 'w'))
       .replace('@LARMS@', ''.join('  | %d => %s\n' % (i, l1_entry(p, i)[0]) for i in range(4, p.nvar)))
       .replace('@L1ARMS@', ''.join('  | %d =>\n    %s\n' % (i, wrap(l1_entry(p, i)[1], 4)) for i in range(4, p.nvar)))
       .replace('@NV@', str(p.nvar)).replace('@T@', T))
    Bl = [qlean(p.P['B'][i]) for i in range(p.nvar)]
    El = [qlean(p.P['E'][i]) for i in range(p.nvar)]
    out.append('''/-- The norm bounds of the centres (list). -/
def B%sl : List ℚ := %s

/-- The norm bounds of the centres. -/
def B%s (i : ℕ) : ℚ := B%sl.getD i 0

/-- The radii of the balls (list). -/
def E%sl : List ℚ := %s

/-- The radii of the balls. -/
def E%s (i : ℕ) : ℚ := E%sl.getD i 0

end %s
''' % (T, lst(Bl, 'q'), T, T, T, lst(El, 'q'), T, T, NS))
    mod = 'RationalStellaratorGCTorusEnv%s' % T
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


if __name__ == '__main__' and 'env' in sys.argv:
    dL = emit_data(L, 1)
    dH = emit_data(H, 4)
    eL = emit_env(L, dL, ['PlasmaLean.Design.KamFlowField'])
    eH = emit_env(H, dH, ['PlasmaLean.Design.RationalStellaratorGCTorusEnvL', 'PlasmaLean.Design.KamTorusAData'])
    print(dL, dH, eL, eH)


def node_lines(p, r):
    """kernel facts of one rounding node record r."""
    T = p.tag
    n = r['n']
    nm = 'tr%s_%s' % (T, p.nm(n))
    c = r['c']
    cl = '(%d : ℤ)' % c if c >= 0 else '(-%d : ℤ)' % (-c)
    J = r['JJ']
    out = []
    out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n')
    out.append('/-- Kernel check of the node `%s`: truncation norm. -/\n' % p.nm(n))
    out.append('theorem k%s_%s : nodeK S%s N%s M%s Wt%s Kv%s %s %s %d %d %d %d %d %d %d %d %d %d ≤ %d := by\n'
               '  decide +kernel\n\n' % (T, p.nm(n), T, T, T, T, T, nm, cl, r['dd'], r['de'], n, r['b'], r['W'],
                                         r['dc'], r['dr'], J, r['Ki'], r['Kj'], r['K']))
    out.append('/-- Kernel check of the node `%s`: a priori `ℓ¹` bound. -/\n' % p.nm(n))
    out.append('theorem l%s_%s : nodeL1 S%s L%s %s %s %d %d %d < 2 ^ (%d - 1) := by\n  decide +kernel\n\n' % (
        T, p.nm(n), T, T, nm, cl, r['dd'], r['de'], n, r['b']))
    return out


def norm_lines(p, r):
    T = p.tag
    n = r['n']
    tag = r['meta']['name']
    nm = 'tr%s_%s' % (T, tag)
    out = []
    out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n')
    out.append('/-- Kernel check of the norm node `%s`. -/\n' % tag)
    out.append('theorem k%s_%s : normK N%s M%s Wt%s Kv%s %s (%d, %d, %d) %d %d %d %d %d %d %d ≤ %d := by\n'
               '  decide +kernel\n\n' % (T, tag, T, T, T, T, nm, r['w'][0], r['w'][1], r['w'][2], r['b'], r['W'],
                                         r['dc'], r['dr'], r['JJ'], r['Ki'], r['Kj'], r['K']))
    out.append('/-- Kernel check of the norm node `%s`: a priori `ℓ¹` bound. -/\n' % tag)
    out.append('theorem l%s_%s : Ex.majN L%s %s < 2 ^ (%d - 1) := by\n  decide +kernel\n\n' % (
        T, tag, T, nm, r['b']))
    return out


def center_lines(p, i):
    T = p.tag
    r = p.P['normrec'][i]
    out = []
    out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n')
    out.append('/-- Kernel check of the norm of the centre `%s`. -/\n' % p.nm(i))
    out.append('theorem c%s_%s : centerK N%s M%s Kv%s %d %d %d %d %d %d %d ≤ %d := by\n  decide +kernel\n\n' % (
        T, p.nm(i), T, T, T, i, r['b'], r['W'], r['dc'], r['dr'], p.N, p.M, r['K']))
    out.append('/-- A priori `ℓ¹` bound of the centre `%s`. -/\n' % p.nm(i))
    out.append('theorem cl%s_%s : L%s %d < 2 ^ (%d - 1) := by\n  decide +kernel\n\n' % (T, p.nm(i), T, i, r['b']))
    return out


def emit_checks(p, envmod, nfiles, only=None):
    T = p.tag
    items = []
    for i in range(4, p.nvar):
        items.append(('c', i))
    for r in p.P['nodes']:
        items.append(('n' if r['var'] is not None else 'm', r))
    if only is not None:
        items = items[:only]
    chunks = [items[k::nfiles] for k in range(nfiles)]
    mods = []
    for f, ch in enumerate(chunks):
        mod = 'RationalStellaratorGCTorusCheck%s%d' % (T, f + 1)
        mods.append(mod)
        out = [HEADER, 'public import PlasmaLean.Design.%s\n' % envmod.replace('Env', 'Trees')]
        out.append('''
/-!
# Kernel checks of the guiding-centre torus certificate (%s resolution, part %d)

Each theorem is one kernel evaluation (`decide +kernel`) of exact integer arithmetic on the data of
`Design/RationalStellaratorGCTorusData%s*`: the weighted digit sums (`nodeK`, `normK`, `centerK` of
`Certificates/KronBallGrid`) of the Kronecker images of the truncation polynomials of the ball
pipeline, and their a priori `ℓ¹` bounds. Generated by `scripts/gc_kam/emit_lean.py`.
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall

''' % ({'H': 'high', 'L': 'low'}[T], f + 1, T, NS))
        for kind, x in ch:
            if kind == 'c':
                out += center_lines(p, x)
            elif kind == 'n':
                out += node_lines(p, x)
            else:
                out += norm_lines(p, x)
        out.append('end %s\n' % NS)
        open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mods


if __name__ == '__main__' and 'checktest' in sys.argv:
    print(emit_checks(L, 'RationalStellaratorGCTorusEnvL', 1, only=int(sys.argv[2])))

if __name__ == '__main__' and 'checktestH' in sys.argv:
    # a few high-res items: one centre, one degree-2 node, the eta norm node
    items = [('c', 20)]
    rs = [r for r in H.P['nodes'] if r['var'] is not None and r['w'][0] == 2][:1]
    items += [('n', r) for r in rs]
    items += [('m', r) for r in H.P['nodes'] if r['var'] is None and r['meta']['name'] == 'eta']
    out = [HEADER, 'public import PlasmaLean.Design.RationalStellaratorGCTorusEnvH\n\n@[expose] public section\n\nnamespace %s\n\nopen PlasmaLean.Certificates.Kron2 PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall\n\n' % NS]
    for kind, x in items:
        out += center_lines(H, x) if kind == 'c' else node_lines(H, x) if kind == 'n' else norm_lines(H, x)
    out.append('end %s\n' % NS)
    open('/tmp/gcw/TestH.lean', 'w').write(''.join(out))


def emit_trees(p, envmod):
    T = p.tag
    mod = 'RationalStellaratorGCTorusTrees%s' % T
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % envmod]
    out.append('''
/-!
# Expression trees of the guiding-centre torus certificate (%s resolution)

The expression trees (`Certificates/KronExpr`, `Ex`) of the nodes of the %s-resolution ball
pipeline: each node computes a polynomial in the previous variables (homogenized with `t = 1` and
`V = 1`). Generated by `scripts/gc_kam/emit_lean.py`.
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronExpr

''' % ({'H': 'high', 'L': 'low'}[T], {'H': 'high', 'L': 'low'}[T], NS))
    for r in p.P['nodes']:
        if r['var'] is not None:
            nm = 'tr%s_%s' % (T, p.nm(r['n']))
            out.append('/-- Expression tree of the node `%s` (variable `%d`). -/\n' % (p.nm(r['n']), r['n']))
        else:
            nm = 'tr%s_%s' % (T, r['meta']['name'])
            out.append('/-- Expression tree of the norm node `%s`. -/\n' % r['meta']['name'])
        out.append('def %s : Ex :=\n  %s\n\n' % (nm, wrap(tree_lean(r['tree']), 2)))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(''.join(out))
    return mod

LEAFS2 = ['PdP'] + [b + k for b in ['D', 'nR', 'nZ'] for k in ['uuP', 'uzP', 'zzP', 'uphP', 'zphP']]
LEAFS1 = ['DuP', 'DzP', 'DphP', 'nRuP', 'nRzP', 'nRphP', 'nZuP', 'nZzP', 'nZphP', 'PuP', 'EpP']
EVALS = ('eval_add\', eval_sub\', eval_mul, eval_neg\', eval_pow\', eval_one, eval_ofNat\', eval_zero\', '
         'eval_algebraMap, eval_smul\', eval_polyExpr')
# deriv-form identities (Rel L): name, statement lhs, rhs, source lemma
DPD = []
for b, nm in [('D', 'KamNewton.Dp'), ('nR', 'KamNewton.nRp'), ('nZ', 'KamNewton.nZp')]:
    DPD += [('dpd0_' + b, 0, nm, b + 'uP', 'pd0_' + b), ('dpd1_' + b, 1, nm, b + 'zP', 'pd1_' + b)]
for b in ['D', 'nR', 'nZ']:
    DPD += [('dpd_%s_uu' % b, 0, b + 'uP', b + 'uuP', b + '_uu'), ('dpd_%s_uz' % b, 1, b + 'uP', b + 'uzP', b + '_uz'),
            ('dpd_%s_zu' % b, 0, b + 'zP', b + 'uzP', b + '_zu'), ('dpd_%s_zz' % b, 1, b + 'zP', b + 'zzP', b + '_zz'),
            ('dpd_%s_phu' % b, 0, b + 'phP', b + 'uphP', b + '_phu'),
            ('dpd_%s_phz' % b, 1, b + 'phP', b + 'zphP', b + '_phz')]
DPD += [('dpd0_P', 0, 'PuP', 'PdP', 'Pd_d0'), ('dpd1_P', 1, 'PuP', None, 'P_d1')]


def rel_proof(p, r, meta):
    T = p.tag
    trn = 'tr%s_%s' % (T, p.nm(r['n']))
    kind = meta.get('rel', 'plain')
    K = 'KH' if T == 'H' else 'KL'
    X = 'XH' if T == 'H' else 'XL'
    dp = ', '.join(x[0] for x in DPD) if T == 'L' else ''
    s0 = ('Ex.eval, %s, Int.cast_ofNat, Int.cast_one, Int.cast_neg, pdS, pd, %s, xB, Matrix.cons_val_zero, '
          'Matrix.cons_val_one, Matrix.head_cons, PolyExprS.eval, PolyExprS.eval_ofPoly, PolyExprS.deriv, '
          'PolyExprS.deriv_ofPoly, deriv_eV, single_00, single_10, map_one' % (X, K))
    if T == 'L':
        s0 += ', ' + dp
    extra = list(meta.get('unfold', []))
    if kind == 'E':
        extra = ['E_val', 'eq', 'eR']
    if kind == 'Ed':
        extra = ['dE%d' % meta['idx'], 'eq', 'eR']
    if kind == 'Pof':
        extra = ['FlowFieldS.Pof', 'FlowFieldS.Dof', 'gcFlow']
    if kind == 'W0':
        extra = ['W0of']
    ev = EVALS + ', Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat'
    if kind == 'leaf':
        ev += (', %s, sumE, monoE, PolyExpr.eval, PolyExpr.eval_npow, Algebra.algebraMap_self, '
               'RingHom.id_apply, Matrix.cons_val' % meta['leaf'])
    lines = ['  unfold %s' % trn,
             '  simp only [%s]' % wrap(s0 + ''.join(', ' + x for x in extra), 13),
             '  refine ext_eval fun θ ψ => ?_',
             '  simp only [%s]' % wrap(ev, 13),
             '  ring']
    return '\n'.join(lines)


def rel_macros(p):
    return ''


def x_body(p, i):
    m = p.meta[i]
    X = m['X']
    return X


def emit_rel(p, treemod, extra_imports):
    T = p.tag
    mod = 'RationalStellaratorGCTorusRel%s' % T
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % treemod]
    out += ['public import %s\n' % m for m in extra_imports]
    out.append('''
/-!
# True values of the %s-resolution ball pipeline of the guiding-centre torus

The value `X%s i` of each variable of the %s-resolution ball pipeline as an element of the strip
algebra (the torus `K = (1 + u, z)`, the field polynomials, the node `(1 + E)^{−1/2}`, the
brackets, the guiding-centre flow form and its derivatives%s),
and the identity of every node: `c · X n = eval X e` (`rel%s_*`), proved pointwise on the
torus (`ext_eval`) by `ring`.
Generated by `scripts/gc_kam/emit_lean.py`.
-/

@[expose] public section
noncomputable section

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall WEll1Z2 Complex PolyExpr

''' % ({'H': 'high', 'L': 'low'}[T], T, {'H': 'high', 'L': 'low'}[T],
         ', the torsion numerator' if T == 'L' else '', T, NS))
    if T == 'H':
        out.append('''/-- The guiding-centre torus `u₀ = R − 1` (the high-resolution centre). -/
def u₀G : FA := xH 4

/-- The guiding-centre torus `z₀`. -/
def z₀G : FA := xH 5

/-- The low-resolution torus `u_S`. -/
def uSG : FA := xL 4

/-- The low-resolution torus `z_S`. -/
def zSG : FA := xL 5

/-- The torus point `(u₀, z₀, cos 2φ, sin 2φ, 0, 0)`. -/
def KH : Fin 6 → FA := xB u₀G z₀G

/-- The true values of the variables. -/
def XH : ℕ → FA
''')
    else:
        out.append('''/-- The torus point `(u, z, cos 2φ, sin 2φ, 0, 0)` (`KL u z = xB u z`). -/
abbrev KL (u z : FA) : Fin 6 → FA := xB u z

''')
        for nm, i, src, dst, lem in DPD:
            if dst is None:
                out.append('/-- `%s` in derivative form. -/\ntheorem %s (x : Fin 6 → FA) :\n    PolyExpr.deriv x '
                           '(Pi.single %d 1) %s = 0 := %s x\n\n' % (lem, nm, i, src, lem))
            else:
                out.append('/-- `%s` in derivative form. -/\ntheorem %s (x : Fin 6 → FA) :\n    PolyExpr.deriv x '
                           '(Pi.single %d 1) %s = PolyExpr.eval x %s := %s x\n\n' % (lem, nm, i, src, dst, lem))
        out.append('''/-- `E_d0` in derivative form. -/
theorem dE0 (x : Fin 6 → FA) : PolyExpr.deriv x (Pi.single 0 1) EpP =
    (2 * PolyExpr.eval x KamNewton.nRp * pd x 0 KamNewton.nRp +
    2 * (1 + x 0) ^ 2 * PolyExpr.eval x KamNewton.Dp * pd x 0 KamNewton.Dp +
    2 * PolyExpr.eval x KamNewton.nZp * pd x 0 KamNewton.nZp + 2 * (1 + x 0) *
    PolyExpr.eval x KamNewton.Dp ^ 2) * PolyExpr.eval x PuP ^ 2 +
    2 * (PolyExpr.eval x KamNewton.nRp ^ 2 +
    (1 + x 0) ^ 2 * PolyExpr.eval x KamNewton.Dp ^ 2 + PolyExpr.eval x KamNewton.nZp ^ 2) *
    PolyExpr.eval x PuP * pd x 0 PuP := E_d0 x

/-- `E_d1` in derivative form. -/
theorem dE1 (x : Fin 6 → FA) : PolyExpr.deriv x (Pi.single 1 1) EpP =
    (2 * PolyExpr.eval x KamNewton.nRp * pd x 1 KamNewton.nRp +
    2 * (1 + x 0) ^ 2 * PolyExpr.eval x KamNewton.Dp * pd x 1 KamNewton.Dp +
    2 * PolyExpr.eval x KamNewton.nZp * pd x 1 KamNewton.nZp) * PolyExpr.eval x PuP ^ 2 +
    2 * (PolyExpr.eval x KamNewton.nRp ^ 2 + (1 + x 0) ^ 2 * PolyExpr.eval x KamNewton.Dp ^ 2 +
    PolyExpr.eval x KamNewton.nZp ^ 2) * PolyExpr.eval x PuP * pd x 1 PuP := E_d1 x

/-- The true values of the variables at the torus `(u, z)`. -/
def XL (u z : FA) : ℕ → FA
''')
    for i in range(p.nvar):
        Xs = x_body(p, i).replace('KL', '(KL u z)') if T == 'L' else x_body(p, i)
        out.append('  | %d => %s\n' % (i, wrap(Xs, 8)))
    out.append('  | _ => 0\n\n')
    out.append(rel_macros(p))
    for r in p.P['nodes']:
        if r['var'] is None:
            continue
        n = r['n']
        meta = p.meta[n]
        c = r['c']
        cl = '((%d : ℤ) : ℂ)' % c if c >= 0 else '((-%d : ℤ) : ℂ)' % (-c)
        lhsX = 'XH %d' % n if T == 'H' else 'XL u z %d' % n
        rhsX = 'XH' if T == 'H' else '(XL u z)'
        args = '' if T == 'H' else ' (u z : FA)'
        out.append('set_option linter.unusedSimpArgs false in\n/-- The identity of the node `%s`. -/\ntheorem rel%s_%s%s :\n    %s • %s = Ex.eval %s tr%s_%s := by\n%s\n\n'
                   % (p.nm(n), T, p.nm(n), args, cl, lhsX, rhsX, T, p.nm(n), rel_proof(p, r, meta).replace('(KL)', '(KL u z)')))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod


if __name__ == '__main__' and 'rel' in sys.argv:
    tL = emit_trees(L, 'RationalStellaratorGCTorusEnvL')
    tH = emit_trees(H, 'RationalStellaratorGCTorusEnvH')
    rL = emit_rel(L, tL, ['PlasmaLean.Design.RationalStellaratorGCInstance', 'PlasmaLean.Design.RationalStellaratorGCPoly2'])
    rH = emit_rel(H, tH, ['PlasmaLean.Design.RationalStellaratorGCInstance', 'PlasmaLean.Design.KamTorusA'])
    print(tL, tH, rL, rH)


def qdec(q):
    return qlean(q)


def emit_assembly(p, checkmods, relmod):
    """the ball chain: norms of the centres, the balls of all variables (step by step)."""
    T = p.tag
    N, M, S = p.N, p.M, p.S
    X = 'XH' if T == 'H' else 'XL u z'
    Xf = 'XH' if T == 'H' else '(XL u z)'
    mod = 'RationalStellaratorGCTorusChain%s' % T
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % relmod]
    out += ['public import PlasmaLean.Design.%s\n' % m for m in checkmods]
    out.append('public import PlasmaLean.Design.RationalStellaratorGCTorusCommon\n')
    out.append('''
/-!
# The %s-resolution ball chain of the guiding-centre torus

The balls `‖X i − x i‖_r ≤ E i` of all variables of the %s-resolution pipeline, on every strip
`r ≥ 0` with `e^r ≤ 74315/2^16`%s,
built variable by variable (`ball%s_k`, `chain_succ`) from the kernel checks of
`Design/RationalStellaratorGCTorusCheck%s*` (`node_full`), the node identities of
`Design/RationalStellaratorGCTorusRel%s` and the node step `vstep`. Generated by
`scripts/gc_kam/emit_lean.py`.
-/

@[expose] public section
noncomputable section

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

''' % ({'H': 'high', 'L': 'low'}[T], {'H': 'high', 'L': 'low'}[T],
       '\nand every torus `(u, z)` within the input radii of the low-resolution torus' if T == 'L' else '',
       T, T, T, NS))
    # centre lemmas
    out.append('''/-- The centre of `cos 2φ`. -/
theorem x%s_c : x%s 2 = cS := ctr_cPoly S%s N%s M%s

/-- The centre of `sin 2φ`. -/
theorem x%s_s : x%s 3 = sS := ctr_sPoly S%s N%s M%s

''' % (T, T, T, T, T, T, T, T, T, T))
    # norms
    out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n/-- **Norms of the centres.** -/\ntheorem norm%s {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) :\n'
               '    ∀ i, i < %d → Bd r (x%s i) (B%s i)\n' % (T, p.nvar, T, T))
    out.append('  | 0, _ => by rw [x%s_t]; exact (Bd_one r).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
    out.append('  | 1, _ => by rw [x%s_V]; exact (Bd_one r).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
    out.append('  | 2, _ => by rw [x%s_c]; exact (Bd_cS_q hq).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
    out.append('  | 3, _ => by rw [x%s_s]; exact (Bd_sS_q hq).le (by norm_num [B%s, B%sl])\n' % (T, T, T))
    for i in range(4, p.nvar):
        r = p.P['normrec'][i]
        w = p.P['W'][i]
        out.append('  | %d, _ => center_full hq box%s l1%s kron%s (fun _ => rfl) %d %d %d %d %d %d %d %d %d\n'
                   '      (B%s %d) rfl (by decide +kernel) cl%s_%s rfl c%s_%s (by decide +kernel)\n'
                   % (i, T, T, T, i, w[2], r['b'], r['W'], r['dc'], r['dr'], N, M, r['K'], T, i, T, p.nm(i), T, p.nm(i)))
    out.append('  | n + %d, h => absurd h (by omega)\n\n' % p.nvar)
    # chain
    targs = '{r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16)'
    if T == 'L':
        targs += (' {u z : FA}\n    (hU : Bd r (u - xL 4) (EL 4)) (hZ : Bd r (z - xL 5) (EL 5))\n'
                  '    (hA : Bd r (dTh u - xL 6) (EL 6)) (hB : Bd r (dTh z - xL 7) (EL 7))')
    targs_use = 'hr hq' + (' hU hZ hA hB' if T == 'L' else '')
    out.append(pre_lemmas(p, targs, targs_use, X, Xf))
    out.append('set_option linter.unusedVariables false in\n/-- The empty chain. -/\ntheorem ball%s_0 %s :\n    ∀ i, i < 0 → Bd r (%s i - x%s i) (E%s i) :=\n'
               '  fun i h => absurd h (Nat.not_lt_zero i)\n\n' % (T, targs, X, T, T))
    normnodes = {}
    for rr in p.P['nodes']:
        if rr['var'] is None:
            normnodes.setdefault(rr['n'], []).append(rr)
    idx = {p.nm(j): j for j in range(p.nvar)}
    for k in range(p.nvar):
        m = p.meta[k]
        kind = m['kind']
        nm = p.nm(k)
        step = None
        if kind == 'const':
            lem = {0: 'x%s_t.symm' % T, 1: 'x%s_V.symm' % T, 2: 'x%s_c.symm' % T, 3: 'x%s_s.symm' % T}[k]
            step = 'step_exact %s (by decide +kernel)' % lem
        elif kind in ('input', 'data'):
            step = 'step_exact rfl (by decide +kernel)'
        elif kind == 'torus':
            step = {'U': 'hU', 'Z': 'hZ', 'A': 'hA', 'B': 'hB'}[nm]
        elif kind == 'Linput':
            step = 'step%s_%s %s' % (T, nm, 'hq')
        elif kind == 'derived':
            step = 'step_exact dTh_x%s_%s.symm (by decide +kernel)' % (T, nm)
        elif kind == 'embed':
            step = 'step_exact embed_x%s_%s.symm (by decide +kernel)' % (T, nm)
        elif kind == 'vnode':
            step = 'vnode%s %s (ball%s_%d %s)' % (T, targs_use, T, k, targs_use)
        elif kind == 'node':
            rr = p.nodes[k]
            c = rr['c']
            cl = '(%d : ℤ)' % c if c >= 0 else '(-%d : ℤ)' % (-c)
            step = ('node_full hr hq hW%s box%s l1%s kron%s (fun _ => rfl)\n      (fun i hi => norm%s hq i (by omega)) '
                    '(ball%s_%d %s) tr%s_%s %d %d %d %s\n      %d %d %d %d %d %d %d %d %d (by decide +kernel) '
                    '(by decide +kernel) (by decide +kernel)\n      (by norm_num) (by decide +kernel) l%s_%s k%s_%s '
                    '(by decide +kernel) (rel%s_%s%s)'
                    % (T, T, T, T, T, T, k, targs_use, T, nm, rr['dd'], rr['de'], rr['w'][2], cl,
                       rr['A'], rr['JJ'], rr['b'], rr['W'], rr['dc'], rr['dr'], rr['Ki'], rr['Kj'], rr['K'],
                       T, nm, T, nm, T, nm, ' u z' if T == 'L' else ''))
        else:
            raise Exception(kind)
        out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n/-- The chain up to the variable `%s`. -/\ntheorem ball%s_%d %s :\n'
                   '    ∀ i, i < %d → Bd r (%s i - x%s i) (E%s i) :=\n  chain_succ (ball%s_%d %s)\n    (%s)\n\n'
                   % (nm, T, k + 1, targs, k + 1, X, T, T, T, k, targs_use, step))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod

if __name__ == '__main__' and 'checks' in sys.argv:
    cL = emit_checks(L, 'RationalStellaratorGCTorusEnvL', 4)
    cH = emit_checks(H, 'RationalStellaratorGCTorusEnvH', 16)
    print(cL, cH)


def norm_call(p, rr, Rq, hE='hE', hn='hn'):
    T = p.tag
    tag = rr['meta']['name']
    w = rr['w']
    return ('norm_full hr hq hW%s box%s l1%s kron%s (fun _ => rfl) %s %s tr%s_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d\n'
            '      %s (by decide +kernel) (by decide +kernel) (by decide +kernel) l%s_%s k%s_%s (by decide +kernel)'
            % (T, T, T, T, hn, hE, T, tag, w[0], w[1], w[2], rr['A'], rr['JJ'], rr['b'], rr['W'], rr['dc'], rr['dr'],
               rr['Ki'], rr['Kj'], rr['K'], qlean(Rq), T, tag, T, tag))


def qfact(stmt):
    return '(by exact_mod_cast (show %s by decide +kernel))' % stmt


def pre_lemmas(p, targs, targs_use, X, Xf):
    T = p.tag
    out = []
    idx = {p.nm(j): j for j in range(p.nvar)}
    Xn = 'XH' if T == 'H' else 'XL'
    # embedding lemmas (H)
    for k in range(p.nvar):
        m = p.meta[k]
        if m['kind'] == 'embed':
            nm = p.nm(k)
            src = {'Ue': 4, 'Ze': 5}[nm]
            tgt = {'Ue': 'uSG', 'Ze': 'zSG'}[nm]
            out.append('/-- The embedded low-resolution centre `%s`. -/\ntheorem embed_x%s_%s : x%s %d = %s :=\n'
                       '  ctr_embedGrid SL NL ML %d (NH - NL) (MH - ML) (SH - SL) %s\n\n'
                       % (nm, T, nm, T, k, tgt, L.P['W'][src][2], L.gname(src)))
    # derivative lemmas
    for k in range(p.nvar):
        m = p.meta[k]
        nm = p.nm(k)
        if m['kind'] == 'derived' or (T == 'L' and nm in ('A', 'B')):
            srcn = {'thU': 'U', 'thZ': 'Z', 'thUe': 'Ue', 'thZe': 'Ze', 'A': 'U', 'B': 'Z'}[nm]
            s_ = idx[srcn]
            pS = p.P['W'][s_][2]
            if T == 'H':
                srcX = {'U': 'u₀G', 'Z': 'z₀G', 'Ue': 'uSG', 'Ze': 'zSG'}[srcn]
            else:
                srcX = 'xL %d' % s_
            pre_rw = ('rw [← embed_x%s_%s]\n  ' % (T, srcn)) if srcn in ('Ue', 'Ze') else ''
            cX = ('x%s %d' % (T, s_)) if srcn in ('Ue', 'Ze') else srcX
            out.append('/-- The centre `%s` is `∂_θ` of the centre `%s`. -/\ntheorem dTh_x%s_%s : x%s %d = dTh (%s) := by\n'
                       '  %srw [show dTh (%s) = dS (((1 : ℕ) : ℤ) : ℂ) (((0 : ℕ) : ℤ) : ℂ) (%s) by simp [dTh]]\n'
                       '  exact (dS_ctr_grid S%s N%s M%s %d %s _ _).symm\n\n'
                       % (nm, srcn, T, nm, T, k, srcX, pre_rw, cX, cX, T, T, T, pS, p.gname(s_)))
    # transport inputs (H)
    for k in range(p.nvar):
        m = p.meta[k]
        if m['kind'] == 'Linput':
            nm = p.nm(k)
            srcn, thn = ('U', 'thU') if nm == 'LRx' else ('Z', 'thZ')
            srcX = 'u₀G' if srcn == 'U' else 'z₀G'
            th = idx[thn]
            out.append('/-- The transport input `%s`. -/\ntheorem step%s_%s {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) :\n'
                       '    Bd r (XH %d - xH %d) (EH %d) :=\n'
                       '  step_Linput (ana_ctr_grid SH NH MH _ _) (dS_ctr_grid SH NH MH %d %s _ _).symm\n'
                       '    (dTh_xH_%s ▸ normH hq %d (by norm_num))\n    (by decide +kernel)\n\n'
                       % (nm, T, nm, k, k, k, p.P['W'][idx[srcn]][2], p.gname(idx[srcn]), thn, th))
    # the node step
    vk = [k for k in range(p.nvar) if p.meta[k]['kind'] == 'vnode'][0]
    v0 = idx['V0']
    Ei = idx['E']
    nn = {rr['meta']['name']: rr for rr in p.P['nodes'] if rr['var'] is None}
    vs = p.P['vstep']
    hyps = '(hE : ∀ i, i < %d → Bd r (%s i - x%s i) (E%s i))' % (vk, X, T, T)
    out.append('set_option linter.unusedVariables false in\nset_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n/-- The node step: the ball of `(1 + E)^{−1/2}`. -/\n'
               'theorem vnode%s %s\n    %s :\n    Bd r (%s %d - x%s %d) (E%s %d) := by\n' % (T, targs, hyps, X, vk, T, vk, T, vk))
    out.append('  have hn : ∀ i, i < %d → Bd r (x%s i) (B%s i) := fun i hi => norm%s hq i (by omega)\n' % (vk, T, T, T))
    for nmn, R, h in [('Vm1', vs['Ra'], 'h1'), ('V2m1', vs['Rn2'], 'h2'), ('eta', vs['Reta'], 'h3')]:
        out.append('  have %s := %s\n' % (h, norm_call(p, nn[nmn], R)))
    out.append('  have e1 : Ex.eval %s tr%s_Vm1 = x%s %d - 1 := by\n    unfold tr%s_Vm1; simp only [Ex.eval, %s]\n' % (Xf, T, T, v0, T, Xn))
    out.append('  have e2 : Ex.eval %s tr%s_V2m1 = x%s %d ^ 2 - 1 := by\n    unfold tr%s_V2m1; simp only [Ex.eval, %s]; ring\n' % (Xf, T, T, v0, T, Xn))
    out.append('  have e3 : Ex.eval %s tr%s_eta = x%s %d ^ 2 * (1 + %s %d) - 1 := by\n    unfold tr%s_eta; simp only [Ex.eval, %s]; ring\n'
               % (Xf, T, T, v0, X, Ei, T, Xn))
    out.append('  rw [e1] at h1\n  rw [e2] at h2\n  rw [e3] at h3\n')
    out.append('  have hEb : Bd r (%s %d) ((B%s %d + E%s %d : ℚ) : ℝ) := by\n'
               '    have := (hn %d (by norm_num)).add (hE %d (by norm_num))\n    rw [add_sub_cancel] at this; push_cast; exact this\n'
               % (X, Ei, T, Ei, T, Ei, Ei, Ei))
    a, n2, eta, b, mm, g, eps = (qlean(vs[k_]) for k_ in ['Ra', 'Rn2', 'Reta', 'b', 'm', 'g', 'eps'])
    out.append('  have hv := vstep (a := ((%s : ℚ) : ℝ)) (n2 := ((%s : ℚ) : ℝ)) (η := ((%s : ℚ) : ℝ))\n'
               '    (b := ((%s : ℚ) : ℝ)) (m := ((%s : ℚ) : ℝ)) (g := ((%s : ℚ) : ℝ)) (ε := ((E%s %d : ℚ) : ℝ))\n'
               '    hr h1 h2 h3 hEb\n' % (a, n2, eta, b, mm, g, T, vk))
    facts = ['%s < 1' % a, '1 / (1 - %s) ≤ %s' % (a, b), '%s ^ 2 * %s ≤ %s' % (b, n2, mm),
             'B%s %d + E%s %d ≤ %s' % (T, Ei, T, Ei, mm), '%s < 1' % mm, '(0 : ℚ) ≤ %s' % g,
             '1 ≤ %s ^ 2 * (1 - %s)' % (g, mm), '%s ^ 3 / 2 * %s + %s < 2' % (g, mm, a),
             '%s ^ 3 / 2 * (%s ^ 2 * %s) ≤ E%s %d' % (g, b, eta, T, vk)]
    for f in facts:
        out.append('    %s\n' % qfact(f))
    out.append('  have eX : %s %d = invSqrt ℂ 1 (algebraMap ℂ FA ((1 : ℝ) : ℂ) + %s %d) := by\n'
               '    simp only [%s, eV, PolyExprS.eval, PolyExprS.eval_ofPoly]\n    rfl\n' % (X, vk, X, Ei, Xn))
    out.append('  rw [eX, show x%s %d = x%s %d from rfl]\n  exact hv\n\n' % (T, vk, T, v0))
    return ''.join(out)

if __name__ == '__main__' and 'chain' in sys.argv:
    chL = emit_assembly(L, ['RationalStellaratorGCTorusCheckL%d' % k for k in range(1, 5)], 'RationalStellaratorGCTorusRelL')
    chH = emit_assembly(H, ['RationalStellaratorGCTorusCheckH%d' % k for k in range(1, 17)], 'RationalStellaratorGCTorusRelH')
    print(chL, chH)


OUTPUTS_L = [('Dt', 'PolyExprS.eval (xB u z) (gcD (1 / 256))'), ('nRt', 'PolyExprS.eval (xB u z) (gcNR (1 / 256))'),
             ('nZt', 'PolyExprS.eval (xB u z) (gcNZ (1 / 256))'),
             ('Dtu', 'pdS (xB u z) 0 (gcD (1 / 256))'), ('Dtz', 'pdS (xB u z) 1 (gcD (1 / 256))'),
             ('nRtu', 'pdS (xB u z) 0 (gcNR (1 / 256))'), ('nRtz', 'pdS (xB u z) 1 (gcNR (1 / 256))'),
             ('nZtu', 'pdS (xB u z) 0 (gcNZ (1 / 256))'), ('nZtz', 'pdS (xB u z) 1 (gcNZ (1 / 256))'),
             ('W0', 'W0of u z'), ('Ptor', '(gcFlow (1 / 256)).Pof u z')]


def emit_outputs(p, chainmod, cst):
    T = p.tag
    idx = {p.nm(j): j for j in range(p.nvar)}
    mod = 'RationalStellaratorGCTorusOut%s' % T
    out = [HEADER, 'public import PlasmaLean.Design.%s\n' % chainmod]
    out.append('''
/-!
# Results of the %s-resolution ball chain of the guiding-centre torus

%s
Generated by `scripts/gc_kam/emit_lean.py`.
-/

@[expose] public section
noncomputable section

namespace %s

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.Kron2 WEll1Z2 Complex

''' % ({'H': 'high', 'L': 'low'}[T],
       ('The strip bounds of the guiding-centre torus `K₀` (`u₀G`, `z₀G`), of its residual\n(the `e₀` of '
        'the KAM theorem) and its distances to the low-resolution torus.') if T == 'H' else
       ('At every torus `(u, z)` within the input radii of the low-resolution torus, on every\nstrip '
        '`e^r ≤ 74315/2^16`: bounds of the guiding-centre field and its `u`, `z`-derivatives,\nof the winding '
        'form, of the deviations from the means and of the torsion pieces.'), NS))
    targs = '{r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16)'
    if T == 'L':
        targs += (' {u z : FA}\n    (hU : Bd r (u - xL 4) (EL 4)) (hZ : Bd r (z - xL 5) (EL 5))\n'
                  '    (hA : Bd r (dTh u - xL 6) (EL 6)) (hB : Bd r (dTh z - xL 7) (EL 7))')
    targs_use = 'hr hq' + (' hU hZ hA hB' if T == 'L' else '')
    X = 'XH' if T == 'H' else 'XL u z'
    Xf = 'XH' if T == 'H' else '(XL u z)'
    Xn = 'XH' if T == 'H' else 'XL'
    nv = p.nvar
    out.append('/-- The full chain. -/\ntheorem ball%s_all %s :\n    ∀ i, i < %d → Bd r (%s i - x%s i) (E%s i) :=\n  ball%s_%d %s\n\n'
               % (T, targs, nv, X, T, T, T, nv, targs_use))
    out.append('''/-- A value is bounded by its centre norm plus its radius. -/
theorem val%s_le %s
    (i : ℕ) (hi : i < %d) :
    Bd r (%s i) ((B%s i + E%s i : ℚ) : ℝ) := by
  have := (norm%s hq i hi).add (ball%s_all %s i hi)
  rw [add_sub_cancel] at this
  push_cast
  exact this

''' % (T, targs, nv, X, T, T, T, T, targs_use))
    if T == 'L':
        for nm, expr in OUTPUTS_L:
            k = idx[nm]
            out.append('/-- The bound of `%s`. -/\ntheorem gcL_%s %s :\n    Bd r (%s) ((BL %d + EL %d : ℚ) : ℝ) :=\n  valL_le %s %d (by norm_num)\n\n'
                       % (expr, nm, targs, expr, k, k, targs_use, k))
    nn = {rr['meta']['name']: rr for rr in p.P['nodes'] if rr['var'] is None}
    roles = (['dU', 'dZ', 'dA', 'dB', 'resR', 'resZ'] if T == 'H' else ['X', 'Ddev', 'Wdev'])
    for nmn in roles:
        rr = nn[nmn]
        n = rr['n']
        Rq = cst['R_' + nmn]
        out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
                   '/-- The norm node `%s`. -/\ntheorem norm%s_%s %s :\n    Bd r (Ex.eval %s tr%s_%s) ((%s : ℚ) : ℝ) :=\n'
                   '  %s\n\n' % (nmn, T, nmn, targs, Xf, T, nmn, qlean(Rq),
                                 norm_call(p, rr, Rq, hE='(ball%s_%d %s)' % (T, n, targs_use),
                                           hn='(fun i hi => norm%s hq i (by omega))' % T)))
    out.append('end %s\n' % NS)
    open(OUT + mod + '.lean', 'w').write(kernel_fact_text(''.join(out)))
    return mod

if __name__ == '__main__' and 'outputs' in sys.argv:
    C = pickle.load(open('/tmp/gcw/gc_const.pkl', 'rb'))
    print(emit_outputs(L, 'RationalStellaratorGCTorusChainL', C), emit_outputs(H, 'RationalStellaratorGCTorusChainH', C))
