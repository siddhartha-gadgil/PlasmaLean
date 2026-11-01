"""UNTRUSTED generator.  The nesting chain of the Dommaschk tori C (inner) and A (outer).

Extends the low-resolution admissibility chain of torus A (`emit_adm.py --tag A`, 195 variables,
surrogate 32 x 32, scale 2^-64, oracle angle psi_o = 2 phi) by variables with UNIT weights (strip 0,
kernel weights P = 1, E = 0: l1 norms bound suprema):

  * the surrogate of torus C (`Design/DommaschkKamCAdmEnv`, 24 x 28) embedded in the 32 x 32 layout
    (no new data: `embedGrid 24 28 8 4 0 (DommaschkKamC.gA 4)`), and the common reference curve
    ref = (refU, refZ) = the theta-average (k = 0 column) of the C surrogate;
  * X_T = U_T - refU, Y_T = Z_T - refZ for T = C, A (exact grids), cos theta, sin theta;
  * the radial functions Rad_T = X_T cos theta + Y_T sin theta (polar-angle condition about ref);
  * the gauge G(x) = a X^2 + 2 b X Y + d Y^2 (a, d even and b odd trigonometric polynomials of degree
    <= DEG in psi_o, dyadic data) and F_C = 1 - G(x_C), F_A = G(x_A) - 1;
  * for each positive function F in (Rad_C, Rad_A, F_C, F_A): an approximate inverse square root q_F
    (data, real even grid), the node s_F = q_F^2 and the norm node ||s_F F - 1|| = eps_F < 1, so that
    s_F F > 0 pointwise with s_F >= 0: F > 0 everywhere.

G(ref + r e) = r^2 G(ref + e): G(x_C) < 1 < G(x_A) orders the two tori along every ray from the
reference point.  Every emitted constant is recomputed in exact rationals.

(needs numpy and gmpy2: the venv /tmp/dqa-venv; run with -I)
usage: python emit_nest.py [--emit [--only ...]] [--deg 4]
"""
import argparse
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, '..', '..'))
sys.path.insert(0, HERE)

import numpy as np                                            # noqa: E402
import adm_ball as AB                                         # noqa: E402
import dk_torus as DT                                         # noqa: E402
import emit_adm as EA                                         # noqa: E402

NADM = 195
NA_, MA_, NC_, MC_ = 32, 32, 24, 28
DN, DM = NA_ - NC_, MA_ - MC_
NFUN = ('RC', 'RA', 'FC', 'FA')


def build(deg=4, verbose=True):
    DT.select('C')
    plC, idxC, _, ctxC = EA.build(NC_, MC_, 64, verbose=False)
    DT.select('A')
    pl, idx, norms, ctx = EA.build(NA_, MA_, 64, verbose=False)
    assert pl.nvar == NADM and plC.nvar == NADM
    pl.P, pl.E_EXP = 1, 0
    N, M, S = pl.N, pl.M, pl.S
    t = idx['t']
    gC4, gC5 = plC.G[4], plC.G[5]

    def emb(g):
        G = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
        for i in range(2 * NC_ + 1):
            for j in range(2 * MC_ + 1):
                G[i + DN][j + DM] = g[i][j]
        return G
    eC4, eC5 = emb(gC4), emb(gC5)
    gA4, gA5 = pl.G[4], pl.G[5]

    def nocol(g):
        return [[0 if i == N else g[i][j] for j in range(2 * M + 1)] for i in range(2 * N + 1)]

    def subcol(g, h):
        return [[g[i][j] - (h[i][j] if i == N else 0) for j in range(2 * M + 1)] for i in range(2 * N + 1)]
    FC4 = ctxC['FU']
    FC5 = ctxC['FZ']
    v = {}
    v['XC'] = pl.data(nocol(eC4), 0, 'XC', FC4)
    v['YC'] = pl.data(nocol(eC5), 1, 'YC', FC5)
    v['XA'] = pl.data(subcol(gA4, eC4), 0, 'XA', max(ctx['FU'], FC4) + 1)
    v['YA'] = pl.data(subcol(gA5, eC5), 1, 'YA', max(ctx['FZ'], FC5) + 1)
    cg = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    sg = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
    cg[N + 1][M] = cg[N - 1][M] = 2 ** (S - 1)
    sg[N + 1][M], sg[N - 1][M] = 2 ** (S - 1), -2 ** (S - 1)
    v['ct'] = pl.data(cg, 0, 'ct', S + 1)
    v['st'] = pl.data(sg, 1, 'st', S + 1)
    # the gauge (floats, untrusted design)
    n = 256
    th = 2 * np.pi * np.arange(n) / n
    UC, ZC = plC.centre_values(4, n, n).real, plC.centre_values(5, n, n).real
    UA, ZA = pl.centre_values(4, n, n).real, pl.centre_values(5, n, n).real
    rU, rZ = UC.mean(axis=0), ZC.mean(axis=0)
    xC = (UC - rU) + 1j * (ZC - rZ)
    xA = (UA - rU) + 1j * (ZA - rZ)

    def fth(w, k):
        return (w * np.exp(-1j * k * th)[:, None]).mean(axis=0)
    a1, am = fth(xC, 1), fth(xC, -1)
    al = 1 / a1
    be = -am / np.conj(a1) / a1

    def Lm(x):
        return al[None, :] * x + be[None, :] * np.conj(x)
    sC, sA = np.abs(Lm(xC)).max(axis=0), np.abs(Lm(xA)).min(axis=0)
    cc = np.sqrt(sC * sA)
    al, be = al / cc, be / cc
    u, w = al + be, 1j * (al - be)
    fa, fb, fd = np.abs(u) ** 2, (u * np.conj(w)).real, np.abs(w) ** 2

    def coef_grid(f, p):
        Fh = np.fft.fft(f) / len(f)
        G = [[0] * (2 * M + 1) for _ in range(2 * N + 1)]
        for m in range(-deg, deg + 1):
            c = Fh[m % len(f)] * (1j ** p) * 2.0 ** S
            G[N][M + m] = int(round(c.real))
        s = 1 if p % 2 == 0 else -1
        for m in range(1, deg + 1):
            avg = AB.round_div(G[N][M + m] + s * G[N][M - m], 2)
            G[N][M + m], G[N][M - m] = avg, s * avg
        G[N][M] = 2 * AB.round_div(G[N][M], 2) if s == 1 else 0
        return G
    fw = lambda G: max(AB.clog2(max(abs(x) for c in G for x in c) + 1) + 1, 8)   # noqa: E731
    for nm, f, p in (('ga', fa, 0), ('gb', fb, 1), ('gd', fd, 0)):
        G = coef_grid(f, p)
        v[nm] = pl.data(G, p, nm, fw(G))
    mul = lambda i, j: ('mul', ('var', i), ('var', j))             # noqa: E731
    add = lambda e, f: ('add', e, f)                               # noqa: E731
    sub = lambda e, f: ('sub', e, f)                               # noqa: E731
    cm = lambda k, e: ('mul', ('cst', k), e)                       # noqa: E731
    nd = lambda name, e, c=1: pl.node(name, e, c, rel=(name,))['var']   # noqa: E731
    v['RC'] = nd('RC', add(mul(v['XC'], v['ct']), mul(v['YC'], v['st'])))
    v['RA'] = nd('RA', add(mul(v['XA'], v['ct']), mul(v['YA'], v['st'])))
    for T in ('C', 'A'):
        v['XX' + T] = nd('XX' + T, mul(v['X' + T], v['X' + T]))
        v['XY' + T] = nd('XY' + T, mul(v['X' + T], v['Y' + T]))
        v['YY' + T] = nd('YY' + T, mul(v['Y' + T], v['Y' + T]))
    gq = lambda T: add(add(mul(v['ga'], v['XX' + T]), cm(2, mul(v['gb'], v['XY' + T]))),  # noqa: E731
                       mul(v['gd'], v['YY' + T]))
    v['FC'] = nd('FC', sub(mul(t, t), gq('C')))
    v['FA'] = nd('FA', sub(gq('A'), mul(t, t)))
    n1, n2 = 1 << AB.clog2(4 * (2 * N + 1)), 1 << AB.clog2(4 * (2 * M + 1))
    eps = {}
    mins = {}
    for nm in NFUN:
        Fv = pl.centre_values(v[nm], n1, n2).real
        mins[nm] = float(Fv.min())
        assert Fv.min() > 0, nm
        G = AB.grid_from_values(Fv ** -0.5, N, M, S, 0)
        v['q' + nm] = pl.data(G, 0, 'q' + nm, fw(G))
    for nm in NFUN:
        v['s' + nm] = nd('s' + nm, mul(v['q' + nm], v['q' + nm]))
    for nm in NFUN:
        eps[nm] = pl.node('e' + nm, sub(mul(v['s' + nm], v[nm]), mul(t, t)), 0, rel=('e' + nm,))
    if verbose:
        print('nest chain: %d variables' % pl.nvar)
        print('  pointwise minima (surrogate, float):', {k: '%.4g' % x for k, x in mins.items()})
        for s in pl.steps:
            if s.get('kind') in ('node', 'norm') and s['n'] >= NADM:
                print('  %-5s n=%3d %s img %.2f Mbit' % (
                    s['name'], s['n'], ('B=%.5g E=%.3g' % (float(pl.B[s['var']]), float(pl.E[s['var']])))
                    if s['kind'] == 'node' else 'bound %.4g' % float(s['bound']), s['W'] * s['R'] * s['b'] / 1e6))
        for nm in ('XC', 'YC', 'XA', 'YA', 'ga', 'gb', 'gd') + tuple('q' + k for k in NFUN):
            print('  data %-4s n=%3d B=%.6g F=%d' % (nm, v[nm], float(pl.B[v[nm]]), pl.F[v[nm]]))
    return pl, idx, ctx, plC, ctxC, v, eps


# ======================================================================================== Lean emission
HEADER, qlean, lst, wrap = EA.HEADER, EA.qlean, EA.lst, EA.wrap
NS = 'PlasmaLean.Design.DommaschkKamA'
OPEN = ('open PlasmaLean.Design.DommaschkKamC\n\n' + EA.OPEN)
OUT = EA.OUT
EXPR = ('XC', 'YC', 'XA', 'YA', 'ct', 'st')       # grids given by expressions (no new data)
GEN = 'Generated by `scripts/dommaschk_kam/emit_nest.py`.'


class EmitN:
    def __init__(self, pl, idx, ctx, plC, ctxC, v, eps):
        self.pl, self.idx, self.ctx, self.plC, self.ctxC, self.v, self.eps = pl, idx, ctx, plC, ctxC, v, eps
        self.N, self.M, self.S = pl.N, pl.M, pl.S
        self.nvar = pl.nvar
        self.nodes = {s['n']: s for s in pl.steps if s.get('kind') == 'node' and s['n'] >= NADM}
        self.normnodes = [s for s in pl.steps if s.get('kind') == 'norm' and s['n'] >= NADM]
        self.newvars = list(range(NADM, self.nvar))
        self.files = []
        self.checkload = []

    def nm(self, i):
        return self.pl.names[i]

    def write(self, mod, text):
        open(os.path.join(OUT, mod + '.lean'), 'w').write(text)
        self.files.append(mod)

    def head(self, imports, title, body, meta=None):
        out = [HEADER] + ['public import %s\n' % (m if m.startswith('Mathlib') else 'PlasmaLean.' + m)
                          for m in imports]
        import textwrap
        body = '\n\n'.join(textwrap.fill(' '.join(par.split()), 100, break_long_words=False,
                                           break_on_hyphens=False) for par in body.split('\n\n'))
        if meta:
            out += ['meta import PlasmaLean.%s\n' % m for m in meta]
        out.append('\n/-!\n# %s\n\n%s\n-/\n\n@[expose] public section\nnoncomputable section\n\nnamespace %s\n\n%s\n'
                   % (title, body, NS, OPEN))
        return out

    # ---------------------------------------------------------------- data
    def emit_data(self):
        ids = [i for i in self.newvars if self.nm(i) not in EXPR]
        out = [HEADER, 'public import Mathlib.Data.List.Basic\n\n']
        out.append("""/-!
# Data of the nesting chain of the Dommaschk tori C and A

Packed half grids (`Certificates/KronBallGrid`, `halfGridR`, rows of length `2M + 1`, `M = %d`) of
the new data and node centres of the nesting chain (`Design/DommaschkKamANestEnv`): the gauge
coefficients `a`, `b`, `d`, the node centres and the approximate inverse square roots `q_F`.
Generated by the untrusted oracle `scripts/dommaschk_kam/emit_nest.py`; nothing here is trusted.
-/

@[expose] public section

namespace %s

""" % (self.M, NS))
        for i in ids:
            G, p, F = self.pl.G[i], self.pl.W[i][2], self.pl.F[i]
            rows = EA.pack_rows(EA.half_grid(G, self.N, self.M, p), self.N, self.M, F)
            out.append('set_option linter.style.longLine false in\n')
            out.append('/-- Packed half grid of the centre `%s` (field width %d). -/\n' % (self.nm(i), F))
            out.append('def datN_%s : List ℕ := [\n%s]\n\n' % (self.nm(i), ',\n'.join('  0x%x' % x for x in rows)))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamANestData', ''.join(out))

    # ---------------------------------------------------------------- environment
    def gdef(self, i):
        nm = self.nm(i)
        e = {'XC': 'fun i j => if i = NA then 0 else embC 4 i j',
             'YC': 'fun i j => if i = NA then 0 else embC 5 i j',
             'XA': 'fun i j => gA 4 i j - (if i = NA then embC 4 i j else 0)',
             'YA': 'fun i j => gA 5 i j - (if i = NA then embC 5 i j else 0)',
             'ct': 'fun i j => if (i = NA + 1 ∨ i = NA - 1) ∧ j = MA then 2 ^ 63 else 0',
             'st': 'fun i j => if i = NA + 1 ∧ j = MA then 2 ^ 63 else if i = NA - 1 ∧ j = MA then -2 ^ 63 else 0'}
        if nm in e:
            return e[nm]
        return 'symGrid NA MA ((-1) ^ %d) (halfGridR %d NA datN_%s)' % (self.pl.W[i][2], self.pl.F[i], nm)

    def l1pf(self, i):
        nm = self.nm(i)
        if nm in EXPR:
            return 'l1_gridPolyNM_le_const NA MA fun i j _ _ => abs_gN_%s i j' % nm
        return 'l1_dataGrid_le NA MA %d datN_%s %d (by kernel_fact)' % (self.pl.F[i], nm, self.pl.W[i][2])

    def emit_env(self):
        NV = self.nvar
        FC4, FC5 = self.ctxC['FU'], self.ctxC['FZ']
        FA4, FA5 = self.ctx['FU'], self.ctx['FZ']
        out = self.head(['Design.DommaschkKamAAdmEnv', 'Design.DommaschkKamCAdmEnv', 'Design.DommaschkKamANestData',
                         'Mathlib.Data.List.GetD'],
                        'The ball environment of the nesting chain of the Dommaschk tori C and A',
                        """The nesting chain extends the low-resolution admissibility chain of torus A
(`Design/DommaschkKamAAdmEnv`, variables `0, …, %d`, layout `32 × 32`, scale `2^{−64}`, oracle angle
`ψₒ = 2φ`) by %d variables with unit strip weights (`ρ = 0`): the surrogate of torus C embedded in
the layout (`embC`, no new data) without its `θ`-average (`X_C`, `Y_C`), the surrogate of torus A
minus the same average (`X_A`, `Y_A`), `cos θ`, `sin θ`, the gauge coefficients, the radial functions,
the gauge values, the approximate inverse square roots and their squares. The lists are the Adm lists
followed by the new entries (`xN_lt`, `BN_lt`, `EN_lt`). %s""" % (NADM - 1, NV - NADM, GEN))
        out.append("""/-- The surrogate grids of torus C (`i = 4, 5`) embedded in the layout `32 × 32`. -/
def embC (k : ℕ) : ℕ → ℕ → ℤ :=
  embedGrid DommaschkKamC.NA DommaschkKamC.MA 8 4 0 (DommaschkKamC.gA k)

/-- Entry bound of the embedded `U` grid of torus C. -/
theorem abs_embC4 (i j : ℕ) : |embC 4 i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  have := abs_embedGridN_le DommaschkKamC.NA DommaschkKamC.MA 8 4 0
    (fun i j => abs_dataGrid_le DommaschkKamC.NA DommaschkKamC.MA %d DommaschkKamC.datA_U 0
      (by norm_num) i j) i j
  exact this.trans (le_of_eq (by norm_num))

/-- Entry bound of the embedded `z` grid of torus C. -/
theorem abs_embC5 (i j : ℕ) : |embC 5 i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  have := abs_embedGridN_le DommaschkKamC.NA DommaschkKamC.MA 8 4 0
    (fun i j => abs_dataGrid_le DommaschkKamC.NA DommaschkKamC.MA %d DommaschkKamC.datA_Z 1
      (by norm_num) i j) i j
  exact this.trans (le_of_eq (by norm_num))

""" % (FC4, FC4, FC5, FC5))
        for i in self.newvars:
            out.append('/-- Grid of the centre `%s`. -/\ndef gN_%s : ℕ → ℕ → ℤ :=\n  %s\n\n' % (
                self.nm(i), self.nm(i), wrap(self.gdef(i), 2)))
        out.append("""/-- Entry bound of `X_C`. -/
theorem abs_gN_XC (i j : ℕ) : |gN_XC i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  unfold gN_XC; split_ifs
  · simp
  · exact abs_embC4 i j

/-- Entry bound of `Y_C`. -/
theorem abs_gN_YC (i j : ℕ) : |gN_YC i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  unfold gN_YC; split_ifs
  · simp
  · exact abs_embC5 i j

/-- Entry bound of `X_A`. -/
theorem abs_gN_XA (i j : ℕ) : |gN_XA i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  have h1 : |gA 4 i j| ≤ ((2 ^ %d : ℕ) : ℤ) :=
    abs_dataGrid_le NA MA %d datA_U 0 (by norm_num) i j
  have h2 : |(if i = NA then embC 4 i j else 0)| ≤ ((2 ^ %d : ℕ) : ℤ) := by
    split_ifs
    · exact abs_embC4 i j
    · simp
  have h3 := abs_sub (gA 4 i j) (if i = NA then embC 4 i j else 0)
  unfold gN_XA; push_cast at h1 h2 ⊢; linarith

/-- Entry bound of `Y_A`. -/
theorem abs_gN_YA (i j : ℕ) : |gN_YA i j| ≤ ((2 ^ %d : ℕ) : ℤ) := by
  have h1 : |gA 5 i j| ≤ ((2 ^ %d : ℕ) : ℤ) :=
    abs_dataGrid_le NA MA %d datA_Z 1 (by norm_num) i j
  have h2 : |(if i = NA then embC 5 i j else 0)| ≤ ((2 ^ %d : ℕ) : ℤ) := by
    split_ifs
    · exact abs_embC5 i j
    · simp
  have h3 := abs_sub (gA 5 i j) (if i = NA then embC 5 i j else 0)
  unfold gN_YA; push_cast at h1 h2 ⊢; linarith

/-- Entry bound of `cos θ`. -/
theorem abs_gN_ct (i j : ℕ) : |gN_ct i j| ≤ ((2 ^ 65 : ℕ) : ℤ) := by
  unfold gN_ct; split_ifs <;> norm_num

/-- Entry bound of `sin θ`. -/
theorem abs_gN_st (i j : ℕ) : |gN_st i j| ≤ ((2 ^ 65 : ℕ) : ℤ) := by
  unfold gN_st; split_ifs <;> norm_num

""" % (self.pl.F[self.v['XC']], self.pl.F[self.v['YC']], self.pl.F[self.v['XA']], FA4, FA4, FC4,
       self.pl.F[self.v['YA']], FA5, FA5, FC5))
        assert self.pl.F[self.v['XA']] == max(FA4, FC4) + 1 and FA4 == FC4
        out.append('/-- The grids of the variables: the Adm grids, then the new ones. -/\n'
                   'def gNl : List (ℕ → ℕ → ℤ) := gAl ++%s\n\n' % lst(['gN_%s' % self.nm(i) for i in self.newvars]))
        out.append('/-- The grids of the variables. -/\ndef gN (i : ℕ) : ℕ → ℕ → ℤ := gNl.getD i (fun _ _ => 0)\n\n')
        out.append("""/-- The polynomials of the variables. -/
def PlN : ℕ → P2
  | 0 => Tpoly SA NA MA
  | 1 => Vpoly
  | 2 => sPoly
  | 3 => cPoly
  | n + 4 => gridPolyNM NA MA (gN (n + 4))

""")
        out.append('/-- The weights of the variables (list). -/\ndef WtNl : List (ℕ × ℕ × ℕ) := WtAl ++%s\n\n'
                   % lst(['(%d, %d, %d)' % self.pl.W[i] for i in self.newvars]))
        out.append('/-- The weights of the variables. -/\ndef WtN (i : ℕ) : ℕ × ℕ × ℕ := WtNl.getD i (1, 0, 0)\n\n')
        out.append('/-- The `ℓ¹` bounds of the variable polynomials (list). -/\ndef LNl : List ℕ := LAl ++%s\n\n'
                   % lst(['lwA %d' % self.pl.F[i] for i in self.newvars]))
        out.append('/-- The `ℓ¹` bounds of the variable polynomials. -/\ndef LN (i : ℕ) : ℕ := LNl.getD i 0\n\n')
        out.append("""/-- The Kronecker images of the variable polynomials. -/
def KvN (b W : ℕ) : ℕ → ℤ
  | 0 => (2 : ℤ) ^ SA * ((1 <<< (b * (NA + W * MA)) : ℕ) : ℤ)
  | 1 => 2 * ((1 <<< (b * W) : ℕ) : ℤ)
  | 2 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) + 1
  | 3 => ((1 <<< (b * (0 + W * 2)) : ℕ) : ℤ) - 1
  | n + 4 => packGridNM b W NA (gN (n + 4)) (2 * MA + 1)

/-- The honest centres. -/
def xN (i : ℕ) : FA := ctr SA NA MA (WtN i) (PlN i)

/-- The Adm grids are kept. -/
theorem gN_lt {i : ℕ} (h : i < %d) : gN i = gA i := by
  unfold gN gNl gA
  rw [List.getD_append _ _ _ _ (by rw [show gAl.length = %d by rfl]; exact h)]

/-- The Adm weights are kept. -/
theorem WtN_lt {i : ℕ} (h : i < %d) : WtN i = WtA i := by
  unfold WtN WtNl WtA
  rw [List.getD_append _ _ _ _ (by rw [show WtAl.length = %d by rfl]; exact h)]

/-- The Adm `ℓ¹` bounds are kept. -/
theorem LN_lt {i : ℕ} (h : i < %d) : LN i = LA i := by
  unfold LN LNl LA
  rw [List.getD_append _ _ _ _ (by rw [show LAl.length = %d by rfl]; exact h)]

/-- The Adm polynomials are kept. -/
theorem PlN_lt {i : ℕ} (h : i < %d) : PlN i = PlA i := by
  match i, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | n + 4, h => simp only [PlN, PlA, gN_lt h]

/-- **The Adm centres are kept.** -/
theorem xN_lt {i : ℕ} (h : i < %d) : xN i = xA i := by
  simp only [xN, xA, WtN_lt h, PlN_lt h]

/-- The phases are below `4`. -/
theorem hWN : ∀ i, (WtN i).2.2 < 4 :=
  getD_prop (Pr := fun w : ℕ × ℕ × ℕ => w.2.2 < 4) (by kernel_fact) (by kernel_fact)

/-- Degree boxes. -/
theorem boxN : ∀ i, InBox (PlN i) (BxA i).1 (BxA i).2
  | 0 => InBox.monomial NA MA _
  | 1 => InBox.monomial 0 1 _
  | 2 => box_sPoly
  | 3 => box_cPoly
  | _ + 4 => box_gridPolyNM NA MA _

/-- The grids vanish beyond the last variable. -/
theorem gN_out (n : ℕ) : gN (n + %d) = fun _ _ => 0 := by
  unfold gN
  have h : gNl.length = %d := by rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- `ℓ¹` bounds of the Adm variables. -/
theorem l1N_%d : ∀ i, i < %d → l1 (PlN i) ≤ LN i := fun i h => by
  rw [PlN_lt h, LN_lt h]; exact l1A i

""" % ((NADM,) * 8 + (NV, NV, NADM, NADM)))
        for i in self.newvars:
            out.append('set_option maxRecDepth 100000 in\n/-- `ℓ¹` bounds up to the variable `%s`. -/\n'
                       'theorem l1N_%d : ∀ i, i < %d → l1 (PlN i) ≤ LN i :=\n  chain_succ l1N_%d\n    (%s)\n\n'
                       % (self.nm(i), i + 1, i + 1, i, self.l1pf(i)))
        out.append("""set_option maxRecDepth 100000 in
/-- `ℓ¹` bounds. -/
theorem l1N (i : ℕ) : l1 (PlN i) ≤ LN i := by
  rcases lt_or_ge i %d with h | h
  · exact l1N_%d i h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h
    exact (l1_gridPolyNM_le_const NA MA (C := 0) fun i j _ _ => by rw [gN_out n]; simp).trans
      (by simp)

/-- The Kronecker images. -/
theorem kronN : ∀ b W i, kron b W (PlN i) = KvN b W i
  | b, W, 0 => kron_Tpoly SA NA MA b W
  | b, W, 1 => kron_Vpoly b W
  | b, W, 2 => kron_sPoly b W
  | b, W, 3 => kron_cPoly b W
  | b, W, _ + 4 => kron_gridPolyNM b W NA MA _

""" % (NV, NV))
        out.append('/-- The norm bounds of the centres (list; strip `0` for the new ones). -/\ndef BNl : List ℚ := BAl ++%s\n\n'
                   % lst([qlean(self.pl.B[i]) for i in self.newvars]))
        out.append('/-- The norm bounds of the centres. -/\ndef BN (i : ℕ) : ℚ := BNl.getD i 0\n\n')
        out.append('/-- The radii of the balls (list; strip `0` for the new ones). -/\ndef ENl : List ℚ := EAl ++%s\n\n'
                   % lst([qlean(self.pl.E[i]) for i in self.newvars]))
        out.append('/-- The radii of the balls. -/\ndef EN (i : ℕ) : ℚ := ENl.getD i 0\n\n')
        out.append("""/-- The Adm norm bounds are kept. -/
theorem BN_lt {i : ℕ} (h : i < %d) : BN i = BA i := by
  unfold BN BNl BA
  rw [List.getD_append _ _ _ _ (by rw [show BAl.length = %d by rfl]; exact h)]

/-- The Adm radii are kept. -/
theorem EN_lt {i : ℕ} (h : i < %d) : EN i = EA i := by
  unfold EN ENl EA
  rw [List.getD_append _ _ _ _ (by rw [show EAl.length = %d by rfl]; exact h)]

end %s
""" % (NADM, NADM, NADM, NADM, NS))
        self.write('DommaschkKamANestEnv', ''.join(out))

    # ---------------------------------------------------------------- trees
    def emit_trees(self):
        out = self.head(['Design.DommaschkKamANestEnv'], 'Expression trees of the nesting chain',
                        'The expression trees (`Certificates/KronExpr`, `Ex`) of the new nodes and norm nodes of '
                        'the nesting chain of the Dommaschk tori C and A. ' + GEN)
        for s in self.pl.steps:
            if s.get('kind') in ('node', 'norm') and s['n'] >= NADM:
                what = 'node `%s` (variable `%d`)' % (s['name'], s['n']) if s['kind'] == 'node' else 'norm node `%s`' % s['name']
                out.append('set_option linter.style.longLine false in\n/-- Expression tree of the %s. -/\ndef trN_%s : Ex :=\n  %s\n\n' % (
                    what, s['name'], wrap(EA.tree_lean(s['tree']), 2)))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamANestTrees', ''.join(out))

    # ---------------------------------------------------------------- checks
    def center_lines(self, i):
        r = self.pl.normrec[i]
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm of the centre `%s` (unit weights). -/\n' % self.nm(i),
                'theorem cN_%s : centerKw 1 0 NA MA KvN %d %d %d %d %d %d %d ≤ %d := by\n  kron2_proof\n\n' % (
                    self.nm(i), i, r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- A priori `ℓ¹` bound of the centre `%s`. -/\n' % self.nm(i),
                'theorem clN_%s : LN %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (self.nm(i), i, r['b'])]

    def node_lines(self, r):
        cl = '(%d : ℤ)' % r['c']
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the node `%s`: truncation norm (unit weights). -/\n' % r['name'],
                'theorem kN_%s : nodeKw 1 0 SA NA MA WtN KvN trN_%s %s %d %d %d %d %d %d %d %d %d %d ≤ %d := by\n'
                '  kron2_proof\n\n' % (r['name'], r['name'], cl, r['dd'], r['de'], r['n'], r['b'], r['W'], r['dc'],
                                       r['dr'], r['J'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'],
                'theorem lN_%s : nodeL1 SA LN trN_%s %s %d %d %d < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (
                    r['name'], r['name'], cl, r['dd'], r['de'], r['n'], r['b'])]

    def norm_lines(self, r):
        return ['set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm node `%s` (unit weights). -/\n' % r['name'],
                'theorem kN_%s : normKw 1 0 NA MA WtN KvN trN_%s (%d, %d, %d) %d %d %d %d %d %d %d ≤ %d := by\n'
                '  kron2_proof\n\n' % (r['name'], r['name'], r['w'][0], r['w'][1], r['w'][2], r['b'], r['W'], r['dc'],
                                       r['dr'], r['J'], r['Ki'], r['Kj'], r['K']),
                'set_option linter.style.longLine false in\n',
                '/-- Proof-term check of the norm node `%s`: a priori `ℓ¹` bound. -/\n' % r['name'],
                'theorem lN_%s : Ex.majN LN trN_%s < 2 ^ (%d - 1) := by\n  kron_lt\n\n' % (r['name'], r['name'], r['b'])]

    def emit_checks(self, nfiles):
        items = [('c', i) for i in self.newvars]
        items += [('n', s) for s in self.nodes.values()] + [('m', s) for s in self.normnodes]

        def cost(it):
            k, x = it
            if k == 'c':
                r = self.pl.normrec[x]
                return r['W'] * (2 * self.M + 1) * r['b']
            return x['W'] * (x['J'] + 1) * x['b']
        bins = [[] for _ in range(nfiles)]
        load = [0] * nfiles
        for it in sorted(items, key=cost, reverse=True):
            f = min(range(nfiles), key=lambda k: load[k])
            bins[f].append(it)
            load[f] += cost(it)
        mods = []
        for f, ch in enumerate(bins):
            ch.sort(key=lambda it: it[1] if it[0] == 'c' else it[1]['n'] + 0.5)
            mod = 'DommaschkKamANestCheck%d' % (f + 1)
            mods.append(mod)
            out = self.head(['Design.DommaschkKamANestTrees', 'Certificates.KronProof2D'],
                            'Proof-term checks of the nesting chain (part %d)' % (f + 1),
                            'Explicit proof terms (`kron2_proof`; `kron_lt` for the `ℓ¹` bounds): the digit sums with '
                            'unit weights (`nodeKw 1 0`, `normKw 1 0`, `centerKw 1 0`; strip `ρ = 0`) of the new '
                            'centres, nodes and norm nodes of the nesting chain. ' + GEN,
                            meta=['Design.DommaschkKamANestTrees'])
            for kind, x in ch:
                out += self.center_lines(x) if kind == 'c' else self.node_lines(x) if kind == 'n' else self.norm_lines(x)
            out.append('end %s\n' % NS)
            self.write(mod, ''.join(out))
        self.checkmods = mods
        self.checkload = load

    # ---------------------------------------------------------------- honest values
    def hname(self, i):
        return 'xN %d' % i if self.pl.kind[i] in ('data', 'grid') else self.nm(i) + 'n'

    def ev_text(self, e):
        k = e[0]
        if k == 'var':
            i = e[1]
            return 'XA %d' % i if i < NADM else self.hname(i)
        if k == 'cst':
            return '((%d : ℤ) : FA)' % e[1]
        op = {'add': '+', 'sub': '-', 'mul': '*'}[k]
        return '(%s %s %s)' % (self.ev_text(e[1]), op, self.ev_text(e[2]))

    def emit_rel(self):
        out = self.head(['Design.DommaschkKamANestTrees', 'Design.DommaschkKamAAdmRel'],
                        'Honest values of the nesting chain',
                        'The value `XN i` of each variable of the nesting chain at the surrogates: the Adm values '
                        '`XA i` for `i < %d` (`XN_lt`), the centres for the new data, and for every node exactly '
                        'the evaluation of its expression tree (`relN_*`: `X n = eval X e`). %s' % (NADM, GEN))
        for i in self.newvars:
            r = self.nodes.get(i)
            if r is None:
                continue
            assert r['c'] == 1
            out.append('set_option linter.style.longLine false in\n/-- The honest value of the node `%s`. -/\ndef %sn : FA :=\n  %s\n\n'
                       % (self.nm(i), self.nm(i), wrap(self.ev_text(r['tree']), 2)))
        out.append('/-- The honest values of the variables (list): the Adm values, then the new ones. -/\n'
                   'def XNl : List FA := XAl ++%s\n\n' % lst([self.hname(i) for i in self.newvars]))
        out.append('/-- The honest values of the variables. -/\ndef XN (i : ℕ) : FA := XNl.getD i 0\n\n')
        out.append("""/-- **The Adm values are kept.** -/
theorem XN_lt {i : ℕ} (h : i < %d) : XN i = XA i := by
  unfold XN XNl XA
  rw [List.getD_append _ _ _ _ (by rw [show XAl.length = %d by rfl]; exact h)]

""" % (NADM, NADM))
        for r in self.nodes.values():
            out.append('set_option linter.style.longLine false in\nset_option maxRecDepth 100000 in\n'
                       '/-- The identity of the node `%s`. -/\n'
                       'theorem relN_%s : ((1 : ℤ) : ℂ) • XN %d = Ex.eval XN trN_%s := by\n'
                       '  rw [Int.cast_one, one_smul]\n  rfl\n\n' % (r['name'], r['name'], r['n'], r['name']))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamANestRel', ''.join(out))

    # ---------------------------------------------------------------- the chain
    def emit_chain(self):
        NV = self.nvar
        out = self.head(['Design.DommaschkKamANestRel', 'Design.DommaschkKamAAdmChain'] +
                        ['Design.%s' % m for m in self.checkmods],
                        'The ball chain of the nesting certificate',
                        'The balls `‖X i − x i‖₀ ≤ E i` (strip `ρ = 0`) of all variables of the nesting chain: the '
                        'Adm balls of torus A restricted to `ρ = 0`, then variable by variable from the kernel '
                        'checks with unit weights and the node identities; and the norm nodes `nN_*`. ' + GEN)
        out.append("""/-- The Adm weight condition at `ρ = 0`. -/
theorem hq0A : Real.exp 0 ≤ ((68553 : ℕ) : ℝ) / 2 ^ 16 := by rw [Real.exp_zero]; norm_num

/-- The unit weight condition at `ρ = 0`. -/
theorem hq0N : Real.exp 0 ≤ ((1 : ℕ) : ℝ) / 2 ^ 0 := by simp

/-- Norms of the Adm centres at `ρ = 0`. -/
theorem normN_%d : ∀ i, i < %d → Bd 0 (xN i) (BN i) := fun i h => by
  rw [xN_lt h, BN_lt h]; exact normA hq0A i h

""" % (NADM, NADM))
        for i in self.newvars:
            r = self.pl.normrec[i]
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- Norms of the centres up to the variable `%s`. -/
theorem normN_%d : ∀ i, i < %d → Bd 0 (xN i) (BN i) :=
  chain_succ normN_%d
    (center_fullw hq0N boxN l1N kronN (fun _ => rfl) %d %d %d %d %d %d %d %d %d
      (BN %d) rfl (by kernel_fact) clN_%s rfl cN_%s (by kernel_fact))

""" % (self.nm(i), i + 1, i + 1, i, i, self.pl.W[i][2], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'],
                r['K'], i, self.nm(i), self.nm(i)))
        out.append("""/-- **Norms of the centres** (strip `0`). -/
theorem normN : ∀ i, i < %d → Bd 0 (xN i) (BN i) := normN_%d

/-- The Adm balls at `ρ = 0`. -/
theorem ballN_%d : ∀ i, i < %d → Bd 0 (XN i - xN i) (EN i) := fun i h => by
  rw [XN_lt h, xN_lt h, EN_lt h]; exact ballA_all le_rfl hq0A i h

""" % (NV, NV, NADM, NADM))
        for k in self.newvars:
            nmk = self.nm(k)
            if self.pl.kind[k] in ('data', 'grid'):
                step = 'step_exact_w rfl (by kernel_fact)'
            else:
                r = self.nodes[k]
                step = ('node_fullw le_rfl hq0N hWN boxN l1N kronN (fun _ => rfl)\n'
                        '      (fun i hi => normN i (by omega)) ballN_%d trN_%s %d %d %d (%d : ℤ)\n'
                        '      %d %d %d %d %d %d %d %d %d (by kernel_fact) (by kernel_fact) (by kernel_fact)\n'
                        '      (by norm_num) (by kernel_fact) lN_%s kN_%s (by kernel_fact) relN_%s' % (
                            k, nmk, r['dd'], r['de'], r['p'], r['c'], r['A'], r['J'], r['b'], r['W'], r['dc'],
                            r['dr'], r['Ki'], r['Kj'], r['K'], nmk, nmk, nmk))
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The chain up to the variable `%s`. -/
theorem ballN_%d : ∀ i, i < %d → Bd 0 (XN i - xN i) (EN i) :=
  chain_succ ballN_%d
    (%s)

""" % (nmk, k + 1, k + 1, k, step))
        out.append("""/-- **All balls of the chain** (strip `0`). -/
theorem ballN_all : ∀ i, i < %d → Bd 0 (XN i - xN i) (EN i) := ballN_%d

/-- **Value bounds**: `‖X i‖₀ ≤ B i + E i`. -/
theorem valN_le (i : ℕ) (hi : i < %d) : Bd 0 (XN i) ((BN i + EN i : ℚ) : ℝ) := by
  have := (normN i hi).add (ballN_all i hi)
  rw [add_sub_cancel] at this; push_cast; exact this

""" % (NV, NV, NV))
        for r in self.normnodes:
            out.append("""set_option linter.style.longLine false in
set_option maxRecDepth 100000 in
/-- The norm node `%s` (strip `0`). -/
theorem nN_%s : Bd 0 (Ex.eval XN trN_%s) ((%s : ℚ) : ℝ) :=
  norm_fullw le_rfl hq0N hWN boxN l1N kronN (fun _ => rfl) (fun i hi => normN i hi) ballN_all
    trN_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d %s (by kernel_fact) (by kernel_fact) (by kernel_fact)
    lN_%s kN_%s (by kernel_fact)

""" % (r['name'], r['name'], r['name'], qlean(r['bound']), r['name'], r['w'][0], r['w'][1], r['w'][2], r['A'],
       r['J'], r['b'], r['W'], r['dc'], r['dr'], r['Ki'], r['Kj'], r['K'], qlean(r['bound']), r['name'], r['name']))
        out.append('end %s\n' % NS)
        self.write('DommaschkKamANestChain', ''.join(out))



def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--deg', type=int, default=4)
    ap.add_argument('--ncheck', type=int, default=4)
    args = ap.parse_args()
    res = build(args.deg)
    if args.emit:
        em = EmitN(*res)
        em.emit_data()
        em.emit_env()
        em.emit_trees()
        em.emit_checks(args.ncheck)
        em.emit_rel()
        em.emit_chain()
        print('emitted:', em.files)
        print('check loads (Mbit):', [round(x / 1e6, 1) for x in em.checkload])


if __name__ == '__main__':
    main()
