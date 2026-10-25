"""UNTRUSTED (energy window): kernel-checked norms of the coefficients of the energy-window torus
family in the scaled gyro-length s = (rho - 1/256)/2^-32.  With the node tori K_j (nodes t_j = -1,
-5/16, 5/16, 1; pipelines Design/RationalStellaratorGCEw<j>*H), K(s) = sum_k s^k C_k with
C_k = sum_j Vinv[k][j] K_j.  For the families f = U, Z, LRx, LZx, thU, thZ (u, z, 2^96 Lt u,
2^96 Lt z, d_theta u, d_theta z): the norms of C_k (k = 1, 2, 3), of C_0 and of C_0 - f_e (f_e the
embedded certified low-resolution torus).  Emits RationalStellaratorGCEwCombCheck<g>.lean (light kernel
checks) and RationalStellaratorGCEwComb.lean (the bounds via norm3_fullN).
Usage: python ew_comb.py H1.pkl H2.pkl H3.pkl H4.pkl"""
import sys, os, pickle
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
import fam_ball
from fam_ball import FamPipeline, decode_slice, encode_slice, famL1
from ballcert import up


def ql(q):
    q = Fr(q)
    return '%d' % q.numerator if q.denominator == 1 else '%d / %d' % (q.numerator, q.denominator)

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'PlasmaLean', 'Design') + '/'
NS = 'PlasmaLean.Design.RationalStellaratorGC'
TS = [Fr(-1), Fr(-5, 16), Fr(5, 16), Fr(1)]
HS = [pickle.load(open(f, 'rb'))['H'] for f in sys.argv[1:5]]
N, M, D, S = 36, 27, 12, 107
FAMS = [4, 5, 6, 7, 8, 9]          # U, Z, LRx, LZx, thU, thZ
EMB = {4: 10, 5: 11, 8: 12, 9: 13}  # Ue, Ze, thUe, thZe


def stored(P, i):
    f = P['fam'][i]
    c0, a, bb = f['sym']
    p = P['W'][i][2]
    s_new = 1 if p % 2 == 0 else -1
    if a == 0 and bb == 0:
        return f['slices'], c0, p
    st = [encode_slice(decode_slice(sd, N, M, f['s'], c0, a, bb), N, M, s_new)[0] for sd in f['slices']]
    return st, 1, p


# the combined environment: index -> (node j in 1..4, family index)
IDX = [(j + 1, f) for j in range(4) for f in FAMS] + [(1, EMB[f]) for f in [4, 5, 8, 9]]
PL = FamPipeline(N, M, D, S, 'C', 8)
for (j, f) in IDX:
    P = HS[j - 1]
    st, c0, p = stored(P, f)
    PL.add_fam(st, p, '%d_%d' % (j, f), sym=(c0, 0, 0), box=tuple(P['Bx'][f]))
    assert PL.W[PL.nvar - 1] == tuple(P['W'][f]), (j, f)
# inverse Vandermonde: C_k = sum_j Vi[k][j] K_j
import itertools
V = [[t ** k for k in range(4)] for t in TS]
def inv(A):
    n = len(A); A = [row[:] + [Fr(int(i == r)) for i in range(n)] for r, row in enumerate(A)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0); A[c], A[piv] = A[piv], A[c]
        pv = A[c][c]; A[c] = [x / pv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                fct = A[r][c]; A[r] = [x - fct * y for x, y in zip(A[r], A[c])]
    return [row[n:] for row in A]
Vinv_jk = inv(V)             # V[j][k] = t_j^k ;  Vinv[k][j]
Vi = Vinv_jk
from math import lcm
def comb_tree(k, f, emb):
    den = 1
    for j in range(4):
        den = lcm(den, Vi[k][j].denominator)
    terms = []
    for j in range(4):
        cnum = Vi[k][j] * den
        assert cnum.denominator == 1
        if cnum != 0:
            terms.append((int(cnum), IDX.index((j + 1, f))))
    if emb:
        terms.append((-den, IDX.index((1, EMB[f]))))
    e = None
    for cnum, v in terms:
        t = ('mul', ('cst', cnum), ('var', v))
        e = t if e is None else ('add', e, t)
    return e, den
NAMES = {4: 'U', 5: 'Z', 6: 'LRx', 7: 'LZx', 8: 'thU', 9: 'thZ'}
items = []
for f in FAMS:
    for k in range(4):
        e, den = comb_tree(k, f, False)
        items.append(('C%d%s' % (k, NAMES[f]), e, den, k, f, False))
    if f in EMB:
        e, den = comb_tree(0, f, True)
        items.append(('D0%s' % NAMES[f], e, den, 0, f, True))
recs = []
for nm, e, den, k, f, emb in items:
    r = PL.node(nm, e, 0, Lb=1)
    r['meta'] = dict(name=nm)
    Rq = up(r['rad'], 6)
    recs.append((nm, e, den, k, f, emb, r, Rq))
    print('%-8s den=%-6d |.| <= %.4e  (actual coefficient norm %.4e)' % (nm, den, float(r['rad']), float(r['rad'] / den)))
pickle.dump({nm: (den, k, f, emb, Rq) for nm, e, den, k, f, emb, r, Rq in recs}, open(os.path.join(os.environ.get('EW_COMB_OUT', '.'), 'comb.pkl'), 'wb'))


def tree_lean(e):
    k = e[0]
    if k == 'var':
        return '.var %d' % e[1]
    if k == 'cst':
        return '.cst %d' % e[1] if e[1] >= 0 else '.cst (%d)' % e[1]
    op = {'add': '.add', 'sub': '.sub', 'mul': '.mul'}[k]
    return '%s (%s) (%s)' % (op, tree_lean(e[1]), tree_lean(e[2]))


HEADER = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''
KVMODS = ['RationalStellaratorGCEw%dKvH' % j for j in range(1, 5)]
# light module: environment functions, trees and kernel checks (grouped)
G = int(os.environ.get('EW_COMB_G', 8))
groups = [recs[g::G] for g in range(G)]
envtxt = HEADER + ''.join('public import PlasmaLean.Design.%s\n' % m for m in KVMODS) + '''
/-!
# The energy-window combinations: environment (light module)

The combined variable list of the norm checks of `Design/RationalStellaratorGCEwComb`: variable
`6 (j − 1) + (f − 4)` is the family `f ∈ {4, …, 9}` (`u, z, 2^96 𝓛u, 2^96 𝓛z, ∂_θu, ∂_θz`) of the
node pipeline `j ∈ {1, …, 4}`, and variables `24, …, 27` are the embedded certified low-resolution
torus `u_L, z_L, ∂_θu_L, ∂_θz_L` (families `10, …, 13` of node `1`); weights, boxes, static `ℓ¹`
bounds and Kronecker images are those of the node pipelines. The trees `trEwC_*` are the integer
combinations `∑_j d_k V⁻¹_{kj} K_j` (`C_k` scaled by `d_k`). Generated by
`scripts/gc_kam/ew_comb.py`.
-/

@[expose] public section

namespace %s

open PlasmaLean.Certificates.KronBallCheb

/-- The combined variables: (node, family). -/
def ewIdxl : List (Nat × Nat) := [%s]

/-- The node of a combined variable. -/
def ewNode (i : Nat) : Nat := (ewIdxl.getD i (0, 0)).1

/-- The family of a combined variable. -/
def ewFam (i : Nat) : Nat := (ewIdxl.getD i (0, 0)).2

/-- Weights. -/
def WtEw (i : Nat) : Nat × Nat × Nat :=
  match ewNode i with
  | 1 => WtHE1 (ewFam i) | 2 => WtHE2 (ewFam i) | 3 => WtHE3 (ewFam i) | 4 => WtHE4 (ewFam i)
  | _ => (1, 0, 0)

/-- Static `ℓ¹` bounds. -/
def LEw (i : Nat) : Nat :=
  match ewNode i with
  | 1 => LHE1 (ewFam i) | 2 => LHE2 (ewFam i) | 3 => LHE3 (ewFam i) | 4 => LHE4 (ewFam i)
  | _ => 0

/-- Degree boxes. -/
def BxEw (i : Nat) : Nat × Nat × Nat :=
  match ewNode i with
  | 1 => BxHE1 (ewFam i) | 2 => BxHE2 (ewFam i) | 3 => BxHE3 (ewFam i) | 4 => BxHE4 (ewFam i)
  | _ => (0, 0, 0)

/-- Kronecker images. -/
def KvEw (b W R : Nat) (i : Nat) : Int :=
  match ewNode i with
  | 1 => KvHE1 b W R (ewFam i) | 2 => KvHE2 b W R (ewFam i) | 3 => KvHE3 b W R (ewFam i)
  | 4 => KvHE4 b W R (ewFam i) | _ => 0

''' % (NS, ', '.join('(%d, %d)' % jf for jf in IDX))
for nm, e, den, k, f, emb, r, Rq in recs:
    envtxt += '/-- The combination `%s` (scale `%d`). -/\ndef trEwC_%s : ExN := %s\n\n' % (nm, den, nm, tree_lean(e))
envtxt += 'end %s\n' % NS
open(OUT + 'RationalStellaratorGCEwCombEnv.lean', 'w').write(envtxt)
for g, grp in enumerate(groups):
    txt = HEADER + 'public import PlasmaLean.Design.RationalStellaratorGCEwCombEnv\n' + '''
/-!
# Kernel checks of the energy-window combinations (part %d)

Each theorem is one kernel evaluation (`decide +kernel`) of the weighted digit sum `norm3KN` of the
Kronecker image of an integer combination of node tori (`Design/RationalStellaratorGCEwCombEnv`).
Light module. Generated by `scripts/gc_kam/ew_comb.py`.
-/

@[expose] public section

-- check the theorems one at a time (bounded memory per process)
set_option Elab.async false

namespace %s

open PlasmaLean.Certificates.KronBallCheb

''' % (g + 1, NS)
    for nm, e, den, k, f, emb, r, Rq in grp:
        w = r['w']
        txt += ('set_option maxRecDepth 100000 in\n/-- Kernel check of the combination `%s`. -/\n'
                'theorem kEw_%s : norm3KN WtEw KvEw 36 27 trEwC_%s (%d, %d, %d) %d %d %d %d %d %d %d %d %d ≤\n'
                '    %d := by\n  decide +kernel\n\n'
                '/-- A priori `ℓ¹` bound of the combination `%s`. -/\n'
                'theorem lEw_%s : ExN.majN LEw trEwC_%s < 2 ^ (%d - 1) := by\n  decide +kernel\n\n'
                % (nm, nm, nm, w[0], w[1], w[2], r['b'], r['W'], r['R'], r['Kw'], r['dr'], r['L'], r['fuel'],
                   r['Ki'], r['Kj'], r['K_'], nm, nm, nm, r['b']))
    txt += 'end %s\n' % NS
    open(OUT + 'RationalStellaratorGCEwCombCheck%d.lean' % (g + 1), 'w').write(txt)
pickle.dump([(nm, e, den, k, f, emb, {kk: v for kk, v in r.items() if kk != 'tree'}, Rq)
             for nm, e, den, k, f, emb, r, Rq in recs], open(os.path.join(os.environ.get('EW_COMB_OUT', '.'), 'comb_recs.pkl'), 'wb'))

# ------------------------------------------------------------------ the assembly module (heavy)
FN = {4: 'U', 5: 'Z', 6: 'LRx', 7: 'LZx', 8: 'thU', 9: 'thZ'}
txt = HEADER + ''.join('public import PlasmaLean.Design.RationalStellaratorGCEw%dOutH\n' % j for j in range(1, 5))
txt += ''.join('public import PlasmaLean.Design.RationalStellaratorGCEwCombCheck%d\n' % (g + 1) for g in range(G))
txt += 'public import PlasmaLean.Design.RationalStellaratorGCEwInterp\n'
txt += """
/-!
# Norms of the coefficients of the energy-window torus family

The Lagrange family `K(s) = ∑_j ℓ_j(s) K_j` of the node tori (`combEw`) has the monomial
coefficients `C_k = ∑_j V⁻¹_{kj} K_j` (`coefEw`). For the families `u, z, 2^96 𝓛u, 2^96 𝓛z,
∂_θu, ∂_θz` of the node pipelines, the strip norms of `C_k` (`k = 0, …, 3`) and of `C_0 − f_L`
(`f_L` the certified low-resolution torus) are bounded by kernel-checked norm nodes of integer
combinations (`norm3_fullN` on the combined environment of
`Design/RationalStellaratorGCEwCombEnv`), uniformly in the pitch parameter `|c| = 1` and on every
strip `0 ≤ r ≤ r_A`. Generated by `scripts/gc_kam/ew_comb.py`.

**Sanity.** `xEw_node`: the node tori are the family centres of the node pipelines.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace %s

open Polynomial PlasmaLean.Certificates.Kron2 PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton
  PlasmaLean.Certificates.KronExpr PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb
  WEll1Z2 Complex

/-- The polynomials of the combined variables. -/
def PEw (i : ℕ) : P3 :=
  match ewNode i with
  | 1 => PHE1 (ewFam i) | 2 => PHE2 (ewFam i) | 3 => PHE3 (ewFam i) | 4 => PHE4 (ewFam i)
  | _ => 0

/-- The centres of the combined variables. -/
def xCw (c : ℂ) (i : ℕ) : FA := ctr3 107 36 27 12 c (WtEw i) (PEw i)

/-- The norm bounds of the combined centres. -/
def BEw (i : ℕ) : ℚ :=
  match ewNode i with
  | 1 => BHE1 (ewFam i) | 2 => BHE2 (ewFam i) | 3 => BHE3 (ewFam i) | 4 => BHE4 (ewFam i)
  | _ => 0

/-- The node tori (variable `i` of the node pipeline `j`). -/
def xEw (j : Fin 4) (c : ℂ) (i : ℕ) : FA :=
  match j with
  | 0 => xHE1 c i | 1 => xHE2 c i | 2 => xHE3 c i | 3 => xHE4 c i

/-- **Sanity**: the node tori are the family centres of the node pipelines. -/
theorem xEw_node (c : ℂ) : xEw 0 c 4 = xHE1 c 4 ∧ xEw 3 c 5 = xHE4 c 5 := ⟨rfl, rfl⟩

/-- The weights of the combined variables have phase `< 4`. -/
theorem hWEw : ∀ i, (WtEw i).2.2 < 4 := by
  intro i; unfold WtEw
  generalize ewNode i = n
  match n with
  | 1 => exact hWHE1 _
  | 2 => exact hWHE2 _
  | 3 => exact hWHE3 _
  | 4 => exact hWHE4 _
  | 0 => change (0 : ℕ) < 4; norm_num
  | _ + 5 => change (0 : ℕ) < 4; norm_num

/-- The degree boxes of the combined variables. -/
theorem boxEw (i : ℕ) : InBox3 (PEw i) (BxEw i).1 (BxEw i).2.1 (BxEw i).2.2 := by
  unfold PEw BxEw
  generalize ewNode i = n
  match n with
  | 1 => exact boxHE1 _
  | 2 => exact boxHE2 _
  | 3 => exact boxHE3 _
  | 4 => exact boxHE4 _
  | 0 => exact inBox3_zero _ _ _
  | _ + 5 => exact inBox3_zero _ _ _

/-- The static `ℓ¹` bounds of the combined variables. -/
theorem l1Ew (R i : ℕ) : l1 (flat R (PEw i)) ≤ LEw i := by
  unfold PEw LEw
  generalize ewNode i = n
  match n with
  | 1 => exact l1HE1 R _
  | 2 => exact l1HE2 R _
  | 3 => exact l1HE3 R _
  | 4 => exact l1HE4 R _
  | 0 => simp [l1, liftN]
  | _ + 5 => simp [l1, liftN]

/-- The Kronecker images of the combined variables. -/
theorem kronEw (b W R i : ℕ) : kron b W (flat R (PEw i)) = KvEw b W R i := by
  unfold PEw KvEw
  generalize ewNode i = n
  match n with
  | 1 => exact kronHE1 b W R _
  | 2 => exact kronHE2 b W R _
  | 3 => exact kronHE3 b W R _
  | 4 => exact kronHE4 b W R _
  | 0 => simp
  | _ + 5 => simp

/-- The norms of the combined centres. -/
theorem normEw {r : ℝ} (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ i, i < 28 → Bd r (xCw c i) (BEw i) := by
  intro i hi
  interval_cases i
""" % NS
for i, (j, f) in enumerate(IDX):
    txt += '  · exact normHE%d hq hc %d (by norm_num)\n' % (j, f)
txt += """
/-- The combined centres are exact (radius `0`). -/
theorem ballEw (r : ℝ) (c : ℂ) : ∀ i, i < 28 → Bd r (xCw c i - xCw c i) ((0 : ℚ) : ℝ) :=
  fun i _ => by rw [sub_self, Rat.cast_zero]; exact Bd_zero r

"""
NODEFN = {1: 0, 2: 1, 3: 2, 4: 3}
for nm, e, den, k, f, emb, r, Rq in recs:
    w = r['w']
    terms = []
    for j in range(4):
        cnum = Vi[k][j] * den
        if cnum != 0:
            terms.append('((%d : ℤ) : FA) * xEw %d c %d' % (int(cnum), j, f))
    rhs = ' + '.join(terms)
    if emb:
        rhs += ' + ((%d : ℤ) : FA) * xHE1 c %d' % (-den, EMB[f])
    txt += ('set_option maxRecDepth 100000 in\nset_option exponentiation.threshold 4096 in\n'
            '/-- The combination `%s` of the node tori (`%d` times the coefficient). -/\n'
            'theorem normEw_%s {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ} (hc : ‖c‖ = 1) :\n'
            '    Bd r (%s) ((%s : ℚ) : ℝ) := by\n'
            '  have h := norm3_fullN hr hq hc hWEw boxEw (l1Ew %d) (fun _ => rfl) (normEw hq hc) (ballEw r c) trEwC_%s (%d, %d, %d)\n'
            '      %d %d %d %d %d %d %d %d %d %d %d %d\n      (%s : ℚ) (kronEw %d %d %d) (by decide +kernel)\n'
            '      (by decide +kernel) (by decide +kernel) lEw_%s kEw_%s (by decide +kernel)\n'
            '  have e : Ex.eval (xCw c) (toEx trEwC_%s) = %s := rfl\n'
            '  rwa [e] at h\n\n'
            % (nm, den, nm, rhs, ql(Rq), r['R'], nm, w[0], w[1], w[2], r['A'], r['J'], r['K'], r['b'], r['W'],
               r['Kw'], r['dr'], r['L'], r['fuel'], r['Ki'], r['Kj'], r['K_'], ql(Rq), r['b'], r['W'], r['R'],
               nm, nm, nm, rhs))
txt += 'end %s\n' % NS
open(OUT + 'RationalStellaratorGCEwComb.lean', 'w').write(txt)

print('emitted', G, 'check modules')
