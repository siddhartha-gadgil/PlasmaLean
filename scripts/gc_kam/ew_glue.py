"""UNTRUSTED (energy window): emit the glue modules of the energy-window certificate that depend on
the numbers of the node pipelines and of the combination norms:
  RationalStellaratorGCEwDisc.lean  validity and majorants of the residual trees on the complex disc
                                    |s| <= 2^20 of the scaled gyro-length (bounds aDQ of the inputs)
  RationalStellaratorGCEwRes.lean   coefficient bounds and the residual of the torus family for
                                    every |s| <= 1 (interpolation with analytic remainder)
Usage: python ew_glue.py H1.pkl H2.pkl H3.pkl H4.pkl comb_recs.pkl"""
import sys, os, re, pickle, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
os.environ.setdefault('LAM_DEN', '32')
import fam_ball  # noqa: F401
import ew_majlib as LM
from ew_majlib import up

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'PlasmaLean', 'Design') + '/'
HS = [pickle.load(open(f, 'rb'))['H'] for f in sys.argv[1:5]]
RECS = pickle.load(open(sys.argv[5], 'rb'))
COMB = {nm: (den, k, f, emb, Rq) for nm, e, den, k, f, emb, r, Rq in RECS}
VI = [[Fr(-25, 462), Fr(128, 231), Fr(128, 231), Fr(-25, 462)],
      [Fr(25, 462), Fr(-2048, 1155), Fr(2048, 1155), Fr(-25, 462)],
      [Fr(128, 231), Fr(-128, 231), Fr(-128, 231), Fr(128, 231)],
      [Fr(-128, 231), Fr(2048, 1155), Fr(-2048, 1155), Fr(128, 231)]]
RS = 2 ** 20
AC = Fr(74315, 2 ** 16)
E6 = [up(H['E'][6], 4) for H in HS]
E7 = [up(H['E'][7], 4) for H in HS]


def cb(nm):
    den, k, f, emb, Rq = COMB[nm]
    return Fr(Rq) / den


b = []
for k in range(4):
    bu, bz = cb('C%dU' % k), cb('C%dZ' % k)
    lu = (cb('C%dLRx' % k) + sum(abs(VI[k][j]) * E6[j] for j in range(4))) / 2 ** 96
    lz = (cb('C%dLZx' % k) + sum(abs(VI[k][j]) * E7[j] for j in range(4))) / 2 ** 96
    b.append([bu, bz, AC if k == 0 else Fr(0), AC if k == 0 else Fr(0), lu, lz])
# rational upper bounds of the coefficients (6 significant digits)
bq = [[up(x, 6) if x > 0 else Fr(0) for x in row] for row in b]
aD = [up(sum(Fr(RS) ** k * bq[k][i] for k in range(4)), 6) for i in range(6)]
print('coefficient bounds', [[float(x) for x in row] for row in bq])
print('disc bounds aD', [float(x) for x in aD])
mE, mE4, mQQ, mN, g = LM.node_bounds(aD)
eN, resR, resZ = LM.trees(LM.LAM1)
lam = LM.LAM1
eNt = ('n', Fr(1), ('m', ('c', -lam), LM.eBm))
eFt = ('m', ('s', ('c', Fr(1)), ('m', ('c', lam / 2), LM.eBm)), eNt)
Yt = {k: ('m', ('c', Fr(1, 2)), ('m', LM.W3, K)) for k, K in [('D', LM.KD), ('R', LM.KR), ('Z', LM.KZ)]}
corrR = ('s', ('m', ('m', eFt, Yt['D']), ('v', 4)), ('m', eFt, Yt['R']))
corrZ = ('s', ('m', ('m', eFt, Yt['D']), ('v', 5)), ('m', eFt, Yt['Z']))
MR = up(LM.mQ(aD, g, resR, {}), 4)
MZ = up(LM.mQ(aD, g, resZ, {}), 4)
CR = up(LM.mQ(aD, g, corrR, {}), 4)
CZ = up(LM.mQ(aD, g, corrZ, {}), 4)
hEw = Fr(1, 2 ** 32)
MtR = up(MR + hEw * RS * CR, 4)
MtZ = up(MZ + hEw * RS * CZ, 4)
rem = lambda M: 3 * M * Fr(1, RS) ** 4 / (1 - Fr(1, RS))
print('node bounds mE %s mE4 %s mQQ %s mN %s g %s' % (float(mE), float(mE4), float(mQQ), float(mN), float(g)))
print('M_R %s M_Z %s (maj %s %s corr %s %s)  remainder %.3e %.3e' % (float(MtR), float(MtZ), float(MR), float(MZ),
      float(CR), float(CZ), float(rem(MtR)), float(rem(MtZ))))
EJ = []
for j in range(1, 5):
    txt = open(D + 'RationalStellaratorGCEw%dOutH.lean' % j).read()
    vals = []
    for nm in ['resR', 'resZ']:
        m = re.search(r'theorem normHE%d_%s .*?\(\(\((.*?) : ℚ\) : ℚ\) : ℝ\)' % (j, nm), txt, re.S)
        vals.append(Fr(m.group(1).replace(' ', '')) / 2 ** 96)
    EJ.append(vals)
emaxR = max(v[0] for v in EJ)
emaxZ = max(v[1] for v in EJ)
e0E = Fr(7, 10 ** 21)
print('node residuals', [[float(x) for x in v] for v in EJ])
print('e0 check R: %.4e  Z: %.4e  <= %.1e' % (2 * emaxR + rem(MtR), 2 * emaxZ + rem(MtZ), float(e0E)))
assert 2 * emaxR + rem(MtR) <= e0E and 2 * emaxZ + rem(MtZ) <= e0E
pickle.dump(dict(bq=bq, aD=aD, g=g, mE=mE, mE4=mE4, mQQ=mQQ, mN=mN, MR=MR, MZ=MZ, CR=CR, CZ=CZ, MtR=MtR,
                 MtZ=MtZ, EJ=EJ), open(os.environ.get('EW_GLUE_PKL', 'glue.pkl'), 'wb'))


def ql(q):
    q = Fr(q)
    return '(%d : ℚ)' % q.numerator if q.denominator == 1 else '(%d / %d : ℚ)' % (q.numerator, q.denominator)


HEADER = '''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

'''
mu = open(D + 'RationalStellaratorGCMuMaj.lean').read()
i0 = mu.index('/-- The bounds `aTQ` are nonnegative. -/')
i1 = mu.index('set_option maxRecDepth 100000 in\n/-- **The Taylor constant of the `R`-residual**')
chunk = mu[i0:i1]
for a_, b_ in [('aTQ_nonneg', 'aDQ_nonneg'), ('mu_maj_E4', 'ewD_maj_E4'), ('mu_maj_E', 'ewD_maj_E'),
               ('mu_maj_Q', 'ewD_maj_Q'), ('gQ_nonneg', 'gDQ_nonneg'), ('nodesOK_eV4', 'nodesOK_eV4D'),
               ('nodesOK_eVD4', 'nodesOK_eV4D'),
               ('nodesOK_eBm', 'nodesOK_eBmD'), ('maj_eBm_le', 'maj_eBm_leD'), ('nodesOK_eN', 'nodesOK_eND'),
               ('nodesOK_eF', 'nodesOK_eFD'), ('nodesOK_eY', 'nodesOK_eYD'), ('nodesOK_res', 'nodesOK_resD'),
               ('aTQ', 'aDQ'), ('mE4Q', 'mE4DQ'), ('mEQ', 'mEDQ'), ('mQQ', 'mQDQ'), ('mNQ', 'mNDQ'),
               ('gQ', 'gDQ')]:
    chunk = chunk.replace(a_, b_)
chunk = re.sub(r'nodesOK_eV\b', 'nodesOK_eVD', chunk)
chunk = chunk.replace('nodesOK_eV4DD', 'nodesOK_eV4D').replace('nodesOK_eVDD', 'nodesOK_eVD')
chunk = chunk.replace('  have hm : PolyExprS.maj (fun i => (aDQ i : ℝ)) (.mul (.const (-(lam1 : ℂ))) eBm) ≤ (mNDQ : ℝ) := by',
                      '  have hm : PolyExprS.maj (fun i => (aDQ i : ℝ)) (.mul (.const (-(lam1 : ℂ))) eBm) ≤\n      (mNDQ : ℝ) := by')
chunk = chunk.replace('    NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) eYR ∧ NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) eYZ := by',
                      '    NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) eYR ∧\n      NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) eYZ := by')
vec = lambda xs: '![' + ',\n    '.join(ql(x) for x in xs) + ']'
disc = HEADER + '''public import PlasmaLean.Design.RationalStellaratorGCEwInterp
public import PlasmaLean.Design.RationalStellaratorGCMuMaj

/-!
# Validity and majorants on the complex disc of the scaled gyro-length

The energy-window torus family `K(s) = ∑_k s^k C_k` (`Design/RationalStellaratorGCEwInterp`)
extends to complex `s`. On the disc `|s| ≤ 2^20` its inputs `xK ι K(s)` are bounded by `aDQ`
(from the kernel-checked coefficient norms of `Design/RationalStellaratorGCEwComb`). This module
certifies, with the rational mirrors of `Design/RationalStellaratorGCMuMaj` evaluated by the kernel:

* node validity at `aDQ` with one node bound `g = gDQ` (`nodesOK_resD`, `nodesOK_corrD`);
* the majorants of the residual trees `T₀ = resR(1/256, λ₁)` and of the corrections
  `T₁ = F Y_D 𝓛u − F Y_R` (and the `z` versions) at `aDQ` (`ewD_maj`);
* uniformity in the pitch parameter `|λ| ≤ 1/16` (`ewD_valid_maj`, `ConstLe`).

These give the bound `M` of the analytic remainder of the interpolation in `s`.
Generated by `scripts/gc_kam/ew_glue.py`.

**Sanity.** `corrRQ_toS`: the mirror embeds to the correction expression at `λ₁`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCMu

open PlasmaLean.Design.RationalStellaratorGC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Theory.KAM.PQS

/-- Rational bounds of the inputs `xK ι K(s)` on the disc `|s| ≤ 2^20`. -/
def aDQ : Fin 6 → ℚ := %s

/-- The bound of the majorant of `E` on the disc. -/
def mEDQ : ℚ := %s
/-- The bound of the majorant of `E₄` on the disc. -/
def mE4DQ : ℚ := %s
/-- The bound of the majorant of `Q P P₄` on the disc. -/
def mQDQ : ℚ := %s
/-- The bound of the majorant under the node `(1 − λ₁|B|)^{−1/2}` on the disc. -/
def mNDQ : ℚ := %s
/-- The uniform node bound on the disc. -/
def gDQ : ℚ := %s

''' % (vec(aD), ql(mE), ql(mE4), ql(mQQ), ql(mN), ql(g)) + chunk + '''/-- The mirror of the correction of the `R`-residual, `F Y_D 𝓛u − F Y_R`. -/
def corrRQ : PQS (Fin 6) := .sub (.mul eYDFQ (.var 4)) eYRFQ

/-- The mirror of the correction of the `z`-residual, `F Y_D 𝓛z − F Y_z`. -/
def corrZQ : PQS (Fin 6) := .sub (.mul eYDFQ (.var 5)) eYZFQ

/-- **Sanity**: the mirror embeds to the correction expression at `λ₁`. -/
theorem corrRQ_toS : corrRQ.toS = corrR lam1 := by
  simp only [corrRQ, toS, eYDFQ, eYRFQ, eFQ_toS, eYDQ_toS, eYRQ_toS, corrR, eYDF, eYRF]

/-- The mirror of the `z`-correction embeds to it. -/
theorem corrZQ_toS : corrZQ.toS = corrZ lam1 := by
  simp only [corrZQ, toS, eYDFQ, eYZFQ, eFQ_toS, eYDQ_toS, eYZQ_toS, corrZ, eYDF, eYZF]

/-- The nodes of the correction mirrors at `aDQ`. -/
theorem nodesOK_corrD : NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) corrRQ.toS ∧
    NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) corrZQ.toS := by
  obtain ⟨hD, hR, hZ⟩ := nodesOK_eYD
  have hF := nodesOK_eFD
  rw [← eFQ_toS] at hF
  rw [← eYDQ_toS] at hD
  rw [← eYRQ_toS] at hR
  rw [← eYZQ_toS] at hZ
  exact ⟨⟨⟨⟨hF, hD⟩, trivial⟩, hF, hR⟩, ⟨⟨⟨hF, hD⟩, trivial⟩, hF, hZ⟩⟩

set_option maxRecDepth 100000 in
/-- **The kernel majorants on the disc.** -/
theorem ewD_maj : mQ aDQ gDQ resRQ ≤ %s ∧ mQ aDQ gDQ resZQ ≤ %s ∧
    mQ aDQ gDQ corrRQ ≤ %s ∧ mQ aDQ gDQ corrZQ ≤ %s := by
  decide +kernel

/-- **Validity and majorants on the disc, uniform in the pitch parameter**: at every bound
`0 ≤ a ≤ aDQ` and `|λ| ≤ 1/16`, the residual trees and the corrections are valid and
`T̂₀(a) + 2⁻³² 2^20 T̂₁(a) ≤ M`. -/
theorem ewD_valid_maj {a : Fin 6 → ℝ} (ha : ∀ i, 0 ≤ a i) (haa : ∀ i, a i ≤ aDQ i) {lm : ℝ}
    (hlm : |lm| ≤ lam1) :
    PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resRp ∧ PolyExprS.Valid a (corrR lm) ∧
    PolyExprS.maj a (gcFlowMu (1 / 256) lm).resRp + hEw * (2 ^ 20 : ℝ) * PolyExprS.maj a (corrR lm)
      ≤ (%s : ℝ) ∧
    PolyExprS.Valid a (gcFlowMu (1 / 256) lm).resZp ∧ PolyExprS.Valid a (corrZ lm) ∧
    PolyExprS.maj a (gcFlowMu (1 / 256) lm).resZp + hEw * (2 ^ 20 : ℝ) * PolyExprS.maj a (corrZ lm)
      ≤ (%s : ℝ) := by
  have hD0 : ∀ i, (0 : ℚ) ≤ aDQ i := by decide +kernel
  have hg0 : (0 : ℚ) ≤ gDQ := by decide +kernel
  obtain ⟨cR, cZ⟩ := constLe_res hlm
  obtain ⟨cD, cRc, cZc⟩ := constLe_corr hlm
  have kR : PolyExprS.ConstLe (corrR lm) corrRQ.toS := by
    simp only [corrR, corrRQ, toS]; exact .sub (.mul cD (PolyExprS.constLe_refl _)) cRc
  have kZ : PolyExprS.ConstLe (corrZ lm) corrZQ.toS := by
    simp only [corrZ, corrZQ, toS]; exact .sub (.mul cD (PolyExprS.constLe_refl _)) cZc
  obtain ⟨nR, nZ⟩ := nodesOK_resD
  obtain ⟨nCR, nCZ⟩ := nodesOK_corrD
  rw [← resRQ_toS] at nR cR
  rw [← resZQ_toS] at nZ cZ
  obtain ⟨m1, m2, m3, m4⟩ := ewD_maj
  have aD0 : ∀ i, (0 : ℝ) ≤ (aDQ i : ℝ) := fun i => by exact_mod_cast hD0 i
  have bnd : ∀ {e : PolyExprS ℂ (Fin 6)} {P : PQS (Fin 6)}, PolyExprS.ConstLe e P.toS →
      NodesOK (fun i => (aDQ i : ℝ)) (gDQ : ℝ) P.toS →
      PolyExprS.Valid a e ∧ PolyExprS.maj a e ≤ (mQ aDQ gDQ P : ℝ) := fun {e P} hc hn => by
    have hv' := valid_of_nodesOK hn
    have hva := hv'.mono ha haa
    refine ⟨hc.valid ha hva, ?_⟩
    calc PolyExprS.maj a e ≤ PolyExprS.maj a P.toS := hc.maj_le ha hva
      _ ≤ PolyExprS.maj (fun i => (aDQ i : ℝ)) P.toS := PolyExprS.maj_mono ha haa hv'
      _ ≤ (mQ aDQ gDQ P : ℝ) := PQS.maj_le hD0 hg0 P hn
  obtain ⟨v1, b1⟩ := bnd cR nR
  obtain ⟨v2, b2⟩ := bnd kR nCR
  obtain ⟨v3, b3⟩ := bnd cZ nZ
  obtain ⟨v4, b4⟩ := bnd kZ nCZ
  have q1 : (mQ aDQ gDQ resRQ : ℝ) ≤ %s := by exact_mod_cast m1
  have q2 : (mQ aDQ gDQ resZQ : ℝ) ≤ %s := by exact_mod_cast m2
  have q3 : (mQ aDQ gDQ corrRQ : ℝ) ≤ %s := by exact_mod_cast m3
  have q4 : (mQ aDQ gDQ corrZQ : ℝ) ≤ %s := by exact_mod_cast m4
  have h0 : (0 : ℝ) ≤ PolyExprS.maj a (corrR lm) := PolyExprS.maj_nonneg ha _
  have h0' : (0 : ℝ) ≤ PolyExprS.maj a (corrZ lm) := PolyExprS.maj_nonneg ha _
  refine ⟨v1, v2, ?_, v3, v4, ?_⟩
  · have : hEw * (2 ^ 20 : ℝ) * PolyExprS.maj a (corrR lm) ≤ hEw * 2 ^ 20 * %s := by
      have := b2.trans q3; unfold hEw; gcongr
    norm_num [hEw] at this ⊢; push_cast at q1 ⊢; linarith
  · have : hEw * (2 ^ 20 : ℝ) * PolyExprS.maj a (corrZ lm) ≤ hEw * 2 ^ 20 * %s := by
      have := b4.trans q4; unfold hEw; gcongr
    norm_num [hEw] at this ⊢; push_cast at q2 ⊢; linarith

end PlasmaLean.Design.RationalStellaratorGCMu
''' % (ql(MR), ql(MZ), ql(CR), ql(CZ), ql(MtR), ql(MtZ), ql(MR), ql(MZ), ql(CR), ql(CZ), ql(CR), ql(CZ))
open(D + 'RationalStellaratorGCEwDisc.lean', 'w').write(disc)
print('EwDisc emitted')

# ------------------------------------------------------------------------------------- EwRes
LB = {}


def qlr(q):
    q = Fr(q)
    return '(%d : ℝ)' % q.numerator if q.denominator == 1 else '(%d / %d : ℝ)' % (q.numerator, q.denominator)


NN = {}
DEN = {}
from math import lcm
for k in range(4):
    den = 1
    for j in range(4):
        den = lcm(den, VI[k][j].denominator)
    DEN[k] = den
    NN[k] = [int(VI[k][j] * den) for j in range(4)]
FAMI = {'U': 4, 'Z': 5, 'LRx': 6, 'LZx': 7, 'thU': 8, 'thZ': 9}


def rq(nm):
    return ql(COMB[nm][4])


def isum(k, f, X='X'):
    return ' + '.join('((%d : ℤ) : FA) * %s %d' % (NN[k][j], X, j) for j in range(4))


res = HEADER + '''public import PlasmaLean.Design.RationalStellaratorGCEwComb
public import PlasmaLean.Design.RationalStellaratorGCEwConst
public import PlasmaLean.Design.RationalStellaratorGCEwNodes
public import PlasmaLean.Design.RationalStellaratorGCEwDisc

/-!
# The residual of the energy-window torus family

The **energy-window torus family** `K(s, λ) = (uEw s c, zEw s c) = ∑_j ℓ_j(s) K_j(λ)` (the Lagrange
interpolation of the four node tori in the scaled gyro-length `s = (ρ − 1/256)/2⁻³²`,
`λ = lamF c`). For every `|s| ≤ 1` its flow-form residual for `gcFlowMu (1/256 + s 2⁻³²) λ` is
bounded by `e₀ = 7 × 10⁻²¹` on the strip `r_A` (`ewResR_family`, `ewResZ_family`):

* the coefficients `C_k` of the family (and of `𝓛u`, `𝓛z`) are bounded through the kernel-checked
  integer combinations of `Design/RationalStellaratorGCEwComb` (`coef*_bd`);
* on the complex disc `|s| ≤ 2^20` the inputs are bounded by `aDQ` and the trees are valid with
  `T̂₀ + 2⁻¹² T̂₁ ≤ M` (`Design/RationalStellaratorGCEwDisc`);
* the node residuals are those of the node pipelines (`Design/RationalStellaratorGCEwNodes`);
* `Bd_interp` (`Theory/KAM/ParamInterp`) with the Lebesgue bound `2` gives
  `‖res(s)‖ ≤ 2 max_j e_j + 3 M 2⁻⁸⁰/(1 − 2⁻²⁰)`.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced). Generated by `scripts/gc_kam/ew_glue.py`.

**Sanity.** `uEw_node`: at the nodes the family is the node torus.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb WEll1Z2 Complex

/-- The node tori, `u`-component. -/
def UEw (c : ℂ) : Fin 4 → FA := fun j => xEw j c 4

/-- The node tori, `z`-component. -/
def ZEw (c : ℂ) : Fin 4 → FA := fun j => xEw j c 5

/-- **The energy-window torus family** (`u`-component) at the scaled gyro-length `s`. -/
def uEw (s : ℝ) (c : ℂ) : FA := combEw (UEw c) s

/-- **The energy-window torus family** (`z`-component). -/
def zEw (s : ℝ) (c : ℂ) : FA := combEw (ZEw c) s

/-- **Sanity**: at the nodes the family is the node torus. -/
theorem uEw_node (j : Fin 4) (c : ℂ) : uEw (tEw j) c = xEw j c 4 := combEw_node _ j

/-- The node tori are analytic. -/
theorem ana_UEw {c : ℂ} (hc : ‖c‖ = 1) : ∀ j, Ana (UEw c j) := by
  intro j; fin_cases j
  · exact ana_uHE1 hc
  · exact ana_uHE2 hc
  · exact ana_uHE3 hc
  · exact ana_uHE4 hc

/-- The node tori are analytic. -/
theorem ana_ZEw {c : ℂ} (hc : ‖c‖ = 1) : ∀ j, Ana (ZEw c j) := by
  intro j; fin_cases j
  · exact ana_zHE1 hc
  · exact ana_zHE2 hc
  · exact ana_zHE3 hc
  · exact ana_zHE4 hc

/-- The node tori are real. -/
theorem isReal_UEw {c : ℂ} (hc : ‖c‖ = 1) : ∀ j, IsReal (UEw c j) := by
  intro j; fin_cases j
  · exact isReal_uHE1 hc
  · exact isReal_uHE2 hc
  · exact isReal_uHE3 hc
  · exact isReal_uHE4 hc

/-- The node tori are real. -/
theorem isReal_ZEw {c : ℂ} (hc : ‖c‖ = 1) : ∀ j, IsReal (ZEw c j) := by
  intro j; fin_cases j
  · exact isReal_zHE1 hc
  · exact isReal_zHE2 hc
  · exact isReal_zHE3 hc
  · exact isReal_zHE4 hc

/-- From a bound of an integer multiple. -/
theorem bd_of_intMul {r : ℝ} {d : ℕ} (hd : 0 < d) {x : FA} {R : ℝ}
    (h : Bd r (((d : ℤ) : FA) * x) R) : Bd r x (R / d) := by
  have h2 := h.smul ((d : ℂ)⁻¹)
  have e : ((d : ℂ))⁻¹ • (((d : ℤ) : FA) * x) = x := by
    rw [show (((d : ℤ) : FA)) = algebraMap ℂ FA (d : ℂ) by simp, ← Algebra.smul_def, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast hd.ne'), one_smul]
  rw [e, norm_inv, Complex.norm_natCast] at h2
  exact h2.le (by rw [div_eq_inv_mul])

'''
for k in range(4):
    res += '''/-- The coefficient `C_%d` as an integer combination (scale `%d`). -/
theorem coefEw_int%d (X : Fin 4 → FA) :
    ((%d : ℤ) : FA) * coefEw X %d = %s := by
  refine ext_eval fun θ ψ => ?_
  simp [coefEw, Fin.sum_univ_four, ViEw, eval_add', eval_mul, eval_neg', eval_algebraMap,
    Algebra.smul_def]
  ring

''' % (k, DEN[k], k, DEN[k], k, isum(k, None))
# coefficient bounds for u, z, thU, thZ (stored families) and Lt
for fam, comp, idx in [('U', 'u', 4), ('Z', 'z', 5), ('LRx', 'lrx', 6), ('LZx', 'lzx', 7), ('thU', 'thu', 8),
                       ('thZ', 'thz', 9)]:
    for k in range(4):
        X = '(fun j => xEw j c %d)' % idx
        res += '''set_option exponentiation.threshold 4096 in
/-- `‖C_%d‖` of the family `%s`. -/
theorem coef_%s_%d {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ}
    (hc : ‖c‖ = 1) : Bd r (coefEw %s %d) (((%s : ℚ) : ℝ) / %d) := by
  have h := normEw_C%d%s hr hq hc
  have e := coefEw_int%d %s
  beta_reduce at e
  rw [← e] at h
  exact bd_of_intMul (by norm_num) h

''' % (k, fam, fam, k, X, k, rq('C%d%s' % (k, fam)), DEN[k], k, fam, k, X)

res += """/-- `coefEw` is additive. -/
theorem coefEw_add (X Y : Fin 4 → FA) (k : Fin 4) :
    coefEw (fun j => X j + Y j) k = coefEw X k + coefEw Y k := by
  simp only [coefEw, smul_add, Finset.sum_add_distrib]

/-- `coefEw` commutes with scalars. -/
theorem coefEw_smul (a : ℂ) (X : Fin 4 → FA) (k : Fin 4) :
    coefEw (fun j => a • X j) k = a • coefEw X k := by
  simp only [coefEw, Finset.smul_sum, smul_comm a]

/-- A crude bound of a coefficient from bounds of the node values. -/
theorem Bd_coefEw {r : ℝ} {X : Fin 4 → FA} {B : Fin 4 → ℝ} (h : ∀ j, Bd r (X j) (B j)) (k : Fin 4) :
    Bd r (coefEw X k) (∑ j, |ViEw k j| * B j) := by
  simp only [coefEw, Fin.sum_univ_four]
  have t : ∀ j, Bd r (((ViEw k j : ℝ) : ℂ) • X j) (|ViEw k j| * B j) := fun j => by
    have := (h j).smul ((ViEw k j : ℝ) : ℂ); rwa [Complex.norm_real, Real.norm_eq_abs] at this
  exact (((t 0).add (t 1)).add (t 2)).add (t 3)

"""
for comp, fam, idx, ei, nm6 in [('U', 'LRx', 4, 6, 'u'), ('Z', 'LZx', 5, 7, 'z')]:
    EQ = [up(HS[jj]['E'][ei], 4) for jj in range(4)]
    bound = (Fr(COMB['C0%s' % fam][4]) * 0)  # placeholder
    for k in range(4):
        tot = Fr(COMB['C%d%s' % (k, fam)][4]) / DEN[k] + sum(abs(VI[k][jj]) * EQ[jj] for jj in range(4))
        LB[(comp, k)] = tot / 2 ** 96
        res += """set_option linter.unusedSimpArgs false in
set_option exponentiation.threshold 4096 in
/-- `‖𝓛 C_%d‖` of the family (`%s`-component). -/
theorem coef_L%s_%d {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ}
    (hc : ‖c‖ = 1) : Bd r (Lt KamTorusA.iota (coefEw (%sEw c) %d)) %s := by
  have hA := coef_%s_%d hr hq hc
  have herr : ∀ j, Bd r ((2 : ℂ) ^ 96 • Lt KamTorusA.iota (%sEw c j) - xEw j c %d)
      (![%s, %s, %s, %s] j) := by
    intro j; fin_cases j
    · exact (ballLt_HE1 hr hq hc).%s.le (by
        simpa using qle (show EHE1 %d ≤ %s by decide +kernel))
    · exact (ballLt_HE2 hr hq hc).%s.le (by
        simpa using qle (show EHE2 %d ≤ %s by decide +kernel))
    · exact (ballLt_HE3 hr hq hc).%s.le (by
        simpa using qle (show EHE3 %d ≤ %s by decide +kernel))
    · exact (ballLt_HE4 hr hq hc).%s.le (by
        simpa using qle (show EHE4 %d ≤ %s by decide +kernel))
  have hB := Bd_coefEw herr %d
  have e : (2 : ℂ) ^ 96 • Lt KamTorusA.iota (coefEw (%sEw c) %d) =
      coefEw (fun j => xEw j c %d) %d +
        coefEw (fun j => (2 : ℂ) ^ 96 • Lt KamTorusA.iota (%sEw c j) - xEw j c %d) %d := by
    rw [Lt, dS_coefEw (ana_%sEw hc), ← coefEw_smul, ← coefEw_add]
    congr 1; funext j; simp [Lt]
  have h2 := (hA.add hB).smul (((2 : ℂ) ^ 96)⁻¹)
  rw [← e, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at h2
  refine h2.le ?_
  simp only [Fin.sum_univ_four, ViEw, Matrix.cons_val, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, norm_inv, norm_pow, Complex.norm_ofNat]
  norm_num

""" % (k, nm6, comp, k, comp, k, qlr(LB[(comp, k)]), fam, k, comp, ei,
       qlr(EQ[0]), qlr(EQ[1]), qlr(EQ[2]), qlr(EQ[3]),
       '1' if comp == 'U' else '2', ei, ql(EQ[0]), '1' if comp == 'U' else '2', ei, ql(EQ[1]),
       '1' if comp == 'U' else '2', ei, ql(EQ[2]), '1' if comp == 'U' else '2', ei, ql(EQ[3]),
       k, comp, k, ei, k, comp, ei, k, comp)
# the D0 combinations: C_0 - (embedded low-resolution torus)
for fam, idx, emb, lhs_emb in [('U', 4, 10, 'xLM c 4'), ('Z', 5, 11, 'xLM c 5'), ('thU', 8, 12, 'dTh (xLM c 4)'),
                               ('thZ', 9, 13, 'dTh (xLM c 5)')]:
    X = '(fun j => xEw j c %d)' % idx
    sel = {'U': '1', 'Z': '2.1', 'thU': '2.2.1', 'thZ': '2.2.2'}[fam]
    res += """set_option exponentiation.threshold 4096 in
/-- `‖C_0 − f_L‖` of the family `%s` (`f_L` the certified low-resolution torus). -/
theorem coefD0_%s {r : ℝ} (hr : 0 ≤ r) (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) {c : ℂ}
    (hc : ‖c‖ = 1) : Bd r (coefEw %s 0 - %s) (((%s : ℚ) : ℝ) / %d) := by
  have h := normEw_D0%s hr hq hc
  have e := coefEw_int0 %s
  beta_reduce at e
  have e2 : xHE1 c %d = %s := (embHE1 hc).%s
  have e3 : ((%d : ℤ) : FA) * (coefEw %s 0 - %s) = %s + ((-%d : ℤ) : FA) * xHE1 c %d := by
    rw [mul_sub, e, e2]; push_cast; ring
  rw [← e3] at h
  exact bd_of_intMul (by norm_num) h

""" % (fam, fam, X, lhs_emb, rq('D0%s' % fam), DEN[0], fam, X, emb, lhs_emb, sel, DEN[0], X, lhs_emb,
       isum(0, None).replace('X ', 'xEw ').replace('* xEw 0', '* xEw 0 c %d' % idx).replace('* xEw 1', '* xEw 1 c %d' % idx).replace('* xEw 2', '* xEw 2 c %d' % idx).replace('* xEw 3', '* xEw 3 c %d' % idx),
       DEN[0], emb)


bmat = '![' + ', '.join('![' + ', '.join(qlr(bq[k][i]) for i in range(6)) + ']' for k in range(4)) + ']'
res += """/-- Rational bounds of the coefficients of the inputs (`k`, input `i`). -/
def bEw : Fin 4 → Fin 6 → ℝ := @BMAT@

set_option linter.unusedSimpArgs false in
/-- The inputs are bounded by `bEw` on the strip `r_A`. -/
theorem inputsEw_bd {c : ℂ} (hc : ‖c‖ = 1) :
    ∀ k i, Bd KamTorusA.rA (inputsEw (UEw c) (ZEw c) k i) (bEw k i) := by
  have hr := rA_nonneg'
  have hq := exp_rA_le'
  intro k i
  fin_cases k <;> fin_cases i <;> simp only [inputsEw, bEw, Matrix.cons_val, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one,
    ↓reduceIte, Fin.reduceEq]
""".replace('@BMAT@', bmat)
for k in range(4):
    for i in range(6):
        if i == 0:
            t = "(coef_U_%d hr hq hc).le (by norm_num)" % k
        elif i == 1:
            t = "(coef_Z_%d hr hq hc).le (by norm_num)" % k
        elif i in (2, 3):
            t = ("(Bd_%sS_q hq).le (by norm_num)" % ('c' if i == 2 else 's')) if k == 0 else "Bd_zero _"
        elif i == 4:
            t = "(coef_LU_%d hr hq hc).le (by norm_num)" % k
        else:
            t = "(coef_LZ_%d hr hq hc).le (by norm_num)" % k
        res += "  · exact %s\n" % t
res += "\n"


avec = '![' + ', '.join(qlr(x) for x in aD) + ']'
RHOS = ['(16777215 / 4294967296 : ℝ)', '(268435451 / 68719476736 : ℝ)', '(268435461 / 68719476736 : ℝ)',
        '(16777217 / 4294967296 : ℝ)']
for comp, Mt, ecomp in [('R', MtR, 0), ('Z', MtZ, 1)]:
    ev = '![' + ', '.join(qlr(EJ[j][ecomp]) for j in range(4)) + ']'
    emax = max(EJ[j][ecomp] for j in range(4))
    res += """/-- The node residual bounds (`%s`-component). -/
def e%sEw : Fin 4 → ℝ := %s

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
/-- **The residual of the energy-window torus family** (`%s`-component): for every scaled
gyro-length `|s| ≤ 1` and every pitch parameter `λ = lamF c`, `‖D̃ 𝓛K − ñ‖_{r_A} ≤ e₀` for the field
at `ρ = 1/256 + s 2⁻³²`. -/
theorem ewRes%s_family {s : ℝ} (hs : |s| ≤ 1) {c : ℂ} (hc : ‖c‖ = 1) :
    Bd KamTorusA.rA ((gcFlowMu (1 / 256 + s * hEw) (lamF c)).res%s KamTorusA.iota (uEw s c)
      (zEw s c)) e0E := by
  have hU := ana_UEw hc
  have hZ := ana_ZEw hc
  have hl : |lamF c| ≤ RationalStellaratorGCMu.lam1 := abs_lamF_le hc
  have hD0 : ∀ i, (0 : ℝ) ≤ (RationalStellaratorGCMu.aDQ i : ℝ) := fun i => by
    have := (show ∀ i, (0 : ℚ) ≤ RationalStellaratorGCMu.aDQ i by decide +kernel) i
    exact_mod_cast this
  obtain ⟨vR, vCR, mR, vZ, vCZ, mZ⟩ :=
    RationalStellaratorGCMu.ewD_valid_maj hD0 (fun _ => le_rfl) hl
  have hab : ∀ i, ∑ k : Fin 4, ((2 ^ 20 : NNReal) : ℝ) ^ k.val * bEw k i ≤
      (RationalStellaratorGCMu.aDQ i : ℝ) := by
    intro i; fin_cases i <;>
      simp [Fin.sum_univ_four, bEw, RationalStellaratorGCMu.aDQ] <;> norm_num
  have he : ∀ j, Bd KamTorusA.rA (interpF (inputsEw (UEw c) (ZEw c))
      (gcFlowMu (1 / 256) (lamF c)).res%sp (corr%s (lamF c)) hEw (tEw j)) (e%sEw j) := by
    intro j
    rw [← res%s_combEw hU hZ, combEw_node, combEw_node]
    obtain ⟨r1, r2, r3, r4⟩ := rhoEw_center
    fin_cases j
    · simp only [e%sEw, Fin.zero_eta, Matrix.cons_val_zero]; rw [← r1]
      exact (ewRes%s_1 hc).le (by norm_num)
    · simp only [e%sEw, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; rw [← r2]
      exact (ewRes%s_2 hc).le (by norm_num)
    · simp only [e%sEw, Fin.reduceFinMk, Matrix.cons_val]; rw [← r3]
      exact (ewRes%s_3 hc).le (by norm_num)
    · simp only [e%sEw, Fin.reduceFinMk, Matrix.cons_val]; rw [← r4]
      exact (ewRes%s_4 hc).le (by norm_num)
  have hI := Bd_interp rA_nonneg' (inputsEw (UEw c) (ZEw c)) bEw (inputsEw_bd hc)
    (R := 2 ^ 20) (by norm_num) hab v%s vC%s (κ := hEw) (by norm_num [hEw])
    (by push_cast at m%s ⊢; exact m%s) tEw (wEw s) e%sEw s (ρ := 1) (Λ := 2) (by norm_num)
    (fun j => by fin_cases j <;> norm_num [tEw]) hs
    (wEw_leb s (abs_le.mp hs).1 (abs_le.mp hs).2) (wEw_exact s) he
  rw [uEw, zEw, res%s_combEw hU hZ]
  refine hI.le ?_
  have hw := wEw_leb s (abs_le.mp hs).1 (abs_le.mp hs).2
  have hsum : ∑ j, |wEw s j| * e%sEw j ≤ (∑ j, |wEw s j|) * %s := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    fin_cases j <;> norm_num [e%sEw]
  have h2 : (∑ j, |wEw s j|) * %s ≤ 2 * %s :=
    mul_le_mul_of_nonneg_right hw (by norm_num)
  have hrem : (1 + 2) * %s * (1 / ((2 ^ 20 : NNReal) : ℝ)) ^ 4 / (1 - 1 / ((2 ^ 20 : NNReal) : ℝ)) ≤
      7 / 10 ^ 21 - 2 * %s := by
    push_cast; norm_num
  rw [e0E]
  linarith

""" % (comp, comp, ev, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp, comp,
       comp, comp, comp, comp, comp, comp, comp, qlr(emax), comp, qlr(emax), qlr(emax), qlr(Mt), qlr(emax))

open(D + 'RationalStellaratorGCEwRes.lean', 'w').write(res + 'end PlasmaLean.Design.RationalStellaratorGC\n')
print('EwRes (part) emitted')

# ----------------------------------------------------------------------------------- EwExact
def qv(nm):
    den, k, f, emb, Rq = COMB[nm]
    return Fr(Rq) / den


MU = Fr(1, 10 ** 11)
ELM = {4: Fr(59, 5000000000), 5: Fr(29, 2500000000), 6: Fr(59, 5000000000), 7: Fr(117, 10 ** 10)}
dK = {}
for fam, ei in [('U', 4), ('Z', 5), ('thU', 6), ('thZ', 7)]:
    dK[fam] = qv('D0%s' % fam) + sum(qv('C%d%s' % (k, fam)) for k in range(1, 4))
    assert MU + dK[fam] <= ELM[ei], (fam, float(dK[fam]))
nK = {fam: sum(qv('C%d%s' % (k, fam)) for k in range(4)) for fam in ['U', 'Z', 'thU', 'thZ']}
nL = {comp: sum(LB[(comp, k)] for k in range(4)) for comp in ['U', 'Z']}
caps = {'U': Fr(193, 1000), 'Z': Fr(1623, 10000), 'thU': Fr(327, 2000), 'thZ': Fr(1617, 10000)}
for fam in caps:
    assert nK[fam] <= caps[fam], (fam, float(nK[fam]))
assert nL['U'] <= Fr(547, 5000) and nL['Z'] <= Fr(1037, 10000)
print('distances to the low-resolution torus', {k: float(v) for k, v in dK.items()})
print('norms', {k: float(v) for k, v in nK.items()}, {k: float(v) for k, v in nL.items()})


def ksum(fam):
    return ' + '.join('((%s : ℚ) : ℝ) / %d' % (ql(COMB['C%d%s' % (k, fam)][4]).replace(' : ℚ', '').strip('()'), DEN[k])
                      for k in range(1, 4))


ex = HEADER + '''public import PlasmaLean.Design.RationalStellaratorGCEwRes
public import PlasmaLean.Design.RationalStellaratorGCEwConst

/-!
# Exact invariant tori over the energy window

For every gyro-length `ρ ∈ rhoEw = [1/256 − 2⁻³², 1/256 + 2⁻³²]` and every pitch parameter
`λ = μB₀/E ∈ [0, 1/16]` the hypotheses `KamH` of the KAM theorem with inverse-square-root nodes hold
for the field `gcFlowMu ρ λ` at the energy-window torus family `K(s, λ)` (`s = (ρ − 1/256)/2⁻³²`)
with the constants `cE` (`ew_kamH`):

* the residual is `ewResR_family`, `ewResZ_family` (interpolation in `s` with analytic remainder);
* every torus `μ`-close to `K(s, λ)` lies in the admissibility balls of the certified
  low-resolution chain (`ew_close_balls`: `‖K(s) − K_L‖ ≤ 7.1 × 10⁻⁹ < 1.18 × 10⁻⁸`), so the
  bounds of `Design/RationalStellaratorGCEwAdm` apply;
* the global conditions are `ew_global`.

**Main result** (`ew_family_torus`): an exact real analytic invariant torus of the flow form of
`gcFlowMu ρ λ` (strip `r_A/7`, `ι = (75 + √5)/562`), `10⁻¹¹`-close to `K(s, λ)`.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced). Generated by `scripts/gc_kam/ew_glue.py`.

**Sanity.** `rho0_mem_rhoEw`: the design gyro-length `1/256` lies in the window.
-/

@[expose] public section
noncomputable section

set_option linter.style.longLine false

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Certificates.KronExpr
  PlasmaLean.Certificates.KronBall PlasmaLean.Certificates.KronBallCheb WEll1Z2 Complex

/-- **The energy window of gyro-lengths** `[1/256 − 2⁻³², 1/256 + 2⁻³²]` (model units). -/
def rhoEw : Set ℝ := Set.Icc (1 / 256 - hEw) (1 / 256 + hEw)

/-- **Sanity**: the design gyro-length lies in the window. -/
theorem rho0_mem_rhoEw : (1 / 256 : ℝ) ∈ rhoEw := ⟨by norm_num [hEw], by norm_num [hEw]⟩

/-- The scaled gyro-length of a point of the window lies in `[−1, 1]`. -/
theorem abs_sEw_le {ρ : ℝ} (h : ρ ∈ rhoEw) : |(ρ - 1 / 256) / hEw| ≤ 1 := by
  obtain ⟨h1, h2⟩ := h
  have hp : (0 : ℝ) < hEw := by norm_num [hEw]
  rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]; constructor <;> linarith

/-- The gyro-length in terms of the scaled one. -/
theorem rho_eq_sEw (ρ : ℝ) : 1 / 256 + (ρ - 1 / 256) / hEw * hEw = ρ := by
  have hp : (0 : ℝ) < hEw := by norm_num [hEw]
  field_simp; ring

/-- A family `∑_k s^k C_k` is within the sum of the coefficient bounds of `C_0`'s target. -/
theorem Bd_combEw_sub {r : ℝ} {X : Fin 4 → FA} {Y : FA} {B0 B1 B2 B3 : ℝ}
    (h0 : Bd r (coefEw X 0 - Y) B0) (h1 : Bd r (coefEw X 1) B1) (h2 : Bd r (coefEw X 2) B2)
    (h3 : Bd r (coefEw X 3) B3) {s : ℝ} (hs : |s| ≤ 1) :
    Bd r (combEw X s - Y) (B0 + B1 + B2 + B3) := by
  rw [combEw_eq, Fin.sum_univ_four]
  have hk : ∀ k : ℕ, ‖((s : ℂ) ^ k)‖ ≤ 1 := fun k => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]; exact pow_le_one₀ (abs_nonneg _) hs
  have t : ∀ {x : FA} {B : ℝ} (k : ℕ), Bd r x B → Bd r (((s : ℂ) ^ k) • x) B := fun k h =>
    (h.smul _).le (by have := mul_le_mul_of_nonneg_right (hk k) h.nonneg; linarith)
  have e : ((s : ℂ) ^ (0 : Fin 4).val) • coefEw X 0 + ((s : ℂ) ^ (1 : Fin 4).val) • coefEw X 1 +
      ((s : ℂ) ^ (2 : Fin 4).val) • coefEw X 2 + ((s : ℂ) ^ (3 : Fin 4).val) • coefEw X 3 - Y =
      (coefEw X 0 - Y) + ((s : ℂ) ^ 1) • coefEw X 1 + ((s : ℂ) ^ 2) • coefEw X 2 +
        ((s : ℂ) ^ 3) • coefEw X 3 := by simp; abel
  rw [e]
  exact ((h0.add (t 1 h1)).add (t 2 h2)).add (t 3 h3)

'''
for fam, X, Y, ei, cap in [('U', '(UEw c)', 'xLM c 4', 4, None), ('Z', '(ZEw c)', 'xLM c 5', 5, None)]:
    pass
ex += """/-- A cubic `∑_k s^k Y_k` with `|s| ≤ 1` is bounded by the sum of the bounds of the `Y_k`. -/
theorem bd_poly4 {r : ℝ} {Y : Fin 4 → FA} {B : Fin 4 → ℝ} (h : ∀ k, Bd r (Y k) (B k)) {s : ℝ}
    (hs : |s| ≤ 1) : Bd r (∑ k : Fin 4, ((s : ℂ) ^ k.val) • Y k) (∑ k, B k) := by
  have hk : ∀ k : ℕ, ‖((s : ℂ) ^ k)‖ ≤ 1 := fun k => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]; exact pow_le_one₀ (abs_nonneg _) hs
  have t : ∀ k : Fin 4, Bd r (((s : ℂ) ^ k.val) • Y k) (B k) := fun k =>
    ((h k).smul _).le (by have := mul_le_mul_of_nonneg_right (hk k.val) (h k).nonneg; linarith)
  simp only [Fin.sum_univ_four]
  exact (((t 0).add (t 1)).add (t 2)).add (t 3)

set_option exponentiation.threshold 4096 in
/-- **The family is close to the certified low-resolution torus** (`u, z, ∂_θu, ∂_θz`), and bounded. -/
theorem ew_family_near {s : ℝ} (hs : |s| ≤ 1) {c : ℂ} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16) :
    Bd r (uEw s c - xLM c 4) (%s) ∧ Bd r (zEw s c - xLM c 5) (%s) ∧
    Bd r (dTh (uEw s c) - dTh (xLM c 4)) (%s) ∧ Bd r (dTh (zEw s c) - dTh (xLM c 5)) (%s) ∧
    Bd r (uEw s c) (%s) ∧ Bd r (zEw s c) (%s) ∧ Bd r (dTh (uEw s c)) (%s) ∧
    Bd r (dTh (zEw s c)) (%s) ∧ Bd r (Lt KamTorusA.iota (uEw s c)) (%s) ∧
    Bd r (Lt KamTorusA.iota (zEw s c)) (%s) := by
  have hU := ana_UEw hc
  have hZ := ana_ZEw hc
  have eU : ∀ j, dTh (UEw c j) = xEw j c 8 := by
    intro j; fin_cases j
    · exact (dTh_xHE1_U hc).symm
    · exact (dTh_xHE2_U hc).symm
    · exact (dTh_xHE3_U hc).symm
    · exact (dTh_xHE4_U hc).symm
  have eZ : ∀ j, dTh (ZEw c j) = xEw j c 9 := by
    intro j; fin_cases j
    · exact (dTh_xHE1_Z hc).symm
    · exact (dTh_xHE2_Z hc).symm
    · exact (dTh_xHE3_Z hc).symm
    · exact (dTh_xHE4_Z hc).symm
  have dU : dTh (uEw s c) = combEw (fun j => xEw j c 8) s := by
    rw [uEw, dTh, dS_combEw hU]; congr 1; funext j; exact eU j
  have dZ : dTh (zEw s c) = combEw (fun j => xEw j c 9) s := by
    rw [zEw, dTh, dS_combEw hZ]; congr 1; funext j; exact eZ j
  have b0 : Bd r (0 : FA) 0 := Bd_zero r
  have nU := Bd_combEw_sub (Y := 0) (by rw [sub_zero]; exact coef_U_0 hr hq hc) (coef_U_1 hr hq hc)
    (coef_U_2 hr hq hc) (coef_U_3 hr hq hc) hs
  have nZ := Bd_combEw_sub (Y := 0) (by rw [sub_zero]; exact coef_Z_0 hr hq hc) (coef_Z_1 hr hq hc)
    (coef_Z_2 hr hq hc) (coef_Z_3 hr hq hc) hs
  have nA := Bd_combEw_sub (Y := 0) (by rw [sub_zero]; exact coef_thU_0 hr hq hc)
    (coef_thU_1 hr hq hc) (coef_thU_2 hr hq hc) (coef_thU_3 hr hq hc) hs
  have nB := Bd_combEw_sub (Y := 0) (by rw [sub_zero]; exact coef_thZ_0 hr hq hc)
    (coef_thZ_1 hr hq hc) (coef_thZ_2 hr hq hc) (coef_thZ_3 hr hq hc) hs
  rw [sub_zero] at nU nZ nA nB
  have LU : Lt KamTorusA.iota (uEw s c) = ∑ k : Fin 4, ((s : ℂ) ^ k.val) •
      Lt KamTorusA.iota (coefEw (UEw c) k) := by
    rw [uEw, combEw_eq]; simp only [Lt]
    rw [show (∑ k : Fin 4, ((s : ℂ) ^ k.val) • coefEw (UEw c) k) = combEw (UEw c) s from
      (combEw_eq _ _).symm, dS_combEw hU, combEw_eq]
    simp only [dS_coefEw hU]
  have LZ : Lt KamTorusA.iota (zEw s c) = ∑ k : Fin 4, ((s : ℂ) ^ k.val) •
      Lt KamTorusA.iota (coefEw (ZEw c) k) := by
    rw [zEw, combEw_eq]; simp only [Lt]
    rw [show (∑ k : Fin 4, ((s : ℂ) ^ k.val) • coefEw (ZEw c) k) = combEw (ZEw c) s from
      (combEw_eq _ _).symm, dS_combEw hZ, combEw_eq]
    simp only [dS_coefEw hZ]
  have hk : ∀ k : ℕ, ‖((s : ℂ) ^ k)‖ ≤ 1 := fun k => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]; exact pow_le_one₀ (abs_nonneg _) hs
  have t : ∀ {x : FA} {B : ℝ} (k : ℕ), Bd r x B → Bd r (((s : ℂ) ^ k) • x) B := fun k h =>
    (h.smul _).le (by have := mul_le_mul_of_nonneg_right (hk k) h.nonneg; linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Bd_combEw_sub (coefD0_U hr hq hc) (coef_U_1 hr hq hc) (coef_U_2 hr hq hc)
      (coef_U_3 hr hq hc) hs).le (by norm_num)
  · exact (Bd_combEw_sub (coefD0_Z hr hq hc) (coef_Z_1 hr hq hc) (coef_Z_2 hr hq hc)
      (coef_Z_3 hr hq hc) hs).le (by norm_num)
  · rw [dU]
    exact (Bd_combEw_sub (coefD0_thU hr hq hc) (coef_thU_1 hr hq hc) (coef_thU_2 hr hq hc)
      (coef_thU_3 hr hq hc) hs).le (by norm_num)
  · rw [dZ]
    exact (Bd_combEw_sub (coefD0_thZ hr hq hc) (coef_thZ_1 hr hq hc) (coef_thZ_2 hr hq hc)
      (coef_thZ_3 hr hq hc) hs).le (by norm_num)
  · exact nU.le (by norm_num)
  · exact nZ.le (by norm_num)
  · rw [dU]; exact nA.le (by norm_num)
  · rw [dZ]; exact nB.le (by norm_num)
  · rw [LU]
    exact (bd_poly4 (B := ![%s, %s, %s, %s]) (fun k => by
      fin_cases k
      exacts [coef_LU_0 hr hq hc, coef_LU_1 hr hq hc, coef_LU_2 hr hq hc, coef_LU_3 hr hq hc]) hs).le
      (by simp [Fin.sum_univ_four]; norm_num)
  · rw [LZ]
    exact (bd_poly4 (B := ![%s, %s, %s, %s]) (fun k => by
      fin_cases k
      exacts [coef_LZ_0 hr hq hc, coef_LZ_1 hr hq hc, coef_LZ_2 hr hq hc, coef_LZ_3 hr hq hc]) hs).le
      (by simp [Fin.sum_univ_four]; norm_num)

""" % (tuple(qlr(up(x, 6)) for x in [dK['U'], dK['Z'], dK['thU'], dK['thZ'], nK['U'], nK['Z'], nK['thU'],
                                       nK['thZ'], nL['U'], nL['Z']]) + tuple(qlr(LB[('U', k)]) for k in range(4)) + tuple(qlr(LB[('Z', k)]) for k in range(4)))
DK = {k: up(v, 6) for k, v in dK.items()}
NK = {k: up(v, 3) for k, v in nK.items()}
NL = {k: up(v, 3) for k, v in nL.items()}
pickle.dump(dict(DK=DK, NK=NK, NL=NL), open(os.environ.get('EW_NEAR_PKL', 'near.pkl'), 'wb'))
ex += """/-- **Every torus `μ`-close to the family lies in the admissibility balls** of the certified
low-resolution chain, with the torus bounds of `cE`. -/
theorem ew_close_balls {s : ℝ} (hs : |s| ≤ 1) {c : ℂ} (hc : ‖c‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (hrA : r ≤ KamTorusA.rA) {u z : FA}
    (hC : Close r KamTorusA.iota u z (uEw s c) (zEw s c) μM) :
    Bd r (u - xLM c 4) (ELM 4) ∧ Bd r (z - xLM c 5) (ELM 5) ∧ Bd r (dTh u - xLM c 6) (ELM 6) ∧
      Bd r (dTh z - xLM c 7) (ELM 7) ∧ Bd r u auM ∧ Bd r z azM ∧ Bd r (dTh u) aRtM ∧
      Bd r (dTh z) aztM ∧ Bd r (Lt KamTorusA.iota u) aLRM ∧ Bd r (Lt KamTorusA.iota z) aLzM := by
  have hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hrA).trans exp_rA_le'
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := ew_family_near hs hc hr hq
  have hc0 := ne_zero_of_norm_one_mu hc
  have hA6 : xLM c 6 = dTh (xLM c 4) := by rw [xLM_der_A hc0]; simp [dTh]
  have hB7 : xLM c 7 = dTh (xLM c 5) := by rw [xLM_der_B hc0]; simp [dTh]
  have e1 := qle (show (1 / 10 ^ 11 + %s : ℚ) ≤ ELM 4 by decide +kernel)
  have e2 := qle (show (1 / 10 ^ 11 + %s : ℚ) ≤ ELM 5 by decide +kernel)
  have e3 := qle (show (1 / 10 ^ 11 + %s : ℚ) ≤ ELM 6 by decide +kernel)
  have e4 := qle (show (1 / 10 ^ 11 + %s : ℚ) ≤ ELM 7 by decide +kernel)
  push_cast at e1 e2 e3 e4
  have tri : ∀ {x y w : FA} {a b : ℝ}, Bd r (x - y) a → Bd r (y - w) b → Bd r (x - w) (a + b) :=
    fun h1 h2 => by have := h1.add h2; rwa [sub_add_sub_cancel] at this
  have tri' : ∀ {x y : FA} {a b : ℝ}, Bd r (x - y) a → Bd r y b → Bd r x (a + b) :=
    fun h1 h2 => by have := h1.add h2; rwa [sub_add_cancel] at this
  refine ⟨(tri hC.du n1).le (by rw [μM]; linarith), (tri hC.dz n2).le (by rw [μM]; linarith),
    ?_, ?_, (tri' hC.du n5).le ?_, (tri' hC.dz n6).le ?_, (tri' hC.dut n7).le ?_,
    (tri' hC.dzt n8).le ?_, (tri' hC.duL n9).le ?_, (tri' hC.dzL n10).le ?_⟩
  · rw [hA6]; exact (tri hC.dut n3).le (by rw [μM]; linarith)
  · rw [hB7]; exact (tri hC.dzt n4).le (by rw [μM]; linarith)
  all_goals norm_num [auM, azM, aRtM, aztM, aLRM, aLzM, μM]

""" % (ql(DK['U']).strip('()').replace(' : ℚ', ''), ql(DK['Z']).strip('()').replace(' : ℚ', ''),
       ql(DK['thU']).strip('()').replace(' : ℚ', ''), ql(DK['thZ']).strip('()').replace(' : ℚ', ''))
ex += """/-- **Admissibility over the energy window** (from `μ`-closeness to the family torus). -/
theorem ewAdm {s : ℝ} (hs : |s| ≤ 1) {r : ℝ} (hr : 0 < r) (hrA : r ≤ KamTorusA.rA) {c : ℂ}
    (hc : ‖c‖ = 1) {u z : FA} (hu : Ana u) (hz : Ana z)
    (hC : Close r KamTorusA.iota u z (uEw s c) (zEw s c) μM) :
    (gcFlowMu (1 / 256 + s * hEw) (lamF c)).AdmBounds cE KamTorusA.iota r u z := by
  have hq : Real.exp r ≤ (74315 : ℕ) / 2 ^ 16 := (Real.exp_le_exp.2 hrA).trans exp_rA_le'
  obtain ⟨hU, hZ, hA, hB, tu, tz, tRt, tzt, tLR, tLz⟩ := ew_close_balls hs hc hr.le hrA hC
  have hρ : |1 / 256 + s * hEw - 1 / 256| ≤ hEw := by
    have hp : (0 : ℝ) < hEw := by norm_num [hEw]
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hp]
    exact mul_le_of_le_one_left hp.le hs
  exact ewAdm_core hρ hr hq hc hU hZ hA hB tu tz hu hz tRt tzt tLR tLz

/-- `|ρ| ≤ ρ_max` on the window. -/
theorem abs_rho_le_max {s : ℝ} (hs : |s| ≤ 1) :
    |1 / 256 + s * hEw| ≤ ((RationalStellaratorGCMu.rhoMaxQ : ℚ) : ℝ) := by
  have hp : (0 : ℝ) < hEw := by norm_num [hEw]
  have h1 : |s * hEw| ≤ hEw := by
    rw [abs_mul, abs_of_pos hp]; nlinarith [abs_nonneg s]
  have h2 := abs_add_le (1 / 256 : ℝ) (s * hEw)
  have e : ((RationalStellaratorGCMu.rhoMaxQ : ℚ) : ℝ) = 1 / 256 + hEw := by
    norm_num [RationalStellaratorGCMu.rhoMaxQ, hEw]
  rw [e]; rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 256)] at h2; linarith

/-- **All hypotheses of the KAM theorem over the energy window**: for every scaled gyro-length
`|s| ≤ 1` and every parameter `|c| = 1` (`λ = lamF c`). -/
theorem ew_kamH {s : ℝ} (hs : |s| ≤ 1) {c : ℂ} (hc : ‖c‖ = 1) :
    (gcFlowMu (1 / 256 + s * hEw) (lamF c)).KamH cE KamTorusA.iota (uEw s c) (zEw s c) e0E μM where
  G := ew_global (abs_rho_le_max hs) (abs_lamF_le hc)
  hδ0 := by norm_num [cE, δ0G, KamTorusA.rA]
  hρ6 := by norm_num [cE, δ0G, KamTorusA.rA]
  hθ := rfl
  he₀ := by norm_num [e0E]
  hκ := cE_kap_pos
  hsmall := cE_small
  hcK := cE_cK_nonneg
  hcL := cE_cL_nonneg
  hμK := cE_μK
  hμt := cE_μt
  hμL := cE_μL
  hadm := fun r u z hlo hhi hu hz hC => ewAdm hs
    (lt_of_lt_of_le (by norm_num [cE, δ0G, KamTorusA.rA]) hlo) hhi hc hu hz hC
  ana_u₀ := ana_combEw (ana_UEw hc) s
  ana_z₀ := ana_combEw (ana_ZEw hc) s
  real_u₀ := isReal_combEw (isReal_UEw hc) s
  real_z₀ := isReal_combEw (isReal_ZEw hc) s
  e0R := ewResR_family hs hc
  e0Z := ewResZ_family hs hc
  hvR' := (ew_valid cE_avecμ.1 cE_avecμ.2 _ (abs_lamF_le hc)).2.1
  hvZ' := (ew_valid cE_avecμ.1 cE_avecμ.2 _ (abs_lamF_le hc)).2.2

/-- **The energy-window torus family** at `(ρ, λ)` (`u`-component). -/
def uEwF (ρ lm : ℝ) : FA := uEw ((ρ - 1 / 256) / hEw) (cOfM lm)

/-- **The energy-window torus family** at `(ρ, λ)` (`z`-component). -/
def zEwF (ρ lm : ℝ) : FA := zEw ((ρ - 1 / 256) / hEw) (cOfM lm)

/-- **Exact invariant tori over the energy window of gyro-lengths and the pitch-angle cell.** For
every `ρ ∈ [1/256 − 2⁻³², 1/256 + 2⁻³²]` and every `λ ∈ [0, 1/16]` there is a real analytic torus
`(u, z)` (strip `r_A/7`) solving the flow-form invariance equation of the `μ > 0` passing field
`gcFlowMu ρ λ` exactly, with rotational transform `ι = (75 + √5)/562`, and `10⁻¹¹`-close to the
energy-window family torus `K(ρ, λ) = (1 + uEwF ρ λ, zEwF ρ λ)`. -/
theorem ew_family_torus {ρ lm : ℝ} (hρ : ρ ∈ rhoEw) (hlm : lm ∈ Set.Icc (0 : ℝ) (1 / 16)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlowMu ρ lm).resR KamTorusA.iota u z = 0 ∧
      (gcFlowMu ρ lm).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z (uEwF ρ lm) (zEwF ρ lm) μM := by
  have h := gcMu_kam_torus (ew_kamH (abs_sEw_le hρ) (cOfM_norm lm))
  rw [rInf_cE, lamF_cOfM hlm, rho_eq_sEw] at h
  exact h

end PlasmaLean.Design.RationalStellaratorGC
"""
open(D + 'RationalStellaratorGCEwExact.lean', 'w').write(ex)
print('EwExact emitted')
