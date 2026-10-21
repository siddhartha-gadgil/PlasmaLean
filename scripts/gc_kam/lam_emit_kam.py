"""UNTRUSTED: emit PlasmaLean/Design/RationalStellaratorGCMu{Adm,Exact}.lean (admissibility, residual,
constants and the KAM application for the mu > 0 passing torus family) by transforming the
rho-family files RationalStellaratorGCFam{Adm,Exact}.lean (structure identical) with the
constants of lam_maj.py (/tmp/lamc/lam_const.pkl) and the variable indices of the lam pipelines.
Every emitted proof is checked by Lean."""
import sys, os, re, pickle
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fam_ball  # noqa: F401
ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
C = pickle.load(open('/tmp/lamc/lam_const.pkl', 'rb'))
H = pickle.load(open(os.environ.get('LAM_PKL_H', '/tmp/lamc/lam_cert_H.pkl'), 'rb'))['H']
L = pickle.load(open(os.environ.get('LAM_PKL_L', '/tmp/lamc/lam_cert_L.pkl'), 'rb'))['L']
FH = pickle.load(open('/tmp/famw/fam_cert_H.pkl', 'rb'))['H']
FL = pickle.load(open('/tmp/famw/fam_cert_L.pkl', 'rb'))['L']
idxH = {v: k for k, v in H['names'].items()}
idxL = {v: k for k, v in L['names'].items()}
fidxH = {v: k for k, v in FH['names'].items()}
fidxL = {v: k for k, v in FL['names'].items()}
LAMDEN = int(os.environ.get('LAM_DEN', '16'))
LAM1 = Fr(2, LAMDEN)


def qfrac(q):
    q = Fr(q)
    return '%d / %d' % (q.numerator, q.denominator) if q.denominator != 1 else '%d' % q.numerator


def rename_tokens(s):
    s = re.sub(r'([A-Za-z_0-9]*)HF', lambda m: m.group(1) + 'HM', s)
    s = re.sub(r'([A-Za-z_0-9]*)LF', lambda m: m.group(1) + 'LM', s)
    return s


def fix_indices(s, tag, fidx, idx):
    """replace `XHF c 73` style indices (old Fam indices) by the new indices of the same names."""
    inv = {v: k for k, v in fidx.items()}

    def rep(m):
        i = int(m.group(2))
        nm = inv.get(i)
        if nm is None or nm not in idx:
            return m.group(0)
        return '%s%d' % (m.group(1), idx[nm])
    return rep


from ballcert import up as bup
from fam_ball import decode_slice


def q2lean(q):
    """a positive rational as a Lean real literal `a / b`."""
    q = Fr(q)
    if q.denominator == 1:
        return '%d' % q.numerator
    return '%d / %d' % (q.numerator, q.denominator)


RENAMES = [('ρF_mem', 'lamF_mem'), ('abs_ρF_le', 'abs_lamF_le'), ('μF', 'μM'), ('e0F', 'e0M'), ('auF', 'auM'),
           ('azF', 'azM'), ('aRtF', 'aRtM'), ('aztF', 'aztM'), ('aLRF', 'aLRM'), ('aLzF', 'aLzM'),
           ('sDF', 'sDM'), ('sRF', 'sRM'), ('sWF', 'sWM'), ('tTF', 'tTM'), ('τF', 'τM'), ('cF_au', 'cM_au'),
           ('cF', 'cM'), ('Bd_uF', 'Bd_uM'), ('Bd_zF', 'Bd_zM'), ('Bd_dTh_uF', 'Bd_dTh_uM'),
           ('Bd_dTh_zF', 'Bd_dTh_zM'), ('Bd_Lt_uF', 'Bd_Lt_uM'), ('Bd_Lt_zF', 'Bd_Lt_zM'), ('ana_uF', 'ana_uM'),
           ('ana_zF', 'ana_zM'), ('isReal_uF', 'isReal_uM'), ('isReal_zF', 'isReal_zM'), ('famResR', 'muResR'),
           ('famResZ', 'muResZ'), ('fdist_u', 'mdist_u'), ('fdist_z', 'mdist_z'), ('fdist_a', 'mdist_a'),
           ('fdist_b', 'mdist_b'), ('Bd_DdevF', 'Bd_DdevM'), ('Bd_WdevF', 'Bd_WdevM'), ('Bd_XtorF', 'Bd_XtorM'),
           ('avgY0', 'avgY0M'), ('avgY1', 'avgY1M'), ('adm_Di_F', 'adm_Di_M'), ('adm_Wi_F', 'adm_Wi_M'),
           ('adm_T_F', 'adm_T_M'), ('avF_le', 'avM_le'), ('avF', 'avM'), ('famAdm', 'muAdm'),
           ('uFam', 'uFamM'), ('zFam', 'zFamM'), ('cOf_norm', 'cOfM_norm'), ('cOf', 'cOfM'),
           ('ρF_cOf', 'lamF_cOfM'), ('rInf_cF', 'rInf_cM'), ('gc_family_torus', 'mu_family_torus')]


def apply_renames(s):
    for a, b in RENAMES:
        s = re.sub(r'(?<![A-Za-z0-9_\.])' + re.escape(a) + r'(?![A-Za-z0-9_\'])', b, s)
    s = re.sub(r'(?<![A-Za-z0-9_])cF\.', 'cM.', s)
    s = re.sub(r'(?<![A-Za-z0-9_])cF_([A-Za-z0-9_\'τμ]+)', r'cM_\1', s)
    return s


def literal(s, old, new):
    assert old in s, ('literal not found', old)
    return s.replace(old, new)


def emit_adm():
    s = open(ROOT + 'RationalStellaratorGCFamAdm.lean').read()
    s = rename_tokens(s)
    s = apply_renames(s)
    s = s.replace('RationalStellaratorGCFamOutH', 'RationalStellaratorGCMuOutH')
    s = s.replace('RationalStellaratorGCFamOutL', 'RationalStellaratorGCMuOutL')
    s = s.replace('RationalStellaratorGCFamMaj', 'RationalStellaratorGCMuMaj')
    s = s.replace('RationalStellaratorGCFamily.', 'RationalStellaratorGCMu.')
    s = s.replace('gcFlow (ρF c)', 'gcFlowMu (1 / 256) (lamF c)')
    s = s.replace('gcD (ρF c)', 'gcDM (1 / 256) (lamF c)')
    s = s.replace('gcNR (ρF c)', 'gcNRM (1 / 256) (lamF c)')
    s = s.replace('gcNZ (ρF c)', 'gcNZM (1 / 256) (lamF c)')
    s = s.replace('ne_zero_of_norm_one', 'ne_zero_of_norm_one_mu')
    # the parameter lemmas
    old_param = s[s.index('/-- **Sanity**: the parameter of the family lies in the cell. -/'):
                  s.index('/-! ## Constants -/')]
    new_param = '''/-- **Sanity**: the pitch parameter of the family lies in the cell `[0, @L1@]`. -/
theorem lamF_mem {c : ℂ} (hc : ‖c‖ = 1) : 0 ≤ lamF c ∧ lamF c ≤ @L1@ := by
  have h := Complex.abs_re_le_norm c
  rw [hc] at h
  have h' := abs_le.mp h
  constructor <;> rw [lamF] <;> linarith [h'.1, h'.2]

/-- `|lamF c| ≤ λ₁`. -/
theorem abs_lamF_le {c : ℂ} (hc : ‖c‖ = 1) : |lamF c| ≤ RationalStellaratorGCMu.lam1 := by
  obtain ⟨h1, h2⟩ := lamF_mem hc
  rw [abs_of_nonneg h1, RationalStellaratorGCMu.lam1]; linarith

'''.replace('@L1@', q2lean(LAM1))
    s = s.replace(old_param, new_param)
    # constants
    fb = C['fb']
    rep = [('def e0M : ℝ := 27 / 10 ^ 22', 'def e0M : ℝ := %s' % q2lean(C['e0'])),
           ('def auM : ℝ := 1947 / 10000 + μM', 'def auM : ℝ := %s + μM' % q2lean(C['au0'])),
           ('def azM : ℝ := 409 / 2500 + μM', 'def azM : ℝ := %s + μM' % q2lean(C['az0'])),
           ('def aRtM : ℝ := 1647 / 10000 + μM', 'def aRtM : ℝ := %s + μM' % q2lean(C['aRt0'])),
           ('def aztM : ℝ := 1629 / 10000 + μM', 'def aztM : ℝ := %s + μM' % q2lean(C['azt0'])),
           ('def aLRM : ℝ := 221 / 2000 + μM', 'def aLRM : ℝ := %s + μM' % q2lean(C['aLR0'])),
           ('def aLzM : ℝ := 131 / 1250 + μM', 'def aLzM : ℝ := %s + μM' % q2lean(C['aLz0'])),
           ('def sDM : ℝ := 16389 / 10000', 'def sDM : ℝ := %s' % q2lean(C['sD'])),
           ('def sWM : ℝ := 8871 / 50', 'def sWM : ℝ := %s' % q2lean(C['sW'])),
           ('def tTM : ℝ := 3799 / 100', 'def tTM : ℝ := %s' % q2lean(C['tT'])),
           ('def τM : ℝ := 411 / 1000', 'def τM : ℝ := %s' % q2lean(C['tau'])),
           ('  bD := 12791 / 10000', '  bD := %s' % q2lean(fb['Dt'])),
           ('  bDu := 22391 / 10000', '  bDu := %s' % q2lean(fb['Dtu'])),
           ('  bDz := 20441 / 100000', '  bDz := %s' % q2lean(fb['Dtz'])),
           ('  bnR := 10201 / 100000', '  bnR := %s' % q2lean(fb['nRt'])),
           ('  bnRu := 95121 / 100000', '  bnRu := %s' % q2lean(fb['nRtu'])),
           ('  bnRz := 74651 / 100000', '  bnRz := %s' % q2lean(fb['nRtz'])),
           ('  bnZ := 10601 / 100000', '  bnZ := %s' % q2lean(fb['nZt'])),
           ('  bnZu := 87241 / 100000', '  bnZu := %s' % q2lean(fb['nZtu'])),
           ('  bnZz := 82001 / 100000', '  bnZz := %s' % q2lean(fb['nZtz'])),
           ('  cKb := 6170', '  cKb := %s' % q2lean(C['cKb'])),
           ('  cLb := 21400', '  cLb := %s' % q2lean(C['cLb'])),
           ('theorem cM_au : cM.au = 1947 / 10000 + 1 / 10 ^ 11 := rfl',
            'theorem cM_au : cM.au = %s + 1 / 10 ^ 11 := rfl' % q2lean(C['au0']))]
    for a, b in rep:
        s = literal(s, a, b)
    # torus bounds
    for old, new in [('1947 / 10000', q2lean(C['au0'])), ('409 / 2500', q2lean(C['az0'])),
                     ('1647 / 10000', q2lean(C['aRt0'])), ('1629 / 10000', q2lean(C['azt0'])),
                     ('221 / 2000', q2lean(C['aLR0'])), ('131 / 1250', q2lean(C['aLz0']))]:
        s = s.replace(old, new)
    return s


def remap_indices(s):
    Lmap = {116: 'DtF', 118: 'nRtF', 120: 'nZtF', 122: 'DtuF', 124: 'DtzF', 126: 'nRtuF', 128: 'nRtzF',
            130: 'nZtuF', 132: 'nZtzF', 135: 'FF', 136: 'qiF', 137: 'YF', 138: 'Uo', 139: 'Zo', 140: 'Ao',
            141: 'Bo'}
    for n, nm in Lmap.items():
        assert fidxL[nm] == n, (nm, n, fidxL[nm])
    s = re.sub(r'\b(116|118|120|122|124|126|128|130|132|135|136|137|138|139|140|141)\b',
               lambda m: str(idxL[Lmap[int(m.group(1))]]), s)
    Hmap = {73: 'DtF', 75: 'nRtF', 77: 'nZtF'}
    for n, nm in Hmap.items():
        assert fidxH[nm] == n
        s = re.sub(r'(XHM c |\be)%d\b' % n, lambda m: m.group(1) + str(idxH[nm]), s)
    s = s.replace('(hi : i < 78)', '(hi : i < %d)' % H['nvar'])
    return s


def H_norm_rq(name):
    r = [r for r in H['nodes'] if r.get('var') is None and r['meta']['name'] == name][0]
    return bup(Fr(r['rad']), 4)


def L_norm_rq(name):
    r = [r for r in L['nodes'] if r.get('var') is None and r['meta']['name'] == name][0]
    return bup(Fr(r['rad']), 4)


def qlean_q(q):
    """a rational as `(a / b : ℚ)` in the style of the emitter (`qlean`)."""
    from lam_emit_lean import qlean
    return qlean(q)


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


def emit_adm_full():
    s = emit_adm()
    s = remap_indices(s)
    # distances to the low-resolution family (norms dU..dB of the high-resolution chain)
    for fam_lit, nm in [('((1163 / 10 ^ 11 : ℚ) : ℝ)', 'dU'), ('((229 / 20000000000 : ℚ) : ℝ)', 'dZ'),
                        ('((1161 / 10 ^ 11 : ℚ) : ℝ)', 'dA'), ('((1159 / 10 ^ 11 : ℚ) : ℝ)', 'dB')]:
        s = literal(s, fam_lit, '(%s : ℝ)' % qlean(H_norm_rq(nm)))
    for fam_lit, nm in [('(1 / 10 ^ 11 + 1163 / 10 ^ 11 : ℚ)', 'dU'), ('(1 / 10 ^ 11 + 229 / 20000000000 : ℚ)', 'dZ'),
                        ('(1 / 10 ^ 11 + 1161 / 10 ^ 11 : ℚ)', 'dA'), ('(1 / 10 ^ 11 + 1159 / 10 ^ 11 : ℚ)', 'dB')]:
        s = literal(s, fam_lit, '(1 / 10 ^ 11 + %s)' % qlean(H_norm_rq(nm)))
    # deviations of D and W0
    RDd = L_norm_rq('DdevF')
    RWd = L_norm_rq('WdevF')
    RX = bup(Fr([r for r in L['nodes'] if r.get('var') is None and r['meta']['name'] == 'XF'][0]['rad']), 4)
    assert RDd.denominator == 1 and RWd.denominator == 1
    s = literal(s, '(752400000000000 / 2 ^ 51)', '(%d / 2 ^ 51)' % RDd.numerator)
    s = literal(s, '(2149000000000000 / 2 ^ 59)', '(%d / 2 ^ 59)' % RWd.numerator)
    s = s.replace('(1337 / 10 ^ 8 : ℚ)', qlean(RX)).replace('1337 / 10 ^ 8', qlean(RX)[1:-5])
    # the torsion average
    vY = idxL['YF']
    fY = L['fam'][vY]
    N_, M_ = L['N'], L['M']
    cents = [decode_slice(sd, N_, M_, fY['s'])[N_][M_] for sd in fY['slices']]
    Y0 = cents[0]
    Y1 = sum(abs(x) for x in cents[1:])
    s = s.replace('509165477863147786', str(Y0)).replace('365841897391020', str(Y1))
    YB = Fr(L['B'][vY]) + Fr(L['E'][vY])
    YBq = bup(YB, 6)
    ELq = bup(Fr(L['E'][vY]), 3)
    assert YBq / (1 - RX) <= C['tT'], (float(YBq / (1 - RX)), float(C['tT']))
    s = literal(s, '379886 / 10000', q2lean(YBq))
    s = literal(s, '286 / 10 ^ 4', q2lean(ELq))
    s = s.replace('(3799 / 100)', '(%s)' % q2lean(C['tT'])).replace('3799 / 100', q2lean(C['tT']))
    # the family field bounds of muAdm
    fb = C['fb']
    for old, key in [('12791 / 10000', 'Dt'), ('22391 / 10000', 'Dtu'), ('20441 / 100000', 'Dtz'),
                     ('10201 / 100000', 'nRt'), ('95121 / 100000', 'nRtu'), ('74651 / 100000', 'nRtz'),
                     ('10601 / 100000', 'nZt'), ('87241 / 100000', 'nZtu'), ('82001 / 100000', 'nZtz')]:
        s = s.replace(old, q2lean(fb[key]))
    # the `μ > 0` flow form and its validity
    s = re.sub(r'\bgcFlow\b', 'gcFlowMu', s)
    s = s.replace('(gcFlow_valid _ avM (RationalStellaratorGCMu.gc_maj_E_lt avM_le.1 avM_le.2)).1',
                  '(RationalStellaratorGCMu.mu_valid_cell avM_le.1 avM_le.2 (abs_lamF_le hc)).1')
    return wrap_long(s)


def wrap_long(s, width=100):
    """Break lines longer than `width` at the last `, ` / ` ` before the limit (continuation
    indented by 4 more spaces)."""
    out = []
    for line in s.split('\n'):
        while len(line) > width:
            ind = len(line) - len(line.lstrip(' '))
            k = line.rfind(', ', 0, width - 1)
            if k > ind + 10:
                head, rest = line[:k + 1], line[k + 2:]
            else:
                k = line.rfind(' ', ind + 10, width)
                if k < 0:
                    break
                head, rest = line[:k], line[k + 1:]
            out.append(head)
            line = ' ' * (ind + 4) + ('-- ' if head.lstrip().startswith('--') else '') + rest
        out.append(line)
    return '\n'.join(out)


EXACT = r'''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuAdm

/-!
# Exact invariant tori of the `μ > 0` passing guiding-centre fields of a whole pitch-angle cell

The hypotheses `KamH` of the KAM theorem for fields with inverse-square-root nodes
(`Design/KamFlowIterationS`) for the `μ > 0` passing guiding-centre fields `gcFlowMu (1/256) λ` of
the rational stellarator (`ρ₀ = 1/256`: 3.5 MeV alphas at `B₀R₀ ≈ 69 T·m`), **for every pitch
parameter `λ = μB₀/E ∈ [0, @L1@]`**, at the approximate torus `K(λ)` given by the family centre
`(xHM c 4, xHM c 5)` at the parameter `c = e^{iϑ}` with `cos ϑ = @D@ λ − 1` (a Chebyshev series of
degree `@HD@` in `λ`, certified for all `ϑ` at once by the family ball chains
`Design/RationalStellaratorGCMuChain{H,L}`), and the rotational transform `ι = (75 + √5)/562`;
the constants `cM` are uniform over the cell:

* the Diophantine constant `γ = 0.0687` of `ι/2`;
* the initial error `e₀ = @E0@` on the strip `r_A = 0.1257` (`muResR`);
* admissibility of every `μ = 10⁻¹¹`-close torus (`muAdm`);
* node validity and the Taylor constant `C₂ ≤ @C2@`, uniform in `|λ| ≤ @L1@`
  (`Design/RationalStellaratorGCMuMaj`);
* the step constants `c_K ≤ @CK@`, `c_L ≤ @CL@`, and **the smallness condition**
  `32 κ e₀/δ₀⁴ ≈ @SM@ ≤ 1`.

**Main result** (`mu_family_torus`): for every `λ ∈ [0, @L1@]` there is a real analytic torus
`(u, z)` with `D̃ 𝓛K = ñ` exactly for the flow form of `gcFlowMu (1/256) λ`, `μ`-close to the
family torus `K(λ)` (`uFamM λ`, `zFamM λ`) on the strip `r_A/7`.

**Sanity.** `cOfM_norm`: the parameter `cOfM λ` lies on the unit circle.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGC

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton WEll1Z2 Complex
open PlasmaLean.Certificates.KronBallCheb

/-- Unfolding set for the step constants of `cM`. -/
macro "cM_norm" : tactic =>
  `(tactic| (simp only [SC.cK, SC.k1, SC.k2, SC.kc, SC.k20, SC.g, SC.kη1, SC.kη2, SC.kh, SC.kE,
    SC.tTot, SC.τ', SC.kTc, SC.eM, SC.mA, SC.mV, SC.cL, SC.kA, SC.XRb, SC.XZb, SC.kRem, SC.kS,
    SC.kap, cM, e0M, δ0G, KamTorusA.rA, auM, azM, aRtM, aztM, aLRM, aLzM, acG, μM, sDM, sRM, sWM,
    tTM, τM, RationalStellaratorGCMu.C2Q, max_def]; norm_num))

/-- `τ' > 0`. -/
theorem cM_τ' : 0 < cM.τ' := by cM_norm

/-- `c_K ≤ @CK@`. -/
theorem cM_cK : cM.cK ≤ @CK@ := by cM_norm

/-- `c_L ≤ @CL@`. -/
theorem cM_cL : cM.cL ≤ @CL@ := by cM_norm

/-- `c_K ≥ 0`. -/
theorem cM_cK_nonneg : 0 ≤ cM.cK := by cM_norm

/-- `c_L ≥ 0`. -/
theorem cM_cL_nonneg : 0 ≤ cM.cL := by cM_norm

/-- **The smallness condition** `32 κ e₀/δ₀⁴ ≤ 1` (actual value `≈ @SM@`). -/
theorem cM_small : 32 * cM.kap * e0M / cM.δ0 ^ 4 ≤ 1 := by cM_norm

/-- `κ > 0`. -/
theorem cM_kap_pos : 0 < cM.kap := by cM_norm

/-- Displacement budget (torus). -/
theorem cM_μK : 2 * cM.cK * e0M / cM.δ0 ^ 2 ≤ μM := by cM_norm

/-- Displacement budget (`θ`-derivatives). -/
theorem cM_μt : 2 * (cM.cK / cM.E1) * e0M / cM.δ0 ^ 3 ≤ μM := by cM_norm

/-- Displacement budget (transport). -/
theorem cM_μL : 2 * cM.cL * e0M / cM.δ0 ^ 2 ≤ μM := by cM_norm

/-- The perturbation profile is the rational profile `mvQ`. -/
theorem cM_mvec : cM.mvec = fun i => (RationalStellaratorGCMu.mvQ i : ℝ) := by
  funext i; fin_cases i <;> simp [SC.mvec, cM, RationalStellaratorGCMu.mvQ]

/-- The Taylor segment bounds lie below the validity bounds `aTQ`. -/
theorem cM_avecT : (∀ i, 0 ≤ (cM.avec + cM.Tq • cM.mvec) i) ∧
    ∀ i, (cM.avec + cM.Tq • cM.mvec) i ≤ (RationalStellaratorGCMu.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, SC.mvec, SC.Tq, cM, RationalStellaratorGCMu.aTQ, auM, azM, aLRM, aLzM,
      acG, μM, e0M, δ0G, KamTorusA.rA] <;> norm_num

/-- The limit segment bounds lie below the validity bounds `aTQ`. -/
theorem cM_avecμ : (∀ i, 0 ≤ (cM.avec + (2 * μM) • mOne) i) ∧
    ∀ i, (cM.avec + (2 * μM) • mOne) i ≤ (RationalStellaratorGCMu.aTQ i : ℝ) := by
  refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
    simp [SC.avec, mOne, cM, RationalStellaratorGCMu.aTQ, auM, azM, aLRM, aLzM, acG, μM] <;>
    norm_num

/-- The global conditions for the family torus at `λ` (`|λ| ≤ λ₁`). -/
theorem cM_global {lm : ℝ} (hlm : |lm| ≤ RationalStellaratorGCMu.lam1) :
    (gcFlowMu (1 / 256) lm).GlobalH cM KamTorusA.iota where
  dio := iota_dio
  γ_pos := by norm_num [cM]
  hτ' := cM_τ'
  hC2R := by
    have h := (RationalStellaratorGCMu.mu_C2_cell cM_avecT.1 cM_avecT.2 hlm).1
    rwa [← cM_mvec] at h
  hC2Z := by
    have h := (RationalStellaratorGCMu.mu_C2_cell cM_avecT.1 cM_avecT.2 hlm).2
    rwa [← cM_mvec] at h
  hvR := (RationalStellaratorGCMu.mu_valid_cell cM_avecT.1 cM_avecT.2 hlm).2.1
  hvZ := (RationalStellaratorGCMu.mu_valid_cell cM_avecT.1 cM_avecT.2 hlm).2.2
  hδ2 := by
    have := Real.exp_one_lt_d9
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simp only [cM, δ0G, KamTorusA.rA]
    norm_num at this ⊢
    nlinarith
  hac := by
    have := exp_rA_le'; push_cast at this; simp only [cM, acG]; linarith
  hE1 := ⟨by norm_num [cM], by
    have := Real.exp_one_gt_d9; simp only [cM]; norm_num at this ⊢; linarith⟩
  hcb := ⟨cM_cK, cM_cL⟩

/-- **All hypotheses of the KAM theorem hold for the family torus** at every parameter `|c| = 1`
(`λ = lamF c`). -/
theorem cM_kamH {c : ℂ} (hc : ‖c‖ = 1) :
    (gcFlowMu (1 / 256) (lamF c)).KamH cM KamTorusA.iota (xHM c 4) (xHM c 5) e0M μM where
  G := cM_global (abs_lamF_le hc)
  hδ0 := by norm_num [cM, δ0G, KamTorusA.rA]
  hρ6 := by norm_num [cM, δ0G, KamTorusA.rA]
  hθ := rfl
  he₀ := by norm_num [e0M]
  hκ := cM_kap_pos
  hsmall := cM_small
  hcK := cM_cK_nonneg
  hcL := cM_cL_nonneg
  hμK := cM_μK
  hμt := cM_μt
  hμL := cM_μL
  hadm := fun ρ u z hlo hhi hu hz hC => muAdm
    (lt_of_lt_of_le (by norm_num [cM, δ0G, KamTorusA.rA]) hlo) hhi hc hu hz hC
  ana_u₀ := ana_uM hc
  ana_z₀ := ana_zM hc
  real_u₀ := isReal_uM hc
  real_z₀ := isReal_zM hc
  e0R := muResR hc
  e0Z := muResZ hc
  hvR' := (RationalStellaratorGCMu.mu_valid_cell cM_avecμ.1 cM_avecμ.2 (abs_lamF_le hc)).2.1
  hvZ' := (RationalStellaratorGCMu.mu_valid_cell cM_avecμ.1 cM_avecμ.2 (abs_lamF_le hc)).2.2

/-- The limiting strip `ρ_∞ = r_A/7`. -/
theorem rInf_cM : rInf cM = KamTorusA.rA / 7 := by unfold rInf; simp only [cM, δ0G]; ring

/-! ## The parameter of `λ` -/

/-- The parameter value `c = e^{iϑ}` with `cos ϑ = @D@ λ − 1` (clamped to `[−1, 1]`). -/
def cOfM (lm : ℝ) : ℂ :=
  ⟨max (-1) (min 1 (@D@ * lm - 1)), Real.sqrt (1 - max (-1) (min 1 (@D@ * lm - 1)) ^ 2)⟩

/-- **Sanity**: the parameter lies on the unit circle. -/
theorem cOfM_norm (lm : ℝ) : ‖cOfM lm‖ = 1 := by
  set x := max (-1) (min 1 (@D@ * lm - 1)) with hx
  have h1 : -1 ≤ x := le_max_left _ _
  have h2 : x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
  have h3 : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [Complex.norm_def, Complex.normSq_mk, cOfM, ← hx]
  rw [Real.mul_self_sqrt h3, show x * x + (1 - x ^ 2) = 1 by ring, Real.sqrt_one]

/-- On the cell, `lamF (cOfM λ) = λ`. -/
theorem lamF_cOfM {lm : ℝ} (h : lm ∈ Set.Icc (0 : ℝ) (@L1@)) : lamF (cOfM lm) = lm := by
  obtain ⟨h1, h2⟩ := h
  have e : max (-1) (min 1 (@D@ * lm - 1)) = @D@ * lm - 1 := by
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  simp only [lamF, cOfM, e]
  ring

/-- **The family torus** at `λ` (the `R − 1` component). -/
def uFamM (lm : ℝ) : FA := xHM (cOfM lm) 4

/-- **The family torus** at `λ` (the `z` component). -/
def zFamM (lm : ℝ) : FA := xHM (cOfM lm) 5

/-- **Exact invariant tori of the `μ > 0` passing guiding-centre fields of the whole pitch-angle
cell** `λ = μB₀/E ∈ [0, @L1@]` (`ρ₀ = 1/256`). For every such `λ` there is a real analytic torus
`(u, z)` (strip `r_A/7 ≈ 0.018`) solving the flow-form invariance equation of the passing field
`B̃ = B + ∇×(ρ(x) b)`, `ρ(x) = ρ₀ √(1 − λ|B(x)|)`, of the rational stellarator exactly, with
rotational transform `ι = (75 + √5)/562`, and `10⁻¹¹`-close to the certified family torus
`K(λ) = (1 + uFamM λ, zFamM λ)` in `u, z, ∂_θu, ∂_θz, 𝓛u, 𝓛z` on that strip. -/
theorem mu_family_torus {lm : ℝ} (hlm : lm ∈ Set.Icc (0 : ℝ) (@L1@)) :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧
      (gcFlowMu (1 / 256) lm).resR KamTorusA.iota u z = 0 ∧
      (gcFlowMu (1 / 256) lm).resZ KamTorusA.iota u z = 0 ∧
      Close (KamTorusA.rA / 7) KamTorusA.iota u z (uFamM lm) (zFamM lm) μM := by
  have h := gcMu_kam_torus (cM_kamH (cOfM_norm lm))
  rw [rInf_cM, lamF_cOfM hlm] at h
  exact h

end PlasmaLean.Design.RationalStellaratorGC
'''


def emit_exact(HD):
    s = EXACT
    small = float(C['small'])
    rep = {'@L1@': q2lean(LAM1), '@D@': str(LAMDEN), '@HD@': str(HD), '@E0@': '%.2g' % float(C['e0']),
           '@C2@': '%.3g' % float(C['C2']), '@CK@': q2lean(C['cKb']), '@CL@': q2lean(C['cLb']),
           '@SM@': '%.3f' % small}
    for k, v in rep.items():
        s = s.replace(k, v)
    return s


if __name__ == '__main__':
    open(ROOT + 'RationalStellaratorGCMuAdm.lean', 'w').write(emit_adm_full())
    open(ROOT + 'RationalStellaratorGCMuExact.lean', 'w').write(emit_exact(H['D']))
    print('ok')


def emit_forever():
    s = open(ROOT + 'RationalStellaratorGCFamForever.lean').read()
    head_end = s.index('open scoped RealInnerProductSpace')
    body = s[head_end:]
    body = rename_tokens(body)
    body = apply_renames(body)
    body = remap_indices(body)
    extra = [('aResF_le', 'aResM_le'), ('aResF', 'aResM'), ('norm_xK_leF', 'norm_xK_leM'),
             ('gc_family_exact_data', 'mu_family_exact_data'), ('gc_family_flowTorus', 'mu_family_flowTorus'),
             ('gc_family_master', 'mu_family_master'), ('gc_family_field_confined_forever',
                                                        'mu_family_field_confined_forever'),
             ('famL_inputs', 'muL_inputs'), ('famL_old_u', 'muL_old_u'), ('famL_old_z', 'muL_old_z'),
             ('famL_old_a', 'muL_old_a'), ('famL_old_b', 'muL_old_b'), ('famOld_u', 'muOld_u'),
             ('famOld_z', 'muOld_z'), ('famOld_a', 'muOld_a'), ('famOld_b', 'muOld_b'),
             ('Bd_three', 'Bd_three_mu'), ('margin_le', 'margin_le_mu')]
    for a, b in extra:
        body = re.sub(r'(?<![A-Za-z0-9_\.])' + re.escape(a) + r'(?![A-Za-z0-9_\'])', b, body)
    body = body.replace('ne_zero_of_norm_one', 'ne_zero_of_norm_one_mu')
    body = body.replace('RationalStellaratorGCFamily.', 'RationalStellaratorGCMu.')
    # the stored rho = 1/256 low-resolution torus comparisons: the norm bounds
    for fam_lit, nm in [('(1839 / 10 ^ 6 : ℚ)', 'dUo'), ('(1337 / 10 ^ 6 : ℚ)', 'dZo'),
                        ('(329 / 250000 : ℚ)', 'dAo'), ('(1259 / 10 ^ 6 : ℚ)', 'dBo')]:
        body = literal(body, fam_lit, qlean(L_norm_rq(nm)))
    # cut everything from the exact data on: replaced by the mu-specific part
    cut = body.index('/-- **The exact guiding-centre torus of `ρ` in real form**')
    return s[:head_end], body[:cut]


if __name__ == '__main__' and 'forever' in sys.argv:
    h, b = emit_forever()
    open('/tmp/lamw/forever_part1.lean', 'w').write(b)
    print('ok')
