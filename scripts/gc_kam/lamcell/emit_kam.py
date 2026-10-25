"""UNTRUSTED (pitch cell [LAM_LO, LAM_HI], see lc.py): emit the admissibility and KAM modules
RationalStellaratorGCMu{Adm,Exact}.lean of the cell into $LAM_WORK/emit (original names; install.py
renames) by scripts/gc_kam/lam_emit_kam.py.  Patches: the cell [LAM_LO, LAM_HI] in `lamF_mem`, `cOfM`
(`cos theta' = LAMDEN lam - KOFF`), `lamF_cOfM`, `mu_family_torus`; lam1 = LAM_HI; the variable
indices of the rho-family templates (RationalStellaratorGCFam{Adm,Exact}) are mapped by name only.

Fixes of lam_emit_kam.py (October 2026, failure of the cell [1/8, 3/16]):
  * SIMULTANEOUS substitution of the template literals.  lam_emit_kam.py replaced the torus bounds
    of the template one after the other (`409 / 2500` -> az0, then `1629 / 10000` -> azt0, ...), so a
    new value equal to a LATER template literal was replaced again: for [1/8, 3/16] az0 = 1629/10000
    (= the template's azt literal) became azt0 = 1623/10000, and Adm claimed the false bound
    `BHM 5 + EHM 5 ≤ 1623/10000` (BHM 5 = 1629/10000).  Both literal loops (torus bounds, field
    bounds) are now one regex pass each (`subst`, digit boundaries); the constant definitions
    (`def azM : ℝ := ...`, which were also rewritten again by the torus loop) are in the same pass
    as the torus bounds.
  * every bound fact of Adm, the torus constants and the Maj bounds `aTQ` are validated with exact
    `Fraction` arithmetic against the rational lists of the emitted Env modules (validate.py) BEFORE
    the files are written;
  * no `decide +kernel` (policy of 25 October 2026): the small bound facts and side conditions are
    proved by `decide_cbv`.
Usage: python emit_kam.py      (after maj_g.py and emit.py: needs $LAM_WORK/emit/*{Maj,EnvH,EnvL}.lean)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc
import re
import validate


def subst(s, pairs):
    """replace all template literals `old` by `new` in ONE pass (a new value is never replaced again);
    literals match only between non-digits."""
    d = dict(pairs)
    assert len(d) == len(pairs), 'duplicate template literal'
    pat = re.compile(r'(?<![0-9])(?:%s)(?![0-9])' % '|'.join(re.escape(o) for o in sorted(d, key=len, reverse=True)))
    for o in d:
        assert re.search(r'(?<![0-9])%s(?![0-9])' % re.escape(o), s), ('template literal not found', o)
    return pat.sub(lambda m: d[m.group(0)], s)


def write_checked(name, txt, C, idxH):
    """validate an emitted module (exact arithmetic against the emitted Env lists), then write it."""
    txt = validate.to_decide_cbv(txt, name)
    if name.endswith('Adm.lean'):
        rd = lambda m: open(EMIT + 'RationalStellaratorGCMu%s.lean' % m).read()
        for k, v in validate.H_IDX.items():
            assert idxH[k] == v, ('high-resolution index moved', k, idxH[k], v)
        n, K = validate.validate(rd('EnvH'), rd('EnvL'), txt, rd('Maj'), C)
        assert C['small'] <= 1, ('smallness condition fails', float(C['small']))
        print('%s: %d bound facts and the constants validated (exact)' % (name, n))
    open(EMIT + name, 'w').write(txt)


W = lc.WORK
EMIT = os.path.join(W, 'emit') + '/'
os.makedirs(EMIT, exist_ok=True)
os.environ['LAM_DEN'] = str(lc.LAMDEN)
os.environ['LAM_PKL_H'] = os.path.join(W, 'lam_cert_H.pkl')
os.environ['LAM_PKL_L'] = os.path.join(W, 'lam_cert_L.pkl')
LOs = lc.q2lean(lc.LO)
reps = [
    ("ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'", "ROOT = LAMCELL_DESIGN"),
    ("C = pickle.load(open('/tmp/lamc/lam_const.pkl', 'rb'))", "C = pickle.load(open(LAMCELL_WORK + '/lam_const.pkl', 'rb'))"),
    ("FH = pickle.load(open('/tmp/famw/fam_cert_H.pkl', 'rb'))['H']", "FH = {'names': {}}"),
    ("FL = pickle.load(open('/tmp/famw/fam_cert_L.pkl', 'rb'))['L']", "FL = {'names': {}}"),
    ("        assert fidxL[nm] == n, (nm, n, fidxL[nm])\n", "        pass\n"),
    ("        assert fidxH[nm] == n\n", "        pass\n"),
    ("LAM1 = Fr(2, LAMDEN)", "LAM1 = LAMCELL_HI"),
    ("/-- **Sanity**: the pitch parameter of the family lies in the cell `[0, @L1@]`. -/\n"
     "theorem lamF_mem {c : ℂ} (hc : ‖c‖ = 1) : 0 ≤ lamF c ∧ lamF c ≤ @L1@ := by",
     "/-- **Sanity**: the pitch parameter of the family lies in the cell `[%s, @L1@]`. -/\n"
     "theorem lamF_mem {c : ℂ} (hc : ‖c‖ = 1) : %s ≤ lamF c ∧ lamF c ≤ @L1@ := by" % (LOs, LOs)),
    ("  rw [abs_of_nonneg h1, RationalStellaratorGCMu.lam1]; linarith",
     "  rw [abs_of_nonneg (le_trans (by norm_num) h1), RationalStellaratorGCMu.lam1]; linarith"),
    ("Set.Icc (0 : ℝ) (@L1@)", "Set.Icc (@L0@ : ℝ) (@L1@)"),
    ("∈ [0, @L1@]", "∈ [@L0@, @L1@]"),
    ("@D@ * lm - 1", "@D@ * lm - @K@"),
    ("`cos ϑ = @D@ λ − 1`", "`cos ϑ = @D@ λ − @K@`"),
    ("    rep = {'@L1@': q2lean(LAM1),", "    rep = {'@L0@': LAMCELL_LO, '@K@': LAMCELL_K, '@L1@': q2lean(LAM1),"),
    # simultaneous substitution of the literal loops (see the docstring)
    # the constant definitions and the torus bounds in ONE pass (the definitions are the longer
    # literals, so they win at their positions; their new values are not rescanned)
    ("    for a, b in rep:\n        s = literal(s, a, b)\n    # torus bounds\n"
     "    for old, new in [('1947 / 10000', q2lean(C['au0']))",
     "    s = LAMCELL_SUBST(s, rep + [('1947 / 10000', q2lean(C['au0']))"),
    ("('131 / 1250', q2lean(C['aLz0']))]:\n        s = s.replace(old, new)\n",
     "('131 / 1250', q2lean(C['aLz0']))])\n"),
    ("    for old, key in [('12791 / 10000', 'Dt')", "    s = LAMCELL_SUBST(s, [(old, q2lean(fb[key])) for old, key in [('12791 / 10000', 'Dt')"),
    ("('82001 / 100000', 'nZtz')]:\n        s = s.replace(old, q2lean(fb[key]))\n",
     "('82001 / 100000', 'nZtz')]])\n"),
    # validated writes
    ("open(ROOT + 'RationalStellaratorGCMuAdm.lean', 'w').write(emit_adm_full())",
     "LAMCELL_WRITE('RationalStellaratorGCMuAdm.lean', emit_adm_full(), C, idxH)"),
    ("open(ROOT + 'RationalStellaratorGCMuExact.lean', 'w').write(emit_exact(H['D']))",
     "LAMCELL_WRITE('RationalStellaratorGCMuExact.lean', emit_exact(H['D']), C, idxH)"),
]
lc.run_patched('lam_emit_kam.py', reps, [],
               extra_globals=dict(LAMCELL_DESIGN=lc.DESIGN, LAMCELL_WORK=W, LAMCELL_HI=lc.HI, LAMCELL_LO=LOs,
                                  LAMCELL_K=str(lc.KOFF), LAMCELL_EMIT=EMIT,
                                  LAMCELL_SUBST=subst, LAMCELL_WRITE=write_checked))
