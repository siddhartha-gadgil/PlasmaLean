"""UNTRUSTED (pitch cell [LAM_LO, LAM_HI], see lc.py): emit the admissibility and KAM modules
RationalStellaratorGCMu{Adm,Exact}.lean of the cell into $LAM_WORK/emit (original names; install.py
renames) by scripts/gc_kam/lam_emit_kam.py.  Patches: the cell [LAM_LO, LAM_HI] in `lamF_mem`, `cOfM`
(`cos theta' = LAMDEN lam - KOFF`), `lamF_cOfM`, `mu_family_torus`; lam1 = LAM_HI; the variable
indices of the rho-family templates (RationalStellaratorGCFam{Adm,Exact}) are mapped by name only.
Usage: python emit_kam.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc

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
    ("open(ROOT + 'RationalStellaratorGCMuAdm.lean', 'w')", "open(LAMCELL_EMIT + 'RationalStellaratorGCMuAdm.lean', 'w')"),
    ("open(ROOT + 'RationalStellaratorGCMuExact.lean', 'w')", "open(LAMCELL_EMIT + 'RationalStellaratorGCMuExact.lean', 'w')"),
]
lc.run_patched('lam_emit_kam.py', reps, [],
               extra_globals=dict(LAMCELL_DESIGN=lc.DESIGN, LAMCELL_WORK=W, LAMCELL_HI=lc.HI, LAMCELL_LO=LOs,
                                  LAMCELL_K=str(lc.KOFF), LAMCELL_EMIT=EMIT))
