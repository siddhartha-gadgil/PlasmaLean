"""UNTRUSTED (pitch cell [LAM_LO, LAM_HI], see lc.py): the KAM constants of the cell and the Lean
majorant module, by scripts/gc_kam/lam_maj.py with the largest pitch parameter `lam1 = LAM_HI`
(the majorants are uniform over |lam| <= lam1).  Output: $LAM_WORK/lam_const.pkl and
$LAM_WORK/emit/RationalStellaratorGCMuMaj.lean (original names; install.py renames).
Usage: python maj.py
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
lc.run_patched('lam_maj.py', [
    ("ROOT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'", "ROOT = LAMCELL_DESIGN"),
    ("LAM1 = Fr(2, LAMDEN)", "LAM1 = LAMCELL_HI"),
    ("pickle.dump(CONST, open('/tmp/lamc/lam_const.pkl', 'wb'))",
     "pickle.dump(CONST, open(LAMCELL_WORK + '/lam_const.pkl', 'wb'))"),
    ("open(ROOT + 'RationalStellaratorGCMuMaj.lean', 'w')", "open(LAMCELL_EMIT + 'RationalStellaratorGCMuMaj.lean', 'w')"),
], [], extra_globals=dict(LAMCELL_DESIGN=lc.DESIGN, LAMCELL_HI=lc.HI, LAMCELL_WORK=W, LAMCELL_EMIT=EMIT))
