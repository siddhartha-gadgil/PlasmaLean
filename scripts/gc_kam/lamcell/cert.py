"""UNTRUSTED driver (pitch cell [LAM_LO, LAM_HI], see lc.py): the two family ball pipelines of
scripts/gc_kam/lam_cert.py for the cell.  Patches: the pitch node `lamv = (r - R0)/LAMDEN`; the stored
rho = 1/256, mu = 0 low-resolution torus (profile comparison) is read from the certified Lean data
Design/RationalStellaratorGCMuDataL (`sdLM_Uo`, `sdLM_Zo`); the low-resolution input balls use the
distances of this cell's high-resolution run; output $LAM_WORK/lam_cert_{H,L}.pkl.
Usage: python cert.py H|L   (H first: L needs its distances)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc

which = sys.argv[1]
os.environ['LAM_DEN'] = str(lc.LAMDEN)
os.environ['LAM_CHEB'] = os.path.join(lc.WORK, 'cheb.npz')
os.environ.setdefault('LAM_H', '36,27,107,12')
os.environ.setdefault('LAM_LD', '5')
os.environ.setdefault('LAM_LDC', '5')
W = lc.WORK
reps = [
    ("sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')", "pass"),
    ("lam = B.node('lamv', (r - 63 * st) / LAMDEN, rel='lam')",
     "lam = B.node('lamv', (r - LAMCELL_R0 * st) / LAMDEN, rel='lam')"),
    ("    OLD = pickle.load(open('/tmp/gcw/gc_cert.pkl', 'rb'))['L']\n"
     "    assert (OLD['N'], OLD['M'], OLD['S']) == (LN, LM, LS)\n"
     "    ou = [encode_slice(OLD['G'][4], LN, LM, 1)[0]]\n"
     "    oz = [encode_slice(OLD['G'][5], LN, LM, -1)[0]]\n",
     "    _LEANL = LAMCELL_SLICES(['RationalStellaratorGCMuDataL'])\n"
     "    ou, oz = _LEANL['sdLM_Uo'], _LEANL['sdLM_Zo']\n"),
    ("        DIST = [Fr(117, 10 ** 10), Fr(23, 2000000000), Fr(117, 10 ** 10), Fr(29, 2500000000)]\n",
     "        DIST = pickle.load(open(LAMCELL_WORK + '/lam_cert_H.pkl', 'rb'))['DIST']\n"),
    ("os.makedirs('/tmp/lamc', exist_ok=True)", "os.makedirs(LAMCELL_WORK, exist_ok=True)"),
    ("open('/tmp/lamc/lam_cert_%s.pkl' % WHICH, 'wb')", "open(LAMCELL_WORK + '/lam_cert_%s.pkl' % WHICH, 'wb')"),
]
if which == 'L':
    # the high-resolution pickle holds `DIST`
    assert os.path.exists(os.path.join(W, 'lam_cert_H.pkl')), 'run cert.py H first'
lc.run_patched('lam_cert.py', reps, [which],
               extra_globals=dict(LAMCELL_R0=lc.R0, LAMCELL_WORK=W, LAMCELL_SLICES=lc.read_slices))
