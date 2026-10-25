"""UNTRUSTED (pitch cell [LAM_LO, LAM_HI], see lc.py): emit the Lean certificate modules of the cell
(Data, Kv, Trees, Env, Rel, Check, Chain, Out; high and low resolution) by
scripts/gc_kam/lam_emit_lean.py `all`, into $LAM_WORK/emit with the original module names (install.py
renames them).  Patches: `lamF c = (KOFF + Re c)/LAMDEN`, `r = R0 + LAMDEN lamF c`; the congruences with
the rho = 1/256, mu = 0 pipeline (`rel_congr`) are those of the certified Design/RationalStellaratorGCMuRelL
(the lam-independent nodes are the same; every congruence is re-checked by the kernel).
Usage: python emit.py
"""
import os, sys, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lc

W = lc.WORK
EMIT = os.path.join(W, 'emit') + '/'
os.makedirs(EMIT, exist_ok=True)
os.environ['LAM_DEN'] = str(lc.LAMDEN)
os.environ['LAM_PKL_H'] = os.path.join(W, 'lam_cert_H.pkl')
os.environ['LAM_PKL_L'] = os.path.join(W, 'lam_cert_L.pkl')
os.environ.setdefault('LAM_GH', '64')
os.environ.setdefault('LAM_GL', '8')
os.environ.setdefault('LAM_HCAP', '1')

# congruences of the certified low-resolution relations: variable -> name of the mu = 0 relation
rel = open(lc.DESIGN + 'RationalStellaratorGCMuRelL.lean').read()
OLD = {}
for blk in rel.split('\ntheorem ')[1:]:
    m = re.search(r'rel_congr \(XLM_congr c u z\) \(by decide \+kernel\) \(XLM_old c u z \(j := (\d+)\) rfl\) '
                  r'\(relL_(\S+) u z\)', blk)
    if m:
        OLD[int(m.group(1))] = m.group(2)
assert len(OLD) > 50, len(OLD)

D, K, R0 = lc.LAMDEN, lc.KOFF, lc.R0
LOs, HIs = lc.q2lean(lc.LO), lc.q2lean(lc.HI)
reps = [
    ("OUT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'", "OUT = LAMCELL_EMIT"),
    ("`r = 64 + cos ϑ = 63 + 8λ`", "`r = 64 + cos ϑ = %d + %dλ`" % (R0, D)),
    ("(((63 + %d * lamF c", "(((%d + %%d * lamF c" % R0),
    ("`λ = lamF c = (1 + Re c)/8 ∈ [0, 1/4]`", "`λ = lamF c = (%d + Re c)/%d ∈ [%s, %s]`" % (K, D, LOs, HIs)),
    ("parameter `r = 63 + 8λ`", "parameter `r = %d + %dλ`" % (R0, D)),
    ("/-- **The pitch parameter of the family** at `w = c`: `λ = (1 + Re c)/@D@` (for `c = e^{iϑ}`:\n"
     "`λ = (1 + cos ϑ)/@D@`, in `[0, 2/@D@]`). -/\n"
     "def lamF (c : ℂ) : ℝ := (1 + c.re) / @D@\n",
     "/-- **The pitch parameter of the family** at `w = c`: `λ = (%d + Re c)/@D@` (for `c = e^{iϑ}`:\n"
     "`λ = (%d + cos ϑ)/@D@`, in `[%s, %s]`). -/\n"
     "def lamF (c : ℂ) : ℝ := (%d + c.re) / @D@\n" % (K, K, LOs, HIs, K)),
    ("`63 + @D@ lamF c = 64 + (c + c⁻¹)/2`", "`%d + @D@ lamF c = 64 + (c + c⁻¹)/2`" % R0),
    ("(((63 + @D@ * lamF c : ℝ)) : ℂ) = 64 + (c + c⁻¹) / 2", "(((%d + @D@ * lamF c : ℝ)) : ℂ) = 64 + (c + c⁻¹) / 2" % R0),
    ("OLDL = pickle.load(open('/tmp/gcw/gc_cert.pkl', 'rb'))['L']\n"
     "OLDL_NODES = {r['n']: r for r in OLDL['nodes'] if r.get('var') is not None}\n",
     "OLDL_NODES = LAMCELL_OLD\n"),
    ("if o is not None and o['tree'] == r['tree'] and o['c'] == c and n not in spl:",
     "if o is not None and n not in spl:"),
    ("OLDL['names'][n].replace(\"'\", \"p\")", "OLDL_NODES[n]"),
]
lc.run_patched('lam_emit_lean.py', reps, ['all'], extra_globals=dict(LAMCELL_EMIT=EMIT, LAMCELL_OLD=OLD))
