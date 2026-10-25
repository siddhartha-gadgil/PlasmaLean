"""UNTRUSTED (energy window): install the Lean files of node j emitted by ew_emit_lean.py (original
names, in EW_TMP) under PlasmaLean/Design with the module names RationalStellaratorGCEw<j>*H* and the
identifier suffix `HM` -> `HE<j>`; the certified low-resolution modules (`...MuDataL`, `...MuRelL`, ...)
are referenced unchanged.  Usage: python ew_rename.py EW_TMP j RHO_LATEX"""
import sys, os, re
src, j, rho = sys.argv[1], sys.argv[2], sys.argv[3]
DST = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'PlasmaLean', 'Design') + '/'
KINDS = ['Data', 'Kv', 'Trees', 'Env', 'Rel', 'Check', 'Chain', 'Out']
for f in sorted(os.listdir(src)):
    if not f.endswith('.lean'):
        continue
    s = open(os.path.join(src, f)).read()
    s = re.sub(r'RationalStellaratorGCMu(%s)H' % '|'.join(KINDS), r'RationalStellaratorGCEw%s\1H' % j, s)
    s = s.replace('HM', 'HE%s' % j)
    s = s.replace('scripts/gc_kam/lam_emit_lean.py', 'scripts/gc_kam/ew_emit_lean.py')
    # the module docstring: name the node
    s = s.replace('-/\n\n@[expose]', '\nEnergy-window node %s: gyro-length `ρ_%s = %s`, its own family torus `K_%s(λ)`; the\n'
                  'fields at `ρ_%s` are the nodes `DtJ`, `nRtJ`, `nZtJ`.\n-/\n\n@[expose]' % (j, j, rho, j, j), 1)
    g = re.sub(r'RationalStellaratorGCMu(%s)H' % '|'.join(KINDS), r'RationalStellaratorGCEw%s\1H' % j, f)
    open(DST + g, 'w').write(s)
print('installed')
