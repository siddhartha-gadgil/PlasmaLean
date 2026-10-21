"""UNTRUSTED helper: after emitting RationalStellaratorGCTorusMaj.lean (gc_maj.py), compile it once and
drop / split the trailing `norm_num` of each mirror lemma according to the linter (no-op or single goal)."""
import subprocess, re, sys
f = sys.argv[1]
out = subprocess.run(['lake', 'env', 'lean', f], capture_output=True, text=True, cwd='/Users/gadgil/code/PlasmaLean').stdout
never = set(); seq = set()
for l in out.splitlines():
    m = re.match(r'.*?:(\d+):(\d+): warning: (.*)', l)
    if not m: continue
    ln = int(m.group(1)); msg = m.group(3)
    if 'never executed' in msg: never.add(ln)
    if 'would suffice' in msg: seq.add(ln)
lines = open(f).read().split('\n')
for ln in sorted(never | seq, reverse=True):
    s = lines[ln - 1]
    if ln in never:
        lines[ln - 1] = s.replace(' <;> norm_num', '')
    else:
        i = s.index(' <;> norm_num')
        lines[ln - 1] = s[:i]
        lines.insert(ln, '  norm_num')
open(f, 'w').write('\n'.join(lines))
print(len(never), len(seq))
