import sys, json
def wrap(s, ind=2, width=98):
    out=[]; line=" "*ind
    toks=s.split(", ")
    for i,t in enumerate(toks):
        piece=t+(", " if i<len(toks)-1 else "")
        if len(line)+len(piece.rstrip())>width:
            out.append(line.rstrip()); line=" "*(ind+1)+piece
        else: line+=piece
    out.append(line.rstrip())
    return "\n".join(out)
def fill(t, P):
    for k,v in P.items(): t=t.replace('@@'+k+'@@',v)
    assert '@@' not in t, [l for l in t.split('\n') if '@@' in l][:5]
    return t
cfg=json.load(open(sys.argv[1]))
data=dict(l.split(' ',1) for l in open(cfg['data']).read().strip().split('\n'))
P=dict(cfg['params'])
for k in ('FS','FU','SUB','SUP','PRES'): P[k]=wrap(data[k].strip())
out=""
for t in cfg['templates']:
    out+=fill(open(t).read(),P)
sys.stdout.write(out)
