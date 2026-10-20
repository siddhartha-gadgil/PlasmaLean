import sys
data=dict(l.split(' ',1) for l in open(sys.argv[1]).read().strip().split('\n'))
P=dict(ns=sys.argv[2], chilo=sys.argv[3], chihi=sys.argv[4], aux=sys.argv[5], auxdoc=sys.argv[6], Delta=sys.argv[7], Tmax=sys.argv[8])
def wrap(s, ind=2, width=98):
    # wrap a long bracketed list on ", " boundaries
    out=[]; line=" "*ind
    toks=s.split(", ")
    for i,t in enumerate(toks):
        piece=t+(", " if i<len(toks)-1 else "")
        if len(line)+len(piece.rstrip())>width:
            out.append(line.rstrip()); line=" "*(ind+1)+piece
        else: line+=piece
    out.append(line.rstrip())
    return "\n".join(out)
D=dict(FS=wrap(data['FS'].strip()),FU=wrap(data['FU'].strip()),SUB=wrap(data['SUB'].strip()),SUP=wrap(data['SUP'].strip()),PRES=wrap(data['PRES'].strip()))
tmpl=open('/tmp/k4/design_template.lean').read()
for k,v in list(P.items())+list(D.items()):
    tmpl=tmpl.replace('@@'+k+'@@',v)
sys.stdout.write(tmpl)
