from fractions import Fraction as Fr
from bhfine import fine
W=[l.split() for l in open('windows.txt')]
coarse=[(Fr(int(x[0])),Fr(int(x[1])),Fr(x[2]),Fr(x[3]),x[2],x[3]) for x in W]
fw=[(Fr(a,4),Fr(b,4),Fr(str(l)),Fr(str(h)),a,b,l,h) for a,b,l,h in fine()]
def sci(d):  # Decimal like 1.352E-23 -> "1.352e-23"
    return str(d).replace('E','e')
lines=[]
for (lo,hi,L,H,a,b,l,h) in fw:
    lines.append("  ⟨%d/4, %d/4, %s, %s⟩"%(a,b,sci(l),sci(h)))
open('fine_lean.txt','w').write(",\n".join(lines))
allw=[(lo,hi,L,H) for (lo,hi,L,H,*_) in coarse]+[(lo,hi,L,H) for (lo,hi,L,H,*_) in fw]
# nodes at T=1+k/4, k=0..236
nodesF=[]; nodesS=[]
for k in range(237):
    T=1+Fr(k,4)
    cands=[(L,s) for (lo,hi,L,H,s,_) in coarse if lo<=T]+[(Fr(str(l)),sci(l)) for (lo,hi,L,H,a,b,l,h) in fw if lo<=T]
    v,s=max(cands,key=lambda c:c[0])
    nodesF.append(v); nodesS.append(s)
# checks
last=nodesF[-1]
def node(i): return nodesF[i] if i<len(nodesF) else last
ok=True
for (lo,hi,L,H) in allw:
    i=int(4*lo-4); j=int(4*hi-4)
    if not (node(i)>=L and node(j)<=H): ok=False; print("BAD",lo,hi,float(L),float(H),float(node(i)),float(node(j)))
assert all(nodesF[i]<=nodesF[i+1] for i in range(236))
print("ok",ok,len(nodesF),float(last))
out=[]
for i in range(0,237,8): out.append("  "+", ".join(nodesS[i:i+8]))
open('nodes_lean.txt','w').write(",\n".join(out))
