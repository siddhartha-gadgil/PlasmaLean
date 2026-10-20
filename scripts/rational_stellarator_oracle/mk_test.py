import sys, dense
from pipeline import *
from plan import Searcher
from lean_out import d3_str
from math import comb
fit=sys.argv[1]; delta=float(sys.argv[2]); wt=0.125; rf=0.5
P=load_P(fit)
sg=1
Qt,dQ=defect_chart(P,sg)
Dsz=max(j+k for j,r in enumerate(Qt) for k,f in enumerate(r) if any(f))
A=scale_root(Qt,1,10,Dsz)
dlt=int(delta*4*2**E)
tp=[0]*(2*dQ+1)
for m in range(dQ+1): tp[2*m]=comb(dQ,m)
D=[[[dlt*10**Dsz*x for x in tp]],[[dlt*4*10**(Dsz-1)*x for x in tp]],[[dlt*4*10**(Dsz-2)*x for x in tp]]]
dd=(deg_ax(A,0),deg_ax(A,1),deg_ax(A,2))
print('dd',dd)
dense.COST[0]=0
S=Searcher('abs',(1.0,1.0,wt),rem_frac=rf,floor=int(0.64*dlt*10**Dsz),dd=dd)
pl=S.search(A,D,0,[1.0,1.0,1.0],0)
print('cost',dense.COST[0],'leaves',S.leaves,len(pl))
open('/tmp/rsc/lt/T20.lean','w').write(f'''import PlasmaLean.Design.RationalStellaratorCover
open PlasmaLean.Design.RationalStellarator.Cover
set_option maxRecDepth 100000
def A : D3 := d3% "{d3_str(A)}"
def Dp : D3 := d3% "{d3_str(D)}"
def pl : Plan := plan% "{pl}"
set_option profiler true
theorem t : check true ({dd[0]}, {dd[1]}, {dd[2]}) pl A Dp 0 = true := by decide +kernel
''')
