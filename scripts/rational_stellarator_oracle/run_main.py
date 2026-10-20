import sys, dense
from pipeline import *
from plan import Searcher
from math import comb
fit=sys.argv[1]; delta=float(sys.argv[2]); wt=float(sys.argv[3]); rf=float(sys.argv[4]) if len(sys.argv)>4 else 0.3
P=load_P(fit)
for sg in (1,-1):
    dense.COST[0]=0
    Qt,dQ=defect_chart(P,sg)
    c_root=dense.COST[0]
    Dsz=max(j+k for j,r in enumerate(Qt) for k,f in enumerate(r) if any(f))
    A=scale_root(Qt,1,10,Dsz)
    dlt=int(delta*4*2**E)
    # D = dlt (1+2s)^2 (1+t^2)^dQ scaled: s = sigma/10
    tp=[0]*(2*dQ+1)
    for m in range(dQ+1): tp[2*m]=comb(dQ,m)
    D=[[[dlt*10**Dsz*x for x in tp]],[[dlt*4*10**(Dsz-1)*x for x in tp]],[[dlt*4*10**(Dsz-2)*x for x in tp]]]
    dense.COST[0]=0
    S=Searcher('abs',(1.0,1.0,wt),rem_frac=rf,floor=int(0.64*dlt*10**Dsz))
    pl=S.search(A,D,0,[1.0,1.0,1.0],0)
    print('chart',sg,'root cost',c_root,'tree cost',dense.COST[0],'leaves',S.leaves,'nodes',S.nodes,'plan len',len(pl) if pl else None, S.fail)
    print(sorted(S.depth_cost.items()))
    if pl: open(f'plan_main_{sg}.txt','w').write(pl)
