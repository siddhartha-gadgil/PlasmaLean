import sys, dense
from pipeline import *
from plan import Searcher
from math import comb
fit='fit_10_5_0.1_sym.pkl'
P=load_P(fit)
dI=max(e[2]+e[3] for e in P)
print('P terms',len(P),'dI',dI, 'parity ok', all((e[1]+e[2])%2==0 for e in P))
It=trim(chart(P,dI,1))
Dsz=max(j+k for j,r in enumerate(It) for k,f in enumerate(r) if any(f))
print('I Dsz',Dsz,'entries',sum(len(f) for r in It for f in r))
Ib=float(sys.argv[1]); Ia=0.0010; RF=float(sys.argv[2]); WT=float(sys.argv[3])
Ibi=int(Ib*2**E); Iai=int(Ia*2**E)
tp=[comb(dI,m//2) if m%2==0 else 0 for m in range(2*dI+1)]
A10=scale_root(It,1,10,Dsz)   # sigma = s*10
def restrict(A,ax,sgn):
    if ax==0:
        out=[]
        for j,B in enumerate(A):
            out=add2(out,[[x*(sgn**j) for x in f] for f in B])
        return [out]
    else:
        return [[ [sum((sgn**k)*(B[k][m] if m<len(B[k]) else 0) for k in range(len(B))) for m in range(max((len(f) for f in B),default=0))] ] for B in A]
tot=0
for ax in (0,1):
    for sgn in (1,-1):
        F=restrict(A10,ax,sgn)
        # A := Ib*10^Dsz*(1+t^2)^dI - F ; D := -1 (upper mode)
        Bp=[[[Ibi*10**Dsz*x for x in tp]]]
        Af=add3(Bp,neg3(F)) if True else None
        Dm=[[[-1]]]
        dd=(deg_ax(Af,0),deg_ax(Af,1),deg_ax(Af,2))
        dense.COST[0]=0
        S=Searcher('up',(1.0,1.0,WT),rem_frac=RF,trunc=True,dd=dd)
        pl=S.search(Af,Dm,0,[1.0,1.0,1.0],0)
        print('face',ax,sgn,'cost',dense.COST[0],'leaves',S.leaves,'ok',pl is not None, S.fail if pl is None else '')
        tot+=dense.COST[0]
print('faces total',tot)
