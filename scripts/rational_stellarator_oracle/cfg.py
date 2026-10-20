import sys, dense
from pipeline import *
from plan import Searcher
from math import comb
from fractions import Fraction as Fr
def run(fit, delta, a_num, a_den, wt=0.125, rf=0.5, sg=1, dd_fixed=True, P=None):
    P=P or load_P(fit)
    Qt,dQ=defect_chart(P,sg)
    Dsz=max(j+k for j,r in enumerate(Qt) for k,f in enumerate(r) if any(f))
    A=scale_root(Qt,a_num,a_den,Dsz)
    dlt=int(delta*4*2**E)
    tp=[0]*(2*dQ+1)
    for m in range(dQ+1): tp[2*m]=comb(dQ,m)
    D=[[[dlt*a_den**Dsz*x for x in tp]],[[dlt*4*a_num*a_den**(Dsz-1)*x for x in tp]],[[dlt*4*a_num**2*a_den**(Dsz-2)*x for x in tp]]]
    dd=(deg_ax(A,0),deg_ax(A,1),deg_ax(A,2)) if dd_fixed else None
    dense.COST[0]=0
    a=a_num/a_den
    S=Searcher('abs',(1.0,1.0,wt),rem_frac=rf,floor=int((1-2*a)**2*dlt*a_den**Dsz),dd=dd)
    pl=S.search(A,D,0,[1.0,1.0,1.0],0)
    return dense.COST[0], S.leaves, pl, A, D, dd
if __name__=="__main__":
    fit=sys.argv[1]
    for args in sys.argv[2:]:
        d,an,ad,wt=args.split(',')
        c,l,pl,_,_,_=run(fit,float(d),int(an),int(ad),float(wt))
        print(args,'cost',c,'leaves',l,flush=True)
