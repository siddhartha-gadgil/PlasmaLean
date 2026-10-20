import sys, dense
from pipeline import *
from plan import Searcher
from math import comb
from fractions import Fraction as Fr
fit='fit_10_5_0.1_sym.pkl'
P=load_P(fit)
dI=5
It=trim(chart(P,dI,1))
Dsz=10
Ia=float(sys.argv[1]); lam=Fr(sys.argv[2]); RF=float(sys.argv[3])
Iai=int(Ia*2**E)
tp=[comb(dI,m//2) if m%2==0 else 0 for m in range(2*dI+1)]
A=scale_root(It,1,40,Dsz)   # s = sigma/40 ; times 40^Dsz
# subtract Ia*(1+t^2)^5 + lam*(s^2+z^2-rho^2)(1+t^2)^5 with rho = 1/40 -> in sigma: (sigma^2+zeta^2-1)/1600
# scaled by 40^Dsz * 2^E (lam has denominator)
lamn, lamd = lam.numerator, lam.denominator
A=scal3(lamd, A)
c0 = lamd*Iai*40**Dsz - lamn*2**E*40**(Dsz-2)
sub=[[[c0*x for x in tp],[],[lamn*2**E*40**(Dsz-2)*x for x in tp]],[],[[lamn*2**E*40**(Dsz-2)*x for x in tp]]]
Af=add3(A,neg3(sub))
Dm=[[[0]]]
dd=(deg_ax(Af,0),deg_ax(Af,1),deg_ax(Af,2))
dense.COST[0]=0
S=Searcher('up',(1.0,1.0,0.125),rem_frac=RF,trunc=True,dd=dd)
pl=S.search(Af,Dm,0,[1.0,1.0,1.0],0)
print('start cost',dense.COST[0],'leaves',S.leaves,'ok',pl is not None, (S.fail[:2] if pl is None else ''))
