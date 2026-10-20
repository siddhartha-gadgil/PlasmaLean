import sys, dense
from pipeline import *
from plan import Searcher
from math import comb
from fractions import Fraction as Fr
from tsim3 import Jpoly
fit='fit_10_5_0.1_sym.pkl'
P=load_P(fit)
dI=5
Ia=Fr(sys.argv[1]); ca=Fr(sys.argv[2]); mu=Fr(sys.argv[3]); rho=Fr(sys.argv[4]); RF=float(sys.argv[5])
lam=1+mu
# polynomial (sparse, exact rationals then scaled): P - Ia*2^E - lam*2^E*(J - ca)   (C,S-degree <= 5; J has degree 1)
J={(2,0,0,0):Fr(1),(0,2,0,0):Fr(1),(0,2,0,1):Fr(1,2),(2,0,0,1):Fr(-1,2),(1,1,1,0):Fr(1)}
Pq={e:Fr(v) for e,v in P.items()}
Pq[(0,0,0,0)]=Pq.get((0,0,0,0),0)-Ia*2**E+lam*ca*2**E
for e,v in J.items(): Pq[e]=Pq.get(e,0)-lam*v*2**E
den=1
for v in Pq.values(): den=den*v.denominator//__import__('math').gcd(den,v.denominator)
Pi={e:int(v*den) for e,v in Pq.items() if v!=0}
It=trim(chart(Pi,dI,1))
Dsz=max(j+k for j,r in enumerate(It) for k,f in enumerate(r) if any(f))
A=scale_root(It,rho.numerator,rho.denominator,Dsz)
Dm=[[[0]]]
dd=(deg_ax(A,0),deg_ax(A,1),deg_ax(A,2))
dense.COST[0]=0
S=Searcher('up',(1.0,1.0,float(sys.argv[6])),rem_frac=RF,trunc=True,dd=dd)
pl=S.search(A,Dm,0,[1.0,1.0,1.0],0)
print('start cost',dense.COST[0],'leaves',S.leaves,'ok',pl is not None, (S.fail[:2] if pl is None else ''),'den',den)
