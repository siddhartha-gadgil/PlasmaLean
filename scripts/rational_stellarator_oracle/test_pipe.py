from pipeline import *
from poly import *
import numpy as np, dense
P=load_P('fit_10_5_0.1.pkl')
dense.COST[0]=0
Qt,dQ=defect_chart(P,1)
print('cost',dense.COST[0],'dQ',dQ,'shape',len(Qt),max(len(r) for r in Qt), sum(len(f) for r in Qt for f in r))
# check against float
Pf={e:v/2**E for e,v in P.items()}
G,N,Nt=field_polys(0.25,1.0)
Q=lie(Pf,G)
for (s,z,t) in [(0.03,-0.05,0.3),(-0.08,0.02,-0.9)]:
    C=(1-t*t)/(1+t*t); S=2*t/(1+t*t)
    v=peval(Q,[s,z,C,S])*(1+t*t)**dQ*4*2**E
    print(v, eval3(Qt,s,z,t))
