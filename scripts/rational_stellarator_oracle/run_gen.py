import sys, json, pickle
from gen import *
import dense
fit='fit_10_5_0.1_sym.pkl'
P=load_P(fit)
print('P terms',len(P))
dense.COST[0]=0
Q,dQ=mainRoot(P,1)
print('mainRoot cost(dense ops not counted)', 'dQ',dQ, 'degs', degs(Q))
dsg, dze, dta = degs(Q)
A=trim(scale0(10,dsg,scale1(10,dze,Q)))
# compare to old pipeline
from pipeline import defect_chart, load_P as lp2
Qold,_=defect_chart({tuple(e):c for c,e in P},1)
from dense import eval3
print('check', eval3(Q,0.03,-0.02,0.4), eval3(Qold,0.03,-0.02,0.4))
delta=int(sys.argv[1]) if len(sys.argv)>1 else 17592186
fac=10**(dsg+dze)
tp=onePlusSq(dQ)
D=[[[delta*fac*x for x in tp]],[[delta*4*(fac//10)*x for x in tp]],[[delta*4*(fac//100)*x for x in tp]]]
dd=(max(degs(A)[0],degs(D)[0]),max(degs(A)[1],degs(D)[1]),max(degs(A)[2],degs(D)[2]))
print('dd',dd)
dense.COST[0]=0
S=Searcher('abs',(1.0,1.0,0.125),rem_frac=0.5,floor=int(0.64*delta*fac),dd=dd)
pl=S.search(A,D,0,[1.0,1.0,1.0],0)
print('main cost',dense.COST[0],'leaves',S.leaves,'nodes',S.nodes)
pickle.dump(dict(P=P,Q=Q,A=A,D=D,dd=dd,plan=pl,delta=delta,dsg=dsg,dze=dze,dQ=dQ),open('main_data.pkl','wb'))
