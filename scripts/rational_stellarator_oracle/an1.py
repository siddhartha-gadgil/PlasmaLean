import pickle, numpy as np, sys
from poly import *
K,M=int(sys.argv[1]),int(sys.argv[2])
L,c=pickle.load(open(f'fit_{K}_{M}_0.1.pkl','rb'))
G,N,Nt=field_polys(0.25,1.0)
P=I_poly(L,c,1.0)
Q=lie(P,G)
Pr=reduce_circle(P); Qr=reduce_circle(Q)
print('terms P',len(P),len(Pr),'Q',len(Q),len(Qr))
print('max deg Q', max(sum(e[:2]) for e in Q), max(e[0] for e in Q), max(e[1] for e in Q), max(e[2]+e[3] for e in Q))
rng=np.random.default_rng(1)
n=200000
a=0.1
s=a*(2*rng.random(n)-1); z=a*(2*rng.random(n)-1); th=2*np.pi*rng.random(n)
x=[s,z,np.cos(th),np.sin(th)]
Iv=peval(P,x); Qv=peval(Q,x); Qrv=peval(Qr,x)
absQ=sum(abs(cc)*np.abs(np.prod([x[i]**e[i] for i in range(4)],axis=0)) for e,cc in Qr.items())
Ib=0.0041
m=Iv<=Ib
print('max|Q|',np.abs(Qv[m]).max(), np.abs(Qrv[m]).max(),'max abs-sum',absQ[m].max(),'ratio',absQ[m].max()/np.abs(Qv[m]).max())
for d in range(0,12):
    Qd={e:v for e,v in Qr.items() if e[0]+e[1]==d}
    if not Qd: continue
    v=peval(Qd,x)
    ab=sum(abs(cc)*np.abs(np.prod([x[i]**e[i] for i in range(4)],axis=0)) for e,cc in Qd.items())
    print(d,len(Qd),'max|Qd|',np.abs(v[m]).max(),'abs',ab[m].max())
