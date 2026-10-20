import pickle, numpy as np, sys
from poly import *
K,M=int(sys.argv[1]),int(sys.argv[2])
L,c=pickle.load(open(f'fit_{K}_{M}_0.1.pkl','rb'))
G,N,Nt=field_polys(0.25,1.0)
P=I_poly(L,c,1.0)
Q=lie(P,G)
Qr=reduce_circle(Q)
print('terms P',len(P),'Q',len(Q),len(Qr))
rng=np.random.default_rng(1)
n=100000
a=0.1
s=a*(2*rng.random(n)-1); z=a*(2*rng.random(n)-1); th=2*np.pi*rng.random(n)
x=[s,z,np.cos(th),np.sin(th)]
Iv=peval(P,x); Qv=peval(Q,x)
Ib=0.00417
m=Iv<=Ib
mx=np.abs(Qv[m]).max()
for name,QQ in (('raw',Q),('red',Qr)):
    absQ=sum(abs(cc)*np.abs(np.prod([x[i]**e[i] for i in range(4)],axis=0)) for e,cc in QQ.items())
    print(name,'max|Q|',mx,'abs',absQ[m].max(),'F',absQ[m].max()/mx)
# fourier-form F: coefficients of s^j z^k cos/sin n th
# compute via sampling theta exactly: project reduce form into fourier using numeric fft on theta grid
from collections import defaultdict
sz=defaultdict(dict)
for e,cc in Qr.items(): sz[(e[0],e[1])][(e[2],e[3])]=cc
nt=64; tg=np.linspace(0,2*np.pi,nt,endpoint=False)
four={}
for jk,d in sz.items():
    f=sum(cc*np.cos(tg)**e2*np.sin(tg)**e3 for (e2,e3),cc in d.items())
    F=np.fft.rfft(f)/nt
    four[jk]=F
absF=np.zeros(n)
for (j,k),F in four.items():
    w=np.abs(s)**j*np.abs(z)**k
    absF+=w*(np.abs(F[0].real)+2*np.sum(np.abs(F[1:].real)+np.abs(F[1:].imag)))
print('fourier abs F', absF[m].max()/mx)
