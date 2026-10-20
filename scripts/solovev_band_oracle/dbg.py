import pickle,sys
from design2 import *
r=pickle.load(open(sys.argv[1],'rb'))
Fu=r['Fu']; Fs=r['Fs']; q=r['q']; Pq=mul(P,q)
for s in [0.1,0.3,0.5,0.7,0.9,0.97]:
    S=Fr(s); T=Phiinv(float(evalQ(Fu,S)))
    K=upLab(evalQ(Fu,S)); k=anyLow(evalQ(Fu,S),20)
    vals=[]
    for c in (r['chilo'],r['chihi']):
        for gg in (gL,gU):
            cond=float(evalQ(condQ(Fu,c,gg,hL),S)); src=float(evalQ(Pq,S))+float(evalQ(Pnu,S))*float(AHi*svCeilF(K)-BLo*sqL(k))
            vals.append((round(cond,3),round(src,3)))
    print(s,"T=%.2f"%T,K,k,vals)
