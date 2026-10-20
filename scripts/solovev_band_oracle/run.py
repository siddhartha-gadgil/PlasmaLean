from design import *
chilo,chihi=Fr(sys.argv[1]),Fr(sys.argv[2]); q0=Fr(sys.argv[3]); kq=int(sys.argv[4]); T1=Fr(sys.argv[5])
KL=float(sys.argv[6]); KU=float(sys.argv[7]); m=int(sys.argv[8]) if len(sys.argv)>8 else 10
kap=Fr(1,20); N=int(__import__("os").environ.get("NN","200"))
q=scale(q0,[Fr(math.comb(kq,i)*(-1)**i) for i in range(kq+1)])   # q0 (1-s)^kq
qf=lambda s: float(q0)*(1-s)**kq
# design steady states with conservative geometry
KLE=float(__import__('os').environ.get('KLE','0'))
SL=lambda s,T: nu(s)*(0.99*2.29e22*sv(min(max(T-1,1.0),59))-0.201*(T+5)/4)+qf(s)-KL-KLE*s**8
KE=float(__import__('os').environ.get('KE','0'))
SU=lambda s,T: nu(s)*(2.291e22*sv(min(max(T+1,1.0),60)))+qf(s)+KU+KE*s**8
xs,PL=steady(float(chihi),SL,1.0,gam=float(gU),h=float(hU),N=N)
xs,PU=steady(float(chilo),SU,float(T1),gam=float(gL),h=float(hL),N=N)
print("steady sub T0=%.2f T.3=%.2f; sup T0=%.2f T.3=%.2f"%(Phiinv(PL[0]),Phiinv(PL[60]),Phiinv(PU[0]),Phiinv(PU[60])))
Fs=toPsiPoly(PhiQ(1),lsfitF(PL,float(PhiQ(1)),m,N),10**6); Fu=toPsiPoly(PhiQ(T1),lsfitF(PU,float(PhiQ(T1)),m,N),10**6)
Pq=mul(P,q)
def QL(chi,gam): return lambda k,K: add(add(condQ(Fs,chi,gam,hU),Pq),scale(Fr(229,10)*10**21*svFloor(k)-Fr(201,1000)*(Fr(K)+4)/4,Pnu))
def QU(chi,gam): return lambda k,K: scale(-1,add(add(condQ(Fu,chi,gam,hL),Pq),scale(Fr(2291,100)*10**21*svCeil(K),Pnu)))
QP=lambda k,K: add(mul(add([Fr(40000)],scale(Fr(456900),wp)),w2),scale(-NQ*10**20*Fr(113,60)*Fr(K)*keV,w1))
levL=[(T,PhiQ(T)) for T in range(1,61)]+[(Fr(j,8),PhiQ(Fr(j,8))) for j in range(9,32) if j%8]
levU=[(T,PhiQ(T)) for T in range(1,61)]
pl,fl=pieces(Fs,[QL(c,g) for c in (chilo,chihi) for g in (gL,gU)],kap,10**4,False,levL,Kfine=20)
pu,fu=pieces(Fu,[QU(c,g) for c in (chilo,chihi) for g in (gL,gU)],kap,10**4,True,levU)
levP=[(Fr(j,4),PhiQ(Fr(j,4))) for j in range(4,120)]
pp,fp=pieces(Fu,[QP],Fr(0),10**4,True,levP,Kfine=8)
def show(F,nm): print(nm,"T(0)=%.2f T(.3)=%.2f T(.9)=%.2f T(1)=%.2f"%tuple(Phiinv(float(evalQ(F,x))) for x in (0,.3,.9,1)))
show(Fs,"sub"); show(Fu,"sup")
print("lower",len(pl),fl,"upper",len(pu),fu,"pressure",len(pp),fp)
def minon(p,n=4000): return min(float(evalQ(p,Fr(i,n))) for i in range(n+1))
print("min -F'",minon(scale(-1,deriv(Fs))),minon(scale(-1,deriv(Fu))),"gap",minon(add(Fu,scale(-1,Fs))))
import pickle; pickle.dump(dict(Fs=Fs,Fu=Fu,pl=pl,pu=pu,pp=pp,q=q,chilo=chilo,chihi=chihi,T1=T1),open('res.pkl','wb'))
import os
if os.environ.get('DIAG'):
    for s0 in (0.9,0.95,0.98,0.99,0.995,0.999,1.0):
        sQ=Fr(s0); T=Phiinv(float(evalQ(Fu,sQ)))
        K=math.ceil(T)
        vals=[float(evalQ(QU(c,g)(0,max(K,2)),sQ)) for c in (chilo,chihi) for g in (gL,gU)]
        # nominal smooth: -P*(N) with design geometry gL,hL and sv(T+1)
        d1=float(evalQ(deriv(Fu),sQ)); d2=float(evalQ(deriv(deriv(Fu)),sQ)); s=s0
        Nn=float(chilo)*(float(gL)*s*d2+(float(hL)+(-ALPHA/(1-ALPHA*s)+BETA/(1-BETA*s))*float(gL)*s)*d1)+SU(s,T)-KU-KE*s**8
        print(s0,"T=%.2f"%T,"corners",["%.3f"%v for v in vals],"P*Nnominal(with sv(T+1))=%.3f"%(float(evalQ(P,sQ))*Nn))
