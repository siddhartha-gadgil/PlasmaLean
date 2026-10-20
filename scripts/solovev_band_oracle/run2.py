import sys, os, math, pickle
from fractions import Fraction as Fr
from design2 import *
args=dict(a.split('=') for a in sys.argv[1:])
g=lambda k,d: args.get(k,d)
chilo=Fr(g('chilo','1')); chihi=Fr(g('chihi','1')); q0=Fr(g('q0','2')); kq=int(g('kq','6'))
T1=Fr(g('T1','3/2')); KL=float(g('KL','0.2')); KU=float(g('KU','0.2')); m=int(g('m','10'))
Dl=Fr(g('Delta','40000')); kap=Fr(g('kap','1/20')); N=int(g('N','200')); KE=float(g('KE','0')); KLE=float(g('KLE','0'))
dw=lambda T: 0.25 if 5<=T<=30 else 1.0
q=scale(q0,[Fr(math.comb(kq,i)*(-1)**i) for i in range(kq+1)])
qf=lambda s: float(q0)*(1-s)**kq
SL=lambda s,T: nu(s)*(0.99*2.29e22*sv(min(max(T-dw(T),1.0),59))-0.201*float(sqB(Fr(T+0.1).limit_denominator(20))))+qf(s)-KL-KLE*s**8
SU=lambda s,T: nu(s)*(1.01*2.291e22*sv(min(max(T+dw(T),1.0),60))-0.2009*float(sqL(Fr(max(T-0.1,0)).limit_denominator(20))))+qf(s)+KU+KE*s**8
xs,PL=steady(float(chihi),SL,1.0,gam=float(gL),h=float(hU),N=N,gams=[float(gL),float(gU)],pick=min)
xs,PU=steady(float(chilo),SU,float(T1),gam=float(gU),h=float(hL),N=N,gams=[float(gL),float(gU)],pick=max)
Tsu=[Phiinv(p) for p in PU]
pr=max(nu(xs[i])*1e20*(1+53/60)*Tsu[i]*1.602176634e-16/(float(Dl)+456900*(1-11*xs[i]/12)) for i in range(N+1))
print("maxp/(peq+D)=%.3f"%pr)
if g('only','0')=='1':
    print("steady sub T0=%.2f T.3=%.2f; sup T0=%.2f T.3=%.2f"%(Phiinv(PL[0]),Phiinv(PL[60]),Phiinv(PU[0]),Phiinv(PU[60]))); sys.exit()
print("steady sub T0=%.2f T.3=%.2f; sup T0=%.2f T.3=%.2f"%(Phiinv(PL[0]),Phiinv(PL[60]),Phiinv(PU[0]),Phiinv(PU[60])))
Fs=toPsiPoly(PhiQ(1),lsfitF(PL,float(PhiQ(1)),m,N),10**6); Fu=toPsiPoly(PhiQ(T1),lsfitF(PU,float(PhiQ(T1)),m,N),10**6)
Pq=mul(P,q)
def QL(chi,gam): return lambda k,K: add(add(condQ(Fs,chi,gam,hU),Pq),scale(ALo*svFloorF(k)-BHi*sqB(K),Pnu))
def QU(chi,gam): return lambda k,K: scale(-1,add(add(condQ(Fu,chi,gam,hL),Pq),scale(AHi*svCeilF(K)-BLo*sqL(k),Pnu)))
QP=lambda k,K: add(mul(add([Dl],scale(Fr(456900),wp)),w2),scale(-NQ*10**20*Fr(113,60)*Fr(K)*keV,w1))
levL=[PhiQ(k) for k in GRIDL]
levU=[PhiQ(K) for K in sorted(CE) if K<=60]
def show(F,nm): print(nm,"T(0)=%.2f T(.3)=%.2f T(.9)=%.2f T(1)=%.2f"%tuple(Phiinv(float(evalQ(F,x))) for x in (0,.3,.9,1)))
show(Fs,"sub"); show(Fu,"sup")
print("min -F'",minon(scale(-1,deriv(Fs))),minon(scale(-1,deriv(Fu))),"gap",minon(add(Fu,scale(-1,Fs))))
pl,fl=pieces(Fs,[QL(c,gg) for c in (chilo,chihi) for gg in (gL,gU)],kap,10**4,False,levL,lowLab,lambda Fc: anyUp(Fc,20))
pu,fu=pieces(Fu,[QU(c,gg) for c in (chilo,chihi) for gg in (gL,gU)],kap,10**4,True,levU,lambda Fd: anyLow(Fd,20),upLab)
levP=[PhiQ(Fr(j,8)) for j in range(8,240)]
pp,fp=pieces(Fu,[QP],Fr(0),10**4,True,levP,lambda Fd: Fr(0),lambda Fc: anyUp(Fc,8))
print("lower",len(pl),fl,"upper",len(pu),fu,"pressure",len(pp),fp)
pickle.dump(dict(Fs=Fs,Fu=Fu,pl=pl,pu=pu,pp=pp,q=q,q0=q0,kq=kq,chilo=chilo,chihi=chihi,T1=T1,Dl=Dl,kap=kap),open(g('out','res2.pkl'),'wb'))
