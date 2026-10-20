import math, sys, os, pickle
from fractions import Fraction as Fr
os.environ.setdefault('ALPHA','0.8'); os.environ.setdefault('BETA','0.3'); os.environ.setdefault('N0','0.9')
from qp import *
from sol import steady, Phi, Phiinv, sv, nu
from bhfine import fine
AQ=Fr(4,5); BQ=Fr(3,10); NQ=Fr(9,10)
W=[l.split() for l in open('windows.txt')]
W=[(Fr(int(x[0])),Fr(int(x[1])),Fr(x[2]),Fr(x[3])) for x in W]
WF=[(Fr(a,4),Fr(b,4),Fr(str(l)),Fr(str(h))) for a,b,l,h in fine()]
FL={}; CE={}
for lo,hi,l,h in W+WF:  # fine overrides coarse (same values at shared ends anyway)
    FL[lo]=l; CE[hi]=h
def svFloorF(k): return FL.get(Fr(k),Fr(0))
def svCeilF(K): return CE.get(Fr(K),Fr(0))
def sqB(K):
    for lim,m in ((2,1),(6,2),(12,3),(20,4)):
        if K<=lim: return (K+m*m)/Fr(2*m)
    return (K+25)/Fr(10)
def sqL(k):
    for lim,m in ((2,1),(6,2),(12,3),(20,4)):
        if k<=lim: return 2*m*k/(k+m*m)
    return 10*k/(k+25)
def PhiQ(T): T=Fr(T); return T/10+T**3/300
w1=[Fr(1),-AQ]; w2=[Fr(1),-BQ]; wp=[Fr(1),Fr(-11,12)]
P=mul(w1,w2); Pdl=add(scale(-AQ,w2),scale(BQ,w1)); Pnu=scale(NQ,mul(w1,w1))
gL,gU,hL,hU=Fr(49,100),Fr(21,40),Fr(49,100),Fr(21,40)
keV=Fr(1602176634,10**25)
ALo=Fr(229,10)*10**21; AHi=Fr(2291,100)*10**21; BHi=Fr(201,1000); BLo=Fr(2009,10000)
def condQ(F,chi,gam,h):
    d1=deriv(F); d2=deriv(d1)
    return scale(chi,add(scale(gam,mul([0,1],add(mul(P,d2),mul(Pdl,d1)))),scale(h,mul(P,d1))))
def lsfitF(Fv,F1,m,N):
    xs=[i/N for i in range(N+1)]
    A=[[(1-x)**j for j in range(1,m+1)] for x in xs]; b=[Fv[i]-F1 for i in range(N+1)]
    M=[[sum(A[r][i]*A[r][j] for r in range(N+1)) for j in range(m)]+[sum(A[r][i]*b[r] for r in range(N+1))] for i in range(m)]
    for i in range(m):
        p=max(range(i,m),key=lambda r:abs(M[r][i])); M[i],M[p]=M[p],M[i]
        for r in range(i+1,m):
            f_=M[r][i]/M[i][i]
            for c in range(i,m+1): M[r][c]-=f_*M[i][c]
    c=[0]*m
    for i in range(m-1,-1,-1): c[i]=(M[i][m]-sum(M[i][j]*c[j] for j in range(i+1,m)))/M[i][i]
    return c
def toPsiPoly(F1,cs,den):
    Q=[Fr(0)]*(len(cs)+1); Q[0]=Fr(F1)
    for j,v in enumerate(cs,1):
        vr=Fr(round(v*den),den)
        for i in range(j+1): Q[i]+=vr*math.comb(j,i)*(-1)**i
    return Q
def crossF(F,levels):
    out=[]; f0=float(evalQ(F,0)); f1=float(evalQ(F,1))
    for L in levels:
        if f1<float(L)<f0:
            a,b=0.0,1.0
            for _ in range(60):
                m=(a+b)/2
                if float(evalQ(F,m))>float(L): a=m
                else: b=m
            out.append(a)
    return sorted(out)
GRIDL=[Fr(j) for j in range(0,5)]+[Fr(j,4) for j in range(20,121)]+[Fr(j) for j in range(31,61)]
def lowLab(Fd):  # largest grid label k with Phi(k)<=F(d)
    return max([k for k in GRIDL if PhiQ(k)<=Fd])
def upLab(Fc):   # smallest window end K with F(c)<=Phi(K)
    return min([K for K in sorted(CE) if PhiQ(K)>=Fc and K<=60])
def anyUp(Fc,den):
    K=Fr(math.ceil(Phiinv(float(Fc))*den),den)
    while PhiQ(K)<Fc: K+=Fr(1,den)
    return K
def anyLow(Fd,den):
    k=Fr(math.floor(Phiinv(float(Fd))*den),den)
    while PhiQ(k)>Fd: k-=Fr(1,den)
    return max(k,Fr(0))
def pieces(F,Qfs,kap,rnd,up,levels,lowf,upf,maxsub=(1,2,3,4,6,8,12,16,24,32,48)):
    cr=crossF(F,levels)
    rf=math.ceil if up else math.floor
    ends=sorted(set(Fr(rf(p*rnd),rnd) for p in cr if 0<rf(p*rnd)<rnd))+[Fr(1)]
    ps=[]; c=Fr(0); fails=0; worst=None
    for d in ends:
        ok=False
        for n in maxsub:
            pts=[c+(d-c)*Fr(i,n) for i in range(n+1)]
            sub=[]
            good=True
            for i in range(n):
                a,b=pts[i],pts[i+1]
                k=lowf(evalQ(F,b)); K=upf(evalQ(F,a))
                if not all(kap<=lowerBound(b-a,shift(a,Qf(k,K))) for Qf in Qfs): good=False; break
                sub.append((b,k,K))
            if good: ps+=sub; ok=True; break
        if not ok:
            fails+=1
            k=lowf(evalQ(F,d)); K=upf(evalQ(F,c))
            mn=min(min(float(evalQ(Qf(k,K),c+(d-c)*Fr(i,40))) for i in range(41)) for Qf in Qfs)
            print("   FAIL",float(c),float(d),k,K,"minQ",mn); ps.append((d,k,K))
        c=d
    return ps,fails
def minon(p,n=2000): return min(float(evalQ(p,Fr(i,n))) for i in range(n+1))
