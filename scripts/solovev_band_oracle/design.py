import math, sys
from fractions import Fraction as Fr
from qp import *
from sol import steady, Phi, Phiinv, nu, sv, BETA, N0, ALPHA
W=[l.split() for l in open('windows.txt')]
W=[(int(x[0]),int(x[1]),Fr(x[2]),Fr(x[3])) for x in W]
def svFloor(k):
    for lo,hi,l,h in W:
        if lo==k: return l
    return Fr(0)
def svCeil(k):
    for lo,hi,l,h in W:
        if hi==k: return h
    return Fr(0)
def PhiQ(T): T=Fr(T); return T/10+T**3/300
BQ=Fr(BETA).limit_denominator(100); NQ=Fr(N0).limit_denominator(100)
AQ=Fr(ALPHA).limit_denominator(100)
w1=[Fr(1),-AQ]; w2=[Fr(1),-BQ]; wp=[Fr(1),Fr(-11,12)]
P=mul(w1,w2); Pdl=add(scale(-AQ,w2),scale(BQ,w1)); Pnu=scale(NQ,mul(w1,w1))
gL,gU,hL,hU=Fr(49,100),Fr(21,40),Fr(49,100),Fr(21,40)
keV=Fr(1602176634,10**25)
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
    for (T,L) in levels:
        if f1<float(L)<f0:
            a,b=0.0,1.0
            for _ in range(60):
                m=(a+b)/2
                if float(evalQ(F,m))>float(L): a=m
                else: b=m
            out.append((a,T))
    return sorted(out)
def pieces(F,Qfs,kap,rnd,up,levels,Kfine=None,maxsub=48):
    cr=crossF(F,levels)
    rf=math.ceil if up else math.floor
    ends=sorted(set(Fr(rf(p*rnd),rnd) for p,T in cr if 0<rf(p*rnd)<rnd))+[Fr(1)]
    ps=[]; c=Fr(0); fails=0
    for d in ends:
        Fd=evalQ(F,d); Fc=evalQ(F,c)
        k=max([T for T in range(0,61) if PhiQ(T)<=Fd]+[0])
        if Kfine:
            K=Fr(math.ceil(Phiinv(float(Fc))*Kfine),Kfine)
            while PhiQ(K)<Fc: K+=Fr(1,Kfine)
        else: K=min([T for T in range(1,61) if PhiQ(T)>=Fc]+[60])
        ok=False
        for n in (1,2,3,4,6,8,12,16,24,32,48):
            pts=[c+(d-c)*Fr(i,n) for i in range(n+1)]
            if all(all(kap<=lowerBound(pts[i+1]-pts[i],shift(pts[i],Qf(k,K))) for Qf in Qfs) for i in range(n)):
                ps+=[(pts[i+1],k,K) for i in range(n)]; ok=True; break
        if not ok:
            fails+=1
            mn=min(min(float(evalQ(Qf(k,K),c+(d-c)*Fr(i,40))) for i in range(41)) for Qf in Qfs)
            print("   FAIL",float(c),float(d),k,K,"minQ",mn); ps.append((d,k,K))
        c=d
    return ps,fails
