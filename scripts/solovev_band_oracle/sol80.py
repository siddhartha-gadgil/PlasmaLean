import math, sys
from ss import sv, solve_tri
aR=2.2908e22; bR=0.20094
import os
BETA=float(os.environ.get('BETA','0.7')); N0=float(os.environ.get('N0','0.9'))
ALPHA=float(os.environ.get('ALPHA',str(11/12)))
def nu(s): return N0*(1-ALPHA*s)/(1-BETA*s)
def dlnnu(s): return -ALPHA/(1-ALPHA*s)+BETA/(1-BETA*s)
def Phi(T): return T/10+T**3/300
def Phiinv(F):
    lo,hi=-100.0,200.0
    for _ in range(80):
        m=(lo+hi)/2
        if Phi(m)<F: lo=m
        else: hi=m
    return (lo+hi)/2
def chih(T): return 0.1+T*T/100
# steady: chi0*(g Phi'' + hw Phi') + S(s,T) = 0, g=gam*s, hw = h + dlnnu*gam*s
def steady(chi0,S,Te,gam=0.51,h=0.51,N=200,iters=4000):
    hh=1/N; xs=[i*hh for i in range(N+1)]
    P=[Phi(float(os.environ.get("TST","15"))*(1-x*x)+Te*x*x) for x in xs]; P[N]=Phi(Te)
    def res(P):
        r=[]
        for i in range(N):
            s=xs[i]; T=Phiinv(P[i])
            if i==0: d1=(P[1]-P[0])/hh; d2=0; g=0; hw=h
            else:
                d1=(P[i+1]-P[i-1])/(2*hh); d2=(P[i+1]-2*P[i]+P[i-1])/hh**2; g=gam*s; hw=h+dlnnu(s)*gam*s
            r.append(chi0*(g*d2+hw*d1)+S(s,T))
        return r
    dt=0.02
    for it in range(iters):
        Pold=P[:]
        for k in range(8):
            r=res(P); eps=1e-7; J={}
            for col in range(3):
                Pp=P[:]
                for j in range(col,N,3): Pp[j]+=eps
                r2=res(Pp)
                for i in range(N):
                    for j in (i-1,i,i+1):
                        if 0<=j<N and j%3==col: J[(i,j)]=(r2[i]-r[i])/eps
            # dPhi/dt = chih(T)*N
            ch=[chih(Phiinv(P[i])) for i in range(N)]
            di=[1/dt-ch[i]*J[(i,i)] for i in range(N)]
            lo=[-ch[i]*J.get((i,i-1),0) for i in range(N)]; up=[-ch[i]*J.get((i,i+1),0) for i in range(N)]
            dx=solve_tri(lo,di,up,[ch[i]*r[i]-(P[i]-Pold[i])/dt for i in range(N)])
            for i in range(N): P[i]+=dx[i]
            if max(map(abs,dx))<1e-10: break
        if max(abs(P[i]-Pold[i]) for i in range(N))<1e-9*dt: break
        dt=min(dt*1.3,100)
    return xs,P
def qaux(s,q0,k,fl): return q0*(1-s)**k+fl
def S0(q0,k,fl): return lambda s,T: nu(s)*(aR*sv(max(T,0.01))-bR*math.sqrt(max(T,0)))+qaux(s,q0,k,fl)
Vp=lambda s:1599*(1+0.05*s); hc=45261.
def report(chi0,q0,k,fl,Te=1.0):
    xs,P=steady(chi0,S0(q0,k,fl),Te)
    T=[Phiinv(p) for p in P]; N=len(xs)-1; hh=1/N
    w=lambda i: hh if 0<i<N else hh/2
    pa=sum(w(i)*hc*nu(xs[i])**2/0.9*0+0 for i in range(N+1))
    Pal=sum(w(i)*hc*Vp(xs[i])*nu(xs[i])*nu(xs[i])*aR*sv(T[i]) for i in range(N+1))  # heatcap(1e20)*nu * rate(nu*aR sv)
    Paux=sum(w(i)*hc*Vp(xs[i])*nu(xs[i])*qaux(xs[i],q0,k,fl) for i in range(N+1))
    c=1+53/60; keV=1.602176634e-16
    ratio=max(nu(xs[i])*1e20*c*T[i]*keV/(80000+456950*(1-11*xs[i]/12)) for i in range(N+1))
    print("chi0=%.3f q0=%g k=%g fl=%g: T0=%.2f T.3=%.2f T.9=%.2f Pal=%.0fMW Paux=%.1fMW Q=%.1f maxp/peq=%.3f"%(chi0,q0,k,fl,T[0],T[int(0.3*N)],T[int(0.9*N)],Pal/1e6,Paux/1e6,5*Pal/max(Paux,1e-9),ratio))
    return xs,T
if __name__=="__main__":
    for a in sys.argv[1:]:
        report(*[float(x) for x in a.split(',')])
