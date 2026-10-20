import math, sys
# Bosch-Hale DT reactivity m^3/s, T keV
def sv(T):
    BG=34.3827; mrc2=1124656; C1=1.17302e-9;C2=1.51361e-2;C3=7.51886e-2;C4=4.60643e-3;C5=1.35e-2;C6=-1.0675e-4;C7=1.366e-5
    th=T/(1-T*(C2+T*(C4+T*C6))/(1+T*(C3+T*(C5+T*C7))))
    xi=(BG**2/(4*th))**(1/3)
    return C1*th*math.sqrt(xi/(mrc2*T**3))*math.exp(-3*xi)*1e-6
a=2.5
alphaRate=2.2908e22; bremsRate=0.20094
def qaux(p, A=134.0, fl=0.43): return A*p*(1-p)**8+fl
def chihat(T): return 0.1+T*T/100
def dchihat(T): return T/50
def R(p,T,A,fl): return alphaRate*sv(max(T,0.01))+qaux(p,A,fl)-bremsRate*math.sqrt(max(T,0))
def solve_tri(lo,di,up,rhs):
    n=len(di); c=[0]*n; d=[0]*n
    c[0]=up[0]/di[0]; d[0]=rhs[0]/di[0]
    for i in range(1,n):
        m=di[i]-lo[i]*c[i-1]
        c[i]=up[i]/m if i<n-1 else 0
        d[i]=(rhs[i]-lo[i]*d[i-1])/m
    x=[0]*n; x[-1]=d[-1]
    for i in range(n-2,-1,-1): x[i]=d[i]-c[i]*x[i+1]
    return x
def residual(T,chi0,A,fl,N):
    h=1/N; k=4*chi0/a**2
    F=[0]*(N)
    for i in range(N):
        pm=(i+0.5)*h; Tm=(T[i]+T[i+1])/2
        F[i]=pm*chihat(Tm)*(T[i+1]-T[i])/h
    res=[0]*N
    for i in range(N):
        p=i*h
        if i==0: div=F[0]/(h/2)
        else: div=(F[i]-F[i-1])/h
        res[i]=k*div+R(p,T[i],A,fl)
    return res
def march(T,chi0,A,fl,N,dt=0.05,steps=4000):
    h=1/N
    for s in range(steps):
        Told=T[:]
        for it in range(8):
            res=residual(T,chi0,A,fl,N)
            # numerical jacobian tridiagonal
            eps=1e-6
            lo=[0]*N;di=[0]*N;up=[0]*N
            for j in range(N):
                Tp=T[:]; Tp[j]+=eps
                r2=residual(Tp,chi0,A,fl,N) if False else None
            # analytic-ish: perturb by coloring (3 colors)
            J={}
            for col in range(3):
                Tp=T[:]
                for j in range(col,N,3): Tp[j]+=eps
                r2=residual(Tp,chi0,A,fl,N)
                for i in range(N):
                    for j in (i-1,i,i+1):
                        if 0<=j<N and j%3==col:
                            J[(i,j)]=(r2[i]-res[i])/eps
            for i in range(N):
                di[i]=1/dt - J[(i,i)]
                lo[i]=-J.get((i,i-1),0); up[i]=-J.get((i,i+1),0)
            rhs=[res[i]-(T[i]-Told[i])/dt for i in range(N)]
            dx=solve_tri(lo,di,up,rhs)
            for i in range(N): T[i]+=dx[i]
            if max(abs(x) for x in dx)<1e-10: break
        if max(abs(T[i]-Told[i]) for i in range(N))<1e-9*dt: break
        dt=min(dt*1.2,50)
    return T
if __name__=="__main__":
    chi0=float(sys.argv[1]); A=float(sys.argv[2]); fl=float(sys.argv[3]); N=60
    for T0 in (3,30):
        T=[T0*(1-i/N)+1*(i/N) for i in range(N)]+[1.0]
        T=march(T,chi0,A,fl,N)
        print("start",T0,"T(0)=%.2f T(.1)=%.2f T(.3)=%.2f T(.5)=%.2f T(.9)=%.2f"%(T[0],T[6],T[18],T[30],T[54]))
