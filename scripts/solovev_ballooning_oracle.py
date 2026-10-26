"""UNTRUSTED oracle for the ballooning certificate of the reactor Solov'ev equilibrium.

NOT part of the trusted base: everything produced here is re-checked by the Lean kernel
(PlasmaLean/Design/SolovevBallooning*.lean). Only standard axioms are used there.

What it does (one pipeline, three steps):

  data  -- solve a convex SOCP (cvxpy + Clarabel) for ONE set of Riccati certificate data valid
           for all surfaces psiT = s^2, 0 < s <= 25: the scaled flux
               Phi = u a + x A0(y) + x A1(y) w^2/(w^2+u^2) + A2(y) w u/(w^2+u^2),  w = 2,
           u = s * sigma, a = delta + 3 beta_hat / |B|^2, with coefficients quadratic in s and the
           s^0 coefficients fixed so that the certificate degenerates exactly on the magnetic
           axis (f0 = (3 sqrt2/35) x + O(s)). The margin of the scaled Riccati inequality is
           maximised relative to the per-surface optimum. Writes a JSON file.
  plan  -- adaptive binary subdivision of the (tau, s) rectangle [-1,1] x [0,25]
           (tau = t/NT, s = n/NS, NT = 4096, NS = 1024) using an EXACT integer mirror of the
           kernel checker `boxOK`/`axisOK` of SolovevBallooningDefs.lean (fixed-point balls,
           second-order forward mode, Polya test), with a one-step lookahead planner.
  emit  -- write SolovevBallooningData.lean, the cell modules SolovevBallooningCells*.lean
           (shared corner lemmas `cn..`, box lemmas `cov..`) and the assembly plan, and install
           them (updating the cover literal and imports of SolovevBallooning.lean).

Usage:
  python scripts/solovev_ballooning_oracle.py data  out.json           (needs numpy, cvxpy)
  python scripts/solovev_ballooning_oracle.py plan  out.json plan.txt
  python scripts/solovev_ballooning_oracle.py emit  out.json plan.txt GENDIR [K=16]
  python scripts/solovev_ballooning_oracle.py install GENDIR
"""
import sys, json, math, re, glob, os, shutil
from fractions import Fraction
from functools import lru_cache
try:
    import numpy as np
except ImportError:  # only needed for `data`
    np = None
sys.setrecursionlimit(10000)

# ----------------------------------------------------------------------------------------
# 1. Floating-point model of the scaled coefficients (for the SOCP only)
# ----------------------------------------------------------------------------------------
A=7/4; L=10.; F=50.; cA=A/L**2; r2=math.sqrt(2); rate=F*L**2/(r2*A)
def trip(B,b,g):
    BR,BP,BZ=B; bR,bP,bZ=b; gR,gZ=g
    return (BP*bZ-BZ*bP)*gR + (BR*bP-BP*bR)*gZ
def base(s,x,y):
    """scaled coefficients: P_hat=s^2 P(sigma~/s) coefficients, Theta = s q0 + sig~ q1, dh = s d, a = delta + 3 iB beta"""
    R=np.sqrt(L**2+2*s*y); iR=1/R; zh=r2*x*iR; Wh=s*zh**2+2*y
    BR,BP,BZ=-cA*s*R*zh, F*iR, cA*s*Wh
    gsR,gsZ=R*Wh/2, R*x*r2/2
    gtR,gtZ=x*(100+s*y)*iR, -R*y*r2/2
    Phit=-rate*iR**3
    kR,kP,kZ=-Phit*gtR, s*iR, -Phit*gtZ
    ell=200*r2*iR/7
    GR=cA*cA*s*s*R*zh**2-2500*iR**3-cA*cA*s*R*Wh; GZ=2*cA*cA*s*zh*(s*Wh-R*R)
    B2=BR**2+BP**2+BZ**2; iB=1/B2
    den=7*r2*R*iB/400
    p0=(kR**2+kP**2+kZ**2)*den; p1=-2*(kR*gsR+kZ*gsZ)*den; p2=(gsR**2+gsZ**2)*den
    sq0=-6*cA*ell*trip((BR,BP,BZ),(kR,kP,kZ),(GR,GZ))*iB**2
    q1=6*cA*ell*trip((BR,BP,BZ),(gsR,0*x,gsZ),(GR,GZ))*iB**2
    dh=s*3*rate*y*iR**5
    beta=cA*cA*s*(R*R*zh**2+Wh**2)-50*y*iR**2
    acore=3*iB*beta
    return dict(p0=p0,p1=p1,p2=p2,sq0=sq0,q1=q1,d=dh,acore=acore,B2=B2,R=R)

# ----------------------------------------------------------------------------------------
# 2. SOCP for the certificate data
# ----------------------------------------------------------------------------------------
def _cvxpy():
    import cvxpy as cp
    return cp
def solve(svals, w=2.0, K=2, Nt=256, Nc=41, fixed=None, verbose=True):
    """common data for all s in svals (scaled formulation); returns data & margin"""
    ts=np.linspace(0,2*np.pi,Nt,endpoint=False); x=np.cos(ts); y=np.sin(ts)
    Xb=np.array([x*y**k for k in range(K+1)]).T
    dXb=np.array([-y**(k+1)+(k*(1-y**2)*y**(k-1) if k>0 else 0) for k in range(K+1)]).T
    Yb=np.array([y**k for k in range(K+1)]).T
    dYb=np.array([(k*y**(k-1)*x if k>0 else 0*y) for k in range(K+1)]).T
    c0=_cvxpy().Variable(K+1); c1=_cvxpy().Variable(K+1); c2=_cvxpy().Variable(K+1); dl=_cvxpy().Variable(); m=_cvxpy().Variable()
    chis=np.linspace(-np.pi/2,np.pi/2,Nc)[1:-1]
    cons=[]
    for s in svals:
        b=base(s,x,y)
        a=dl+b['acore']
        f0=Xb@c0; f1=Xb@c1; f2=Yb@c2; df0=dXb@c0; df1=dXb@c1; df2=dYb@c2
        for ch in chis:
            sg=w*math.tan(ch); D=w*w+sg*sg
            rho=w*w/D; nu=w*sg/D; drho=-2*sg*w*w/D**2; dnu=w*(w*w-sg*sg)/D**2
            P=b['p0']+sg*b['p1']+sg**2*b['p2']
            Fv=sg*a+f0+rho*f1+nu*f2
            E=b['sq0']-df0-rho*df1-nu*df2-_cvxpy().multiply(b['d'],a+drho*f1+dnu*f2)
            cons.append(E-_cvxpy().multiply(s/P,_cvxpy().square(Fv))>=m*s)
        cons.append(b['sq0']-df0-_cvxpy().multiply(b['d'],a)-_cvxpy().multiply(s/b['p2'],_cvxpy().square(a))>=m*s)
    prob=_cvxpy().Problem(_cvxpy().Maximize(m),cons)
    prob.solve(solver=_cvxpy().CLARABEL)
    return dict(m=m.value,dl=dl.value,A0=c0.value,A1=c1.value,A2=c2.value)

kappa0=3*math.sqrt(2)/35
def bases(K,x,y):
    Xb=np.array([x*y**k for k in range(K+1)]).T
    dXb=np.array([-y**(k+1)+(k*(1-y**2)*y**(k-1) if k>0 else 0*y) for k in range(K+1)]).T
    Yb=np.array([y**k for k in range(K+1)]).T
    dYb=np.array([(k*y**(k-1)*x if k>0 else 0*y) for k in range(K+1)]).T
    return Xb,dXb,Yb,dYb
def solveG(svals, D=2, w=2.0, K=3, Nt=128, Nc=25, wt=None):
    ts=np.linspace(0,2*np.pi,Nt,endpoint=False); x=np.cos(ts); y=np.sin(ts)
    Xb,dXb,Yb,dYb=bases(K,x,y)
    C0=_cvxpy().Variable((D+1,K+1)); C1=_cvxpy().Variable((D+1,K+1)); C2=_cvxpy().Variable((D+1,K+1)); DL=_cvxpy().Variable(D+1); m=_cvxpy().Variable()
    cons=[C0[0,0]==kappa0, C0[0,1:]==0, C1[0,:]==0, C2[0,:]==0]
    chis=np.linspace(-np.pi/2,np.pi/2,Nc)[1:-1]
    sgs=w*np.tan(chis)
    for s in svals:
        pw=np.array([s**j for j in range(D+1)])
        c0=pw@C0; c1=pw@C1; c2=pw@C2; dl=pw@DL
        b=base(s,x,y)
        a=dl+b['acore']
        f0=Xb@c0; f1=Xb@c1; f2=Yb@c2; df0=dXb@c0; df1=dXb@c1; df2=dYb@c2
        for sg in sgs:
            Dn=w*w+sg*sg
            rho=w*w/Dn; nu=w*sg/Dn; drho=-2*sg*w*w/Dn**2; dnu=w*(w*w-sg*sg)/Dn**2
            P=b['p0']+sg*b['p1']+sg**2*b['p2']
            Fv=sg*a+f0+rho*f1+nu*f2
            E=b['sq0']-df0-rho*df1-nu*df2-_cvxpy().multiply(b['d'],a+drho*f1+dnu*f2)
            cons.append(E-_cvxpy().multiply(s/P,_cvxpy().square(Fv))>=m*s)
        cons.append(b['sq0']-df0-_cvxpy().multiply(b['d'],a)-_cvxpy().multiply(s/b['p2'],_cvxpy().square(a))>=m*s)
    prob=_cvxpy().Problem(_cvxpy().Maximize(m),cons)
    prob.solve(solver=_cvxpy().CLARABEL)
    return dict(m=float(m.value),w=w,K=K,D=D,DL=DL.value.tolist(),C0=C0.value.tolist(),C1=C1.value.tolist(),C2=C2.value.tolist())

def solveR(svals, mstar, D=2, w=2.0, K=3, Nt=128, Nc=25):
    ts=np.linspace(0,2*np.pi,Nt,endpoint=False); x=np.cos(ts); y=np.sin(ts)
    Xb,dXb,Yb,dYb=bases(K,x,y)
    C0=_cvxpy().Variable((D+1,K+1)); C1=_cvxpy().Variable((D+1,K+1)); C2=_cvxpy().Variable((D+1,K+1)); DL=_cvxpy().Variable(D+1); m=_cvxpy().Variable()
    cons=[C0[0,0]==kappa0, C0[0,1:]==0, C1[0,:]==0, C2[0,:]==0]
    chis=np.linspace(-np.pi/2,np.pi/2,Nc)[1:-1]
    sgs=w*np.tan(chis)
    for s,ms in zip(svals,mstar):
        pw=np.array([s**j for j in range(D+1)])
        c0=pw@C0; c1=pw@C1; c2=pw@C2; dl=pw@DL
        b=base(s,x,y)
        a=dl+b['acore']
        f0=Xb@c0; f1=Xb@c1; f2=Yb@c2; df0=dXb@c0; df1=dXb@c1; df2=dYb@c2
        for sg in sgs:
            Dn=w*w+sg*sg
            rho=w*w/Dn; nu=w*sg/Dn; drho=-2*sg*w*w/Dn**2; dnu=w*(w*w-sg*sg)/Dn**2
            P=b['p0']+sg*b['p1']+sg**2*b['p2']
            Fv=sg*a+f0+rho*f1+nu*f2
            E=b['sq0']-df0-rho*df1-nu*df2-_cvxpy().multiply(b['d'],a+drho*f1+dnu*f2)
            cons.append(E-_cvxpy().multiply(s/P,_cvxpy().square(Fv))>=m*s*ms)
        cons.append(b['sq0']-df0-_cvxpy().multiply(b['d'],a)-_cvxpy().multiply(s/b['p2'],_cvxpy().square(a))>=m*s*ms)
    prob=_cvxpy().Problem(_cvxpy().Maximize(m),cons)
    prob.solve(solver=_cvxpy().CLARABEL)
    return dict(m=float(m.value),w=w,K=K,D=D,DL=DL.value.tolist(),C0=C0.value.tolist(),C1=C1.value.tolist(),C2=C2.value.tolist())

# ----------------------------------------------------------------------------------------
# 3. Exact integer mirror of SolovevBallooningDefs.lean
# ----------------------------------------------------------------------------------------
S=4294967296
def div0(a,b): return 0 if b==0 else a//b
class Bl:
    __slots__=('m','r','ok')
    def __init__(s,m,r,ok): s.m=m; s.r=r; s.ok=ok
    def __repr__(s): return f"Bl({s.m},{s.r},{s.ok})"
def ofInt(n): return Bl(n*S,0,True)
def ofFrac(p,q):
    if q>0: return Bl((p*S)//q, 1, True)
    # q <= 0: invalid ball (Lean: Int.ediv/emod semantics; value irrelevant)
    return Bl(0,1,False)
ZERO=Bl(0,0,True)
def add(a,b): return Bl(a.m+b.m,a.r+b.r,a.ok and b.ok)
def neg(a): return Bl(-a.m,a.r,a.ok)
def sub(a,b): return Bl(a.m-b.m,a.r+b.r,a.ok and b.ok)
def dbl(a): return Bl(a.m+a.m,a.r+a.r,a.ok)
def mul(a,b): return Bl((a.m*b.m)//S,(abs(a.m)*b.r+a.r*abs(b.m)+a.r*b.r)//S+2,a.ok and b.ok)
def sq(a): return Bl((a.m*a.m)//S,((abs(a.m)+abs(a.m))*a.r+a.r*a.r)//S+2,a.ok)
def lo(a): return a.m-a.r
def hi(a): return a.m+a.r
def mag(a): return abs(a.m)+a.r
def ofLoHi(l,h,ok): return Bl((l+h)//2,abs(h-l)//2+2,ok)
S2=18446744073709551616
def inv(a):
    # Int.ediv by possibly nonpositive values: Lean ediv semantics
    def ediv(x,y):
        if y==0: return 0
        if y>0: return x//y
        return -(x//(-y))  # Int.ediv x (-y) = -(x ediv y) for x>=0... only x=S2>0 here
    return ofLoHi(ediv(S2,hi(a)),ediv(S2,lo(a))+1,a.ok and lo(a)>0)
def isqrtAux(k,n,g):
    while k>0:
        k-=1
        ng=div0(g+div0(n,g),2)
        if ng<g: g=ng
        else: return g
    return g
def isqrt(n): return isqrtAux(64,n,n//4294967296+4294967296)
def toNat(x): return x if x>0 else 0
def bsqrt(a):
    L=lo(a)*S; H=hi(a)*S
    ql=isqrt(toNat(L)); qh=isqrt(toNat(H))+1
    return ofLoHi(ql if ql*ql<=L else 0, qh, a.ok and lo(a)>=0 and H<=qh*qh)
# ---------------- trees (mirror) ----------------
def c(p,q=1): return ('c',p,q)
def v(i): return ('v',i)
def tadd(a,b): return ('add',a,b)
def tmul(a,b): return ('mul',a,b)
def tneg(a): return ('neg',a)
def tsq(a): return ('sq',a)
def tsub(a,b): return tadd(a,tneg(b))
tX,tY,tR,tr,tiR,tiB,tS,tT,tK=[v(i) for i in range(9)]
tzh=tmul(tr,tmul(tX,tiR))
tWh=tadd(tmul(tS,tsq(tzh)),tmul(c(2),tY))
tBR=tneg(tmul(c(7,400),tmul(tS,tmul(tR,tzh))))
tBP=tmul(c(50),tiR)
tBZ=tmul(c(7,400),tmul(tS,tWh))
tgsR=tmul(c(1,2),tmul(tR,tWh))
tgsZ=tmul(c(1,2),tmul(tmul(tR,tX),tr))
tgtR=tmul(tmul(tX,tadd(c(100),tmul(tS,tY))),tiR)
tgtZ=tneg(tmul(c(1,2),tmul(tmul(tR,tY),tr)))
tiR3=tmul(tiR,tsq(tiR))
trate=tmul(c(10000,7),tr)
tkR=tmul(tmul(trate,tiR3),tgtR)
tkP=tmul(tS,tiR)
tkZ=tmul(tmul(trate,tiR3),tgtZ)
tell=tmul(c(200,7),tmul(tr,tiR))
tGR=tneg(tadd(tmul(c(49,80000),tmul(tS,tmul(tR,tY))),tmul(c(2500),tiR3)))
tGZ=tmul(c(49,80000),tmul(tmul(tS,tzh),tsub(tmul(tS,tWh),tsq(tR))))
tB2=tadd(tadd(tsq(tBR),tsq(tBP)),tsq(tBZ))
tden=tmul(c(7,400),tmul(tmul(tr,tR),tiB))
tp0=tmul(tadd(tadd(tsq(tkR),tsq(tkP)),tsq(tkZ)),tden)
tp1=tmul(tmul(c(-2),tadd(tmul(tkR,tgsR),tmul(tkZ,tgsZ))),tden)
tp2=tmul(tadd(tsq(tgsR),tsq(tgsZ)),tden)
def tcross(bR,bP,bZ,gR,gZ): return tadd(tmul(tsub(tmul(tBP,bZ),tmul(tBZ,bP)),gR),tmul(tsub(tmul(tBR,bP),tmul(tBP,bR)),gZ))
tsq0=tneg(tmul(tmul(c(21,200),tell),tmul(tcross(tkR,tkP,tkZ,tGR,tGZ),tsq(tiB))))
tq1=tmul(tmul(c(21,200),tell),tmul(tmul(tBP,tsub(tmul(tgsZ,tGR),tmul(tgsR,tGZ))),tsq(tiB)))
td=tmul(tmul(tmul(c(3),trate),tmul(tY,tS)),tmul(tiR,tsq(tsq(tiR))))
tbeta=tsub(tmul(c(49,160000),tmul(tS,tadd(tmul(c(2),tsq(tX)),tsq(tWh)))),tmul(c(50),tmul(tY,tsq(tiR))))
def ptree(l,y):
    if not l: return c(0)
    return tadd(l[0],tmul(y,ptree(l[1:],y)))
def dvT(i): return tneg(tY) if i==0 else (tX if i==1 else c(0,1))
def diff(dv,e):
    k=e[0]
    if k=='c': return c(0,1)
    if k=='v': return dv(e[1])
    if k=='add': return tadd(diff(dv,e[1]),diff(dv,e[2]))
    if k=='mul': return tadd(tmul(diff(dv,e[1]),e[2]),tmul(e[1],diff(dv,e[2])))
    if k=='neg': return tneg(diff(dv,e[1]))
    if k=='sq': return tmul(c(2,1),tmul(e[1],diff(dv,e[1])))
class Data:
    def __init__(s,dl,A0,A1,A2): s.dl=dl; s.A0=A0; s.A1=A1; s.A2=A2
def baseT(D):
    tf0=tmul(tX,ptree(D.A0,tY)); tf1=tmul(tX,ptree(D.A1,tY)); tf2=ptree(D.A2,tY)
    return [tp0,tp1,tp2,tsub(tsq0,diff(dvT,tf0)),diff(dvT,tf1),diff(dvT,tf2),td,
            tadd(D.dl,tmul(c(3,1),tmul(tiB,tbeta))),tf0,tf1,tf2,tS]
tin=[tsub(tmul(c(16),tsub(tsub(v(3),v(4)),tmul(v(6),v(7)))),tmul(c(8),tmul(v(6),v(10)))),
     tadd(tneg(tmul(c(8),v(5))),tmul(c(8),tmul(v(6),v(9)))),
     tadd(tmul(c(4),tsub(tmul(c(2),tsub(v(3),tmul(v(6),v(7)))),v(4))),tmul(c(2),tmul(v(6),v(10)))),
     tneg(tmul(c(2),v(5))), tsub(v(3),tmul(v(6),v(7)))]
tgg=[tmul(c(4),tadd(v(8),v(9))), tadd(tmul(c(4),v(7)),tmul(c(2),v(10))), v(8), v(7)]
V0,V1,V2,V11=v(0),v(1),v(2),v(11)
etree=[
 tsub(tmul(V0,tin[0]),tmul(V11,tsq(tgg[0]))),
 tsub(tadd(tmul(V0,tin[1]),tmul(V1,tin[0])),tmul(V11,tmul(c(2),tmul(tgg[0],tgg[1])))),
 tsub(tadd(tadd(tmul(V0,tin[2]),tmul(V1,tin[1])),tmul(V2,tin[0])),tmul(V11,tadd(tmul(c(2),tmul(tgg[0],tgg[2])),tsq(tgg[1])))),
 tsub(tadd(tadd(tmul(V0,tin[3]),tmul(V1,tin[2])),tmul(V2,tin[1])),tmul(V11,tmul(c(2),tadd(tmul(tgg[0],tgg[3]),tmul(tgg[1],tgg[2]))))),
 tsub(tadd(tadd(tmul(V0,tin[4]),tmul(V1,tin[3])),tmul(V2,tin[2])),tmul(V11,tadd(tmul(c(2),tmul(tgg[1],tgg[3])),tsq(tgg[2])))),
 tsub(tadd(tmul(V1,tin[4]),tmul(V2,tin[3])),tmul(V11,tmul(c(2),tmul(tgg[2],tgg[3])))),
 tsub(tmul(V2,tin[4]),tmul(V11,tsq(tgg[3])))]
def Dt0(i):
    return {0:tneg(tmul(tK,tY)),1:tmul(tK,tX),2:tmul(tmul(tS,tK),tmul(tX,tiR)),
            4:tneg(tmul(tmul(tmul(tS,tK),tmul(tX,tiR)),tsq(tiR))),7:c(1,1),8:tneg(tmul(tT,tsq(tK)))}.get(i,c(0,1))
_dtB2=diff(Dt0,tB2)
def Dt(i): return tneg(tmul(_dtB2,tsq(tiB))) if i==5 else Dt0(i)
def Ds0(i): return {2:tmul(tY,tiR),4:tneg(tmul(tY,tiR3)),6:c(1,1)}.get(i,c(0,1))
_dsB2=diff(Ds0,tB2)
def Ds(i): return tneg(tmul(_dsB2,tsq(tiB))) if i==5 else Ds0(i)
DTL=[Dt(i) for i in range(9)]; DSL=[Ds(i) for i in range(9)]
# ---------------- evaluation ----------------
def ieval(e,I,cache):
    key=id(e)
    if key in cache: return cache[key]
    k=e[0]
    if k=='c': r=ofFrac(e[1],e[2])
    elif k=='v': r=I(e[1])
    elif k=='add': r=add(ieval(e[1],I,cache),ieval(e[2],I,cache))
    elif k=='mul': r=mul(ieval(e[1],I,cache),ieval(e[2],I,cache))
    elif k=='neg': r=neg(ieval(e[1],I,cache))
    else: r=sq(ieval(e[1],I,cache))
    cache[key]=r; return r
def idual(e,I,I1,cache):
    key=id(e)
    if key in cache: return cache[key]
    k=e[0]
    if k=='c': r=(ofFrac(e[1],e[2]),ZERO)
    elif k=='v': r=(I(e[1]),I1(e[1]))
    elif k=='add':
        A=idual(e[1],I,I1,cache); B=idual(e[2],I,I1,cache); r=(add(A[0],B[0]),add(A[1],B[1]))
    elif k=='mul':
        A=idual(e[1],I,I1,cache); B=idual(e[2],I,I1,cache); r=(mul(A[0],B[0]),add(mul(A[1],B[0]),mul(A[0],B[1])))
    elif k=='neg':
        A=idual(e[1],I,I1,cache); r=(neg(A[0]),neg(A[1]))
    else:
        A=idual(e[1],I,I1,cache); r=(sq(A[0]),dbl(mul(A[0],A[1])))
    cache[key]=r; return r
def ihd(e,I,I1,I2,cache):
    key=id(e)
    if key in cache: return cache[key]
    k=e[0]
    if k=='c': r=(ofFrac(e[1],e[2]),ZERO,ZERO)
    elif k=='v': r=(I(e[1]),I1(e[1]),I2(e[1]))
    elif k=='add':
        A=ihd(e[1],I,I1,I2,cache); B=ihd(e[2],I,I1,I2,cache); r=(add(A[0],B[0]),add(A[1],B[1]),add(A[2],B[2]))
    elif k=='mul':
        A=ihd(e[1],I,I1,I2,cache); B=ihd(e[2],I,I1,I2,cache)
        r=(mul(A[0],B[0]),add(mul(A[1],B[0]),mul(A[0],B[1])),add(add(mul(A[2],B[0]),dbl(mul(A[1],B[1]))),mul(A[0],B[2])))
    elif k=='neg':
        A=ihd(e[1],I,I1,I2,cache); r=(neg(A[0]),neg(A[1]),neg(A[2]))
    else:
        A=ihd(e[1],I,I1,I2,cache); r=(sq(A[0]),dbl(mul(A[0],A[1])),dbl(add(sq(A[1]),mul(A[0],A[2]))))
    cache[key]=r; return r
def envI(lst):
    return lambda i: lst[i] if i<9 else ZERO
sqrt2B=bsqrt(ofInt(2))
NT=4096; NS=1024
def ivHull(p0,p1,q): return ofLoHi(lo(ofFrac(p0,q)),hi(ofFrac(p1,q)),q>0 and p0<=p1)
def kapB(T): return mul(ofInt(2),inv(add(ofInt(1),sq(T))))
def RB(T,Sb): return bsqrt(add(ofInt(100),mul(ofInt(2),mul(Sb,mul(kapB(T),T)))))
def boxVars(T,Sb):
    K=kapB(T); R=RB(T,Sb)
    l=[sub(K,ofInt(1)),mul(K,T),R,sqrt2B,inv(R),ZERO,Sb,T,K]
    B2=ieval(tB2,envI(l),{})
    l[5]=inv(B2)
    return l
def pointVars(t,n): return boxVars(ofFrac(t,NT),ofFrac(n,NS))
def baseVals(bt,V):
    cache={}; I=envI(V)
    return [ieval(e,I,cache) for e in bt]
def lk(l,j): return l[j] if j<len(l) else ZERO
def eCorner(bt,t,n):
    b=baseVals(bt,pointVars(t,n)); cache={}
    return [ieval(etree[k],lambda j: lk(b,j),cache) for k in range(7)]
def e2(bt,DL,V):
    I=envI(V); c1={}
    V1=[ieval(DL[i],I,c1) for i in range(9)]
    c2={}
    V2=[idual(DL[i],I,lambda j: lk(V1,j),c2)[1] for i in range(9)]
    c3={}
    B=[ihd(e,I,lambda j: lk(V1,j),lambda j: lk(V2,j),c3) for e in bt]
    c4={}
    g=lambda j,p: B[j][p] if j<len(B) else ZERO
    return [ihd(etree[k],lambda j: g(j,0),lambda j: g(j,1),lambda j: g(j,2),c4)[2] for k in range(7)]
def mulOnePlus(p):
    if not p: return []
    out=[p[0]]; b=p[0]
    for a in p[1:]:
        out.append(a+b); b=a
    out.append(b)
    return out
def allPos(p): return len(p)>0 and all(a>0 for a in p)
def polyaOK(M,p):
    for _ in range(M+1):
        if allPos(p): return True
        p=mulOnePlus(p)
    return False
POW2=[1,2,4,8,16,32,64]
def cornerOK(bt,t,n,R):
    E=eCorner(bt,t,n)
    if not all(E[k].ok for k in range(7)): return False
    if not polyaOK(24,[(lo(E[k])-R[k])*POW2[k] for k in range(7)]): return False
    return polyaOK(24,[((lo(E[k])-R[k]) if k%2==0 else (-hi(E[k])-R[k]))*POW2[k] for k in range(7)])
def reserve(Mt,Ms,dt,ds,axis):
    return [ (mag(Mt[k])*toNat(dt*dt)*(NS*NS) + mag(Ms[k])*toNat(ds*ds)*((4*NT*NT) if axis else NT*NT))//(8*NT*NT*NS*NS)+1 for k in range(7)]
def boxparts(bt,t0,t1,n0,n1):
    V=boxVars(ivHull(t0,t1,NT),ivHull(n0,n1,NS))
    return e2(bt,DTL,V), e2(bt,DSL,V)
def boxOK(bt,t0,t1,n0,n1,parts=None):
    if not (t0<t1 and 0<=n0<n1<=25*NS): return False
    Mt,Ms=parts if parts else boxparts(bt,t0,t1,n0,n1)
    if not all(Mt[k].ok and Ms[k].ok for k in range(7)): return False
    R=reserve(Mt,Ms,t1-t0,n1-n0,False)
    return all(cornerOK(bt,t,n,R) for (t,n) in [(t0,n0),(t1,n0),(t0,n1),(t1,n1)])
def axisOK(bt,t0,t1,n1,parts=None):
    if not (t0<t1 and 0<n1<=25*NS): return False
    Mt,Ms=parts if parts else boxparts(bt,t0,t1,0,n1)
    if not all(Mt[k].ok and Ms[k].ok for k in range(7)): return False
    R=reserve(Mt,Ms,t1-t0,n1,True)
    return all(cornerOK(bt,t,n1,R) for t in [t0,t1])
# ---------------- data ----------------
def frac(x,bits=24):
    f=Fraction(round(x*2**bits),2**bits); return (f.numerator,f.denominator)
def make_data(r,bits=24):
    """Data trees exactly as emitted to Lean (see lean_data)."""
    D=r['D']; K=r['K']
    def horner(cs,const=None):
        fr=[frac(x,bits) for x in cs]
        inner=c(*fr[-1])
        for f in reversed(fr[1:-1]): inner=tadd(c(*f),tmul(tS,inner))
        if const is None: return tmul(tS,inner)
        return tadd(const,tmul(tS,inner))
    def col(C,k,const=None):
        return horner([C[j][k] for j in range(D+1)],const)
    A0=[col(r['C0'],0,tmul(c(3,35),tr))]+[col(r['C0'],k) for k in range(1,K+1)]
    A1=[col(r['C1'],k) for k in range(K+1)]
    A2=[col(r['C2'],k) for k in range(K+1)]
    fr=[frac(x,bits) for x in r['DL']]
    dl=c(*fr[-1])
    for f in reversed(fr[:-1]): dl=tadd(c(*f),tmul(tS,dl))
    return Data(dl,A0,A1,A2)
def lean_tm(e):
    k=e[0]
    if k=='c': return f"(c ({e[1]}) {e[2]})"
    if k=='v': return {0:'tX',1:'tY',2:'tR',3:'tr',4:'tiR',5:'tiB',6:'tS'}[e[1]]
    if k=='add': return f"(add {lean_tm(e[1])} {lean_tm(e[2])})"
    if k=='mul': return f"(mul {lean_tm(e[1])} {lean_tm(e[2])})"
    if k=='neg': return f"(neg {lean_tm(e[1])})"
    return f"(sq {lean_tm(e[1])})"
def lean_data(D,name):
    L=lambda l: "[" + ",\n    ".join(lean_tm(e) for e in l) + "]"
    return f"@[expose] def {name} : Data where\n  dl := {lean_tm(D.dl)}\n  A0 := {L(D.A0)}\n  A1 := {L(D.A1)}\n  A2 := {L(D.A2)}\n"

# ----------------------------------------------------------------------------------------
# 4. Planner
# ----------------------------------------------------------------------------------------
def parts_weights(Mt,Ms,t0,t1,n0,n1):
    a=sum(mag(Mt[k]) for k in range(7))*(t1-t0)**2*NS*NS
    b=sum(mag(Ms[k]) for k in range(7))*(n1-n0)**2*(4 if n0==0 else 1)*NT*NT
    return a,b
stats={'tries':0}
def plan(bt,t0,t1,n0,n1,d):
    stats['tries']+=1
    P=boxparts(bt,t0,t1,n0,n1)
    ok = axisOK(bt,t0,t1,n1,P) if n0==0 else boxOK(bt,t0,t1,n0,n1,P)
    if ok: return ["A" if n0==0 else "L"]
    if d==0: return None
    a,b=parts_weights(P[0],P[1],t0,t1,n0,n1)
    if (a>=b and t1-t0>=2) or n1-n0<2:
        tm=(t0+t1)//2
        p=plan(bt,t0,tm,n0,n1,d-1)
        if p is None: return None
        q=plan(bt,tm,t1,n0,n1,d-1)
        if q is None: return None
        return [f"T{tm}"]+p+q
    nm=(n0+n1)//2
    p=plan(bt,t0,t1,n0,nm,d-1)
    if p is None: return None
    q=plan(bt,t0,t1,nm,n1,d-1)
    if q is None: return None
    return [f"S{nm}"]+p+q
def split_list(tok,pts,f,lo_,hi_):
    if not pts: return f(lo_,hi_)
    p=pts[0]
    a=f(lo_,p)
    if a is None: return None
    b=split_list(tok,pts[1:],f,p,hi_)
    if b is None: return None
    return [f"{tok}{p}"]+a+b
def full_plan(bt,n_lo,n_hi,spts,tpts,depth=14):
    return split_list("S",[p for p in spts if n_lo<p<n_hi],
        lambda a,b: split_list("T",tpts,lambda t0,t1: plan(bt,t0,t1,a,b,depth),-NT,NT), n_lo,n_hi)

def lookahead_plan(bt, depth=16):
    """Planner with bounded lookahead: at a failing box compare the `T` and `S` splits by the
    greedy leaf count of the children and keep the cheaper one."""
    @lru_cache(maxsize=None)
    def ok(t0,t1,n0,n1):
        P=boxparts(bt,t0,t1,n0,n1)
        return axisOK(bt,t0,t1,n1,P) if n0==0 else boxOK(bt,t0,t1,n0,n1,P)
    @lru_cache(maxsize=None)
    def greedy(t0,t1,n0,n1,d):
        if ok(t0,t1,n0,n1): return 1
        if d==0: return 10**6
        P=boxparts(bt,t0,t1,n0,n1)
        a,b=parts_weights(P[0],P[1],t0,t1,n0,n1)
        if (a>=b and t1-t0>=2) or n1-n0<2:
            tm=(t0+t1)//2; return greedy(t0,tm,n0,n1,d-1)+greedy(tm,t1,n0,n1,d-1)
        nm=(n0+n1)//2; return greedy(t0,t1,n0,nm,d-1)+greedy(t0,t1,nm,n1,d-1)
    def rec(t0,t1,n0,n1,d):
        if ok(t0,t1,n0,n1): return ["A" if n0==0 else "L"]
        if d==0: return None
        best=None
        if t1-t0>=2:
            tm=(t0+t1)//2
            best=(greedy(t0,tm,n0,n1,d-1)+greedy(tm,t1,n0,n1,d-1),'T',tm)
        if n1-n0>=2:
            nm=(n0+n1)//2
            cst=greedy(t0,t1,n0,nm,d-1)+greedy(t0,t1,nm,n1,d-1)
            if best is None or cst<best[0]: best=(cst,'S',nm)
        _,k,m=best
        if k=='T':
            p=rec(t0,m,n0,n1,d-1); q=rec(m,t1,n0,n1,d-1)
            return None if p is None or q is None else [f"T{m}"]+p+q
        p=rec(t0,t1,n0,m,d-1); q=rec(t0,t1,m,n1,d-1)
        return None if p is None or q is None else [f"S{m}"]+p+q
    spts=[1024,2048,4096,6144,8192,12288,16384,20480]
    tpts=[-3072,-2048,-1024,0,1024,2048,3072]
    return split_list("S",spts,lambda a,b: split_list("T",tpts,
        lambda t0,t1: rec(t0,t1,a,b,depth),-NT,NT),0,25600)

# ----------------------------------------------------------------------------------------
# 5. Emitting the Lean modules
# ----------------------------------------------------------------------------------------
HDR='''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module
'''
def parse(tokens,i,t0,t1,n0,n1):
    tok=tokens[i]
    if tok in ("L","A"): return {'k':tok,'b':(t0,t1,n0,n1),'n':1}, i+1
    v=int(tok[1:])
    if tok[0]=='T':
        a,i=parse(tokens,i+1,t0,v,n0,n1); b,i=parse(tokens,i,v,t1,n0,n1)
    else:
        a,i=parse(tokens,i+1,t0,t1,n0,v); b,i=parse(tokens,i,t0,t1,v,n1)
    return {'k':tok,'b':(t0,t1,n0,n1),'n':a['n']+b['n'],'c':(a,b)}, i
def toks(node):
    if node['k'] in ("L","A"): return [node['k']]
    return [node['k']]+toks(node['c'][0])+toks(node['c'][1])
def chunk(node,CH,chunks):
    if node['n']<=CH:
        name=f"cov{len(chunks)}"
        chunks.append((name,node))
        return ["@"+name]
    return [node['k']]+chunk(node['c'][0],CH,chunks)+chunk(node['c'][1],CH,chunks)
def emit(datafile, K, CH, outdir, planfile=None):
    r=json.load(open(datafile)); D=make_data(r); bt=baseT(D)
    if planfile:
        p=open(planfile).read().split()
    else:
        spts=[1024,2048,4096,6144,8192,12288,16384,20480]
        p=full_plan(bt,0,25600,spts,[-3072,-2048,-1024,0,1024,2048,3072],16)
    assert p is not None
    tree,i=parse(p,0,-NT,NT,0,25600); assert i==len(p)
    chunks=[]; asm=chunk(tree,CH,chunks)
    # pack chunks into K modules greedily in order
    total=tree['n']; target=total/K
    mods=[[] for _ in range(K)]; m=0; acc=0
    for name,node in chunks:
        if acc>=target*(m+1) and m<K-1: m+=1
        mods[m].append((name,node)); acc+=node['n']
    mods=[x for x in mods if x]
    open(f"{outdir}/SolovevBallooningData.lean","w").write(HDR+'''
public import PlasmaLean.Design.SolovevBallooningDefs

/-!
# Ballooning certificate data for the reactor Solov'ev equilibrium

The Riccati certificate data `gdata` (one data set for ALL surfaces `0 < s ≤ 25`: the
coefficients are quadratic polynomials in `s`), proposed by the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py` (convex SOCP, coefficients rounded to multiples of
`2⁻²⁴`). The `s⁰` coefficients are fixed exactly so that the certificate degenerates correctly
on the magnetic axis (`f₀ = (3√2/35) x + O(s)`, `f₁, f₂ = O(s)`).
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

open Tm

/-- **The certificate data** (untrusted oracle output, checked by the kernel). -/
'''+lean_data(D,'gdata')+'''
end PlasmaLean.Design.SolovevBallooning
''')
    def boxR(node):
        t0,t1,n0,n1=node['b']
        Mt,Ms=boxparts(bt,t0,t1,n0,n1)
        axis=(node['k']=='A')
        return reserve(Mt,Ms,t1-t0,n1-n0,axis)
    def corners(node):
        t0,t1,n0,n1=node['b']
        if node['k']=='A': return [(t0,n1),(t1,n1)]
        return [(t0,n0),(t1,n0),(t0,n1),(t1,n1)]
    names=[]
    for j,mod in enumerate(mods):
        mname=f"SolovevBallooningCells{j:02d}"
        names.append(mname)
        body=[]
        # shared corner lemmas (per module)
        nodes={}   # (t,n) -> list of lemmas [R]
        assign={}  # (name, corner index) -> lemma name
        lemmas=[]  # (lname, t, n, R)
        boxinfo=[]
        for name,node in mod:
            assert node['n']==1
            boxinfo.append((name,node,boxR(node)))
        # process boxes in order of decreasing reserve size for better grouping
        for name,node,R in boxinfo:
            for ci,(t,n) in enumerate(corners(node)):
                lst=nodes.setdefault((t,n),[])
                done=False
                for L in lst:
                    Rm=[max(a,b) for a,b in zip(L['R'],R)]
                    if Rm==L['R'] or cornerOK(bt,t,n,Rm):
                        L['R']=Rm; assign[(name,ci)]=L['name']; done=True; break
                if not done:
                    assert cornerOK(bt,t,n,R), (name,t,n)
                    lname=f"cn{j:02d}_{len(lemmas)}"
                    L={'name':lname,'t':t,'n':n,'R':list(R)}
                    lst.append(L); lemmas.append(L); assign[(name,ci)]=lname
        for L in lemmas:
            Rs='['+', '.join(str(x) for x in L['R'])+']'
            l2=f"    {Rs} = true := by"
            if len(l2)>100:
                l2=f"    {Rs} =\n      true := by"
            body.append(f'''/-- Kernel-checked corner test at `({L['t']}/NT, {L['n']}/NS)`. -/
theorem {L['name']} : cornerOK gdata ({L['t']}) ({L['n']})
{l2}
  bl_cert
''')
        for name,node,R in boxinfo:
            t0,t1,n0,n1=node['b']
            cs=[assign[(name,ci)] for ci in range(len(corners(node)))]
            tok=("Z:" if node['k']=='A' else "Q:")+",".join(cs)
            body.append(f'''/-- Kernel-checked box `[{t0}, {t1}]/NT × [{n0}, {n1}]/NS`. -/
theorem {name} : Cover gdata ({t0}) ({t1}) ({n0}) ({n1}) := by
  ballooning_cover "{tok}"
''')
        print("module",j,"boxes",len(boxinfo),"corner lemmas",len(lemmas))
        leaves=sum(nd['n'] for _,nd in mod)
        open(f"{outdir}/{mname}.lean","w").write(HDR+f'''
public import PlasmaLean.Design.SolovevBallooningEvalCert

/-!
# Ballooning certificate: kernel-checked cells, part {j}

{leaves} boxes of the `(τ, s)` cover (plan from the UNTRUSTED oracle
`scripts/solovev_ballooning_oracle.py`). The corner tests `cornerOK` are shared between
neighbouring boxes (lemmas `cn…`, evaluation certificates `bl_cert`: one kernel leaf per ball
operation, ≈ 10⁴ nodes per corner); each box lemma `cov…` checks the second-derivative bounds
`hessOK` of its box (by kernel evaluation when the declaration is checked) and refers to its
corner lemmas through `Cover.leaf2`/`Cover.axis2`.
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

set_option maxRecDepth 100000

'''+"\n".join(body)+'''
end PlasmaLean.Design.SolovevBallooning
''')
    open(f"{outdir}/assembly.txt","w").write(" ".join(asm))
    json.dump({'modules':names,'leaves':total,'chunks':len(chunks)},open(f"{outdir}/gen.json","w"))
    print("leaves",total,"chunks",len(chunks),"modules",len(mods),[sum(nd['n'] for _,nd in m) for m in mods])

def install(gen):
    repo='/Users/gadgil/code/PlasmaLean/PlasmaLean/Design'
    for f in glob.glob(repo+'/SolovevBallooningCells*.lean'): os.remove(f)
    for f in glob.glob(gen+'/SolovevBallooningCells*.lean')+[gen+'/SolovevBallooningData.lean']:
        shutil.copy(f, repo)
    mods=json.load(open(gen+'/gen.json'))['modules']
    p=repo+'/SolovevBallooning.lean'
    s=open(p).read()
    s=re.sub(r'(public import PlasmaLean\.Design\.SolovevBallooningCells\d+\n)+',
             ''.join(f'public import PlasmaLean.Design.{m}\n' for m in mods), s)
    i=s.index('  ballooning_cover "S'); j=s.index('"\n',i+20)
    asm=open(gen+'/assembly.txt').read().strip()
    words=asm.split(' '); lines=[]; cur=''; limit=76
    for w in words:
        if len(cur)+len(w)+3>limit: lines.append(cur); cur=w; limit=92
        else: cur=(cur+' '+w) if cur else w
    lines.append(cur)
    s=s[:i]+'  ballooning_cover "'+(' \\\n    '.join(lines))+'"'+s[j+1:]
    n=json.load(open(gen+'/gen.json'))['leaves']
    s=re.sub(r'is cut into \d+ boxes', f'is cut into {n} boxes', s)
    s=re.sub(r'assembled from \d+ kernel-checked box lemmas in the \d+ parallel\n  modules `SolovevBallooningCells00` … `\d+`', f'assembled from {n} kernel-checked box lemmas in the {len(mods)} parallel\n  modules `SolovevBallooningCells00` … `{len(mods)-1:02d}`', s)
    s=re.sub(r'assembled from the \d+ kernel-checked\nboxes', f'assembled from the {n} kernel-checked\nboxes', s)
    open(p,'w').write(s)
    print("installed",len(mods),"modules,",n,"boxes")

# ----------------------------------------------------------------------------------------
def main():
    cmd=sys.argv[1]
    if cmd=='data':
        sv=[0.05,0.5,1,2,3,4,6,8,10,12,14,16,18,20,22,24,25]
        ms=[solve([s],K=3,Nt=128,Nc=25)['m'] for s in sv]
        r=solveR(sv,ms,D=2,K=3)
        print("relative margin",r['m'])
        json.dump(r,open(sys.argv[2],'w'))
    elif cmd=='plan':
        r=json.load(open(sys.argv[2])); bt=baseT(make_data(r))
        p=lookahead_plan(bt)
        assert p is not None, "planning failed"
        print("boxes",sum(1 for x in p if x in ("L","A")))
        open(sys.argv[3],'w').write(" ".join(p))
    elif cmd=='emit':
        K=int(sys.argv[5]) if len(sys.argv)>5 else 16
        os.makedirs(sys.argv[4],exist_ok=True)
        emit(sys.argv[2],K,1,sys.argv[4],sys.argv[3])
    elif cmd=='install':
        install(sys.argv[2])
    else:
        print(__doc__)

if __name__=="__main__":
    main()
