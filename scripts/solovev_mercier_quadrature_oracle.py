"""UNTRUSTED oracle for PlasmaLean/Design/SolovevMercierQuadrature.lean.

Exact Python mirror (integer fixed-point arithmetic, scale 2^32, outward rounding, checked
integer square roots) of the Lean checker `cellCheck N e0 e1`, which encloses for every
eps in [e0, e1] the normalized Mercier integrals of the reactor Solov'ev equilibrium
(Pn, Qn, S3n, S5n, IPhi; eps = s/50, flux surface psiT = s^2) by validated quadrature in
the rational parameter tau (y = 2 tau/(1+tau^2) = sin t) and tests
    Qn * IPhi < 3 * (3 Pn S5n - Qn S3n).
This script only PROPOSES the eps-cells (greedy search); the Lean kernel re-evaluates every
accepted cell (`decide +kernel`) and `cellCheck_sound` proves what acceptance means.
Usage: python3 scripts/solovev_mercier_quadrature_oracle.py 32 1.03
(prints the cells and the certified margin rhs/lhs of each).
"""
from fractions import Fraction as Fr
import sys
S=4294967296
def ediv(a,d):  # Lean Int ediv for d>0 (floor); d<0 not used
    assert d>0; return a//d
class I:
    __slots__=('lo','hi','ok')
    def __init__(s,lo,hi,ok): s.lo=lo; s.hi=hi; s.ok=ok
def ofInt(n): return I(n*S,n*S,True)
def ofFrac(p,q): return I(ediv(p*S,q), -ediv(-(p*S),q), q>0)
def add(a,b): return I(a.lo+b.lo,a.hi+b.hi,a.ok and b.ok)
def neg(a): return I(-a.hi,-a.lo,a.ok)
def sub(a,b): return I(a.lo-b.hi,a.hi-b.lo,a.ok and b.ok)
def mul(a,b):
    p=[a.lo*b.lo,a.lo*b.hi,a.hi*b.lo,a.hi*b.hi]
    return I(ediv(min(min(p[0],p[1]),min(p[2],p[3])),S), -ediv(-max(max(p[0],p[1]),max(p[2],p[3])),S), a.ok and b.ok)
def sq(a):
    if 0<=a.lo: return I(ediv(a.lo*a.lo,S),-ediv(-(a.hi*a.hi),S),a.ok)
    if a.hi<=0: return I(ediv(a.hi*a.hi,S),-ediv(-(a.lo*a.lo),S),a.ok)
    return I(0,-ediv(-max(a.lo*a.lo,a.hi*a.hi),S),a.ok)
def inv(a):
    if 0<a.lo: return I(ediv(S*S,a.hi) if a.hi>0 else None, -ediv(-(S*S),a.lo), a.ok)
    return I(0,0,False)
def ndiv(n,g): return n//g if g>0 else 0
def isqrtAux(k,n,g):
    while k>0:
        g2=(g+ndiv(n,g))//2
        if g2<g: g=g2; k-=1
        else: return g
    return g
def isqrt(n): return isqrtAux(64,n,n//4294967296+4294967296)
def toNat(z): return z if z>0 else 0
def sqrt(a):
    r=isqrt(toNat(a.lo*S))
    lo = r if r*r<=a.lo*S else 0
    s=isqrt(toNat(a.hi*S))+1
    return I(lo,s,a.ok and (a.hi*S<=s*s))
one=ofInt(1); two=ofInt(2); four=ofInt(4); k9=ofFrac(441,400); c36=ofInt(36)
def Ycell(N,i):
    return I(ediv(2*i*N*S,N*N+i*i), -ediv(-(2*(i+1)*N*S),N*N+(i+1)**2), True)
def Wcell(N,i):
    return I(ediv(4*N*N*S,N*N+(i+1)**2), -ediv(-(4*N*N*S),N*N+i*i), True)
def evp(E,Y): return sqrt(sub(one,sq(mul(E,Y))))
def evs(E,Y): return sqrt(add(two,mul(two,evp(E,Y))))
def evP(E,Y,W): return mul(mul(evs(E,Y),inv(evp(E,Y))),W)
def evQ(E,Y,W):
    p=evp(E,Y); q=inv(p)
    return mul(mul(mul(evs(E,Y),sub(two,p)),mul(sq(q),q)),W)
def evS3(E,Y,W):
    p=evp(E,Y); q=inv(p)
    return mul(mul(mul(mul(two,sq(Y)),add(two,p)),mul(inv(evs(E,Y)),mul(sq(q),q))),W)
def evS5(E,Y,W):
    p=evp(E,Y); q=inv(p)
    return mul(mul(mul(mul(two,sq(Y)),sub(add(four,mul(two,p)),sq(p))),mul(inv(evs(E,Y)),mul(mul(sq(q),q),sq(q)))),W)
def evPhi(R2,Sg,E,Y):
    v=add(one,mul(E,Y))
    G=add(sq(add(mul(two,Y),mul(E,add(one,sq(Y))))),mul(mul(two,sub(one,sq(Y))),sq(v)))
    return mul(add(mul(k9,R2),mul(mul(c36,sq(add(Y,Sg))),mul(v,inv(G)))),inv(mul(v,sqrt(v))))
def sumIv(c,N):
    acc=I(0,0,True)
    for i in range(N): acc=add(acc,c(i))
    return acc
def ofQlo(q): return ediv(q.numerator*S,q.denominator)
def ofQhi(q): return -ediv(-(q.numerator*S),q.denominator)
def cellCheck(N,e0,e1,verbose=False):
    E=I(ofQlo(e0),ofQhi(e1),True)
    sP=sumIv(lambda i: evP(E,Ycell(N,i),Wcell(N,i)),N)
    sQ=sumIv(lambda i: evQ(E,Ycell(N,i),Wcell(N,i)),N)
    s3=sumIv(lambda i: evS3(E,Ycell(N,i),Wcell(N,i)),N)
    s5=sumIv(lambda i: evS5(E,Ycell(N,i),Wcell(N,i)),N)
    if not (sQ.hi>0 and sQ.lo>0): return False,0
    R=I(ediv(sP.lo*S,sQ.hi), -ediv(-(sP.hi*S),sQ.lo), True)
    K=I(ediv(s3.lo*S,sQ.hi), -ediv(-(s3.hi*S),sQ.lo), True)
    Sg=mul(E,K); R2=sq(R)
    sF=sumIv(lambda i: mul(add(evPhi(R2,Sg,E,Ycell(N,i)),evPhi(R2,Sg,E,neg(Ycell(N,i)))),Wcell(N,i)),N)
    ok = N>0 and sP.ok and sQ.ok and s3.ok and s5.ok and sF.ok and sP.lo>=0 and sQ.lo>0 and s3.lo>=0 and s5.lo>=0 and sF.hi>=0
    lhs=sQ.hi*sF.hi; rhs=3*(3*sP.lo*s5.lo-sQ.hi*s3.hi)
    if verbose:
        D=S*N
        print([float(Fr(x,D)) for x in (sP.lo,sP.hi,sQ.lo,sQ.hi,s3.lo,s3.hi,s5.lo,s5.hi,sF.lo,sF.hi)])
    return ok and lhs<rhs, (rhs/lhs if lhs>0 else 0)
def search(N,target):
    e=Fr(0); cells=[]
    widths=[Fr(k,1000) for k in (100,80,60,50,40,32,25,20,16,12,10,8)]
    while e<Fr(1,2):
        for w in widths:
            e1=min(e+w,Fr(1,2))
            ok,r=cellCheck(N,e,e1)
            if ok and r>target:
                cells.append((e,e1,r)); e=e1; break
        else: raise Exception("fail at %s"%e)
    return cells
if __name__=="__main__":
    N=int(sys.argv[1]); target=float(sys.argv[2])
    cells=search(N,target)
    for c in cells: print(c[0],c[1],round(c[2],4))
    print(len(cells))
