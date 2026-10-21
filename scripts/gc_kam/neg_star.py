"""UNTRUSTED oracle (v_par < 0 torus): centre coefficients and l1 deviations of the radial and winding
polynomials of K0 (Design/RationalStellaratorGCNegStarCheck), decoded from the packed high-resolution grids."""
import re,sys
from fractions import Fraction
D='/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'
def rows(fname,name):
    s=open(D+fname).read()
    i=s.index('def %s : List ℕ := ['%name); j=s.index(']',i)
    body=s[i:j].split('[',1)[1]
    return [int(t,16) for t in re.findall(r'0x[0-9a-fA-F]+',body)]
N,M,F=40,30,112
def fieldW(data,f): return ((data>>(F*f))%(1<<F))-(1<<(F-1))
def half(rs,i,j): return fieldW(rs[i-N],j) if (i>=N and i-N<len(rs)) else 0
def sym(rs,s):
    return {(i,j): half(rs,i,j)+s*half(rs,2*N-i,2*M-j) for i in range(2*N+1) for j in range(2*M+1)}
U=sym(rows('RationalStellaratorGCNegTorusDataH1.lean','datH_U'),1)
Z=sym(rows('RationalStellaratorGCNegTorusDataH2.lean','datH_Z'),-1)
thU={k:(k[0]-N)*v for k,v in U.items()}; thZ={k:(k[0]-N)*v for k,v in Z.items()}
def add(a,b,sb=1):
    r=dict(a)
    for k,v in b.items(): r[k]=r.get(k,0)+sb*v
    return r
def mul(a,b):
    r={}
    for (i,j),v in a.items():
        if v==0: continue
        for (k,l),w in b.items():
            if w==0: continue
            r[(i+k,j+l)]=r.get((i+k,j+l),0)+v*w
    return r
def shift(a,di,dj): return {(i+di,j+dj):v for (i,j),v in a.items()}
S=101
A=add(U,Z); B=add(U,Z,-1)
rad=add(A,shift(B,2,0))
c0=rad.get((N+1,M),0); L=sum(abs(v) for k,v in rad.items() if k!=(N+1,M))
print('rad c0/2^102',c0/2**102,'L',L/2**102,'lower',(c0-L)/2**102)
print('rad maxcoef bits', max(abs(v) for v in rad.values()).bit_length(), 'c0',c0)
wd=add(mul(U,thZ),mul(Z,thU),-1)
c0w=wd.get((2*N,2*M),0); Lw=sum(abs(v) for k,v in wd.items() if k!=(2*N,2*M))
print('wind c0',c0w/2**202,'L',Lw/2**202,'lower',(c0w-Lw)/2**202)
print('wind maxcoef bits', max(abs(v) for v in wd.values()).bit_length(), 'c0', c0w)
import json
json.dump({'c0rad':c0,'Lrad':L,'c0w':c0w,'Lw':Lw},open('/tmp/gcwn/star.json','w'))
print('L1 U',sum(abs(v) for v in U.values())/2**101,'Z',sum(abs(v) for v in Z.values())/2**101,'thU',sum(abs(v) for v in thU.values())/2**101,'thZ',sum(abs(v) for v in thZ.values())/2**101)
