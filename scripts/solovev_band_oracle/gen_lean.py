import pickle, sys
from fractions import Fraction as Fr
from design2 import *
r=pickle.load(open(sys.argv[1],'rb'))
def checkOn(p,m,a,b,n):
    pts=[a]+[Fr(i+1,n) for i in range(n)]
    return all(m<=lowerBound(pts[i+1]-pts[i],shift(pts[i],p)) for i in range(n))
def mingrid(p):
    for n in (8,16,32,64):
        if checkOn(p,0,Fr(0),Fr(1),n): return n
    return None
Fs,Fu=r['Fs'],r['Fu']
print("deriv grids", mingrid(scale(-1,deriv(Fs))), mingrid(scale(-1,deriv(Fu))), "gap grid", mingrid(add(Fu,scale(-1,Fs))))
print("F_sub(3/10) vs Phi(10):", float(evalQ(Fs,Fr(3,10))), float(PhiQ(10)), evalQ(Fs,Fr(3,10))>=PhiQ(10))
print("F_sup(0)=",float(evalQ(Fu,0)),"T=",Phiinv(float(evalQ(Fu,0))), "F_sub(0) T=",Phiinv(float(evalQ(Fs,0))))
print("edges", evalQ(Fs,1)==PhiQ(1), evalQ(Fu,1)==PhiQ(r['T1']))
def fq(x): 
    x=Fr(x); return str(x.numerator) if x.denominator==1 else "%d/%d"%(x.numerator,x.denominator)
def poly(F): 
    s=", ".join(fq(c) for c in F); return "["+s+"]"
def pcs(ps):
    return "["+", ".join("(%s, %s, %s)"%(fq(d),fq(k),fq(K)) for d,k,K in ps)+"]"
open(sys.argv[2],'w').write("FS "+poly(Fs)+"\nFU "+poly(Fu)+"\nSUB "+pcs(r['pl'])+"\nSUP "+pcs(r['pu'])+"\nPRES "+pcs(r['pp'])+"\n")
print("labels: sub k min", min(k for _,k,_ in r['pl']), "sup K max", max(K for _,_,K in r['pu']), "sup k min", min(k for _,k,_ in r['pu']), "ceilOK all", all(K in CE for _,_,K in r['pu']))
