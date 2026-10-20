import pickle, sys
from fractions import Fraction as Fr
from design2 import *
r=pickle.load(open(sys.argv[1],'rb')); den=int(sys.argv[2])
Fu=r['Fu']; Dl=r['Dl']
QP=lambda k,K: add(mul(add([Dl],scale(Fr(456900),wp)),w2),scale(-NQ*10**20*Fr(113,60)*Fr(K)*keV,w1))
levP=[PhiQ(Fr(j,den)) for j in range(den,30*den)]
pp,fp=pieces(Fu,[QP],Fr(0),10**4,True,levP,lambda Fd: Fr(0),lambda Fc: anyUp(Fc,den))
print("pressure",len(pp),fp)
if fp==0:
    r['pp']=pp; pickle.dump(r,open(sys.argv[1],'wb'))
