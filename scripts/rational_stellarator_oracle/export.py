import pickle, numpy as np, sys
from fractions import Fraction as Fr
from poly import *
def cmp_key(e): return tuple(e)
def export_P(fitfile, E=40):
    L,c=pickle.load(open(fitfile,'rb'))
    P=reduce_circle(I_poly(L,c,1.0))
    Pi={e:int(round(v*2**E)) for e,v in P.items()}
    Pi={e:v for e,v in Pi.items() if v!=0}
    return Pi
def fpoly_str(p):
    return ";\n".join(f"{v} {' '.join(map(str,e))}" for e,v in sorted(p.items()))
if __name__=="__main__":
    Pi=export_P(sys.argv[1])
    print(len(Pi), max(abs(v) for v in Pi.values()).bit_length())
    open(sys.argv[2],'w').write(fpoly_str(Pi))
