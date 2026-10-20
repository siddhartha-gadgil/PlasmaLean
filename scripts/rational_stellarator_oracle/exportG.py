from fractions import Fraction as Fr
from poly import *
G,N,Nt=field_polys(Fr(1,4),Fr(1))
for i,g in enumerate(G):
    g4={e:4*v for e,v in g.items()}
    assert all(v.denominator==1 for v in g4.values())
    print(i,len(g4),";".join(f"{int(v)} {' '.join(map(str,e))}" for e,v in sorted(g4.items())))
