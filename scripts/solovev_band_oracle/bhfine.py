# Bosch-Hale (Nucl. Fusion 32 (1992) 611) D-T reactivity in 50-digit decimal; fine windows
from decimal import Decimal as D, getcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction as Fr
getcontext().prec = 50
BG=D('34.3827'); mrc2=D('1124656'); C1=D('1.17302e-9'); C2=D('1.51361e-2'); C3=D('7.51886e-2')
C4=D('4.60643e-3'); C5=D('1.35e-2'); C6=D('-1.0675e-4'); C7=D('1.366e-5')
def bh(T):  # m^3/s
    T=D(T)
    th=T/(1-T*(C2+T*(C4+T*C6))/(1+T*(C3+T*(C5+T*C7))))
    xi=(BG**2/(4*th))**(D(1)/3)
    return C1*th*(xi/(mrc2*T**3)).sqrt()*(-3*xi).exp()*D('1e-6')
def r4(x, mode):
    e = x.adjusted()
    q = D(1).scaleb(e-3)
    return x.quantize(q, rounding=mode)
def fine():
    out=[]
    for i in range(100):
        lo=Fr(20+i,4); hi=Fr(21+i,4)
        L=r4(D('0.99')*bh(D(lo.numerator)/D(lo.denominator)),ROUND_FLOOR)
        H=r4(D('1.01')*bh(D(hi.numerator)/D(hi.denominator)),ROUND_CEILING)
        out.append((20+i,21+i,L,H))
    return out
if __name__=="__main__":
    # check the coarse table reproduces
    import sys
    for k in (1,5,10,15,30,59):
        print(k, r4(D('0.99')*bh(k),ROUND_FLOOR), r4(D('1.01')*bh(k+1),ROUND_CEILING))
    for w in fine()[:3]+fine()[-2:]: print(w)
