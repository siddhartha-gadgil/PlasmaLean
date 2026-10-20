from fractions import Fraction as Fr
def add(p,q):
    n=max(len(p),len(q)); return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(n)]
def scale(c,p): return [c*x for x in p]
def mul(p,q):
    if not p or not q: return []
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]+=x*y
    return r
def deriv(p): return [i*p[i] for i in range(1,len(p))]
def evalQ(p,x):
    r=0
    for c in reversed(p): r=r*x+c
    return r
def shift(c,p):
    # p(c+t)
    r=[]
    for a in reversed(p):
        r=add([a],mul([c,1],r))
    return r
def lowerBound(h,p):
    if not p: return 0
    return p[0]+min(0,h*lowerBound(h,p[1:]))
