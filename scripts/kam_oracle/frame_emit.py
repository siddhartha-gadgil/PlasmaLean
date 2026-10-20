"""UNTRUSTED.  Oracle for the frame and torsion certificate of torus A (K3 lemma 5).

Produces the data of PlasmaLean/Design/KamTorusAFrameData.lean (surrogate torus, zero-mean
function g, multiplier s, atom expression trees) and predicts every kernel computation of
PlasmaLean/Design/KamTorusAFrameCheck.lean exactly (big integers, Fractions): the weights and
box of the top tree, the Kronecker parameters (b = 752, W = 309, d = 17), the centre coefficient
c0Phi, the digit sum, the closeness bounds and the perturbation majorant.

Torsion density (frame (d_theta K, N), N = V0/(w W0), V0 = (R-1, z), w = D/R^3):
    T0 = ((X - DX V0) x V0) / (w W0^2) = 16 R^3 G / (D_l^3 W0^2),
mean over the torus ~ 0.39864 (= 2 pi d iota/d Phi, shear 0.063).

Usage: python frame_emit.py [out.lean]   (needs numpy, sympy, gmpy2; reads the K2 data file)
"""
import sys
import re
from fractions import Fraction as Fr

import numpy as np
from gmpy2 import mpz
import sympy as sp

DATA = __file__.rsplit('/scripts/', 1)[0] + '/PlasmaLean/Design/KamTorusAData.lean'

# ---------------- K2 data ----------------
src=open(DATA).read()
def lit(name):
    m=re.search(r'def '+name+r' : ℕ := (0x[0-9a-fA-F]+)',src); return int(m.group(1),16)
N,M,P=32,22,90
dA,dB=lit('dataA'),lit('dataB')
def dec(val,i,j):
    if i<N: return 0
    f=(i-N)*(2*M+1)+j
    return ((val>>(96*f))%(1<<96))-(1<<95)
cA=np.zeros((2*N+1,2*M+1),dtype=object); cB=cA.copy()
for i in range(N,2*N+1):
    for j in range(2*M+1):
        cA[i,j]=dec(dA,i,j); cB[i,j]=dec(dB,i,j)


# ---------------- atoms ----------------
r,z,C,S=sp.symbols('r z C S')
R=1+r
D8=8*R**2-((R**2-1)**2-4*z**2)*S-z*((R**2-1)*(R**2-5)-4*z**2)*C
Dl=2*D8                      # 16 D
NR8=R*((R**4-1+4*z**2)*C-z*(R**4-5+4*z**2)*S)
A1=2*NR8                      # 16 Num_R
A2=R**2*(-8*z*C-((R**2-1)*(R**2-5)-12*z**2)*S)   # 16 Num_Z
# derivative wrt R equals derivative wrt r
atoms={'Dl':Dl,'DlR':sp.diff(Dl,r),'Dlz':sp.diff(Dl,z),
       'A1':A1,'A1R':sp.diff(A1,r),'A1z':sp.diff(A1,z),
       'A2':A2,'A2R':sp.diff(A2,r),'A2z':sp.diff(A2,z)}
atoms={k:sp.Poly(sp.expand(v),r,z,C,S) for k,v in atoms.items()}

# ---------------- design (floating point) ----------------
cAi=cA; cBi=cB
n1,m1,p=7,5,32
ng,mg=7,5; ns,ms=4,3
cval=0.3
Nt,Np=512,256
# truncated, rounded coefficient grids (only i>=N stored as in data; reflect implicitly)
def trunc(c):
  out={}
  for i in range(N,N+n1+1):
    for j in range(M-m1,M+m1+1):
      v=int(c[i,j])
      if v: out[(i-N,j-M)]=round(v/2**(P-p))  # integer over 2^p
  return out
tA=trunc(cAi); tB=trunc(cBi)
# l1 errors (sup bounds) over all modes: note data stores half grid; full series = data itself (cos/sin with i>=N)
def errs(c,t):
  e0=e1=0.0
  for i in range(N,2*N+1):
    for j in range(2*M+1):
      v=int(c[i,j])/2**P - t.get((i-N,j-M),0)/2**p
      e0+=abs(v); e1+=abs(v)*(i-N)
  return e0,e1
eR,ea=errs(cAi,tA); ez,eb=errs(cBi,tB)
print('[design]','errors R %.3g z %.3g a %.3g b %.3g'%(eR,ez,ea,eb))
th=2*np.pi*np.arange(Nt)/Nt; ps=2*np.pi*np.arange(Np)/Np
TH,PS=np.meshgrid(th,ps,indexing='ij'); PH=(PS+np.pi/2)/2
def ev(t,sine):
  F=0*TH; Ft=0*TH
  for (k,m),v in t.items():
    ang=k*TH+m*PS; v=v/2**p
    if sine: F+=v*np.sin(ang); Ft+=v*k*np.cos(ang)
    else: F+=v*np.cos(ang); Ft-=v*k*np.sin(ang)
  return F,Ft
R,a=ev(tA,False); Z,b=ev(tB,True); rr=R-1
Cg,Sg=np.cos(2*PH),np.sin(2*PH)
def peval(poly,rv,zv):
  out=0*TH
  for (i,j,k,l),c in poly.terms(): out=out+float(c)*rv**i*zv**j*Cg**k*Sg**l
  return out
A={k:peval(p_,rr,Z) for k,p_ in atoms.items()}
def top(A,r,z,a,b):
  Dl=A['Dl']
  Y1=Dl*A['A1']-((Dl*A['A1R']-A['A1']*A['DlR'])*r+(Dl*A['A1z']-A['A1']*A['Dlz'])*z)
  Y2=Dl*A['A2']-((Dl*A['A2R']-A['A2']*A['DlR'])*r+(Dl*A['A2z']-A['A2']*A['Dlz'])*z)
  G=Y1*z-Y2*r; W0=a*z-b*r
  return 16*(1+r)**3*G, Dl**3*W0**2
num,Q=top(A,rr,Z,a,b)
T=num/Q
print('[design]','T0(Ktilde) mean %.6f min %.3f max %.3f; Q min %.3g max %.3g'%(T.mean(),T.min(),T.max(),Q.min(),Q.max()))
# g: minus oscillating part of T truncated
Th=np.fft.fft2(T)/T.size
kf=np.fft.fftfreq(Nt,1/Nt).astype(int)[:,None]; mf=np.fft.fftfreq(Np,1/Np).astype(int)[None,:]
mask=(np.abs(kf)<=ng)&(np.abs(mf)<=mg); mask[0,0]=False
gcoef={}  # cos series: g = sum_{k>=0 half} gc cos(k th + m ps)
for k in range(0,ng+1):
  for m in range(-mg,mg+1):
    if k==0 and m<=0: continue
    c=-2*Th[k,m].real
    gcoef[(k,m)]=round(c*2**p)
def evcos(co):
  F=0*TH
  for (k,m),v in co.items(): F+=v/2**p*np.cos(k*TH+m*PS)
  return F
g=evcos(gcoef)
res=T+g
print('[design]','T+g: mean %.6f min %.6f max %.6f'%(res.mean(),res.min(),res.max()))
# s ~ Q^{-1/2} normalised
sq=Q**-0.5; sq/=sq.mean()
Sh=np.fft.fft2(sq)/sq.size
scoef={}
for k in range(0,ns+1):
  for m in range(-ms,ms+1):
    if k==0 and m<0: continue
    c=Sh[k,m].real*(1 if (k==0 and m==0) else 2)
    scoef[(k,m)]=round(c*2**p)
s=evcos(scoef)
cn=cval
F=num+Q*(g-cn)
Phi=s*s*F
Ph=np.fft.fft2(Phi)/Phi.size
c0=Ph[0,0].real; rest=np.abs(Ph).sum()-abs(c0)
print('[design]','Phi centre %.4g rest l1 %.4g ratio %.4f ; min Phi %.4g'%(c0,rest,rest/c0,Phi.min()))
l1s=sum(abs(v) for v in scoef.values())/2**p; l1g=sum(abs(v) for v in gcoef.values())/2**p
print('[design]','l1 s %.4g  l1 g %.4g  margin (c0-rest)/l1s^2 = %.4g'%(l1s,l1g,(c0-rest)/l1s**2))
d=dict(tA=tA,tB=tB,gcoef=gcoef,scoef=scoef,n1=n1,m1=m1,p=p,cval=cval)

# ---------------- exact predictions and emission ----------------
SYMATOMS = atoms
cval = Fr(d['cval']).limit_denominator(100)
cn, cd = cval.numerator, cval.denominator

# ---------------- expression trees ----------------
def V(i): return ('v', i)
def K(c): return ('c', int(c))
def add(a, b): return ('+', a, b)
def sub(a, b): return ('-', a, b)
def mul(a, b): return ('*', a, b)

def wt(e, W):
    t = e[0]
    if t == 'v': return W[e[1]]
    if t == 'c': return (0, 0, 0)
    x = wt(e[1], W); y = wt(e[2], W)
    if t == '*': return (x[0] + y[0], x[1] + y[1], (x[2] + y[2]) % 4)
    assert x[0] == y[0] and x[1] == y[1] and (x[2] - y[2]) % 2 == 0, (x, y)
    return x

def sg(a, b, W): return 1 if wt(a, W)[2] == wt(b, W)[2] else -1

def evH(e, W, env):
    t = e[0]
    if t == 'v': return env[e[1]]
    if t == 'c': return mpz(e[1])
    if t == '*': return evH(e[1], W, env) * evH(e[2], W, env)
    a = evH(e[1], W, env); b = evH(e[2], W, env) * sg(e[1], e[2], W)
    return a + b if t == '+' else a - b

def ev(e, env):
    t = e[0]
    if t == 'v': return env[e[1]]
    if t == 'c': return e[1]
    a = ev(e[1], env); b = ev(e[2], env)
    return a + b if t == '+' else a - b if t == '-' else a * b

def box(e, Bx):
    t = e[0]
    if t == 'v': return Bx[e[1]]
    if t == 'c': return (0, 0)
    x = box(e[1], Bx); y = box(e[2], Bx)
    if t == '*': return (x[0] + y[0], x[1] + y[1])
    return (max(x[0], y[0]), max(x[1], y[1]))

def majN(e, L):
    t = e[0]
    if t == 'v': return L[e[1]]
    if t == 'c': return abs(e[1])
    x = majN(e[1], L); y = majN(e[2], L)
    return x * y if t == '*' else x + y

def majQ(e, B):
    t = e[0]
    if t == 'v': return B[e[1]]
    if t == 'c': return Fr(abs(e[1]))
    x = majQ(e[1], B); y = majQ(e[2], B)
    return x * y if t == '*' else x + y

def dmajQ(e, B, E):
    t = e[0]
    if t == 'v': return E[e[1]]
    if t == 'c': return Fr(0)
    if t == '*':
        da = dmajQ(e[1], B, E); db = dmajQ(e[2], B, E)
        ba = majQ(e[1], B); bb = majQ(e[2], B)
        return da * (bb + db) + ba * db
    return dmajQ(e[1], B, E) + dmajQ(e[2], B, E)

def lean(e):
    t = e[0]
    if t == 'v': return f'v {e[1]}'
    if t == 'c': return f'c ({e[1]})' if e[1] < 0 else f'c {e[1]}'
    op = {'+': 'a', '-': 's', '*': 'm'}[t]
    return f'{op} ({lean(e[1])}) ({lean(e[2])})'

def size(e): return 1 if e[0] in 'vc' else 1 + size(e[1]) + size(e[2])

# base variables: 0 r, 1 z, 2 C, 3 S, 4 t, 5 V
WB = [(1, 0, 0), (1, 0, 1), (0, 1, 3), (0, 1, 0), (1, 0, 0), (0, 1, 0)]
ATOMS = ['Dl', 'DlR', 'Dlz', 'A1', 'A1R', 'A1z', 'A2', 'A2R', 'A2z']
TARGET = {'Dl': (5, 1), 'DlR': (4, 1), 'Dlz': (4, 1), 'A1': (6, 1), 'A1R': (5, 1), 'A1z': (5, 1),
          'A2': (6, 1), 'A2R': (5, 1), 'A2z': (5, 1)}

def atom_tree(name):
    poly = SYMATOMS[name]; dt, dv = TARGET[name]
    tree = None
    for (i, j, k, l), c in sorted(poly.terms()):
        assert c == int(c)
        assert i + j <= dt and k + l <= dv
        m = K(int(c))
        for var, cnt in ((0, i), (1, j), (2, k), (3, l), (4, dt - i - j), (5, dv - k - l)):
            for _ in range(cnt): m = mul(m, V(var))
        tree = m if tree is None else add(tree, m)
    return tree

AT = {nm: atom_tree(nm) for nm in ATOMS}
WA = {nm: wt(AT[nm], WB) for nm in ATOMS}
# top variables: 0..8 atoms, 9 r, 10 z, 11 a, 12 b, 13 y, 14 s, 15 t, 16 V
WT = [WA[nm] for nm in ATOMS] + [(1, 0, 0), (1, 0, 1), (1, 0, 3), (1, 0, 0), (1, 0, 0), (1, 0, 0),
                                 (1, 0, 0), (0, 1, 0)]
Dl, DlR, Dlz, A1, A1R, A1z, A2, A2R, A2z = [V(i) for i in range(9)]
r, z, a, b, y, s, t, Vv = [V(i) for i in range(9, 17)]

def Yc(A, AR, Az):
    return sub(mul(Dl, A), add(mul(sub(mul(Dl, AR), mul(A, DlR)), r),
                               mul(sub(mul(Dl, Az), mul(A, Dlz)), z)))

Y1 = Yc(A1, A1R, A1z); Y2 = Yc(A2, A2R, A2z)
G = sub(mul(Y1, z), mul(Y2, r))
W0 = sub(mul(a, z), mul(b, r))
Rr = add(r, t)
t5V = mul(mul(mul(mul(mul(t, t), t), t), t), Vv)
F = add(mul(mul(mul(K(16 * cd), mul(mul(Rr, Rr), Rr)), G), t5V),
        mul(mul(mul(mul(Dl, Dl), Dl), mul(W0, W0)), sub(mul(K(cd), y), mul(K(cn), t))))
PHI = mul(mul(s, s), F)
wPhi = wt(PHI, WT)
print('atom weights', WA, 'Phi weight', wPhi, 'tree sizes', {k: size(v) for k, v in AT.items()},
      size(PHI))

# ---------------- surrogate data ----------------
tA = d['tA']; tB = d['tB']; gco = d['gcoef']; sco = d['scoef']
def half_grid(co):
    """big-grid half data: c[(i,j)] for i>=N (keys (k,m) -> (N+k, M+m))."""
    return {(N + k, M + m): v for (k, m), v in co.items() if v != 0}
HA, HB, HG, HS = half_grid(tA), half_grid(tB), half_grid(gco), half_grid(sco)
for H in (HA, HB, HG, HS):
    for (i, j) in H: assert N <= i <= N + n1 and M - m1 <= j <= M + m1
assert (N, M) not in HG

def win_list(H):
    """row-major list over i in [N, N+n1], j in [M-m1, M+m1]."""
    return [H.get((N + ii, M - m1 + jj), 0) for ii in range(n1 + 1) for jj in range(2 * m1 + 1)]

sig1 = 2 ** (p + 1)
def cpt(H):  # compact coordinates (i', j') -> value
    return lambda i, j: H.get((i + N - n1, j + M - m1), 0)
def sym(H, sgn):
    c = cpt(H)
    return lambda i, j: c(i, j) + sgn * c(2 * n1 - i, 2 * m1 - j)
gRt = sym(HA, 1)
gr = lambda i, j: gRt(i, j) - (sig1 if (i, j) == (n1, m1) else 0)
gz = sym(HB, -1)
ga = lambda i, j: (i - n1) * gRt(i, j)
gb = lambda i, j: (i - n1) * gz(i, j)
gy = sym(HG, 1)
gs = sym(HS, 1)
I1, J1 = 2 * n1 + 1, 2 * m1 + 1
def gl1(g): return sum(abs(g(i, j)) for i in range(I1) for j in range(J1))

# ---------------- Kronecker parameters ----------------
BXB = [(2 * n1, 2 * m1), (2 * n1, 2 * m1), (0, 2), (0, 2), (n1, m1), (0, 1)]
BXA = {nm: box(AT[nm], BXB) for nm in ATOMS}
BXT = [BXA[nm] for nm in ATOMS] + [(2 * n1, 2 * m1)] * 6 + [(n1, m1), (0, 1)]
abox, Jbox = box(PHI, BXT)
Wk = abox + 1
dk = 0
while Wk * (Jbox + 1) > 2 ** dk: dk += 1
LB = [gl1(gr), gl1(gz), 2, 2, sig1, 2]
LA = {nm: majN(AT[nm], LB) for nm in ATOMS}
LT = [LA[nm] for nm in ATOMS] + [gl1(gr), gl1(gz), gl1(ga), gl1(gb), gl1(gy), gl1(gs), sig1, 2]
majPhi = majN(PHI, LT)
ci0 = n1 * wPhi[0]; cj0 = m1 * wPhi[0] + wPhi[1]
print('box', (abox, Jbox), 'W', Wk, 'd', dk, 'majPhi bits', majPhi.bit_length(), 'centre', ci0, cj0)
bk = majPhi.bit_length() + 2
bk = (bk + 7) // 8 * 8
print('b =', bk, 'Kronecker integer ~ %.1f MB' % (bk * Wk * (Jbox + 1) / 8e6))

def pack(g, bb, W):
    tot = mpz(0)
    for j in range(J1):
        row = mpz(0)
        for i in range(I1):
            row += mpz(g(i, j)) << (bb * i)
        tot += row << (bb * W * j)
    return tot

def kron_env(bb, W):
    X = mpz(1) << bb
    base = [pack(gr, bb, W), pack(gz, bb, W), X ** (2 * W) - 1, X ** (2 * W) + 1,
            mpz(sig1) * X ** (n1 + W * m1), 2 * X ** W]
    at = [evH(AT[nm], WB, base) for nm in ATOMS]
    top = at + [base[0], base[1], pack(ga, bb, W), pack(gb, bb, W), pack(gy, bb, W),
                pack(gs, bb, W), base[4], base[5]]
    return top

def digits(T, bb, nd):
    H = 1 << (bb - 1)
    out = []
    off = mpz(H)
    for k in range(nd.bit_length() - 1):
        off = off + (off << (bb << k))
    T = int(T + off)
    assert T >= 0 and T >> (bb * nd) == 0
    B = bb // 8
    bs = T.to_bytes((T.bit_length() + 7) // 8 + 1, 'little')
    for n in range(nd):
        out.append(int.from_bytes(bs[n * B:(n + 1) * B], 'little') - H)
    return out

if __name__ == '__main__':
    env = kron_env(bk, Wk)
    Phi_int = evH(PHI, WT, env)
    nd = 2 ** dk
    dg = digits(Phi_int, bk, nd)
    slot0 = ci0 + Wk * cj0
    c0 = dg[slot0]
    L = sum(abs(x) for x in dg) - abs(c0)
    kappa = Fr(sig1) ** wPhi[0] * 2 ** wPhi[1]
    print('c0/kappa = %.6g, L/kappa = %.6g, ratio %.4f' % (c0 / kappa, L / kappa, L / c0))
    assert majPhi + c0 < 2 ** (bk - 1)
    # ---------------- perturbation (Fractions) ----------------
    def gl1big(f):
        return sum(abs(f(i, j)) for i in range(2 * N + 1) for j in range(2 * M + 1))
    sh = 2 ** (P - p)
    def big(c, H): return lambda i, j: (int(c[i, j]) if i >= N else 0) - sh * H.get((i, j), 0)
    dA = big(cAi, HA); dB = big(cBi, HB)
    eR = Fr(gl1big(dA), 2 ** P); ez = Fr(gl1big(dB), 2 ** P)
    ea = Fr(gl1big(lambda i, j: (i - N) * dA(i, j)), 2 ** P)
    eb = Fr(gl1big(lambda i, j: (i - N) * dB(i, j)), 2 ** P)
    print('closeness', float(eR), float(ez), float(ea), float(eb))
    def up(x, den=10 ** 9):  # round up to den
        return Fr(-((-x.numerator * den) // x.denominator), den)
    eRu, ezu, eau, ebu = up(eR), up(ez), up(ea), up(eb)
    gL1 = sum(abs(v) for v in HG.values()); sL1 = sum(abs(v) for v in HS.values())
    yB = up(Fr(gL1, 2 ** p), 1000); sB = up(Fr(sL1, 2 ** p), 1000)
    BB = [Fr(19, 100), Fr(19, 100), Fr(1), Fr(1), Fr(1), Fr(1)]
    EB = [eRu, ezu, Fr(0), Fr(0), Fr(0), Fr(0)]
    BA = [majQ(AT[nm], BB) for nm in ATOMS]
    EA = [dmajQ(AT[nm], BB, EB) for nm in ATOMS]
    BT = BA + [Fr(19, 100), Fr(19, 100), Fr(1, 5), Fr(1, 5), yB, sB, Fr(1), Fr(1)]
    ET = EA + [eRu, ezu, eau, ebu, Fr(0), Fr(0), Fr(0), Fr(0)]
    dPhi = dmajQ(PHI, BT, ET)
    print('dmaj Phi %.6g  (margin c0-L over kappa %.6g)' % (float(dPhi), float((c0 - L) / kappa)))
    print('c0Phi =', -c0)
    print('check_phi holds:', 10 * L + 9 * kappa <= 10 * (-c0))
    print('close bounds (1e-9 units):', eRu, ezu, eau, ebu, ' g, s bounds:', yB, sB)

# ---------------- Lean emission ----------------
def monos(name):
    poly = SYMATOMS[name]; dt, dv = TARGET[name]
    out = []
    for (i, j, k, l), c in sorted(poly.terms()):
        vs = [0] * i + [1] * j + [2] * k + [3] * l + [4] * (dt - i - j) + [5] * (dv - k - l)
        out.append((int(c), vs))
    return out

def emit_list(name, vals, doc):
    lines = [f'/-- {doc} -/', f'def {name} : List ℤ :=']
    cur = '  ['
    for x in vals:
        tok = f'{x}, '
        if len(cur) + len(tok) > 98:
            lines.append(cur.rstrip())
            cur = '    '
        cur += tok
    lines.append(cur.rstrip().rstrip(',') + ']')
    return '\n'.join(lines)

def emit_atom(name, lname, doc):
    lines = [f'/-- {doc} -/', f'def {lname} : Ex := sumEx [']
    ms = monos(name)
    for idx, (c, vs) in enumerate(ms):
        tail = ',' if idx < len(ms) - 1 else ']'
        cs = f'({c})' if c < 0 else str(c)
        lines.append(f'  monoEx {cs} {vs}{tail}'.replace(' ', ' '))
    return '\n'.join(lines)

def emit_data(path):
    HAr = dict(HA); HAr[(N, M)] = HAr.get((N, M), 0) - 2 ** p
    docs = {'Dl': '`16 D` (the cleared denominator).', 'DlR': '`∂_R (16 D)`.',
            'Dlz': '`∂_z (16 D)`.', 'A1': '`16 X̃_R = 8 R Ps` (numerator of `dR/dφ`).',
            'A1R': '`∂_R (8 R Ps)`.', 'A1z': '`∂_z (8 R Ps)`.',
            'A2': '`16 X̃_z = 4 R² Pz` (numerator of `dz/dφ`).', 'A2R': '`∂_R (4 R² Pz)`.',
            'A2z': '`∂_z (4 R² Pz)`.'}
    parts = []
    parts.append(emit_list('listA', win_list(HAr),
        '`2^p ×` the cosine coefficients of `R̃ − 1` on the window\n(row-major in `(k, m)`, '
        '`0 ≤ k ≤ n₁`, `|m| ≤ m₁`).'))
    parts.append(emit_list('listB', win_list(HB), '`2^p ×` the sine coefficients of `z̃`.'))
    parts.append(emit_list('listG', win_list(HG),
        '`2^p ×` the cosine coefficients of the zero-mean certificate function `g`.'))
    parts.append(emit_list('listS', win_list(HS),
        '`2^p ×` the cosine coefficients of the positivity multiplier `s`.'))
    for nm, ln in zip(ATOMS, ['atomDl', 'atomDlR', 'atomDlz', 'atomA1', 'atomA1R', 'atomA1z',
                              'atomA2', 'atomA2R', 'atomA2z']):
        parts.append(emit_atom(nm, ln, 'Atom ' + docs[nm]))
    open(path, 'w').write('\n\n'.join(parts) + '\n')

if __name__ == '__main__':
    out = sys.argv[1] if len(sys.argv) > 1 else 'frame_data_body.lean'
    emit_data(out)
    print('emitted data body (lists and atom trees) to', out)
