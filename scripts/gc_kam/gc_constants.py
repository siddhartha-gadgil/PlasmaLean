"""UNTRUSTED: numerical estimate of the KAM step constants (structure SC of Design/KamFlowStep) for
the guiding-centre torus (gc_torus.py output), using the PolyExprS majorant rules of
Theory/KAM/PolyExprS on the expression trees of gcmodel.py, and compare with torus A (cA).
Usage: python gc_constants.py <num> <den>"""
import sys, os, json, math
import numpy as np, sympy as sp
sys.path.insert(0, os.path.dirname(__file__))
sys.path.insert(0, '/Users/gadgil/code/PlasmaLean/scripts/kam_oracle')
import gcmodel as G
from flow_torus import index_sets
from gc_torus import GalerkinGC, gcparts, IOTA

num, den = int(sys.argv[1]), int(sys.argv[2]); RHO = num / den
d = np.load('/tmp/k2work/gc_torus_%d_%d.npz' % (num, den))
a, b, N, M = d['a'], d['b'], int(d['N']), int(d['M'])
rA = 0.1257; mu = 1e-10

# ---- leaf polynomial majorants ----
Pcache = {}
def leafpoly(n): return sp.Poly(G.ALLP[n], G.u, G.z, G.c, G.s)
def pmaj(n, av):
    P = Pcache.setdefault(n, leafpoly(n))
    return sum(abs(float(co)) * av[0] ** i * av[1] ** j * av[2] ** k * av[3] ** l for (i, j, k, l), co in P.terms())
def pmajD(n, av, bv):
    P = Pcache.setdefault(n, leafpoly(n)); tot = 0.0
    for (i, j, k, l), co in P.terms():
        e = (i, j, k, l); base = abs(float(co))
        for v in range(4):
            if e[v] == 0: continue
            t = base * e[v] * bv[v]
            for w in range(4):
                t *= av[w] ** (e[w] - (1 if w == v else 0))
            tot += t
    return tot
def pmajD2(n, av, bv):
    P = Pcache.setdefault(n, leafpoly(n)); tot = 0.0
    for (i, j, k, l), co in P.terms():
        e = list((i, j, k, l)); base = abs(float(co))
        for v in range(4):
            for w in range(4):
                ee = e[:]
                if ee[v] == 0: continue
                f = ee[v]; ee[v] -= 1
                if ee[w] == 0: continue
                f *= ee[w]; ee[w] -= 1
                t = base * f * bv[v] * bv[w]
                for x in range(4): t *= av[x] ** ee[x]
                tot += t
    return tot
# NB: leaf majorants above are for monomial form (sumE/monoE); the Lean majorant of monoE uses the
# same products, so they coincide up to the order of multiplication.

def isqG(c, t): return 1 / math.sqrt(c - t)
def cv(k): return {'rho': abs(RHO), 'half': 0.5}.get(k, abs(k) if not isinstance(k, str) else 0)

def maj(t, av):
    k = t[0]
    if k == 'const': return cv(t[1])
    if k == 'var': return av[t[1]]
    if k in ('add', 'sub'): return maj(t[1], av) + maj(t[2], av)
    if k == 'mul': return maj(t[1], av) * maj(t[2], av)
    if k == 'poly': return pmaj(t[1], av)
    if k == 'node':
        m = pmaj('EpP', av); assert m < 1, ('invalid node', m); return isqG(1, m)
    if k == 'ref': return maj(t[2], av)
def majD(t, av, bv):
    k = t[0]
    if k == 'const': return 0.0
    if k == 'var': return bv[t[1]]
    if k in ('add', 'sub'): return majD(t[1], av, bv) + majD(t[2], av, bv)
    if k == 'mul': return majD(t[1], av, bv) * maj(t[2], av) + maj(t[1], av) * majD(t[2], av, bv)
    if k == 'poly': return pmajD(t[1], av, bv)
    if k == 'node':
        m = pmaj('EpP', av); return isqG(1, m) ** 3 / 2 * pmajD('EpP', av, bv)
    if k == 'ref': return majD(t[2], av, bv)
def majD2(t, av, bv):
    k = t[0]
    if k in ('const', 'var'): return 0.0
    if k in ('add', 'sub'): return majD2(t[1], av, bv) + majD2(t[2], av, bv)
    if k == 'mul':
        return (majD2(t[1], av, bv) * maj(t[2], av) + 2 * majD(t[1], av, bv) * majD(t[2], av, bv)
                + maj(t[1], av) * majD2(t[2], av, bv))
    if k == 'poly': return pmajD2(t[1], av, bv)
    if k == 'node':
        m = pmaj('EpP', av); g = isqG(1, m)
        return 3 * g ** 5 / 4 * pmajD('EpP', av, bv) ** 2 + g ** 3 / 2 * pmajD2('EpP', av, bv)
    if k == 'ref': return majD2(t[2], av, bv)

# ---- torus norms (numerical, grid FFT) ----
Nt, Np = 256, 192
g = GalerkinGC(N, M, IOTA, RHO, Nt, Np)
R, zz, Rth, Rps, zth, zps = g.fields(a, b)
uu = R - 1
LR = 2 * Rps + IOTA * Rth; Lz = 2 * zps + IOTA * zth
def strip(f):
    F = np.fft.fft2(f.reshape(Nt, Np)) / (Nt * Np)
    k = np.fft.fftfreq(Nt, 1 / Nt); m = np.fft.fftfreq(Np, 1 / Np)
    K, Mm = np.meshgrid(k, m, indexing='ij')
    return float(np.sum(np.abs(F) * np.exp(rA * (np.abs(K) + np.abs(Mm))))), F
au, _ = strip(uu); az, _ = strip(zz); aRt, _ = strip(Rth); azt, _ = strip(zth)
aLR, _ = strip(LR); aLz, _ = strip(Lz)
au += mu; az += mu; aRt += mu; azt += mu; aLR += mu; aLz += mu
ac = 74315 / 2 ** 16
av = [au, az, ac, ac]
print('torus strip norms: au %.4f az %.4f aRt %.4f azt %.4f aLR %.4f aLz %.4f' % (au, az, aRt, azt, aLR, aLz))
print('node validity: maj E = %.4f (< 1 required)' % pmaj('EpP', av))
T = G.TREES
e0, e1 = [0, 0, 0, 0], None
def unit(i): v = [0.0] * 4; v[i] = 1.0; return v
bD = maj(T['gcD'], av); bDu = majD(T['gcD'], av, unit(0)); bDz = majD(T['gcD'], av, unit(1))
bnR = maj(T['gcNR'], av); bnRu = majD(T['gcNR'], av, unit(0)); bnRz = majD(T['gcNR'], av, unit(1))
bnZ = maj(T['gcNZ'], av); bnZu = majD(T['gcNZ'], av, unit(0)); bnZz = majD(T['gcNZ'], av, unit(1))
print('field majorants (crude): bD %.3f bDu %.3f bDz %.3f bnR %.3f bnRu %.3f bnRz %.3f bnZ %.3f bnZu %.3f bnZz %.3f'
      % (bD, bDu, bDz, bnR, bnRu, bnRz, bnZ, bnZu, bnZz))
# D - 1 majorant: base polynomial without constant + correction
Dm1 = G.ALLP['Dp'] - 1
P1 = sp.Poly(Dm1, G.u, G.z, G.c, G.s)
majDm1 = sum(abs(float(co)) * av[0] ** i * av[1] ** j * av[2] ** k * av[3] ** l for (i, j, k, l), co in P1.terms())
majDm1 += maj(T['gcD'][2], av)
print('|D~ - 1| majorant %.4f' % majDm1)
sR = 1 / (1 - au)
# sharp numerical strip norms at K0 (admissibility: + Lipschitz * mu, negligible)
h_ = 1e-30
Dt_, nRt_, nZt_ = gcparts(uu, zz, g.cc, g.ss, RHO)
cu = gcparts(uu + 1j * h_, zz, g.cc, g.ss, RHO); cz = gcparts(uu, zz + 1j * h_, g.cc, g.ss, RHO)
bD, Fd = strip(Dt_); bDu, _ = strip(cu[0].imag / h_); bDz, _ = strip(cz[0].imag / h_)
bnR, _ = strip(nRt_); bnRu, _ = strip(cu[1].imag / h_); bnRz, _ = strip(cz[1].imag / h_)
bnZ, _ = strip(nZt_); bnZu, _ = strip(cu[2].imag / h_); bnZz, _ = strip(cz[2].imag / h_)
cD = float(Fd[0, 0].real); devD = strip(Dt_ - cD)[0]
sD = 1 / (cD - devD)
print('sharp field norms: bD %.3f bDu %.3f bDz %.3f bnR %.3f bnRu %.3f bnRz %.3f bnZ %.3f bnZu %.3f bnZz %.3f'
      % (bD, bDu, bDz, bnR, bnRu, bnRz, bnZ, bnZu, bnZz))
print('D~ mean %.4f deviation %.4f sD %.4f' % (cD, devD, sD))
# W0 = dTh u * z - dTh z * u : numerical Neumann bound around its mean
W0 = Rth * zz - zth * uu
nW, FW = strip(W0); c0 = float(FW[0, 0].real)
devW = nW - abs(c0)
sW = 1 / (abs(c0) - devW) if abs(c0) > devW else float('inf')
print('W0 mean %.5f deviation %.5f  sW %.2f' % (c0, devW, sW))
# torsion T0 = R^3 P / (D^3 W0^2) numerically
h = 1e-30
Dt, nRt, nZt = gcparts(uu, zz, g.cc, g.ss, RHO)
Dc = gcparts(uu + 1j * h, zz, g.cc, g.ss, RHO); D_u = [x.imag / h for x in Dc]
Dc = gcparts(uu, zz + 1j * h, g.cc, g.ss, RHO); D_z = [x.imag / h for x in Dc]
Du, nRu, nZu = D_u; Dz, nRz, nZz = D_z
Pn = ((nRt * Dt - Dt * (nRu * uu + nRz * zz) + nRt * (Du * uu + Dz * zz)) * zz
      - (nZt * Dt - Dt * (nZu * uu + nZz * zz) + nZt * (Du * uu + Dz * zz)) * uu)
T0 = R ** 3 * Pn / (Dt ** 3 * W0 ** 2)
tT, FT = strip(T0); tau = abs(float(FT[0, 0].real))
print('torsion: |T0| %.3f  <T0> %.4f' % (tT, FT[0, 0].real))
# SC formulas (Design/KamFlowStep)
gam = 0.0687; E1 = 2.718; d0 = rA / 7; e0 = 6e-22
th = e0 / d0 ** 4; eM = th * d0 ** 4
kE = sD; keta1 = sW * (az + au) * kE; keta2 = bD * sR ** 3 * (aRt + azt) * kE
kh = (1 + au) ** 3 * sD * sW; kTc = (1 + au) ** 3 * sD * sW ** 2 * (az + au) * kE
tTot = tT + kTc * eM; taup = tau - kTc * eM; gg = 2 * E1 * gam
k20 = keta2 / gg; kc = (keta1 * d0 + tTot * k20) / taup; k2 = k20 + kc; k1 = (keta1 * d0 + tTot * k2) / gg
mA = max(aRt, azt); mV = max(au, az)
cK = k1 * mA + k2 * d0 * kh * mV
kS = (bDu + bDz) * sD * kE * d0 + 3 * sR * kE * d0 + sW * (az + au) * kE / E1
kRem = kS * k2 * kh * mV * d0 + k1 * kE / E1
XRb = bnR * sD; XZb = bnZ * sD
kA = max((bnRu + XRb * bDu) * sD + (bnRz + XRb * bDz) * sD, (bnZu + XZb * bDu) * sD + (bnZz + XZb * bDz) * sD)
cL = kA * cK + kE * d0 ** 2 + kRem * th * d0 ** 3
cKb, cLb = cK * 1.01, cL * 1.01
Tq = th * d0 ** 2
avec = [au, az, ac, ac, aLR, aLz]; mvec = [cKb, cKb, 0, 0, cLb, cLb]
aT = [avec[i] + Tq * mvec[i] for i in range(6)]
# resRp = D w_R - n_R : majD2 with the 6-variable bounds (vars 4, 5 = velocities)
def maj6(t, av6):
    if t[0] == 'var' and t[1] >= 4: return av6[t[1]]
    return None
def majD2_res(Dtree, ntree, wvar):
    # majD2(sub(mul(D, var w), n)) = majD2(D)*a_w + 2 majD(D) * m_w + majD2(n)
    a4 = [aT[0], aT[1], aT[2], aT[3]]; b4 = [mvec[0], mvec[1], mvec[2], mvec[3]]
    return majD2(Dtree, a4, b4) * aT[wvar] + 2 * majD(Dtree, a4, b4) * mvec[wvar] + majD2(ntree, a4, b4)
C2 = max(majD2_res(T['gcD'], T['gcNR'], 4), majD2_res(T['gcD'], T['gcNZ'], 5)) / 2
kap = bD * kRem * d0 + (bDu + bDz) * cK * kE * d0 ** 2 + C2
small = 32 * kap * e0 / d0 ** 4
out = dict(rho=[num, den], au=au, az=az, aRt=aRt, azt=azt, aLR=aLR, aLz=aLz, majE=pmaj('EpP', av),
           bD=bD, bDu=bDu, bDz=bDz, bnR=bnR, bnRu=bnRu, bnRz=bnRz, bnZ=bnZ, bnZu=bnZu, bnZz=bnZz,
           majDm1=majDm1, sD=sD, sR=sR, W0mean=c0, W0dev=devW, sW=sW, tT=tT, tau=tau,
           cK=cK, cL=cL, C2=C2, kap=kap, e0_assumed=e0, smallness=small,
           e0_max_for_smallness=d0 ** 4 / (32 * kap))
print(json.dumps(out, indent=1))
json.dump(out, open('/tmp/k2work/gc_constants_%d_%d.json' % (num, den), 'w'), indent=1)
