"""UNTRUSTED (energy window): the step constants of the KAM theorem uniform over the energy window
|rho - 1/256| <= ETA = 2^-32, lam in [0, 1/16] (adapted from lam_maj.py): the residual bound e0 from
the node pipelines (Lebesgue bound LAMB of the four nodes plus the analytic remainder REM), the field
bounds of the certified low-resolution chain plus ETA times the correction bounds, the inverse of D~,
the torsion and the twist re-bounded as in Design/RationalStellaratorGCBoxAdm, and the Taylor constant
C2 at |rho| <= 1/256 + ETA.  Usage: python ew_const.py L.pkl H1.pkl ... H4.pkl OUT.pkl"""
import sys, os, pickle, math
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
import fam_ball  # noqa: F401
import ew_majlib as LM
from ew_majlib import up, down

ETA = Fr(1, 2 ** 32)
LAMB = Fr(os.environ.get('EW_LAMB', '2'))
REM = Fr(os.environ.get('EW_REM', '1/10000000000000000000000'))
L = pickle.load(open(sys.argv[1], 'rb'))['L']
HS = [pickle.load(open(f, 'rb'))['H'] for f in sys.argv[2:6]]
nmL = {v: k for k, v in L['names'].items()}
MU = Fr(1, 10 ** 11)
rA = Fr(1257, 10000)
d0 = rA / 7
ej = []
for H in HS:
    norms = {r['meta']['name']: r for r in H['nodes'] if r.get('var') is None}
    ej.append((norms['resR']['rad'] / 2 ** 96, norms['resZ']['rad'] / 2 ** 96))
emax = max(max(a, b) for a, b in ej)
e0 = up(LAMB * emax + REM, 2)
print('node residuals', [(float(a), float(b)) for a, b in ej], 'e0 =', float(e0))
# torus bounds (unchanged: cM's au etc. have slack 1e-4 >> the window shift)
au, az = Fr(193, 1000) + MU, Fr(1623, 10000) + MU
aRt, azt = Fr(327, 2000) + MU, Fr(1617, 10000) + MU
aLR, aLz = Fr(547, 5000) + MU, Fr(1037, 10000) + MU
ac = Fr(74315, 2 ** 16)
CORR = {'Dt': 177, 'Dtu': 4997, 'Dtz': 1620, 'nRt': 91, 'nRtu': 2623, 'nRtz': 861, 'nZt': 1113,
        'nZtu': 30768, 'nZtz': 6181}
fb = {}
for n in CORR:
    i = nmL[n + 'F']
    fb[n] = up(L['B'][i] + L['E'][i] + ETA * CORR[n], 5)
norms = {r['meta']['name']: r for r in L['nodes'] if r.get('var') is None}
dc0, wc0 = Fr(2126414735707981, 2 ** 51), -Fr(5398240620830529, 2 ** 59)
dD = Fr(743900000000000, 2 ** 51) + ETA * 177
sD = up(1 / (dc0 - dD), 5)
sW = Fr(17181, 100)
sR = 1 / (1 - au)
# torsion numerator perturbation (DBd algebra with the rounded field bounds of BoxAdm)
Bf = {'Dt': Fr(13, 10), 'Dtu': Fr(23, 10), 'Dtz': Fr(21, 100), 'nRt': Fr(11, 100), 'nRtu': Fr(95, 100),
      'nRtz': Fr(75, 100), 'nZt': Fr(11, 100), 'nZtu': Fr(87, 100), 'nZtz': Fr(82, 100)}
def X(n): return (Bf[n], ETA * CORR[n])
def mul(a, b): return (a[0] * b[0], a[0] * b[1] + a[1] * b[0] + a[1] * b[1])
def add(a, b): return (a[0] + b[0], a[1] + b[1])
U, Z = (au, Fr(0)), (az, Fr(0))
def part(nR, nRu, nRz, W):
    return mul(add(add(mul(X(nR), X('Dt')), mul(X('Dt'), add(mul(X(nRu), U), mul(X(nRz), Z)))),
                   mul(X(nR), add(mul(X('Dtu'), U), mul(X('Dtz'), Z)))), W)
P = add(part('nRt', 'nRtu', 'nRtz', Z), part('nZt', 'nZtu', 'nZtz', U))
dP = up(P[1], 3)
assert P[0] <= 1
q = Fr(28660)
dY = up((1 + au) ** 3 * dP * q, 3)
D3 = mul(mul(X('Dt'), X('Dt')), X('Dt'))
dF = up(D3[1] * Fr(13, 1000) ** 2, 3)
hX = Fr(313, 25000000) + q * dF
i175 = nmL['YF']
YB, YE = L['B'][i175] + L['E'][i175], L['E'][i175]
tT = up((YB + dY) / (1 - hX), 5)
fY = L['fam'][i175]
from fam_ball import decode_slice
NL_, ML_, SL_ = L['N'], L['M'], L['S']
avgs = [Fr(decode_slice(sd, NL_, ML_, fY['s'])[NL_][ML_], 2 ** SL_) for sd in fY['slices']]
Ym0, Ym1 = avgs[0], 2 * sum(abs(x) for x in avgs[1:])
tau = down(abs(Ym0) - Ym1 - YE - dY - (YB + dY) * hX / (1 - hX), 3)
print('dP %.3e dY %.3e dF %.3e hX %.3e tT %s tau %s' % (dP, dY, dF, hX, float(tT), float(tau)))
gam, E1 = Fr(687, 10000), Fr(2718, 1000)
th = e0 / d0 ** 4
eM = th * d0 ** 4
kE = sD
keta1 = sW * (az + au) * kE
keta2 = fb['Dt'] * sR ** 3 * (aRt + azt) * kE
kh = (1 + au) ** 3 * sD * sW
kTc = (1 + au) ** 3 * sD * sW ** 2 * (az + au) * kE
tTot = tT + kTc * eM
taup = tau - kTc * eM
gg = 2 * E1 * gam
k20 = keta2 / gg
kc = (keta1 * d0 + tTot * k20) / taup
k2 = k20 + kc
k1 = (keta1 * d0 + tTot * k2) / gg
mA, mV = max(aRt, azt), max(au, az)
cK = k1 * mA + k2 * d0 * kh * mV
kS = (fb['Dtu'] + fb['Dtz']) * sD * kE * d0 + 3 * sR * kE * d0 + sW * (az + au) * kE / E1
kRem = kS * k2 * kh * mV * d0 + k1 * kE / E1
XRb, XZb = fb['nRt'] * sD, fb['nZt'] * sD
kA = max((fb['nRtu'] + XRb * fb['Dtu']) * sD + (fb['nRtz'] + XRb * fb['Dtz']) * sD,
         (fb['nZtu'] + XZb * fb['Dtu']) * sD + (fb['nZtz'] + XZb * fb['Dtz']) * sD)
cL = kA * cK + kE * d0 ** 2 + kRem * th * d0 ** 3
cKb, cLb = up(cK, 3), up(cL, 3)
Tq = th * d0 ** 2
aT = [au + Tq * cKb, az + Tq * cKb, ac, ac, aLR + Tq * cLb, aLz + Tq * cLb]
mvec = [cKb, cKb, Fr(0), Fr(0), cLb, cLb]
aTQ = [Fr(965000001, 5000000000), Fr(811500001, 5000000000), ac, ac, Fr(547000001, 5000000000),
       Fr(518500001, 5000000000)]
assert all(aTQ[i] >= aT[i] for i in range(6))
mE, mE4, mQQ, mN, g = LM.node_bounds(aTQ)
LM.RHO0 = Fr(1, 256) + ETA
eN, resR, resZ = LM.trees(LM.LAM1)
C2R = LM.mD2Q(aTQ, mvec, g, resR, {}) / 2
C2Z = LM.mD2Q(aTQ, mvec, g, resZ, {}) / 2
C2 = up(max(C2R, C2Z), 3)
kap = fb['Dt'] * kRem * d0 + (fb['Dtu'] + fb['Dtz']) * cK * kE * d0 ** 2 + C2
small = 32 * kap * e0 / d0 ** 4
print('cK %.1f cL %.1f g %s C2 %.4e kap %.4e smallness %.4f' % (cK, cL, float(g), C2, kap, small))
print('budgets %.3e %.3e %.3e' % (2 * cK * e0 / d0 ** 2, 2 * (cK / E1) * e0 / d0 ** 3, 2 * cL * e0 / d0 ** 2))
print('fb', {k: float(v) for k, v in fb.items()}, 'sD', float(sD))
pickle.dump(dict(e0=e0, ej=ej, fb=fb, sD=sD, tT=tT, tau=tau, cKb=cKb, cLb=cLb, C2=C2, g=g, dP=dP, dY=dY,
                 dF=dF, hX=hX, mvec=mvec, small=small, kap=kap), open(sys.argv[6], 'wb'))
