"""UNTRUSTED.  Numerical constants of the coarse certificate (mirrors CoilKamCert.lean):
coefficient sums at the strip weights (bounded by E^n with E = 1/(1-rho)), the mapping
hypothesis, Mcoil, the sup bound M of the residual, and the Paley-Wiener tail."""
import json
from fractions import Fraction as Fr
import math

from emit_lean import records, D, N1, L
pred = json.load(open('/tmp/ckwork/predict.json'))
recs = records(pred['N'], pred['M'])
rest = recs[1:]
n = lambda r: abs(r[0]) + abs(r[1])  # noqa: E731


def wsum(G, E, rs):
    return sum(Fr(G(r)) * E ** n(r) for r in rs) / D


rho_p, rho, r_s = Fr(1, 20), Fr(1, 25), Fr(1, 50)
Ep, Er, Ers = 1 / (1 - rho_p), 1 / (1 - rho), 1 / (1 - r_s)
s1 = Fr(abs(recs[0][2] - D) + sum(abs(r[2]) + abs(r[3]) for r in rest), D)
s2 = Fr(abs(recs[0][4]) + sum(abs(r[4]) + abs(r[5]) for r in rest), D)
GA = lambda r: abs(r[2]) + abs(r[3])  # noqa: E731
GB = lambda r: abs(r[4]) + abs(r[5])  # noqa: E731
eR = wsum(GA, Ep, recs) - Fr(sum(GA(r) for r in recs), D)
eZ = wsum(GB, Ep, recs) - Fr(sum(GB(r) for r in recs), D)
C = (Ep + 1 / (1 + rho_p)) / 2
Sh = (Ep - 1 / Ep) / 2
print(f"s1 {float(s1):.6f} s2 {float(s2):.6f} eR {float(eR):.5f} eZ {float(eZ):.5f} C {float(C):.6f} Sh {float(Sh):.5f}")
imq = (eR * C) ** 2 + ((1 + s1 + eR) * Sh) ** 2 + eZ ** 2
reb = max(s1, s2) + (1 + s1 + eR) * (C - 1) + eR * Sh + eR + eZ
print(f"Im bound {math.sqrt(imq):.5f}  Re tube {float(reb):.5f}")
w, d, eta = Fr(23, 100), Fr(12, 100), Fr(7, 100)
assert imq < eta ** 2 and reb < w and w + d <= Fr(7, 20) and eta < d
# Mcoil(w, d, eta)
k0 = 90485364 / 2 ** 32
Tp = k0 * 2.3 * math.sqrt((4 + 2 * float(w)) ** 2 + float(eta) ** 2) / (float(d) ** 2 - float(eta) ** 2) ** 1.5
Ta = (1 - float(eta) ** 2 / (1 - float(w)) ** 2) ** -1.5 * (1 / (1 - float(w)) + float(eta) / (1 - float(w)) ** 2)
Mc = 192 * Tp + Ta + 0.003
print(f"Mcoil(w={w}, d={d}, eta={eta}) = {Mc:.1f}")
SR = wsum(GA, Er, recs)
SL = wsum(lambda r: (abs(r[0]) + abs(r[1])) * GA(r), Er, recs)
SLZ = wsum(lambda r: (abs(r[0]) + abs(r[1])) * GB(r), Er, recs)
Cr = (Er + 1 / (1 + rho)) / 2
print(f"SR {float(SR):.4f} SL {float(SL):.4f} SLZ {float(SLZ):.4f} C(rho) {float(Cr):.5f}")
MR = 2 * float(Cr) * Mc * float(SL) + float(SR) * 2 * float(Cr) * Mc
MZ = 2 * float(Cr) * Mc * float(SLZ) + float(SR) * Mc
print(f"sup bounds: M_R {MR:.4e} M_Z {MZ:.4e}")
q = 1 / (1 + float(rho - r_s))
geoZ = (1 + q) / (1 - q)
tail = lambda K: 2 * q ** (K + 1) / (1 - q)  # noqa: E731
K1, K2 = 7, 15
boxW = (2 * K1 + 1) * (2 * K2 + 1) * float(Ers) ** (K1 + K2)
tot1, tot2 = int(pred['tot1']), int(pred['tot2'])
sampR = tot1 / D / (N1 * L) * boxW
sampZ = tot2 / D / (N1 * L) * boxW
tailR = 2 * MR * geoZ * (tail(K1) + tail(K2))
tailZ = 2 * MZ * geoZ * (tail(K1) + tail(K2))
print(f"sample part: R {sampR:.4e}, Z {sampZ:.4e};  aliasing tail: R {tailR:.4e}, Z {tailZ:.4e}")
print(f"certified: ||E_R||_r <= {sampR + tailR:.4e}, ||E_z||_r <= {sampZ + tailZ:.4e}  (r = {float(r_s)})")
