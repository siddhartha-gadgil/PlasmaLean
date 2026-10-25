"""UNTRUSTED (energy window): the Chebyshev coefficients (in the pitch variable) of the Fourier
coefficients of the certified family torus K(lam) of Design/RationalStellaratorGCMuDataH*, decoded
from the stored Lean data (inverse of lam_cert.slice_grids).  Writes an npz (CA, CB, NT, MT) usable
as an initial guess.  Usage: python ew_decode_h.py out.npz"""
import sys, os, numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'kam_oracle'))
import ew_leandata
from fam_ball import decode_slice
from flow_torus import index_sets
D = ew_leandata.read(['RationalStellaratorGCMuDataH%d' % k for k in range(1, 7)])
N, M, S = 36, 27, 107
NT, MT = 28, 20
Is, Iz = index_sets(NT, MT)
CA, CB = [], []
for jw, (su, sz) in enumerate(zip(D['sdHM_U'], D['sdHM_Z'])):
    fac = Fr(1) if jw == 0 else Fr(1, 2)
    gu = decode_slice(su, N, M, 1)
    gz = decode_slice(sz, N, M, -1)
    a = []
    for (k, m) in Is:
        if (k, m) == (0, 0):
            v = Fr(gu[N][M], 2 ** S) / fac + (1 if jw == 0 else 0)
        else:
            v = Fr(gu[N + k][M + m], 2 ** (S - 1)) / fac
        a.append(str(v))
    b = [str(Fr(gz[N + k][M + m], 2 ** (S - 1)) / fac) for (k, m) in Iz]
    CA.append(a); CB.append(b)
np.savez(sys.argv[1], CA=np.array(CA), CB=np.array(CB), NT=NT, MT=MT)
print(len(CA), 'coefficients; a00 =', float(Fr(CA[0][0])))
