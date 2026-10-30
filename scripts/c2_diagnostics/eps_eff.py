"""UNTRUSTED numerics (Q-19, task d).  eps_eff of field(1/4) on invariant tori (driver for nemov.py),
plus the bounce-time-weighted distribution of the per-bounce radial drift proxy Hhat/Ihat.

usage: python eps_eff.py [ntransits]
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, json
from field import rhs, B_f, Bm_f, dBm_f
from tori import sections, iota_of, conjugacy, K_eval, rk4, NS
from nemov import nemov_sums, eps_eff_from

NLINES = 8


def run(rs, ntransits=150, nb=300):
    sec = sections(1 + rs, 0*rs, 2000)
    io, _ = iota_of(sec)
    alpha = 2*np.pi*np.arange(NLINES)/NLINES + 0.1
    Y0 = []
    for i in range(len(rs)):
        cR, cZ, _ = conjugacy(sec[:, :, i], io[i], 40)
        Y0.append(np.array([K_eval(cR, alpha), K_eval(cZ, alpha),
                            K_eval(cR, alpha, True), K_eval(cZ, alpha, True)]))
    Y0 = np.concatenate(Y0, axis=1)
    nsteps = 2*ntransits*NS
    dphi = np.pi/NS
    store = np.empty((nsteps + 1, 4, Y0.shape[1]))
    k = [0]

    def cb(p, yy):
        store[k[0]] = yy; k[0] += 1
    rk4(rhs, Y0, 0.0, nsteps, dphi, every=1, callback=cb)
    phi = dphi*np.arange(nsteps + 1)
    results = []
    for i, r in enumerate(rs):
        parts_in = []
        for j in range(NLINES):
            col = i*NLINES + j
            Rr, zz, dR, dz = store[:, 0, col], store[:, 1, col], store[:, 2, col], store[:, 3, col]
            BR, BP, BZ = B_f(Rr, phi, zz)
            B = np.array([BR, BP, BZ]); Bm = np.sqrt((B**2).sum(0))
            gB = np.array(dBm_f(Rr, phi, zz))
            ra = np.array([dR, 0*dR, dz])
            gpsi_v = np.cross(ra, B, axis=0)
            gpsi = np.sqrt((gpsi_v**2).sum(0))
            gkg = (np.cross(B, gB, axis=0)*gpsi_v).sum(0)/Bm**2
            dsB = Rr/BP          # ds/B per dphi = 1/B^phi
            parts_in.append((dsB, Bm, gpsi, gkg))
        bmin = min(p[1].min() for p in parts_in); bmax = max(p[1].max() for p in parts_in)
        bgrid = np.linspace(bmin, bmax, nb + 2)[1:-1]
        parts = [nemov_sums(dphi, *p, bgrid) for p in parts_in]
        ee, e32 = eps_eff_from(parts, bgrid)
        # half-length check (convergence of the L -> infinity limit)
        half = len(phi)//2
        parts_h = [nemov_sums(dphi, *(a[:half] for a in p), bgrid) for p in parts_in]
        eh, _ = eps_eff_from(parts_h, bgrid)
        drift = max(np.abs(p[2]).max()/np.abs(p[2][:2*NS]).max() for p in parts_in)
        nwell = sum(p[3] for p in parts).max()
        print(f"r = {r:.4f} iota = {io[i]:.6f}: eps_eff = {ee:.4f} (half length {eh:.4f});  "
              f"|B| in [{bmin:.3f}, {bmax:.3f}], mirror ratio (Bmax-Bmin)/(Bmax+Bmin) = "
              f"{(bmax-bmin)/(bmax+bmin):.3f};  max wells/b' = {nwell};  |grad psi| growth {drift:.3f}",
              flush=True)
        results.append(dict(r=float(r), iota=float(io[i]), eps_eff=float(ee), eps_eff_half=float(eh),
                            bmin=float(bmin), bmax=float(bmax)))
    return results


if __name__ == '__main__':
    nt = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    rA = 0.13073386650096105
    rs = np.array([0.05, 0.10, rA, 0.20, 0.287, 0.36])
    res = run(rs, nt)
    json.dump(res, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'eps_eff_summary.json'), 'w'),
              indent=1)
