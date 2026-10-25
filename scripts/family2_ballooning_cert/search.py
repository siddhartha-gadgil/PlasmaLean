#!/usr/bin/env python3
"""UNTRUSTED search for the family-2 ballooning surface certificate (NOT part of the trusted base).

Nothing here is used by Lean as a hypothesis: a certificate found here must be re-checked by a
kernel checker (not yet implemented; see notes/theory/finite-beta-stellarator.md section 9).

Target (Lean `LandremanFamily2Ballooning.family2_stable_of_cert`, after the secular reduction
with a = c0 - Jpar, B . grad Jpar = -q1): on the surface psi = k^2/2 find
    Phi(x, s) = (c0 - Jpar(x)) s + F(x, s)
with, for every x on the surface and every s in R,
    q0 - d (c0 - Jpar) - DF(x, s)(B, d) - Phi^2 / P >= 0,     P = 1/g2 + s^2 g2/B2,
and the s -> +-infinity limit  q0 - d a - a^2 B2/g2 - B . grad f0 >= 0.
F is the ansatz of `model.Model` (B-splines in a tip-clustering angle theta and zeta, rational in
s with scaled widths u = s/(sigma |B|/g2) and absolute widths).

Method: c0 at the flux-surface-average optimum of the tail condition; second-order-cone
programme (Clarabel) maximising the normalised margin, with an ACTIVE SET of (x, s) samples:
start from a coarse sample set, check the defect on a dense candidate set, add the worst
violations, repeat.  Each solve is kept below `--max-nnz` nonzeros (memory ~ 150 bytes/nnz).

Usage:
  search.py tail K [--NT 128 --NZ 16]                 tail LP only (margin in units 1e-4)
  search.py search K --out CERT.json [options]       full search (skips if CERT.json exists)
  search.py check CERT.json [--fine 2]               dense re-check of a certificate
  search.py band KLO KHI NK --outdir DIR [--jobs J]  `search` on NK surfaces in parallel
Requires numpy, scipy, clarabel.
"""
import argparse
import json
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model as M  # noqa: E402


def grid(md, mT, mZ, o1=0.5, o2=0.5):
    th = 2 * np.pi * (np.arange(mT) + o1) / mT
    ze = np.pi * (np.arange(mZ) + o2) / mZ
    TH, ZE = np.meshgrid(th, ze, indexing='ij')
    return md.points(TH.ravel(), ZE.ravel())


def s_candidates(D, umin=-2, umax=4, nu=19, smin=-5, smax=0, ns=11):
    """Candidate s-values per point: scaled (s = w u) and absolute; shape (n, m)."""
    w = np.sqrt(D['B2']) / D['g2']
    U = np.concatenate([[0.0], np.outer([1, -1], np.logspace(umin, umax, nu)).ravel()])
    Sa = np.outer([1, -1], np.logspace(smin, smax, ns)).ravel()
    n = len(w)
    return np.concatenate([w[:, None] * U[None, :], np.tile(Sa, (n, 1))], axis=1)


def sub(D, idx):
    """Restriction of the point data to the indices idx."""
    out = {}
    for key, v in D.items():
        if key in ('X', 'DX'):
            out[key] = v[idx]
        elif key == 'x':
            out[key] = v[:, idx]
        elif isinstance(v, np.ndarray) and v.ndim == 1 and len(v) == len(D['d']):
            out[key] = v[idx]
        else:
            out[key] = v
    return out


def tail_cmd(a):
    md = M.Model(a.k, a.epsm, a.NT, a.NZ, [])
    c0, avg = M.c0_tail_opt(a.k)
    D = grid(md, 3 * a.NT, 3 * a.NZ)
    t = time.time()
    f0, m = M.tail_lp(md, D, c0)
    print(json.dumps(dict(k=a.k, NT=a.NT, NZ=a.NZ, c0=c0, avg_margin=avg, lp_margin_1e4=m,
                          time=time.time() - t)))


def make_model(cfg):
    return M.Model(cfg['k'], cfg['epsm'], cfg['NT'], cfg['NZ'], cfg['sig'], scaled=True,
                   sigabs=cfg['sigabs'])


def dense_check(md, c0, C, fine=2.0, chunk=4000):
    """Minimum normalised defect over a dense grid (offset from the sample grids) and its
    location, plus the tail minimum."""
    D = grid(md, int(fine * 3 * md.NT), int(fine * 3 * md.NZ), 0.31, 0.27)
    Sc = s_candidates(D, -3, 5, 33, -7, 1, 25)
    best = (np.inf, None)
    n = len(D['d'])
    for i0 in range(0, n, chunk):
        idx = np.arange(i0, min(n, i0 + chunk))
        Dl = sub(D, idx)
        df = md.defect(Dl, c0, C, Sc[idx])
        i, j = np.unravel_index(np.argmin(df), df.shape)
        if df[i, j] < best[0]:
            best = (float(df[i, j]), dict(theta=float(Dl['th'][i]), zeta=float(Dl['ze'][i]),
                                          s=float(Sc[idx][i, j])))
    tail = float(md.tail_defect(D, c0, C).min())
    return dict(min_defect=best[0], at=best[1], tail_min=tail, points=n, s_per_point=Sc.shape[1])


def search(cfg, log=print):
    md = make_model(cfg)
    c0, avg = M.c0_tail_opt(cfg['k'])
    t0 = time.time()
    D = grid(md, int(cfg['ov'] * md.NT), int(cfg['ov'] * md.NZ))
    n = len(D['d'])
    Sc = s_candidates(D)
    per = 3 * (16 * md.nf + 2)
    # initial active set: every point with a few s-values
    w = np.sqrt(D['B2']) / D['g2']
    init = [np.zeros(n), w, -w, np.full(n, 1e-2), np.full(n, -1e-2)]
    if cfg.get('init', 'small') == 'full':
        init += [10 * w, -10 * w, np.full(n, 1e-3), np.full(n, -1e-3)]
    act_i = np.concatenate([np.arange(n)] * len(init))
    act_s = np.concatenate(init)
    hist = []
    c0s, m, C, st = c0, -np.inf, None, ''
    for it in range(cfg['rounds']):
        nnz = len(act_i) * per + n * 3 * 18
        if nnz > cfg['max_nnz']:
            log('active set too large: nnz %.3g' % nnz)
            break
        blocks = [md.rows(D, act_i, act_s), md.tail_rows(D, np.arange(n))]
        c0s, m, C, st = M.solve(md, blocks, cbound=cfg['cbound'], fixed={0: c0}, reg=cfg['reg'])
        # check all candidates at the sample points
        df = md.defect(D, c0s, C, Sc)
        viol = df < max(m, 0) * 0.5
        hist.append(dict(round=it, samples=int(len(act_i)), nnz=int(nnz), status=st,
                         margin=float(m), cand_min=float(df.min()),
                         n_viol=int(viol.sum()), time=time.time() - t0))
        log(json.dumps(hist[-1]))
        if not viol.any():
            break
        # add the worst violated candidate of each violating point, plus up to `add` more
        order = np.argsort(df, axis=1)
        rows = np.where(viol.any(axis=1))[0]
        new_i = rows
        new_s = Sc[rows, order[rows, 0]]
        extra = np.argwhere(viol)
        if len(extra) > cfg['add']:
            sel = np.argsort(df[viol])[:cfg['add']]
            extra = extra[sel]
        act_i = np.concatenate([act_i, new_i, extra[:, 0]])
        act_s = np.concatenate([act_s, new_s, Sc[extra[:, 0], extra[:, 1]]])
    res = dict(cfg, c0=float(c0s), tail_avg_margin=float(avg), margin=float(m), status=st,
               history=hist, C=np.asarray(C).tolist(), nf=md.nf, nb=md.nb)
    res['dense'] = dense_check(md, c0s, np.asarray(C), cfg['fine'])
    res['time'] = time.time() - t0
    return res


DEFAULTS = dict(epsm=0.05, NT=128, NZ=16, sig=[1.0, 8.0], sigabs=[1e-3, 1e-2], ov=1.5,
                rounds=6, add=4000, max_nnz=1.0e7, cbound=0.05, fine=1.5, reg=1e-2)


def cfg_from(a, k):
    cfg = dict(DEFAULTS)
    cfg['k'] = k
    for key in ('epsm', 'NT', 'NZ', 'ov', 'rounds', 'add', 'max_nnz', 'fine', 'reg', 'cbound'):
        if getattr(a, key, None) is not None:
            cfg[key] = type(DEFAULTS[key])(getattr(a, key))
    if getattr(a, 'sig', None):
        cfg['sig'] = [float(v) for v in a.sig.split(',') if v]
    if getattr(a, 'sigabs', None):
        cfg['sigabs'] = [float(v) for v in a.sigabs.split(',') if v]
    return cfg


def run_one(args):
    cfg, out = args
    if os.path.exists(out):
        return out, 'exists'
    res = search(cfg, log=lambda s: print('[k=%g] %s' % (cfg['k'], s), flush=True))
    tmp = out + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(res, f)
    os.replace(tmp, out)
    return out, 'margin %.4g dense %.4g' % (res['margin'], res['dense']['min_defect'])


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sp_ = p.add_subparsers(dest='cmd', required=True)
    for name in ('tail', 'search', 'band'):
        q = sp_.add_parser(name)
        if name == 'band':
            q.add_argument('klo', type=float)
            q.add_argument('khi', type=float)
            q.add_argument('nk', type=int)
            q.add_argument('--outdir', required=True)
            q.add_argument('--jobs', type=int, default=1)
        else:
            q.add_argument('k', type=float)
        for opt in ('epsm', 'NT', 'NZ', 'ov', 'rounds', 'add', 'max_nnz', 'fine', 'sig', 'sigabs', 'reg', 'cbound'):
            q.add_argument('--' + opt)
        if name == 'search':
            q.add_argument('--out', required=True)
    q = sp_.add_parser('check')
    q.add_argument('cert')
    q.add_argument('--fine', type=float, default=2.0)
    a = p.parse_args()
    if a.cmd == 'tail':
        a.epsm = float(a.epsm or DEFAULTS['epsm'])
        a.NT = int(a.NT or DEFAULTS['NT'])
        a.NZ = int(a.NZ or DEFAULTS['NZ'])
        tail_cmd(a)
    elif a.cmd == 'search':
        print(run_one((cfg_from(a, a.k), a.out)))
    elif a.cmd == 'band':
        os.makedirs(a.outdir, exist_ok=True)
        ks = np.linspace(a.klo, a.khi, a.nk) if a.nk > 1 else np.array([a.klo])
        jobs = [(cfg_from(a, float(k)), os.path.join(a.outdir, 'cert_k%.4f.json' % k)) for k in ks]
        if a.jobs > 1:
            import multiprocessing as mp
            with mp.get_context('spawn').Pool(min(a.jobs, len(jobs))) as pool:
                for r in pool.imap_unordered(run_one, jobs):
                    print(r, flush=True)
        else:
            for j in jobs:
                print(run_one(j), flush=True)
    elif a.cmd == 'check':
        res = json.load(open(a.cert))
        md = make_model(res)
        print(json.dumps(dense_check(md, res['c0'], np.array(res['C']), a.fine)))


if __name__ == '__main__':
    main()
