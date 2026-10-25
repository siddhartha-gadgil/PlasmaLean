"""UNTRUSTED helper (energy window): read the stored Chebyshev coefficients (`SliceData` literals)
of generated Lean data modules back into `fam_ball.Slice` objects, so that the oracle pipelines can
be re-run on exactly the data already certified in Lean (e.g. the low-resolution family torus of
`Design/RationalStellaratorGCMuDataL`)."""
import re, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'ew_shim'))
from fam_ball import Slice

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'PlasmaLean', 'Design') + '/'
PAT = re.compile(r'def (\w+) : List SliceData := \[(.*?)\]\n', re.S)
SL = re.compile(r'⟨(\d+), (\d+), (\d+),\s*0x([0-9a-f]+),\s*0x([0-9a-f]+), (\d+), (\d+)⟩')


def mkslice(Nj, Mj, Fj, blk, col, k1, k2):
    W = Fj * Nj
    rows = [(blk >> (W * r)) % (1 << W) if W > 0 else 0 for r in range(2 * Mj + 1)]
    s = Slice(Nj, Mj, Fj, rows, col)
    assert s.blk == blk and (s.k1, s.k2) == (k1, k2), (Nj, Mj)
    return s


def read(modules):
    out = {}
    for m in modules:
        txt = open(ROOT + m + '.lean').read()
        for name, body in PAT.findall(txt):
            out[name] = [mkslice(*[int(x, 16) if i in (3, 4) else int(x) for i, x in enumerate(t)])
                         for t in SL.findall(body)]
    return out


if __name__ == '__main__':
    d = read(['RationalStellaratorGCMuDataL'])
    print(len(d), [len(d[k]) for k in ['sdLM_U', 'sdLM_Z', 'sdLM_Uo', 'sdLM_Zo']])
