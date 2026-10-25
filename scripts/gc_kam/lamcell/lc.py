"""UNTRUSTED helper of the pitch-cell pipeline (scripts/gc_kam/lamcell): configuration and runner.

A pitch cell is `lam = mu B0 / E in [LAM_LO, LAM_HI]` at rho0 = 1/256 (3.5 MeV alphas at the design
B0 R0).  The certified pipeline of the cell [0, 1/16] (scripts/gc_kam/lam_*.py, Lean modules
Design/RationalStellaratorGCMu*) is re-used unchanged; the scripts of this directory run those
generators with a few textual patches (`run_patched`): the parameter variable `r = 64 + cos theta'`
now encodes `lam = LAM_LO + (r - 63)/LAMDEN = (r - R0)/LAMDEN` with `LAMDEN = 2/(LAM_HI - LAM_LO)`
and `R0 = 63 - LAMDEN LAM_LO`, hard-coded paths are replaced by repository-relative ones and all
output goes to the work directory (never over existing Lean files).

Environment:
  LAM_LO, LAM_HI   cell endpoints (rationals, default 1/16 and 1/8); LAMDEN and LAMDEN*LAM_LO must be
                   integers, 0 <= LAM_LO < LAM_HI <= 1/4
  LAM_TAG          module tag: Lean modules Design/RationalStellaratorGCMu<TAG>*, namespace
                   PlasmaLean.Design.RationalStellaratorGC.Mu<TAG> (default '2')
  LAM_WORK         work directory (default $TMPDIR/lamcell-<TAG>)
Every patch is asserted to apply, so a change of the original generators fails loudly.
"""
import os, sys, re
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
GCK = os.path.dirname(HERE)
REPO = os.path.dirname(os.path.dirname(GCK))
KO = os.path.join(REPO, 'scripts', 'kam_oracle')
DESIGN = os.path.join(REPO, 'PlasmaLean', 'Design') + '/'
SHIM = os.path.join(HERE, 'shim')

LO = Fr(os.environ.get('LAM_LO', '1/16'))
HI = Fr(os.environ.get('LAM_HI', '1/8'))
TAG = os.environ.get('LAM_TAG', '2')
assert 0 <= LO < HI <= Fr(1, 4), ('cell must satisfy 0 <= LAM_LO < LAM_HI <= 1/4', LO, HI)
_den = Fr(2) / (HI - LO)
assert _den.denominator == 1, ('2/(LAM_HI - LAM_LO) must be an integer', _den)
LAMDEN = int(_den)
assert (LAMDEN * LO).denominator == 1, ('LAMDEN * LAM_LO must be an integer', LAMDEN * LO)
KOFF = 1 + int(LAMDEN * LO)          # lam = (KOFF + cos theta') / LAMDEN
R0 = 63 - int(LAMDEN * LO)           # lam = (r - R0) / LAMDEN, r = 64 + cos theta'
WORK = os.environ.get('LAM_WORK') or os.path.join(os.environ.get('TMPDIR', '/tmp'), 'lamcell-' + TAG)
PRE = 'RationalStellaratorGCMu' + TAG
SUBNS = 'Mu' + TAG
os.makedirs(WORK, exist_ok=True)


def q2lean(q):
    """a nonnegative rational as a Lean real literal `a / b`."""
    q = Fr(q)
    return '%d' % q.numerator if q.denominator == 1 else '%d / %d' % (q.numerator, q.denominator)


def setup_path():
    for p in (KO, GCK, SHIM):
        if p in sys.path:
            sys.path.remove(p)
        sys.path.insert(0, p)
    # the shim gcmodel (repository-relative source path) must win over scripts/gc_kam/gcmodel.py
    import importlib.util
    if 'gcmodel' not in sys.modules or not getattr(sys.modules['gcmodel'], '__lamcell__', False):
        spec = importlib.util.spec_from_file_location('gcmodel', os.path.join(SHIM, 'gcmodel.py'))
        mod = importlib.util.module_from_spec(spec)
        sys.modules['gcmodel'] = mod
        spec.loader.exec_module(mod)


def patch(src, reps, name):
    for a, b in reps:
        n = src.count(a)
        assert n >= 1, ('%s: patch target not found' % name, a[:120])
        src = src.replace(a, b)
    return src


def run_patched(script, reps, argv, extra_globals=None):
    """Run scripts/gc_kam/<script> as __main__ with the textual replacements `reps`."""
    setup_path()
    path = os.path.join(GCK, script)
    src = patch(open(path).read(), reps, script)
    g = {'__name__': '__main__', '__file__': path, '__builtins__': __builtins__}
    if extra_globals:
        g.update(extra_globals)
    old = sys.argv
    sys.argv = [path] + list(argv)
    try:
        exec(compile(src, path + ' (lamcell-patched)', 'exec'), g)
    finally:
        sys.argv = old
    return g


# ------------------------------------------------------------------ stored Lean data (SliceData)
PAT = re.compile(r'def (\w+) : List SliceData := \[(.*?)\]\n', re.S)
SL = re.compile(r'⟨(\d+), (\d+), (\d+),\s*0x([0-9a-f]+),\s*0x([0-9a-f]+), (\d+), (\d+)⟩')


def read_slices(modules):
    """The `List SliceData` literals of generated Lean data modules, as fam_ball.Slice objects."""
    setup_path()
    from fam_ball import Slice
    out = {}
    for m in modules:
        txt = open(DESIGN + m + '.lean').read()
        for name, body in PAT.findall(txt):
            sl = []
            for t in SL.findall(body):
                Nj, Mj, Fj, blk, col, k1, k2 = [int(x, 16) if i in (3, 4) else int(x) for i, x in enumerate(t)]
                W = Fj * Nj
                rows = [(blk >> (W * r)) % (1 << W) if W > 0 else 0 for r in range(2 * Mj + 1)]
                s = Slice(Nj, Mj, Fj, rows, col)
                assert s.blk == blk and (s.k1, s.k2) == (k1, k2), (Nj, Mj)
                sl.append(s)
            out[name] = sl
    return out
