"""UNTRUSTED: emit the Lean data module `PlasmaLean/Design/PolygonCoilData.lean` and the
certificate chunk modules from a design and the per-face grids (see polygon_cert.py)."""
import sys, pickle
sys.path.insert(0, '.')
from polygon_cert import *

def emit_data(reps, o, grids, fn):
    L = []
    L.append('''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.PolygonCoilCheck

/-!
# Data of the polygonal helical coil set and of the frontier grids

Literal data (produced by the untrusted scripts `scripts/rational_stellarator_coils/
polygon_design.py`, `polygon_cert.py`, `polygon_emit.py`; every use is checked):

* `repK`, `repV`: the two representative closed polygonal filaments (16 vertices each, integer
  coordinates at scale `2⁻³²`) and their current numerators `K` (`μ₀I/4π = K/2³²`).
* `fils`: the full coil set of 8 filaments, the images of the representatives under the
  symmetry group `{id, Rot_π, σ, Rot_π σ}` with currents `K, K, -K, -K`.
* `offs`: the offsets of the checker weights; `filsD`: the filament data of the checker.
* `gridF`, `faceF` (`F = 0, …, 3`): the grid lines `m` (`t = m/4096`, `φ = 2 arctan t`) and the
  `w`-grids of the four faces of the fundamental frontier piece.
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil
''')
    L.append('/-- Current numerators of the representative filaments. -/')
    L.append('def repK : List Int := [%s]' % ', '.join(str(K) for K, _ in reps))
    L.append('')
    L.append('/-- Vertices of the representative filaments (scale `2⁻³²`). -/')
    L.append('def repV : List (List (Int × Int × Int)) := [')
    rows = []
    for K, vs in reps:
        rows.append('  [' + ',\n   '.join('(%d, %d, %d)' % v for v in vs) + ']')
    L.append(',\n'.join(rows) + ']')
    L.append('''
/-- Rotation by `π` about the `z`-axis on integer points. -/
def gRi (p : Int × Int × Int) : Int × Int × Int := (-p.1, -p.2.1, p.2.2)
/-- The stellarator symmetry `σ(x, y, z) = (y, x, -z)` on integer points. -/
def gSi (p : Int × Int × Int) : Int × Int × Int := (p.2.1, p.1, -p.2.2)

/-- The orbit of one representative filament: `id, Rot_π` with current `K`, `σ, Rot_π σ` with
current `-K`. -/
def orbit (K : Int) (vs : List (Int × Int × Int)) : List (Int × List (Int × Int × Int)) :=
  [(K, vs), (K, vs.map gRi), (-K, vs.map gSi), (-K, vs.map (fun p => gRi (gSi p)))]

/-- The full coil set (8 filaments). -/
def fils : List (Int × List (Int × Int × Int)) :=
  (List.zip repK repV).flatMap (fun kv => orbit kv.1 kv.2)
''')
    L.append('/-- Offsets of the checker weights. -/')
    L.append('def offs : Offs := ⟨%d, %d, %d, %d, %d, %d, %d, %d⟩' % o)
    L.append('''
/-- Filament data (vertex records and segment constants) of the coil set. -/
def filsD : List Fil := fils.map (fun f => mkFil offs f.1 f.2)

/-- Validity of the integer data (checked once). -/
def dataOK : Bool := fils.all (fun f => filOK offs f.1 f.2)
''')
    HELH = {0: (19, 25, 223, 100), 1: (3, 2, 19, 5), 2: (147, 100, 17, 2), 3: (147, 100, 17, 2)}
    for face in range(4):
        g = grids[face]
        L.append('/-- Grid lines `m` of face %d (`t = m/4096`). -/' % face)
        L.append('def grid%d : List Nat := [%s]' % (face, ', '.join(str(m) for m in g['ms'])))
        L.append('/-- Face %d: kind, `w`-grid `wn/wd`, and the `hel` bounds. -/' % face)
        h = HELH[face]
        L.append('def face%d : Face := ⟨%d, %d, [%s], %d, %d, %d, %d⟩' % (face, face, g['wd'], ', '.join(str(w) for w in g['wn']), h[0], h[1], h[2], h[3]))
        L.append('')
    L.append('end PlasmaLean.Design.PolygonCoil')
    open(fn, 'w').write('\n'.join(L) + '\n')

if __name__ == "__main__":
    reps = load_design(sys.argv[1]); fils = full_filaments(reps); o = offsets(fils)
    grids = {}
    for face in range(4):
        grids[face] = pickle.load(open(sys.argv[2 + face], 'rb'))
    emit_data(reps, o, grids, sys.argv[6])

CH = 4   # line pairs per chunk

def emit_certs(grids, nfiles, base):
    """distribute chunk theorems over nfiles modules; module k imports module k-1 within its chain
    (chains: files 0..nfiles-1 split into nfiles//2 chains of length 2)."""
    items = []
    for face in range(4):
        n = len(grids[face]['ms'])
        nch = (n - 1 + CH - 1) // CH
        for i in range(nch):
            items.append((face, i, min(CH, n - 1 - CH * i)))
    # balance by number of lines
    loads = [0] * nfiles; buckets = [[] for _ in range(nfiles)]
    for it in items:
        k = loads.index(min(loads)); buckets[k].append(it); loads[k] += it[2] + 1
    nchain = nfiles // 2
    for k in range(nfiles):
        chain, pos = k % nchain, k // nchain
        imp = 'PlasmaLean.Design.PolygonCoilDataL' if pos == 0 else '%s%02d' % (base.replace('/', '.'), k - nchain)
        L = ['''/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import %s

/-!
# Polygonal-coil frontier certificate, part %d

Explicit certificates (`chunk_cert`, `Design/PolygonCoilChunkCert`: one leaf per vertex step,
per block of three segment steps, per corner assembly and per cell) of the checker `checkChunk`
of `Design/PolygonCoilCheck` on chunks of %d consecutive line pairs of the face grids of
`Design/PolygonCoilData` (chunk `i` of face `f` is `(gridF.drop (%d * i)).take %d`), with the
filament data read from the literal `filsDLB` (`filsDLB_eq`) and the face checks `faceChkF`.
Each theorem certifies, through `Design/PolygonCoilSoundA`-`D`, the frontier error bound on the
corresponding cells. (Modules are chained pairwise only to bound the number of concurrent
build processes.)
-/

@[expose] public section

namespace PlasmaLean.Design.PolygonCoil
''' % (imp, k, CH, CH, CH + 1)]
        for (face, i, _) in buckets[k]:
            L.append('/-- Certificate chunk %d of face %d. -/' % (i, face))
            L.append('theorem cert_%d_%d : checkChunk offs filsD face%d ((grid%d.drop (%d * %d)).take %d) = true := by\n  chunk_cert filsDLB_eq faceChk%d\n' % (face, i, face, face, CH, i, CH + 1, face))
        L.append('end PlasmaLean.Design.PolygonCoil')
        open('/Users/gadgil/code/PlasmaLean/%s%02d.lean' % (base, k), 'w').write('\n'.join(L) + '\n')
    return items
