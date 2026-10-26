"""UNTRUSTED: emit the Lean modules of the cubic-interpolation frontier certificate.

usage: cubic_emit.py design.pkl spec.json

`spec.json` gives, per face, the number of w-cells `n` and the t-spacing `dm` (grid lines
`t = m/4096`), the number of line-certificate files, the number of build chains, and `eta`
(scale 2^-40).  The script

* computes every line record with `cubic_cert.line_out4` (bit-for-bit replica of `lineOut4`),
* checks every cell with `cell_ok_full` (replica of `cellOK4`),
* writes `PlasmaLean/Design/PolygonCoilCubicData.lean` (coil and face data),
  `PolygonCoilCubicLinesNN.lean` (line data and `line_cert` certificates, chained to bound the number of
  concurrent build processes), `PolygonCoilCubicCellsF.lean` (cell checks) and
  `PolygonCoilCubicCover.lean` (assembly).

Nothing here is trusted: the Lean kernel re-runs the checker on the emitted data.
"""
import json, math, multiprocessing as mp, os, pickle, sys, time
from cubic_cert import *

HDR = """/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module
"""
OUT = '/Users/gadgil/code/PlasmaLean/PlasmaLean/Design/'


def rec(r):
    return '⟨%s, %d, %d, %d, %d, %d, %d, %d⟩' % ('true' if r[0] else 'false', *r[1:])


def ilist(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def make_grid(dm):
    K = -(-2 * 1697 // dm)
    g0 = -1697 - (K * dm - 2 * 1697) // 2
    return [g0 - dm] + [g0 + k * dm for k in range(K + 1)] + [g0 + K * dm + dm]


def main():
    design, specf = sys.argv[1], sys.argv[2]
    spec = json.load(open(specf))
    reps = load_design(design)
    fils = full_filaments(reps)
    o = offsets(fils)
    segs = all_segs(o, fils)
    nS = sum(len(f) for f in segs)
    faces, grids, datas = [], [], []
    t0 = time.time()
    cache = spec.get('cache')
    if cache and os.path.exists(cache):
        faces, grids, datas, worst_all = pickle.load(open(cache, 'rb'))
    else:
        worst_all = 0
        with mp.Pool(14) as pool:
            for kind in range(4):
                fs = spec['faces'][kind]
                wd, wn = face_wgrid(kind, fs['n'])
                F = Face4(kind, wd, wn, 2000, 1, 1000, 1)
                g = make_grid(fs['dm'])
                Ls, worst, bad = eval_face(o, nS, segs, F, g, 10 ** 15, pool)
                print('face', kind, 'lines', len(g), 'corners', len(g) * len(wn), 'worst',
                      worst / 2 ** 40, 'bad', len(bad), 'time', round(time.time() - t0), flush=True)
                if bad:
                    raise SystemExit('cells fail: %s' % bad[:3])
                faces.append(F)
                grids.append(g)
                datas.append(Ls)
                worst_all = max(worst_all, worst)
        if cache:
            pickle.dump((faces, grids, datas, worst_all), open(cache, 'wb'))
    eta = spec.get('eta') or worst_all
    assert eta >= worst_all
    print('eta', eta, eta / 2 ** 40, flush=True)
    # ---------------------------------------------------------------- data module
    L = [HDR, 'public import PlasmaLean.Design.PolygonCoilCubicCheck',
         'public import PlasmaLean.Design.PolygonCoilData',
         'public import PlasmaLean.Design.PolygonCoilFilsCert', '', '''/-!
# Data of the cubic-interpolation frontier certificate

Literal data produced by the untrusted scripts `scripts/rational_stellarator_coils/
polygon_design_minimax.py` (the coil design), `cubic_cert.py` and `cubic_emit.py`; every use is
checked by the kernel:

* `repKC`, `repVC`: the two representative closed polygonal filaments (%d vertices each, integer
  coordinates at scale `2⁻³²`) and their current numerators (`μ₀I/4π = K/2³²`);
* `filsC`: the full coil set of 8 filaments (the orbits under `{id, Rot_π, σ, Rot_π σ}`,
  `PolygonCoilData.orbit`), `%d` straight segments;
* `offsC`, `filsDC`, `nSC`: the checker offsets, filament data and segment count bound;
* `faceC0`–`faceC3`, `gridC0`–`gridC3`: the faces (with their `w`-grids) and the grid lines
  `t = m/4096` of the four faces of the fundamental frontier piece.
-/''' % (len(reps[0][1]), nS), '', '@[expose] public section', '', 'namespace PlasmaLean.Design.PolygonCoil', '']
    L.append('/-- Current numerators of the representative filaments of the cubic design. -/')
    L.append('def repKC : List Int := %s' % ilist([K for K, _ in reps]))
    L.append('')
    L.append('/-- Vertices of the representative filaments of the cubic design (scale `2⁻³²`). -/')
    L.append('def repVC : List (List (Int × Int × Int)) := [')
    rows = []
    for K, vs in reps:
        rows.append('  [' + ',\n   '.join('(%d, %d, %d)' % v for v in vs) + ']')
    L.append(',\n'.join(rows) + ']')
    L.append('')
    L.append('/-- The coil set of the cubic design: the orbits of the representatives. -/')
    L.append('def filsC : List (Int × List (Int × Int × Int)) :=')
    L.append('  (List.zip repKC repVC).flatMap (fun kv => orbit kv.1 kv.2)')
    L.append('')
    L.append('/-- Offsets of the checker weights of the cubic design. -/')
    L.append(wrap('def offsC : Offs := ⟨%d, %d, %d, %d, %d, %d, %d, %d⟩' % o))
    L.append('')
    L.append('/-- Filament data of the cubic design. -/')
    L.append('def filsDC : List Fil := filsC.map (fun f => mkFil offsC f.1 f.2)')
    L.append('')
    L.append('/-- Literal copy of `filsDC` (checked once by `filsDL_eq`; used by the line checks so that')
    L.append('the segment constants are not recomputed for every line). -/')
    fl = []
    for f in segs:
        vts = ', '.join('⟨%d, %d, %d, %d⟩' % (s['px'], s['py'], s['pz'], s['pp']) for s in f)
        sgs = ', '.join('⟨%d, %d, %d, %d, %d, %d, %d, %d⟩' % ((s['vv'],) + s['w1'] + s['w2'] + (s['kv'],))
                        for s in f)
        fl.append('⟨[' + vts + '],\n  [' + sgs + ']⟩')
    L.append(wrap('def filsDL : List Fil := [' + ',\n '.join(fl) + ']'))
    L.append('')
    L.append('set_option maxRecDepth 100000 in')
    L.append('/-- The literal copy `filsDL` is `filsDC` (explicit certificate `fils_cert`,')
    L.append('`Design/PolygonCoilFilsCert`: one leaf per vertex image, vertex record and segment). -/')
    L.append('theorem filsDL_eq : filsDL = filsDC := by fils_cert')
    L.append('')
    L.append('/-- Segment count bound of the cubic design. -/')
    L.append('def nSC : Nat := %d' % nS)
    L.append('')
    for kind in range(4):
        F, g = faces[kind], grids[kind]
        L.append('/-- Face %d of the cubic certificate (kind, `w`-grid, `hel` bounds). -/' % kind)
        L.append(wrap('def faceC%d : Face4 := ⟨%d, %d, %s, %d, %d, %d, %d⟩' % (
            kind, F.kind, F.wd, ilist(F.wn), F.htn, F.htd, F.hwn, F.hwd)))
        L.append('')
        L.append('/-- Grid lines `m` (`t = m/4096`) of face %d. -/' % kind)
        L.append(wrap('def gridC%d : List Int := %s' % (kind, ilist(g))))
        L.append('')
    L.append('/-- The certified error numerator of the cubic certificate (`η = etaC·2⁻⁴⁰`). -/')
    L.append('def etaC : Nat := %d' % eta)
    L.append('')
    L.append('end PlasmaLean.Design.PolygonCoil')
    open(OUT + 'PolygonCoilCubicData.lean', 'w').write('\n'.join(L) + '\n')
    # ---------------------------------------------------------------- line modules
    items = []
    for kind in range(4):
        g = grids[kind]
        for k in range(len(g)):
            items.append((kind, k, line_params(g, k), datas[kind][k]))
    nfiles = spec['line_files']
    nchains = spec['chains']
    cost = [len(it[3]) for it in items]
    tot = sum(cost)
    chunks, cur, acc = [], [], 0
    for it, c in zip(items, cost):
        cur.append(it)
        acc += c
        if acc >= tot * (len(chunks) + 1) / nfiles and len(chunks) < nfiles - 1:
            chunks.append(cur)
            cur = []
    if cur:
        chunks.append(cur)
    names = []
    for c, chunk in enumerate(chunks):
        name = 'PolygonCoilCubicLines%02d' % c
        names.append(name)
        prev = c - nchains
        imp = 'public import PlasmaLean.Design.PolygonCoilCubicData'
        imp += '\npublic import PlasmaLean.Design.PolygonCoilCubicLineCert'
        if prev >= 0:
            imp += '\npublic import PlasmaLean.Design.' + names[prev]
        T = [HDR, imp, '', '''/-!
# Cubic frontier certificate: grid lines, part %d

For each grid line `m` of a face (with its `t`-neighbours), the literal corner records `dCF_k`
and their per-segment certificate (`line_cert`, `Design/PolygonCoilCubicLineCert`: one leaf per
vertex step, per block of three segment and remainder steps, and per corner assembly). (Modules
are chained only to bound the number of concurrent build processes.)
-/''' % c, '', '@[expose] public section', '', 'namespace PlasmaLean.Design.PolygonCoil', '']
        for (kind, k, p, Ls) in chunk:
            T.append('/-- Corner records of grid line %d of face %d. -/' % (k, kind))
            T.append('def dC%d_%d : List CRec := [' % (kind, k) + ',\n  '.join(rec(r) for r in Ls) + ']')
            T.append('')
            T.append('/-- Certificate of grid line %d of face %d. -/' % (k, kind))
            T.append(wrap('theorem lC%d_%d : lineOut4 offsC nSC filsDL faceC%d (%d) (%d) (%d) (%d) = dC%d_%d := by'
                          % (kind, k, kind, p[0], p[1], p[2], p[3], kind, k)))
            T.append('  line_cert')
            T.append('')
        T.append('end PlasmaLean.Design.PolygonCoil')
        open(OUT + name + '.lean', 'w').write('\n'.join(T) + '\n')
    # ---------------------------------------------------------------- cells and cover
    lines_of = {}
    for c, chunk in enumerate(chunks):
        for (kind, k, p, Ls) in chunk:
            lines_of[(kind, k)] = names[c]
    for kind in range(4):
        emit_cells(kind, faces[kind], grids[kind], eta,
                   sorted(set(lines_of[(kind, k)] for k in range(len(grids[kind])))))
    emit_cover(faces, grids, eta)
    json.dump(dict(eta=eta, grids=grids, names=names, lines_of={'%d_%d' % k: v for k, v in lines_of.items()},
                   nlines=[len(g) for g in grids], wn=[F.wn for F in faces], wd=[F.wd for F in faces]),
              open('/tmp/pd2/cubic_emit_meta.json', 'w'))
    print('emitted', len(chunks), 'line files; total time', round(time.time() - t0))


def emit_cells(k, F, g, eta, mods):
    n = len(g)
    T = [HDR, '\n'.join('public import PlasmaLean.Design.' + m for m in mods),
         'public import PlasmaLean.Design.PolygonCoilCubicFrontier',
         'public import PlasmaLean.Certificates.BoolCert',
         'public import PlasmaLean.Certificates.KernelFact', '', '''/-!
# Cubic frontier certificate: the cells and the cover of face %d

* `rowCF_i`: `cellsRow4` on the records of the grid lines `i, …, i+3` of face `F`, by an explicit
  `BCert` certificate (`bool_cert`, `Certificates/BoolCert`): one `&&` step per cell, and per cell
  its geometric conditions and its error bound `Nat.ble … η` as kernel-checked comparison leaves;
* `cellsCF`: all cells of the face pass (`cellsAll4`, assembled from the rows);
* `linesC_F`, `rowsC_F`: the facts certified by the line checks `lCF_k` (`lineOut4_sound`);
* `coverC_F`, `faceCovC_F`: the certified bound on the face (`face_sound`).
-/''' % k, '', 'public section', '', 'namespace PlasmaLean.Design.PolygonCoil', '',
         'open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator Set Real',
         '  PlasmaLean.Certificates.BoolCert', '']
    T.append('/-- The line records of face %d. -/' % k)
    T.append('@[expose]')
    T.append(wrap('def dataC%d : List (List CRec) := [' % k
                                 + ', '.join('dC%d_%d' % (k, i) for i in range(n)) + ']'))
    T.append('')
    for i in range(n - 3):
        T.append('/-- The cells of row %d of face %d pass. -/' % (i, k))
        T.append(wrap('theorem rowC%d_%d : cellsRow4 faceC%d etaC (%d) (%d) (%d) (%d) dC%d_%d dC%d_%d dC%d_%d dC%d_%d'
                      ' faceC%d.wn = true := by' % (k, i, k, g[i], g[i + 1], g[i + 2], g[i + 3], k, i, k, i + 1,
                                                    k, i + 2, k, i + 3, k)))
        T.append('  bool_cert')
        T.append('')
    T.append('/-- **All cells of face %d pass** (`η = %d·2⁻⁴⁰`). -/' % (k, eta))
    T.append('theorem cellsC%d : cellsAll4 etaC faceC%d gridC%d dataC%d = true :=' % (k, k, k, k))
    T.append(wrap('  ' + ''.join('cellsAll4_cons rowC%d_%d <| ' % (k, i) for i in range(n - 3)) + 'cellsAll4_end'))
    T.append('')
    T.append('/-- Face %d carries the proved `hel` constants. -/' % k)
    T.append('theorem face4OK_%d : Face4OK faceC%d := by' % (k, k))
    T.append('  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [faceC%d] <;> norm_num' % k)
    T.append('')
    T.append('/-- The line facts of face %d. -/' % k)
    T.append('theorem linesC_%d : List.Forall₂ (fun m L => List.Forall₂ (LVal filsC faceC%d m) faceC%d.wn L ∧'
             % (k, k, k))
    T.append('    QuadP (LW filsC faceC%d m) faceC%d.wn L) gridC%d dataC%d :=' % (k, k, k, k))
    body = ''.join('.cons (line_facts face4OK_%d lC%d_%d).1 <| ' % (k, k, i) for i in range(n)) + '.nil'
    T.append(wrap('  ' + body))
    T.append('')
    T.append('/-- The strip facts of face %d. -/' % k)
    T.append('theorem rowsC_%d : RowsT filsC faceC%d gridC%d dataC%d :=' % (k, k, k, k))
    body = ''.join('rowsT_cons (line_facts face4OK_%d lC%d_%d).2 <| ' % (k, k, i) for i in range(1, n - 2)) \
        + 'rowsT_end'
    T.append(wrap('  ' + body))
    T.append('')
    wlo, whi = F.wn[1], F.wn[-2]
    T.append('set_option maxRecDepth 20000 in')
    T.append('/-- **The certified bound on face %d.** -/' % k)
    T.append('theorem coverC_%d : RectGood filsC %d etaC (((%d : ℤ) : ℝ) / 4096) (((%d : ℤ) : ℝ) / 4096)'
             % (k, k, g[1], g[-2]))
    T.append('    (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) (((%d : ℤ) : ℝ) / ((%d : ℕ) : ℝ)) := by'
             % (wlo, F.wd, whi, F.wd))
    T.append('  have h := face_sound filsC faceC%d face4OK_%d etaC (by kernel_fact) gridC%d dataC%d linesC_%d'
             % (k, k, k, k, k))
    T.append('    rowsC_%d cellsC%d (by kernel_fact)' % (k, k))
    T.append('  rw [show gridC%d.length = %d by kernel_fact, show faceC%d.wn.length = %d by kernel_fact]'
             ' at h' % (k, n, k, len(F.wn)))
    T.append('  rwa [show gridC%d.getD 1 0 = %d by kernel_fact,' % (k, g[1]))
    T.append('    show gridC%d.getD %d 0 = %d by kernel_fact,' % (k, n - 2, g[-2]))
    T.append('    show faceC%d.wn.getD 1 0 = %d by kernel_fact,' % (k, wlo))
    T.append('    show faceC%d.wn.getD %d 0 = %d by kernel_fact,' % (k, len(F.wn) - 2, whi))
    T.append('    show faceC%d.wd = %d from rfl, show faceC%d.kind = %d from rfl] at h' % (k, F.wd, k, k))
    T.append('')
    T.append('/-- **The cover of face %d.** -/' % k)
    T.append('theorem faceCovC_%d : FaceCovC %d :=' % (k, k))
    T.append('  ⟨_, _, _, _, coverC_%d, by norm_num, by norm_num, by norm_num [faceLoC, aF],' % k)
    T.append('    by norm_num [faceHiC, aF]⟩')
    T.append('')
    T.append('end PlasmaLean.Design.PolygonCoil')
    open(OUT + 'PolygonCoilCubicCells%d.lean' % k, 'w').write('\n'.join(T) + '\n')


def emit_cover(faces, grids, eta):
    T = [HDR, '\n'.join('public import PlasmaLean.Design.PolygonCoilCubicCells%d' % k for k in range(4)),
         'public import PlasmaLean.Design.PolygonCoilCubicConfined', '', '''/-!
# Confinement over 52 transits for the concrete cubic-certified coil set

Assembles the four face covers `faceCovC_F` (`Design/PolygonCoilCubicCellsF`) into `coversC` and
applies `coil_confined_of_coversC` (`Design/PolygonCoilCubicConfined`).
-/''', '', 'public section', '', 'namespace PlasmaLean.Design.PolygonCoil', '',
         'open PlasmaLean.Fields PlasmaLean.Design.RationalStellarator',
         '  PlasmaLean.Design.RationalStellarator.Coils PlasmaLean.Design.RationalStellarator.CoilsTF',
         '  PlasmaLean.Design.RationalStellarator.Confined Set Real', '']
    T.append('''/-- **The four face covers** (kernel certificates, `η = etaC·2⁻⁴⁰`). -/
theorem coversC : CoversC := ⟨faceCovC_0, faceCovC_1, faceCovC_2, faceCovC_3⟩

/-- **Confinement over 52 transits in the field of a concrete polygonal coil set.** Every field
line of the coil field `tfField + polyCoilFieldC` (the closed TF filament plus the 8 closed
polygonal helical filaments `filsC`, 192 straight segments, `Design/PolygonCoilCubicData`) on
`[0, 8·52]` starting in the start tube stays in the confinement tube `T` and its toroidal angle
advances by at least `2π·52` (52 transits).

Conditional on the field line: `γ` is assumed to solve the field-line equation on `[0, 8·52]`
(existence is not proved here). The certified winding error on the frontier is
`etaRC = etaC·2⁻⁴⁰ ≈ 3.221 × 10⁻⁶`. -/
theorem coil_stellarator_confined_concrete_N {γ : ℝ → Space}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (8 * 52), HasDerivAt γ (coilField polyCoilFieldC (γ t)) t)
    (h0 : γ 0 ∈ startTube) :
    (∀ s ∈ Icc (0 : ℝ) (8 * 52), γ s ∈ tubeT) ∧
      2 * π * 52 ≤ ∫ u in (0 : ℝ)..(8 * 52), phiRateOf (coilField polyCoilFieldC) (γ u) :=
  coil_confined_of_coversC coversC hγ h0
''')
    T.append('end PlasmaLean.Design.PolygonCoil')
    open(OUT + 'PolygonCoilCubicCover.lean', 'w').write('\n'.join(T) + '\n')


def wrap(s, width=100):
    """break a long term at spaces into lines of at most `width` characters (indent 4)."""
    out, cur = [], ''
    for tok in s.split(' '):
        if cur and len(cur) + 1 + len(tok) > width:
            out.append(cur)
            cur = '    ' + tok
        else:
            cur = tok if not cur else cur + ' ' + tok
    out.append(cur)
    return '\n'.join(out)


if __name__ == '__main__':
    main()
