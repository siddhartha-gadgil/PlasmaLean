"""Kernel-check the original 52-bit panel arithmetic and the archived 20/26/20-bit digits."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
import gzip
import json
from math import ceil, floor
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_action_pilot import PanelPolynomial, sqrt_nonnegative
from bounce_launch_box import Box, S
from bounce_mirror_pilot import HEIGHTS, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal
from replay_physical_action_archive import segment
from screen_physical_action_panels import packed_rows
from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import DESIGN, digest, save


PACKAGE = 'NativeTickCache'
FIELDS = ('den', 'r8', 'r16', 'u', 'num')


def box_literal(box):
    return f'⟨{box.lo}, {box.hi}⟩'


def panel_equality(field, poly, time, index):
    """Expose each Horner product and let Lean check one exact multiplication at a time."""
    val = Box(0, 0)
    term = 'HornerRun.nil'
    for coeff in reversed(poly.coefficients):
        val = coeff + time*val
        term = f'(HornerRun.cons (out := {box_literal(val)}) {term} (by with_unfolding_all rfl))'
    return (f'  have bound_{field} : onPanel models.{field} (timeBox {index}) = '
            f'{box_literal(poly.on(time))} := by\n    rw [clock]\n'
            f'    exact onPanel_of_run coef_{field} err_{field} {term} (by with_unfolding_all rfl)\n')


def physical_models(trace, index, outgoing=None):
    data = polynomial_data()
    enclosure = segment(trace, index)
    if outgoing is not None:
        from dataclasses import replace
        enclosure = replace(enclosure, outgoing_radius=outgoing)
    tube, angles, fields = enclosure.fields(data)
    d, nr, nz = fields
    r = tube[0]
    r2 = r*r
    r4 = r2*r2
    r8 = r4*r4
    rd = r*d
    u = rd*rd + nr*nr + nz*nz
    gap, = ShiftedStrength(data).numerators(tube, angles, fields, [HEIGHTS[1]])
    return d, r8, r8*r8, u, -gap


def header(name, imports):
    return ('module\n'+''.join('public import '+dep+'\n' for dep in imports) + f'''
/-! # Original native mirror-action digits -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates Certificates.NativeActionInterval Certificates.MirrorActionQuadrature
open Certificates.TrajectoryTaylorModel DommaschkNativeActionColumns Set
set_option linter.style.longLine false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
''')


def sources(index, backward, paired=False):
    with gzip.open(RECORD, 'rt') as fp:
        traces = json.load(fp)['traces']
    trace, = [v for v in traces if v['direction'] == (-1 if backward else 1)]
    if paired and backward:
        raise ValueError('the reflected proof uses one forward model for both archived records')
    direction = 'Paired' if paired else ('Backward' if backward else 'Forward')
    name = f'DommaschkNativeTicks{direction}{index:03}'
    outgoing = max(v['steps'][index]['physical_radius_out'] for v in traces) if paired else None
    models = physical_models(trace, index, outgoing)
    polys = list(map(PanelPolynomial, models))
    oriented_row = 324-index if backward else 325+index
    original = packed_rows()[oriented_row]
    group, offset = divmod(oriented_row, 16)
    data = name+'Data'
    imports = ['PlasmaLean.Design.DommaschkNativeActionColumns','PlasmaLean.Design.DommaschkActionQ0R470']
    start = header(name, imports)
    start += ('\ndef models : Five Model := ⟨'+',\n  '.join(map(model_literal, models))+'⟩\n'
              +f'abbrev height : ℚ := {HEIGHTS[1]}\n'
              +f'def archive := DommaschkActionQ0R470.slabGroup{group}[{offset}].packed\n'
              +f'def record (n : ℕ) := archive >>> (72 * {"(47-n)" if backward else "n"})\n')
    for field, poly in zip(FIELDS, polys):
        coeffs = ', '.join(map(box_literal, poly.coefficients))
        start += (f'theorem coef_{field} : models.{field}.poly.map rational = [{coeffs}] := '
                  'by with_unfolding_all rfl\n'
                  f'theorem err_{field} : (rational models.{field}.radius).hi = {poly.remainder.hi} := '
                  'by with_unfolding_all rfl\n')
    start += f'end PlasmaLean.Design.{name}\n'
    declarations = [(data, start, [])]
    chunks = []
    for first in range(0, 48, 8):
        chunk = f'{name}Part{first//8}'
        chunks.append(chunk)
        src = header(name, [PACKAGE+'.'+data])
        for n in range(first,first+8):
            t = Box(floor((Fraction(n,24)-1)*S), ceil((Fraction(n+1,24)-1)*S))
            boxes = [poly.on(t) for poly in polys]
            d, r8, r16, u, numer = boxes
            rt = sqrt_nonnegative(u)
            mass = rt/d
            speed = Box(2*S,2*S)*(Box(max(numer.lo,0),max(numer.hi,0)) /
                (r16*(Box.rational(HEIGHTS[1])+rt/r8)))
            p = original >> (72*(47-n if backward else n))
            if (ceil(Fraction(mass.hi*2**20,S)),
                    ceil(Fraction(speed.hi*2**26,S))) != (p%(2**24), (p>>24)%(2**24)):
                raise ValueError(f'{name} panel {n} has changed density or squared-speed ticks')
            src += f'''
theorem panel{n} : ∃ root,
    Checked true (models.map (fun m => onPanel m (timeBox {n}))) root height (record {n}) := by
  let boxes : Five Box := ⟨{", ".join(map(box_literal,boxes))}⟩
  have clock : timeBox {n} = {box_literal(t)} := by with_unfolding_all rfl
{''.join(panel_equality(f, poly, t, n) for f,poly in zip(FIELDS, polys))}  have horner : models.map (fun m => onPanel m (timeBox {n})) = boxes := by
    simp only [Five.map, boxes, {", ".join("bound_"+f for f in FIELDS)}]
  rw [horner]
  refine ⟨{box_literal(rt)}, ?_⟩
  constructor
  · constructor <;> first
    | (intro _; rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl)
    | (rw [← Int.ble'_eq_true]; with_unfolding_all rfl)
  all_goals first | (rw [← Int.blt'_eq_true]; with_unfolding_all rfl) | with_unfolding_all rfl
'''
        declarations.append((chunk, src+f'end PlasmaLean.Design.{name}\n', []))
    end = header(name, [PACKAGE+'.'+c for c in chunks])
    end += '''
theorem checked (n : Fin 48) : ∃ root,
    Checked true (models.map (fun m => onPanel m (timeBox n))) root height (record n) := by
  fin_cases n
''' + ''.join(f'  · exact panel{i}\n' for i in range(48))
    end += '''
/-- The actual decoded columns at an arbitrary point in this directed panel. -/
theorem physical_columns (n : Fin 48) {s R φ z : ℝ}
    (hs : s ∈ Icc (2 * (n:ℝ) / 48 - 1) (2 * ((n:ℝ) + 1) / 48 - 1))
    (hr : 0 < R) (hm : Five.Rel (fun m x => m.Mem s x) models (quantities R φ z height)) :
    DommaschkPhysicalActionPanel.arcDensity R φ z ≤ density (record n) / 1048576 ∧
    max (2 * ((height:ℝ) - magnitude R φ z)) 0 ≤ speedSq (record n) / 67108864 := by
  obtain ⟨root, cert⟩ := checked n
  exact physical hr (by norm_num [height]) cert (five_mem (time_mem hs) hm)
'''
    declarations.append((name, end+f'end PlasmaLean.Design.{name}\n', ['checked','physical_columns']))
    return name, declarations


def check(job):
    index, back, version, env, cache, *mode = job
    name, declarations = sources(index,back,*mode)
    deps = [digest(DESIGN / (m+'.trace')) for m in ('DommaschkActionQ0R470','DommaschkNativeActionColumns')]
    root, rec = compile_modules(cache/name, declarations, [], [version,digest(RECORD),deps], env, PACKAGE)
    out = {k:v for k,v in rec.items() if k != 'artifacts'}
    out.update(index=index, direction=-1 if back else 1, packet_sha256=digest(RECORD), panels=48,
               import_paths=[str(root)])
    save(root/'row.json', out)
    print(f'{name} accepted {rec["key"]}', flush=True)
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--row', type=int, default=16, choices=range(325), metavar='0..324')
    p.add_argument('--direction', type=int, choices=(-1,1))
    p.add_argument('--workers', type=int, choices=(1,2), default=1)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/native-action-columns')
    p.add_argument('--output', type=Path)
    args = p.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'), lean_path=lake('printenv','LEAN_PATH'))
    jobs = [(args.row, sign == -1, version, env, args.cache.resolve()) for sign in (1,-1)
            if args.direction is None or args.direction == sign]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        reports = list(pool.map(check,jobs))
    if args.output:
        save(args.output,reports)


if __name__ == '__main__':
    main()
