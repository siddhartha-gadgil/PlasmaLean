"""Bind each archived native action digit to the actual signed field on its entire trial tube."""

import argparse
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from emit_sparse_taylor_slab import ROOT, RECORD
from verify_backward_physical_prefix import compile_modules, union
import verify_native_action_columns as ticks
import verify_native_action_models as models
from verify_physical_trace_slabs import digest, save


PACKAGE = 'NativePhysicalPanelCache'


def source(index, backward, model, tick):
    direction = 'Backward' if backward else 'Forward'
    name = f'DommaschkNativePhysicalPanels{direction}{index:03d}'
    phi = '(-t)' if backward else 't'
    src = ticks.header(name, [models.OUTPUT_PACKAGE+'.'+model, ticks.PACKAGE+'.'+tick])
    src += f'''
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkBounceField
open DommaschkPhysicalActionPanel

abbrev row := {model}.row
abbrev record := {tick}.record

/-- At each physical state in the signed outgoing tube, the original panel bounds arclength
and squared parallel speed, and supplies its correctly rounded speed witness. -/
theorem physical {{prev : Certificates.PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}} (n : Fin 48)
    (ht : t ∈ Icc ({index}/64:ℝ) ({index+1}/64))
    (hx : x ∈ (physicalSlab prev row ({index}/64)).tube t)
    (hs : 128*t-{2*index+1} ∈ Icc (2*(n:ℝ)/48-1) (2*((n:ℝ)+1)/48-1)) :
    arcDensity (x 0) {phi} (x 1) ≤ density (record n) / 1048576 ∧
    max (2*(({tick}.height:ℝ) - strength {phi} x)) 0 ≤ speedSq (record n) / 67108864 ∧
    rootTest true (record n) = true ∧ rootNeighbor true (record n) = true := by
  obtain ⟨hr,hd,h8,h16,hu,hn⟩ := {model}.physical ht hx
  rw [← DommaschkNativeActionGeometry.squared_numerator hr {phi}] at hu
  have mem : Five.Rel (fun m z => m.Mem (128*t-{2*index+1}) z)
      {tick}.models (quantities (x 0) {phi} (x 1) {tick}.height) := by
    with_unfolding_all exact ⟨hd,h8,h16,hu,hn⟩
  obtain ⟨mass,sq⟩ := {tick}.physical_columns n hs hr mem
  obtain ⟨_,cert⟩ := {tick}.checked n
  exact ⟨mass,sq,cert.packed_root,cert.packed_neighbor⟩

end PlasmaLean.Design.{name}
'''
    return name, src, ['physical']


def verify(job):
    i, backward, args = job
    tick_report = ticks.check((i, backward, args.version, args, args.tick_cache))
    tick_dir = Path(tick_report['import_paths'][0])
    tick_result = (tick_dir, json.loads((tick_dir/'accepted.json').read_text()))
    model_args = SimpleNamespace(**{**vars(args), 'row': i, 'cache': args.model_cache,
                                    'direction': -1 if backward else 1, 'paired': False,
                                    'fields': list(range(4))})
    field_data = models.static_data()
    static = models.verify_static(model_args, field_data)
    pieces = models.verify_row(model_args, field_data, static)
    model = pieces[-1][1]
    item = source(i, backward, model['module'], tick_report['module'])
    deps = [*static, *pieces, tick_result]
    overlay = union(args.cache, deps)
    base, result = compile_modules(args.cache/item[0], [item], [overlay],
                                   [args.version, digest(RECORD), *[m['key'] for _,m in deps]],
                                   args, PACKAGE)
    out = {k:v for k,v in result.items() if k != 'artifacts'}
    out.update(index=i, direction=model_args.direction, panels=48, bound_archive=digest(RECORD),
               model=model['key'], ticks=tick_report['key'],
               import_paths=[str(base), str(overlay)])
    save(base/'row.json', out)
    print(f'{item[0]} accepted {result["key"]}', flush=True)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row', type=int, default=16, choices=range(325), metavar='0..324')
    parser.add_argument('--direction', type=int, choices=(-1,1))
    parser.add_argument('--workers', type=int, choices=(1,2), default=1)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/native-physical-panels')
    parser.add_argument('--model-cache', type=Path, default=ROOT/'.lake/native-action-checks')
    parser.add_argument('--tick-cache', type=Path, default=ROOT/'.lake/native-action-columns')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()
    args.version = lake('lean','--version')
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    directions = [args.direction] if args.direction else [1,-1]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        out = list(pool.map(verify, [(args.row,d<0,args) for d in directions]))
    if args.output:
        save(args.output,out)


if __name__ == '__main__':
    main()
