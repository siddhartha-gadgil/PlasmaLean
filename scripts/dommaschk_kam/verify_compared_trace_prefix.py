"""Attach contiguous physical two-tube comparisons to the calibrated pilot and its second birth."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


THEORY = 'DommaschkComparedTracePrefixes'
BLOCKS = 'ComparedPrefixBlocks'
PACKAGE = 'ComparedTraceCache'


def row_data(report, index, packets):
    name = report['module']
    if report['packets'] != packets:
        raise ValueError(f'expected the original signed pair at index {index}')
    if 'start' in report and 'stop' in report:
        lo,hi = report['start'],report['stop']
        if not 0 <= lo <= index < hi <= 325 or name != f'DommaschkGroupedProfile{lo:03d}To{hi:03d}Rows':
            raise ValueError(f'incorrect signed group at index {index}')
        rows = [[name+'.'+side+end+f'{index:03d}' for end in ('Inner','Outer')] for side in ('fwd','back')]
        proofs = [name+'.'+side+f'{index:03d}' for side in ('fwd','back')]
        return 'GroupedProfileRowsCache.'+name, proofs, rows
    if report['row'] != index:
        raise ValueError(f'wrong individual pair at index {index}')
    if name == f'DommaschkNativePairedProfile{index:03d}' and report['direct'] is True:
        providers = [f'DommaschkNativeActionPaired{index:03d}', f'DommaschkNativeActionQ0R478Paired{index:03d}']
        if report['providers'] != providers:
            raise ValueError(f'wrong normalized field models at {index}')
        rows = [[p+'.row' for p in providers], [p+'.backRow' for p in providers]]
        package = 'NativePairedProfileCache'
    elif name == f'DommaschkComparedProfiles{index:03d}':
        rows = [[name+'.'+side+end for end in ('Inner','Outer')] for side in ('fwd','back')]
        package = 'ComparedProfileCache'
    else:
        raise ValueError(f'missing the full field and arclength comparison on both clocks at {index}')
    return package+'.'+name, [name+'.forward',name+'.backward'], rows


def block_source(start, rows):
    stop = start+len(rows)
    name = f'DommaschkComparedRows{start:03d}To{stop:03d}'
    src = header(name, ['PlasmaLean.Design.'+THEORY, *dict.fromkeys(r[0] for r in rows)])
    src += 'open Certificates.PositionFrameSlabs DommaschkPairedActionProfiles\nset_option maxHeartbeats 2000000\n'
    for sign, direction in enumerate(('forward','backward')):
        rel = 'Compared' if sign == 0 else '(fun t => Compared (-t))'
        inner,outer = zip(*(r[2][sign] for r in rows), strict=True)
        src += f'''theorem {direction} {{a b : State}} {{xs zs : List Step}}
    (tail : OnPairedTubes {rel} (next {inner[-1]}) (next {outer[-1]}) ((({stop}:ℕ):ℝ)/64) xs zs) :
    OnPairedTubes {rel} a b ((({start}:ℕ):ℝ)/64) ([{', '.join(inner)}] ++ xs) ([{', '.join(outer)}] ++ zs) := by
  simp only [List.cons_append, List.nil_append]
'''
        for i, row in enumerate(rows,start):
            src += f'''  refine OnPairedTubes.cons_at {i} ?_ ?_
  · intro t ht x hx z hz
    have beginClock : (({i}:ℕ):ℝ) = {i} := by norm_num
    have endClock : ((({i}+1:ℕ):ℝ)) = {i+1} := by norm_num
    rw [beginClock,endClock] at ht
    rw [beginClock] at hx hz
    exact {row[1][sign]} ht hx hz
'''
        src += '  exact tail\n'
    return name,src+f'end PlasmaLean.Design.{name}\n',['forward','backward']


def ground_source(suffix, counts, rows, blocks):
    n = len(rows)
    family, cal = 'DommaschkCommonEndpointTraces'+suffix, 'DommaschkCalibratedFamily'+suffix
    name = f'DommaschkComparedBirths{n:03d}On'+suffix
    src = header(name,['CalibratedFamilyCache.'+cal,'PairedProfileCache.DommaschkPairedActionProfile000',
                       *[BLOCKS+'.'+b for b in blocks]])
    src += f'''open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkComparedTracePrefixes
open DommaschkPairedActionProfiles DommaschkPairedActionBirth DommaschkSignedObservable
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set
open {family} (checkpoint)
theorem paired : ComparedRows {n} (checkpoint .q0r470) (checkpoint .q0r478) := by
  constructor
'''
    for sign,side in enumerate(('forward','backward')):
        src += '  · '
        for j in reversed(range(len(blocks))):
            states = (['MirrorEndpoint.start .q0r470','MirrorEndpoint.start .q0r478'] if j == 0 else
                      ['next '+r for r in rows[8*j-1][2][sign]])
            suffixes = '(xs := []) (zs := []) (by trivial)' if j+1 == len(blocks) else f'h{j+1}'
            src += f'have h{j} := {blocks[j]}.{side} (a := {states[0]}) (b := {states[1]}) {suffixes}\n    '
        src += 'rw [show ((0:ℕ):ℝ)/64 = 0 by norm_num] at h0\n    with_unfolding_all exact h0\n'
    src += f'''theorem from_common_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → ∃ y z : ℝ → Plane,
        y φ = coordinates.symm (birth uC zC uA zA (47/100) φ) ∧ {cal}.Observed φ y ∧
        z φ = coordinates.symm (birth uC zC uA zA (239/500) φ) ∧
        (∀ t ∈ Icc (-({counts['q0r478']}:ℝ)/64) ({counts['q0r478']}/64), HasDerivWithinAt z
          (DommaschkJacobian.euclideanFlow 0 1 t (z t)) (Icc (-({counts['q0r478']}:ℝ)/64) ({counts['q0r478']}/64)) t) ∧
        ∀ t ∈ Icc (-({n}:ℝ)/64) ({n}/64), Compared t (y t) (z t) := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,_,each,calibrate⟩ := {cal}.same_embedded_tori
  refine ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => ?_⟩
  obtain ⟨x,y,start,path,obs⟩ := calibrate φ small
  have outer := each .q0r478 φ (by simpa [MirrorEndpoint.opposite, MirrorEndpoint.width, azimuth] using small)
  obtain ⟨z,born,_,_,ode,comp⟩ := compare_birth path outer (small.trans (by norm_num [halfWidth]))
    (by change 1 ≤ {counts['q0r478']}; norm_num) (by norm_num : 0 < {n})
    (by change {n} ≤ {counts['q0r470']}; norm_num) (by change {n} ≤ {counts['q0r470']}; norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
'''
    for side in ('forward','backward'):
        src += f'''    (by
      intro prev t x ht hx
      have h := DommaschkPairedActionProfile000.outer_{side}_regular (prev := prev) (x := x) (t := t)
        (by simpa only [zero_div,halfWidth] using ht)
        (by rw [zero_div]; with_unfolding_all exact hx)
      simpa only [Bool.false_eq_true,↓reduceIte] using h)
'''
    src += f'''    paired
  exact ⟨y,z,start,obs,born,ode,comp⟩
end PlasmaLean.Design.{name}
'''
    return name,src,['paired','from_common_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--calibrated', required=True,type=Path)
    parser.add_argument('--launch-profile',required=True,type=Path)
    parser.add_argument('--rows',required=True,type=Path,nargs='+',help='ordered signed row or row-group receipts, starting at zero')
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/compared-trace-prefix')
    parser.add_argument('--output',required=True,type=Path)
    args = parser.parse_args()
    def read(path):
        return json.loads(path.read_text())
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    args.cache = args.cache.resolve()
    cal,launch = read(args.calibrated),read(args.launch_profile)
    reports = []
    for path in args.rows:
        record = read(path)
        lo,hi = record.get('start',len(reports)),record.get('stop',len(reports)+1)
        if type(lo) is not int or type(hi) is not int or lo != len(reports) or not lo < hi <= 325:
            parser.error(f'nonconsecutive comparison receipt {path}')
        reports.extend([record]*(hi-lo))
    n,counts = len(reports),cal['lengths_each_direction']
    if set(counts) != set(ENDPOINTS) or not 1 <= n <= min(325,counts['q0r470'],counts['q0r478']):
        parser.error('the calibrated family must enclose the whole requested pair of prefixes')
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    packets = [digest(load(r)[1]) for r in (470,478)]
    if (cal['module'] != 'DommaschkCalibratedFamily'+suffix or launch['module'] != 'DommaschkPairedActionProfile000'
            or launch['packets'] != packets or launch['row'] != 0):
        parser.error('expected the authenticated calibrated family and original launch regularity')
    rows = [row_data(report,index,packets) for index,report in enumerate(reports)]
    def imports(group):
        roots = []
        unique = {r['key']:r for r in group}
        for report in unique.values():
            paths = list(map(Path,report['import_paths']))
            admitted(paths[0],report['module'],report['key'])
            roots.extend(paths)
        return merge_import_roots(args.cache,roots,list(unique))
    keys = [lake('lean','--version'),digest(DESIGN/(THEORY+'.trace'))]
    blocks = []
    for start in range(0,n,8):
        group = reports[start:start+8]
        overlay = imports(group)
        item = block_source(start,rows[start:start+8])
        root,record = compile_modules(args.cache/item[0],[item],[overlay],
                                      [*keys,*[r['key'] for r in group]],args,BLOCKS)
        blocks.append({**record,'import_paths':list(map(str,[root,overlay]))})
    deps = [cal,launch,*blocks]
    overlay = imports(deps)
    item = ground_source(suffix,counts,rows,[r['module'] for r in blocks])
    root,record = compile_modules(args.cache/item[0],[item],[overlay],
                                  [*keys,*[r['key'] for r in deps]],args,PACKAGE)
    out = {k:v for k,v in record.items() if k != 'artifacts'}
    out.update(length=n,calibrated_key=cal['key'],packets=packets,row_keys=[r['key'] for r in reports],
               import_paths=list(map(str,[root,overlay])))
    save(args.output,out)
    print(item[0],record['key'],flush=True)


if __name__ == '__main__':
    main()
