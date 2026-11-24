"""Bind eight authenticated signed trace lengths to one common pair of physical Q-16 tori."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


ENDPOINTS = ('q0r470','q0r478','q0r523','q0r531','q1r456','q1r464','q1r509','q1r517')
PACKAGE = 'CommonEndpointTraceCache'


def receipt(path):
    return json.loads(path.read_text())


def authenticate_pilot(report):
    n = report['slabs_per_direction']
    name = f'DommaschkPairedPrefix{n:03d}'
    if not 3 <= n <= 391 or (report['module'],report['packet_sha256']) != (name,digest(RECORD)):
        raise ValueError('expected the original pilot paired-prefix receipt')
    roots = list(map(Path,report['import_paths']))
    marker = admitted(roots[0],name,report['key'])
    if f'PlasmaLean.Design.{name}.exists_nested_paired' not in marker['theorems']:
        raise ValueError('pilot receipt lacks the paired physical trajectory')
    for sign,module in [('forward',f'DommaschkPhysicalPrefix{n:03d}'),
                        ('backward',f'DommaschkBackwardPrefix{n:03d}')]:
        matches = [r for r in roots if r.parent.name == module and r.name == report[sign+'_key']]
        if len(matches) != 1:
            raise ValueError(f'missing independent {sign} physical prefix {module}')
        admitted(matches[0],module,report[sign+'_key'])
    return n,roots


def authenticate_secondary(report):
    label,n = report['endpoint'],report['length_each_direction']
    if label not in ENDPOINTS[1:] or not 1 <= n <= 391:
        raise ValueError(f'invalid secondary endpoint or length: {label}, {n}')
    checksum = digest(RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz'))
    name = f'DommaschkSignedPrefix{label.upper()}{n:03d}'
    if (report['module'],report['packet_sha256']) != (name,checksum):
        raise ValueError(f'{label} receipt does not match its own two-direction archive')
    root,overlay = Path(report['proof_root']),Path(report['import_path'])
    marker = admitted(root,name,report['key'])
    expected = f'PlasmaLean.Design.{name}.from_entry'
    if expected not in marker['theorems'] or marker['theorems'] != report['theorems']:
        raise ValueError(f'missing certificate for every admitted section entry at {label}')
    obj = f'{SIGNED_PACKAGE}/{name}.olean'
    if digest(overlay/obj) != marker['artifacts'][obj]:
        raise ValueError(f'wrong imported section-entry theorem at {label}')
    for direction in (1,-1):
        rows = report['rows'][str(direction)]
        if [(r['index'],r['direction'],r['endpoint']) for r in rows] != [
                (i,direction,label) for i in range(n)]:
            raise ValueError(f'incomplete or mislabelled signed row list for {label}')
    return label,n,[root,overlay]


def source(counts):
    pilot = counts[ENDPOINTS[0]]
    fw,bw = f'DommaschkPhysicalPrefix{pilot:03d}',f'DommaschkBackwardPrefix{pilot:03d}'
    name = 'DommaschkCommonEndpointTraces'+'_'.join(str(counts[e]) for e in ENDPOINTS)
    mods = {e:f'DommaschkSignedPrefix{e.upper()}{counts[e]:03d}' for e in ENDPOINTS[1:]}
    text = ['module','public import PlasmaLean.Design.DommaschkEndpointTraceFamily',
            f'public import PairedPrefixCache.DommaschkPairedPrefix{pilot:03d}']
    text += [f'public import {SIGNED_PACKAGE}.{m}' for m in mods.values()]
    text += [f'''
/-! # All eight signed launch paths on one common pair of physical tori -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch
open DommaschkEndpointTraceFamily DommaschkBackwardPairedPrefix Theory.KAM
set_option maxRecDepth 16000

def checkpoint : MirrorEndpoint → Checkpoint
  | .q0r470 => ⟨{pilot}, {fw}.exitState, {bw}.exitState,
      {fw}.rows, {bw}.rows⟩''']
    for label,module in mods.items():
        text += [f'  | .{label} => ⟨{counts[label]}, {module}.forwardExit,',
                 f'      {module}.backwardExit, {module}.forwardRows, {module}.backwardRows⟩']
    text += [f'''
theorem row_counts (e : MirrorEndpoint) :
    (checkpoint e).forwardRows.length = (checkpoint e).length ∧
    (checkpoint e).backwardRows.length = (checkpoint e).length := by
  cases e <;> constructor <;> with_unfolding_all rfl

theorem pilot_from_section {{uC zC uA zA : FA}} {{φ : ℝ}}
    (entry : SectionEntry .q0r470 uC zC uA zA φ) :
    (checkpoint .q0r470).Passage .q0r470 uC zC uA zA φ :=
  pilot_from_entry entry ⟨{fw}.checked, {fw}.field_bounds⟩
    ⟨{bw}.checked, {bw}.field_bounds⟩

theorem all_from_entry (e : MirrorEndpoint) {{uC zC uA zA : FA}} {{φ : ℝ}}
    (entry : SectionEntry e uC zC uA zA φ) : (checkpoint e).Passage e uC zC uA zA φ := by
  cases e with
  | q0r470 => exact pilot_from_section entry''']
    for label,module in mods.items():
        text.append(f'  | {label} => exact {module}.from_entry entry')
    text += [f'''
theorem same_nested_tori : DommaschkEndpointTraceFamily.Common checkpoint :=
  common_of_entry checkpoint all_from_entry

end PlasmaLean.Design.{name}
''']
    return name,'\n'.join(text),['row_counts','pilot_from_section','all_from_entry','same_nested_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pilot',required=True,type=Path,help='q0r470 paired physical trajectory')
    parser.add_argument('--secondary',nargs=7,required=True,type=Path,
                        help='one authenticated signed prefix for each other endpoint')
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/common-endpoint-traces')
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    pilot = receipt(args.pilot)
    n,roots = authenticate_pilot(pilot)
    inputs = {ENDPOINTS[0]:(n,pilot['key'],pilot['packet_sha256'],roots)}
    for f in args.secondary:
        report = receipt(f)
        label,count,parents = authenticate_secondary(report)
        if label in inputs:
            raise ValueError(f'duplicate signed endpoint {label}')
        inputs[label] = (count,report['key'],report['packet_sha256'],parents)
    if set(inputs) != set(ENDPOINTS):
        raise ValueError('requires all eight distinct endpoints')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    keys = [version,digest(DESIGN/'DommaschkEndpointTraceFamily.trace'),
            [(e,*inputs[e][:3]) for e in ENDPOINTS]]
    overlay = merge_import_roots(args.cache,[r for e in ENDPOINTS for r in inputs[e][3]],keys)
    counts = {e:inputs[e][0] for e in ENDPOINTS}
    item = source(counts)
    base,marker = compile_modules(args.cache/item[0],[item],[overlay],keys,env,PACKAGE)
    result = {k:v for k,v in marker.items() if k != 'artifacts'}
    result.update(lengths_each_direction=counts,signed_rows=2*sum(counts.values()),
                  endpoints={e:{'key':inputs[e][1],'packet_sha256':inputs[e][2]} for e in ENDPOINTS},
                  import_paths=[str(base),str(overlay)])
    save(args.output,result)
    print(item[0],marker['key'],flush=True)


if __name__ == '__main__':
    main()
