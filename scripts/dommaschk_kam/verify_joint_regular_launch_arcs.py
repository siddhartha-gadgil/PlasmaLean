"""Bind simultaneous kinetic control of two radial launch families to the signed 328-row passage."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_regular_birth_arcs import NAME as SECONDARY
from verify_signed_mirror_passage import merge_import_roots


BRIDGE = 'DommaschkJointRegularLaunchArcs'
PACKAGE = 'JointRegularLaunchArcsCache'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--regular-arcs', type=Path, required=True)
    p.add_argument('--require-both', action='store_true', help='require at least 328 signed outer pairs')
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/joint-regular-launch-arcs')
    a = p.parse_args()
    record = json.loads(a.regular_arcs.read_text())
    if record['module'] != SECONDARY:
        p.error('expected the accepted second-radius regular-birth result')

    def roots(r, theorem):
        paths = list(map(Path,r['import_paths']))
        marker = admitted(paths[0], r['module'], r['key'])
        if f"PlasmaLean.Design.{r['module']}.{theorem}" not in marker['theorems']:
            p.error(f"missing {theorem} for {r['module']}")
        return paths

    def summary(m, paths):
        return {k:v for k,v in m.items() if k != 'artifacts'} | {'import_paths': list(map(str,paths))}

    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()

    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    paths = roots(record, 'from_passage')
    keys = [record['key'], digest(DESIGN/'DommaschkJointLaunchArcs.trace'), lake('lean','--version')]
    template = Path(__file__).parent/'templates/joint_regular_launch_arcs.lean.tpl'
    bridge = (BRIDGE, template.read_text(), ['from_family'])
    top, mark = compile_modules(a.cache/BRIDGE, [bridge], paths, keys, a, PACKAGE)
    result = summary(mark, [top,*paths])
    result['secondary_regularity'] = record['key']
    result['both_from_birth'] = False
    if a.require_both:
        fam, counts = record['birth'], record['lengths_each_direction']
        suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
        if (fam['module'] != 'DommaschkRegularBirthArcs'+suffix
                or not re.fullmatch(r'391(?:_[1-9][0-9]*){7}', suffix) or not 328 <= counts['q0r478'] <= 391):
            p.error('requires both radial passages, including at least 328 outer pairs')
        family, cal = 'DommaschkCommonEndpointTraces'+suffix, 'DommaschkCalibratedFamily'+suffix
        name = 'DommaschkTwoRadiusRegularArcs'+suffix
        src = f'''module
public import {PACKAGE}.{BRIDGE}
public import RegularBirthArcsCache.{fam['module']}

@[expose] public section
namespace PlasmaLean.Design.{name}
open DommaschkJointRegularLaunchArcs
open {family} (checkpoint)
set_option maxRecDepth 65536
set_option maxHeartbeats 3500000
theorem through_both_births : Joint checkpoint {cal}.Observed := by
  apply from_family {fam['module']}.pilot (by change 316 ≤ 391; norm_num)
    (by change 327 < {counts['q0r478']}; norm_num) {family}.row_counts
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl)
    (F := (checkpoint .q0r478).forwardRows.drop 327)
    (G := (checkpoint .q0r478).backwardRows.drop 327) <;> with_unfolding_all rfl
end PlasmaLean.Design.{name}
'''
        keys.extend([mark['key'],fam['key']])
        overlay = merge_import_roots(a.cache/'ground',[top,*paths,*roots(fam,'both')],keys)
        done, proof = compile_modules(a.cache/name, [(name,src,['through_both_births'])],
                                     [overlay], keys, a, 'TwoRadiusRegularArcsCache')
        result.update(both_from_birth=True, physical=summary(proof,[done,overlay]), family=fam['key'],
                      lengths_each_direction=counts)
    save(a.output,result)
    print(result.get('physical',result)['key'], flush=True)


if __name__ == '__main__':
    main()
