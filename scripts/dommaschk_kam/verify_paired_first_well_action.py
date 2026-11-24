"""Compare two physical first-well actions using 325 paired tube bounds and the outer mirrors."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_compared_trace_prefix import PACKAGE as COMPARED
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_first_well_action import NAME as WELL
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkPairedFirstWell325'
PACKAGE = 'PairedFirstWellActionCache'
THEORY = 'DommaschkPairedFirstWellAction'


def ground(suffix, cal, paired, outer_length):
    name = 'DommaschkComparedFirstWellsOn' + suffix
    checkpoint = f'DommaschkCommonEndpointTraces{suffix}.checkpoint'
    src = f'''module
public import {PACKAGE}.{NAME}
public import CalibratedFamilyCache.{cal}
public import {COMPARED}.{paired}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch DommaschkQ0R478MirrorBranch327 DommaschkPairedFirstWellAction
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
theorem from_common_tori : OnCommonTori {checkpoint} {cal}.Observed := by
  apply {NAME}.from_family (extraF := ({checkpoint} .q0r478).forwardRows.drop 327)
    (extraB := ({checkpoint} .q0r478).backwardRows.drop 327) {cal}.same_embedded_tori
    (fun h => ⟨h.2.2.1,h.2.2.2.2.2⟩)
  · change 325 ≤ 391
    norm_num
  · change 325 ≤ 391
    norm_num
  · change 327 / 64 < ({outer_length} : ℝ) / 64
    norm_num
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · exact {paired}.paired
end PlasmaLean.Design.{name}
'''
    return name, src, ['from_common_tori']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--well', type=Path, required=True)
    p.add_argument('--calibrated', type=Path)
    p.add_argument('--compared', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/paired-first-well-action')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    if bool(a.calibrated) != bool(a.compared):
        p.error('attach the calibrated through-mirror family and its complete paired comparisons together')

    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()

    def roots(report):
        paths = list(map(Path, report['import_paths']))
        admitted(paths[0], report['module'], report['key'])
        return paths

    def result(record, paths):
        return {k: record[k] for k in ('module','key','theorems','axioms')} | {
            'import_paths': list(map(str, paths))}

    well = json.loads(a.well.read_text())
    packets = [digest(load(r)[1]) for r in (470,478)]
    if well['module'] != WELL or well['packet_sha256'] != packets[1]:
        p.error('expected the second launch’s certified mirror branches and regularity')
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    versions = [lake('lean','--version'),digest(DESIGN/(THEORY+'.trace')),well['key']]
    paths = roots(well)
    source = (Path(__file__).parent/'templates/paired_first_well_action.lean.tpl').read_text()
    item = (NAME,source,['from_family'])
    root,mark = compile_modules(a.cache/NAME,[item],paths,versions,a,PACKAGE)
    out = result(mark,[root,*paths]) | {'complete': False, 'packets': packets}
    if a.compared:
        cal,comp = [json.loads(d.read_text()) for d in (a.calibrated,a.compared)]
        counts = cal['lengths_each_direction']
        suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
        if (counts['q0r470'] != 391 or counts['q0r478'] <= 327 or comp['length'] != 325
                or comp['packets'] != packets or comp['calibrated_key'] != cal['key']
                or cal['module'] != 'DommaschkCalibratedFamily'+suffix
                or comp['module'] != 'DommaschkComparedBirths325On'+suffix):
            p.error('expected all 325 signed pairs and the calibrated family on which they were proved')
        keys = [*versions,mark['key'],cal['key'],comp['key']]
        overlay = merge_import_roots(a.cache/'ground',[root,*paths,*roots(cal),*roots(comp)],keys)
        item = ground(suffix,cal['module'],comp['module'],counts['q0r478'])
        rb,done = compile_modules(a.cache/item[0],[item],[overlay],keys,a,'ComparedFirstWellsCache')
        out.update(complete=True, birth=result(done,[rb,overlay]), calibrated_key=cal['key'],
                   compared_key=comp['key'])
    save(a.output,out)
    print(out.get('birth',out)['key'])


if __name__ == '__main__':
    main()
