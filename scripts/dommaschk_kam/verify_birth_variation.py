"""Attach the actual pilot birth derivatives to an authenticated eight-endpoint trace family."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from emit_birth_variation import TARGET, emit
from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS, PACKAGE as FAMILY_PACKAGE, source as family_source
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    if TARGET.read_text() != emit():
        raise ValueError('regenerated arithmetic differs from the imported pilot certificate')
    report = json.loads(args.family.read_text())
    counts = report['lengths_each_direction']
    if set(counts) != set(ENDPOINTS) or any(type(n) is not int or not 1 <= n <= 391 for n in counts.values()):
        raise ValueError('requires one checked length per endpoint')
    source_name, source, _ = family_source(counts)
    root, overlay = map(Path, report['import_paths'])
    if report['module'] != source_name or root.name != report['key']:
        raise ValueError('endpoint lengths do not name the authenticated family')
    marker = admitted(root, source_name, report['key'])
    if (root/FAMILY_PACKAGE/(source_name+'.lean')).read_text() != source:
        raise ValueError('family theorem does not match its canonical generated source')
    if f'PlasmaLean.Design.{source_name}.all_from_entry' not in marker['theorems']:
        raise ValueError('missing physical entry theorem for the eight endpoints')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    name = 'DommaschkPilotBirth'+'_'.join(str(counts[e]) for e in ENDPOINTS)
    body = f'''module
public import PlasmaLean.Design.DommaschkPilotBirthVariation
public import {FAMILY_PACKAGE}.{source_name}

@[expose] public section
namespace PlasmaLean.Design.{name}

theorem physical_birth : DommaschkBirthVariation.CommonPilot {source_name}.checkpoint :=
  DommaschkBirthVariation.common_pilot _ {source_name}.all_from_entry

end PlasmaLean.Design.{name}
'''
    traces = [digest(DESIGN/(f'Dommaschk{m}.trace')) for m in
              ('BirthVariation','BirthVariationBounds','PilotBirthVariation')]
    keys = [lake('lean','--version'),report['key'],traces]
    env = SimpleNamespace(lean=Path(lake('lean','--print-prefix'))/'bin/lean',
                          lean_path=lake('printenv','LEAN_PATH'))
    base, proof = compile_modules(ROOT/'.lake/birth-variation'/name,[(name,body,['physical_birth'])],
                                  [root,overlay],keys,env,'BirthVariationCache')
    result = {k:v for k,v in proof.items() if k != 'artifacts'}
    result.update(family_key=report['key'], lengths_each_direction=counts,
                  signed_rows=2*sum(counts.values()), import_paths=list(map(str,[base,root,overlay])))
    save(args.output,result)
    print(f"{name}.physical_birth {proof['key']}")


if __name__ == '__main__':
    main()
