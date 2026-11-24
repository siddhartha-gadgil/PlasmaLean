"""Realize a local physical ODE interval with each sign's own archived endpoint frames."""

import argparse
from pathlib import Path
import subprocess

from screen_independent_endpoint_frames import trial_frames
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_physical_launches import reports
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_endpoint_signed_prefix import DEPENDENCY, PACKAGE, input_root, physical_source
from verify_horner_endpoint_jacobian import checked_shared_roots
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--jacobians',type=Path,required=True)
    p.add_argument('--references',type=Path,nargs='+',required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--endpoint',choices=ENDPOINTS)
    p.add_argument('--direction',type=int,choices=(-1,1))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-independent-physical')
    args = p.parse_args()
    args.cache = args.cache.resolve()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    version = lake('lean','--version')
    refs = {(r['endpoint'],r['direction'],r['index']):r for r in reports(args.references)}
    output = []
    for jac in reports([args.jacobians]):
        label,i,sign = jac['endpoint'],jac['index'],jac['matrix_direction']
        if args.endpoint not in (None,label) or args.direction not in (None,sign):
            continue
        if i < 1 or sign not in (-1,1):
            raise ValueError('expected a signed continuation from a previous row')
        packet = RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
        checksum = digest(packet)
        tag = 'Forward' if sign == 1 else 'Back'
        jm = f'DommaschkJacobian{label.upper()}Independent{tag}{i:03}'
        fm = f'DommaschkTraceResidual{label.upper()}{tag}{i:03}'
        jacdir = input_root(jac,label,1,i,jm,checksum,version)
        parents = checked_shared_roots(jac,jacdir,version)
        imports = merge_import_roots(args.cache,[jacdir,*parents],[jac['key'],'physical-field-imports'])
        ref = refs[label,sign,i]
        refdir = input_root(ref,label,sign,i,fm,checksum,version)
        prior,current = trial_frames(packet,i-1,i)
        pair, reflected = current
        previous = prior[0].forward if sign == 1 else prior[0].backward
        name,src = physical_source(label,sign,pair,previous,jm,fm)
        root,record = compile_modules(args.cache/name,[(name,src,['checked','field_bounds','physical_step'])],
            [imports,refdir],[checksum,version,digest(DESIGN/(DEPENDENCY+'.trace')),jac['key'],ref['key']],args,PACKAGE)
        report = {k:v for k,v in record.items() if k!='artifacts'}
        report.update(endpoint=label,index=i,direction=sign,packet_sha256=checksum,jacobian_key=jac['key'],
                      residual_key=ref['key'],import_paths=list(map(str,[root,imports,refdir])),
                      frame_conjugate=(pair.forward_left==reflected.forward_left and
                                       pair.forward['frame_end']==reflected.forward['frame_end']))
        output.append(report)
        print(f'{name}.physical_step {record["key"]}',flush=True)
    if not output:
        raise ValueError('no Jacobian matches the requested endpoint and direction')
    save(args.output,output)


if __name__ == '__main__':
    main()
