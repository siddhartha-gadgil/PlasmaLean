"""Join the wide-frame enclosure, signed central defects and paired spatial bounds on original rows."""
import argparse
import json
from pathlib import Path

from radial_ribbon_jacobians import trial
from ribbon_central_data import LENGTH, WITNESS_SHA, label
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_endpoint_signed_prefix import physical_source
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_radial_ribbon_packets import PACKAGE as PACKETS, load
from verify_ribbon_central_group import authenticate as central_authenticate
from verify_ribbon_spatial_group import JACOBIAN, fuse
from verify_signed_mirror_passage import merge_import_roots

PACKAGE='RadialRibbonPhysicalCache'


def archived(rows, sign, index):
    tag='forward' if sign>0 else 'backward'
    return f'{rows}.{tag}{index//16*16:03}[{index%16}]'


def physical(k,pair,sign,jac,ref,packet):
    i=pair.index
    ns,src=physical_source(label(k),sign,pair,pair.forward,jac['module'],ref['module'])
    src=src.replace('public import PlasmaLean.Design.DommaschkEndpointContinuation',
        f'public import PlasmaLean.Design.DommaschkWideTraceFields\npublic import {PACKETS}.{packet}')
    for row in (jac,ref):
        src=src.replace(f"public import {row['package']}.{row['module']}\n",
                        f"public import {row['package']}.{row['import_module']}\n")
    at,end=src.index('def previous :'),src.index('\ntheorem checked :')
    prev=packet+'.seed' if i==0 else 'next ('+archived(packet,sign,i-1)+')'
    src=src[:at]+f'def previous : PositionFrameSlabs.State := {prev}\ndef row : Step := {archived(packet,sign,i)}\n'+src[end:]
    src=src.replace('test allLimits previous row','PositionFrameWide.valid previous row')
    src=src.replace('DommaschkEndpointContinuation.forward_rectangle checked',
                    'DommaschkWideTraceFields.forward_rectangle ((Bool.and_eq_true_iff.mp checked).1)')
    src=src.replace('DommaschkBackwardRectangle.field_bounds','DommaschkWideTraceFields.backward_rectangle')
    src=src.replace('    checked rectangle fits','    ((Bool.and_eq_true_iff.mp checked).1) rectangle fits')
    src=src.replace('physical_step_ball checked','PositionFrameWide.physical_step_on checked')
    return ns,src,['field_bounds','physical_step']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',required=True,type=Path)
    p.add_argument('--packets',required=True,type=Path)
    p.add_argument('--tile',required=True,type=int,choices=range(4))
    p.add_argument('--span',required=True,type=int,nargs=2)
    p.add_argument('--spatial',type=Path,default=ROOT/'.lake/ribbon-spatial-campaign')
    p.add_argument('--central',type=Path,default=ROOT/'.lake/ribbon-central-campaign')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/ribbon-physical-checks')
    p.add_argument('--handoff',type=Path,default=ROOT/'.lake/ribbon-physical-campaign')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    lo,hi=a.span
    if not 0<=lo<hi<=LENGTH or digest(a.ribbon)!=WITNESS_SHA:
        p.error('expected original signed radius packet and a valid elapsed-time span')
    _,rows=load(a.ribbon)
    k=a.tile
    env(a)
    packet=json.loads(a.packets.read_text())[str(k)]
    if packet['tile']!=k or packet['ribbon']!=WITNESS_SHA or packet['module']!=f'DommaschkRadialRibbonRows{k}':
        raise ValueError('wrong signed row list')
    root,=map(Path,packet['import_paths'])
    admitted(root,packet['module'],packet['key'])
    imports=[root]
    keys=[packet['key']]
    sources=[]
    verified={}
    for i in range(lo,hi):
        pair=trial(rows,k,i)
        jj=json.loads((a.spatial/f'tile{k}'/'jacobians'/f'{i:03}.json').read_text())
        refs=json.loads((a.central/f'tile{k}'/'references'/f'{i:03}.json').read_text())
        central_authenticate(refs,k,i,verified)
        expected=f'DommaschkJacobian{label(k).upper()}PairedForward{i:03}'
        if ((jj['tile'],jj['index'],jj['packet_sha256'],jj['module'],jj['package'])!=(k,i,WITNESS_SHA,expected,JACOBIAN)
                or tuple(jj['projected_radii'])!=pair.common_radii or jj['common_rate']!=str(pair.common_rate)):
            raise ValueError(f'wrong projected rectangle or rate on tile {k}, row {i}')
        uid=(jj['import_paths'][0],jj['import_module'],jj['key'])
        if uid not in verified:
            verified[uid]=admitted(Path(uid[0]),uid[1],uid[2])
        if 'PlasmaLean.Design.'+expected+'.physical_clock_log_norm' not in verified[uid]['theorems']:
            raise ValueError('missing physical logarithmic norm')
        for row in [jj,*refs]:
            imports.extend(map(Path,row['import_paths']))
            keys.append(row['key'])
        for ref in refs:
            sources.append(physical(k,pair,ref['direction'],jj,ref,packet['module']))
    keys=list(dict.fromkeys(keys))
    links=merge_import_roots(a.cache,list(dict.fromkeys(imports)),keys)
    name=f'DommaschkRibbonPhysical{k}Rows{lo:03}To{hi:03}'
    claims=['PlasmaLean.Design.'+ns+'.'+t for ns,_,ts in sources for t in ts]
    receipt_root,rec=compile_modules(a.cache/name,[(name,fuse(sources),[])],[links],
        [a.version,WITNESS_SHA,digest(DESIGN/'DommaschkWideTraceFields.trace'),keys],a,PACKAGE,qualified_claims=claims)
    result={key:v for key,v in rec.items() if key!='artifacts'}
    result.update(tile=k,span=[lo,hi],packet_sha256=WITNESS_SHA,parents=keys,import_paths=list(map(str,[receipt_root,links])))
    for i in range(lo,hi):
        path=a.handoff/f'tile{k}'/'steps'/f'{i:03}.json'
        path.parent.mkdir(parents=True,exist_ok=True)
        save(path,result)
    save(a.output,result)
    print(f'{name} {rec["key"]}, {2*(hi-lo)} true signed IVP steps',flush=True)


if __name__=='__main__':
    main()
