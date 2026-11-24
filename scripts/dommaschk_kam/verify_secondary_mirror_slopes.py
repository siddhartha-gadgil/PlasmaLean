"""Check the outward squared-strength derivative on both archived Q0 physical output tubes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path
import re
from string import Template
import subprocess

from bounce_mirror_pilot import Model, R0M, angle_models
from emit_position_slabs import step
from emit_rectangular_jacobian import CLOCK
from emit_sparse_jacobian import derivative_file, header
from emit_sparse_taylor_slab import ROOT, field, model_literal, models
from screen_sparse_jacobians import field_jet
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules
from verify_mirror_slopes import ANGLES, SLOPES, angle_sources, bounds_source, tube_source
from verify_physical_trace_slabs import DESIGN, JACOBIAN_PACKAGE, digest, save
from verify_secondary_mirror_caps import load


JET = 'SecondaryMirrorJetCache'
ANGLE = 'SecondaryMirrorAngleCache'
MARGIN = 'SecondaryMirrorMarginCache'
TUBE = 'SecondaryMirrorDerivativeCache'


def joint_row(i,traces):
    back,forward = (t['steps'][i] for t in traces)
    if (back['coefficients'][0] != forward['coefficients'][0]
            or back['coefficients'][1] != [-v for v in forward['coefficients'][1]]):
        raise ValueError('the two archived reference curves do not reflect')
    e = max(r['physical_radius_out'] for r in (back,forward))
    r,z = (Model(c,e) for c in forward['coefficients'])
    waves = angle_models(Fraction(2*i+1,128),Fraction(1,128),Fraction(0))
    return r,(r-R0M,z,waves[2],waves[1]),{-1:back,1:forward}


def jet_files(label,i,data):
    _,cols,rows = data
    ns = f'Dommaschk{label}MirrorJet{i:03}'
    inp = ns+'Inputs'
    block,local = divmod(i,8)
    harmonic = f'DommaschkHarmonicBlock{block:02}'
    def begin(deps,title):
        return header(deps,title,ns,'DommaschkJacobian')
    end = f'\nend PlasmaLean.Design.{ns}\n'
    src = begin(['DommaschkJacobianFrames'],'Spatial and angular variables on both output tubes')
    src += 'open Certificates.PositionFrameSlabs\n'
    src += 'def trial : Inputs := ⟨'+', '.join(map(model_literal,cols))+'⟩\n'
    for sign,name in [(-1,'back'),(1,'fwd')]:
        src += f'def {name}Row : Step := {step(rows[sign])}\n'
    files = {inp:src+end}
    fields = []
    for symbol,tag,jet in zip(('dD','dnR','dnZ'),'DRZ',field_jet(),strict=True):
        n = ns+tag
        files[n] = begin([inp],'Sparse QA2R field on the output tube')+field(symbol,cols)+end
        fields.append(n)
        for axis,d in enumerate('UZ'):
            n = ns+tag+d
            files[n] = derivative_file(symbol,'grad'+tag+d,axis,models(jet[axis+1],cols),ns,inp,
                                       'DommaschkJacobian')
            fields.append(n)
    clock = CLOCK.read_text()
    clock = clock[clock.index('theorem clock_inputs'):clock.index('/-- The enclosed transformed')]
    files[ns] = (begin([*fields,harmonic],'Positive denominator on the physical clock')
                 + Template(clock).substitute(i=i,end=i+1,offset=2*i+1,harmonic=harmonic,
                     local=local,base=8*block,count=min(8,391-8*block))+end)
    files = add_shared_powers(files,inp,ns,cols)
    def rename(m):
        return f'public import {JET}.{m[1]}' if m[1] in files else m[0]
    declarations = [(n,re.sub(r'^public import PlasmaLean\.Design\.(\w+)$',rename,s,flags=re.M),
                     ['clock_inputs','denominator_pos'] if n == ns else []) for n,s in files.items()]
    external = sorted({m for _,s,_ in declarations for m in
                       re.findall(r'^public import PlasmaLean\.Design\.(\w+)$',s,flags=re.M)})
    return ns,declarations,[digest(DESIGN/(m+'.trace')) for m in external]


def verify(i,*,label,traces,keys,cache,args):
    data = joint_row(i,traces)
    jet,files,deps = jet_files(label,i,data)
    jr,j = compile_modules(cache/jet,files,[],[keys,deps],args,JET)
    old,src = angle_sources(i,data[1],jet)
    angles = jet+'Angles'
    src = src.replace(old,angles).replace('public import '+JACOBIAN_PACKAGE+'.','public import '+JET+'.')
    angular = [f'angle{f}{d}_checked' for f in 'DRZ' for d in 'CS']
    ar,a = compile_modules(cache/angles,[(angles,src,angular)],[jr],[keys,j['key']],args,ANGLE)
    old,src,rate = bounds_source(i,jet,angles,row_data=data)
    margin = jet+'Margin'
    src = src.replace(old,margin).replace('public import '+ANGLES+'.','public import '+ANGLE+'.')
    src = src.replace('public import '+JACOBIAN_PACKAGE+'.','public import '+JET+'.')
    mr,m = compile_modules(cache/margin,[(margin,src,['numerator_margin'])],[jr,ar],
                           [keys,j['key'],a['key'],digest(DESIGN/'DommaschkMirrorStrengthSlope.trace')],
                           args,MARGIN)
    row_names = {1:jet+'.fwdRow',-1:jet+'.backRow'}
    old,src = tube_source(i,jet,margin,rate,closed=True,row_data=data,frame_rows=row_names)
    tube = jet+'Physical'
    src = src.replace(old,tube).replace('public import '+SLOPES+'.','public import '+MARGIN+'.')
    src = src.replace('public import '+JACOBIAN_PACKAGE+'.','public import '+JET+'.')
    theorems = [f'{d}_{p}' for d in ('fwd','back') for p in ('transverse','level_transverse')]
    tr,t = compile_modules(cache/tube,[(tube,src,theorems)],[jr,ar,mr],
                           [keys,m['key'],digest(DESIGN/'DommaschkMirrorEndpointSign.trace'),
                            digest(DESIGN/'DommaschkPositionFramesFwd.trace')],args,TUBE)
    print(f'{label} signed row {i}: {t["key"]}',flush=True)
    return {'index':i,'module':tube,'key':t['key'],'rate':str(rate),'axioms':t['axioms'],
            'theorems':t['theorems'],'import_paths':list(map(str,[tr,mr,ar,jr]))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch',type=int,default=478)
    parser.add_argument('--rows',type=int,nargs='+',default=[317,325,326])
    parser.add_argument('--workers',type=int,choices=(1,2,3),default=1)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-mirror-slopes')
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    label,path,traces,_ = load(args.launch)
    if len(set(args.rows)) != len(args.rows) or any(not 0 <= i < 391 for i in args.rows):
        parser.error('choose distinct slab indices in [0,390]')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    keys = [digest(path),lake('lean','--version')]
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        records = list(pool.map(lambda i: verify(i,label=label,traces=traces,keys=keys,
                                                 cache=args.cache.resolve(),args=args),args.rows))
    if args.output:
        save(args.output,{'endpoint':label,'packet_sha256':keys[0],'rows':records})


if __name__ == '__main__':
    main()
