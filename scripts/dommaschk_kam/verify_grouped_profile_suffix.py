"""Certify groups of original signed 470/478 rows on a common rescaled angular clock."""
import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import json
from pathlib import Path
import re
import subprocess
import sys

from bounce_mirror_pilot import Model, R0M
from emit_sparse_jacobian import derivative_file, header
from emit_sparse_taylor_slab import ROOT, field, model_literal, models
from screen_sparse_jacobians import field_jet
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules
from verify_centered_strength import gradient_item
from verify_grouped_mirror_exclusion import span_models
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import JET


GROUP = 'GroupedProfileProofCache'
SPANS = [(236,247),(247,252),(252,258),(258,263),(263,269),(269,274),(274,280),
         (280,285),(285,291),(291,302),(302,313),(313,319),(319,325)]


def merge(x,y):
    p = [(v+w)//2 for v,w in zip(x.a,y.a,strict=True)]
    err = max(sum(abs(i-j) for i,j in zip(p,m.a,strict=True))+m.e for m in (x,y))
    return Model(p,err)


def group_data(a,b,records):
    tubes = []
    for _,_,traces,_ in records:
        r,z,c,s = span_models(traces)(a,b)
        e = max(r.e,z.e)
        tubes.append((Model(r.a,e),Model(z.a,e),c,s))
    common = tuple(map(merge,*tubes))
    return tubes,common


def sparse_group_fields(name,tube,with_gradient,args):
    if args.backend == 'harmonic' or (args.backend == 'hybrid' and not with_gradient):
        from grouped_profile_harmonics import harmonic_fields
        return harmonic_fields(name,tube,with_gradient,args)
    r,z,c,s = tube
    cols = (r-R0M,z,c,s)
    inp = name+'Inputs'
    end = '\nend PlasmaLean.Design.'+name+'\n'
    mods = {inp:header(['DommaschkJacobianFrames'],'Grouped physical inputs',name,'DommaschkJacobian')
            +'def trial : Inputs := ⟨'+', '.join(map(model_literal,cols))+'⟩\n'+end}
    deps = []
    for symbol,tag,polys in zip(('dD','dnR','dnZ'),'DRZ',field_jet(),strict=True):
        mod = name+tag
        deps.append(mod)
        mods[mod] = header([inp],'Physical polynomial on a group',name,'DommaschkJacobian')+field(symbol,cols)+end
        if with_gradient:
            for axis,letter in enumerate('UZ'):
                mod = name+tag+letter
                deps.append(mod)
                mods[mod] = derivative_file(symbol,'grad'+tag+letter,axis,models(polys[axis+1],cols),
                                            name,inp,'DommaschkJacobian')
    mods[name] = header(deps,'Grouped polynomial values',name,'DommaschkJacobian')+end
    modules = add_shared_powers(mods,inp,name,cols)
    def imports(m):
        return f'public import {JET}.{m[1]}' if m[1] in modules else m[0]
    terms = [(n,re.sub(r'^public import PlasmaLean\.Design\.(\w+)$',imports,src,flags=re.M),[])
             for n,src in modules.items()]
    dependencies = sorted({m for _,src,_ in terms for m in
                         re.findall(r'^public import PlasmaLean\.Design\.(\w+)$',src,flags=re.M)})
    out = compile_modules(args.cache/name,terms,[],
             [args.keys,*[digest(DESIGN/(n+'.trace')) for n in dependencies]],args,JET)
    return out


def gradients(stem,tube,args):
    jet = stem+'Jet'
    r,z,c,s = tube
    fields = sparse_group_fields(jet,tube,True,args)
    item,rates = gradient_item(stem,jet,(r,(r-R0M,z,c,s),{}))
    links = [fields[0],args.native_links] if args.backend=='harmonic' else [fields[0]]
    proof = compile_modules(args.cache/item[0],[item],links,
                            [args.keys,fields[1]['key'],digest(DESIGN/'DommaschkCenteredStrength.trace'),
                             digest(DESIGN/'DommaschkPairedActionProfiles.trace')],args,GROUP)
    return fields,proof,rates


def values(stem,tubes,args):
    result = []
    for tag,tube in zip(('Inner','Outer'),tubes,strict=True):
        r,z,c,s = tube
        center = (Model(r.a),Model(z.a),c,s)
        result.append([sparse_group_fields(stem+tag+suffix,box,False,args)
                       for suffix,box in [('Center',center),('Tube',tube)]])
    return result


def campaign(args,records):
    from verify_mirror_physical_hit import admitted
    from verify_physical_trace_slabs import key_of
    packets = [digest(path) for _,path,_,_ in records]
    code = [Path(__file__).resolve(),*[Path(__file__).with_name(s) for s in
            ('grouped_profile_arithmetic.py','grouped_profile_harmonics.py')]]
    key = key_of([packets,[digest(p) for p in code],SPANS,args.backend,
                  digest(DESIGN/'DommaschkGroupedProfileCompare.trace')])
    output = args.cache.resolve()/'campaign'/key
    output.mkdir(parents=True,exist_ok=True)
    completed,errors = {},{}
    def run(span):
        a,b = span
        path = output/f'{a:03}.json'
        cmd = [sys.executable,str(code[0]),'--group',str(a),'--backend',args.backend,
               '--cache',str(args.cache),'--output',str(path)]
        with (output/f'{a:03}.log').open('w') as log:
            subprocess.run(cmd,check=True,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        d = json.loads(path.read_text())
        expected = f'DommaschkGroupedProfile{a:03}To{b:03}Rows'
        if (d['start'],d['stop'],d['module'],d['packets']) != (a,b,expected,packets):
            raise ValueError(f'wrong signed group receipt {path}')
        admitted(Path(d['import_paths'][0]),expected,d['key'])
        return dict(start=a,stop=b,key=d['key'],receipt=str(path))
    starts = args.groups or [a for a,_ in SPANS]
    if len(starts)!=len(set(starts)):
        raise ValueError('a group was requested twice')
    spans = [(a,dict(SPANS)[a]) for a in starts]
    def update():
        save(args.output,dict(key=key,packets=packets,requested=spans,
                              accepted_rows=sum(r['stop']-r['start'] for r in completed.values()),
                              complete=len(completed)==len(spans),errors=errors,
                              groups=[completed[a] for a in sorted(completed)]))
    update()
    pending = iter(spans)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        active = {}
        while True:
            while len(active)<args.workers and not errors:
                span = next(pending,None)
                if span is None:
                    break
                active[pool.submit(run,span)] = span[0]
            if not active:
                break
            done,_ = wait(active,return_when=FIRST_COMPLETED)
            for job in done:
                a = active.pop(job)
                try:
                    record = job.result()
                except (OSError,ValueError,subprocess.CalledProcessError) as exc:
                    errors[a] = f'{exc}: {output}/{a:03}.log'
                else:
                    completed[a] = record
                    print(a,record['stop'],record['key'],flush=True)
                update()
    if errors:
        raise SystemExit('a grouped comparison failed')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    selection = p.add_mutually_exclusive_group(required=True)
    selection.add_argument('--group',type=int,choices=[a for a,_ in SPANS])
    selection.add_argument('--groups',type=int,nargs='+',choices=[a for a,_ in SPANS])
    selection.add_argument('--all',action='store_true',help='verify all 13 groups and record their signed receipts')
    selection.add_argument('--screen',action='store_true',help='replay every group using exact arithmetic')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-profile-suffix')
    p.add_argument('--backend',choices=('harmonic','sparse','hybrid'),default='harmonic',
                   help='hybrid reuses a checked sparse gradient with harmonic field values')
    p.add_argument('--workers',type=int,choices=range(1,4),default=1)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument('--gradient-only',action='store_true')
    mode.add_argument('--values-only',action='store_true')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    records = [load(k) for k in (470,478)]
    if (args.gradient_only or args.values_only) and args.group is None:
        p.error('intermediate checks require one --group')
    if args.groups or args.all:
        campaign(args,records)
        return
    if args.screen:
        from grouped_profile_arithmetic import screen_group
        groups = [screen_group(a,b,*group_data(a,b,records)) for a,b in SPANS]
        save(args.output,dict(kind='exact arithmetic preflight',packets=[digest(p) for _,p,_,_ in records],
                              rows=sum(b-a for a,b in SPANS),groups=groups))
        return
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    args.cache = args.cache.resolve()
    args.keys = [[digest(path) for _,path,_,_ in records],lake('lean','--version')]
    if args.backend!='sparse':
        from grouped_profile_harmonics import prepare
        prepare(args)
    a,b = args.group,dict(SPANS)[args.group]
    tubes,common = group_data(a,b,records)
    stem = f'DommaschkGroupedProfile{a:03}To{b:03}'
    if args.values_only:
        packages = values(stem,tubes,args)
        save(args.output,dict(start=a,stop=b,values=[[p[1]['key'] for p in ps] for ps in packages]))
        return
    fields,gradient,rates = gradients(stem,common,args)
    if args.gradient_only:
        save(args.output,dict(start=a,stop=b,jet=fields[1]['key'],gradient=gradient[1]['key'],
                              rates=list(map(str,rates)),packets=args.keys[0]))
        print(stem,rates,gradient[1]['key'],flush=True)
        return
    boxes = values(stem,tubes,args)
    from grouped_profile_arithmetic import finish
    finish(stem,a,b,tubes,common,records,fields,gradient,rates,boxes,args)


if __name__=='__main__':
    main()
