"""Recover a section-zero backward residual from the forward components and its own exact budget."""

import argparse
from fractions import Fraction
from math import isqrt
from pathlib import Path
import subprocess
import sys

from emit_reflected_reference import render
from screen_reflected_reference import check, paired_jobs
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_physical_launches import reports
from verify_endpoint_reference_slabs import ENDPOINTS, PACKAGE as FORWARD
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, key_of, save


PACKAGE = 'ReflectedEndpointResidualCache'
THEOREMS = ['exact_pair','forward_sharp','physical_defect']


def screen(label,packet):
    rows=[]
    scale=2**80
    for pair in paired_jobs(packet):
        i,square,_,budget=check(pair)
        scaled=square*scale**2
        sharp=isqrt(scaled.numerator//scaled.denominator)+1
        ratio=Fraction(sharp,scale)/budget
        rows.append((i,ratio))
    worst=max(rows,key=lambda x:x[1])
    return {'endpoint':label,'packet_sha256':digest(packet),'tested':len(rows),
            'failed':[i for i,r in rows if r>1],'worst_index':worst[0],'worst_ratio':str(worst[1])}


def declarations(name,source):
    return [(name,source,THEOREMS)]


def reflected_source(packet,i,forward,backward):
    source=render(packet,i,FORWARD,forward_name=forward,backward_name=backward)
    ending='end PlasmaLean.Design.'+backward+'\n'
    if not source.endswith(ending):
        raise ValueError('unexpected reflected certificate namespace')
    return source.removesuffix(ending) + '''abbrev reference := backReference
abbrev frame := backFrame
abbrev budget := backBudget

''' + ending


def checked_reflected_parent(row,root,version):
    f=row['reflected_forward']
    lab,i=row['endpoint'],row['index']
    expected=f'DommaschkTraceResidual{lab.upper()}Forward{i:03}'
    if f['module'] != expected:
        raise ValueError('incorrect forward residual in reflection receipt')
    froot=Path(f['root'])
    admitted(froot,expected,f['key'])
    name=row['module']
    source=(root/PACKAGE/(name+'.lean')).read_text()
    inputs=[PACKAGE,row['packet_sha256'],version,f['key'],digest(DESIGN/'DommaschkSectionReflection.trace')]
    if key_of([inputs,declarations(name,source)]) != row['key']:
        raise ValueError('forward residual key does not match the reflected proof')
    return froot


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=ENDPOINTS[1:4],required=True)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--row',type=int)
    mode.add_argument('--screen',action='store_true',help='retest all signed budgets with the dyadic sharp bound')
    p.add_argument('--forward',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/endpoint-reflected-residuals')
    a=p.parse_args()
    if a.row is not None and not 0<=a.row<391:
        p.error('row must lie between 0 and 390')
    a.cache=a.cache.resolve()
    label,i=a.endpoint,a.row
    packet=RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
    if a.screen:
        save(a.output,screen(label,packet))
        return
    checksum=digest(packet)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    version=lake('lean','--version')
    forward=a.forward
    if forward is None:
        forward=a.cache/'forward'/label/f'{i:03}.json'
        forward.parent.mkdir(parents=True,exist_ok=True)
        subprocess.run([sys.executable,Path(__file__).with_name('verify_endpoint_reference_slabs.py'),
            '--endpoints',label,'--range',str(i),str(i),'--direction','1','--workers','1','--shared','--output',forward],
            check=True,cwd=ROOT)
    f,=(r for r in reports([forward]) if (r['endpoint'],r['index'],r['direction'])==(label,i,1))
    fname=f'DommaschkTraceResidual{label.upper()}Forward{i:03}'
    if (f['module'],f['packet_sha256'],f['section_in_half_pi'],Fraction(f['launch_u'])) != (
            fname,checksum,0,Fraction(int(label[3:]),1000)):
        raise ValueError('expected the original forward proof from the same phase-zero row')
    froot,=map(Path,f['import_paths'])
    admitted(froot,fname,f['key'])
    bname=f'DommaschkTraceResidual{label.upper()}Back{i:03}'
    source=reflected_source(packet,i,fname,bname)
    root,r=compile_modules(a.cache/bname,declarations(bname,source),[froot],
        [PACKAGE,checksum,version,f['key'],digest(DESIGN/'DommaschkSectionReflection.trace')],a,PACKAGE)
    back={k:v for k,v in r.items() if k!='artifacts'}
    back.update(endpoint=label,launch_u=f['launch_u'],section_in_half_pi=0,index=i,direction=-1,
                lean_version=version,packet_sha256=checksum,import_paths=[str(root)],package=PACKAGE,
                reflected_forward={'module':fname,'key':f['key'],'root':str(froot)})
    save(a.output,[back,f])
    print(f'{bname}.physical_defect {r["key"]}',flush=True)


if __name__=='__main__':
    main()
