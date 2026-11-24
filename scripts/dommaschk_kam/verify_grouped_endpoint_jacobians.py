"""Share the nine physical QA2R polynomials across consecutive projected trial rectangles."""
import argparse
from fractions import Fraction as F
from math import ceil
from pathlib import Path
import subprocess

from bounce_mirror_pilot import Model, angle_models, evaluate
from endpoint_reflected_trials import paired_rows
from grouped_profile_harmonics import prepare
from screen_endpoint_jacobian_sharing import first_failure, native_jet, own_models
from screen_independent_endpoint_frames import trial_frames
from verify_backward_physical_prefix import compile_modules
from verify_endpoint_reference_slabs import ENDPOINTS
from verify_grouped_mirror_exclusion import compose
from verify_harmonic_group_exclusion import harmonics, inputs
from verify_horner_endpoint_jacobian import DATA
from verify_native_action_models import emit_horner_field
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


FIELDS = 'GroupedTrialJetCache'
ENDPOINT_LABELS = tuple(ENDPOINTS)


def tube(pairs,section=0):
    """Enclose the four original trial coordinates under the common affine clock."""
    start,stop = pairs[0].index,pairs[-1].index+1
    n = stop-start
    rows = []
    for pair in pairs:
        w = angle_models(F(2*pair.index+1,128),F(1,128),F(0))
        c,s = (w[2],w[1]) if section==0 else (-w[2],-w[1])
        rows.append([*own_models(pair),c,s])
    m = (start+stop-1)//2
    out = []
    for k,center in enumerate(rows[m-start]):
        poly = compose(center.a,start+stop-1-2*m,n)
        e = 0
        for i,row in enumerate(rows,start):
            original = row[k]
            local = compose(poly,F(2*i+1-start-stop,n),F(1,n))
            e = max(e,ceil(original.e+sum(abs(a-b) for a,b in zip(local,original.a,strict=True))))
        out.append(Model(poly,e))
    return out


def shared_jet(stem,box,args):
    item,coordinates = inputs(stem+'Inputs',box)
    terms = [item]
    models = []
    providers = []
    for tag,symbol,_,channels,(_,sta) in args.native_data:
        fld,model = emit_horner_field(stem+tag,symbol,channels,coordinates,sta['module'],item[0],DATA,FIELDS)
        terms.append(fld)
        models.append(model)
        providers.append(fld[0])
    name = stem+'Fields'
    source = 'module\n'+''.join('public import '+FIELDS+'.'+p+'\n' for p in providers)
    terms.append((name,source,[]))
    result = compile_modules(args.cache/name,terms,[args.native_links],
        [FIELDS,args.keys,*[p[1]['key'] for p in args.native_static],digest(DESIGN/'DommaschkGroupedHarmonicGap.trace')],
        args,FIELDS)
    return result,models,providers


def restricted(models,a,b,i):
    lo,hi = F(2*i-a-b,b-a),F(2*i+2-a-b,b-a)
    row = [m.restrict(lo,hi) for m in models]
    return [row[j:j+3] for j in (0,3,6)]


def trial_data(label,start,stop):
    """Group the physical coordinates, retaining every required signed matrix and budget."""
    packet=RECORD.with_name(f'bounce_frame_{label[:2]}_u{label[3:]}.json.gz')
    section=int(label[1])
    if section:
        rows=[[(1,forward),(-1,back)] for forward,back in trial_frames(packet,start,stop-1)]
    else:
        rows=[[(None,pair)] for pair in paired_rows(packet,start,stop-1)]
    box=tube([row[0][1] for row in rows],section)
    r,z,c,s=box
    waves=harmonics(c,s)
    candidate=[evaluate(term,(r,z),waves)[0] for triple in native_jet() for term in triple]
    failures={}
    for branches in rows:
        i=branches[0][1].index
        local=restricted(candidate,start,stop,i)
        for sign,pair in branches:
            panel=first_failure(local,pair)
            if panel is not None:
                failures[i if sign is None else f'{i}:{sign}']=panel
    return packet,rows,box,candidate,failures


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--span',type=int,nargs=2,required=True,metavar=('FIRST','STOP'))
    p.add_argument('--endpoint',choices=ENDPOINT_LABELS,default='q0r478')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-trial-jacobians')
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--preflight',action='store_true',help='evaluate the exact eight-panel matrix test without compiling')
    p.add_argument('--rows',type=int,nargs='+',help='check only the specified moving frames in this group')
    p.add_argument('--handoff',type=Path,help='atomically add accepted rows to a running endpoint campaign')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    a,b = args.span
    if not 0<=a<b<=391:
        p.error('the trial span must be a nonempty subset of the original trace')
    if args.rows and (len(set(args.rows))!=len(args.rows) or any(i<a or i>=b for i in args.rows)):
        p.error('requested rows must be distinct indices in the trial span')
    packet,rows,box,candidate,failures=trial_data(args.endpoint,a,b)
    if args.preflight:
        save(args.output,dict(start=a,stop=b,packet_sha256=digest(packet),failures=failures))
        return
    if failures:
        raise ValueError(f'original frame budget fails on eight-panel test: {failures}')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean_path = lake('printenv','LEAN_PATH')
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.cache = args.cache.resolve()
    args.keys = [[digest(packet)],lake('lean','--version')]
    prepare(args)
    stem = f'Dommaschk{args.endpoint.upper()}GroupedTrial{a:03}To{b:03}'
    result,models,providers = shared_jet(stem,box,args)
    if any(x.a != y.a or x.e != y.e for x,y in zip(models,candidate,strict=True)):
        raise ValueError('screened polynomials differ from the physical Horner proof models')
    if args.fields_only:
        save(args.output,dict(start=a,stop=b,key=result[1]['key'],module=result[1]['module'],
                              wall_seconds=result[1]['wall_seconds'],peak_rss_kib=result[1]['peak_rss_kib']))
        return
    from grouped_trial_jacobian_rows import finish
    finish(stem,a,b,rows,result,models,providers,args)


if __name__=='__main__':
    main()
