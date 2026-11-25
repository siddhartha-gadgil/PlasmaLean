"""Check quantitative transverse first-mirror slopes on the four opposite QA2R launches."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from types import SimpleNamespace

from emit_position_slabs import step
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_harmonic_group_exclusion import inputs
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_native_action_models import emit_horner_field
from verify_opposite_mirror_caps import bracket_nodes
from verify_opposite_submirror import LABELS, read_packet, shared_group
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_physical_first_mirror_values import SIGNS, source_start
from verify_radial_ribbon_slopes import FIELDS, INPUT, RESULT, STATIC, assemble, slope_fields, static, value
from verify_signed_mirror_passage import merge_import_roots


RATE = F(1,256)
GROUPS = [(LABELS[:2],320,329),(LABELS[2:],326,331),(LABELS[2:],331,336)]
ROWS = 'OppositeSlopeRowCache'
BRANCHES = 'OppositeMirrorBranchCache'


def row_source(e,field,group_start,group_stop,start,stop,traces):
    name=f'DommaschkOppositeSlope{e.upper()}From{start}To{stop}'
    blocks=[f'DommaschkHarmonicBlock{k:02}' for k in range(start//8,(stop-1)//8+1)]
    src=header(name,[RESULT+'.'+field,'PlasmaLean.Design.DommaschkOppositeMirrorSlope',
                    *['PlasmaLean.Design.'+x for x in blocks]])
    src+='open Certificates.PositionFrameSlabs DommaschkOppositeMirrorExclusion DommaschkOppositeMirrorSlope\n'
    proofs=[]
    for i in range(start,stop):
        c=F(2*i+1-group_start-group_stop,group_stop-group_start)
        w=F(1,group_stop-group_start)
        for trace in traces:
            back=trace['direction']==-1
            tag=('back' if back else 'fwd')+f'{i:03}'
            bb=str(back).lower()
            src+=f'''def {tag}Row : Step := {step(trace['steps'][i])}
private theorem {tag}Fit : FitsRow (i := {i}) (DommaschkHarmonicBlock{i//8:02}.packet {i%8})
    {bb} {tag}Row ({c}) ({w}) {field}.group := by constructor <;> kernel_fact
theorem {tag}_slope : SlabSlope {bb} {tag}Row ({i}/64) ({i+1}/64) ({RATE}) := by
  have h := slope {tag}Fit {field}.outward
  norm_num at h ⊢
  exact h
'''
            proofs.append(tag+'_slope')
    return (name,src+f'end PlasmaLean.Design.{name}\n',proofs),blocks


def branches_source(e,k,n,bindings,signs,clocks):
    name='DommaschkOppositeMirrorBranches'+e.upper()
    src=source_start(name,['PlasmaLean.Design.DommaschkOppositeMirrorBranches',SIGNS+'.'+signs,
                           *[ROWS+'.'+g['module'] for g in bindings]])
    src+='open DommaschkOppositeMirrorBranches DommaschkOppositeMirrorSlope\n'
    src+='set_option linter.all false\n'
    claims=['forward_window','backward_window','from_original_passage']
    for back,base in enumerate(clocks):
        side='back' if back else 'fwd'
        bb=str(bool(back)).lower()
        for i in range(k,n):
            g,=(r for r in bindings if r['start']<=i<r['stop'])
            row=g['module']+'.'+side+f'{i:03}'
            src+=f'''private theorem {side}{i}w : Window (MirrorEndpoint.start .{e}) {bb} {base}.rows
    ({i}/64) ({i+1}/64) ({RATE}) := by
  have hi : {i} < {base}.rows.length := by change {i} < {n}; norm_num
  have data : {base}.rows[{i}] = {row}Row := by with_unfolding_all rfl
  have h : SlabSlope {bb} {base}.rows[{i}] ({i}/64) ({i+1}/64) ({RATE}) := data.symm ▸ {row}_slope
  have clockEnd : ((({i}:ℕ):ℝ)+1)/64 = {i+1}/64 := by norm_num
  rw [← clockEnd] at h ⊢
  exact @row_window {base}.rows (MirrorEndpoint.start .{e}) {bb} {i} ({RATE}) hi (by norm_num) h
'''
        phrase=f'{side}{n-1}w'
        for i in reversed(range(k,n-1)):
            phrase=f'Window.append {side}{i}w ({phrase}) (by norm_num)'
        title='backward_window' if back else 'forward_window'
        src+=f'''theorem {title} (tail : List Step) :
    Window (MirrorEndpoint.start .{e}) {bb} ({base}.rows++tail) ({k}/64) ({n}/64) ({RATE}) :=
  Window.tail ({phrase}) tail
'''
    src+=f'''theorem from_original_passage {{c : Checkpoint}} {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    {{F B : List Step}} (path : c.Passage .{e} uC zC uA zA φ)
    (angle : |φ-azimuth (MirrorEndpoint.opposite .{e})| ≤ 1/64)
    (fl : c.forwardRows.length = c.length) (bl : c.backwardRows.length = c.length)
    (f : c.forwardRows = {clocks[0]}.rows ++ F) (b : c.backwardRows = {clocks[1]}.rows ++ B)
    (room : {n} < c.length) : FirstBranches .{e} c {k} {n-1} uC zC uA zA φ := by
  apply DommaschkOppositeMirrorBranches.from_passage path (by rfl) _ _ _ _ fl bl room angle
  · rw [f]; exact {signs}.fwd F
  · rw [b]; exact {signs}.back B
  · rw [f,show ((({n-1}:ℕ):ℝ)+1)/64={n}/64 by norm_num]; exact forward_window F
  · rw [b,show ((({n-1}:ℕ):ℝ)+1)/64={n}/64 by norm_num]; exact backward_window B
end PlasmaLean.Design.{name}
'''
    return name,src,claims


def verify_branch(e,limits,rows,parts,packets,args):
    area=json.loads(Path(args.areas.format(label=e)).read_text())
    if (area['endpoint']!=e or area['packet_sha256']!=packets[e]
            or area['brackets']!=[limits[e],limits[e]]):
        raise ValueError('ordered pre-mirror signs and the exterior cap must be for '+e)
    ordered=area['ordered']
    if ordered['module']!='DommaschkArea'+e.upper()+'Sides':
        raise ValueError('unexpected original signed area package')
    admitted(Path(ordered['import_paths'][0]),ordered['module'],ordered['key'])
    k,n=limits[e]
    ordered_rows=sorted(rows[e],key=lambda r:r['start'])
    if [i for x in ordered_rows for i in range(x['start'],x['stop'])]!=list(range(k,n)):
        raise ValueError('slope windows do not cover the complete archived bracket '+e)
    src=branches_source(e,k,n,ordered_rows,ordered['module'],[c['module'] for c in area['clocks']])
    keys=[args.version,packets[e],ordered['key'],[s['key'] for s in ordered_rows],
          digest(DESIGN/'DommaschkOppositeMirrorBranches.trace')]
    overlay=merge_import_roots(args.cache/'branches',[union(args.cache,parts),
                                *map(Path,ordered['import_paths'])],keys)
    root,record=compile_modules(args.cache/src[0],[src],[overlay],keys,args,BRANCHES)
    return {k:record[k] for k in ('module','key','theorems','axioms')} | {
        'prefix_needed':n+1,'incoming_and_caps_key':ordered['key'],'import_paths':[str(root),str(overlay)]}


def group(labels,a,b,traces,tables,packets,args):
    tube = shared_group({e:traces[e] for e in labels},a,b)
    name='DommaschkOppositeMirrorSlope'+''.join(e[3:] for e in labels)+f'From{a}To{b}'
    src,coords=inputs(name+'Inputs',tube)
    vals={tag:value(table,coords[1:]) for tag,_,table in tables}
    providers={tag:name+tag for tag,_,_ in tables}
    final,slack=assemble(name,src[0],providers,vals,tube,rate=RATE)
    row={'labels':labels,'start':a,'stop':b,'squared_rate':str(RATE),'margin':str(slack)}
    if args.screen:
        return row,[]
    keys=[args.version,[packets[e] for e in labels],a,b,digest(DESIGN/'DommaschkGroupedHarmonicGap.trace'),
          digest(DESIGN/'DommaschkDyadicHorner.trace')]
    ir=compile_modules(args.cache/src[0],[src],[],keys,args,INPUT)
    parts=[ir,*args.statics.values()]
    for tag,target,table in tables:
        data=args.statics[tag]
        m,y=emit_horner_field(providers[tag],target,table,coords,data[1]['module'],src[0],STATIC,INPUT,
                              integer=True)
        if (y.a,y.e)!=(vals[tag].a,vals[tag].e):
            raise ArithmeticError(f'{name} {tag} outward model mismatch')
        parts.append(compile_modules(args.cache/m[0],[m],[ir[0],data[0]],
                                     [keys,ir[1]['key'],data[1]['key']],args,FIELDS))
    overlay=union(args.cache,parts)
    top=compile_modules(args.cache/name,[final],[overlay],
        [keys,[p[1]['key'] for p in parts],digest(DESIGN/'DommaschkRibbonSlopeCover.trace')],args,RESULT)
    row.update(module=name,key=top[1]['key'],axioms=top[1]['axioms'],import_paths=[str(top[0]),str(overlay)])
    return row,[*parts,top]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-mirror-slopes')
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--screen',action='store_true')
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--groups',type=int,nargs='+',choices=range(len(GROUPS)))
    p.add_argument('--areas',help='N164 full signed area receipt file pattern containing {label}')
    args=p.parse_args()
    data={e:read_packet(e) for e in LABELS}
    traces={e:v[0] for e,v in data.items()}
    packets={e:v[1] for e,v in data.items()}
    limits={}
    for e in LABELS:
        caps=list(bracket_nodes(e))
        limits[e]=[min(r[-2] for r in caps),max(r[-1] for r in caps)]
        start,stop=limits[e]
        expected=set(range(start,stop))
        if not expected.issubset({i for labels,a,b in GROUPS if e in labels for i in range(a,b)}):
            raise ValueError(e+' lacks full lower-to-upper clock coverage')
    tables=list(slope_fields())
    if not args.screen:
        env(args)
        args.statics=static(tables,SimpleNamespace(**{**vars(args),'cache':ROOT/'.lake/radial-ribbon-slopes'}))
    rows=[];parts=[];bindings={e:[] for e in LABELS}
    for i in args.groups if args.groups is not None else range(len(GROUPS)):
        labels,a,b=GROUPS[i]
        row,packages=group(labels,a,b,traces,tables,packets,args)
        if not args.screen and not args.fields_only:
            field=row['module']
            overlay=union(args.cache,packages)
            added=[]
            for e in labels:
                lo,hi=limits[e];start,stop=max(a,lo),min(b,hi)
                src,blocks=row_source(e,field,a,b,start,stop,traces[e])
                verified=compile_modules(args.cache/src[0],[src],[overlay],[row['key'],packets[e],
                    digest(DESIGN/'DommaschkOppositeMirrorSlope.trace'),
                    *[digest(DESIGN/(x+'.trace')) for x in blocks]],args,ROWS)
                bindings[e].append({'start':start,'stop':stop,'module':src[0],'key':verified[1]['key']})
                added.append(verified)
            packages.extend(added)
        rows.append(row);parts.extend(packages)
        save(args.output,{'kind':'screen' if args.screen else 'fields','packets':packets,'limits':limits,
                          'groups':rows,'bindings':bindings})
        print(labels,a,b,row.get('key',row['margin']),flush=True)
    if args.areas:
        if args.screen or args.fields_only or len(rows)!=len(GROUPS):
            p.error('branch binding requires the complete physical row campaign')
        branches={}
        for e in LABELS:
            branches[e]=verify_branch(e,limits,bindings,parts,packets,args)
            save(args.output,{'kind':'first-mirror-branches','packets':packets,'limits':limits,'groups':rows,
                              'bindings':bindings,'branches':branches})
            print(e,branches[e]['key'],flush=True)


if __name__=='__main__':
    main()
