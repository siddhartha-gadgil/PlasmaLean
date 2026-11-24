"""Bind one group of physical central-field values to the original signed residuals."""
from fractions import Fraction as F
import json
import os
from pathlib import Path
from tempfile import NamedTemporaryFile

from emit_sparse_taylor_slab import model_literal
from grouped_central_models import coordinates
from verify_backward_physical_prefix import compile_modules,union
from verify_grouped_central_defects import FIELDS,LABELS
from verify_horner_endpoint_jacobian import inputs_source
from verify_mirror_physical_hit import admitted
from verify_native_action_models import footer,header
from verify_native_endpoint_residuals import BOUNDS,SYMBOLS,TAGS,sharp_source,wrapper
from verify_physical_trace_slabs import DESIGN,digest,key_of,save

ROW='GroupedCentralRowCache'
PACKAGE='GroupedCentralResidualCache'


def restriction(name,local,group,values,a,b):
    big=group+'Inputs'
    src=header(name,[ROW+'.'+local,FIELDS+'.'+group+'Z','PlasmaLean.Design.DommaschkGroupedTrialJet'])
    src+=f'''private def small : Inputs := ⟨{local}.displacement,{local}.vertical,
  {local}.phase .cos1,{local}.phase .sin1⟩
private def large : Inputs := ⟨{big}.displacement,{big}.vertical,
  {big}.phase .cos1,{big}.phase .sin1⟩
private theorem fits : DommaschkGroupedTrialJet.BoxMap ({a}) ({b}) small large := by
  constructor <;> kernel_fact
private theorem waves (w : Wave) :
    DommaschkGroupedMirrorModels.Fits ({a}) ({b}) ({local}.phase w) ({big}.phase w) := by
  cases w <;> kernel_fact
'''
    for t,s,v in zip(TAGS,SYMBOLS,values,strict=True):
        src+=f'''
namespace {t}
def model : Model := {model_literal(v)}
theorem sound {{s u z θ : ℝ}} (hs : |s| ≤ 1) (hu : {local}.displacement.Mem s u)
    (hz : {local}.vertical.Mem s z) (ang : ∀ w, ({local}.phase w).Mem s (w.value θ)) :
    model.Mem s (evR u z (Real.cos θ) (Real.sin θ) {s}) := by
  obtain ⟨clock,point⟩ := fits.mem hs (u := u) (z := z) (c := Real.cos θ) (v := Real.sin θ)
    ⟨hu,hz,ang .cos1,ang .sin1⟩
  apply DommaschkGroupedTrialJet.Pullback.mem (a := {a}) (b := {b})
    (group := {group}{t}.model) (by kernel_fact) hs
  exact {group}{t}.sound clock point.1 point.2.1 (fun w => (waves w).mem hs (ang w))
end {t}
'''
    return name,src+footer(name),[t+'.sound' for t in TAGS]


def checked_parents(row,root,version):
    label,i,sign=row['endpoint'],row['index'],row['direction']
    a,b=row['central_group']
    if label not in LABELS or not 0<=a<=i<b<=391:
        raise ValueError('invalid central group or original endpoint')
    name=f'Dommaschk{label.upper()}Central{a:03}To{b:03}'
    rowname=name+f'Row{i:03}'
    parents=row['grouped_central_parents']
    if [p['module'] for p in parents]!=['DommaschkHornerJetData'+t for t in TAGS]+[
            name+'Z',rowname+'Restricted',rowname]:
        raise ValueError('inconsistent shared central-field dependencies')
    for p in parents:
        admitted(Path(p['root']),p['module'],p['key'])
    decl=wrapper(label,i,sign,rowname)
    keys=[version,row['packet_sha256'],*[p['key'] for p in parents]]
    if ((root/PACKAGE/(decl[0]+'.lean')).read_text()!=decl[1] or
            key_of([keys,[decl]])!=row['key'] or decl[0]!=row['module']):
        raise ValueError('the grouped residual is not bound to its signed physical parents')
    return [Path(p['root']) for p in parents]


def install(records,source,campaign):
    from verify_endpoint_trace_campaign import records_for
    row=records[0]
    label,i,checksum=row['endpoint'],row['index'],row['packet_sha256']
    status=json.loads((campaign/'status.json').read_text())
    if status['endpoint']!=label or status['packet_sha256']!=checksum:
        raise ValueError('the receiving trajectory uses different original data')
    if i==0 or i>=status['target_length_each_way']:
        return
    if i not in records_for(source,'references',label,checksum):
        raise ValueError('the independent signed continuation backend rejected the grouped row')
    dest=campaign/'references'/f'{i:03}.json'
    with NamedTemporaryFile(dir=dest.parent,prefix='.grouped-') as tmp:
        tmp.write(source.read_bytes())
        tmp.flush()
        try:
            os.link(tmp.name,dest)
        except FileExistsError:
            if i not in records_for(dest,'references',label,checksum):
                raise ValueError(f'incompatible existing reference proof at {dest}')


def finish(stem,start,stop,rows,parents,args):
    results=[]
    for i,(f,b,local,ratios,box,_) in rows.items():
        name=stem+f'Row{i:03}'
        inp=inputs_source(name+'Inputs',i,coordinates(f),0)
        adapter=restriction(name+'Restricted',inp[0],stem,local,F(2*i+1-start-stop,stop-start),F(1,stop-start))
        deps=list(parents)
        links=union(args.cache,deps)
        base=[args.version,args.checksum]
        restricted=compile_modules(args.cache/adapter[0],[inp,adapter],[links],
            [*base,*[m['key'] for _,m in deps],digest(DESIGN/'DommaschkGroupedTrialJet.trace'),
             digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace')],args,ROW)
        deps.append(restricted)
        providers={t:adapter[0]+'.'+t for t in TAGS}|{'Inputs':inp[0]}
        sharp=sharp_source(name,f,b,ratios,box,providers=providers,field_imports=[ROW+'.'+adapter[0]])
        bounds=compile_modules(args.cache/name,[sharp],[union(args.cache,deps)],
              [*base,*[m['key'] for _,m in deps],digest(DESIGN/'DommaschkPhysicalCentralJet.trace'),
               digest(DESIGN/'DommaschkSectionReflection.trace')],args,BOUNDS)
        deps.append(bounds)
        references=[]
        links=union(args.cache,deps)
        sources=[dict(module=m['module'],key=m['key'],root=str(root)) for root,m in deps]
        for sign in (1,-1):
            item=wrapper(args.endpoint,i,sign,name)
            root,m=compile_modules(args.cache/item[0],[item],[links],
                          [*base,*[x['key'] for x in sources]],args,PACKAGE)
            row={k:v for k,v in m.items() if k!='artifacts'}
            row.update(index=i,endpoint=args.endpoint,direction=sign,section_in_half_pi=0,
                launch_u=str(F(int(args.endpoint[3:]),1000)),packet_sha256=args.checksum,
                lean_version=args.version,import_paths=[str(root)],package=PACKAGE,
                central_group=[start,stop],grouped_central_parents=sources)
            checked_parents(row,root,args.version)
            references.append(row)
        source=bounds[0]/'signed-row.json'
        save(source,references)
        if args.handoff:
            install(references,source,args.handoff)
        results.extend(references)
        save(args.output,results)
        print(f'{args.endpoint} {i} both signed central defects accepted',flush=True)
