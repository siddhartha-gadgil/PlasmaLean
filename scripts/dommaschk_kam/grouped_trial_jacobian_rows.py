"""Restrict a physical grouped jet and check each original moving frame."""
from fractions import Fraction as F
import json
import os
from pathlib import Path
from tempfile import NamedTemporaryFile

from bounce_mirror_pilot import R0M, angle_models
from emit_sparse_taylor_slab import model_literal
from screen_endpoint_jacobian_sharing import own_models
from verify_backward_physical_prefix import compile_modules, union
from verify_grouped_endpoint_jacobians import ENDPOINT_LABELS, FIELDS, restricted
from verify_horner_endpoint_jacobian import JACOBIAN, SYMBOLS, TAGS, endpoint_modules, inputs_source
from verify_mirror_physical_hit import admitted
from verify_native_action_models import footer, header
from verify_physical_trace_slabs import DESIGN, digest, key_of, save

LOCAL = 'GroupedTrialLocalInputCache'
ADAPTER = 'GroupedTrialRestrictedCache'


def restrict_source(name, local, group, fields, jet, a, b):
    boxes = group+'Inputs'
    src = header(name,[LOCAL+'.'+local,FIELDS+'.'+group+'Fields',
                       'PlasmaLean.Design.DommaschkGroupedTrialJet'])
    src += f'''private def small : Inputs :=
  ⟨{local}.displacement, {local}.vertical, {local}.phase .cos1, {local}.phase .sin1⟩
private def large : Inputs :=
  ⟨{boxes}.displacement, {boxes}.vertical, {boxes}.group.cosine, {boxes}.group.sine⟩
private theorem fits : DommaschkGroupedTrialJet.BoxMap ({a}) ({b}) small large := by
  constructor <;> kernel_fact

private theorem coordinates {{s u z θ : ℝ}} (hs : |s| ≤ 1) (hu : {local}.displacement.Mem s u)
    (hz : {local}.vertical.Mem s z) (waves : ∀ w, ({local}.phase w).Mem s (w.value θ)) :
    |(({a} : ℚ) : ℝ) + (({b} : ℚ) : ℝ)*s| ≤ 1 ∧
      large.Mem ((({a} : ℚ) : ℝ) + (({b} : ℚ) : ℝ)*s) u z (Real.cos θ) (Real.sin θ) :=
  fits.mem hs ⟨hu,hz,waves .cos1,waves .sin1⟩
'''
    for tag,field,symbol,model in zip(TAGS,fields,SYMBOLS,(m for triple in jet for m in triple),strict=True):
        src += f'''
namespace {tag}
def model : Model := {model_literal(model)}
theorem sound {{s u z θ : ℝ}} (hs : |s| ≤ 1) (hu : {local}.displacement.Mem s u)
    (hz : {local}.vertical.Mem s z) (waves : ∀ w, ({local}.phase w).Mem s (w.value θ)) :
    model.Mem s (evR u z (Real.cos θ) (Real.sin θ) {symbol}) := by
  obtain ⟨clock, point⟩ := coordinates hs hu hz waves
  apply DommaschkGroupedTrialJet.Pullback.mem (a := {a}) (b := {b})
    (group := {field}.model) (by kernel_fact) hs
  exact {field}.sound clock point.1 point.2.1 ({boxes}.angles clock point.2.2.1 point.2.2.2)
end {tag}
'''
    return name,src+footer(name),[t+'.sound' for t in TAGS]


def matrix_keys(parents, checksum, version):
    return [JACOBIAN,version,checksum,digest(DESIGN/'DommaschkGroupedTrialJet.trace'),
            *[p['key'] for p in parents],digest(DESIGN/'DommaschkJacobianPanels.trace')]


def checked_grouped_roots(row, root, version):
    label, i = row['endpoint'],row['index']
    a,b = row['grouped_trial']
    if label not in ENDPOINT_LABELS or not 0 <= a <= i < b <= 391:
        raise ValueError('wrong grouped-trial endpoint or row')
    stem = f'Dommaschk{label.upper()}GroupedTrial{a:03}To{b:03}'
    basis = stem+f'Row{i:03}'
    parents = row['grouped_parents']
    expected = [*['DommaschkHornerJetData'+t for t in TAGS],stem+'Fields',basis+'Input',basis+'Restricted']
    if [p['module'] for p in parents] != expected:
        raise ValueError('incomplete or inconsistent grouped-trial dependency names')
    for parent in parents:
        admitted(Path(parent['root']),parent['module'],parent['key'])
    name = row['module']
    declarations = []
    for module in (name+'Panels',name+'Bounds',name):
        claims = [t.split('.')[-1] for t in row['theorems']] if module==name else []
        declarations.append((module,(root/JACOBIAN/(module+'.lean')).read_text(),claims))
    if key_of([matrix_keys(parents,row['packet_sha256'],version),declarations]) != row['key']:
        raise ValueError('grouped-trial parents do not match the accepted frame matrix')
    return [Path(p['root']) for p in parents]


def handoff(row, source, campaign):
    """Let the existing campaign discover one complete immutable row during its next scan."""
    from verify_endpoint_trace_campaign import records_for
    status = json.loads((campaign/'status.json').read_text())
    i, label, checksum = row['index'],row['endpoint'],row['packet_sha256']
    if (status['endpoint'] != label or status['packet_sha256'] != checksum or
            not 0 < i < status['target_length_each_way']):
        raise ValueError('handoff does not match the active physical trace')
    dest = campaign/'jacobians'/f'{i:03}.json'
    if i not in records_for(source,'jacobians',label,checksum):
        raise ValueError('grouped matrix was not admitted by the trace campaign')
    if ['jacobians',i] in status['active_jobs']:
        return 'already being proved'
    with NamedTemporaryFile(dir=dest.parent,prefix='.incoming-') as packet:
        packet.write(source.read_bytes())
        packet.flush()
        try:
            os.link(packet.name,dest)
            return 'installed'
        except FileExistsError:
            if i not in records_for(dest,'jacobians',label,checksum):
                raise ValueError(f'incumbent record is incompatible: {dest}')
            return 'already installed'


def finish(stem,start,stop,rows,group,models,providers,args):
    results = []
    packet = args.keys[0][0]
    version = args.keys[1]
    section=int(args.endpoint[1])
    for branches in rows:
        pair=branches[0][1]
        i = pair.index
        if args.rows and i not in args.rows:
            continue
        prefix = stem+f'Row{i:03}'
        r,z = own_models(pair)
        angles=angle_models(F(2*i+1,128),F(1,128),F(0))
        if section:
            angles=[wave.integer((-1)**((j+1)//2)) for j,wave in enumerate(angles)]
        local = inputs_source(prefix+'Input',i,(r,r-R0M,z,angles),section)
        angle_traces = [digest(DESIGN/'DommaschkOppositeHarmonic.trace')] if section else []
        inp = compile_modules(args.cache/local[0],[local],[],
                              [LOCAL,packet,version,digest(DESIGN/f'DommaschkHarmonicBlock{i//8:02}.trace'),
                               *angle_traces],
                              args,LOCAL)
        jet = restricted(models,start,stop,i)
        res = restrict_source(prefix+'Restricted',local[0],stem,providers,jet,
                              F(2*i+1-start-stop,stop-start),F(1,stop-start))
        sources = [*args.native_static,group,inp]
        adapted = compile_modules(args.cache/res[0],[res],[union(args.cache,sources)],
            [ADAPTER,version,*[m['key'] for _,m in sources],digest(DESIGN/'DommaschkGroupedTrialJet.trace')],
            args,ADAPTER)
        sources.append(adapted)
        parents = [{'root':str(path),'key':m['key'],'module':m['module']} for path,m in sources]
        links=union(args.cache,sources)
        pair_results=[]
        for sign,frame in branches:
            mods = endpoint_modules(args.endpoint,frame,jet,[res[0]+'.'+t for t in TAGS],
                                    local[0],matrix_sign=sign,field_imports=[ADAPTER+'.'+res[0]])
            root,record = compile_modules(args.cache/mods[-1][0],mods,[links],
                                          matrix_keys(parents,packet,version),args,JACOBIAN)
            row = {k:v for k,v in record.items() if k!='artifacts'}
            row.update(endpoint=args.endpoint,launch_u=str(F(int(args.endpoint[3:]),1000)),
                       section_in_half_pi=section,direction=1,index=i,projected_radii=frame.common_radii,
                       paired_trials=True,common_rate=str(frame.common_rate),packet_sha256=packet,
                       lean_version=version,import_paths=[str(root)],grouped_trial=[start,stop],
                       grouped_parents=parents)
            if sign is not None:
                row['matrix_direction']=sign
            checked_grouped_roots(row,root,version)
            save(root/'row.json',row)
            pair_results.append(row)
        results.extend(pair_results)
        save(args.output,results)
        if args.handoff:
            combined=Path(pair_results[0]['import_paths'][0])/'matrix-pair.json'
            save(combined,pair_results)
            state=handoff(pair_results[0],combined,args.handoff)
        else:
            state='verified'
        print(f'{i} {state}'+''.join(f' {m["key"]} {m["wall_seconds"]}s' for m in pair_results),flush=True)
