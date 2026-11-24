"""Enclose the incoming field strength on four original opposite-section trajectories."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import json
from pathlib import Path
from types import SimpleNamespace

from emit_position_slabs import step
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_common_endpoint_traces import ENDPOINTS
from verify_grouped_mirror_exclusion import GAPS, ROWS, ordered
from verify_harmonic_group_exclusion import field_margins, native_gap
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_native_action_models import static_data, verify_static
from verify_opposite_mirror_caps import bracket_nodes
from verify_opposite_submirror import FINAL, LABELS, THEORY, ground_source, read_packet, shared_group
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def partition(traces, limits, channels):
    """Try a common clock, splitting time or radial labels only when the sign needs it."""
    def split(labels, a, b):
        tube = shared_group({e:traces[e] for e in labels}, a, b)
        upper = field_margins(tube, channels)
        if upper < 0:
            return [(labels, a, b, tube, upper)]
        if b-a >= 4 or (len(labels) == 1 and b-a > 1):
            mid = (a+b)//2
            return split(labels,a,mid) + split(labels,mid,b)
        if len(labels) > 1:
            mid = len(labels)//2
            return split(labels[:mid],a,b) + split(labels[mid:],a,b)
        raise ValueError(f'{labels[0]} row {a} needs a narrower enclosure')
    stop = min(limits.values())
    tasks = []
    for a in range(0,stop,20):
        tasks.extend(split(LABELS,a,min(a+20,stop)))
    for e in LABELS:
        if limits[e] > stop:
            tasks.extend(split((e,),stop,limits[e]))
    return tasks


def row_proofs(label, traces, start, stop, field):
    name = f'DommaschkOppositeIncoming{label.upper()}{start:03}To{stop:03}'
    blocks = [f'DommaschkHarmonicBlock{k:02}' for k in range(start//8,(stop-1)//8+1)]
    src = header(name,[GAPS+'.'+field,'PlasmaLean.Design.'+THEORY,*['PlasmaLean.Design.'+b for b in blocks]])
    src += 'open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkOppositeMirrorExclusion\n'
    proofs = []
    for i in range(start,stop):
        a = Fraction(2*i+1-start-stop,stop-start)
        b = Fraction(1,stop-start)
        clock = f'(({i}:ℕ):ℝ)'
        packet = f'(DommaschkHarmonicBlock{i//8:02}.packet {i%8})'
        for tr in traces:
            back = tr['direction'] == -1
            tag = ('back' if back else 'fwd')+f'{i:03}'
            phase = '(-t)' if back else 't'
            src += f'def {tag}Row : Step := {step(tr["steps"][i])}\n'
            src += f'''private theorem {tag}Fit : FitsRow (i := {i}) {packet} {str(back).lower()} {tag}Row
    ({a}) ({b}) {field}.group := by constructor <;> kernel_fact
theorem {tag}_below {{prev : State}} {{x : Plane}} {{t : ℝ}}
    (ht : t ∈ Set.Icc ({clock}/64) (({clock}+1)/64))
    (hx : x ∈ (physicalSlab prev {tag}Row ({clock}/64)).tube t) :
    strength (Real.pi/2 + {phase}) x < DommaschkFirstMirrorLaunchSign.height false :=
  {tag}Fit.below {field}.below ht hx
'''
            proofs.append(tag+'_below')
    return (name,src+f'end PlasmaLean.Design.{name}\n',proofs),blocks


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--calibrated',type=Path,help='calibrated common-torus family to observe')
    p.add_argument('--limit',type=int,help='use at most this many incoming rows in each direction')
    p.add_argument('--screen-only',action='store_true')
    p.add_argument('--workers',type=int,choices=(1,2,3,4),default=1)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-incoming-fields')
    p.add_argument('--static-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    if args.limit is not None and args.limit < 1:
        p.error('expected a positive row limit')
    traces,packets,limits = {},{},{}
    for e in LABELS:
        traces[e],packets[e] = read_packet(e)
        bounds = [a for _,_,_,j,a,_ in bracket_nodes(e) if j == 0]
        limits[e] = min(bounds) if args.limit is None else min(*bounds,args.limit)
    args.channels = static_data()
    tasks = partition(traces,limits,args.channels)
    data = dict(packets=packets,limits=limits,kernel_checked=False,
                groups=[dict(labels=ls,start=a,stop=b,upper=str(u)) for ls,a,b,_,u in tasks])
    if args.screen_only:
        save(args.output,data)
        return
    env(args)
    args.cache = args.cache.resolve()
    args.static = verify_static(SimpleNamespace(cache=args.static_cache,fields=range(4),lean=args.lean,
                                                lean_path=args.lean_path),args.channels)
    def verify(task):
        ls,a,b,tube,upper = task
        stem = 'DommaschkOppositeShared'+''.join(e[3:] for e in ls)+f'From{a:03}To{b:03}'
        local = SimpleNamespace(**vars(args))
        local.keys = [args.version,*[packets[e] for e in ls]]
        local.drop = Fraction(0)
        local.clearance = False
        fields = native_gap(stem,tube,local)
        if local.upper != upper:
            raise ValueError('screen and proof use different physical upper bounds')
        field = fields[-1][1]
        overlay = union(args.cache,fields)
        results = []
        for label in ls:
            item,blocks = row_proofs(label,traces[label],a,b,stem)
            keys = [args.version,packets[label],field['key'],digest(DESIGN/(THEORY+'.trace')),
                    *[digest(DESIGN/(x+'.trace')) for x in blocks]]
            proved = compile_modules(args.cache/item[0],[item],[overlay],keys,args,ROWS)
            row = dict(start=a,stop=b,module=item[0],key=proved[1]['key'],field=field['key'])
            results.append((label,row,[*fields,proved]))
        print(stem,field['key'],flush=True)
        return results
    args.keys = [args.version,packets]
    lists = {e:[] for e in LABELS}
    deps = {e:[] for e in LABELS}
    with ThreadPoolExecutor(args.workers) as workers:
        for result in workers.map(verify,tasks):
            for e,row,packages in result:
                lists[e].append(row)
                deps[e].extend(packages)
    completed = {}
    for e in LABELS:
        rows = sorted(lists[e],key=lambda r:r['start'])
        if [i for r in rows for i in range(r['start'],r['stop'])] != list(range(limits[e])):
            raise ValueError(f'incomplete ordered signed cover at {e}')
        completed[e] = ordered('Opposite'+e.upper(),rows,deps[e],args,opposite=True)
    data.update(kernel_checked=True,ordered=completed)
    if args.calibrated:
        cal = json.loads(args.calibrated.read_text())
        counts = cal['lengths_each_direction']
        suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
        if cal['module'] != 'DommaschkCalibratedFamily'+suffix:
            raise ValueError('expected the calibrated common-torus family')
        parents = [cal,*completed.values()]
        for record in parents:
            admitted(Path(record['import_paths'][0]),record['module'],record['key'])
        keys = [r['key'] for r in parents]
        roots = [Path(s) for r in parents for s in r['import_paths']]
        imports = merge_import_roots(args.cache,roots,keys)
        item = ground_source('DommaschkCommonEndpointTraces'+suffix,cal['module'],counts,
                             [completed[e]['module'] for e in LABELS],coverage=limits)
        root,rec = compile_modules(args.cache/item[0],[item],[imports],keys,args,FINAL)
        data['actual'] = {k:rec[k] for k in ('module','key','axioms','theorems')}
        data['actual'].update(lengths={e:min(counts[e],limits[e]) for e in LABELS},
                              calibrated_key=cal['key'],import_paths=[str(root),str(imports)])
    save(args.output,data)


if __name__ == '__main__':
    main()
