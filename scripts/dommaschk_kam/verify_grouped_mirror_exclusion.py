"""Certify a signed, uninterrupted submirror prefix with shared affine-clock Taylor models."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as F
from functools import lru_cache
from math import ceil, comb
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model, R0M
from emit_position_slabs import step
from emit_sparse_taylor_slab import ROOT, field, model_literal
from screen_mirror_prefix_signs import gap_model
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules, union
from verify_mirror_endpoint_signs import header, gap_proof
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_pre_mirror_signs import offsets
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import joint_row


BASE = 'GroupedMirrorFieldCache'
GAPS = 'GroupedMirrorGapCache'
JOINT = 'GroupedMirrorJointCache'
ROWS = 'GroupedMirrorRowCache'
FINAL = 'GroupedMirrorOrderedCache'
THEORY = 'DommaschkGroupedMirrorModels'


def compose(p,a,b):
    """Exact ascending coefficients of p(a+b*x)."""
    return [sum(c*comb(k,j)*a**(k-j)*b**j for k,c in enumerate(p) if k>=j)
            for j in range(len(p))]


def span_models(traces):
    """Enclose the original rows on a common affine clock, caching their individual models."""
    @lru_cache(None)
    def row(i):
        radial,(_,z,c,s),_ = joint_row(i,traces)
        return radial,z,c,s

    def grouped(a,b):
        n = b-a
        m = (a+b-1)//2
        group = []
        for k,centre in enumerate(row(m)):
            poly = compose(centre.a,a+b-1-2*m,n)
            error = 0
            for j in range(a,b):
                local = compose(poly,F(2*j+1-a-b,n),F(1,n))
                exact = row(j)[k]
                distance = sum(abs(v-w) for v,w in zip(local,exact.a,strict=True))
                error = max(error,ceil(exact.e+distance))
            group.append(Model(poly,error))
        return group

    return grouped


def partition(traces,stop):
    grouped = span_models(traces)

    def visit(a,b):
        tube = grouped(a,b)
        if gap_model(*tube).bound()[1] < 0:
            return [(a,b,tube,[tube])]
        if b-a>1:
            mid = (a+b)//2
            return visit(a,mid)+visit(mid,b)
        r,*rest = tube
        parts = []
        for _,shift,error in offsets(r.e):
            branch = [Model([r.a[0]+shift,*r.a[1:]],error),*rest]
            if gap_model(*branch).bound()[1] >= 0:
                raise ValueError(f'row {a} still contains zero after radial bisection')
            parts.append(branch)
        return [(a,b,tube,parts)]
    return visit(0,stop)


def group_literal(tube):
    return '⟨'+', '.join(map(model_literal,tube))+'⟩'


def gap(name,tube,args):
    r,z,c,s = tube
    cols = (r-R0M,z,c,s)
    end = f'\nend PlasmaLean.Design.{name}\n'
    inp = name+'Inputs'
    src = header(name,['PlasmaLean.Design.'+THEORY])
    src += 'def trial : Inputs := ⟨'+', '.join(map(model_literal,cols))+'⟩\n'+end
    mods = {inp:src}
    for lab,poly in zip('DRZ',('dD','dnR','dnZ'),strict=True):
        mods[name+lab] = header(name,['PlasmaLean.Design.'+inp])+field(poly,cols)+end
    mods = add_shared_powers(mods,inp,name,cols)
    files = []
    for n,decl in mods.items():
        for module in mods:
            decl = decl.replace('public import PlasmaLean.Design.'+module+'\n',
                                'public import '+BASE+'.'+module+'\n')
        files.append((n,decl,[]))
    base = compile_modules(args.cache/(name+'Fields'),files,[],[args.keys,BASE,
        digest(DESIGN/'DommaschkStoredPowers.trace'),digest(DESIGN/(THEORY+'.trace'))],args,BASE)
    src = header(name,[BASE+'.'+name+f for f in 'DRZ'])
    src += 'open DommaschkMirrorEndpointSign DommaschkPreMirrorSigns DommaschkGroupedMirrorModels\n'
    src += 'set_option maxHeartbeats 1600000\n'
    src += gap_proof(False,False,HEIGHTS[0],r,cols)
    src += f'''def group : Group := {group_literal(tube)}

theorem below : group.Below (DommaschkFirstMirrorLaunchSign.height false) := by
  intro w R z t hw hR hr hz hc hs
  apply physical_sign false hR (by norm_num [DommaschkFirstMirrorLaunchSign.height])
  exact sign_on_models hw hr ⟨shifted_mem (u := trial.u) hr
    (eq_of_beq (by kernel_fact)) (by kernel_fact),hz,hc,hs⟩
'''+end
    result = compile_modules(args.cache/name,[(name,src,['below'])],[base[0]],
                             [args.keys,base[1]['key']],args,GAPS)
    return [base,result]


def join(name,tube,parts,providers,packages,args,
         threshold='DommaschkFirstMirrorLaunchSign.height false'):
    r,*_ = tube
    a,*p = r.a
    (_,l,dl),(_,rr,dr) = offsets(r.e)
    src = header(name,[GAPS+'.'+p for p in providers])
    src += 'open DommaschkGroupedMirrorModels\n'
    src += f'''def group : Group := {group_literal(tube)}
theorem below : group.Below ({threshold}) := by
  intro w R z t hw hR hr hz hc hs
  obtain half | half := cover_spatial_radius (bits := 80) (a := {a}) (p := {p})
    (l := {l}) (dl := {dl}) (r := {rr}) (dr := {dr}) (e := {r.e})
    (by norm_num) (by norm_num) (by norm_num) hr
'''
    for provider,part in zip(providers,parts,strict=True):
        src += f'  · change ({model_literal(part[0])}).Mem w R at half\n'
        src += f'    exact {provider}.below hw hR half hz hc hs\n'
    src += f'\nend PlasmaLean.Design.{name}\n'
    return compile_modules(args.cache/name,[(name,src,['below'])],[union(args.cache,packages)],
                           [args.keys,[r['key'] for _,r in packages]],args,JOINT)


def run_group(task,label,traces,args,provider=gap,
              threshold='DommaschkFirstMirrorLaunchSign.height false'):
    a,b,tube,parts = task
    stem = f'Dommaschk{label}Submirror{a:03}To{b:03}'
    packages = []
    if len(parts) == 1:
        pkg = GAPS
        packages.extend(provider(stem,tube,args))
    else:
        pkg = JOINT
        providers = [stem+s for s in ('Left','Right')]
        for n,part in zip(providers,parts,strict=True):
            packages.extend(provider(n,part,args))
        packages.append(join(stem,tube,parts,providers,packages,args,threshold))
    name = stem+'Rows'
    harmonics = [f'DommaschkHarmonicBlock{q:02}' for q in range(a//8,(b-1)//8+1)]
    src = header(name,[pkg+'.'+stem,*['PlasmaLean.Design.'+h for h in harmonics]])
    src += ('open DommaschkGroupedMirrorModels DommaschkMirrorTubeCrossing Certificates.PositionFrameSlabs\n'
            'set_option maxHeartbeats 1000000\n')
    labels = []
    for i in range(a,b):
        p = f'(DommaschkHarmonicBlock{i//8:02}.packet {i%8})'
        offset,scale = F(2*i+1-a-b,b-a),F(1,b-a)
        clock = f'(({i}:ℕ):ℝ)' if i<2 else f'({i}:ℝ)'
        start = clock if i<2 else str(i)
        for direction,back,tr in zip(('back','fwd'),('true','false'),traces,strict=True):
            tag = f'{direction}{i:03}'
            src += f'def {tag}Row : Step := {step(tr["steps"][i])}\n'
            src += f'''private theorem {tag}Covers : Covers (i := {i}) {p} {back} {tag}Row
    ({offset}) ({scale}) {stem}.group := by
  constructor <;> kernel_fact
theorem {tag}_below {{prev : State}} {{x : Plane}} {{t : ℝ}}
    (ht : t ∈ Set.Icc ({clock}/64) (({clock}+1)/64))
    (hx : x ∈ (physicalSlab prev {tag}Row ({start}/64)).tube t) :
    strength {('(-t)' if back=='true' else 't')} x < {threshold} :=
  {tag}Covers.below {stem}.below ht hx
'''
            labels.append(tag+'_below')
    src += f'\nend PlasmaLean.Design.{name}\n'
    rec = compile_modules(args.cache/name,[(name,src,labels)],[union(args.cache,packages)],
                          [args.keys,[r['key'] for _,r in packages],*[digest(DESIGN/(h+'.trace')) for h in harmonics]],
                          args,ROWS)
    packages.append(rec)
    print(f'{label} signed rows {a}..{b-1}: {rec[1]["key"]}',flush=True)
    return {'start':a,'stop':b,'module':name,'key':rec[1]['key'],'pieces':len(parts)},packages


def ordered(label,groups,packages,args,threshold='DommaschkFirstMirrorLaunchSign.height false'):
    stop = groups[-1]['stop']
    name = f'Dommaschk{label}SubmirrorPrefix{stop:03}'
    src = header(name,['PlasmaLean.Certificates.PositionFrameObservables',
                       *[ROWS+'.'+g['module'] for g in groups]])
    src += ('open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing\n'
            'set_option maxHeartbeats 3500000\n')
    for d,t in [('back','(-t)'),('fwd','t')]:
        mods = [(i,g['module']+'.'+d+f'{i:03}') for g in groups for i in range(g['start'],g['stop'])]
        src += f'def {d}Rows : List Step := [\n  '+',\n  '.join(m+'Row' for _,m in mods)+']\n'
        src += f'theorem {d}_below (entry : State) : OnTubes (fun t p => strength {t} p <\n'
        src += f'    {threshold}) entry 0 {d}Rows := by\n'
        src += '  rw [show (0 : ℝ) = ((0 : ℕ) : ℝ) / 64 by norm_num]\n'
        for i,m in mods:
            src += f'  refine OnTubes.cons_at {i} ?_ ?_\n  · intro t ht x hx\n'
            src += f'    apply {m}_below (hx := hx)\n'
            src += '    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat] using ht\n'
        src += '  trivial\n'
    src += f'\nend PlasmaLean.Design.{name}\n'
    overlay = union(args.cache,packages)
    root,r = compile_modules(args.cache/name,[(name,src,['back_below','fwd_below'])],[overlay],
                             [args.keys,[g['key'] for g in groups],digest(DESIGN.parent/'Certificates/PositionFrameObservables.trace')],args,FINAL)
    return {k:r[k] for k in ('module','key','theorems','axioms')} | {'import_paths':[str(root),str(overlay)]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch',type=int,default=478)
    parser.add_argument('--workers',type=int,choices=range(1,7),default=1)
    parser.add_argument('--groups',type=int,nargs='+',help='only verify groups with these starting rows')
    parser.add_argument('--prefix-length',type=int,
                        help='reuse full groups but bind just the first N rows for a shorter physical trace')
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-mirror-exclusion')
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    label,path,traces,brackets = load(args.launch)
    tasks = partition(traces,brackets[0][0])
    if args.prefix_length is not None:
        if args.groups or not 1 <= args.prefix_length <= brackets[0][0]:
            parser.error('choose a positive prefix through the first lower bracket without --groups')
        tasks = [t for t in tasks if t[0]<args.prefix_length]
    if args.groups:
        tasks = [t for t in tasks if t[0] in args.groups]
        if len(tasks) != len(set(args.groups)):
            parser.error('requested an unknown group index')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    args.keys = [digest(path),lake('lean','--version')]
    args.cache = args.cache.resolve()
    # Check the split near the contact and the first broad group before the remaining groups.
    if len(tasks)>1:
        tasks = [tasks[-1],*tasks[:-1]]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        verified = sorted(pool.map(lambda t: run_group(t,label,traces,args),tasks),
                          key=lambda result:result[0]['start'])
    groups = [g for g,_ in verified]
    if args.prefix_length is not None:
        groups = [{**g,'stop':min(g['stop'],args.prefix_length)} for g in groups]
    packages = [p for _,ps in verified for p in ps]
    result = {'endpoint':label,'packet_sha256':args.keys[0],'groups':groups}
    if not args.groups:
        result.update(ordered(label,groups,packages,args))
        print(f'{result["module"]}: {result["key"]}',flush=True)
    if args.output:
        save(args.output,result)


if __name__ == '__main__':
    main()
