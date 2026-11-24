"""Replay launch and bracket signs for a reflected Q0 endpoint on its own archived tubes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
import gzip
import json
from pathlib import Path
import subprocess

from bounce_mirror_pilot import HEIGHTS, SCALE
from emit_position_slabs import step
from emit_sparse_taylor_slab import ROOT, RECORD, field, model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_mirror_endpoint_signs import ARCHIVE, endpoint_data, gap_proof, header, point_proof
from verify_physical_trace_slabs import DESIGN, digest, save


INPUTS = 'SecondaryMirrorInputCache'
FIELDS = 'SecondaryMirrorFieldCache'
SIGNS = 'SecondaryMirrorSignCache'
HITS = 'SecondaryMirrorCrossingCache'


def load(launch):
    label = f'Q0R{launch:03}'
    path = RECORD.with_name(f'bounce_frame_q0_u{launch:03}.json.gz')
    packet = json.loads(gzip.decompress(path.read_bytes()))
    traces = packet['traces']
    if (packet['section_in_half_pi'] != 0 or Fraction(packet['launch_u']) != Fraction(launch,1000)
            or packet['coordinate_denominator'] != SCALE or [t['direction'] for t in traces] != [-1,1]):
        raise ValueError(f'wrong reflected Q0 record: {path}')
    sector, = (s for s in json.loads(ARCHIVE.read_text())['sections'] if s['section_in_half_pi'] == 0)
    record, = (e for e in sector['endpoints'] if Fraction(e['launch_radius']) == Fraction(launch,1000))
    b,f = record['crossings']
    if (not (b['success'] and f['success']) or b['brackets'] != f['brackets']
            or tuple(map(Fraction,record['heights'])) != tuple(HEIGHTS)):
        raise ValueError('expected the common reflected bracket and the two fixed QA2R heights')
    brackets = []
    for lower,upper in f['brackets']:
        a,b = 64*Fraction(lower),64*Fraction(upper)
        if a.denominator != 1 or b.denominator != 1 or a >= b:
            raise ValueError('expected an ordered bracket on dyadic nodes')
        brackets.append((int(a),int(b)))
    return label,path,traces,brackets


def tag(label,index,right,upper):
    height = 'Upper' if upper else 'Lower'
    side = 'Right' if right else 'Left'
    return f'Dommaschk{label}Mirror{height}{index:03}{side}'


def snapshot(task, *, label, traces, keys, cache, args):
    i,right,upper = task
    name = tag(label,i,right,upper)
    radial,columns = endpoint_data(i,right,traces)
    end = f'\nend PlasmaLean.Design.{name}\n'
    inp = name+'Inputs'
    source = (header(name,['PlasmaLean.Design.DommaschkBounceTaylor'])
              +'def trial : Inputs := ⟨'+', '.join(map(model_literal,columns))+'⟩\n'+end)
    base = compile_modules(cache/inp,[(inp,source,[])],[],
                           [keys,digest(DESIGN/'DommaschkBounceTaylor.trace'),INPUTS],args,INPUTS)
    fields = []
    for suffix,poly in zip('DRZ',('dD','dnR','dnZ'),strict=True):
        n = name+suffix
        source = header(name,[INPUTS+'.'+inp])+field(poly,columns)+end
        fields.append(compile_modules(cache/n,[(n,source,[])],[base[0]],
                                      [base[1]['key'],FIELDS],args,FIELDS))
    imports = ['PlasmaLean.Design.DommaschkMirrorBracketSlab',
               f'PlasmaLean.Design.DommaschkHarmonicBlock{i//8:02}',
               *[FIELDS+'.'+name+s for s in 'DRZ']]
    source = (header(name,imports)+'open DommaschkMirrorEndpointSign Certificates.PositionFrameSlabs\n'
              +'set_option maxHeartbeats 1600000\n')
    local = point_proof(name,i,upper,right,radial,columns)
    for direction,tr in zip(('Back','Fwd'),traces,strict=True):
        row = direction.lower()+'Row'
        source += f'def {row} : Step := {step(tr["steps"][i])}\n'
        old = f'DommaschkPositionFrames{direction}.block{i//16}[{i%16}]'
        if local.count(old) != 2:
            raise ValueError('unexpected endpoint proof row interface')
        local = local.replace(old,row)
    source += gap_proof(upper,right,HEIGHTS[upper],radial,columns)+local+end
    deps = [base,*fields]
    overlay = union(cache,deps)
    final = compile_modules(cache/name,[(name,source,['sign_on_box','fwd_tube_sign','back_tube_sign'])],
                            [overlay],[keys,[r['key'] for _,r in deps],
                                       *[digest(DESIGN/(s.split('.')[-1]+'.trace')) for s in imports[:2]]],
                            args,SIGNS)
    print(f'{name}: {final[1]["key"]}',flush=True)
    return [*deps,final]


def crossings(label,traces,brackets):
    modules = [tag(label,a,False,j) for j,(a,_) in enumerate(brackets)]
    modules += [tag(label,b-1,True,j) for j,(_,b) in enumerate(brackets)]
    name = f'Dommaschk{label}MirrorCrossings'
    out = header(name,[SIGNS+'.'+s for s in modules])
    out += 'open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing Set\n'
    audit = []
    for j,(a,b) in enumerate(brackets):
        left,right = modules[j],modules[j+2]
        for direction,tr in zip(('back','fwd'),traces,strict=True):
            s = tr['direction']
            short = f'{direction}_'+('upper' if j else 'lower')+'_hit'
            audit.append(short)
            rows = []
            for i in range(a,b):
                if i == a:
                    rows.append(left+'.'+direction+'Row')
                elif i == b-1:
                    rows.append(right+'.'+direction+'Row')
                else:
                    row = f'{direction}Row{i}'
                    out += f'def {row} : Step := {step(tr["steps"][i])}\n'
                    rows.append(row)
            t = lambda i: f'({i}/64:ℝ)'
            out += f'\ntheorem {short} {{y : ℝ → Plane}}\n'
            out += f'    (hy : ContinuousOn y (Icc {t(a)} {t(b)}))\n'
            for i,row in enumerate(rows,a):
                out += f'    {{prev{i} : State}} (h{i} : ∀ t ∈ Icc {t(i)} {t(i+1)},\n'
                out += f'      y t ∈ (physicalSlab prev{i} {row} {t(i)}).tube t)\n'
            h = f'DommaschkFirstMirrorLaunchSign.height {str(bool(j)).lower()}'
            out += f'    : ∃ t ∈ Ioo {t(a)} {t(b)}, strength (({s}:ℝ)*t) (y t) = {h} := by\n'
            out += '  apply intermediate_value_Ioo (by norm_num : '+t(a)+' ≤ '+t(b)+')\n'
            out += f'  · apply continuousOn_strength hy ({s}:ℝ)\n    intro t ht\n'
            out += '    rcases ht with ⟨ha,hb⟩\n'
            for i,row in enumerate(rows,a):
                first = '    '
                if i+1 < b:
                    out += f'    by_cases e{i} : t ≤ {t(i+1)}\n'
                    first += '· '
                out += first+f'have h : t ∈ Icc {t(i)} {t(i+1)} := ⟨by linarith,by linarith⟩\n'
                pad = '      ' if i+1<b else '    '
                out += pad+f'have hr := DommaschkMirrorBracketSlab.positive_radius (a := {t(i)})\n'
                out += pad+f'  (r := {row}) (by simpa only [show {t(i)} + 1/64 = {t(i+1)} by norm_num] using h)\n'
                out += pad+f'  (h{i} t h) (by kernel_fact) (by kernel_fact)\n'+pad+'exact hr\n'
            out += '  · constructor\n'
            for i,side,mod,op in [(a,a,left,'<'),(b-1,b,right,'>')]:
                out += f'    · have ins := h{i} {t(side)} ⟨by norm_num,by norm_num⟩\n'
                out += f'      simpa [DommaschkMirrorEndpointSign.oriented] using {mod}.{direction}_tube_sign ins\n'
    return name,out+f'\nend PlasmaLean.Design.{name}\n',audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--launch',type=int,default=478)
    parser.add_argument('--workers',type=int,default=1)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/secondary-mirror-signs')
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    label,record,traces,brackets = load(args.launch)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    keys = [digest(record),digest(ARCHIVE),lake('lean','--version')]
    cache = args.cache.resolve()
    tasks = [(0,False,0)]
    for j,(a,b) in enumerate(brackets):
        tasks.extend([(a,False,j),(b-1,True,j)])
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        groups = list(pool.map(lambda t: snapshot(t,label=label,traces=traces,keys=keys,cache=cache,args=args),tasks))
    dependencies = [p for group in groups for p in group]
    name,source,audit = crossings(label,traces,brackets)
    overlay = union(cache,dependencies)
    root,r = compile_modules(cache/name,[(name,source,audit)],[overlay],
                             [keys,[m['key'] for _,m in dependencies]],args,HITS)
    print(f'{name}: {r["key"]}',flush=True)
    if args.output:
        save(args.output,{'endpoint':label,'heights':[str(h) for h in HEIGHTS],
            'brackets_in_64ths':brackets,'snapshots':[g[-1][1]['key'] for g in groups],
            'module':name,'key':r['key'],'theorems':r['theorems'],'axioms':r['axioms'],
            'import_paths':[str(root),str(overlay)],'record_sha256':keys[0]})


if __name__ == '__main__':
    main()
