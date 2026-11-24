"""Check both endpoint signs of the physical mirror brackets at the four opposite-section launches."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS, SCALE
from bounce_phase_strength import ShiftedStrength
from replay_physical_action_archive import segment
from screen_action_panel_resolution import endpoint_inputs
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env, section_data, verify as physical_model
from verify_mirror_endpoint_signs import header
import verify_native_action_models as native
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import ARCHIVE
from verify_signed_mirror_passage import merge_import_roots


LABELS = ('q1r456','q1r464','q1r509','q1r517')
CAPS = 'OppositeMirrorCapCache'
HITS = 'OppositeMirrorCrossingCache'


def bracket_nodes(label):
    data = json.loads(ARCHIVE.read_text())
    section, = (s for s in data['sections'] if s['section_in_half_pi'] == 1)
    radius = Fraction(int(label[3:]),1000)
    endpoint, = (r for r in section['endpoints'] if Fraction(r['launch_radius']) == radius)
    if list(map(Fraction,endpoint['heights'])) != list(HEIGHTS):
        raise ValueError(f'unexpected heights at {label}')
    _,_,_,_,traces,packet,_ = endpoint_inputs(label)
    for trace,crossings in zip(traces,endpoint['crossings'],strict=True):
        sign = trace['direction']
        if not crossings['success'] or len(crossings['brackets']) != 2:
            raise ValueError(f'missing brackets for {label} signed clock {sign}')
        for j,(left,right) in enumerate(crossings['brackets']):
            a,b = 64*Fraction(left),64*Fraction(right)
            if a.denominator != 1 or b.denominator != 1 or not 0 < a < b <= len(trace['steps']):
                raise ValueError(f'invalid original grid at {label}')
            yield trace,packet,sign,j,int(a),int(b)


def cap_module(label,sign,j,node,right):
    return ('DommaschkOppositeCap'+label.upper()+('Fwd' if sign==1 else 'Back')+
            ('Upper' if j else 'Lower')+('Right' if right else 'Left')+f'{node:03}')


def cap_source(label,sign,j,node,right,model):
    i = node-int(right)
    s = 1 if right else -1
    clock = f'({node}/64)' if sign==1 else f'(-({node}/64))'
    name = cap_module(label,sign,j,node,right)
    src = header(name,['PlasmaLean.Certificates.MirrorGapAtTime',native.OUTPUT_PACKAGE+'.'+model])
    height = '(DommaschkFirstMirrorLaunchSign.height '+str(bool(j)).lower()+')'
    strength = f'DommaschkMirrorTubeCrossing.strength (Real.pi/2 + {clock}) x'
    comparison = height+' < '+strength if right else strength+' < '+height
    evaluated = f'Certificates.QPoly.evalQ {model}.num.poly ({s})'
    test = f'{evaluated} + {model}.num.radius < 0' if right else f'{model}.num.radius < {evaluated}'
    src+=f'''open Certificates.PositionFrameSlabs Certificates.TrajectoryTaylorModel
abbrev row := {model}.row
theorem on_tube {{prev : State}} {{x : Plane}}
    (hx : x ∈ (physicalSlab prev row ({i}/64)).tube ({node}/64)) : {comparison} := by
  have bound := {model}.physical (t := {node}/64) (prev := prev) (x := x) (by norm_num) hx
  have hr := bound.1
  have m := bound.2.2.2.2.2
  rw [show 128*({node}/64:ℝ)-{2*i+1} = (({s}:ℚ):ℝ) by norm_num] at m
  exact strength_at (above := {str(right).lower()}) (s := {s}) m
    (by change {test}; kernel_fact) (by positivity) (norm_nonneg _)
    (by norm_num [DommaschkFirstMirrorLaunchSign.height])
end PlasmaLean.Design.{name}
'''
    return name,src,['on_tube']


def crossings_source(label,ranges):
    name = 'DommaschkOppositeMirrorCrossings'+label.upper()
    modules = [cap_module(label,sign,j,node,right) for sign,j,a,b in ranges for right,node in ((False,a),(True,b))]
    src = header(name,[CAPS+'.'+m for m in modules])
    src += 'open Set Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign\n'
    proofs = []
    for sign,j,a,b in ranges:
        low,high = [cap_module(label,sign,j,node,r) for r,node in ((False,a),(True,b))]
        clock = 't' if sign==1 else '(-t)'
        level = '(height '+str(bool(j)).lower()+')'
        fn = f'(fun t => strength (Real.pi/2 + {clock}) (y t))'
        thm = ('fwd' if sign==1 else 'back')+('_upper_hit' if j else '_lower_hit')
        src+=f'''theorem {thm} {{y : ℝ → Plane}} {{pl pr : State}}
    (continuous : ContinuousOn {fn} (Icc ({a}/64) ({b}/64)))
    (left : y ({a}/64) ∈ (physicalSlab pl {low}.row ({a}/64)).tube ({a}/64))
    (right : y ({b}/64) ∈ (physicalSlab pr {high}.row ({b-1}/64)).tube ({b}/64)) :
    ∃ t ∈ Ioo ({a}/64:ℝ) ({b}/64), strength (Real.pi/2 + {clock}) (y t) = {level} :=
  intermediate_value_Ioo (by norm_num : ({a}/64:ℝ) ≤ {b}/64) continuous
    ⟨{low}.on_tube left,{high}.on_tube right⟩
'''
        proofs.append(thm)
    return name,src+f'end PlasmaLean.Design.{name}\n',proofs


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--endpoint',choices=LABELS,required=True)
    p.add_argument('--screen-only',action='store_true')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-mirror-caps')
    p.add_argument('--model-cache',type=Path,default=ROOT/'.lake/coarse-action-models')
    p.add_argument('--native-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output',type=Path,required=True)
    a = p.parse_args()
    label = a.endpoint
    data = section_polynomial_data(1)
    strength = ShiftedStrength(data)
    nodes = []
    ranges = []
    for trace,packet,sign,j,lo,hi in bracket_nodes(label):
        ranges.append((sign,j,lo,hi))
        for right,node in [(False,lo),(True,hi)]:
            i = node-int(right)
            tube,angles,fields = segment(trace,i).fields(data)
            gap, = strength.numerators(tube,angles,fields,[HEIGHTS[j]])
            value = Fraction(gap.endpoint(1 if right else -1),SCALE)
            uncertainty = Fraction(gap.e,SCALE)
            margin = (value if right else -value) - uncertainty
            if margin <= 0:
                raise ValueError(f'{label} {sign} node {node}: directed compensated gap {margin}')
            nodes.append((sign,j,i,node,right,margin))
    out = {'endpoint':label,'packet_sha256':packet,'ranges':ranges,
           'minimum_compensated_margin':str(min(x[-1] for x in nodes)),'kernel_checked':False}
    if not a.screen_only:
        env(a)
        cap_cache = a.cache
        a.cache = a.model_cache
        fields,static = section_data(a,1)
        parents = []
        for sign,j,i,node,right,margin in nodes:
            model,columns = physical_model(a,label,i,sign,fields,static,mirror_height=HEIGHTS[j])
            num = columns[-1]
            gap = -num.endpoint(1 if right else -1)
            if margin != Fraction((gap if right else -gap)-num.e,SCALE):
                raise ValueError('cap screen and physical Taylor coefficients disagree')
            item = cap_source(label,sign,j,node,right,model['module'])
            roots = list(map(Path,model['import_paths']))
            base,rec = compile_modules(cap_cache/item[0],[item],roots,
                [a.version,packet,model['key'],digest(DESIGN.parent/'Certificates/MirrorGapAtTime.trace')],a,CAPS)
            parents.append((rec,[base,*roots]))
            print(item[0],rec['key'],flush=True)
        keys = [a.version,packet,*[rec['key'] for rec,_ in parents]]
        overlay = merge_import_roots(cap_cache/'all',[r for _,rs in parents for r in rs],keys)
        item = crossings_source(label,ranges)
        base,rec = compile_modules(cap_cache/item[0],[item],[overlay],keys,a,HITS)
        out.update({k:rec[k] for k in ('module','key','theorems','axioms')},kernel_checked=True,
                   cap_keys=keys[2:],import_paths=list(map(str,[base,overlay])))
    save(a.output,out)
    print(out.get('key',out['minimum_compensated_margin']))


if __name__ == '__main__':
    main()
