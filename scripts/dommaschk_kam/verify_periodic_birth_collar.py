"""Certify two-sided QA2R field-line collars from every original toroidal launch angle."""
import argparse
from fractions import Fraction as F
from math import ceil
from pathlib import Path
from types import SimpleNamespace

from bounce_launch_box import profile_coefficients
from bounce_mirror_pilot import HEIGHTS, Model, R0M, SCALE, ZERO, horner
from emit_sparse_taylor_slab import model_literal
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_grouped_mirror_exclusion import GAPS
from verify_harmonic_group_exclusion import harmonics, negative_gap, radius_cap
from verify_mirror_endpoint_signs import header
from verify_native_action_models import FIELDS, static_data, verify_static
from verify_periodic_birth_strength import SPANS, physical_inputs, verify_field
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


DURATION = F(1,256)
SPEED = F(1,6)
CLEARANCE = F(1,1000)
PHASE = 'PeriodicCollarPhaseCache'


def phase_source(name,a,b,tube,angles,anchors,coefficients,values):
    top = name+'Physical'
    src = header(top, [GAPS+'.'+name, 'PlasmaLean.Design.DommaschkPeriodicBirthCollar',
        'PlasmaLean.Design.DommaschkGroupGapRadius','PlasmaLean.Design.DommaschkPairedActionProfiles'])
    src += '''open Certificates.TrajectoryHarmonicPacket DommaschkPeriodicBirthCollar
open DommaschkPeriodicBirthFourier DommaschkPreMirrorSigns DommaschkFirstMirrorLaunchSign
open DommaschkMirrorEndpointSign DommaschkBounceField DommaschkMirrorLaunch
'''
    inp = name+'Inputs'
    rc = radius_cap(tube[0])
    src += f'''private theorem observed {{w R z ψ : ℝ}} (hw : |w| ≤ 1)
    (hr : {inp}.group.radial.Mem w R) (hz : {inp}.group.height.Mem w z)
    (hc : {inp}.group.cosine.Mem w (Real.cos (2*ψ))) (hs : {inp}.group.sine.Mem w (Real.sin (2*ψ))) :
    Bounds R z ψ := by
  have hu := shifted_mem (u := {inp}.displacement) hr (eq_of_beq (by kernel_fact)) (by kernel_fact)
  have waves := {inp}.angles hw hc hs
  have rbox := DommaschkPairedActionProfiles.range (lo := 3/4) (hi := ({rc})) hw hr (by kernel_fact)
  norm_num at rbox
'''
    for j,symbol in enumerate(('dD','dnR','dnZ')):
        lo,hi=values[j].bound()
        src += f'''  have m{j} := {name+FIELDS[j]}.sound hw hu hz waves
  have b{j} := DommaschkPairedActionProfiles.range (lo := ({lo})) (hi := ({hi})) hw m{j} (by kernel_fact)
  change (({lo} : ℚ) : ℝ) ≤ atPoint {symbol} R ψ z ∧ atPoint {symbol} R ψ z ≤ (({hi} : ℚ) : ℝ) at b{j}
  norm_num at b{j}
'''
    src += f'''  have hR : 1/2 < R := by linarith only [rbox.1]
  have hp : 0 < R := by linarith
  have hd : 0 < atPoint dD R ψ z := by linarith only [b0.1]
  refine ⟨hR,hd,?_,?_,?_⟩
  · rw [abs_div,abs_of_pos hd,div_le_iff₀ hd,abs_le]
    unfold speed
    constructor <;> linarith only [b0.1,b1.1,b1.2]
  · rw [abs_div,abs_of_pos hd,div_le_iff₀ hd,abs_le]
    unfold speed
    constructor <;> linarith only [b0.1,b2.1,b2.2]
  · apply physical_sign false hp (by norm_num [cap,clearance,height])
    apply DommaschkGroupGapRadius.at_lower (radius := ({rc})) hp.le
      (by linarith only [rbox.2]) (by norm_num [height,cap,clearance]) ({name}.gap_upper hw hr hz hc hs)
    norm_num [{name}.upper,height,cap,clearance]
'''
    for j,centre in enumerate(anchors,1):
        (dc,c),(ds,s) = centre
        src += f'''private def pair{j} : Pair ({F((a+b)*j,64)}) ({F((b-a)*j,64)}) :=
  ⟨⟨{c}, {dc}, by kernel_fact⟩, ⟨{s}, {ds}, by kernel_fact⟩,
   {model_literal(angles[2*j])}, {model_literal(angles[2*j-1])}, by kernel_fact, by kernel_fact⟩
'''
    src += f'''theorem resolved : Sector ({a}/64) ({b}/64) := by
  intro t ht R z ψ hR hz hcos hsin
  let s : ℝ := (128*t-{a+b})/{b-a}
  have hs : |s| ≤ 1 := by dsimp [s]; rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
'''
    for j in range(1,4):
        mid,width=F((a+b)*j,64),F((b-a)*j,64)
        src += f'''  have h{j} (v : Bool) : (pair{j}.model v).Mem s (wave v ({2*j}*t)) := by
    have h := pair{j}.sound v hs
    have clock : (({mid} : ℚ) : ℝ) + (({width} : ℚ) : ℝ)*s = {2*j}*t := by
      dsimp [s]; norm_num; ring
    rw [clock] at h
    cases v <;> exact h
'''
    for qchar,sine,err,hyp,target,variable in [('r','false',F(1,1200),'hR','radial','R'),
                                                ('z','true',F(1,3800),'hz','height','z')]:
        qs=coefficients[int(sine=='true')]
        for j,q in enumerate(qs):
            src+=f'  have {qchar}{j} : coeff {sine} {j} = ({q} : ℚ) := by kernel_fact\n'
        src+='  rw [low_eq,'+','.join(qchar+str(j) for j in range(4))+f'] at {hyp}\n'
        src+=f'  have {qchar}mem : {inp}.group.{target}.Mem s {variable} := by\n'
        src+='    apply DommaschkPeriodicBirthCover.linear_mem '+ ' '.join(f'(q{j} := ({q}))' for j,q in enumerate(qs))
        src+=f' (e := ({err+DURATION*SPEED})) hs (h1 {sine}) (h2 {sine}) (h3 {sine})\n'
        src+=f'''    · convert {hyp} using 1
      norm_num [error,duration,speed]
    · kernel_fact
'''
    src+=f'''  apply observed hs rmem zmem
  · exact perturbed (e := 1/128) (h1 false) (by norm_num [duration] at hcos ⊢; exact hcos)
      (by rfl) (by kernel_fact)
  · exact perturbed (e := 1/128) (h1 true) (by norm_num [duration] at hsin ⊢; exact hsin)
      (by rfl) (by kernel_fact)
end PlasmaLean.Design.{top}
'''
    return top,src,['resolved']


def final(groups,packages,args):
    name='DommaschkPeriodicOriginalCollar'
    imports=[PHASE+'.'+row['physical_module'] for row in groups]
    src=header(name,[*imports,'PlasmaLean.Design.DommaschkPeriodicCollarCartesian'])
    src+='open DommaschkPeriodicBirthCollar DommaschkMirrorLaunch DommaschkKamC KamNewton Theory.KAM WEll1Z2 Set\n'
    chain=groups[-1]['physical_module']+'.resolved'
    for row in reversed(groups[:-1]):
        chain=f'sector_join {row["physical_module"]}.resolved ({chain})'
    src+=f'''theorem full_period : Sector 0 (202/64) := by
  have h : Sector (0/64) (202/64) := {chain}
  simpa only [zero_div] using h
theorem original_collar : CommonCollar := from_period full_period
theorem cartesian_field_line {{uC zC uA zA : FA}}
    (hc : Close (9 / 1400) DommaschkKamDio.dkIotaC uC zC u₀C z₀C (1 / 10 ^ 12))
    (ha : Close (9 / 1400) DommaschkKamDio.dkIotaA uA zA
      DommaschkKamA.u₀A DommaschkKamA.z₀A (1 / 10 ^ 12))
    {{u : ℝ}} (hu : u ∈ Icc (11 / 25 : ℝ) (27 / 50)) (φ : ℝ) :
    CartesianPassage (birth uC zC uA zA u φ) φ := (at_original full_period hc ha hu φ).cartesian
end PlasmaLean.Design.{name}
'''
    overlay=union(args.cache,packages)
    base,receipt=compile_modules(args.cache/name,[(name,src,['full_period','original_collar','cartesian_field_line'])],
        [overlay],[args.keys,digest(DESIGN/'DommaschkPeriodicCollarCartesian.trace'),
                   [p[1]['key'] for p in packages]],args,'PeriodicCollarFamilyCache')
    save(args.output,{k:receipt[k] for k in ('module','key','theorems','axioms')} |
         {'kind':'original-periodic-collar','groups':groups,'duration':str(DURATION),
          'speed':str(SPEED),'clearance':str(CLEARANCE),'import_paths':[str(base),str(overlay)]})


def columns(tube, channels):
    radial, height, cosine, sine = tube
    waves = harmonics(cosine,sine)
    values = []
    for field in channels:
        value = ZERO
        for w, group in reversed(field):
            rows = [horner([coefficient for _,coefficient in row], radial-R0M) for row in group]
            value = horner(rows,height)*waves[w]+value
        values.append(value)
    return values


def select(a,b,profiles,channels):
    raw, angles, anchors, coefficients = physical_inputs(a,b,profiles)
    tube = [Model(m.a,m.e+ceil(SCALE*DURATION*(SPEED if i<2 else 2))) for i,m in enumerate(raw)]
    values = columns(tube,channels)
    margin = negative_gap(tube[0],values).bound()[1]
    corrected = margin+radius_cap(tube[0])**16*(HEIGHTS[0]**2-(HEIGHTS[0]-CLEARANCE)**2)
    den = values[0].bound()[0]
    numerator = max(max(map(abs,v.bound())) for v in values[1:3])
    if corrected < 0 and den > 0 and numerator <= SPEED*den:
        return [(a,b,tube,angles,anchors,coefficients,values,margin,corrected,den,numerator)]
    mid = (a+b)//2
    if mid in (a,b):
        raise ArithmeticError(f'failed at ticks {a}..{b}, gap {corrected}, denominator {den}, numerator {numerator}')
    return select(a,mid,profiles,channels)+select(mid,b,profiles,channels)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--cache',type=Path,default=ROOT/'.lake/periodic-birth-collar')
    parser.add_argument('--screen',action='store_true')
    parser.add_argument('--fields-only',action='store_true')
    parser.add_argument('--field-spans',nargs=2,type=int,metavar=('START','STOP'),
                        help='precompute only swept field groups contained in this range of angular ticks')
    args=parser.parse_args()
    args.channels=static_data()
    profiles=[profile_coefficients(t) for t in 'CA']
    tasks=[row for a,b in SPANS for row in select(a,b,profiles,args.channels)]
    if args.field_spans:
        start,stop=args.field_spans
        if not args.fields_only or not 0 <= start < stop <= 202:
            parser.error('--field-spans requires --fields-only and ticks 0 ≤ START < STOP ≤ 202')
        tasks=[task for task in tasks if start <= task[0] and task[1] <= stop]
        if not tasks:
            parser.error('no complete field group lies in the selected range')
    if not args.screen:
        env(args)
        args.keys=[args.version,*[digest(DESIGN/(n+'.trace')) for n in
                   ('DommaschkGroupedHarmonicGap','DommaschkCoreClearance','DommaschkDyadicHorner')]]
        args.static=verify_static(SimpleNamespace(**{**vars(args),'cache':ROOT/'.lake/native-action-checks',
                                      'fields':range(4)}),args.channels)
    groups,all_packages=[],[]
    for a,b,tube,angles,anchors,coefficients,values,margin,corrected,den,num in tasks:
        name=f'DommaschkPeriodicCollar{a:03}To{b:03}'
        row={'module':name,'ticks':[a,b],'lowered_gap':str(corrected),'denominator_lower':str(den),
             'max_numerator':str(num),'speed_bound':str(num/den)}
        if not args.screen:
            packages,upper=verify_field(name,tube,args)
            if upper != margin:
                raise ArithmeticError('the exact gap estimate changed during emission')
            row['field_key']=packages[-1][1]['key']
            if not args.fields_only:
                src=phase_source(name,a,b,tube,angles,anchors,coefficients,values)
                deps=[digest(DESIGN/(n+'.trace')) for n in
                      ('DommaschkPeriodicBirthCollar','DommaschkGroupGapRadius','DommaschkPairedActionProfiles')]
                physical=compile_modules(args.cache/src[0],[src],[union(args.cache,packages)],
                    [deps,packages[-1][1]['key']],args,PHASE)
                row.update(physical_module=src[0],physical_key=physical[1]['key'])
                all_packages.extend([*packages,physical])
        groups.append(row)
        print(a,b,float(corrected),float(num/den),flush=True)
        save(args.output,{'kind':'screen' if args.screen else 'fields','duration':str(DURATION),
                          'speed':str(SPEED),'clearance':str(CLEARANCE),'groups':groups})
    if not args.screen and not args.fields_only:
        final(groups,all_packages,args)


if __name__=='__main__':
    main()
