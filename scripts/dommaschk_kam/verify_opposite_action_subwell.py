"""Check the 320-pair positive-action packet at the original opposite-section inner radius."""
import argparse
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from bounce_common_section import section_polynomial_data
from bounce_mirror_pilot import HEIGHTS
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row, write_table
from replay_physical_action_archive import segment
from screen_opposite_action_prefix import PANELS, TARGET
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save

PACKAGE='OppositeActionSubwellCache'
NAME='DommaschkOppositeInnerActionCore320'
CUT=320


def load(path):
    packet=json.loads(gzip.decompress(path.read_bytes()))
    if ((packet['section_in_half_pi'],F(packet['launch_u']),F(packet['birth_phase_half_width']),
            F(packet['step']),packet['panels_per_step'])!=(1,F(47,100),F(1,2**19),F(1,64),24)
        or [t['direction'] for t in packet['traces']]!=[-1,1]
        or any([r['index'] for r in t['steps']]!=list(range(330)) for t in packet['traces'])):
        raise ValueError('wrong singleton birth, signed ODE row sequence, height clock or panels')
    return packet


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/opposite-action-subwell')
    a=p.parse_args()
    env(a)
    packet=load(a.packet)
    exact=section_polynomial_data(1)
    field=ShiftedStrength(exact)
    groups=[]
    for trace in packet['traces']:
        rows=[panel_row(segment(trace,i),exact,field,HEIGHTS[1],False,PANELS) for i in range(CUT)]
        groups.append(rows if trace['direction']==1 else list(reversed(rows)))
    total=sum(mass for g in groups for _,mass in g)
    previous=total-groups[0][0][1]-groups[1][-1][1]
    scale=3072*2**40
    if not F(previous,scale)<TARGET<F(total,scale):
        raise ValueError('the rounded lower panel table does not first cross the target at row 320')
    with TemporaryDirectory() as scratch:
        p=Path(scratch)
        write_table(groups,HEIGHTS[1],False,NAME,'the opposite-section singleton central subwell',p,PANELS)
        src=(p/(NAME+'.lean')).read_text()
    src=src.replace('public import PlasmaLean.Certificates.MirrorActionQuadrature',
                    'public import PlasmaLean.Certificates.PositiveSubwell\npublic import PlasmaLean.Design.DommaschkNativeWellAction')
    body,_=src.rsplit('end PlasmaLean.Design.'+NAME,1)
    src=body+'''
open Certificates.PositiveSubwell Kinetic.MirrorHeightAction Kinetic.MirrorActionEnvelope
open DommaschkNativeWellAction
'''
    positives=[]
    for i in range((2*CUT+15)//16):
        local=f'positive{i}'
        src+=f'private theorem {local} : slabGroup{i}.all (fun b => positive 48 b.packed) = true := by kernel_fact\n'
        positives.append(local)
    src+='theorem positive_all : slabs.all (fun b => positive 48 b.packed) = true := by\n'
    src+='  simp only [slabs,List.all_append,'+','.join(positives)+',Bool.and_self]\n'
    src+=f'''
noncomputable abbrev coreMass : ℝ := {total} / (3072*1099511627776)

/-- Every true first well around any original birth in the signed core exceeds the prescribed
action as soon as its physical cells are established, without an independent mirror-bracket input. -/
theorem excludes {{f w : ℝ → ℝ}} {{φ l r : ℝ}} (birth : φ ∈ Set.Icc (-5) 5)
    (well : LaunchWell f φ level l r) (cells : Covers false w f level (-5) slabs)
    (cw : ContinuousOn w (Set.Icc l r)) (cf : ContinuousOn f (Set.Icc l r))
    (nn : ∀ t ∈ Set.Icc l r, 0 ≤ w t) :
    l ≤ -5 ∧ 5 ≤ r ∧ target < coreMass ∧ coreMass ≤ action f w l r level := by
  have len : slabs.length = 320+320 := checked.len
  have core := floor_in_first_well len positive_all
    (show Covers false w f level (-(320:ℝ)/64) slabs by convert cells using 1; norm_num)
    (show φ ∈ Set.Icc (-(320:ℝ)/64) ((320:ℝ)/64) by norm_num; exact birth) well nn cf cw
  have sum : total slabs = {total} := by kernel_fact
  rw [sum] at core
  norm_num only [Nat.cast_ofNat, show (-(320:ℝ)/64) = -5 by norm_num,
    show (320:ℝ)/64 = 5 by norm_num] at core
  refine ⟨core.1,core.2.1,by norm_num [target,coreMass],?_⟩
  norm_num [coreMass,level] at core ⊢
  exact core.2.2
end PlasmaLean.Design.{NAME}
'''
    root,rec=compile_modules(a.cache/NAME,[(NAME,src,['excludes'])],[],
                           [a.version,digest(a.packet),digest(DESIGN.parent/'Certificates/PositiveSubwell.trace'),
                            digest(DESIGN/'DommaschkNativeWellAction.trace')],a,PACKAGE)
    result={k:rec[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
    result.update(package=PACKAGE,splits=PANELS,upper=False,counts=[CUT,CUT],target=str(TARGET),
                  height=str(HEIGHTS[1]),mass=str(F(total,scale)),previous=str(F(previous,scale)),
                  panels=2*CUT*PANELS,packet_sha256=digest(a.packet),import_paths=[str(root)])
    save(a.output,result)
    print(NAME,rec['key'],result['mass'],flush=True)


if __name__=='__main__':
    main()
