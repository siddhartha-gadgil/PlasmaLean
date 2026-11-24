"""Prove a lower polynomial for the true action density on each existing outer radial tube group."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path

import numpy as np

from bounce_mirror_pilot import HEIGHTS,Model,SCALE
from emit_sparse_taylor_slab import model_literal
from grouped_profile_arithmetic import ROWS,SIDES,physical_values,preamble,reference_arithmetic
from verify_backward_physical_prefix import compile_modules
from verify_centered_strength import Arithmetic,footer
from verify_coarse_action_models import env
from verify_grouped_profile_suffix import group_data
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_secondary_mirror_caps import load
from verify_secondary_mirror_slopes import JET


PACKAGE='GroupedActionFloorCache'
H=HEIGHTS[1]


@lru_cache(maxsize=1)
def saved_proposals():
    path=Path(__file__).parent/'results/q0r478_action_polynomials.json'
    table=json.loads(path.read_text())
    if (table['endpoint'],table['denominator'],F(table['height']))!=('q0r478',SCALE,H):
        raise ValueError('wrong field, coefficient denominator or action height')
    return {(kind,r['start'],r['stop']):r['coefficients'] for kind in ('grouped','native') for r in table[kind]}


@lru_cache(maxsize=1)
def records():
    return [load(470),load(478)]


def proposal(left,den):
    def at(m,x):
        return np.polynomial.polynomial.polyval(x,[c/SCALE for c in m.a])
    x=np.cos(np.arange(8)*np.pi/7)
    y=np.sqrt(np.maximum(at(left,x),0)/at(den,x))
    fit=np.polynomial.polynomial.polyfit(x,y,7)
    p=Model([round(c*SCALE) for c in fit])
    def margin(offset):
        shifted=p-Model([offset])
        return (left-(shifted*shifted)*den).bound()[0]
    lo,hi=0,SCALE//200
    if margin(hi)<0:
        raise ValueError('failed to enclose the proposed action polynomial')
    while hi-lo>2**30:
        m=(lo+hi)//2
        if margin(m)>=0:
            hi=m
        else:
            lo=m
    return p-Model([hi])


def group_source(rec, fixed=None):
    start,stop=rec['start'],rec['stop']
    parent=rec['module']
    stem=parent.removesuffix('Rows')
    if stem==parent:
        raise ValueError('expected checked outer tube rows')
    side=stem+'Outer'
    jet=stem+'OuterTube'
    name=f'DommaschkQ0R478ActionLower{start:03}To{stop:03}'
    (_,tube),_=group_data(start,stop,records())
    reference=reference_arithmetic(tube).values
    power,num=reference['power'],reference['num']
    raw=physical_values(tube)
    err=F(rec['errors'][1])
    a=Arithmetic()
    ref=f'({side}.referenceR s)^16'
    field=f'physicalSq t ({side}.referenceR s) ({side}.referenceZ s)'
    a.leaf('P',power,'('+ref+')','hp')
    a.leaf('Nref',num,'('+ref+'*'+field+')','hn')
    a.leaf('r',raw['r'],'(x 0)','hr')
    for k,target,m in zip(('D','NR','NZ'),('dD','dnR','dnZ'),raw['values'],strict=True):
        a.leaf(k,m,f'(atPoint {target} (x 0) t (x 1))','in'+k)
    a.literal('adjust',H*H-err)
    a.literal('double',2*H)
    a.literal('inverse',1/(2*H))
    a.literal('two',F(2))
    g=a.op('G',a.op('scaledP','P','*','adjust'),'-','Nref')
    rd=a.op('rD','r','*','D')
    u=a.op('U',a.op('subtotal',a.op('rdSq',rd,'*',rd),'+',a.op('nrSq','NR','*','NR')),'+',a.op('nzSq','NZ','*','NZ'))
    left=a.op('L',a.op('UG',u,'*',g),'*','two')
    den=a.op('Q',a.op('dSq','D','*','D'),'*',
             a.op('divisor',a.op('hpower','double','*','P'),'-',a.op('scaledG',g,'*','inverse')))
    p=proposal(a.values[left],a.values[den]) if fixed is None else Model(fixed)
    a.leaf('p',p,'(QPoly.eval proposed.poly s)','inPoly')
    gap=a.op('margin',left,'-',a.op('product',a.op('pSq','p','*','p'),'*',den))
    lower,_=a.interval(gap)
    if lower<0:
        raise ValueError(f'negative exact model margin on {start}..{stop}')
    a.interval('D')
    a.interval('r')
    src=preamble(name,[SIDES+'.'+side,JET+'.'+jet,ROWS+'.'+parent,
                       'PlasmaLean.Certificates.PolynomialActionFloor'])
    src+=f'''open DommaschkJacobianReflection DommaschkMirrorEndpointSign
def proposed : Model := {model_literal(p)}
abbrev height : ℝ := {H}
def groupClock (t : ℝ) := (128*t-{start+stop})/{stop-start}
'''
    src+='\n'.join(a.defs)
    src+=f'''
theorem physical {{s t : ℝ}} {{x : Plane}} (hs : |s| ≤ 1) (m : InputsAt {side}.group s t x) :
    0 < x 0 ∧ QPoly.eval proposed.poly s ≤ weight t x * Real.sqrt (2*(height-strength t x)) := by
  obtain ⟨pos,hp,hn⟩ := {side}.reference_values hs m.2.2.1 m.2.2.2
  have err := {side}.error_on hs m
  have coords := {side}.field_inputs m
  have hr := m.1
  have inPoly : proposed.Mem s (QPoly.eval proposed.poly s) := by
    rw [Model.Mem,show proposed.radius = 0 by with_unfolding_all rfl]
    simp
'''
    for k,symbol in [('D','dD'),('NR','dnR'),('NZ','dnZ')]:
        src+=f'  have in{k} := {jet}.{symbol}_checked.mem hs coords\n'
        src+=f'  change {jet}.{symbol}0.Mem s (atPoint {symbol} (x 0) t (x 1)) at in{k}\n'
    src+='\n'.join(a.body)
    src+=f'''
  have rp : 0 < x 0 := by linarith only [boundr.1]
  have dp : 0 < atPoint dD (x 0) t (x 1) := by linarith only [boundD.1]
  obtain ⟨wp,hw⟩ := DommaschkPairedArcRatio.physical_identity rp dp
  refine ⟨rp,Certificates.PolynomialActionFloor.point (P := ({side}.referenceR s)^16)
    (G := valG) (U := valU) (h := height) (by norm_num [height])
    (norm_nonneg _) (pow_pos pos _) dp wp ?_ ?_ ?_⟩
  · have e := (abs_le.mp err).2
    change (strength t x)^2 - {field} ≤ ({side}.error:ℝ) at e
    dsimp only [valG,valGNeg,valscaledP]
    have num : (({H*H-err}:ℚ):ℝ) = height^2-({side}.error:ℝ) := by norm_num [height,{side}.error]
    rw [num]
    nlinarith only [mul_le_mul_of_nonneg_left e (pow_nonneg pos.le 16)]
  · dsimp only [valU,valsubtotal,valrdSq,valrD,valnrSq,valnzSq]
    linarith only [hw]
  · have bound : 0 ≤ valmargin := by linarith only [boundmargin.1]
    dsimp only [valmargin,valmarginNeg,valproduct,valpSq,valQ,valdivisor,valdivisorNeg,
      valhpower,valscaledG,valdSq,valL,valUG] at bound
    convert bound using 1
    norm_num only [height,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
    ring
'''
    rows=[]
    for i in range(start,stop):
        for sign,back in [('fwd','false'),('back','true')]:
            row=f'{parent}.{sign}Outer{i:03}'
            field_time='t' if sign=='fwd' else '(-t)'
            offset,factor=F(2*i+1-start-stop,stop-start),F(1,stop-start)
            tag=f'{sign}{i:03}'
            rows.append(tag)
            src+=f'''
theorem {tag} {{prev : PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {row} ({i}/64)).tube t) :
    QPoly.eval proposed.poly (groupClock t) ≤ weight {field_time} x * Real.sqrt (2*(height-strength {field_time} x)) := by
  have incl : Covers (i := {i}) (DommaschkHarmonicBlock{i//8:02}.packet {i%8}) {back}
      {row} ({offset}) ({factor}) {side}.group := by constructor <;> kernel_fact
  obtain ⟨hs,m⟩ := row_inputs incl (by convert ht using 1; norm_num) hx
  obtain ⟨pos,bound⟩ := physical hs m
  have clock : (({offset}:ℚ):ℝ) + (({factor}:ℚ):ℝ)*coord ((({i}:ℕ):ℝ)/64) t = groupClock t := by
    norm_num [coord,groupClock]; ring
  rw [clock] at bound
'''
            if sign=='fwd':
                src+='  exact bound\n'
            else:
                src+='''  change 0 < (flip x) 0 at pos
  rw [flip_zero] at pos
  have w : weight (-t) x = weight t (flip x) := by
    simpa only [weight,neg_neg,flip_zero,flip_one] using arcDensity_reflected pos t (-(x 1))
  rw [w,DommaschkNativeActionReflection.norm pos t]
  exact bound
'''
    integral,total=integral_source(start,stop,p)
    src+=integral
    return (name,src+footer(name),['physical',*rows,'integral']),p.a,lower,total


def integral_source(start,stop,p):
    anti=[F(0),*[F(c,(j+1)*SCALE) for j,c in enumerate(p.a)]]
    src=f'''
def primitive : List ℚ := [{', '.join(map(str,anti))}]
theorem integral :
    (∫ t in ({start}:ℝ)/64..({stop}:ℝ)/64, QPoly.eval proposed.poly (groupClock t)) =
      {F(stop-start,128)*sum(F(2*c,(j+1)*SCALE) for j,c in enumerate(p.a) if j%2==0)} := by
  have der (s : ℝ) : QPoly.eval (QPoly.deriv primitive) s = QPoly.eval proposed.poly s := by
    norm_num [primitive,proposed,ofDyadic,QPoly.deriv,QPoly.add,QPoly.eval]; ring
  have result := PolynomialActionFloor.integral_group (a := ({start}:ℝ)/64) (b := ({stop}:ℝ)/64)
    (by norm_num) proposed.poly primitive der
  have clock (t : ℝ) : groupClock t = (2*t-(({start}:ℝ)/64+({stop}:ℝ)/64))/(({stop}:ℝ)/64-({start}:ℝ)/64) := by
    unfold groupClock; ring
  simp_rw [clock]
  rw [result]
  norm_num [primitive,QPoly.eval]
'''
    total=F(stop-start,64)*sum(F(2*c,(j+1)*SCALE) for j,c in enumerate(p.a) if j%2==0)
    return src,total


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--map',required=True,type=Path)
    p.add_argument('--spans',nargs='*',type=int)
    p.add_argument('--propose',action='store_true',help='fit a new proposal instead of checking the saved exact coefficients')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-action-polynomials')
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    env(a)
    src=json.loads(a.map.read_text())
    groups=[r for path in src['receipts'] if (r:=json.loads(Path(path).read_text()))['module'].startswith('DommaschkGroupedProfile')]
    if a.spans is not None:
        groups=[r for r in groups if r['start'] in a.spans]
        if len(groups)!=len(set(a.spans)):
            p.error('choose starts of available authenticated tube groups')
    result={}
    (a.cache/'rows').mkdir(parents=True,exist_ok=True)
    for r in groups:
        roots=list(map(Path,r['import_paths']))
        admitted(roots[0],r['module'],r['key'])
        fixed=None if a.propose else saved_proposals()['grouped',r['start'],r['stop']]
        decl,coeff,margin,mass=group_source(r,fixed)
        keys=[a.version,r['key'],digest(DESIGN.parent/'Certificates/PolynomialActionFloor.trace')]
        base,rec=compile_modules(a.cache/decl[0],[decl],roots,keys,a,PACKAGE)
        out={k:rec[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
        out.update(start=r['start'],stop=r['stop'],coefficients=coeff,group=r['key'],packets=r['packets'],
                   signed_mass=str(mass),margin=str(margin),import_paths=list(map(str,[base,*roots])))
        save(a.cache/'rows'/f"{r['start']:03}.json",out)
        result[r['start']]=out
        save(a.output,result)
        print(decl[0],rec['key'],flush=True)


if __name__=='__main__':
    main()
