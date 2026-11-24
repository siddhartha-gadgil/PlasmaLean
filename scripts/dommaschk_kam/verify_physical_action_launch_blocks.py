"""Verify both complete Q0R470 birth-adjacent action slabs from shared field bounds."""
import argparse
from collections import defaultdict
from fractions import Fraction as F
import gzip
import json
from math import comb
from pathlib import Path
import re
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model, ZERO
from emit_sparse_taylor_slab import RECORD, ROOT, field, model_literal, models
from screen_physical_action_panels import packed_rows
from screen_sparse_reference_defects import sparse_fields
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import union
from verify_mirror_endpoint_signs import header
from verify_pre_mirror_signs import DESIGN, compile_modules, digest, inputs, jacobian, save


FIELDS='ActionBlockFieldCache'
POWERS='ActionBlockPowersCache'
INPUTS='ActionBlockInputsCache'
CELLS=5


def endpoints(error,i,j):
    lo=-error+2*error*i//CELLS
    hi=-error+2*error*j//CELLS
    return (lo+hi)//2,(hi-lo+1)//2


def compensated_terms(h):
    coeffs=defaultdict(F)
    for q,exponents in sparse_fields()[0]:
        coeffs[exponents]+=q
    for j in range(8):
        coeffs[(j,0,0,0)]-=h*comb(7,j)*F(29,32)**(7-j)
    return [(q,k) for k,q in sorted(coeffs.items()) if q]


def shared_field(a,i,coords,h,terms):
    name=f'DommaschkActionLaunchRegion{i}'
    inp=name+'Inputs'
    src=header(name,['PlasmaLean.Design.DommaschkCompensatedAction'])
    src+='def trial : Inputs := ⟨'+', '.join(map(model_literal,coords))+'⟩\n'
    src+=f'def comp : SP := DommaschkCompensatedAction.shiftedD ({h})\n\nend PlasmaLean.Design.{name}\n'
    result=compile_modules(a.cache/inp,[(inp,src,[])],[],
                           [a.keys,INPUTS,digest(DESIGN/'DommaschkCompensatedAction.trace')],a,INPUTS)
    stored=name+'Stored'
    body=add_shared_powers({inp:src},inp,name,coords)[stored]
    body=body.replace('PlasmaLean.Design.'+inp,INPUTS+'.'+inp)
    table=compile_modules(a.cache/stored,[(stored,body,[])],[result[0]],
                          [POWERS,result[1]['key'],digest(DESIGN/'DommaschkStoredPowers.trace')],a,POWERS)
    leaf=name+'D'
    src=header(name,[POWERS+'.'+stored])+field('comp',coords,terms=terms)+'\nend PlasmaLean.Design.'+name+'\n'
    src=src.replace('apply Blocks.chunk ','apply DommaschkStoredPowers.checkedChunk storedPowers storedPowers_checked ')
    src=re.sub(r'  · exact (comp\d+_checked)',r'  · rw [List.drop_drop]\n    exact \1',src)
    src=src.replace('  · exact Blocks.nil','  · rw [List.drop_drop, List.drop_eq_nil_of_le (by kernel_fact)]\n    exact Blocks.nil')
    src+=f'''\nnamespace PlasmaLean.Design.{leaf}
open DommaschkBounceTaylor
theorem checked : Blocks ⟨7,80⟩ {name}.trial {name}.comp {name}.comp0 := {name}.comp_checked
end PlasmaLean.Design.{leaf}
'''
    one=compile_modules(a.cache/leaf,[(leaf,src,['checked'])],[result[0],table[0]],
                        [FIELDS,table[1]['key']],a,FIELDS)
    return name,[result,table,one]


def data(a):
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    b,f=[t['steps'][0] for t in packet['traces']]
    if (b['coefficients']!=[f['coefficients'][0],[-z for z in f['coefficients'][1]]]
            or packet['section_in_half_pi']!=0 or packet['launch_u']!='47/100'):
        raise ValueError('expected reflected Q0R470 launch')
    rows=packed_rows()
    codes=[(rows[325]>>(72*j))%(1<<72) for j in range(48)]
    if codes!=[(rows[324]>>(72*(47-j)))%(1<<72) for j in range(48)]:
        raise ValueError('the signed action panels have different archived values')
    density=F(min(x%(1<<24) for x in codes),2**20)
    g=F(min((x>>24)%(1<<24) for x in codes),2**26)
    e=max(b['physical_radius_out'],f['physical_radius_out'])
    jac=jacobian(a,0,f,e)
    if not jac or jac[2]!='DommaschkBounceTaylorFirst':
        raise ValueError('the checked original first-slab field models are required')
    return f,e,density,g,jac


def region_gap(a,i,rad,coords,h,terms,jac,leaf,packages):
    name=f'DommaschkActionLaunchGap{i}'
    src=header(name,[FIELDS+'.'+leaf+'D','PlasmaLean.Design.DommaschkBounceTaylorFirst'])
    src+='open DommaschkMirrorEndpointSign DommaschkPhysicalActionPanel DommaschkCompensatedAction\n'
    orig=jac[2]
    ds=[sum(models(t,jac[1]),ZERO) for t in sparse_fields()]
    C=sum(models(terms,coords),ZERO)
    proof=[f'''theorem positive {{w R z c s : ℝ}} (hw : |w| ≤ 1)
    (rad : ({model_literal(rad)}).Mem w R) (normal : {orig}.trial.Mem w (R-dkR0) z c s)
    (localMem : {leaf}.trial.Mem w (R-dkR0) z c s) :
    0 ≤ gap R ((({h}:ℚ):ℝ)) (evR (R-dkR0) z c s dD)
      (evR (R-dkR0) z c s dnR) (evR (R-dkR0) z c s dnZ) := by''']
    table={'r':(rad,'R','rad')}
    for k,p,m in zip(('D','Nr','Nz'),('dD','dnR','dnZ'),ds,strict=True):
        proof.extend([f'  let {k} := evR (R-dkR0) z c s {p}',
                      f'  have in{k} : {orig}.{p}0.Mem w {k} := {orig}.{p}_checked.mem hw normal'])
        table[k]=(m,k,'in'+k)
    proof.extend([f'  let C := evR (R-dkR0) z c s {leaf}.comp',
                  f'  have inC : {leaf}.comp0.Mem w C := {leaf}.comp_checked.mem hw localMem'])
    table['C']=(C,'C','inC')
    for k,q in [('neg',-1),('two',2)]:
        table[k]=(Model.rational(q),f'(({q}:ℚ):ℝ)','in'+k)
        src+=f'private def {k} : Model := {model_literal(table[k][0])}\n'
        proof.append(f'  have in{k} : {k}.Mem w (({q}:ℚ):ℝ) := enclose hw (constant_mem ({q}) w) (by kernel_fact)')
    for k,l,r,op in [('r2','r','r','*'),('tw','two','D','*'),('nc','neg','C','*'),
                      ('plus','tw','nc','+'),('rd','r2','C','*'),('base','rd','plus','*'),
                      ('nn','Nr','Nr','*'),('zz','Nz','Nz','*'),('part','base','nn','+'),
                      ('last','part','zz','+')]:
        m1,x,hx=table[l];m2,y,hy=table[r]
        m=m1*m2 if op=='*' else m1+m2
        val='v'+k
        src+=f'private def {k} : Model := {model_literal(m)}\n'
        proof.append(f'  let {val} := {x} {op} {y}')
        action=f'mem_product_fit hw {hx} {hy}' if op=='*' else f'enclose hw (mem_add {hx} {hy})'
        proof.append(f'  have in{k} : {k}.Mem w {val} := {action} (by kernel_fact)')
        table[k]=(m,val,'in'+k)
    if table['last'][0].bound()[0]<=0:
        raise ValueError(f'insufficient common squared-speed bound on radial interval {i}')
    proof.extend(['  have ht : w ∈ Set.Icc (((-1):ℚ):ℝ) ((1:ℚ):ℝ) := by',
                  '    simpa only [Set.mem_Icc, Rat.cast_neg, Rat.cast_one] using abs_le.mp hw',
                  '  have margin := lower_on (m := last) (a := 0) (by kernel_fact) ht inlast',
                  f'  rw [gap_from_shift ({h}:ℚ) (u := R-dkR0) rfl]',
                  f'  change 0 ≤ R^2*C*(2*D-C)+Nr^2+Nz^2+R^16*(((({h}:ℚ):ℝ))^2-((({h}:ℚ):ℝ))^2)',
                  '  rw [sub_self, mul_zero, add_zero]',
                  '  simpa only [Rat.cast_zero, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat, neg_one_mul, sub_eq_add_neg,',
                  '    pow_two, vlast, vpart, vbase, vrd, vr2, vplus, vtw, vnc, vnn, vzz] using margin'])
    src+='\n'+'\n'.join(proof)+'\n\nend PlasmaLean.Design.'+name+'\n'
    return compile_modules(a.cache/name,[(name,src,['positive'])],[union(a.cache,packages)],
                           [a.keys,packages[-1][1]['key'],digest(DESIGN/'DommaschkBounceTaylorFirst.trace')],
                           a,'ActionBlockGapCache')


def cover_tree(row,e,lo,hi,indent,hyp):
    shift,width=endpoints(e,lo,hi)
    rad,coords=inputs(row,0,width,e,shift)
    output=''
    if lo+1==hi:
        leaf=f'DommaschkActionLaunchRegion{lo}'
        return (indent+f'have shifted := shifted_mem (u := {leaf}.trial.u) {hyp} (eq_of_beq (by kernel_fact)) (by kernel_fact)\n'
                +indent+f'exact DommaschkActionLaunchGap{lo}.positive hw {hyp} normal ⟨shifted,vertical,normal.2.2.1,normal.2.2.2⟩\n')
    mid=(lo+hi)//2
    l,dl=endpoints(e,lo,mid)
    r,dr=endpoints(e,mid,hi)
    if l-dl>shift-width or r-dr>l+dl or r+dr<shift+width:
        raise ValueError('rounded radial cells do not cover their parent')
    output+=indent+f'obtain part | part := cover_spatial_radius (bits := 80) (a := {rad.a[0]}) (p := {rad.a[1:]})\n'
    output+=indent+f'  (l := {l-shift}) (dl := {dl}) (r := {r-shift}) (dr := {dr}) (e := {width}) (by norm_num) (by norm_num) (by norm_num) {hyp}\n'
    for left,right in [(lo,mid),(mid,hi)]:
        s,w=endpoints(e,left,right)
        child=inputs(row,0,w,e,s)[0]
        output+=indent+f'· change ({model_literal(child)}).Mem _ _ at part\n'
        output+=cover_tree(row,e,left,right,indent+'  ','part')
    return output


def geometry_source(name,row,e,den,g,jac):
    src=header(name,['PlasmaLean.Design.DommaschkPhysicalActionCap','PlasmaLean.Design.DommaschkSignedObservable',
                     'PlasmaLean.Design.DommaschkBounceTaylorFirst',*[f'ActionBlockGapCache.DommaschkActionLaunchGap{i}' for i in range(CELLS)]])
    src+='open Certificates Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing DommaschkPhysicalActionPanel DommaschkPreMirrorSigns DommaschkMirrorEndpointSign DommaschkPhysicalFirstStep\n'
    rad,base=inputs(row,0,e,e)
    src+=f'private def radius : Model := {model_literal(rad)}\n'
    src+='private def world : Inputs := ⟨'+', '.join(map(model_literal,base))+'⟩\n'
    d,n,z=[sum(models(t,jac[1]),ZERO) for t in sparse_fields()]
    rr,dd=rad.bound()[1],d.bound()[0]
    b,c=[max(map(abs,f.bound())) for f in (n,z)]
    rc=rad.a[0]
    er=rad.e+sum(map(abs,rad.a[1:]))
    h=HEIGHTS[1]-g/2
    src+=f'''private theorem limits {{w R z t : ℝ}} (hw : |w| ≤ 1) (positiveR : 0 < R) (rad : radius.Mem w R)
    (normal : DommaschkBounceTaylorFirst.trial.Mem w (R-dkR0) z (Real.cos (2*t)) (Real.sin (2*t)))
    (vertical : world.z.Mem w z) :
    arcDensity R t z ≤ ({den}:ℝ) ∧
    max (2*(({HEIGHTS[1]}:ℝ)-‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R t z)‖)) 0 ≤ ({g}:ℝ) := by
  let f := fun q => DommaschkBounceField.atPoint q R t z
  have margin : 0 ≤ gap R ((({h}):ℚ):ℝ) (f dD) (f dnR) (f dnZ) := by
'''
    src+=cover_tree(row,e,0,CELLS,'    ','rad')
    src+=f'''  have d := DommaschkBounceTaylorFirst.dD_range hw (DommaschkBounceTaylorFirst.dD_checked.mem hw normal)
  have n := DommaschkBounceTaylorFirst.dnR_range hw (DommaschkBounceTaylorFirst.dnR_checked.mem hw normal)
  have zed := DommaschkBounceTaylorFirst.dnZ_range hw (DommaschkBounceTaylorFirst.dnZ_checked.mem hw normal)
  change _ ≤ f dD ∧ f dD ≤ _ at d
  change _ ≤ f dnR ∧ f dnR ≤ _ at n
  change _ ≤ f dnZ ∧ f dnZ ≤ _ at zed
  have radial := abs_le.mp (constant_coord (enclose (c := ofDyadic 80 [{rc}] ({er})) hw rad (by kernel_fact)))
  apply upper_columns positiveR (by norm_num) (by norm_num) (by norm_num)
  · change 0 < f dD
    linarith only [d.1]
  · apply density_margin_of_ranges (r := ({rr}:ℝ)) (d := ({dd}:ℝ)) (b := ({b}:ℝ)) (c := ({c}:ℝ)) positiveR.le
    · linarith only [radial.2]
    · norm_num
    · change _ ≤ f dD
      linarith only [d.1]
    · change |f dnR| ≤ _
      exact abs_le.mpr ⟨by linarith only [n.1], by linarith only [n.2]⟩
    · change |f dnZ| ≤ _
      exact abs_le.mpr ⟨by linarith only [zed.1], by linarith only [zed.2]⟩
    all_goals norm_num
  · convert margin using 1
    norm_num [f]
'''
    for tag,rev in [('fwd',False),('back',True)]:
        flag=str(rev).lower();rowname='DommaschkPositionFrames'+tag.title()+'.block0[0]'
        for col,model in [('world','world'),('trial','DommaschkBounceTaylorFirst.trial')]:
            src+=f'''private theorem {tag}_{col} : DommaschkPreMirrorSigns.Matches {flag} {rowname} radius {model} := by
  constructor
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  · exact eq_of_beq (by kernel_fact)
  all_goals kernel_fact
'''
        phase='(-t)' if rev else 't';zval='(-(x 1))' if rev else '(x 1)'
        src+=f'''theorem {tag}_bounds {{previous : PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}}
    (ht : t ∈ Set.Icc (0:ℝ) (1/64)) (tube : x ∈ (physicalSlab previous {rowname} 0).tube t) :
    (arcDensity (x 0) {phase} (x 1) ≤ ({den}:ℝ) ∧ max (2*(({HEIGHTS[1]}:ℝ)-strength {phase} x)) 0 ≤ ({g}:ℝ)) ∧
    0 < x 0 ∧ 0 < DommaschkBounceField.atPoint dD (x 0) {phase} (x 1) := by
  obtain ⟨rad,_,v⟩ := {tag}_world.mem tube
  obtain ⟨_,u,z⟩ := {tag}_trial.mem tube
  rw [show coord 0 t = 128*t-1 by simp [coord]] at rad v u z
  have normal : DommaschkBounceTaylorFirst.trial.Mem (128*t-1) (x 0-dkR0) {zval}
      (Real.cos (2*t)) (Real.sin (2*t)) := by
    refine ⟨u,z,?_,?_⟩
    · change (DommaschkHarmonicSlab0.model false 0 false).Mem _ _
      simpa [TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 false (by simpa using ht)
    · change (DommaschkHarmonicSlab0.model false 0 true).Mem _ _
      simpa [TrajectoryTrig.wave] using DommaschkHarmonicSlab0.physical false 0 true (by simpa using ht)
  have pos : 0 < x 0 := DommaschkMirrorBracketSlab.positive_radius (a := 0) (r := {rowname}) (by simpa using ht) tube (by kernel_fact) (by kernel_fact)
  have hw : |128*t-1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have upper := limits hw pos rad normal v
  have hd := (DommaschkBounceTaylorFirst.dD_range hw (DommaschkBounceTaylorFirst.dD_checked.mem hw normal)).1
  have positiveD : 0 < DommaschkBounceField.atPoint dD (x 0) t {zval} := by
    change _ ≤ DommaschkBounceField.atPoint dD (x 0) t {zval} at hd
    linarith only [hd]
'''
        if rev:
            src+='''  have ar := arcDensity_reflected pos t (-(x 1))
  have st := strength_reflected pos t (-(x 1))
  simp only [neg_neg] at ar st
  rw [← ar, ← st] at upper
  have dp := DommaschkSectionReflection.atPoint_reflect (p := dD) (k := 0) (by kernel_fact) (x 0) t (-(x 1))
  simp only [neg_neg, pow_zero, one_mul] at dp
  rw [← dp] at positiveD
'''
        src+='  exact ⟨upper,pos,positiveD⟩\n'
    return src+'\nend PlasmaLean.Design.'+name+'\n'


def block_source(name,geom,den,g):
    src=header(name,['ActionBlockGeometryCache.'+geom,'PlasmaLean.Certificates.MirrorActionUniformCells',
                     'PlasmaLean.Design.DommaschkPhysicalArcTrace','PlasmaLean.Design.DommaschkActionQ0R470',
                     'PlasmaLean.Design.DommaschkMirrorTwoSlabs','PlasmaLean.Design.DommaschkMirrorTwoBackwardSlabs'])
    src+='''open Certificates.PositionFrameSlabs Certificates.MirrorActionQuadrature DommaschkMirrorTubeCrossing
open DommaschkSignedObservable DommaschkPhysicalActionPanel DommaschkMirrorLaunch DommaschkBackwardPairedPrefix

/-- The two adjacent blocks selected directly from the original 650-slab archive. -/
def birthBlocks : List (Block true) :=
  [DommaschkActionQ0R470.slabs[324]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num),
   DommaschkActionQ0R470.slabs[325]'(by rw [DommaschkActionQ0R470.checked.len]; norm_num)]

private theorem fwd : Direction 1 2 twoExit twoRows := by
  constructor
  · apply Chain.cons (m := twoExit) (n := 0)
    · change run pilotLimits DommaschkPhysicalFirstStep.seed
        [DommaschkPhysicalFirstStep.row, DommaschkPhysicalSecondStep.row] = _
      simp only [run, DommaschkPhysicalFirstStep.checked, DommaschkPhysicalSecondStep.checked, Bool.and_true]
    · exact .nil _
  · refine ⟨DommaschkPhysicalFirstStep.ball_field_bounds, ?_, trivial⟩
    simpa only [zero_add] using DommaschkPhysicalSecondStep.field_bounds

private theorem bwd : Direction (-1) 2 twoBackwardExit twoBackwardRows :=
  ⟨two_backward_checked,two_backward_bounds⟩
'''
    A,G=int(den*2**20),int(g*2**26)
    src+=f'''private theorem packed {{w f : ℝ → ℝ}}
    (bound : ∀ t ∈ Set.Icc (-(1/64):ℝ) (1/64), w t ≤ ({den}:ℝ) ∧
      max (2*(({HEIGHTS[1]}:ℝ)-f t)) 0 ≤ ({g}:ℝ)) :
    Covers true w f ({HEIGHTS[1]}:ℝ) (-(1/64)) birthBlocks := by
  constructor
  · apply cells_of_floor (A := {A}) (G := {G})
    · change floorTest {A} {G} 48 DommaschkActionQ0R470.slabGroup20[4].packed = true
      kernel_fact
    · intro t ht
      have b := bound t ⟨ht.1,by linarith [ht.2]⟩
      norm_num at b ⊢
      exact b
  · constructor
    · apply cells_of_floor (A := {A}) (G := {G})
      · change floorTest {A} {G} 48 DommaschkActionQ0R470.slabGroup20[5].packed = true
        kernel_fact
      · intro t ht
        have b := bound t ⟨by linarith [ht.1],by linarith [ht.2]⟩
        norm_num at b ⊢
        exact b
    · trivial

/-- Every admitted Q-16 birth has one true trajectory proving Covers on all 96 original
cells. Its arclength density is the norm of its actual Cartesian derivative, including
both edges of the quadrature blocks, which lie inside this two-slab physical trace. -/
theorem exists_nested_covers : BirthWith (fun x => ∃ y : ℝ → Plane,
    DommaschkSignedObservable.Path 2 twoExit twoBackwardExit twoRows twoBackwardRows x y ∧
    (Covers true (fun t => arcDensity (y t 0) t (y t 1)) (fun t => strength t (y t))
        ({HEIGHTS[1]}:ℝ) (-(1/64)) birthBlocks ∧
     Covers true (fun t => ‖deriv (fun s => Contract.cylPoint (y s 0) s (y s 1)) t‖)
        (fun t => strength t (y t)) ({HEIGHTS[1]}:ℝ) (-(1/64)) birthBlocks)) := by
  apply birth_with (birthPassage fwd bwd)
  intro x y path
  have limits (t : ℝ) (ht : t ∈ Set.Icc (-(1/64):ℝ) (1/64)) :
      (arcDensity (y t 0) t (y t 1) ≤ ({den}:ℝ) ∧ max (2*(({HEIGHTS[1]}:ℝ)-strength t (y t))) 0 ≤ ({g}:ℝ)) ∧
      0 < y t 0 ∧ 0 < DommaschkBounceField.atPoint dD (y t 0) t (y t 1) := by
    rcases le_total 0 t with right | left
    · have localTime : t ∈ Set.Icc (0:ℝ) (1/64) := ⟨right,ht.2⟩
      apply {geom}.fwd_bounds localTime
      apply path.forward (physicalSlab (MirrorEndpoint.start .q0r470) DommaschkPhysicalFirstStep.row 0)
        (by simp [physicalSlabs,twoRows]) t
      exact ⟨right,by change t ≤ 0+1/64; simpa only [zero_add] using ht.2⟩
    · have localTime : -t ∈ Set.Icc (0:ℝ) (1/64) := ⟨by linarith,by linarith [ht.1]⟩
      have mem := path.backward (physicalSlab (MirrorEndpoint.start .q0r470) DommaschkJacobianBackward000.row 0)
        (by simp [physicalSlabs,twoBackwardRows]) (-t) (show _ from ⟨localTime.1,by change -t ≤ 0+1/64; simpa only [zero_add] using localTime.2⟩)
      have obs := {geom}.back_bounds localTime mem
      simpa only [neg_neg] using obs
  refine ⟨packed (fun t ht => (limits t ht).1), packed ?_⟩
  intro t ht
  obtain ⟨bound,hr,hd⟩ := limits t ht
  have inside : t ∈ Set.Ioo (-(2:ℝ)/64) (2/64) := ⟨by linarith [ht.1],by linarith [ht.2]⟩
  rw [arcDensity_on_path path inside hr hd]
  exact bound

end PlasmaLean.Design.{name}
'''
    return src


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--regions',nargs='+',type=int,choices=range(CELLS),default=range(CELLS))
    p.add_argument('--fields-only',action='store_true')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/physical-action-panels')
    p.add_argument('--jacobian-cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    a.cached_only=False
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    a.keys=[digest(RECORD),lake('lean','--version'),digest(DESIGN/'DommaschkBounceTaylor.trace')]
    f,e,den,g,jac=data(a)
    h=HEIGHTS[1]-g/2
    terms=compensated_terms(h)
    out=[]
    allpkgs=[]
    for i in a.regions:
        shift,width=endpoints(e,i,i+1)
        rad,coords=inputs(f,0,width,e,shift)
        leaf,results=shared_field(a,i,coords,h,terms)
        proof=results[-1] if a.fields_only else region_gap(a,i,rad,coords,h,terms,jac,leaf,results)
        out.append(proof[1])
        allpkgs.extend([*results,proof])
        save(a.output,out)
    if not a.fields_only and list(a.regions)==list(range(CELLS)):
        geom='DommaschkActionLaunchGeometry'
        src=geometry_source(geom,f,e,den,g,jac)
        overlay=union(a.cache,allpkgs)
        checked=compile_modules(a.cache/geom,[(geom,src,['fwd_bounds','back_bounds'])],[overlay],
                                [a.keys,*[r['key'] for _,r in allpkgs]],a,'ActionBlockGeometryCache')
        allpkgs.append(checked)
        top='DommaschkPhysicalLaunchBlocks'
        src=block_source(top,geom,den,g)
        overlay=union(a.cache,allpkgs)
        root,rec=compile_modules(a.cache/top,[(top,src,['exists_nested_covers'])],[overlay],
                                 [a.keys,checked[1]['key'],digest(DESIGN/'DommaschkActionQ0R470.trace')],
                                 a,'ActionBlockCache')
        save(a.output,rec | {'import_paths':[str(root),str(overlay)],'packet_sha256':a.keys[0]})


if __name__=='__main__':
    main()
