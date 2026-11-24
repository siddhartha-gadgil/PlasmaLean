"""Certify the outward derivative of squared QA2R strength on a complete mirror slab."""
import argparse
from fractions import Fraction
import gzip
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import Model, R0M, ZERO, angle_models
from emit_sparse_forward_jacobian import emit
from emit_sparse_jacobian import derivative, derivative_file
from emit_sparse_taylor_slab import RECORD, ROOT, model_literal, models
from screen_sparse_jacobians import field_jet
from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import DESIGN, JACOBIAN_PACKAGE, accepted, digest, upstream


CACHE = ROOT/'.lake/mirror-slopes'
ANGLES = 'MirrorAngleCache'
SLOPES = 'MirrorSlopeCache'
TUBES = 'MirrorSlopeTubeCache'


def data(i):
    with gzip.open(RECORD,'rt') as stream:
        rows = {tr['direction']:tr['steps'][i] for tr in json.load(stream)['traces']}
    f,b = rows[1],rows[-1]
    error = f['physical_trial_radius']
    if max(f['physical_radius_out'],b['physical_radius_out'])>error:
        raise ValueError('one signed physical tube exceeds this field box')
    if (f['coefficients'][0]!=b['coefficients'][0] or
            f['coefficients'][1]!=[-v for v in b['coefficients'][1]]):
        raise ValueError('reference centers do not reflect')
    r,z = (Model(c,error) for c in f['coefficients'])
    waves = angle_models(Fraction(2*i+1,128),Fraction(1,128),Fraction(0))
    return r,(r-R0M,z,waves[2],waves[1]),rows


def angle_sources(i, columns, jac):
    ns=f'DommaschkMirrorSlope{i:03}Angles'
    head=f'''module
public import {JACOBIAN_PACKAGE}.{jac}Stored

/-! # Harmonic polynomial derivatives on the archived mirror bracket -/
@[expose] public section
namespace PlasmaLean.Design.{ns}
open Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly DommaschkBounceTaylor {jac}
set_option maxRecDepth 16000
set_option linter.style.longLine false
set_option Elab.async false
'''
    end=f'end PlasmaLean.Design.{ns}\n'
    terms=[]
    for scalar,tag,jet in zip(('dD','dnR','dnZ'),('D','R','Z'),field_jet(),strict=True):
        for j,letter in enumerate('CS'):
            symbol='angle'+tag+letter
            blocks=models(derivative(jet[0],j+2),columns)
            original=derivative_file(scalar,symbol,j,blocks,ns,jac+'Inputs','DommaschkJacobian')
            marker='abbrev '+symbol+' := '
            _,found,body=original.partition(marker)
            if not found or not body.endswith(end):
                raise ValueError('unexpected sparse derivative certificate')
            spatial=('dU','dZ')[j]
            if not body.startswith(spatial+' '+scalar+'\n'):
                raise ValueError('unexpected polynomial in derivative generator')
            body=body.removesuffix(end).replace(spatial+' '+scalar,'d'+letter+' '+scalar,1)
            terms.append(marker+body.replace('apply Blocks.chunk ',
                f'apply DommaschkStoredPowers.checkedChunk {jac}.storedPowers {jac}.storedPowers_checked '))
    return ns,head+''.join(terms)+end


def spatial(i, version):
    return accepted(upstream(ROOT/'.lake/jacobian-checks',list(emit(i,shared=True).items()),
        'verify_sparse_forward_jacobians.py',digest(RECORD),version,JACOBIAN_PACKAGE),i,0)


def angular(i, version, args):
    root,jac=spatial(i,version)
    _,cols,_=data(i)
    n,src=angle_sources(i,cols,jac['module'])
    labels=['angle'+tag+letter+'_checked' for tag in 'DRZ' for letter in 'CS']
    return compile_modules(CACHE/n,[(n,src,labels)],[root],
        [digest(RECORD),version,jac['key'],jac['artifacts']],args,package=ANGLES)


def bounds_source(i,jac,angles):
    r,cols,_ = data(i)
    name=f'DommaschkMirrorSlope{i:03}'
    rate=Fraction(1,128 if i==316 else 400)
    head=f'''module
public import {JACOBIAN_PACKAGE}.{jac}
public import {ANGLES}.{angles}
public import PlasmaLean.Design.DommaschkMirrorStrengthSlope

/-! # Squared-strength slope on the full QA2R physical bracket -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.TrajectoryTaylorModel DommaschkKam DommaschkKam.DkPoly DommaschkBounceTaylor
open DommaschkMirrorStrengthSlope {jac} {angles}
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000
set_option linter.style.longLine false
set_option Elab.async false
'''
    defs=[]
    lines=[f'''theorem numerator_margin {{w R z c s : ℝ}} (hw : |w| ≤ 1)
    (inp : trial.Mem w (R-dkR0) z c s) :
    ({rate} : ℝ) * (R^17 * evR (R-dkR0) z c s dD) < numerator R z c s := by
  have off : (constant (29/32)).Mem w dkR0 := by
    convert constant_mem (29/32) w using 1
    norm_num [dkR0]
  have rad : ({model_literal(r)}).Mem w R := by
    have h := enclose (c := {model_literal(r)}) hw (mem_add inp.1 off) (by kernel_fact)
    simpa only [sub_add_cancel] using h''']
    table={'radius':(r,'R','rad'),'c':(cols[2],'c','inp.2.2.1'),'s':(cols[3],'s','inp.2.2.2')}
    for scalar,tag,jet in zip(('dD','dnR','dnZ'),'DRZ',field_jet(),strict=True):
        for j,terms in enumerate((*jet,derivative(jet[0],2),derivative(jet[0],3))):
            suffix=('','U','Z','C','S')[j]
            symbol=scalar if j==0 else ('grad' if j<3 else 'angle')+tag+suffix
            k='N' if tag=='R' and not suffix else tag+suffix
            expr='val'+k
            lines += [f'  let {expr} := evR (R-dkR0) z c s {symbol}',
                      f'  have in{k} := {symbol}_checked.mem hw inp']
            table[k]=sum(models(terms,cols),ZERO),expr,'in'+k
    for k,q in [('two',2),('negative',-1),('sixteen',16),('rate',rate)]:
        m=Model.rational(q)
        defs.append(f'private def mdl{k} : Model := {model_literal(m)}')
        lines += [f'  have in{k} : mdl{k}.Mem w ({q} : ℝ) := by',
                  f'    convert enclose (c := mdl{k}) hw (constant_mem ({q}) w) (by kernel_fact) using 1\n    norm_num']
        table[k]=(m,f'({q} : ℝ)','in'+k)
    def op(k,a,b,sign):
        ma,va,ha=table[a]; mb,vb,hb=table[b]
        m=ma*mb if sign=='*' else ma+mb
        act=(f'mem_product_fit hw {ha} {hb}' if sign=='*' else f'enclose hw (mem_add {ha} {hb})')
        defs.append(f'private def mdl{k} : Model := {model_literal(m)}')
        lines.extend([f'  let val{k} := {va} {sign} {vb}',
                      f'  have in{k} : mdl{k}.Mem w val{k} := {act} (by kernel_fact)'])
        table[k]=m,'val'+k,'in'+k
    for t in 'DRZ':
        for k,a,b,sign in [('sC','s',t+'C','*'),('cS','c',t+'S','*'),
                ('minus','sC'+t,'negative','*'),('arc','cS'+t,'minus'+t,'+'),
                ('double','two','arc'+t,'*'),('phi','D','double'+t,'*'),
                ('du','N',t+'U','*'),('dz','Z',t+'Z','*'),
                ('sp','du'+t,'dz'+t,'+'),('material','sp'+t,'phi'+t,'+')]:
            op(k+t,a,b,sign)
    operations=[('rd','radius','D','*'),('rd2','rd','rd','*'),('n2','N','N','*'),
        ('z2','Z','Z','*'),('U0','rd2','n2','+'),('U','U0','z2','+'),
        ('v1','N','D','*'),('v2','radius','materialD','*'),('v3','v1','v2','+'),
        ('v4','rd','v3','*'),('v5','N','materialR','*'),('v6','Z','materialZ','*'),
        ('v7','v4','v5','+'),('v8','v7','v6','+'),('W','two','v8','*'),
        ('lhs','radius','W','*'),('rhs1','N','U','*'),('rhs2','sixteen','rhs1','*'),
        ('rhs3','negative','rhs2','*'),('numer','lhs','rhs3','+'),
        ('r2','radius','radius','*'),('r4','r2','r2','*'),('r8','r4','r4','*'),
        ('r16','r8','r8','*'),('r17','radius','r16','*'),('den','r17','D','*'),
        ('allow','rate','den','*'),('negallow','negative','allow','*'),('margin','numer','negallow','+')]
    for k,a,b,sign in operations: op(k,a,b,sign)
    low,high=table['margin'][0].bound()
    if low<=0: raise ValueError(f'row {i}: squared-strength slope enclosure crosses zero')
    mid,width=(low+high)/2,(high-low)/2
    lines.extend([f'  have enc := enclose (c := ⟨[({mid})],({width})⟩) hw inmargin (by kernel_fact)',
        '  have pos : 0 < valmargin := by',
        '    norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at enc','    linarith only [enc.1]',
        f'  have eq : valmargin = numerator R z c s - ({rate}:ℝ)*(R^17 * evR (R-dkR0) z c s dD) := by',
        '    dsimp only ['+', '.join(dict.fromkeys(v for _,v,_ in table.values() if v.startswith('val')))+
        ', numerator, material]','    ring','  linarith only [pos,eq]'])
    return name,head+'\n'.join(defs+['']+lines)+f'\nend PlasmaLean.Design.{name}\n',rate


def tube_source(i,jac,num,rate,closed=False):
    _,_,rows=data(i)
    name=f'DommaschkMirrorSlope{i:03}' + ('ClosedTube' if closed else 'Tube')
    out=f'''module
public import {SLOPES}.{num}
public import {JACOBIAN_PACKAGE}.{jac}
public import PlasmaLean.Design.DommaschkMirrorEndpointSign
public import PlasmaLean.Design.DommaschkPositionFramesFwd

/-! # Outward transversality for both signed physical mirror tubes -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates Certificates.PositionFrameSlabs TrajectoryTaylorModel
open DommaschkKam DommaschkKam.DkPoly DommaschkBounceField DommaschkBounceTaylor
open DommaschkMirrorStrengthSlope Contract Set
set_option linter.style.longLine false
set_option maxRecDepth 16000

private theorem clock (t : ℝ) : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
'''
    for sign,signed,frame,word in [(1,'1','Fwd','forward'),(-1,'(-1)','Back','backward')]:
        step=rows[sign]; tag=frame.lower();rn=f'row_{tag}'
        z='(y t 1)' if sign==1 else '(-(y t 1))'
        phi='a' if sign==1 else '(-a)'
        a=f'({i}/64 : ℝ)'; b=f'({i+1}/64 : ℝ)'; w=f'(128*t-{2*i+1})'
        # The longer signed solution supplies a two-sided derivative at an internal seam.
        # The polynomial and physical-tube inputs are valid on the entire closed cell.
        domain = 'Icc' if closed else 'Ioo'
        derivative = 'HasDerivAt' if closed else 'HasDerivWithinAt'
        support = '' if closed else f' (Icc {a} {b})'
        flow = 'field' if closed else '(field.hasDerivAt (Icc_mem_nhds ht.1 ht.2))'
        hc = 'ht' if closed else 'Ioo_subset_Icc_self ht'
        euclidean_support = '' if closed else f'(Icc {a} {b}) '
        composition = 'comp_hasDerivAt' if closed else 'comp_hasDerivWithinAt'
        zp=f'{jac}.trial.z.poly' if sign==1 else f'QPoly.scale (-1) {jac}.trial.z.poly'
        out+=f'''
abbrev {rn} := DommaschkPositionFrames{frame}.block{i//16}[{i%16}]

/-- The squared physical field strength has a strictly positive derivative at every
interior point of the original {word} bracket tube on any actual field solution. -/
theorem {tag}_transverse {{t : ℝ}} (ht : t ∈ {domain} {a} {b}) {{y : ℝ → DommaschkBounceField.State}}
    {{prev : PositionFrameSlabs.State}} (hx : coordinates.symm (y t) ∈ (physicalSlab prev {rn} {a}).tube t)
    (field : {derivative} y (physicalFlow 0 {signed} t (y t)){support} t) :
    ∃ v > ({rate}:ℝ), HasDerivAt (fun a => ‖DommaschkQA2R.field DommaschkQA2R.candidate
      (cylPoint (y a 0) {phi} (y a 1))‖^2) v t := by
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hu0 := DommaschkMirrorEndpointSign.coordinate hx 0
  have hz0 := DommaschkMirrorEndpointSign.coordinate hx 1
  change |y t 0 - QPoly.eval (polynomial {rn} 0) (coord {a} t)| ≤ _ at hu0
  change |y t 1 - QPoly.eval (polynomial {rn} 1) (coord {a} t)| ≤ _ at hz0
  have eu : polynomial {rn} 0 = QPoly.add [29/32] {jac}.trial.u.poly := by with_unfolding_all rfl
  have ez : polynomial {rn} 1 = {zp} := by apply eq_of_beq; kernel_fact
  rw [clock,eu,QPoly.eval_add] at hu0
  norm_num only [QPoly.eval_cons,QPoly.eval_nil,mul_zero,add_zero,Rat.cast_div,
    Rat.cast_ofNat] at hu0
  rw [clock,ez{',QPoly.eval_scale' if sign==-1 else ''}] at hz0
  have cap : {rn}.physicalOut / (2:ℝ)^80 ≤ ({jac}.trial.u.radius:ℝ) := by
    change ({step['physical_radius_out']}:ℝ)/2^80 ≤ (({rows[1]['physical_trial_radius']}/2^80 : ℚ):ℝ)
    norm_num
  have hu : {jac}.trial.u.Mem {w} (y t 0-dkR0) := by
    unfold Model.Mem
    apply le_trans _ cap
    convert hu0 using 2
    unfold dkR0
    ring
    norm_num
  have hz : {jac}.trial.z.Mem {w} {z} := by
    unfold Model.Mem
    apply le_trans _ cap
'''
        if sign==1:
            out+='    exact hz0\n'
        else:
            out+=f'''    simp only [Rat.cast_neg,Rat.cast_one,neg_one_mul] at hz0
    rw [show -(y t 1) - QPoly.eval {jac}.trial.z.poly {w} =
        -(y t 1 - -QPoly.eval {jac}.trial.z.poly {w}) by ring,abs_neg]
    exact hz0
'''
        out+=f'''  have hc := {hc}
  have den := {jac}.denominator_pos hc hu hz
  have input := {jac}.clock_inputs hc hu hz
  have margin := {num}.numerator_margin hs input
  have radius : 0 < y t 0 := by
    have h := enclose (c := ⟨[0],1/2⟩) hs hu (by kernel_fact)
    change (⟨[0],1/2⟩ : Model).Mem _ (y t 0 - dkR0) at h
    norm_num [Model.Mem, dkR0, abs_le] at h
    linarith
  exact {word}_of_physical {flow} radius den margin

/-- The physical strength itself crosses any positive attained level transversely.
The Euclidean hypotheses are the ones returned by the actual field-step solver. -/
theorem {tag}_level_transverse {{t h : ℝ}} (ht : t ∈ {domain} {a} {b}) {{y : ℝ → Plane}}
    {{prev : PositionFrameSlabs.State}} (hx : y t ∈ (physicalSlab prev {rn} {a}).tube t)
    (field : {derivative} y (DommaschkJacobian.euclideanFlow 0 {signed} t (y t))
      {euclidean_support}t) (hp : 0 < h)
    (hit : DommaschkMirrorTubeCrossing.strength {'t' if sign==1 else '(-t)'} (y t) = h) :
    ∃ v > ({rate}:ℝ) / (2*h), HasDerivAt (fun a => DommaschkMirrorTubeCrossing.strength {phi} (y a)) v t := by
  apply at_positive_level (f := fun a => DommaschkMirrorTubeCrossing.strength {phi} (y a))
    (k := {rate}) (t := t) (fun a => norm_nonneg _) hp hit
  have d := coordinates.toContinuousLinearMap.hasFDerivAt.{composition} t field
  apply {tag}_transverse (y := fun a => coordinates (y a)) ht
  · simpa only [ContinuousLinearEquiv.symm_apply_apply] using hx
  · apply d.congr_deriv
    exact coordinates.apply_symm_apply _
'''
    return name,out+f'\nend PlasmaLean.Design.{name}\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index',required=True,type=int,choices=range(316,325))
    parser.add_argument('--part',choices=('angles','bounds','tube','closed-tube'),default='angles')
    parser.add_argument('--output',type=Path,help='write a replay manifest with Lean import paths')
    args=parser.parse_args()
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    v=lake('lean','--version')
    namespace=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                             lean_path=lake('printenv','LEAN_PATH'))
    angle_root,angle_record=angular(args.index,v,namespace)
    paths=[angle_root]
    rate=None
    if args.part=='angles':
        root,record=angle_root,angle_record
    else:
        jac_root,jac=spatial(args.index,v)
        name,src,rate=bounds_source(args.index,jac['module'],angle_record['module'])
        root,record=compile_modules(CACHE/name,[(name,src,['numerator_margin'])],
            [jac_root,angle_root],[v,digest(RECORD),jac['key'],angle_record['key'],
                 digest(DESIGN/'DommaschkMirrorStrengthSlope.trace')],namespace,package=SLOPES)
        paths=[root,angle_root,jac_root]
        if args.part in ('tube', 'closed-tube'):
            n,src=tube_source(args.index,jac['module'],name,rate,closed=args.part=='closed-tube')
            deps=[digest(DESIGN/(m+'.trace')) for m in ('DommaschkMirrorEndpointSign',
                'DommaschkPositionFramesFwd','DommaschkPositionFramesBack')]
            labels=['fwd_transverse','back_transverse','fwd_level_transverse','back_level_transverse']
            package = 'MirrorSlopeClosedTubeCache' if args.part == 'closed-tube' else TUBES
            root,record=compile_modules(CACHE/n,[(n,src,labels)],
                paths,[v,digest(RECORD),record['key'],deps],namespace,package=package)
            paths=[root,*paths]
    result={k:record[k] for k in ('module','key','theorems','axioms')}
    result.update(index=args.index,part=args.part,rate_lower=str(rate) if rate else None,
                  import_paths=[str(p) for p in paths])
    output=json.dumps(result,indent=2)
    if args.output:
        args.output.write_text(output+'\n')
    print(output,flush=True)


if __name__=='__main__':
    main()
