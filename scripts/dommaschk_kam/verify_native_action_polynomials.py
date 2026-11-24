"""Integrate a lower polynomial on both signed clocks of each existing Q0R478 native model."""
import argparse
from fractions import Fraction as F
from pathlib import Path
from types import SimpleNamespace

from bounce_mirror_pilot import Model
from emit_sparse_taylor_slab import model_literal
from grouped_profile_arithmetic import preamble
from verify_backward_physical_prefix import compile_modules,union
from verify_centered_strength import Arithmetic,footer
from verify_coarse_action_models import env
from verify_grouped_action_polynomials import H,PACKAGE,integral_source,proposal,records,saved_proposals
from verify_native_action_columns import physical_models
import verify_native_action_models as native
from verify_paired_action_profiles import native_provider
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save


def source(i,model,values,fixed=None):
    name=f'DommaschkQ0R478NativeLowerPolynomial{i:03}'
    d,_,power,u,g=values
    a=Arithmetic()
    a.leaf('D',d,'(atPoint dD (x 0) t (x 1))','hd')
    a.leaf('P',power,'((x 0)^16)','hp')
    a.leaf('U',u,'((x 0)^16*(strength t x)^2)','hu')
    a.leaf('G',g,'((x 0)^16*(height^2-(strength t x)^2))','hg')
    for k,q in [('two',F(2)),('double',2*H),('inverse',1/(2*H))]:
        a.literal(k,q)
    left=a.op('L',a.op('UG','U','*','G'),'*','two')
    den=a.op('Q',a.op('dSq','D','*','D'),'*',
             a.op('divisor',a.op('hpower','double','*','P'),'-',a.op('scaledG','G','*','inverse')))
    p=proposal(a.values[left],a.values[den]) if fixed is None else Model(fixed)
    a.leaf('p',p,'(QPoly.eval proposed.poly s)','inPoly')
    gap=a.op('margin',left,'-',a.op('product',a.op('pSq','p','*','p'),'*',den))
    lower,_=a.interval(gap)
    if lower<0:
        raise ValueError('negative checked lower-polynomial margin')
    a.interval('D')
    src=preamble(name,[native.OUTPUT_PACKAGE+'.'+model,'PlasmaLean.Certificates.PolynomialActionFloor',
                       'PlasmaLean.Design.DommaschkPairedArcRatio'])
    src+=f'''
def proposed : Model := {model_literal(p)}
abbrev height : ℝ := {H}
def groupClock (t : ℝ) := (128*t-{2*i+1})/1
abbrev fwdOuter{i:03} := {model}.row
abbrev backOuter{i:03} := {model}.backRow
'''
    src+='\n'.join(a.defs)
    src+=f'''
theorem physical {{s t : ℝ}} {{x : Plane}} (hs : |s| ≤ 1) (rp : 0 < x 0)
    (hd : {model}.den.Mem s (atPoint dD (x 0) t (x 1)))
    (hp : {model}.r16.Mem s ((x 0)^16))
    (hu : {model}.u.Mem s ((x 0)^16*(strength t x)^2))
    (hg : {model}.num.Mem s ((x 0)^16*(height^2-(strength t x)^2))) :
    QPoly.eval proposed.poly s ≤ weight t x * Real.sqrt (2*(height-strength t x)) := by
  have inPoly : proposed.Mem s (QPoly.eval proposed.poly s) := by
    rw [Model.Mem,show proposed.radius = 0 by with_unfolding_all rfl]
    simp
'''
    src+='\n'.join(a.body)
    src+=f'''
  have dp : 0 < atPoint dD (x 0) t (x 1) := by linarith only [boundD.1]
  obtain ⟨wp,hw⟩ := DommaschkPairedArcRatio.physical_identity rp dp
  apply Certificates.PolynomialActionFloor.point (P := (x 0)^16) (G := (x 0)^16*(height^2-(strength t x)^2))
    (U := (x 0)^16*(strength t x)^2) (h := height) (D := atPoint dD (x 0) t (x 1))
    (by norm_num [height]) (norm_nonneg _) (pow_pos rp _) dp wp le_rfl
  · rw [← DommaschkNativeActionGeometry.squared_numerator rp t]
    dsimp only at hw
    linarith only [hw]
  · have bound : 0 ≤ valmargin := by linarith only [boundmargin.1]
    dsimp only [{', '.join(a.locals)}] at bound
    convert bound using 1
    norm_num only [height,Rat.cast_div,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_intCast]
    ring
'''
    for sign,method,clock in [('fwd','physical','t'),('back','backward_physical','(-t)')]:
        src+=f'''
theorem {sign}{i:03} {{prev : PositionFrameSlabs.State}} {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {sign}Outer{i:03} ({i}/64)).tube t) :
    QPoly.eval proposed.poly (groupClock t) ≤ weight {clock} x * Real.sqrt (2*(height-strength {clock} x)) := by
  obtain ⟨rp,hd,_,hp,hu,hg⟩ := {model}.{method} ht hx
  simp only [groupClock,div_one]
  apply physical (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩) rp hd hp hu
  simpa only [show ((DommaschkFirstMirrorLaunchSign.height true : ℚ):ℝ) = height by
    norm_num [height,DommaschkFirstMirrorLaunchSign.height]] using hg
'''
    integral,total=integral_source(i,i+1,p)
    return (name,src+integral+footer(name),['physical',f'fwd{i:03}',f'back{i:03}','integral']),p.a,lower,total


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--rows',nargs='+',type=int,default=list(range(176,192)))
    p.add_argument('--propose',action='store_true',help='fit a new proposal instead of checking the saved exact coefficients')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-action-profiles')
    p.add_argument('--model-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--output-cache',type=Path,default=ROOT/'.lake/native-action-polynomials')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if not a.rows or len(set(a.rows))!=len(a.rows) or any(i<0 or i>=325 for i in a.rows):
        p.error('choose distinct physical rows through 324')
    if not a.propose and any(('native',i,i+1) not in saved_proposals() for i in a.rows):
        p.error('the saved native polynomials cover indices 176 through 191; use --propose for a new row')
    env(a)
    data=native.static_data()
    static=native.verify_static(SimpleNamespace(**{**vars(a),'cache':a.model_cache,'fields':range(4)}),data)
    traces=records()[1][2]
    result={}
    (a.output_cache/'rows').mkdir(parents=True,exist_ok=True)
    for i in a.rows:
        fields,_,_,packet=native_provider(a,i,478,data,static)
        parent=fields[-1][1]
        cap=max(t['steps'][i]['physical_radius_out'] for t in traces)
        fixed=None if a.propose else saved_proposals()['native',i,i+1]
        decl,coeff,margin,total=source(i,parent['module'],physical_models(traces[1],i,cap),fixed)
        imports=union(a.output_cache,[*static,*fields])
        keys=[a.version,parent['key'],digest(DESIGN.parent/'Certificates/PolynomialActionFloor.trace')]
        base,r=compile_modules(a.output_cache/decl[0],[decl],[imports],keys,a,PACKAGE)
        out={k:r[k] for k in ['module','key','theorems','axioms','wall_seconds','peak_rss_kib']}
        out.update(start=i,stop=i+1,packet_sha256=packet,model=parent['key'],coefficients=coeff,
            signed_mass=str(total),margin=str(margin),import_paths=list(map(str,[base,imports])))
        save(a.output_cache/'rows'/f'{i:03}.json',out)
        result[i]=out
        save(a.output,result)
        print(decl[0],r['key'],flush=True)


if __name__=='__main__':
    main()
