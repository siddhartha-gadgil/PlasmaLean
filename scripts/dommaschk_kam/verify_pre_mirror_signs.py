"""Verify both physical tube signs strictly below the lower mirror height on rows 0–315."""
import argparse
import ast
from fractions import Fraction as F
import gzip
import json
from pathlib import Path
import re
import subprocess

from bounce_mirror_pilot import HEIGHTS, Model, R0M, SCALE, angle_models
from emit_sparse_taylor_slab import RECORD, ROOT, field, model_literal
from shared_sparse_powers import add_shared_powers
from verify_backward_physical_prefix import compile_modules as compile_or_reuse, union
from verify_mirror_endpoint_signs import gap_proof, header
from verify_physical_trace_slabs import DESIGN, ALLOWED, artifact_hashes, digest, key_of, save


INPUTS='PreMirrorInputCache'
FIELDS='PreMirrorFieldCache'
POWERS='PreMirrorPowerCache'
GAPS='PreMirrorGapCache'
SIGNS='PreMirrorSignCache'


class MissingProof(Exception):
    """The requested source and exact dependency key have not yet been accepted."""


def compile_modules(work,decls,links,common,args,package):
    if args.cached_only and not (work/key_of([common,decls])/'accepted.json').is_file():
        raise MissingProof(decls[-1][0])
    return compile_or_reuse(work,decls,links,common,args,package)


def inputs(row,index,er,ez,shift=0):
    radius,vertical=row['coefficients']
    r=Model([radius[0]+shift,*radius[1:]],er)
    waves=angle_models(F(2*index+1,128),F(1,128),F(0))
    return r,(r-R0M,Model(vertical,ez),waves[2],waves[1])


def split(index,record,error):
    left=-error//2
    right=error//2
    return [(side,off,inputs(record,index,max(error+off,-off) if off<0 else max(off,error-off),
                              error,off)) for side,off in [('Left',left),('Right',right)]]


def own_fields(args,index,tag,cols):
    stem=f'DommaschkBeforeField{index:03}'+tag
    inp=stem+'Inputs'
    tail='\nend PlasmaLean.Design.'+stem+'\n'
    src=header(stem,['PlasmaLean.Design.DommaschkBounceTaylor'])+'def trial : Inputs := ⟨'
    src+=', '.join(map(model_literal,cols))+'⟩\n'+tail
    base=compile_modules(args.cache/inp,[(inp,src,[])],[],args.keys+[INPUTS],args,INPUTS)
    packages=[base]
    reuse=base
    if index!=315:
        name=stem+'Stored'
        table=add_shared_powers({inp:src},inp,stem,cols)[name]
        table=table.replace('public import PlasmaLean.Design.'+inp,'public import '+INPUTS+'.'+inp)
        reuse=compile_modules(args.cache/name,[(name,table,[])],[base[0]],
                              [POWERS,base[1]['key'],digest(DESIGN/'DommaschkStoredPowers.trace')],
                              args,POWERS)
        packages.append(reuse)
    for label,p in zip('DRZ',('dD','dnR','dnZ'),strict=True):
        leaf=stem+label
        src=header(stem,[INPUTS+'.'+inp])+field(p,cols)+tail
        if index!=315:
            src=src.replace(INPUTS+'.'+inp,POWERS+'.'+stem+'Stored')
            src=src.replace('apply Blocks.chunk ',
                            'apply DommaschkStoredPowers.checkedChunk storedPowers storedPowers_checked ')
        packages.append(compile_modules(args.cache/leaf,[(leaf,src,[])],list({base[0],reuse[0]}),
                                        [FIELDS,reuse[1]['key']],args,FIELDS))
    return stem,[FIELDS+'.'+stem+s for s in 'DRZ'],packages


def jacobian(args,index,row,out):
    stems=(['DommaschkBounceTaylorFirst'] if index==0 else [f'DommaschkJacobianForward{index:03}',
                                                           f'DommaschkProjectedJacobian{index:03}'])
    for stem in stems:
        tracked=ROOT/'PlasmaLean/Design'/(stem+'Inputs.lean')
        choices=[]
        if tracked.is_file() and (DESIGN/(stem+'.olean')).is_file():
            choices.append((tracked,'PlasmaLean.Design.',[]))
        for path in sorted((args.jacobian_cache/stem).glob('*/accepted.json')):
            package='JacobianTraceCache'
            data=json.loads(path.read_text())
            if data['index']!=index or data['module']!=stem or set(data['axioms'])!=ALLOWED:
                continue
            inp=path.parent/package/(stem+'Inputs.lean')
            if inp.is_file():
                choices.append((inp,package+'.',[(path.parent,data)]))
        for inp,package,parents in choices:
            cols0=[Model(ast.literal_eval(p),int(e)) for p,e in re.findall(
                    r'ofDyadic 80 (\[[^\]]*\]) \((-?\d+)\)',inp.read_text())]
            if len(cols0)!=4 or min(m.e for m in cols0[:2])<out:
                continue
            rad,cols=inputs(row,index,cols0[0].e,cols0[1].e)
            if any((a.a,a.e)!=(b.a,b.e) for a,b in zip(cols0,cols,strict=True)):
                continue
            for base,data in parents:
                artifact_hashes(base,data)
            return rad,cols,stem,[package+stem],parents
    return None


def prove_row(args,i,row,error,models):
    parts=[]
    parents=[]
    base_radius,base=inputs(row,i,error,error) if len(models)>1 else models[0][2][:2]
    for tag,shift,(rad,cols,provider,imports,upstream) in models:
        gap=f'DommaschkBeforeGap{i:03}'+tag
        src=header(gap,['PlasmaLean.Design.DommaschkPreMirrorSigns',*imports])
        src+='open DommaschkMirrorEndpointSign '+provider+'\n'
        src+=gap_proof(False,False,HEIGHTS[0],rad,cols)+'\nend PlasmaLean.Design.'+gap+'\n'
        tracked=(digest(DESIGN/(provider+'.trace')) if imports==['PlasmaLean.Design.'+provider] else None)
        common=args.keys+[tracked,[(r['key'],r['artifacts']) for _,r in upstream],
                         digest(DESIGN/'DommaschkPreMirrorSigns.trace')]
        overlay=union(args.cache,upstream)
        result=compile_modules(args.cache/gap,[(gap,src,['sign_on_models'])],[overlay],common,args,GAPS)
        parts.append((gap,provider,rad,shift))
        parents.extend([*upstream,result])
    name=f'DommaschkPreMirrorSign{i:03}'
    block,offset=divmod(i,8)
    harmonic=f'DommaschkHarmonicBlock{block:02}'
    src=header(name,['PlasmaLean.Design.'+harmonic,*[GAPS+'.'+part[0] for part in parts]])
    src+='open DommaschkMirrorEndpointSign Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing\n'
    src+='open DommaschkPreMirrorSigns\n'
    src+=f'private def Rmodel : Model := {model_literal(base_radius)}\n'
    src+='private def box : Inputs := ⟨'+', '.join(map(model_literal,base))+'⟩\n'
    src+=f'''private theorem clock_inputs {{t u z : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hu : box.u.Mem (128*t-{2*i+1}) u) (hz : box.z.Mem (128*t-{2*i+1}) z) :
    box.Mem (128*t-{2*i+1}) u z (Real.cos (2*t)) (Real.sin (2*t)) := by
  refine ⟨hu,hz,?_,?_⟩
'''
    for col,flag in [('cos','false'),('sin','true')]:
        src+=f'''  · let p := {harmonic}.packet ({offset}:Fin {min(8,391-8*block)})
    have timed := Certificates.TrajectoryHarmonicPacket.physical p false 0 {flag} (t := t)
      (by norm_num at ht ⊢; exact ht)
    change ((p false 0).model {flag}).Mem _ _
    convert timed using 1 <;> norm_num [Certificates.TrajectoryTrig.wave]
'''
    src+=f'''private theorem below {{t R z : ℝ}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (pos : 0 < R) (rad : Rmodel.Mem (128*t-{2*i+1}) R)
    (u : box.u.Mem (128*t-{2*i+1}) (R-dkR0)) (v : box.z.Mem (128*t-{2*i+1}) z) :
    ‖DommaschkQA2R.field DommaschkQA2R.candidate (Contract.cylPoint R t z)‖ <
      DommaschkFirstMirrorLaunchSign.height false := by
  have hs : |128*t-{2*i+1}| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have inp := clock_inputs ht u v
  apply physical_sign false pos (by norm_num [DommaschkFirstMirrorLaunchSign.height])
'''
    if len(parts)==1:
        src+=f'  exact {parts[0][0]}.sign_on_models hs rad inp\n'
    else:
        a,*p=base_radius.a
        (_,_,lower,l),(_,_,upper,r)=parts
        src+=f'''  obtain part | part := cover_spatial_radius (bits := 80) (a := {a}) (p := {p})
    (l := {l}) (dl := {lower.e}) (r := {r}) (dr := {upper.e}) (e := {base_radius.e})
    (by norm_num) (by norm_num) (by norm_num) rad
'''
        for gap,provider,rad,off in parts:
            src+=f'''  · change ({model_literal(rad)}).Mem _ _ at part
    have shifted := shifted_mem (u := {provider}.trial.u) part
      (eq_of_beq (by kernel_fact)) (by kernel_fact)
    exact {gap}.sign_on_models hs part ⟨shifted,inp.2.1,inp.2.2.1,inp.2.2.2⟩
'''
    for tag,back in [('fwd','false'),('back','true')]:
        stored=f'DommaschkPositionFrames{tag.title()}.block{i//16}[{i%16}]'
        phase='t' if tag=='fwd' else '(-t)'
        src+=f'''
private def {tag}Row : Step := {stored}
private theorem {tag}Matches : DommaschkPreMirrorSigns.Matches {back} {tag}Row Rmodel box := by
  constructor
  · apply eq_of_beq; kernel_fact
  · apply eq_of_beq; kernel_fact
  · apply eq_of_beq; kernel_fact
  · kernel_fact
  · kernel_fact
  · kernel_fact

/-- Strictly below the lower mirror height throughout the closed {tag} physical tube. -/
theorem {tag}_tube_below {{prev : State}} {{t : ℝ}} {{x : Plane}} (ht : t ∈ Set.Icc ({i}/64:ℝ) ({i+1}/64))
    (hx : x ∈ (physicalSlab prev {stored} ({i}/64)).tube t) :
    strength {phase} x < DommaschkFirstMirrorLaunchSign.height false := by
  have inside : x ∈ (physicalSlab prev {tag}Row ({i}/64)).tube t := hx
  obtain ⟨r,u,z⟩ := {tag}Matches.mem inside
  have clock : coord ({i}/64) t = 128*t-{2*i+1} := by unfold coord; ring
  rw [clock] at r u z
  have pos : 0 < x 0 := DommaschkMirrorBracketSlab.positive_radius
    (a := {i}/64) (r := {tag}Row)
    (by rwa [show ({i}/64:ℝ)+1/64 = {i+1}/64 by norm_num]) inside
    (by kernel_fact) (by kernel_fact)
'''
        if tag=='fwd':
            src+='  exact below ht pos r u z\n'
        else:
            src+='''  have rev := strength_reflected pos t (-(x 1))
  rw [neg_neg] at rev
  unfold strength
  rw [rev]
  exact below ht pos r u z
'''
    src+='\nend PlasmaLean.Design.'+name+'\n'
    overlay=union(args.cache,parents)
    root,r=compile_modules(args.cache/name,[(name,src,['fwd_tube_below','back_tube_below'])],[overlay],
                           [args.keys,*[r['key'] for _,r in parents],digest(DESIGN/(harmonic+'.trace'))],
                           args,SIGNS)
    public={k:v for k,v in r.items() if k!='artifacts'} | {
        'index':i,'packet_sha256':args.keys[0],'lean_version':args.keys[1],
        'import_paths':[str(root),str(overlay)]}
    (args.cache/'rows').mkdir(exist_ok=True)
    save(args.cache/'rows'/f'{i:03}.json',public)
    print(f'verified uninterrupted below-height physical row {i}: {r["key"]}',flush=True)
    return public


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--range',type=int,nargs=2,default=(0,315),metavar=('FIRST','LAST'))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/pre-mirror-signs')
    p.add_argument('--jacobian-cache',type=Path,default=ROOT/'.lake/jacobian-checks')
    p.add_argument('--available-only',action='store_true',help='skip missing upstream field packages')
    p.add_argument('--fields-only',action='store_true',help='populate isolated sparse field packages')
    p.add_argument('--cached-only',action='store_true',help='export current matching proofs without compiling')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    lo,hi=args.range
    if not 0<=lo<=hi<316:
        p.error('the strictly submirror prefix consists of rows 0–315')
    packet=json.loads(gzip.decompress(RECORD.read_bytes()))
    if (packet['section_in_half_pi'],packet['launch_u'],[t['direction'] for t in packet['traces']]) != (
            0,'47/100',[-1,1]):
        raise ValueError('wrong physical trajectory witness')
    b,f=[t['steps'] for t in packet['traces']]
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path=lake('printenv','LEAN_PATH')
    args.cache=args.cache.resolve()
    args.keys=[digest(RECORD),lake('lean','--version'),digest(DESIGN/'DommaschkBounceTaylor.trace')]
    results=[]
    for i in range(lo,hi+1):
        if b[i]['coefficients']!=[f[i]['coefficients'][0],[-c for c in f[i]['coefficients'][1]]]:
            raise ValueError(f'signed reference mismatch on {i}')
        e=max(t[i]['physical_radius_out'] for t in (b,f))
        provider=jacobian(args,i,f[i],e) if i<315 else None
        try:
            if provider:
                models=[('',0,provider)]
            elif i==315:
                models=[(tag,shift,(r,cols,*own_fields(args,i,tag,cols)))
                        for tag,shift,(r,cols) in split(i,f[i],e)]
            elif args.available_only:
                continue
            else:
                r,cols=inputs(f[i],i,e,e)
                models=[('',0,(r,cols,*own_fields(args,i,'',cols)))]
            if not args.fields_only:
                results.append(prove_row(args,i,f[i],e,models))
        except MissingProof:
            continue
    if args.output:
        save(args.output,results)


if __name__=='__main__':
    main()
