"""Compose an accepted signed physical step with the two checked endpoint mirror signs."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import ALLOWED, RECORD, ROOT, artifact_hashes, digest, save


def admitted(base,name,key):
    r=json.loads((base/'accepted.json').read_text())
    if r['module']!=name or r['key']!=key or set(r['axioms'])!=ALLOWED:
        raise ValueError(f'wrong accepted mathematics for {name}')
    artifact_hashes(base,r)
    return r


def source(i,backward):
    direction='Backward' if backward else 'Forward'
    field=f'DommaschkPhysical{direction}{i:03}'
    package='BackwardTraceCache' if backward else 'PhysicalTraceCache'
    rate='(-1)' if backward else '1'
    angle='(-t)' if backward else 't'
    tag='back' if backward else 'fwd'
    bracket=f'DommaschkMirrorBracket{i:03}'
    name='DommaschkPhysicalMirrorHit'+('Backward' if backward else '')+f'{i:03}'
    height=str(i==324).lower()
    return name,f'''module
public import MirrorBracketCache.{bracket}
public import {package}.{field}

/-! # QA2R field line reaches the mirror height from an admissible local entry -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorTubeCrossing {field}
set_option linter.style.longLine false

/-- Every admissible slab entry yields a true field-line segment with an interior mirror-height hit. -/
theorem hit_from_entry {{x : Plane}} (hx : x ∈ stateSet previous) :
    ∃ y : ℝ → Plane, y ({i}/64) = x ∧ y ({i+1}/64) ∈ stateSet (next row) ∧
      (∀ t : ℝ, t ∈ Set.Icc ({i}/64) ({i+1}/64) →
        HasDerivWithinAt y (DommaschkJacobian.euclideanFlow 0 {rate} t (y t))
          (Set.Icc ({i}/64) ({i+1}/64)) t ∧ y t ∈ (physicalSlab previous row ({i}/64)).tube t) ∧
      ∃ t : ℝ, t ∈ Set.Ioo ({i}/64) ({i+1}/64) ∧ strength {angle} (y t) = DommaschkFirstMirrorLaunchSign.height {height} := by
  obtain ⟨y,hs,he,h⟩ := physical_step.solve x hx
  have end_time : (physicalSlab previous row ({i}/64)).stop = ({i+1}/64 : ℝ) := by
    change ({i}/64:ℝ) + 1/64 = _
    norm_num
  have start_time : (physicalSlab previous row ({i}/64)).start = ({i}/64 : ℝ) := rfl
  rw [end_time] at he
  rw [start_time,end_time] at h
  refine ⟨y,hs,he,h,?_⟩
  simpa using {bracket}.{tag}_hit (fun t ht => (h t ht).1.continuousWithinAt)
    (fun t ht => (h t ht).2)

end PlasmaLean.Design.{name}
'''


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--physical',required=True,type=Path)
    p.add_argument('--brackets',required=True,type=Path)
    p.add_argument('--index',choices=(316,324),type=int,default=316)
    p.add_argument('--output',type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/mirror-signs')
    a=p.parse_args()
    phys=json.loads(a.physical.read_text())
    if phys['packet_sha256']!=digest(RECORD):
        raise ValueError('physical row uses a different witness')
    backward=phys.get('direction')==-1
    if backward:
        if phys.get('row')!=a.index:
            raise ValueError('expected the single backward row for this bracket')
        f=phys
        fo,=map(Path,phys['import_paths'])
        package='BackwardTraceCache'
    else:
        f,=(r for r in phys['rows'] if r['index']==a.index and r['direction']==1)
        fo=Path(phys['imports'])
        package='PhysicalTraceCache'
    br,=(r for r in json.loads(a.brackets.read_text())['brackets']
         if r['module']==f'DommaschkMirrorBracket{a.index:03}')
    bp=list(map(Path,br['import_paths']))
    field=(fo/package/(f['module']+'.olean')).resolve(strict=True)
    fr=admitted(field.parent.parent,f['module'],f['key'])
    rr=admitted(bp[0],br['module'],br['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version=lake('lean','--version')
    if 'lean_version' in phys and version!=phys['lean_version']:
        raise ValueError('compiled physical row has different Lean version')
    a.lean=str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path=lake('printenv','LEAN_PATH')
    name,src=source(a.index,backward)
    root,r=compile_modules(a.cache.resolve()/name,[(name,src,['hit_from_entry'])],[*bp,fo],
                           [version,fr['key'],rr['key']],a,'PhysicalMirrorCache')
    out={k:v for k,v in r.items() if k!='artifacts'}
    out.update(import_paths=[str(root),*map(str,bp),str(fo)],index=a.index,
               direction=-1 if backward else 1,bracket_key=rr['key'],physical_key=fr['key'])
    if a.output:
        save(a.output,out)
    print(json.dumps(out))
