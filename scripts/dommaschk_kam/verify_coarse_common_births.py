"""Place verified opposite-section action cells on a single pair of embedded QA2R tori."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_signed_mirror_passage import merge_import_roots


LABELS=('q1r456','q1r464','q1r509','q1r517')


def source(rows):
    name='DommaschkCoarseOppositeCommon'+''.join(e[-3:] for e,_ in rows)
    src='module\npublic import PlasmaLean.Design.DommaschkKamEmbedded\n'
    src+=''.join(f'public import CoarseActionBirthCache.{m}\n' for _,m in rows)
    claims=' ∧\n      '.join(f'AtBirth .{e} uC zC uA zA φ {m}.Evidence' for e,m in rows)
    proofs=',\n    '.join(f'{m}.from_entry (entries .{e} (by simpa [azimuth,MirrorEndpoint.opposite,MirrorEndpoint.width] using small))' for e,m in rows)
    src+=f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch DommaschkLowerActionPath DommaschkKamC KamNewton Contract Forms
open Fields.VacuumBoozer Theory.KAM WEll1Z2
set_option linter.style.longLine false

theorem common :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ-Real.pi/2| ≤ 1/2^20 →
      {claims} := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,nested,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,nested,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),fun φ small => ?_⟩
  have entries (e : MirrorEndpoint) (h : |φ-azimuth e.opposite| ≤ e.width) : SectionEntry e uC zC uA zA φ :=
    transfer_to_start (by simpa using cC) (by simpa using cA) e h
  exact {('⟨'+proofs+'⟩') if len(rows)>1 else proofs}
end PlasmaLean.Design.{name}
'''
    return name,src,['common']


def check(a):
    receipts=json.loads(a.family.read_text())
    available={r['endpoint']:r for r in receipts['completed']}
    keys=[digest(DESIGN/'DommaschkLowerActionPath.trace'),digest(DESIGN/'DommaschkKamEmbedded.trace')]
    paths=[]
    rows=[]
    for e in a.endpoints:
        rec=json.loads(Path(available[e]['source']).read_text())
        n=rec['signed_length']
        m=f'DommaschkCoarseBirth{e.upper()}N12Of{n:03}'
        if (rec['module'],rec['endpoint'],rec['key'],rec['chronological_cells'])!=(m,e,available[e]['birth'],96):
            raise ValueError(f'inconsistent signed physical passage for {e}')
        roots=list(map(Path,rec['import_paths']))
        admitted(roots[0],m,rec['key'])
        paths.extend(roots)
        keys.append(rec['key'])
        rows.append((e,m))
    env(a)
    keys.append(a.version)
    overlay=merge_import_roots(a.cache,paths,keys)
    decl=source(rows)
    base,r=compile_modules(a.cache/decl[0],[decl],[overlay],keys,a,'CoarseCommonBirthCache')
    out={k:r[k] for k in ['module','key','axioms','theorems']}
    out.update(endpoints=a.endpoints,independent_panels=24*len(rows),chronological_cells=96*len(rows),
               import_paths=list(map(str,[base,overlay])))
    save(a.output,out)
    print(out['module'],out['key'],flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--family',type=Path,required=True)
    p.add_argument('--endpoints',nargs='+',choices=LABELS,default=list(LABELS))
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/coarse-common-birth')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if len(set(a.endpoints))!=len(a.endpoints):
        p.error('use each physical launch once')
    check(a)
