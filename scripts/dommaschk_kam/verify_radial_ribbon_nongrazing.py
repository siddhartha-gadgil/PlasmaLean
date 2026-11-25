"""Join the four complete signed ribbon first-mirror implications into one finite family."""
import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def source(modules):
    name='DommaschkRadialRibbonNoGrazingFamily'
    src=('module\npublic import PlasmaLean.Design.DommaschkRibbonGrazingAlternative\n'
         'public import PlasmaLean.Design.DommaschkRadialSectionAction\n')
    src+=''.join('public import RadialRibbonNoGrazingCache.'+m+'\n' for m in modules)
    src+=f'''
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkLowerActionPath
open DommaschkRadialFamilyContinuity DommaschkRibbonFirstMirrors
open Kinetic.MirrorActionEnvelope DommaschkMirrorTubeCrossing DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 65536
set_option linter.all false
'''
    for clock in ('forward','backward'):
        src+=f'def {clock}Rows (k : Fin 4) : List Step :=\n  match k with\n'
        for k in range(4):
            src+=f'  | {k if k<3 else "_"} => DommaschkRadialRibbonRows{k}.{clock}Rows\n'
    src+='''
theorem on_tubes (k : Fin 4) {y : ℝ → Plane} (closed : Enclosed y (-capClock) capClock)
    (tracked : Tracks (forwardRows k) (backwardRows k) 332 y) : NoGrazing y := by
  fin_cases k
'''
    for m in modules:
        src+=f'  · exact {m}.on_original_tubes closed tracked\n'
    src+='''
theorem upper_caps (k : Fin 4) {y : ℝ → Plane} (tr : Tracks (forwardRows k) (backwardRows k) 332 y) :
    (height true : ℝ) < strength (-capClock) (y (-capClock)) ∧
    (height true : ℝ) < strength capClock (y capClock) := by
  constructor
'''
    for clock,back,proj in [('backward','true',2),('forward','false',1)]:
        src+=f'''  · have count : ({clock}Rows k).length = 340 := by
      fin_cases k
'''
        for j in range(4):
            src+=f'      · exact DommaschkRadialRibbonRows{j}.{clock}_count\n'
        src+=f'''    have hi : 330 < ({clock}Rows k).length := by omega
    obtain ⟨prev,h⟩ := tr.{proj} 330 (by omega) hi
    have x := h capClock (by norm_num [capClock])
    have row : ({clock}Rows k)[330]'hi = DommaschkRadialRibbonUpperCaps.row {back} k := by
      fin_cases k <;> with_unfolding_all rfl
    rw [row] at x
    exact DommaschkRadialRibbonUpperCaps.above k {back} x
'''
    src+='''
theorem excludes_grazing (k : Fin 4) {y : ℝ → Plane} (closed : Enclosed y (-capClock) capClock)
    (tracked : Tracks (forwardRows k) (backwardRows k) 332 y) {l r : ℝ}
    (well : LaunchWell (fun t => strength t (y t)) 0 (height true) l r) :
    ¬(IsLocalMax (fun t => strength t (y t)) l ∨ IsLocalMax (fun t => strength t (y t)) r) :=
  (on_tubes k closed tracked).excludes_localMax well

theorem signs_and_simple (k : Fin 4) {y : ℝ → Plane} (closed : Enclosed y (-capClock) capClock)
    (tracked : Tracks (forwardRows k) (backwardRows k) 332 y) :
    DommaschkRadialSectionAction.Signs y ∧ DommaschkRadialSectionAction.Simple y := by
  have actual := on_tubes k closed tracked
  obtain ⟨back,front⟩ := upper_caps k tracked
  have levelEq : DommaschkNativeWellAction.level = (height true : ℝ) := by
    norm_num [DommaschkNativeWellAction.level,height]
  have signs : DommaschkRadialSectionAction.Signs y := by
    constructor
    · simpa only [levelEq,DommaschkNativeWellAction.field] using actual.birth
    · simpa only [levelEq,DommaschkNativeWellAction.field] using back
    · simpa only [levelEq,DommaschkNativeWellAction.field] using front
  refine ⟨signs,?_⟩
  intro l r well
  rw [levelEq] at well
  obtain ⟨left,right⟩ := actual.well_slopes well
  exact ⟨left.ne,right.ne'⟩
'''
    return name,src+f'end PlasmaLean.Design.{name}\n',[
        'on_tubes','upper_caps','excludes_grazing','signs_and_simple']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ribbon',type=Path,required=True)
    p.add_argument('--tiles',type=Path,nargs='+',required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/radial-ribbon-orientation')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    original=digest(a.ribbon)
    by_tile={}
    for f in a.tiles:
        d=json.loads(f.read_text())
        if d['ribbon']!=original:
            p.error('tile proof is not about the requested original archive')
        for tile,data in d['tiles'].items():
            k=int(tile)
            r=data.get('physical')
            if r is None or k in by_tile or r['module']!='DommaschkRadialRibbonNoGrazing'+tile:
                p.error('one accepted complete signed implication per tile is required')
            by_tile[k]=r
    if set(by_tile)!=set(range(4)):
        p.error('the full radial bracket requires all four physical tiles')
    parents=[by_tile[k] for k in range(4)]
    roots=[]
    for r in parents:
        root,*imports=map(Path,r['import_paths'])
        marker=admitted(root,r['module'],r['key'])
        if f"PlasmaLean.Design.{r['module']}.on_original_tubes" not in marker['theorems']:
            p.error('missing the physical signed tube theorem')
        roots.extend([root,*imports])
    env(a)
    keys=[r['key'] for r in parents]
    imports=merge_import_roots(a.cache,roots,keys)
    item=source([r['module'] for r in parents])
    root,rec=compile_modules(a.cache/item[0],[item],[imports],
          [original,keys,a.version,digest(DESIGN/'DommaschkRibbonGrazingAlternative.trace'),
           digest(DESIGN/'DommaschkRadialSectionAction.trace')],
          a,'RadialRibbonNoGrazingFamilyCache')
    output={k:rec[k] for k in ('module','key','axioms','theorems','wall_seconds','peak_rss_kib')}
    output.update(ribbon=original,parents=keys,import_paths=[str(root),str(imports)])
    save(a.output,output)
    print(rec['module'],rec['key'],flush=True)


if __name__=='__main__':
    main()
