"""Integrate the checked polynomial on every real row of each signed outer group."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_grouped_action_polynomials import PACKAGE as MODELS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN,ROOT,digest,save
from verify_secondary_action_cover import BAND,BAND_MODULE,header
from verify_signed_mirror_passage import merge_import_roots


PACKAGE='ActionPolynomialShellCache'


def source(rec):
    a,b=rec['start'],rec['stop']
    mod=rec['module']
    rows=f'DommaschkGroupedProfile{a:03}To{b:03}Rows' if 'group' in rec else mod
    name=f'DommaschkQ0R478ActionShell{a:03}To{b:03}'
    src=header(name,['PlasmaLean.Design.DommaschkLowerActionPath','PlasmaLean.Certificates.ActionFloorShells',
                     MODELS+'.'+mod,BAND+'.'+BAND_MODULE])
    src+=f'''
open DommaschkPhysicalActionPanel DommaschkPairedActionProfiles
open Certificates Certificates.PolynomialActionFloor
abbrev mass : ℝ := {F(rec['signed_mass'])/2}
def integrand (y : ℝ → Plane) (q : ℝ) := density y q * Real.sqrt (2*({mod}.height-field y q))
'''
    for tag,branch,part,clock in [('fwd','fwd','1','t'),('back','back','2','(-t)')]:
        src+=f'''
private theorem {tag}_on {{y : ℝ → Plane}} (tracked : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {b} y)
    (t : ℝ) (ht : t ∈ Icc ({a}/64:ℝ) ({b}/64)) :
    QPoly.eval {mod}.proposed.poly ({mod}.groupClock t) ≤ integrand y {clock} := by
'''
        for i in range(a,b):
            src+=f'''  have point{i} (h : t ∈ Icc ({i}/64:ℝ) ({i+1}/64)) :
      QPoly.eval {mod}.proposed.poly ({mod}.groupClock t) ≤ integrand y {clock} := by
    have hi : {i} < {BAND_MODULE}.{branch}Rows.length := by change {i}<327; norm_num
    obtain ⟨prev,tube⟩ := tracked.{part} {i} (by norm_num) hi
    have same : {BAND_MODULE}.{branch}Rows[{i}] = {rows}.{tag}Outer{i:03} := by with_unfolding_all rfl
    rw [same] at tube
    have covered : y {clock} ∈ (physicalSlab prev {rows}.{tag}Outer{i:03} ({i}/64)).tube t := by
      have h' : t ∈ Icc ((({i}:ℕ):ℝ)/64) (((({i}:ℕ):ℝ)+1)/64) := by convert h using 1; norm_num
      simpa only [Bool.false_eq_true,↓reduceIte,Nat.cast_ofNat] using tube t h'
    exact {mod}.{tag}{i:03} h covered
'''
        for i in range(a,b-1):
            src+=f'  by_cases h{i} : t ≤ ({i+1}:ℝ)/64\n  · exact point{i} ⟨by linarith [ht.1],h{i}⟩\n'
        src+=f'  exact point{b-1} ⟨by linarith [ht.1],ht.2⟩\n'
    src+=f'''
theorem shell {{y : ℝ → Plane}} (track : Tracks {BAND_MODULE}.fwdRows {BAND_MODULE}.backRows {b} y)
    (cont : ContinuousOn (integrand y) (Icc (-{b}/64:ℝ) ({b}/64))) :
    Shell (integrand y) ({a}/64) ({b}/64) mass := by
  apply shell_of_bounds (by norm_num) (by norm_num)
    (by simpa only [neg_div] using cont)
    ((QPoly.continuous_eval {mod}.proposed.poly).comp (by unfold {mod}.groupClock; fun_prop))
    {mod}.integral
  exact fun t ht => ⟨fwd_on track t ht,back_on track t ht⟩
end PlasmaLean.Design.{name}
'''
    return name,src,['shell']


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--band',required=True,type=Path)
    p.add_argument('--models',required=True,nargs='+',type=Path)
    p.add_argument('--spans',type=int,nargs='*')
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/action-polynomial-shells')
    a=p.parse_args()
    env(a)
    b=json.loads(a.band.read_text())
    if b['module']!=BAND_MODULE:
        p.error('expected the 327-row second-radius mirror branch')
    band=list(map(Path,b['import_paths']))
    admitted(band[0],b['module'],b['key'])
    models={}
    for path in a.models:
        for key,r in json.loads(path.read_text()).items():
            i=int(key)
            if i in models or r['start']!=i:
                p.error('expected one signed model receipt per group')
            models[i]=r
    selected=sorted(models) if a.spans is None else a.spans
    (a.cache/'rows').mkdir(parents=True,exist_ok=True)
    result={}
    for i in selected:
        r=models[i]
        checksum=r['packets'][1] if 'group' in r else r['packet_sha256']
        if checksum!=b['packet_sha256']:
            p.error('model and trajectory use different outer signed witnesses')
        roots=list(map(Path,r['import_paths']))
        admitted(roots[0],r['module'],r['key'])
        keys=[a.version,b['key'],r['key'],digest(DESIGN.parent/'Certificates/ActionFloorShells.trace')]
        overlay=merge_import_roots(a.cache,[*roots,*band],keys)
        decl=source(r)
        base,rec=compile_modules(a.cache/decl[0],[decl],[overlay],keys,a,PACKAGE)
        out={k:rec[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
        out.update(start=i,stop=r['stop'],signed_mass=r['signed_mass'],model=r['key'],packet_sha256=checksum,
                   import_paths=list(map(str,[base,overlay])))
        save(a.cache/'rows'/f'{i:03}.json',out)
        result[i]=out
        save(a.output,result)
        print(decl[0],rec['key'],flush=True)


if __name__=='__main__':
    main()
