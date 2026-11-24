"""Attach the first signed radial comparison to two original births on the same embedded tori."""
import argparse
import json
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkPairedActionBirth000'
SRC = '''module
public import PlasmaLean.Design.DommaschkPairedActionBirth
public import PairedProfileCache.DommaschkPairedActionProfile000
public import SignedEndpointCache.DommaschkSignedLaunchesAll

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkPairedActionBirth000
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkEndpointSignedTrace
open DommaschkPairedActionProfiles DommaschkPairedActionBirth DommaschkPairedActionProfile000
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2 Set
open DommaschkSignedLaunchesAll
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option linter.style.longLine false

abbrev cartSpeed (y : ℝ → Plane) (t : ℝ) :=
  ‖deriv (fun a => Contract.cylPoint (y a 0) a (y a 1)) t‖

def Comparison (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  ∃ i o : ℝ → Plane, Launch .q0r470 uC zC uA zA φ i ∧ Launch .q0r478 uC zC uA zA φ o ∧
    (∀ t ∈ window, Compared t (i t) (o t)) ∧
    (∀ t ∈ Ioo (-halfWidth) halfWidth, 3999 / 4000 * cartSpeed i t ≤ cartSpeed o t)

def Passage (e : MirrorEndpoint) (uC zC uA zA : FA) (φ : ℝ) : Prop :=
  FromBirth e uC zC uA zA φ halfWidth (stateSet (next (fw e))) (stateSet (next (bw e)))
    (physicalSlabs e.start 0 [fw e]) (physicalSlabs e.start 0 [bw e])

theorem from_passages {uC zC uA zA : FA} {φ : ℝ} (room : |φ| ≤ halfWidth)
    (birthi : Passage .q0r470 uC zC uA zA φ) (birtho : Passage .q0r478 uC zC uA zA φ) :
    Comparison uC zC uA zA φ := by
'''


def source():
    out = SRC
    for radius, tag, letter in [(470, 'inner', 'i'), (478, 'outer', 'o')]:
        e = f'.q0r{radius}'
        mod = 'DommaschkSignedLaunchesAll'
        out += f'''  obtain ⟨{letter}, path{letter}, {letter}fw, {letter}b⟩ := from_launch
    (e := {e}) (f := {mod}.fw {e}) (b := {mod}.bw {e}) rfl room birth{letter}
    (by
      intro prev t x ht hx
      have h := {tag}_forward_regular (prev := prev) (x := x) (t := t)
        (by simpa only [zero_div,halfWidth] using ht)
        (by rw [zero_div]; with_unfolding_all exact hx)
      simpa only [Bool.false_eq_true,↓reduceIte] using h)
    (by
      intro prev t x ht hx
      have h := {tag}_backward_regular (prev := prev) (x := x) (t := t)
        (by simpa only [zero_div,halfWidth] using ht)
        (by rw [zero_div]; with_unfolding_all exact hx)
      simpa only [↓reduceIte] using h)
'''
    out += '''  have both (t : ℝ) (ht : t ∈ window) : Compared t (i t) (o t) := by
    by_cases pos : 0 ≤ t
    · have k : t ∈ Icc 0 halfWidth := ⟨pos,ht.2⟩
      apply DommaschkPairedActionProfile000.forward (by simpa only [zero_div,halfWidth] using k)
      · rw [zero_div]; with_unfolding_all exact ifw t k
      · rw [zero_div]; with_unfolding_all exact ofw t k
    · have k : -t ∈ Icc 0 halfWidth := ⟨by linarith,by linarith [ht.1]⟩
      have back : Compared (-(-t)) (i (-(-t))) (o (-(-t))) := by
        apply DommaschkPairedActionProfile000.backward (by simpa only [zero_div,halfWidth] using k)
        · rw [zero_div]; with_unfolding_all exact ib (-t) k
        · rw [zero_div]; with_unfolding_all exact ob (-t) k
      simpa only [neg_neg] using back
  refine ⟨i,o,pathi,patho,both,fun t ht => ?_⟩
  change 3999 / 4000 * ‖deriv _ t‖ ≤ ‖deriv _ t‖
  rw [pathi.weight ht, patho.weight ht]
  exact (both t (Ioo_subset_Icc_self ht)).2.2.2

theorem from_entries {uC zC uA zA : FA} {φ : ℝ} (room : |φ| ≤ halfWidth)
    (ei : SectionEntry .q0r470 uC zC uA zA φ) (eo : SectionEntry .q0r478 uC zC uA zA φ) :
    Comparison uC zC uA zA φ := by
  apply from_passages room
'''
    for entry, lim, fwd, back in [
            ('ei','pilotLimits','DommaschkPhysicalFirstStep','DommaschkPhysicalBackwardFirstStep'),
            ('eo','allLimits','DommaschkPhysicalQ0R478Forward000','DommaschkPhysicalQ0R478Back000')]:
        out += f'  · apply DommaschkEndpointSignedTrace.from_entry {entry}\n'
        for row, mod in [('fw',fwd),('bw',back)]:
            proved = ('ball_field_bounds' if entry == 'ei' else 'launch_field_bounds') if row=='fw' else 'field_bounds'
            extra = ''
            if entry == 'ei':
                extra = (', MirrorEndpoint.pilot_starts.1,DommaschkPhysicalFirstStep.seed' if row=='fw'
                         else ', MirrorEndpoint.pilot_starts.2,DommaschkJacobianBackward000.seed')
            out += f'''    · apply first_chain (lim := {lim})
      · with_unfolding_all exact {mod}.checked
      · simpa [{row},azimuth,MirrorEndpoint.opposite{extra}] using {mod}.{proved}
'''
    out += '''
/-- Both named embedded field tori and both interpolated radii use identical witnesses. -/
theorem from_embedded_tori :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ| ≤ 1 / 2 ^ 19 → Comparison uC zC uA zA φ := by
  obtain ⟨sC,sA,R₀,z₀,ΘC,ΘA,eC,eA,iC,iA,hn,_,_,emb,_,_,_,_,_,_,_,_,uC,zC,uA,zA,
    rfl,rfl,cC,cA⟩ := DommaschkKamEmbedded.dommaschk_Q16_embedded
  rw [eC] at iC
  rw [eA] at iA
  have both := (emb 1 (by norm_num)).embedded
  refine ⟨uC,zC,uA,zA,R₀,z₀,ΘC,ΘA,iC,iA,hn,both (surfaceC uC zC) (by simp),
    both (DommaschkKamA.surfaceA uA zA) (by simp),fun φ small => ?_⟩
  apply from_entries (small.trans (by norm_num [halfWidth]))
  all_goals
    apply transfer_to_start (by simpa using cC) (by simpa using cA)
    simpa [azimuth,MirrorEndpoint.opposite,MirrorEndpoint.width] using small

end PlasmaLean.Design.DommaschkPairedActionBirth000
'''
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profiles', type=Path, required=True)
    p.add_argument('--launches', type=Path, required=True)
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/paired-action-births')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    profiles, births = (json.loads(f.read_text()) for f in (a.profiles, a.launches))
    packets = [digest(load(r)[1]) for r in (470, 478)]
    if (profiles['row'] != 0 or profiles['packets'] != packets
            or profiles['module'] != 'DommaschkPairedActionProfile000'
            or births['module'] != 'DommaschkSignedLaunchesAll'):
        p.error('expected the first row of the original 470/478 pair and the common eight-launch receipt')
    keys, roots = [], []
    for report in [profiles,births]:
        paths = list(map(Path,report['import_paths']))
        admitted(paths[0],report['module'],report['key'])
        keys.append(report['key'])
        roots.extend(paths)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    cache = a.cache.resolve()
    overlay = merge_import_roots(cache,roots,keys)
    theorems = ['from_passages','from_entries','from_embedded_tori']
    full, record = compile_modules(cache/NAME, [(NAME,source(),theorems)],[overlay],
                      [lake('lean','--version'),*keys,packets,digest(DESIGN/'DommaschkPairedActionBirth.trace')],
                      a,'PairedBirthProfileCache')
    out = {k:record[k] for k in ('module','key','theorems','axioms','wall_seconds','peak_rss_kib')}
    out.update(slab=0,parents=keys,packets=packets,import_paths=[str(full),str(overlay)])
    save(a.output,out)
    print(NAME,record['key'],flush=True)


if __name__ == '__main__':
    main()
