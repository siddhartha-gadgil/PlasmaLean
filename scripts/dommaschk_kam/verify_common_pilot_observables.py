"""Place the calibrated 391-row pilot path and all secondary passages on one embedded pair."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_action_flight_floor import NAME as FLOOR, WELL, CEILING
from verify_backward_physical_prefix import compile_modules
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def contact(index, prefix, slope):
    """The same physical row supplies both its crossing and its strict outward slope."""
    row = f'path (by norm_num) (by change {index} < 326; norm_num) (by change {index} < 326; norm_num) rfl rfl'
    return f'''DommaschkSignedMirrorSlope.first_transverse
    (DommaschkSignedMirrorBrackets.first{index} {row}
      (path.below_on (k := {index}) (by norm_num) rfl rfl
        {prefix}.fwd_checked {prefix}.back_checked)) ({slope}.regular {row})'''


def source(counts):
    suffix = '_'.join(str(counts[e]) for e in ENDPOINTS)
    family = 'DommaschkCommonEndpointTraces'+suffix
    pilot = 'DommaschkPilotBirth'+suffix
    name = 'DommaschkCalibratedFamily'+suffix
    n = counts['q0r470']
    text = f'''module
public import PlasmaLean.Design.DommaschkCommonPilotObservables
public import PlasmaLean.Design.DommaschkFiniteRadialAction
public import BirthVariationCache.{pilot}
public import ActionFlightFloorCache.{FLOOR}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Set Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkSignedBirthApproach
open DommaschkFirstMirrorLaunchSign DommaschkSignedMirrorBand DommaschkMirrorBandPassage
open DommaschkNativeWellAction DommaschkActionFlightFloor DommaschkFiniteRadialAction
open DommaschkMirrorBandFlightIdentity DommaschkSignedTraceDensity DommaschkMirrorTubeCrossing
open DommaschkActionHeightInverse (ambient)
set_option maxRecDepth 20000

def Observed (φ : ℝ) (y : ℝ → Plane) : Prop :=
  Passage φ y ∧ FirstWellAction y ∧ TimeBounds φ y ∧ HeightScale y ∧
    (71 / 2500 < ambient y (height true) - ambient y (height false)) ∧ PairTest y

theorem on_326 {{φ x y}} (small : |φ| ≤ 1/2^19) (path : {WELL}.ActualPath x y) :
    Observed φ y := by
  have lower := {contact(316,'DommaschkSubmirror316Of326','DommaschkSignedSlope316')}
  have upper := {contact(324,'DommaschkUpperSubmirror324Of326','DommaschkSignedSlope324')}
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have action := {WELL}.on_path path ({WELL}.all_cells path) (by
    simpa only [{WELL}.level_eq] using upper)
  obtain ⟨⟨p,hp,ep,beforeP,_⟩,m,hm,em,beforeM,_⟩ := lower
  obtain ⟨⟨P,hP,eP,_⟩,M,hM,eM,_⟩ := upper
  have rates := {FLOOR}.all_slopes path
  have branches := DommaschkSignedMirrorBand.branches path (by norm_num) region
    ⟨⟨p,hp,ep,beforeP⟩,m,hm,em,beforeM⟩ ⟨⟨P,hP,eP⟩,M,hM,eM⟩ rates
  have pass := DommaschkMirrorBandPassage.on_path path (by norm_num)
    (small.trans (by norm_num)) region branches
  have short := {FLOOR}.shorter path
  have reg : ∀ t ∈ Icc (-bound) bound, DommaschkSignedTraceDomain.Region (y t) := by
    simpa only [bound, Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path short
      (by norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have under := short.below_on (k := 316) (by norm_num) rfl rfl
    DommaschkCoreSubmirror316Of325.fwd_checked DommaschkCoreSubmirror316Of325.back_checked
  have collar := DommaschkFullBandFlightBounds.on_path short pass reg rates
    (by simpa only [DommaschkFullBandFlightBounds.a, Nat.cast_ofNat, neg_div] using under)
  have high := DommaschkRowFlightBudget.complete collar reg ({CEILING}.central short)
  have times := join_bounds (of_passage path (by norm_num) region pass action) high
  have identity := DommaschkMirrorBandFlightIdentity.on_path short reg pass.2.1
  have scale := height_scale identity times
  have cy₀ : ContinuousOn y (Icc (-((325 : ℕ) : ℝ) / 64) (((325 : ℕ) : ℝ) / 64)) :=
    fun t ht => (short.ode t ht).continuousWithinAt
  have cy : ContinuousOn y (Icc (-bound) bound) := by
    simpa only [bound, Nat.cast_ofNat, neg_div] using cy₀
  have cf : ContinuousOn (profile y) (Icc (-bound) bound) := by
    simpa only [profile, one_mul] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7/8) (reg t ht).1.1)
  exact ⟨pass, action, times, scale, endpoint_width scale,
    pair_test identity times cf (continuousOn_density_region cy reg)⟩

theorem same_embedded_tori : DommaschkCommonPilotObservables.Common {family}.checkpoint Observed := by
  apply DommaschkCommonPilotObservables.of_paths {pilot}.physical_birth (by norm_num [{family}.checkpoint])
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  intro φ x y small path
  have pre := path.take_through (i := 325) (by change 325 < {n}; norm_num)
    (by change 325 < {n}; norm_num) (by change 325 < {n}; norm_num)
  apply on_326 small (x := x)
  with_unfolding_all exact pre

end PlasmaLean.Design.{name}
'''
    return name, text, ['on_326','same_embedded_tori']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--birth', type=Path, required=True)
    parser.add_argument('--flight', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/calibrated-common-family')
    args = parser.parse_args()
    birth, flight = [json.loads(p.read_text()) for p in (args.birth,args.flight)]
    counts = birth['lengths_each_direction']
    if (set(counts) != set(ENDPOINTS) or any(type(n) is not int or not 1 <= n <= 391
                                             for n in counts.values()) or counts['q0r470'] < 326):
        parser.error('requires eight authenticated passes and at least 326 pilot slabs')
    name, source_text, theorems = source(counts)
    pilot = 'DommaschkPilotBirth'+'_'.join(str(counts[e]) for e in ENDPOINTS)
    packet = digest(RECORD)
    if birth['module'] != pilot or flight['module'] != FLOOR or flight['packet_sha256'] != packet:
        parser.error('requires a checked common birth-tangent family and the original pilot floor')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    keys = [lake('lean','--version'), packet, digest(DESIGN/'DommaschkCommonPilotObservables.trace'),
            digest(DESIGN/'DommaschkFiniteRadialAction.trace')]
    imports = []
    for record in (birth, flight):
        roots = list(map(Path, record['import_paths']))
        admitted(roots[0],record['module'],record['key'])
        imports.extend(roots)
        keys.append(record['key'])
    overlay = merge_import_roots(args.cache,imports,keys)
    root, record = compile_modules(args.cache/name,[(name,source_text,theorems)],[overlay],
                                   keys,env,'CalibratedFamilyCache')
    report = {k:v for k,v in record.items() if k != 'artifacts'}
    report.update(lengths_each_direction=counts,birth_key=birth['key'],flight_key=flight['key'],
                  import_paths=list(map(str,[root,overlay])))
    save(args.output,report)
    print(name, record['key'],flush=True)


if __name__ == '__main__':
    main()
