"""Lift the nine signed slope proofs to the 326-row action path and bound each true flight."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


NAME = 'DommaschkActionFlightFloor326'
BAND = 'DommaschkMirrorHeightBand325'
WELL = 'DommaschkNativeFirstWellComplete326'
CEILING = 'DommaschkRowFlightBudget325'


def source():
    text = f'''module
public import PlasmaLean.Design.DommaschkActionFlightFloor
public import PlasmaLean.Design.DommaschkSignedTracePrefix
public import MirrorHeightBandBirthCache.{BAND}
public import NativeFirstWellCache.{WELL}
public import RowFlightBudgetCache.{CEILING}

/-! # All-height flight times and actions on the original 326-slab Q-16 birth path -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{NAME}
open Set Certificates.PositionFrameSlabs DommaschkFirstMirrorLaunchSign
open DommaschkSignedObservable DommaschkSignedBirthApproach DommaschkSignedMirrorBand
open DommaschkMirrorBandPassage DommaschkNativeWellAction DommaschkActionFlightFloor
open DommaschkMirrorTubeCrossing
set_option maxRecDepth 20000

theorem shorter {{x y}} (path : {WELL}.ActualPath x y) :
    Path 325 DommaschkPhysicalPrefix325.exitState DommaschkBackwardPrefix325.exitState
      DommaschkPhysicalPrefix325.rows DommaschkBackwardPrefix325.rows x y := by
  have restricted := path.take_through (i := 324) (by norm_num)
    (by change 324 < 326; norm_num) (by change 324 < 326; norm_num)
  with_unfolding_all exact restricted

theorem all_slopes {{x y}} (path : {WELL}.ActualPath x y) :
    Rates y (316 / 64) (325 / 64) (1 / 400) := {BAND}.all_slopes (shorter path)
theorem from_birth : ThroughBirth (fun φ y => ∃ x, {WELL}.ActualPath x y ∧
    Passage φ y ∧ FirstWellAction y ∧ TimeBounds φ y) := by
  apply from_birthWith {WELL}.from_birth (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  intro φ small x y path certificates
  obtain ⟨lower, upper, action⟩ := certificates
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  obtain ⟨⟨p, hp, ep, beforeP, _⟩, ⟨m, hm, em, beforeM, _⟩⟩ := lower
  obtain ⟨⟨P, hP, eP, _⟩, ⟨M, hM, eM, _⟩⟩ := upper
  have band := branches path (by norm_num) region
    ⟨⟨p,hp,ep,beforeP⟩,m,hm,em,beforeM⟩
    ⟨⟨P,hP,eP.trans {WELL}.level_eq.symm⟩,M,hM,eM.trans {WELL}.level_eq.symm⟩ (all_slopes path)
  have passage := DommaschkMirrorBandPassage.on_path path (by norm_num)
    (small.trans (by norm_num)) region band
  have short := shorter path
  have region325 : ∀ t ∈ Icc (-DommaschkFullBandFlightBounds.b) DommaschkFullBandFlightBounds.b,
      DommaschkSignedTraceDomain.Region (y t) := by
    intro t ht
    apply region t
    norm_num [DommaschkFullBandFlightBounds.b] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have under := short.below_on (k := 316) (by norm_num) rfl rfl
    DommaschkCoreSubmirror316Of325.fwd_checked DommaschkCoreSubmirror316Of325.back_checked
  have collar := DommaschkFullBandFlightBounds.on_path short passage region325 (all_slopes path)
    (by simpa only [DommaschkFullBandFlightBounds.a, Nat.cast_ofNat, neg_div] using under)
  have high := DommaschkRowFlightBudget.complete collar region325 ({CEILING}.central short)
  exact ⟨x, path, passage, action, join_bounds
    (of_passage path (by norm_num) region passage action) high⟩

end PlasmaLean.Design.{NAME}
'''
    return NAME, text, ['shorter', 'all_slopes', 'from_birth']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--band', type=Path, required=True, help='N-99 assembly with the nine slopes')
    parser.add_argument('--well', type=Path, required=True, help='N-101 complete first-well action')
    parser.add_argument('--ceiling', type=Path, required=True, help='316 integrated row budgets')
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/action-flight-floor')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    packet = digest(RECORD)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd], cwd=ROOT, text=True).strip()
    version = lake('lean','--version')
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv','LEAN_PATH'))
    keys = [version,packet,digest(DESIGN/'DommaschkActionFlightFloor.trace'),
            digest(DESIGN/'DommaschkSignedTracePrefix.trace')]
    imports = []
    for path, expected in [(args.band,BAND),(args.well,WELL),(args.ceiling,CEILING)]:
        report = json.loads(path.read_text())
        if report['module'] != expected or report['packet_sha256'] != packet:
            raise ValueError(f'expected the pilot certificate {expected} in {path}')
        if expected == WELL and not report['complete']:
            raise ValueError('requires the unconditional N-101 action cap')
        roots = [Path(p) for p in report['import_paths']]
        admitted(roots[0],expected,report['key'])
        imports.extend(roots)
        keys.append(report['key'])
    overlay = merge_import_roots(args.cache,imports,keys)
    base,record = compile_modules(args.cache/NAME,[source()],[overlay],keys,env,'ActionFlightFloorCache')
    result = {k:v for k,v in record.items() if k != 'artifacts'}
    result.update(packet_sha256=packet,band_key=keys[-3],well_key=keys[-2],ceiling_key=keys[-1],
                  floor='9006443340496896/163793158879589',
                  upper_height_floor='9468238224162816/163793158879589',ceiling='264',
                  import_paths=[str(base),str(overlay)])
    save(args.output,result)
    print(NAME,record['key'],flush=True)


if __name__ == '__main__':
    main()
