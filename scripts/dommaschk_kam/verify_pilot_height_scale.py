"""Join the sharp height calibration and finite radial comparison to the actual pilot path."""
import argparse
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_action_flight_floor import NAME as FLOOR
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


NAME = 'DommaschkFiniteRadialAction326'
SOURCE = f'''module
public import PlasmaLean.Design.DommaschkFiniteRadialAction
public import ActionFlightFloorCache.{FLOOR}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{NAME}
open Set DommaschkSignedBirthApproach DommaschkFiniteRadialAction DommaschkActionFlightFloor
open DommaschkMirrorBandPassage DommaschkMirrorBandFlightIdentity DommaschkFirstMirrorLaunchSign
open DommaschkSignedTraceDomain DommaschkSignedTraceDensity DommaschkMirrorTubeCrossing
open DommaschkActionHeightInverse (ambient)
set_option maxRecDepth 20000

theorem from_birth : ThroughBirth (fun φ y => Passage φ y ∧ TimeBounds φ y ∧ HeightScale y ∧
    (71 / 2500 < ambient y (height true) - ambient y (height false)) ∧ PairTest y) := by
  obtain ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, each⟩ := {FLOOR}.from_birth
  refine ⟨uC, zC, uA, zA, R, z, C, A, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, pass, _, times⟩ := each φ small
  have short := {FLOOR}.shorter path
  have reg : ∀ t ∈ Icc (-bound) bound, Region (y t) := by
    simpa only [bound, Nat.cast_ofNat, neg_div] using DommaschkSignedTraceDomain.on_path short
      (by norm_num) (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have identity := DommaschkMirrorBandFlightIdentity.on_path short reg pass.2.1
  have scale := height_scale identity times
  have cy₀ : ContinuousOn y (Icc (-((325 : ℕ) : ℝ) / 64) (((325 : ℕ) : ℝ) / 64)) :=
    fun t ht => (short.ode t ht).continuousWithinAt
  have cy : ContinuousOn y (Icc (-bound) bound) := by simpa only [bound, Nat.cast_ofNat, neg_div] using cy₀
  have cf : ContinuousOn (profile y) (Icc (-bound) bound) := by
    simpa only [profile, one_mul] using continuousOn_strength cy 1
      (fun t ht => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) (reg t ht).1.1)
  exact ⟨y, start, pass, times, scale, endpoint_width scale,
    pair_test identity times cf (continuousOn_density_region cy reg)⟩

end PlasmaLean.Design.{NAME}
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--flight', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/pilot-height-scale')
    args = parser.parse_args()
    parent = json.loads(args.flight.read_text())
    packet = digest(RECORD)
    if parent['module'] != FLOOR or parent['packet_sha256'] != packet:
        parser.error('requires the original pilot joint first-well flight certificate')
    roots = [Path(p) for p in parent['import_paths']]
    admitted(roots[0], FLOOR, parent['key'])

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    version = lake('lean', '--version')
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix'))/'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    keys = [packet, version, parent['key'], digest(DESIGN/'DommaschkFiniteRadialAction.trace')]
    root, record = compile_modules(args.cache/NAME, [(NAME, SOURCE, ['from_birth'])], roots,
                                   keys, env, 'FiniteRadialActionCache')
    report = {k:v for k,v in record.items() if k != 'artifacts'}
    report.update(flight_key=parent['key'], packet_sha256=packet, lean_version=version,
                  import_paths=list(map(str, [root,*roots])))
    save(args.output, report)
    print(NAME, record['key'], flush=True)


if __name__ == '__main__':
    main()
