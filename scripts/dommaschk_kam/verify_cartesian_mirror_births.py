"""Place every admitted pilot birth/height in the interior of the Cartesian regular-birth set."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save


NAME = 'DommaschkCartesianMirrorBirth325'
SOURCE = '''module
public import PlasmaLean.Design.DommaschkCartesianMirrorBirth
public import RegularMirrorBandCache.DommaschkRegularMirrorHeightBand325

/-! # A positive-volume set of true Cartesian QA2R regular mirror births -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.DommaschkCartesianMirrorBirth325
open Set MeasureTheory DommaschkSignedBirthApproach DommaschkFirstMirrorWell
open DommaschkCartesianMirrorBirth DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 16384

/-- The original torus-interpolated births for all admitted angles and every
height in the closed band lie in the ambient four-dimensional interior. -/
theorem from_birth : ThroughBirth (fun φ y => ∀ h ∈ Icc (height false : ℝ) (height true),
    (point y φ, h) ∈ interior regularBirths) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, every⟩ :=
    DommaschkRegularMirrorHeightBand325.from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ small => ?_⟩
  obtain ⟨y, start, x, path, band⟩ := every φ small
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  exact ⟨y, start, fun h hh => neighborhood path (by norm_num) region band.1
    (small.trans_lt (by norm_num)) hh⟩

/-- The regular births contain a nonempty open set of Cartesian position-height pairs. -/
theorem nonempty_interior : (interior regularBirths).Nonempty := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, every⟩ := from_birth
  obtain ⟨y, _, each⟩ := every 0 (by norm_num)
  exact ⟨(point y 0, height false), each _ ⟨le_rfl, by norm_num [height]⟩⟩

/-- Any law charging every nonempty open set assigns positive mass to the
interior of the physical regular-birth set. -/
theorem positive_mass (μ : Measure (Fields.Space × ℝ)) [Measure.IsOpenPosMeasure μ] :
    0 < μ (interior regularBirths) := isOpen_interior.measure_pos μ nonempty_interior

/-- In particular the physical regular births have strictly positive Cartesian
position-height Lebesgue volume. -/
theorem positive_volume : 0 < volume regularBirths :=
  (positive_mass volume).trans_le (measure_mono interior_subset)

end PlasmaLean.Design.DommaschkCartesianMirrorBirth325
'''


def verify_passage(name, source, theorems, dependency, package, cache, description):
    """Check an on-demand consequence of the original audited N-99 height-band passage."""
    p = argparse.ArgumentParser(description=description)
    p.add_argument('--passage', type=Path, required=True, help='the N-99 through-birth height-band report')
    p.add_argument('--cache', type=Path, default=ROOT/'.lake'/cache)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    report = json.loads(args.passage.read_text())
    parent = 'DommaschkRegularMirrorHeightBand325'
    packet = digest(RECORD)
    if report['module'] != parent or report['packet_sha256'] != packet:
        p.error('expected the complete phase-zero radius-0.470 physical height-band passage')
    roots = list(map(Path, report['import_paths']))
    admitted(roots[0], parent, report['key'])
    admitted(roots[1], 'DommaschkMirrorHeightBand325', report['band_key'])

    def lake(*cmd):
        return subprocess.check_output(['lake', 'env', *cmd], cwd=ROOT, text=True).strip()

    version = lake('lean', '--version')
    if version != report['lean_version']:
        p.error('the passage uses a different Lean version')
    args.lean = str(Path(lake('lean', '--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv', 'LEAN_PATH')
    declarations = [(name, source, theorems)]
    identity = [version, packet, report['key'], digest(DESIGN/(dependency+'.trace'))]
    root, proof = compile_modules(args.cache/name, declarations, roots, identity, args, package)
    result = {k:v for k,v in proof.items() if k != 'artifacts'}
    result.update(packet_sha256=packet, passage_key=report['key'], import_paths=list(map(str, [root, *roots])))
    save(args.output, result)
    print(name, result['key'], flush=True)


def main():
    verify_passage(NAME, SOURCE, ['from_birth', 'nonempty_interior', 'positive_mass', 'positive_volume'],
                   'DommaschkCartesianMirrorBirth', 'CartesianBirthCache', 'cartesian-mirror-birth', __doc__)


if __name__ == '__main__':
    main()
