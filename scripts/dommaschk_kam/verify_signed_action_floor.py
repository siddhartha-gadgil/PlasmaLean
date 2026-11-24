"""Certify the true upper-height Cartesian action floor on a signed submirror prefix."""

import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, RECORD, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def generate(n, k):
    name = f'DommaschkSignedActionFloor{k:03}Of{n:03}'
    forward = f'DommaschkPhysicalPrefix{n:03}'
    backward = f'DommaschkBackwardPrefix{n:03}'
    signs = f'DommaschkSubmirror{k:03}Of{n:03}'
    bound = Fraction(7 * k, 8000)
    source = f'''module

public import PlasmaLean.Design.DommaschkSignedActionFloor
public import SubmirrorPrefixCache.{signs}

/-! # The true finite-window action at the upper mirror height of the pilot's original Q-16 births -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorTubeCrossing DommaschkSignedObservable DommaschkSignedActionFloor
open DommaschkFirstMirrorLaunchSign Kinetic.CylindricalActionSensitivity
open Certificates.PositionFrameSlabs Set MeasureTheory

set_option maxRecDepth 16384

/-- The physical density is integrable and its action exceeds the stated rational floor. -/
def ActionOn (y : ℝ → Plane) : Prop :=
  IntervalIntegrable (integrand (height true) y) volume (-({k} : ℝ) / 64) ({k} / 64) ∧
    {bound.numerator} / {bound.denominator} <
      physicalAction (fun t => y t 0) (fun t => y t 1) (fun t => strength t (y t))
        (-({k} : ℝ) / 64) ({k} / 64) (height true)

/-- The action floor holds on every signed solution in these same authenticated tubes. -/
theorem on_path {{x : Plane}} {{y : ℝ → Plane}}
    (path : Path {n} {forward}.exitState {backward}.exitState
      {forward}.rows {backward}.rows x y) : ActionOn y := by
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have sign := path.below_on (k := {k}) (by norm_num) rfl rfl {signs}.fwd_checked
    {signs}.back_checked
  have sub : Icc (-({k} : ℝ) / 64) ({k} / 64) ⊆ Icc (-({n} : ℝ) / 64) ({n} / 64) :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have bounds := strict_floor (a := -({k} : ℝ) / 64) (b := {k} / 64) (by norm_num)
    (fun t ht => (path.ode t (sub ht)).mono sub) (fun t ht => region t (sub ht)) sign
  unfold ActionOn
  norm_num at bounds ⊢
  exact bounds

/-- Every Q-16 birth in the pilot's section collar has a single physical path with this floor. -/
theorem from_birth :
    BirthWith (fun x => ∃ y, Path {n} {forward}.exitState {backward}.exitState
      {forward}.rows {backward}.rows x y ∧ ActionOn y) := by
  exact birth_with DommaschkPairedPrefix{n:03}.exists_nested_paired (fun _ _ => on_path)

end PlasmaLean.Design.{name}
'''
    return name, source, ['on_path', 'from_birth']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired', type=Path, required=True)
    p.add_argument('--submirror', type=Path, required=True)
    p.add_argument('--output', type=Path)
    p.add_argument('--cache', type=Path, default=ROOT / '.lake/signed-action-floors')
    args = p.parse_args()
    paired = json.loads(args.paired.read_text())
    signs = json.loads(args.submirror.read_text())
    n, k = paired['slabs_per_direction'], signs['slabs']
    packet = digest(RECORD)
    if not (1 <= k <= min(n, 316) and n <= 391):
        p.error('submirror range exceeds its physical prefix or lower mirror bracket')
    if signs['upper'] or signs['paired_key'] != paired['key']:
        p.error('expected a lower-height proof for this same signed physical prefix')
    if paired['packet_sha256'] != packet or signs['packet_sha256'] != packet:
        p.error('physical prefix and submirror signs must use the original pilot packet')
    paths = list(map(Path, signs['import_paths']))
    paired_paths = list(map(Path, paired['import_paths']))
    admitted(paths[0], f'DommaschkSubmirror{k:03}Of{n:03}', signs['key'])
    admitted(paired_paths[0], f'DommaschkPairedPrefix{n:03}', paired['key'])

    def lake(*command):
        return subprocess.check_output(['lake', 'env', *command], cwd=ROOT, text=True).strip()

    version = lake('lean', '--version')
    keys = [packet, version, paired['key'], signs['key'], digest(DESIGN / 'DommaschkSignedActionFloor.trace')]
    overlay = merge_import_roots(args.cache, paths + paired_paths, keys)
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    decl = generate(n, k)
    root, record = compile_modules(args.cache / decl[0], [decl], [overlay], keys,
                                   env, 'SignedActionFloorCache')
    result = {key: v for key, v in record.items() if key != 'artifacts'}
    result.update(slabs=k, signed_trace_length=n, packet_sha256=packet,
                  submirror_key=signs['key'], paired_key=paired['key'], lean_version=version,
                  bound=str(Fraction(7 * k, 8000)), import_paths=[str(root), str(overlay)])
    if args.output:
        save(args.output, result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
