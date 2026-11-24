"""Transport an authenticated physical core action floor to both first upper mirror contacts."""

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


def generate(k, n):
    core = f'DommaschkSignedActionFloor{k:03}Of{n:03}'
    contacts = f'DommaschkFirstMirrorBirth{n:03}'
    forward, backward = f'DommaschkPhysicalPrefix{n:03}', f'DommaschkBackwardPrefix{n:03}'
    name = f'DommaschkFirstUpperActionFrom{k:03}Of{n:03}'
    floor = Fraction(7 * k, 8000)
    source = f'''module

public import PlasmaLean.Design.DommaschkFirstMirrorActionFloor
public import SignedActionFloorCache.{core}
public import SignedMirrorBirthCache.{contacts}

/-! # Physical action between the two first upper mirrors of the same Q-16 birth -/

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkSignedObservable DommaschkFirstMirrorActionFloor
open DommaschkFirstMirrorLaunchSign

set_option maxRecDepth 16384

/-- Both first mirror heights on the original signed birth path, plus the true
Cartesian action floor integrated all the way between the first upper mirrors. -/
theorem from_birth :
    BirthWith (fun x => ∃ y, Path {n} {forward}.exitState {backward}.exitState
      {forward}.rows {backward}.rows x y ∧
      FirstBoth (316/64) (317/64) (height false) y ∧
      FirstAction (324/64) (325/64) (height true) ({floor.numerator}/{floor.denominator}) y) := by
  obtain ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, each⟩ := {contacts}.contacts_from_birth
  refine ⟨uC, zC, uA, zA, r, z, tc, ta, ic, ia, nested, fun φ hφ => ?_⟩
  obtain ⟨sign, approach, hs, clock, entry, ode, y, path, lower, upper⟩ := each φ hφ
  have region := DommaschkSignedTraceDomain.on_path path (by norm_num)
    (by with_unfolding_all rfl) (by with_unfolding_all rfl) rfl rfl
  have mass := ({core}.on_path path).2
  refine ⟨sign, approach, hs, clock, entry, ode, y, path, lower, ?_⟩
  apply from_core (limit := ({n} : ℝ) / 64) (cut := ({k} : ℝ) / 64) upper
    (by norm_num) (by norm_num) (by norm_num)
  · simpa only [Nat.cast_ofNat, neg_div] using path.ode
  · simpa only [Nat.cast_ofNat, neg_div] using region
  · simpa only [neg_div] using mass

end PlasmaLean.Design.{name}
'''
    return name, source, ['from_birth']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--core', type=Path, required=True)
    parser.add_argument('--contacts', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/signed-action-floors')
    args = parser.parse_args()
    core, first = (json.loads(p.read_text()) for p in (args.core, args.contacts))
    n, k = core['signed_trace_length'], core['slabs']
    if not (325 <= n <= 391 and 0 < k <= 316):
        parser.error('the complete upper mirror bracket and the lower-height core must be present')
    packet = digest(RECORD)
    if any(m['packet_sha256'] != packet for m in (core, first)):
        parser.error('both upstream calculations must name the original pilot packet')
    imports = []
    for manifest, name in ((core, f'DommaschkSignedActionFloor{k:03}Of{n:03}'),
                           (first, f'DommaschkFirstMirrorBirth{n:03}')):
        roots = list(map(Path, manifest['import_paths']))
        admitted(roots[0], name, manifest['key'])
        imports.extend(roots)

    def lake(*command):
        return subprocess.check_output(['lake', 'env', *command], cwd=ROOT, text=True).strip()

    version = lake('lean', '--version')
    keys = [version, packet, core['key'], first['key'],
            digest(DESIGN / 'DommaschkFirstMirrorActionFloor.trace')]
    overlay = merge_import_roots(args.cache, imports, keys)
    env = SimpleNamespace(lean=str(Path(lake('lean', '--print-prefix')) / 'bin/lean'),
                          lean_path=lake('printenv', 'LEAN_PATH'))
    decl = generate(k, n)
    root, record = compile_modules(args.cache / decl[0], [decl], [overlay], keys,
                                   env, 'FirstUpperActionFloorCache')
    result = {key: value for key, value in record.items() if key != 'artifacts'}
    result.update(slabs=k, signed_trace_length=n, packet_sha256=packet, lean_version=version,
                  core_key=core['key'], first_contacts_key=first['key'],
                  bound=str(Fraction(7*k, 8000)), import_paths=[str(root), str(overlay)])
    if args.output:
        save(args.output, result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
