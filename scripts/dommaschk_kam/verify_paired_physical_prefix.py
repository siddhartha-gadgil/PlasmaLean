"""Join verified forward and backward q0r470 prefixes at one transferred birth state."""
import argparse
import json
from pathlib import Path
import subprocess

from verify_backward_physical_prefix import compile_modules
from verify_physical_trace_slabs import ALLOWED, DESIGN, RECORD, ROOT, artifact_hashes, digest, save


def validated(path, sign):
    manifest = json.loads(path.read_text())
    n = manifest['length']
    prefix = 'DommaschkPhysicalPrefix' if sign > 0 else 'DommaschkBackwardPrefix'
    maximum = 'max_physical_radius_numerator' if sign > 0 else 'maximum_radius_numerator'
    package = 'PhysicalPrefixCache' if sign > 0 else 'BackwardPrefixCache'
    name = prefix+f'{n:03}'
    roots = list(map(Path,manifest['import_paths']))
    marker = json.loads((roots[0]/'accepted.json').read_text())
    if (n < 3 or manifest['module'] != name or manifest['coordinate_denominator'] != 2**80
            or manifest['packet_sha256'] != digest(RECORD) or set(manifest['axioms']) != ALLOWED
            or marker['key'] != manifest['key'] or marker['module'] != name
            or f'{package}/{name}.olean' not in marker['artifacts']):
        raise ValueError(f'inconsistent prefix manifest: {path}')
    artifact_hashes(roots[0],marker)
    return n, name, roots, manifest['key'], manifest[maximum]


def generate(n,f,b,cap):
    name = f'DommaschkPairedPrefix{n:03}'
    src = f'''module
public import PlasmaLean.Design.DommaschkBackwardPairedPrefix
public import PhysicalPrefixCache.{f}
public import BackwardPrefixCache.{b}

/-! # One Q-16 field line through {n} slabs on each side of the same section entry. -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkMirrorLaunch DommaschkBackwardPairedPrefix
set_option linter.style.longLine false

/-- The two independently certified physical prefixes share one actual transferred birth point. -/
theorem exists_nested_paired : BirthPassage {n} {f}.exitState {b}.exitState {f}.rows {b}.rows :=
  birthPassage ⟨{f}.checked,{f}.field_bounds⟩ ⟨{b}.checked,{b}.field_bounds⟩

/-- Larger of the two archived physical-radius maxima, in units of 2⁻⁸⁰. -/
def maximumRadius : ℕ := {cap}

/-- Both signed halves satisfy the common uniform position-error cap over their exact tubes. -/
theorem uniform_paired_error {{y : ℝ → Plane}}
    (forward : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 {f}.rows,
      ∀ t ∈ Set.Icc slab.start slab.stop, y t ∈ slab.tube t)
    (backward : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 {b}.rows,
      ∀ t ∈ Set.Icc slab.start slab.stop, y (-t) ∈ slab.tube t) :
    (∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 {f}.rows,
      ∃ r ∈ {f}.rows, ∀ t ∈ Set.Icc slab.start slab.stop,
        dist (y t) (reference slab.start r t) ≤ maximumRadius / (2 : ℝ)^80) ∧
    (∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 {b}.rows,
      ∃ r ∈ {b}.rows, ∀ t ∈ Set.Icc slab.start slab.stop,
        dist (y (-t)) (reference slab.start r t) ≤ maximumRadius / (2 : ℝ)^80) := by
  constructor
  · intro slab hs
    obtain ⟨r,hr,bound⟩ := {f}.uniform_tube_error forward slab hs
    refine ⟨r,hr,fun t ht => (bound t ht).trans ?_⟩
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (show {f}.maximumRadius ≤ maximumRadius by kernel_fact)) (by positivity)
  · apply DommaschkBackwardPrefix.tube_error _ backward
    intro r hr
    exact ({b}.radius_bound hr).trans (by kernel_fact)

end PlasmaLean.Design.{name}
'''
    return name,src,['exists_nested_paired','uniform_paired_error']


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--forward',type=Path,required=True)
    p.add_argument('--backward',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-physical')
    p.add_argument('--output',type=Path)
    a = p.parse_args()
    n,fw,fl,fk,mf = validated(a.forward,1)
    nb,bw,bl,bk,mb = validated(a.backward,-1)
    if n != nb:
        p.error('the two prefix lengths must agree')
    subprocess.run(['lake','build','--no-build','PlasmaLean.Design.DommaschkBackwardPairedPrefix'],
                   cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    def lake(*args):
        return subprocess.check_output(['lake','env',*args],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    cap = max(mf,mb)
    declaration = generate(n,fw,bw,cap)
    root,r = compile_modules(a.cache.resolve()/declaration[0],[declaration],[*fl,*bl],
                             [fk,bk,digest(DESIGN/'DommaschkBackwardPairedPrefix.trace'),
                              lake('lean','--version')],a,'PairedPrefixCache')
    out = {k:v for k,v in r.items() if k!='artifacts'}
    out.update(slabs_per_direction=n,packet_sha256=digest(RECORD),maximum_radius_numerator=cap,
               coordinate_denominator=2**80,forward_key=fk,backward_key=bk,
               import_paths=[str(root),*map(str,fl),*map(str,bl)])
    if a.output:
        save(a.output,out)
    print(json.dumps(out),flush=True)
