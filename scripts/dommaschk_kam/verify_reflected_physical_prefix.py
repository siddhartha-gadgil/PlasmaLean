"""Derive a physical backward QA2R trajectory on reflected tubes using a forward prefix alone."""
import argparse
from pathlib import Path
import subprocess
from types import SimpleNamespace

from verify_backward_physical_prefix import compile_modules
from verify_paired_physical_prefix import validated
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def source(n, forward):
    name=f'DommaschkReflectedPrefix{n:03}'
    return name, f'''module
public import PlasmaLean.Design.DommaschkReflectedPilot
public import PhysicalPrefixCache.{forward}

/-! # Exact backward trajectory on {n} reflected forward tubes -/
@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch Certificates.PositionFrameSlabs DommaschkJacobianReflection
open DommaschkJacobian Set {forward}

private theorem positions : rows = DommaschkPositionFramesFwd.blocks.flatten.take {n} := by
  with_unfolding_all rfl

theorem positive : ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows,
    ∀ t ∈ Icc slab.start slab.stop, ∀ x ∈ slab.tube t, 0 < x 0 := by
  rw [positions]
  exact DommaschkReflectedPilot.prefix_positive _ _ _

/-- Every physical entrance state, including an off-midplane one, launches the
negative-clock solution through the reflected forward tubes. -/
theorem trajectory {{x : Plane}} (entry : x ∈ stateSet (MirrorEndpoint.start .q0r470)) :
    ∃ y : ℝ → Plane, y 0 = x ∧ flip (y ({n} / 64)) ∈ stateSet exitState ∧
      (∀ t ∈ Icc 0 ({n} / 64 : ℝ),
        HasDerivWithinAt y (euclideanFlow 0 (-1) t (y t)) (Icc 0 ({n} / 64 : ℝ)) t) ∧
      ∀ slab ∈ physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows,
        ∀ t ∈ Icc slab.start slab.stop, flip (y t) ∈ slab.tube t := by
  have phys := checked.physical (domain := ballDomain) (a := 0)
    (F := euclideanFlow 0 1) (J := velocityJacobian 0 1)
    (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil] using field_bounds)
  have chain : Fields.TrajectorySlabs.Chain (euclideanFlow 0 1) 0
      (stateSet (MirrorEndpoint.start .q0r470)) ({n} / 64) (stateSet exitState)
      (physicalSlabs (MirrorEndpoint.start .q0r470) 0 rows) := by
    simpa only [zero_add, Nat.cast_ofNat, List.flatten_cons, List.flatten_nil, List.append_nil] using phys
  exact DommaschkReflectedPath.endpoint_trajectory .q0r470 chain positive entry

end PlasmaLean.Design.{name}
'''


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('forward',type=Path)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/reflected-physical')
    p.add_argument('--output',type=Path)
    a=p.parse_args()
    n,f,roots,key,cap=validated(a.forward,1)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    version=lake('lean','--version')
    env=SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),
                        lean_path=lake('printenv','LEAN_PATH'))
    name,code=source(n,f)
    base,m=compile_modules(a.cache/name,[(name,code,['positive','trajectory'])],roots,
                           [version,key,digest(DESIGN/'DommaschkReflectedPilot.trace')],env,'ReflectedPrefixCache')
    report={k:v for k,v in m.items() if k!='artifacts'}
    report.update(length=n,forward_key=key,forward_tube_radius_numerator=cap,
                  import_paths=list(map(str,[base,*roots])))
    if a.output:
        save(a.output,report)
    print(n,'slabs from forward-only proof:',m['key'],flush=True)


if __name__ == '__main__':
    main()
