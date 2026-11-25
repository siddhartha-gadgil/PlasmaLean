"""Check true submirror births on both wide symmetry sectors of the original Q16 chart."""
import argparse
from fractions import Fraction as F
from math import ceil
from pathlib import Path

from bounce_mirror_pilot import Model, SCALE
from emit_sparse_taylor_slab import model_literal
from screen_mirror_prefix_signs import gap_model
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_grouped_mirror_exclusion import gap, GAPS
from verify_mirror_endpoint_signs import header
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def physical_models(opposite):
    lo, hi = (89400, 89548) if opposite else (99517, 99622)
    centre = F(lo + hi, 200000)
    rounding = F(1, 10**11)
    delta = F(1, 32 * 6) + rounding
    error = ceil((F(hi - lo, 200000) + delta) * SCALE) + 1
    tube = [Model([round(centre * SCALE), error]), Model([0], ceil(delta * SCALE)),
            Model([(-1 if opposite else 1) * SCALE], SCALE // 512),
            Model([0], SCALE // 16)]
    if gap_model(*tube).bound()[1] >= 0:
        raise ValueError("field enclosure misses the lower mirror height")
    return tube


def branch(opposite, args):
    name = "DommaschkWideBirth" + ("Opposite" if opposite else "Zero")
    tube = physical_models(opposite)
    parts = gap(name, tube, args)
    root = union(args.cache, parts)
    q = str(opposite).lower()
    c, e = tube[0].a
    src = header(name + "Physical", ["PlasmaLean.Design.DommaschkWideBirthBounds",
                                    GAPS + "." + name])
    src += f'''open DommaschkWideBirthBounds DommaschkMirrorLaunch DommaschkMirrorEndpointSign
open DommaschkFirstMirrorLaunchSign Set

theorem resolved : Sector {q} := by
  intro R z φ hr hz hφ
  obtain ⟨hc,hs⟩ := angle_bounds {q} hφ
  obtain ⟨w,hw,hm⟩ := radial_parameter (c := {c}) (e := {e}) (by norm_num)
    (R := R) (by rw [abs_le]; norm_num [rLo, rHi] at hr ⊢; constructor <;> linarith [hr.1,hr.2])
  apply {name}.below hw (by norm_num [rLo, rHi] at hr; linarith [hr.1]) hm
  · change ({model_literal(tube[1])}).Mem w z
    rw [mem_ofDyadic_iff]
    norm_num [Certificates.QPoly.eval] at hz ⊢
    linarith only [hz]
  · change ({model_literal(tube[2])}).Mem w (Real.cos (2 * φ))
    rw [mem_ofDyadic_iff]
    norm_num [Certificates.QPoly.eval, cosCentre, abs_le] at hc ⊢
    constructor <;> linarith [hc.1,hc.2]
  · change ({model_literal(tube[3])}).Mem w (Real.sin (2 * φ))
    rw [mem_ofDyadic_iff]
    norm_num [Certificates.QPoly.eval] at hs ⊢
    linarith only [hs]
end PlasmaLean.Design.{name}Physical
'''
    top = name + "Physical"
    result = compile_modules(args.cache/top, [(top, src, ["resolved"])], [root],
                             [args.keys, parts[-1][1]["key"],
                              digest(DESIGN/"DommaschkWideBirthBounds.trace")], args, "WideBirthCache")
    return [*parts, result]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cache", type=Path, default=ROOT / ".lake/wide-birth-strength")
    args = parser.parse_args()
    env(args)
    args.keys = [args.version, digest(DESIGN/"DommaschkGroupedMirrorModels.trace")]
    parts = [*branch(False, args), *branch(True, args)]
    root = union(args.cache, parts)
    name = "DommaschkWideBirthFamily"
    source = header(name, ["WideBirthCache.DommaschkWideBirthZeroPhysical",
                           "WideBirthCache.DommaschkWideBirthOppositePhysical"])
    source += f'''open DommaschkWideBirthBounds
theorem original_births : CommonBirths := from_sectors
  (by intro q; cases q; exact DommaschkWideBirthZeroPhysical.resolved; exact DommaschkWideBirthOppositePhysical.resolved)
end PlasmaLean.Design.{name}
'''
    base, result = compile_modules(args.cache/name, [(name, source, ["original_births"])], [root],
                                   [args.keys,[p[1]["key"] for p in parts]], args, "WideBirthFamilyCache")
    save(args.output, {k:result[k] for k in ("module","key","theorems","axioms")} |
         {"import_paths":[str(base),str(root)], "phase_half_width":"1/32",
          "radial_faces":["11/25","27/50"]})
    print(name, result["key"])


if __name__ == "__main__":
    main()
