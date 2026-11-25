"""Build immutable original signed row lists for the four closed radial intervals."""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from bounce_frame_witness import DEFAULT_WITNESS
from emit_position_slabs import step
from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


PACKAGE = "RadialRibbonPacketCache"


def load(path):
    data = json.loads(path.read_text())
    expected = [digest(DEFAULT_WITNESS), digest(DEFAULT_WITNESS.with_name("bounce_frame_q0_u478.json.gz"))]
    if (data["tiles"] != 4 or Fraction(data["seed_radius"]) != Fraction(1, 65536)
            or data["endpoints"] != expected or len(data["traces"]) != 8):
        raise ValueError("expected the four continuous upper-bracket tubes on the original candidate")
    branches = {}
    for tile in range(4):
        for sign in (-1,1):
            tr = data["traces"][2*tile+int(sign>0)]
            rows = [r["position"] for r in tr["rows"]]
            if ((tr["tile"],tr["direction"]) != (tile,sign) or len(rows) != 340 or "failure" in tr
                    or any(r["index"] != i for i,r in enumerate(rows))):
                raise ValueError(f"invalid radial interval {tile}, clock {sign}")
            branches[tile,sign] = rows
    return data,branches


def item(k,data,rows):
    name=f"DommaschkRadialRibbonRows{k}"
    source=f"""module
public import PlasmaLean.Design.DommaschkRadialRibbonEntry
@[expose] public section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs
set_option maxRecDepth 65536
set_option linter.style.longLine false
noncomputable abbrev seed := DommaschkRadialRibbonEntry.seed {k}
"""
    states = [tr["seed_center"] for tr in data["traces"] if tr["tile"] == k]
    if states[0] != states[1]:
        raise ValueError("the two signs have different entry balls")
    source += f"theorem seed_point : seed.point = ⟨{states[0][0]},{states[0][1]}⟩ := by with_unfolding_all rfl\n"
    for sign,tag in [(-1,"backward"),(1,"forward")]:
        branch = rows[k,sign]
        groups=[]
        for a in range(0,len(branch),16):
            n=f"{tag}{a:03}"
            groups.append(n)
            source += f"def {n} : List Step := [\n" + ",\n".join(step(r) for r in branch[a:a+16]) + "]\n"
        source += f"def {tag}Rows : List Step := [{','.join(groups)}].flatten\n"
        source += f"theorem {tag}_count : {tag}Rows.length = {len(branch)} := by with_unfolding_all rfl\n"
    source += f"end PlasmaLean.Design.{name}\n"
    return name,source,[]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ribbon",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--cache",type=Path,default=ROOT/".lake/radial-ribbon-packets")
    a=p.parse_args()
    env(a)
    data,rows=load(a.ribbon)
    checksum=digest(a.ribbon)
    result={}
    for k in range(4):
        decl=item(k,data,rows)
        root,r=compile_modules(a.cache/decl[0],[decl],[],
            [a.version,checksum,digest(DESIGN/"DommaschkRadialRibbonEntry.trace")],a,PACKAGE)
        result[k]={key:r[key] for key in ("module","key","wall_seconds","peak_rss_kib")}
        result[k].update(import_paths=[str(root)],ribbon=checksum,tile=k,length=340)
        save(a.output,result)
        print(k,r["key"],flush=True)


if __name__=="__main__":
    main()
