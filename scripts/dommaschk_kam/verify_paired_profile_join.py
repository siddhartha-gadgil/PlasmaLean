"""Join real tube strength, field ceiling and arclength proofs on a shared QA2R row."""
import argparse
import json
from pathlib import Path
import subprocess

from emit_sparse_taylor_slab import ROOT
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_paired_arc_ratio import PACKAGE
from verify_native_paired_profiles import PACKAGE as NATIVE
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


def source(index, arc, strength, providers=None):
    name = f'DommaschkComparedProfiles{index:03d}'
    src = f'''module
public import {NATIVE if providers else PACKAGE}.{arc}
public import CenteredPairCache.{strength}

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open Certificates.PositionFrameSlabs DommaschkPairedActionProfiles
set_option maxRecDepth 16384
set_option linter.style.longLine false
'''
    for back, direction, short in [(False,'forward','fwd'),(True,'backward','back')]:
        phase = '(-t)' if back else 't'
        if providers:
            inner,outer = [p+('.backRow' if back else '.row') for p in providers]
        else:
            inner,outer = [arc+'.'+short+'Row'+s for s in ('I','O')]
        src += f'''
abbrev {short}Inner := {inner}
abbrev {short}Outer := {outer}

theorem {direction} {{a b : State}} {{x y : Plane}} {{t : ℝ}}
    (ht : t ∈ Set.Icc ({index}/64:ℝ) ({index+1}/64))
    (hx : x ∈ (physicalSlab a {short}Inner ({index}/64)).tube t)
    (hy : y ∈ (physicalSlab b {short}Outer ({index}/64)).tube t) :
    Compared {phase} x y := by
  obtain ⟨ic,oc,weight⟩ := {arc}.{direction}_bounds ht hx hy
  apply DommaschkPairedArcRatio.compared_of_squared ic oc _ weight
  with_unfolding_all exact {strength}.{short}_squared_drop ht hx hy
'''
    return name,src+f'\nend PlasmaLean.Design.{name}\n',['forward','backward']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--arc',type=Path,required=True)
    p.add_argument('--strength',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-profile-join')
    a = p.parse_args()
    arc, strength = [json.loads(f.read_text()) for f in (a.arc,a.strength)]
    i = arc['row']
    packets = [digest(load(radius)[1]) for radius in (470,478)]
    labels = ('q0r470','q0r478')
    native = arc['module'] == f'DommaschkNativePairedProfile{i:03d}' and arc.get('direct') is False
    if (not 0 <= i < 325 or arc['packets'] != packets or strength['index'] != i
            or (strength['inner'],strength['outer']) != labels
            or [strength['endpoints'][s]['packet_sha256'] for s in labels] != packets
            or not (native or arc['module'] == f'DommaschkPairedArcRatio{i:03d}')
            or strength['module'] != f'DommaschkCenteredStrengthPair{i:03d}'):
        p.error('expected both authenticated observables for the same original 470/478 row')
    roots, keys = [], []
    for report in (arc,strength):
        paths = list(map(Path,report['import_paths']))
        admitted(paths[0],report['module'],report['key'])
        roots.extend(paths)
        keys.append(report['key'])
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    a.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    a.lean_path = lake('printenv','LEAN_PATH')
    cache = a.cache.resolve()
    overlay = merge_import_roots(cache,roots,keys)
    item = source(i,arc['module'],strength['module'],arc['providers'] if native else None)
    root,r = compile_modules(cache/item[0],[item],[overlay],
                             [lake('lean','--version'),keys,packets,digest(DESIGN/'DommaschkPairedArcRatio.trace')],
                             a,'ComparedProfileCache')
    out = {k:r[k] for k in ('module','key','axioms','theorems','wall_seconds','peak_rss_kib')}
    out.update(row=i,packets=packets,parents=keys,import_paths=[str(root),str(overlay)])
    save(a.output,out)
    print(r['module'],r['key'],flush=True)


if __name__=='__main__':
    main()
