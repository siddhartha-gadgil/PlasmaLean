"""Recover a quantitative height clearance from the already authenticated grouped field models."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import subprocess
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS, R0M
from emit_sparse_taylor_slab import ROOT
from screen_mirror_prefix_signs import gap_model
from verify_backward_physical_prefix import compile_modules, union
from verify_grouped_mirror_exclusion import BASE, GAPS, ROWS, gap, group_literal, ordered, partition, run_group
from verify_harmonic_group_exclusion import radius_cap
from verify_mirror_endpoint_signs import gap_proof, header
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_secondary_mirror_caps import load
from verify_secondary_submirror_birth import source as birth_source
from verify_signed_mirror_passage import merge_import_roots


def margin(name,tube,args):
    original = name.replace(args.label+args.suffix,args.label,1)
    base = gap(original,tube,args.original)
    original_root,marker = base[-1]
    upper = gap_model(*tube).bound()[1]
    h = HEIGHTS[0]
    cap = radius_cap(tube[0])
    if upper+cap**16*(h*h-(h-args.drop)**2) >= 0:
        raise ValueError(f'{name}: original gap {upper} and radius {cap} miss the requested height')
    r,*rest = tube
    proof = gap_proof(False,False,h,r,(r-R0M,*rest))
    start,statement = proof.split(':\n    oriented false (',1)
    expression,body = statement.split(') 0 := by',1)
    body = body.split('\n  change oriented false (gap R ',1)[0]
    src = header(name,[*[BASE+'.'+original+f for f in 'DRZ'],
                       'PlasmaLean.Design.DommaschkGroupGapRadius','PlasmaLean.Design.DommaschkGroupedMirrorModels'])
    src += f'''open DommaschkMirrorEndpointSign DommaschkPreMirrorSigns DommaschkGroupedMirrorModels
open {original}
set_option maxHeartbeats 1600000
def upper : ℚ := {upper}
'''
    src += start.replace('theorem sign_on_models','theorem upper_on_models')
    src += f':\n    {expression} ≤ upper := by{body}\n'
    src += f'''  change gap R (DommaschkFirstMirrorLaunchSign.height false) D nr nz ≤ (upper : ℝ)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le, upper] at bound ⊢
  linarith only [bound.2]

def group : Group := {group_literal(tube)}
theorem below : group.Below ({args.threshold}) := by
  intro w R z t hw hR hr hz hc hs
  apply physical_sign false hR (by norm_num [DommaschkFirstMirrorLaunchSign.height])
  have box := enclose (c := ⟨[({cap/2})],({cap/2})⟩) hw hr (by kernel_fact)
  norm_num [Model.Mem, Certificates.QPoly.eval, abs_le] at box
  have bound := upper_on_models hw hr
    ⟨shifted_mem (u := trial.u) hr (eq_of_beq (by kernel_fact)) (by kernel_fact),hz,hc,hs⟩
  apply DommaschkGroupGapRadius.at_lower (radius := ({cap})) hR.le (by linarith only [box.2])
    (by norm_num [DommaschkFirstMirrorLaunchSign.height]) bound
  norm_num [upper, DommaschkFirstMirrorLaunchSign.height]
end PlasmaLean.Design.{name}
'''
    proof = compile_modules(args.cache/name,[(name,src,['upper_on_models','below'])],
        [original_root,base[0][0]],[args.keys,marker['key'],digest(DESIGN/'DommaschkGroupGapRadius.trace')],args,GAPS)
    args.projections.append(dict(module=name,key=proof[1]['key'],field_key=marker['key'],
                                 original_upper=str(upper),radius_cap=str(cap)))
    return [*base,proof]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--launch',type=int,required=True)
    p.add_argument('--exclusion',type=Path,required=True,help='exact signed N-121-style ordered exclusion')
    p.add_argument('--drop',type=Fraction,required=True)
    p.add_argument('--groups',type=int,nargs='+',help='only project groups with these start indices')
    p.add_argument('--prefix-length',type=int,help='restrict the final ordered result to this many rows')
    p.add_argument('--signed',type=Path,help='attach a real birth path with the same number of signed rows')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-field-clearance')
    p.add_argument('--original-cache',type=Path,default=ROOT/'.lake/grouped-mirror-exclusion')
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    label,archive,traces,brackets = load(args.launch)
    args.label = label
    if not 0 < args.drop < HEIGHTS[0]:
        p.error('require a positive test-height drop smaller than hL')
    original = json.loads(args.exclusion.read_text())
    parent = original['groups']
    maximum = parent[-1]['stop']
    signed = json.loads(args.signed.read_text()) if args.signed else None
    limit = args.prefix_length if args.prefix_length is not None else (
        signed['length_each_direction'] if signed else maximum)
    if not 1<=limit<=maximum or ((args.prefix_length or signed) and args.groups):
        p.error('choose one valid prefix length or a selection of group start indices')
    name = f'Dommaschk{label}SubmirrorPrefix{maximum:03}'
    checksum = digest(archive)
    if (original['module'],original['endpoint'],original['packet_sha256'])!=(name,label,checksum):
        p.error('wrong signed exclusion receipt or archive')
    roots = list(map(Path,original['import_paths']))
    admitted(roots[0],name,original['key'])
    tasks = [t for t in partition(traces,brackets[0][0]) if t[0]<limit]
    if args.groups:
        tasks = [t for t in tasks if t[0] in args.groups]
        if len(tasks)!=len(set(args.groups)):
            p.error('unknown starting index')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    args.keys = [checksum,lake('lean','--version')]
    args.cache = args.cache.resolve()
    args.original = SimpleNamespace(cache=args.original_cache,keys=args.keys,lean=args.lean,lean_path=args.lean_path)
    args.suffix = f'Drop{args.drop.numerator}Over{args.drop.denominator}'
    args.threshold = f'(↑(DommaschkFirstMirrorLaunchSign.height false - ({args.drop})) : ℝ)'
    args.projections = []
    groups,packages = [],[]
    for task in tasks:
        a,b,_,_ = task
        row = next(g for g in parent if g['start']==a)
        old = f'Dommaschk{label}Submirror{a:03}To{b:03}Rows'
        if row['module']!=old or row['stop']!=min(b,maximum):
            p.error('parent row grouping differs from the original archive')
        base = (roots[1]/ROWS/(old+'.olean')).resolve(strict=True).parents[1]
        admitted(base,old,row['key'])
        group,ps = run_group(task,label+args.suffix,traces,args,provider=margin,threshold=args.threshold)
        groups.append({**group,'stop':min(b,limit)})
        packages.extend(ps)
    result = dict(endpoint=label,packet_sha256=checksum,drop=str(args.drop),target=str(HEIGHTS[0]-args.drop),
                  groups=groups,projections=args.projections,parent=original['key'])
    if not args.groups:
        result.update(ordered(label+args.suffix,groups,packages,args,args.threshold))
        if signed:
            n = signed['length_each_direction']
            prefix = f'DommaschkSignedPrefix{label}{n:03}'
            if ((signed['endpoint'].upper(),signed['module'],signed['packet_sha256'],n)
                    != (label,prefix,checksum,limit)):
                p.error('physical birth archive and ordered clearance must have the same endpoint and length')
            root = Path(signed['proof_root'])
            admitted(root,prefix,signed['key'])
            parents = [result['key'],signed['key']]
            paths = [*map(Path,result['import_paths']),root,Path(signed['import_path'])]
            overlay = merge_import_roots(args.cache,paths,parents)
            birth = birth_source(label+args.suffix,n,prefix,result['module'],args.threshold)
            br,bm = compile_modules(args.cache/birth[0],[birth],[overlay],
                [args.keys,parents,digest(DESIGN/'DommaschkEndpointMirrorBranch.trace')],args,
                'GroupedClearanceBirthCache')
            result['physical_birth'] = {k:bm[k] for k in ('module','key','axioms','theorems')}
            result['physical_birth'].update(parents=parents,signed_length=n,import_paths=[str(br),str(overlay)])
    else:
        result['import_paths'] = [str(union(args.cache,packages))]
    save(args.output,result)


if __name__ == '__main__':
    main()
