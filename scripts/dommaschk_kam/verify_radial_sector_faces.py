"""Verify strict endpoint-face action inequalities on one and the same embedded torus pair."""
import argparse
import json
from pathlib import Path
import re

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--exit-faces', action='store_true', help='observe either physical endpoint independently at its own birth')
    modes.add_argument('--action-window', action='store_true', help='retain the quantitative first-well bounds')
    parser.add_argument('--flow', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/radial-sector-faces')
    args = parser.parse_args()
    report = json.loads(args.flow.read_text())
    parent = report['module']
    match = re.fullmatch(r'DommaschkRadialFlowOn(\d+(?:_\d+){7})', parent)
    if not match:
        parser.error('expected the verified radial field-line continuation theorem')
    counts = [int(v) for v in match[1].split('_')]
    if counts[0] != 391 or counts[1] <= 327:
        parser.error('the two true endpoint trajectories must cover their common mirror window')
    roots = list(map(Path, report['import_paths']))
    marker = admitted(roots[0], parent, report['key'])
    expected = {f'PlasmaLean.Design.{parent}.{n}' for n in ['from_entries','from_nested_tori']}
    if not expected.issubset(marker['theorems']):
        parser.error('missing authentic endpoint entries or original embedded tori')
    secant = 'DommaschkTopHeightSecant'+match[1]
    if len(roots) < 2:
        parser.error('missing the independent endpoint action comparison')
    comparator = admitted(roots[1],secant,report['upper_secant'])
    if f'PlasmaLean.Design.{secant}.both_on_paths' not in comparator['theorems']:
        parser.error('missing the two signed first-well endpoint actions')
    template = Path(__file__).parent/'templates/radial_sector_faces.lean.tpl'
    # Copy the already authenticated reconstruction verbatim, including both ODE and birth bindings.
    # The earlier artifact and its production template remain independently reproducible.
    origin = (roots[0]/'RadialFieldLineContinuationCache'/(parent+'.lean')).read_text()
    marker_start = '    FromRadialPassages uC zC uA zA φ := by\n'
    marker_end = '  intro Y born paths early back fwd\n'
    if origin.count(marker_start) != 1 or origin.count(marker_end) != 1:
        parser.error('the original endpoint reconstruction is missing or ambiguous')
    witness = origin.split(marker_start,1)[1].split(marker_end,1)[0].rstrip('\n')
    if not witness.startswith('  obtain ⟨sign, approach,') or '  have pz : Enclosed z ' not in witness:
        parser.error('the original signed physical proof does not contain both endpoint enclosures')
    if args.action_window or args.exit_faces:
        module = 'DommaschkSectorActionBand'
        prop = 'BandFaces'
        if args.exit_faces:
            module, prop = 'DommaschkPhysicalActionExit', 'BoundaryValues'
        cap, floor = 'innerCap', 'outerFloor'
        # The endpoint source supplies both exact absolute estimates in this conjunction.
        fields = 'innerWell,outerWell,_,_,low,high'
        if witness.count(fields) != 1:
            parser.error('expected the archived pair of absolute action bounds')
        witness = witness.replace(fields, 'innerWell,outerWell,innerCap,outerFloor,low,high')
    else:
        module = 'DommaschkSectorFaces'
        prop = 'FaceSigns'
        cap, floor = 'low', 'high'
    src = (template.read_text().replace('FACE_MODULE', module).replace('FACE_PROPERTY', prop)
           .replace('INNER_BOUND', cap).replace('OUTER_BOUND', floor)
           .replace('SUFFIX', match[1]).replace('ENDPOINT_WITNESSES', witness))
    birth_sides = ''
    if args.exit_faces:
        birth_sides = ('\n    ⟨by linarith [hl.2, (abs_le.mp small).1], by linarith [hr.1, (abs_le.mp small).2]⟩'
                       '\n    ⟨by linarith [hL.2, (abs_le.mp small).1], by linarith [hR.1, (abs_le.mp small).2]⟩')
    src = src.replace('EXTRA_BIRTH_BOUNDS', birth_sides)
    name = module+'On'+match[1]
    env(args)
    keys = [args.version,report['key'],digest(DESIGN/(module+'.trace'))]
    item = name,src,['from_entries','from_nested_tori']
    root,rec = compile_modules(args.cache/name,[item],roots,keys,args,'RadialSectorFacesCache')
    out = {k:rec[k] for k in ('module','key','axioms','theorems','wall_seconds','peak_rss_kib')}
    out.update(flow=report['key'],upper_secant=report['upper_secant'],counts=counts,
               import_paths=list(map(str,[root,*roots])))
    save(args.output,out)
    print(name,rec['key'],flush=True)


if __name__=='__main__':
    main()
