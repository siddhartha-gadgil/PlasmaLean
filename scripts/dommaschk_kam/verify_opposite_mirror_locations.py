"""Locate first mirror branches in the original signed node intervals and attach a signed prefix."""

import argparse
import json
from pathlib import Path

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_endpoint_signed_prefix import SIGNED_PACKAGE
from verify_mirror_physical_hit import admitted
from verify_opposite_mirror_caps import LABELS, bracket_nodes, cap_module
from verify_opposite_mirror_slopes import BRANCHES
from verify_physical_first_mirror_values import source_start
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


LOCATIONS = 'OppositeMirrorLocationCache'
PHYSICAL = 'OppositeOriginalBranchCache'


def node_bounds(e, sign, n, edges, side):
    back = str(sign == -1).lower()
    base = 'DommaschkArea'+e.upper()+('Back' if sign == -1 else 'Fwd')
    lines = []
    for j, (left, right) in enumerate(edges):
        for after, node in [(False, left), (True, right)]:
            i = node - int(after)
            cap = cap_module(e, sign, j, node, after)
            label = side+('High' if j else 'Low')+('Right' if after else 'Left')
            f = f'profile (Real.pi/2) y {back} ({node}/64)'
            h = '(height '+str(bool(j)).lower()+' : ℝ)'
            bound = h+' < '+f if after else f+' < '+h
            lines.append(f'''private theorem {label} {{y : ℝ → Plane}}
    (enclosed : OnClock (MirrorEndpoint.start .{e}) {back} {base}.rows y) : {bound} := by
  have within : {i} < {base}.rows.length := by change {i} < {n}; norm_num
  obtain ⟨prev,mem⟩ := enclosed.at_node within (t := {node}/64) (by norm_num)
  have original : y (clock {back} ({node}/64)) ∈
      (physicalSlab prev {cap}.row ({i}/64)).tube ({node}/64) := by with_unfolding_all exact mem
  exact {cap}.on_tube original
''')
    return ''.join(lines)


def locations_source(e, k, n, edges, parent):
    l, r = edges[0]
    u, v = edges[1]
    name = 'DommaschkOppositeMirrorLocations'+e.upper()
    text = source_start(name, ['PlasmaLean.Design.DommaschkOppositeMirrorLocalization',
                                BRANCHES+'.'+parent])
    text += 'open DommaschkOppositeMirrorLocalization DommaschkOppositeMirrorBranches\n'
    text += 'set_option linter.all false\n'
    for sign, side in [(1, 'fwd'), (-1, 'back')]:
        text += node_bounds(e, sign, n, edges, side)
    fwd = 'DommaschkArea'+e.upper()+'Fwd'
    back = 'DommaschkArea'+e.upper()+'Back'
    text += f'''theorem from_original_passage {{c : Checkpoint}} {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    {{F B : List Step}} (path : c.Passage .{e} uC zC uA zA φ)
    (angle : |φ-azimuth (MirrorEndpoint.opposite .{e})| ≤ 1/64)
    (fl : c.forwardRows.length = c.length) (bl : c.backwardRows.length = c.length)
    (f : c.forwardRows = {fwd}.rows ++ F) (b : c.backwardRows = {back}.rows ++ B)
    (room : {n} < c.length) : Located .{e} c {k} {n-1} {l} {r} {u} {v} uC zC uA zA φ := by
  obtain ⟨y,born,ode,ft,bt,branches⟩ := {parent}.from_original_passage path angle fl bl f b room
  have ef : OnClock (MirrorEndpoint.start .{e}) false c.forwardRows y := ft
  have eb : OnClock (MirrorEndpoint.start .{e}) true c.backwardRows y := bt
  refine ⟨y,born,ode,ef,eb,?_⟩
  rw [f] at ef
  rw [b] at eb
  intro clockSide
  obtain ⟨q⟩ := branches clockSide
  refine ⟨q,?_⟩
  cases clockSide
'''
    for side, enclosed in [('fwd', 'ef'), ('back', 'eb')]:
        text += f'''  · exact ⟨between q lowLevel (by norm_num) (by norm_num) ({side}LowLeft {enclosed}.prefix)
               ({side}LowRight {enclosed}.prefix),
           between q highLevel (by norm_num) (by norm_num) ({side}HighLeft {enclosed}.prefix)
               ({side}HighRight {enclosed}.prefix)⟩
'''
    return name, text+f'end PlasmaLean.Design.{name}\n', ['from_original_passage']


def attach_source(e, size, k, n, edges, signed, located):
    name = 'DommaschkOppositeOriginalBranch'+e.upper()+f'{size:03}'
    l, r = edges[0]
    u, v = edges[1]
    text = source_start(name, [LOCATIONS+'.'+located, SIGNED_PACKAGE+'.'+signed])
    text += f'''open DommaschkOppositeMirrorLocalization
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
def checkpoint : Checkpoint := ⟨{size},{signed}.forwardExit,{signed}.backwardExit,
  {signed}.forwardRows,{signed}.backwardRows⟩

theorem from_entry {{uC zC uA zA : FA}} {{φ : ℝ}} (entry : SectionEntry .{e} uC zC uA zA φ)
    (small : |φ-azimuth (MirrorEndpoint.opposite .{e})| ≤ MirrorEndpoint.width .{e}) :
    Located .{e} checkpoint {k} {n-1} {l} {r} {u} {v} uC zC uA zA φ := by
  apply {located}.from_original_passage
    (F := checkpoint.forwardRows.drop {n}) (B := checkpoint.backwardRows.drop {n})
    ({signed}.from_entry entry) (small.trans (by norm_num [MirrorEndpoint.width,MirrorEndpoint.opposite]))
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · with_unfolding_all rfl
  · change {n} < {size}
    norm_num

theorem from_original_birth :
    ∃ (uC zC uA zA : FA) (R Z : ℝ → ℝ) (C A : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate)
        (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R Z C A ∧
      ∀ φ, |φ-azimuth (MirrorEndpoint.opposite .{e})| ≤ MirrorEndpoint.width .{e} →
        Located .{e} checkpoint {k} {n-1} {l} {r} {u} {v} uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,entries⟩ := exists_nested_section_entry
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,fun φ small => from_entry (entries .{e} φ small) small⟩
end PlasmaLean.Design.{name}
'''
    return name, text, ['from_entry', 'from_original_birth']


def checked(item, parents, keys, a, package):
    overlay = merge_import_roots(a.cache/'parents', parents, keys)
    base, receipt = compile_modules(a.cache/item[0], [item], [overlay], keys, a, package)
    return {k: receipt[k] for k in ('module', 'key', 'theorems', 'axioms')} | {
        'import_paths': list(map(str, [base, overlay]))}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--branches', type=Path, required=True)
    p.add_argument('--endpoint', choices=LABELS, help='limit to one original label')
    p.add_argument('--signed', type=Path, help='attach a completed signed through-birth prefix')
    p.add_argument('--cache', type=Path, default=ROOT/'.lake/opposite-mirror-locations')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    env(a)
    branches = json.loads(a.branches.read_text())
    signed = json.loads(a.signed.read_text()) if a.signed else None
    labels = [a.endpoint] if a.endpoint else ([signed['endpoint']] if signed else LABELS)
    result = {'locations': {}, 'original_birth': {}}
    for e in labels:
        caps = list(bracket_nodes(e))
        edges = [[(lo, hi) for _, _, sign, j, lo, hi in caps if sign == s] for s in (1, -1)]
        if edges[0] != edges[1] or len(edges[0]) != 2:
            p.error('the four independent archived signs must use the specified nodes')
        packet = caps[0][1]
        k, n = edges[0][0][0], edges[0][1][1]
        if branches['packets'][e] != packet or branches['limits'][e] != [k, n]:
            p.error('the exact original packet and both signed intervals are required')
        row = branches['branches'][e]
        if row['module'] != 'DommaschkOppositeMirrorBranches'+e.upper():
            p.error('unexpected branch module')
        parents = list(map(Path, row['import_paths']))
        admitted(parents[0], row['module'], row['key'])
        keys = [a.version, packet, row['key'], digest(DESIGN/'DommaschkOppositeMirrorLocalization.trace')]
        item = locations_source(e, k, n, edges[0], row['module'])
        loc = checked(item, parents, keys, a, LOCATIONS)
        result['locations'][e] = loc | {'nodes': edges[0], 'prefix_needed': n+1, 'packet_sha256': packet}
        print(e, 'located', loc['key'], flush=True)
        if signed:
            size = signed['length_each_direction']
            expected = 'DommaschkSignedPrefix'+e.upper()+f'{size:03}'
            if (signed['endpoint'] != e or signed['packet_sha256'] != packet or size <= n
                    or signed['module'] != expected):
                p.error('the physical signed prefix must use the same original rows and extend beyond the cap')
            sr, union = Path(signed['proof_root']), Path(signed['import_path'])
            admitted(sr, expected, signed['key'])
            item = attach_source(e, size, k, n, edges[0], expected, loc['module'])
            final = checked(item, [*map(Path, loc['import_paths']), sr, union],
                            [*keys, loc['key'], signed['key']], a, PHYSICAL)
            result['original_birth'][e] = final | {'length_each_direction': size, 'signed_key': signed['key']}
            print(e, 'original birth', final['key'], flush=True)
        save(a.output, result)


if __name__ == '__main__':
    main()
