"""Join signed 470/478 comparison receipts over a consecutive angular interval."""
import argparse
import json
from pathlib import Path
import subprocess
import time

from verify_backward_physical_prefix import compile_modules
from verify_compared_trace_prefix import block_source, row_data
from verify_mirror_endpoint_signs import header
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_secondary_mirror_caps import load
from verify_signed_mirror_passage import merge_import_roots


BLOCKS = 'GroupedProfileIntervalBlocks'
PACKAGE = 'GroupedProfileIntervalCache'


class IncompleteCoverage(ValueError):
    """An active producer has not yet supplied every requested index."""


def interval_source(start,stop,rows,blocks):
    name = f'DommaschkComparedInterval{start:03}To{stop:03}'
    src = header(name,[BLOCKS+'.'+b for b in blocks])
    src += 'open Certificates.PositionFrameSlabs DommaschkPairedActionProfiles Set\n'
    proofs = []
    for sign,tag in enumerate(('forward','backward')):
        rel = 'Compared' if not sign else '(fun t => Compared (-t))'
        inner,outer = [list(x) for x in zip(*(r[2][sign] for r in rows),strict=True)]
        for side,items in [('Inner',inner),('Outer',outer)]:
            src += f'def {tag}{side} : List Step := [\n  '+',\n  '.join(items)+']\n'
        src += f'''theorem {tag}_append {{a b : State}} {{xs zs : List Step}}
    (tail : OnPairedTubes {rel} (next {inner[-1]}) (next {outer[-1]})
      ((({stop}:ℕ):ℝ)/64) xs zs) :
    OnPairedTubes {rel} a b ((({start}:ℕ):ℝ)/64) ({tag}Inner ++ xs) ({tag}Outer ++ zs) := by
'''
        for j in reversed(range(len(blocks))):
            prev = ['a','b'] if j==0 else ['next '+x for x in rows[8*j-1][2][sign]]
            suffix = 'tail' if j+1 == len(blocks) else f'h{j+1}'
            src += f'  have h{j} := {blocks[j]}.{tag} (a := {prev[0]}) (b := {prev[1]}) {suffix}\n'
        src += f'''  exact h0

theorem {tag} (a b : State) :
    OnPairedTubes {rel} a b ((({start}:ℕ):ℝ)/64) {tag}Inner {tag}Outer := by
  simpa only [List.append_nil] using {tag}_append (a := a) (b := b) (xs := []) (zs := []) (by trivial)

theorem {tag}_on_paths {{a b : State}} {{x y : ℝ → Plane}} {{xs zs : List Step}}
    (hi : ∀ u ∈ physicalSlabs a ((({start}:ℕ):ℝ)/64) ({tag}Inner ++ xs),
      ∀ t ∈ Icc u.start u.stop, x t ∈ u.tube t)
    (ho : ∀ u ∈ physicalSlabs b ((({start}:ℕ):ℝ)/64) ({tag}Outer ++ zs),
      ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t) :
    ∀ t ∈ Icc ({start}/64:ℝ) ({stop}/64), Compared {('t' if not sign else '(-t)')} (x t) (y t) := by
  have result := ({tag} a b).on_nonempty_prefix (by intro eq; cases eq) hi ho
  rw [show {tag}Inner.length = {stop-start} by rfl] at result
  norm_num at result ⊢
  exact result
'''
        proofs.extend([tag+'_append',tag,tag+'_on_paths'])
    src += f'''
theorem signed_on_paths {{fi fo bi bo : State}} {{x y : ℝ → Plane}}
    {{fx fy bx by_ : List Step}}
    (fI : ∀ u ∈ physicalSlabs fi ((({start}:ℕ):ℝ)/64) (forwardInner ++ fx),
      ∀ t ∈ Icc u.start u.stop, x t ∈ u.tube t)
    (fO : ∀ u ∈ physicalSlabs fo ((({start}:ℕ):ℝ)/64) (forwardOuter ++ fy),
      ∀ t ∈ Icc u.start u.stop, y t ∈ u.tube t)
    (bI : ∀ u ∈ physicalSlabs bi ((({start}:ℕ):ℝ)/64) (backwardInner ++ bx),
      ∀ t ∈ Icc u.start u.stop, x (-t) ∈ u.tube t)
    (bO : ∀ u ∈ physicalSlabs bo ((({start}:ℕ):ℝ)/64) (backwardOuter ++ by_),
      ∀ t ∈ Icc u.start u.stop, y (-t) ∈ u.tube t) :
    (∀ θ ∈ Icc ({start}/64:ℝ) ({stop}/64), Compared θ (x θ) (y θ)) ∧
    (∀ θ ∈ Icc (-({stop}/64):ℝ) (-({start}/64)), Compared θ (x θ) (y θ)) := by
  refine ⟨forward_on_paths fI fO, ?_⟩
  intro θ ht
  have inside : -θ ∈ Icc ({start}/64:ℝ) ({stop}/64) :=
    ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
  simpa only [neg_neg] using backward_on_paths (x := fun t => x (-t))
    (y := fun t => y (-t)) bI bO (-θ) inside
'''
    proofs.append('signed_on_paths')
    return name,src+f'\nend PlasmaLean.Design.{name}\n',proofs


def reports(paths,first,last,packets):
    by_index = {}
    inputs = []
    for path in paths:
        if not path.exists():
            raise IncompleteCoverage(f'awaiting group report {path}')
        d = json.loads(path.read_text())
        if 'module' in d:
            inputs.append(d)
        else:
            if d['packets'] != packets:
                raise ValueError(f'wrong source packets in {path}')
            if d.get('errors'):
                raise ValueError(f'group producer failed: {d["errors"]}')
            for info in d['groups']:
                group = json.loads(Path(info['receipt']).read_text())
                if any(info[k]!=group[k] for k in ('start','stop','key')):
                    raise ValueError(f'wrong group receipt {info["receipt"]}')
                inputs.append(group)
    for d in inputs:
        if d['packets'] != packets:
            raise ValueError('expected the two original physical witness digests')
        lo,hi = d['start'],d['stop']
        expected = f'DommaschkGroupedProfile{lo:03}To{hi:03}Rows'
        if not 236 <= lo < hi <= 325 or d['module'] != expected:
            raise ValueError('invalid original signed group range')
        for i in range(max(lo,first),min(hi,last)):
            if i in by_index and d['key']!=by_index[i]['key']:
                raise ValueError(f'different signed groups at row {i}')
            by_index[i] = d
    missing = [i for i in range(first,last) if i not in by_index]
    if missing:
        raise IncompleteCoverage(f'missing {len(missing)} signed row pairs, starting at {missing[0]}')
    for d in {r['key']:r for r in by_index.values()}.values():
        admitted(Path(d['import_paths'][0]),d['module'],d['key'])
    return [by_index[i] for i in range(first,last)]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--reports',nargs='+',type=Path,required=True,help='signed group receipts or campaign manifests')
    p.add_argument('--range',nargs=2,type=int,default=(236,325),metavar=('FIRST','STOP'))
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--wait-seconds',type=int,default=0,help='wait for unfinished group campaigns')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/grouped-profile-intervals')
    args = p.parse_args()
    first,stop = args.range
    if not 236<=first<stop<=325:
        p.error('choose a nonempty subset of the hard suffix [236,325)')
    packets = [digest(load(k)[1]) for k in (470,478)]
    if args.wait_seconds<0:
        p.error('the waiting time must be nonnegative')
    deadline = time.monotonic()+args.wait_seconds
    while True:
        try:
            checked = reports(args.reports,first,stop,packets)
            break
        except IncompleteCoverage as exc:
            remaining = deadline-time.monotonic()
            if remaining<=0:
                raise
            print(exc,flush=True)
            time.sleep(min(30,remaining))
    rows = [row_data(d,i,packets) for i,d in enumerate(checked,first)]
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],text=True,cwd=ROOT).strip()
    args.lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    args.lean_path = lake('printenv','LEAN_PATH')
    cache = args.cache.resolve()
    common = [packets,lake('lean','--version'),digest(DESIGN/'DommaschkComparedTracePrefixes.trace')]
    def check(item,parents,package):
        unique = {d['key']:d for d in parents}
        paths = [Path(x) for d in unique.values() for x in d['import_paths']]
        overlay = merge_import_roots(cache,paths,list(unique))
        root,rec = compile_modules(cache/item[0],[item],[overlay],[package,common,list(unique)],args,package)
        out = {k:v for k,v in rec.items() if k!='artifacts'}
        return {**out,'import_paths':[str(root),str(overlay)]}
    blocks = []
    for offset in range(0,stop-first,8):
        canonical,src,thms = block_source(first+offset,rows[offset:offset+8])
        block = canonical.replace('ComparedRows','GroupedComparedRows')
        item = block,src.replace('PlasmaLean.Design.'+canonical,'PlasmaLean.Design.'+block),thms
        blocks.append(check(item,checked[offset:offset+8],BLOCKS))
    item = interval_source(first,stop,rows,[d['module'] for d in blocks])
    result = check(item,blocks,PACKAGE)
    result.update(start=first,stop=stop,packets=packets,
                  groups=list(dict.fromkeys(d['key'] for d in checked)))
    save(args.output,result)
    print(result['module'],result['key'],flush=True)


if __name__=='__main__':
    main()
