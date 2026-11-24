"""Incrementally cover the original action archive on one physical trajectory; reuse each accepted subtree."""

import argparse
import json
from pathlib import Path
import subprocess
import time
from types import SimpleNamespace

from emit_sparse_taylor_slab import RECORD, ROOT
from verify_backward_physical_prefix import compile_modules
from verify_mirror_physical_hit import admitted
from verify_native_action_birth import PACKAGE, cellref, cover_source, geometry
from verify_physical_trace_slabs import DESIGN, digest, save
from verify_signed_mirror_passage import merge_import_roots


ARC_PACKAGE = 'NativeActionArcCache'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--paired',type=Path,required=True)
    p.add_argument('--blocks',nargs=2,type=int,default=(0,650),metavar=('FIRST','STOP'))
    p.add_argument('--row-cache',type=Path,default=ROOT/'.lake/native-path-cells')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/native-archive-tree')
    p.add_argument('--poll-seconds',type=float,default=15)
    p.add_argument('--progress',type=Path)
    p.add_argument('--output',type=Path,required=True)
    args = p.parse_args()
    pair = json.loads(args.paired.read_text())
    n = pair['slabs_per_direction']
    left,right = args.blocks
    if not 0 <= left < right <= 650 or args.poll_seconds <= 0:
        p.error('select a nonempty interval of original archive blocks and a positive polling interval')
    indices = sorted({cellref(j)[0] for j in range(left,right)})
    if indices[-1]+1 >= n:
        p.error('the signed trajectory must extend past the two closed block edges')
    packet = digest(RECORD)
    if pair['packet_sha256'] != packet or pair['module'] != f'DommaschkPairedPrefix{n:03}':
        raise ValueError('expected the physical signed prefix for this pilot')
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    env = SimpleNamespace(lean=str(Path(lake('lean','--print-prefix'))/'bin/lean'),lean_path=lake('printenv','LEAN_PATH'))
    inputs = [lake('lean','--version'),packet,digest(DESIGN/'DommaschkPhysicalArcTrace.trace'),
              digest(DESIGN.parent/'Certificates/MirrorActionBlockBounds.trace')]
    pair_dirs = list(map(Path,pair['import_paths']))
    admitted(pair_dirs[0],pair['module'],pair['key'])
    trajectory = merge_import_roots(args.cache/'trajectory',pair_dirs,[*inputs,pair['key']])
    branches = {}
    def plan(l,r):
        kids = []
        if r-l > 8:
            mid = (l+r)//2
            kids = [plan(l,mid),plan(mid,r)]
        branches[l,r] = kids
        return l,r
    final = plan(left,right)
    rows,nodes = {},{}
    def progress():
        if args.progress:
            save(args.progress, {'range':[left,right], 'trajectory':pair['key'],
                  'geometric_rows':len(rows),'accepted_tree_nodes':len(nodes),
                  'total_tree_nodes':len(branches),'complete':final in nodes})
    while final not in nodes:
        changed = False
        for i in indices:
            if i in rows:
                continue
            marker = args.row_cache/'paired-rows'/f'{i:03}.json'
            if not marker.is_file():
                continue
            report = json.loads(marker.read_text())
            if report['module'] != f'DommaschkNativePathCellsPaired{i:03}' or report['packet_sha256'] != packet:
                raise ValueError(f'wrong native signed cell prototype for index {i}')
            deps = list(map(Path,report['import_paths']))
            admitted(deps[0],report['module'],report['key'])
            decl = geometry(i)
            base,result = compile_modules(args.cache/decl[0],[decl],deps,[ARC_PACKAGE,*inputs,report['key']],env,ARC_PACKAGE)
            rows[i] = ({**result,'package':ARC_PACKAGE},[base,*deps])
            changed = True
            progress()
        for (l,r),children in branches.items():
            if (l,r) in nodes:
                continue
            parents = []
            descriptor = None
            if children:
                if not all(c in nodes for c in children):
                    continue
                parents = [nodes[c] for c in children]
                descriptor = [(record['module'],b-a) for (record,_),(a,b) in zip(parents,children,strict=True)]
            else:
                needed = sorted({cellref(j)[0] for j in range(l,r)})
                if not all(i in rows for i in needed):
                    continue
                parents = [rows[i] for i in needed]
            keys = [*inputs,pair['key'],*[rec['key'] for rec,_ in parents]]
            overlay = merge_import_roots(args.cache/'subtrees',[p for _,ds in parents for p in ds],keys)
            name,source,theorems = cover_source(n,l,r,descriptor)
            for parent,_ in parents:
                expected = f'public import {PACKAGE}.{parent["module"]}\n'
                if expected not in source:
                    raise ValueError(f'{name} is missing its parent {parent["module"]}')
                source = source.replace(expected,f'public import {parent["package"]}.{parent["module"]}\n')
            # Different layers use different Lean packages so that elaboration never
            # shadows a sibling while a new object is being written.
            dest = PACKAGE if (l,r) == final else f'NativeActionTree{r-l:03}Cache'
            base,result = compile_modules(args.cache/name,[(name,source,theorems)],[overlay,trajectory],
                                          [dest,*keys],env,dest)
            nodes[l,r] = ({**result,'package':dest},[base,overlay])
            print(f'original blocks [{l},{r}) accepted {result["key"]}',flush=True)
            changed = True
            progress()
        if not changed:
            time.sleep(args.poll_seconds)
    rec,paths = nodes[final]
    out = {k:v for k,v in rec.items() if k != 'artifacts'}
    out.update(packet_sha256=packet,paired=pair['key'],length=n,block_range=[left,right],
               physical_cells=48*(right-left),import_paths=list(map(str,[*paths,trajectory])))
    save(args.output,out)


if __name__ == '__main__':
    main()
