"""Prove the 16-panel Q0R478 lower action cells using its checked signed native models."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
from types import SimpleNamespace

from bounce_mirror_pilot import HEIGHTS
from emit_action_quadrature import TARGET
from screen_action_panel_resolution import PACKED, endpoint_inputs
from verify_backward_physical_prefix import compile_modules, union
from verify_coarse_action_models import env
from verify_coarse_physical_action import PACKAGE, TICKS, cell, tick_modules
from verify_mirror_physical_hit import admitted
from verify_native_action_columns import physical_models
import verify_native_action_models as native
from verify_paired_action_profiles import native_provider
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save
from verify_signed_mirror_passage import merge_import_roots


def panels(word):
    """Recover the sixteen coarse digits, checking each of their three chronological copies."""
    result = []
    for _ in range(16):
        digit = word % (1 << 72)
        for _ in range(3):
            if word % (1 << 72) != digit:
                raise ValueError('the 48 chronological cells do not repeat in triples')
            word >>= 72
        result.append(digit)
    if word:
        raise ValueError('extra high digits in a coarse lower action slab')
    return result


def packet_inputs(path):
    pack = json.loads(path.read_text())
    upper, height, counts, _, traces, trace_key, original_key = endpoint_inputs('q0r478')
    if (pack['endpoint'], pack['module'], pack['package'], pack['upper'], pack['splits'],
            pack['height'], pack['counts'], pack['packet_sha256'], pack['action_sha256']) != (
            'q0r478', 'DommaschkCoarseActionQ0R478N16', 'CoarseActionPacketCache', upper, 16,
            str(height), counts, trace_key, original_key):
        raise ValueError('expected the authenticated Q0R478 16-panel lower action packet')
    root = Path(pack['import_paths'][0])
    admitted(root, pack['module'], pack['key'])
    source = root / pack['package'] / (pack['module'] + '.lean')
    blocks = [(int(w,16),int(m)) for w,m in PACKED.findall(source.read_text())]
    if len(blocks) != sum(counts) or upper or height != HEIGHTS[1]:
        raise ValueError('invalid signed block count, comparison or physical height')
    for f,b in zip(blocks[counts[0]:], reversed(blocks[:counts[0]]), strict=True):
        if panels(f[0]) != panels(b[0])[::-1] or f[1] != b[1]:
            raise ValueError('forward and reversed backward coarse digits differ')
    mass = 0
    for n in range(1,counts[0]+1):
        mass += blocks[counts[0]-n][1]+blocks[counts[0]+n-1][1]
        if Fraction(mass,3072*2**40) > TARGET:
            break
    else:
        raise ValueError('the complete coarse interior misses the lower target')
    return pack, root, traces, blocks, n, Fraction(mass,3072*2**40)


def signed_source(i, sign, packet, model, atom, block):
    name, source, audit = cell('q0r478', i, sign, packet, model, atom, *block)
    if sign < 0:
        # The shared model separately proves the true backward tube at the negative clock.
        for original, replacement in [('row','backRow'), ('physical ht hx','backward_physical ht hx')]:
            needle = f'{model}.{original}'
            if source.count(needle) != 1:
                raise ValueError('could not bind the unique backward field declaration')
            source = source.replace(needle, f'{model}.{replacement}')
    return name, source, audit


def verify(i, a, pack, root, traces, blocks, data, static):
    fields, _, _, checksum = native_provider(a, i, 478, data, static)
    common_model = fields[-1][1]
    cap = max(t['steps'][i]['physical_radius_out'] for t in traces)
    values = physical_models(traces[1], i, cap)
    center = pack['counts'][0]
    raw = sum(digit << (72*j) for j,digit in enumerate(panels(blocks[center+i][0])))
    atom = f'DommaschkCoarseSharedLowerQ0R478{i:03}N16'
    deps = [a.version, checksum, pack['key'], digest(DESIGN.parent/'Certificates/CoarseActionCells.trace')]
    tb, tr = compile_modules(a.cell_cache/atom,
        tick_modules(atom, values, HEIGHTS[1], False, 16, raw, False), [], deps, a, TICKS)
    keys = [*deps, common_model['key'], tr['key']]
    field_path = union(a.cell_cache, [*static,*fields])
    overlay = merge_import_roots(a.cell_cache, [root,tb,field_path], keys)
    signed = []
    for sign, j in [(1,center+i),(-1,center-1-i)]:
        decl = signed_source(i, sign, pack, common_model['module'], atom, blocks[j])
        leaf,r = compile_modules(a.cell_cache/decl[0], [decl], [overlay], keys, a, PACKAGE)
        out = {k:r[k] for k in ['module','key','axioms','theorems','wall_seconds','peak_rss_kib']}
        out.update(endpoint='q0r478',index=i,direction=sign,upper=False,height=pack['height'],
            splits=16,coarse_packet=pack['key'],packet_sha256=checksum,model=common_model['key'],
            ticks=tr['key'],tick_seconds=tr['wall_seconds'],chronological_block=j,mass=blocks[j][1],
            expanded_hex=hex(blocks[j][0]),import_paths=[str(leaf),str(overlay)])
        signed.append(out)
        print(out['module'],out['key'],flush=True)
    save(a.cell_cache/'rows'/f'{i:03}.json', signed)
    return signed


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--rows',type=int,nargs='+',required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/paired-action-profiles')
    p.add_argument('--model-cache',type=Path,default=ROOT/'.lake/native-action-checks')
    p.add_argument('--cell-cache',type=Path,default=ROOT/'.lake/coarse-secondary-lower')
    a=p.parse_args()
    if len(a.rows)!=len(set(a.rows)) or any(not 0<=i<327 for i in a.rows):
        p.error('choose distinct indices from 0 through 326')
    packet,root,traces,blocks,n,mass=packet_inputs(a.packet)
    print('first target-crossing symmetric length',n,'mass',mass,flush=True)
    env(a)
    data=native.static_data()
    static=native.verify_static(SimpleNamespace(**{**vars(a),'cache':a.model_cache,'fields':range(4)}),data)
    (a.cell_cache/'rows').mkdir(parents=True,exist_ok=True)
    rows=[]
    for i in a.rows:
        rows.extend(verify(i,a,packet,root,traces,blocks,data,static))
        save(a.output,rows)


if __name__=='__main__':
    main()
