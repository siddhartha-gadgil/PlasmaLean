"""Check both chronological action records against one enlarged, reflected physical tube per slab."""
import argparse
from dataclasses import replace
import gzip
import json
from pathlib import Path

from bounce_mirror_pilot import HEIGHTS, polynomial_data
from bounce_phase_strength import ShiftedStrength
from emit_action_quadrature import panel_row
from emit_sparse_taylor_slab import RECORD
from replay_physical_action_archive import segment
from screen_physical_action_panels import packed_rows
from verify_physical_trace_slabs import digest, save


def digits(word, index):
    return tuple((word >> (72*index + 24*k)) % (1 << 24) for k in range(3))


def screen():
    trace = json.loads(gzip.decompress(RECORD.read_bytes()))
    if (trace['section_in_half_pi'], trace['launch_u'], trace['step']) != (0, '47/100', '1/64'):
        raise ValueError('unexpected source trajectory')
    back, fwd = sorted(trace['traces'], key=lambda t: t['direction'])
    if (back['direction'], fwd['direction']) != (-1, 1):
        raise ValueError('expected both directions')
    data = polynomial_data()
    compensated = ShiftedStrength(data)
    original = packed_rows()
    if len(original) != 650:
        raise ValueError('incorrect number of signed blocks')
    strict = [[0]*3 for _ in range(2)]
    equal_blocks = 0
    for i in range(325):
        r, z = fwd['steps'][i]['coefficients']
        if back['steps'][i]['coefficients'] != [r, [-v for v in z]]:
            raise ValueError(f'row {i}: reflected position polynomials differ')
        nominal = segment(fwd, i)
        radius = max(nominal.outgoing_radius, back['steps'][i]['physical_radius_out'])
        paired = replace(nominal, outgoing_radius=radius)
        packed, _ = panel_row(paired, data, compensated, HEIGHTS[1], True, 48)
        for side, index in enumerate((325+i, 324-i)):
            all_equal = True
            for k in range(48):
                actual = digits(packed, k)
                stored = digits(original[index], k if side == 0 else 47-k)
                for j, (a, b) in enumerate(zip(actual, stored, strict=True)):
                    if a > b:
                        raise ValueError(f'slab {index}, normalized panel {k}, column {j}: {a} > {b}')
                    if a < b:
                        strict[side][j] += 1
                        all_equal = False
            equal_blocks += all_equal
    return {'source_sha256': digest(RECORD), 'height': str(HEIGHTS[1]), 'signed_blocks': 650,
            'cells': 31200, 'columns_dominated': 93600, 'identical_blocks': equal_blocks,
            'strictly_smaller_ticks': dict(zip(('forward', 'backward'), strict)),
            'columns': ['density', 'squared_speed', 'speed']}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = screen()
    print(json.dumps(result))
    if args.output:
        save(args.output, result)
