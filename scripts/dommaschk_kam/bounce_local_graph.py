"""Check an endpoint of a local radial graph bracket at either symmetry phase.

Both actions are enclosed by directed arithmetic over the entire phase interval.
The relevant height and required inequality depend on the radius. A separate
tangent cover of the whole radial bracket supplies uniqueness of its crossing.
"""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path

from bounce_action_pilot import TARGET, enclose_action
from bounce_common_section import common_section_inputs
from bounce_mirror_pilot import HEIGHTS, SCALE
from bounce_phase_frame import check_frame, framed_segments
from bounce_phase_strength import ShiftedStrength, check_shifted_strength
from bounce_screen import FIELD_FILE_SHA, SEEDS


# At the upper height the root has smaller radius.
BRACKETS = {
    0: ((F('.523'), F('.531')), (F('.470'), F('.478'))),
    1: ((F('.509'), F('.517')), (F('.456'), F('.464'))),
}


def endpoint(u, width, dt, panels, section=0):
    index, bracket = next((i, pair) for i, pair in enumerate(BRACKETS[section]) if u in pair)
    inputs, transfer = common_section_inputs(width, F(0), u, section)
    check_frame()
    check_shifted_strength()
    record = enclose_action(inputs, dt, panels, F(0), F(49, 8), ShiftedStrength(inputs[0]),
                            segment_builder=framed_segments)
    lower, upper = map(F, record['action_bounds'][index])
    margin = TARGET-upper if u == bracket[0] else lower-TARGET
    record.pop('straddles')
    record.update(launch_radius=str(u), section_in_half_pi=section,
                  phase_half_width=str(width), transfer=transfer,
                  bracket=list(map(str, bracket)), height_index=index, signed_margin=str(margin))
    return record


def check_record(path):
    """Compose the stored one-sided signs with the independently checked, gapless slope cover."""
    from bounce_radial_tube import merge_tile_rows
    packet = json.loads(path.read_text())
    sections = packet['sections']
    if [row['section_in_half_pi'] for row in sections] != [0, 1]:
        raise ValueError('both symmetry sections are required, once each')
    if (packet['trajectory_denominator'] != SCALE or packet['field_file_sha256'] != FIELD_FILE_SHA or
            packet['seed_sha256'] != {tag: value[1] for tag, value in SEEDS.items()}):
        raise ValueError('unexpected field or launch seeds')
    summaries = []
    for row in sections:
        section = row['section_in_half_pi']
        source = json.loads((path.parent / row['tangent_cover']).read_text())
        tiles = [tile for bracket in source['brackets'] for tile in bracket['tiles']]
        cover = merge_tile_rows(tiles)
        if (cover != source or cover['section_in_half_pi'] != section or
                cover['field_file_sha256'] != packet['field_file_sha256'] or
                cover['seed_sha256'] != packet['seed_sha256']):
            raise ValueError('inconsistent radial cover, section or candidate')
        phase_width = F(cover['alpha_half_width'])
        endpoints = row['endpoints']
        if sorted(F(e['launch_radius']) for e in endpoints) != sorted(sum(BRACKETS[section], ())):
            raise ValueError('four distinct bracket endpoints required')
        margins = []
        for entry in endpoints:
            i = entry['height_index']
            if i not in (0, 1):
                raise ValueError('unknown mirror height')
            r = F(entry['launch_radius'])
            bracket = BRACKETS[section][i]
            if (entry['section_in_half_pi'] != section or
                    not 0 < phase_width <= F(entry['phase_half_width'])
                    or tuple(map(F, entry['bracket'])) != bracket or r not in bracket
                    or list(map(F, entry['heights'])) != list(HEIGHTS) or F(entry['target']) != TARGET):
                raise ValueError('endpoint source and tangent cover disagree')
            B = entry['transfer']
            if (F(B['B_upper_numerator'], B['denominator']) >= HEIGHTS[0] or
                    B['Bphi_lower_numerator'] <= 0):
                raise ValueError('transfer leaves the allowed well')
            if [c['direction'] for c in entry['crossings']] != [-1, 1]:
                raise ValueError('missing one side of a well')
            for c in entry['crossings']:
                if (not c['success'] or len(c['brackets']) != 2 or c['band_slope_lower_numerator'] <= 0 or
                        any(not 0 < F(l) <= F(h) <= F(cover['limit']) for l, h in c['brackets'])):
                    raise ValueError('endpoint was not enclosed on the shared regular trace')
            lower, upper = map(F, entry['action_bounds'][i])
            margin = TARGET-upper if r == bracket[0] else lower-TARGET
            if lower > upper or not margin > 0 or margin != F(entry['signed_margin']):
                raise ValueError('endpoint action failed to separate the target')
            margins.append(margin)
        summary = dict(section_in_half_pi=section, phase_half_width=str(phase_width),
                       action_margin=str(min(margins)),
                       secants=[b['radial_action_secant_lower'] for b in cover['brackets']],
                       radius_separation=str(BRACKETS[section][0][0]-BRACKETS[section][1][1]))
        summaries.append(summary)
    return summaries


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--u', type=F)
    mode.add_argument('--check-record', type=Path, help='recheck both stored graph certificates')
    parser.add_argument('--section', type=int, choices=[0, 1], default=0)
    parser.add_argument('--alpha-half-width', type=F, default=F(1, 32768))
    parser.add_argument('--step', type=F, default=F(1, 64))
    parser.add_argument('--panels', type=int, default=48)
    args = parser.parse_args()
    if args.check_record:
        print(json.dumps(check_record(args.check_record), indent=2))
        raise SystemExit(0)
    if args.u not in sum(BRACKETS[args.section], ()):
        parser.error('the selected radius is not a bracket endpoint at this section')
    record = endpoint(args.u, args.alpha_half_width, args.step, args.panels, args.section)
    print(json.dumps(record, indent=2))
    if F(record['signed_margin']) <= 0:
        raise SystemExit('the action enclosure did not resolve the required endpoint sign')
