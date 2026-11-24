"""Screen archived spatial Jacobians on the coordinate projections of each trial ball."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from math import isqrt
from pathlib import Path

from bounce_mirror_pilot import Model
from bounce_phase_frame import FRAME_SCALE
from emit_sparse_taylor_slab import DATA, RECORD
from screen_reflected_jacobians import paired
from screen_sparse_jacobians import evaluate_box, jobs, split_coordinate


def projected_radii(left, right, trial):
    """Smallest dyadic radii that cover both endpoint row projections of the ball."""
    radii = []
    for a, b in zip(left, right, strict=True):
        square = trial**2 * max(sum(x*x for x in a), sum(x*x for x in b))
        radius = isqrt(square) // FRAME_SCALE
        radii.append(radius + int((radius * FRAME_SCALE)**2 < square))
    return tuple(radii)


def classify(job):
    section, sign, index, start, step, panels, _ = job
    radii = projected_radii(start, step['frame_end'], step['frame_trial_radius'])
    r, z = (Model(p, e) for p, e in zip(step['coefficients'], radii, strict=True))
    args = section, sign, index, start, step, panels
    whole, time = evaluate_box(*args, r, z)
    if whole:
        return 'whole'
    if time:
        return 'time'
    for radial, vertical in ((1, 2), (2, 1), (2, 2), (1, 4), (4, 1), (4, 4)):
        if all(evaluate_box(*args, x, y)[1]
               for x in split_coordinate(r, radial) for y in split_coordinate(z, vertical)):
            return f'{radial}x{vertical}'
    return 'unresolved'


def projected_jobs(path, sign, reflected):
    if reflected:
        back = {job[2]: job[4]['frame_trial_radius']
                for job in jobs(path, 8, False, 4) if job[1] == -1}
        for job, _, _ in paired(path):
            step = job[4]
            radius = max(step['frame_trial_radius'], back[job[2]])
            yield (*job[:4], {**step, 'frame_trial_radius': radius}, *job[5:])
    else:
        yield from (job for job in jobs(path, 8, False, 4) if job[1] == sign)


def screen(path, sign, reflected):
    counts = Counter()
    refined = {}
    for job in projected_jobs(path, sign, reflected):
        method = classify(job)
        counts[method] += 1
        if method != 'whole':
            refined.setdefault(method, []).append(job[2])
    return {'source': path.name, 'packet_sha256': sha256(path.read_bytes()).hexdigest(),
            'field_sha256': sha256(DATA.read_bytes()).hexdigest(), 'direction': sign,
            'reflected_pair': reflected, 'time_panels': 8, 'counts': dict(counts),
            'refined_rows': refined}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('packet', nargs='?', type=Path, default=RECORD)
    parser.add_argument('--direction', type=int, choices=(-1, 1), default=1)
    parser.add_argument('--reflected', action='store_true',
                        help='cover both section-zero trials at the stricter signed budget')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    if args.reflected and args.direction != 1:
        parser.error('paired screening evaluates the positive section-zero representative')
    report = json.dumps(screen(args.packet, args.direction, args.reflected), indent=2) + '\n'
    if args.check and args.check.read_text() != report:
        raise SystemExit('projected Jacobian screen differs from exact replay')
    if args.output:
        args.output.write_text(report)
    print(report, end='')
