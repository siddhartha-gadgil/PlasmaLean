"""Test finite parallel-speed thresholds on the eight archived N-60 action endpoints.

The packet's density and speed are directed bounds on each time panel. The
result keeps that direction when replacing the speed integral by endpoint sums
of the sublevel arclengths. It compares proposed arclength certificates only.
"""
from bisect import bisect_left
from collections import Counter
from fractions import Fraction
import heapq
from pathlib import Path
import re


DESIGN = Path(__file__).resolve().parents[2] / "PlasmaLean" / "Design"
DIGIT = 2**24
SCALE = 2**20
GAP_SCALE = 2**26
PANELS = 48
DENOMINATOR = 64 * PANELS * SCALE**2
# A nonnegative field magnitude and h ≤ 2 imply a parallel speed at most 2.
MAX_SPEED = 2 * SCALE
PACKET = re.compile(r"theorem checked : Packet (true|false) slabs (\d+) (\d+)\s+(\d+) (\d+)")
SLAB = re.compile(r"⟨0x([0-9a-f]+), (\d+), rfl⟩")


def extract(path):
    source = path.read_text()
    header, = PACKET.findall(source)
    sign, left, right, num, den = header
    upper = sign == "true"
    target = Fraction(int(num), int(den))
    rows = SLAB.findall(source)
    if len(rows) != int(left) + int(right):
        raise ValueError(f"{path.name}: slab count")
    weights = Counter()
    for encoded, expected in rows:
        packet = int(encoded, 16)
        mass = 0
        for _ in range(PANELS):
            density = packet % DIGIT
            gap = (packet >> 24) % DIGIT
            speed = (packet >> 48) % DIGIT
            packet >>= 72
            square = speed**2 * GAP_SCALE
            threshold = gap * SCALE**2
            invalid_square = square < threshold if upper else threshold < square
            if invalid_square or speed > MAX_SPEED:
                raise ValueError(f"{path.name}: invalid speed witness")
            mass += density * speed
            weights[speed] += density
        if packet or mass != int(expected):
            raise ValueError(f"{path.name}: corrupt slab mass")
    return upper, target, weights


def grid_bound(weights, width, upper):
    # At a left endpoint the closed superlevel set includes a speed equal to
    # that endpoint. At zero, counting the entire bracket is conservative.
    mass = 0
    for speed, density in weights.items():
        grid_speed = (speed // width) * width
        if upper:
            grid_speed = min(MAX_SPEED, grid_speed + width)
        mass += density * grid_speed
    return Fraction(mass, DENOMINATOR)


def first_uniform_grid(weights, upper, target):
    for exponent in range(MAX_SPEED.bit_length()):
        panels = 2**exponent
        bound = grid_bound(weights, MAX_SPEED // panels, upper)
        margin = target - bound if upper else bound - target
        if margin > 0:
            return panels, margin
    raise ValueError("target still unresolved at the source speed resolution")


def adaptive_grid(weights, upper, target):
    """Bisect the cell with the largest gap between its endpoint rectangles."""
    speeds = sorted(weights)
    tails = [0] * (len(speeds) + 1)
    for i in reversed(range(len(speeds))):
        tails[i] = tails[i + 1] + weights[speeds[i]]

    def tail(v):
        return tails[bisect_left(speeds, v)]

    heap = []

    def cell(a, b):
        width = b - a
        lower, higher = width * tail(b), width * tail(a)
        if width > 1 and lower < higher:
            heapq.heappush(heap, (lower - higher, a, b))
        return higher if upper else lower

    edges = {0, MAX_SPEED}
    mass = cell(0, MAX_SPEED)
    while True:
        bound = Fraction(mass, DENOMINATOR)
        margin = target - bound if upper else bound - target
        if margin > 0:
            nodes = sorted(edges)
            total = sum((b - a) * tail(a if upper else b) for a, b in zip(nodes, nodes[1:]))
            if total != mass:
                raise ArithmeticError("adaptive endpoint sums disagree")
            return len(nodes) - 1, margin
        if not heap:
            raise ValueError("adaptive mesh exhausted at source resolution")
        _, a, b = heapq.heappop(heap)
        mid = (a + b) // 2
        edges.add(mid)
        old = (b - a) * tail(a if upper else b)
        mass += cell(a, mid) + cell(mid, b) - old


if __name__ == "__main__":
    files = sorted(DESIGN.glob("DommaschkActionQ[01]R[0-9][0-9][0-9].lean"))
    if len(files) != 8:
        raise ValueError("expected exactly eight archived endpoint packets")
    for path in files:
        upper, target, weights = extract(path)
        exact = Fraction(sum(s * w for s, w in weights.items()), DENOMINATOR)
        exact_margin = target - exact if upper else exact - target
        if exact_margin <= 0:
            raise ValueError(f"{path.name}: original target comparison failed")
        uniform, _ = first_uniform_grid(weights, upper, target)
        adaptive, margin = adaptive_grid(weights, upper, target)
        side = "upper" if upper else "lower"
        print(f"{path.stem} {side} uniform={uniform} adaptive={adaptive} margin={margin}")
