"""Build both signed native action-model theorems for every requested index, with bounded resources."""
import argparse
from collections import deque
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from copy import copy
import json
import math
import os
from pathlib import Path
import subprocess
import time

from emit_sparse_taylor_slab import ROOT
from verify_native_action_models import manifest, static_data, verify_row, verify_static
from verify_physical_trace_slabs import save
from verify_sparse_reference_slabs import GIB, available_ram


def cpus():
    # /proc/stat includes guest ticks twice when all columns are summed.
    ticks = list(map(int, Path('/proc/stat').read_text().splitlines()[0].split()[1:9]))
    return sum(ticks), ticks[3]


def check_row(args, data, static, i):
    a = copy(args)
    a.row = i
    values = verify_row(a, data, static)
    report = manifest(a, static, values)
    path = a.cache/'paired-rows'/f'{i:03}.json'
    save(path, report)
    return {'index': i, 'manifest': str(path.resolve()), 'key': values[-1][1]['key']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--range', nargs=2, type=int, default=(0, 324), metavar=('FIRST', 'LAST'))
    parser.add_argument('--workers', type=int, default=10, choices=range(1, 25))
    parser.add_argument('--baseline', type=int, default=2)
    parser.add_argument('--reserve-gib', type=int, default=32)
    parser.add_argument('--reserve-cores', type=int, default=2)
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/native-action-checks')
    parser.add_argument('--output', type=Path, required=True)
    a = parser.parse_args()
    if not 0 <= a.range[0] <= a.range[1] <= 324 or not 1 <= a.baseline <= a.workers:
        parser.error('require 0 ≤ FIRST ≤ LAST ≤ 324 and 1 ≤ baseline ≤ workers')
    a.direction, a.paired, a.fields = 1, True, list(range(4))
    a.cache.mkdir(parents=True, exist_ok=True)
    (a.cache/'paired-rows').mkdir(exist_ok=True)
    a.lean = str(Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'],
                                               cwd=ROOT, text=True).strip())/'bin/lean')
    a.lean_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT, text=True).strip()
    data = static_data()
    static = verify_static(a, data)
    pending = deque(range(a.range[0], a.range[1]+1))
    records, errors = {}, {}
    active = {}
    target = a.baseline
    start = last = time.monotonic()
    before = cpus()
    idle = None
    def report():
        save(a.output, {'indices': a.range, 'complete': not (pending or active or errors),
                        'accepted_pairs': len(records), 'accepted_signed_model_theorems': 2*len(records),
                        'elapsed_seconds': round(time.monotonic()-start), 'current_worker_target': target,
                        'active_indices': sorted(active.values()), 'idle_cores': idle,
                        'available_gib': round(available_ram()/GIB, 1),
                        'errors': errors, 'rows': [records[i] for i in sorted(records)]})
    with ThreadPoolExecutor(max_workers=a.workers) as pool:
        while pending or active:
            now = time.monotonic()
            if now-last >= 12:
                after = cpus()
                idle = round((os.cpu_count() or 1)*(after[1]-before[1])/max(1, after[0]-before[0]), 2)
                before, last = after, now
                if idle >= a.reserve_cores+1:
                    target = min(a.workers, target+max(1, math.floor(idle-a.reserve_cores)))
                elif idle < a.reserve_cores:
                    target = max(a.baseline, target-1)
            free_slots = max(0, min(target-len(active), int((available_ram()/GIB-a.reserve_gib)//5)))
            for _ in range(min(free_slots, len(pending))):
                i = pending.popleft()
                active[pool.submit(check_row, a, data, static, i)] = i
            report()
            if not active and pending:
                time.sleep(5)
                continue
            done, _ = wait(active, timeout=5, return_when=FIRST_COMPLETED)
            for job in done:
                i = active.pop(job)
                try:
                    records[i] = job.result()
                    print(f'accepted signed pair {i}: {records[i]["key"]}', flush=True)
                except Exception as e:
                    errors[i] = str(e)
                    print(f'failed signed pair {i}: {e}', flush=True)
            if errors:
                # Existing checks finish and remain resumable. A shared producer defect
                # must be diagnosed before launching the remaining rows.
                pending.clear()
    report()
    if errors:
        raise SystemExit(f'{len(errors)} pair(s) failed')


if __name__ == '__main__':
    main()
