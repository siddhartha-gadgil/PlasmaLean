"""Build actual signed QA2R defect theorems from the q0,u=.47 packet in private directories.

The default pilot covers slabs 0 through 7 in both directions and backward 283.
Use --range LO HI for an inclusive range. Successful artifacts are reusable only
when the generated source, imported build traces, Lean version and artifact
hashes agree. The complete proof source and oleans remain in the specified cache.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import re
from shutil import disk_usage
import subprocess
import tempfile
import time

from emit_sparse_taylor_slab import RECORD, ROOT
from emit_sparse_trace_defect_samples import emit_selected
from screen_sparse_reference_defects import jobs


DESIGN = ROOT / '.lake/build/lib/lean/PlasmaLean/Design'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
GIB = 1 << 30


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def available_ram():
    text = Path('/proc/meminfo').read_text()
    return int(re.search(r'^MemAvailable:\s+([0-9]+) kB', text, re.MULTILINE)[1])*1024


def run_lean(args, env, stats, log):
    start = time.monotonic()
    with log.open('w') as out:
        p = subprocess.run(['/usr/bin/time', '-f', '%M', '-o', str(stats), *args],
                           cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    if p.returncode:
        raise RuntimeError(f'{args[-1]} failed\n' + log.read_text()[-3000:])
    return time.monotonic()-start, int(stats.read_text())


def verify(args):
    job, cache, dependency_key, lean, lean_path = args
    modules = list(emit_selected([job]))
    name = modules[-1][0]
    imports = sorted({s for _, source in modules for s in re.findall(
        r'^public import PlasmaLean.Design.(\w+)$', source, re.MULTILINE)
        if s not in {m for m,_ in modules}})
    key = sha256(json.dumps([dependency_key, modules, [(imp, digest(DESIGN/(imp+'.trace')))
                                              for imp in imports]]).encode()).hexdigest()
    work = cache / name / key
    work.mkdir(parents=True, exist_ok=True)
    with (work/'lock').open('w') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        marker = work/'accepted.json'
        if marker.exists():
            saved = json.loads(marker.read_text())
            if (saved['key'] == key and saved['theorem'] == name+'.physical_defect' and
                    all((work/path).is_file() and digest(work/path) == h
                        for path, h in saved['artifacts'].items())):
                return {**saved, 'resumed': True}
        while available_ram() < 15*GIB:
            time.sleep(5)
        tree = work/'TraceCache'
        tree.mkdir(parents=True, exist_ok=True)
        env = {**os.environ, 'LEAN_NUM_THREADS': '1', 'LEAN_PATH': str(work)+os.pathsep+lean_path}
        stats = work/'peak.txt'
        artifacts = {}
        wall = peak = 0
        for mod, source in modules:
            src, out = tree/(mod+'.lean'), tree/(mod+'.olean')
            for local, _ in modules:
                source = source.replace(f'public import PlasmaLean.Design.{local}\n',
                                        f'public import TraceCache.{local}\n')
            src.write_text(source)
            seconds, rss = run_lean([lean, '-j1', '-R', str(work), '-o', str(out), str(src)],
                                    env, stats, work/(mod+'.log'))
            wall, peak = wall+seconds, max(peak,rss)
            for file in tree.glob(mod+'.olean*'):
                artifacts[str(file.relative_to(work))] = digest(file)
        audit = work/'Audit.lean'
        audit.write_text(f'import TraceCache.{name}\n'
                         f'#print axioms PlasmaLean.Design.{name}.physical_defect\n')
        seconds, rss = run_lean([lean, '-j1', '-R', str(work), str(audit)], env, stats, work/'audit.log')
        output = (work/'audit.log').read_text()
        match = re.search(r'depends on axioms:\s*\[([^]]*)\]', output)
        if not match or set(map(str.strip, match[1].split(','))) != ALLOWED:
            raise ValueError(f'{name}: invalid axiom audit\n{output}')
        result = {'key': key, 'theorem': name+'.physical_defect', 'direction': job[1],
                  'index': job[2], 'axioms': sorted(ALLOWED), 'peak_rss_kib': max(rss,peak),
                  'wall_seconds': round(wall+seconds,3), 'artifacts': artifacts}
        with tempfile.NamedTemporaryFile('w', dir=work, delete=False) as tmp:
            json.dump(result, tmp, indent=2)
        Path(tmp.name).replace(marker)
        return {**result, 'resumed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--workers', type=int, default=3, choices=range(1,7))
    parser.add_argument('--range', nargs=2, type=int, metavar=('LO','HI'))
    parser.add_argument('--direction', type=int, choices=(-1,1))
    parser.add_argument('--cache', type=Path, default=ROOT/'.lake/trace-residual')
    args = parser.parse_args()
    cache = args.cache.resolve()
    cache.mkdir(parents=True, exist_ok=True)
    if disk_usage(cache).free < 2*GIB:
        raise SystemExit('need 2 GiB available for the certificate cache')
    if available_ram() < (12+3*args.workers)*GIB:
        raise SystemExit('requested parallelism exceeds current memory headroom')
    if args.range and not 0 <= args.range[0] <= args.range[1] < 391:
        raise SystemExit('slab range must be contained in [0,390]')
    selected = [j for j in jobs(RECORD,8,False) if
                ((args.range[0] <= j[2] <= args.range[1]) if args.range else
                 (j[2] < 8 or (j[1],j[2]) == (-1,283))) and args.direction in (None,j[1])]
    selected.sort(key=lambda j: (j[2], j[1]))
    static = ['DommaschkBounceTaylor', 'DommaschkFramedTaylorResidual',
              *sorted({f'DommaschkHarmonicBlock{j[2]//8:02}' for j in selected})]
    subprocess.run(['lake','build','--no-build',*['PlasmaLean.Design.'+m for m in static]],
                   cwd=ROOT, stdout=subprocess.DEVNULL, check=True)
    def lake(*cmd):
        return subprocess.check_output(['lake','env',*cmd],cwd=ROOT,text=True).strip()
    lean = str(Path(lake('lean','--print-prefix'))/'bin/lean')
    lean_path = lake('printenv','LEAN_PATH')
    key = [digest(RECORD), digest(Path(__file__)), lake('lean','--version')]
    items = [(j,cache,key,lean,lean_path) for j in selected]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for result in pool.map(verify, items, chunksize=1):
            print(json.dumps({k:v for k,v in result.items() if k != 'artifacts'}), flush=True)


if __name__ == '__main__':
    main()
