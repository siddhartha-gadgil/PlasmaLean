#!/usr/bin/env python3
"""Share compiled Lean outputs (oleans) of PlasmaLean modules between machines, like the Mathlib
cache, by hand: pack on the machine that built them, copy the archive (e.g. via Google Drive),
unpack on the other machine. Standard library only. See Workstation.md, "Sharing compiled files".

  pack [--only] ARCHIVE.tar.gz TARGET...
                                  TARGET is a module (PlasmaLean.Design.Foo) or a prefix ending in
                                  `*` (PlasmaLean.Design.RationalStellaratorGCEw*). The archive holds
                                  the build outputs of the targets and of all their PlasmaLean
                                  imports (transitively), plus a manifest. With --only, just the
                                  targets (smaller; the rest must already be built on the other
                                  machine).
  unpack ARCHIVE.tar.gz           check that this clone matches the manifest (same Lean version, same
                                  lake-manifest.json, identical source of every packed module),
                                  extract into .lake/build, then confirm with `lake --no-build build`
                                  that the targets are up to date.
  info ARCHIVE.tar.gz             print the manifest.

Only PlasmaLean's own modules are packed. Mathlib and the other packages come from the usual
`lake exe cache get` and must be the same versions on both machines (checked through
lake-manifest.json).

Trust: unpacked files are used without being checked again by the kernel on this machine. That is
the point (it saves the build), and it means trusting the machine that built them.
"""

import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import time

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LIB = os.path.join('.lake', 'build', 'lib', 'lean')
IR = os.path.join('.lake', 'build', 'ir')
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(\S+)', re.M)


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def src(mod):
    return os.path.join(*mod.split('.')) + '.lean'


def lean_version():
    """`version X, commit Y` of the toolchain (the platform part of `lean --version` may differ)."""
    out = subprocess.run(['lake', 'env', 'lean', '--version'], cwd=REPO, capture_output=True,
                         text=True, check=True).stdout
    v = re.search(r'version ([^,\s]+)', out)
    c = re.search(r'commit ([0-9a-f]+)', out)
    return f"{v.group(1) if v else '?'} {c.group(1) if c else out.strip()}"


def expand(targets):
    mods = []
    for t in targets:
        if t.endswith('*'):
            pkg, _, base = t[:-1].rpartition('.')
            d = os.path.join(REPO, *pkg.split('.'))
            found = sorted(f[:-5] for f in os.listdir(d) if f.startswith(base) and f.endswith('.lean'))
            if not found:
                sys.exit('no module matches ' + t)
            mods += [pkg + '.' + f for f in found]
        else:
            if not os.path.exists(os.path.join(REPO, src(t))):
                sys.exit('no source file for module ' + t)
            mods.append(t)
    return mods


def closure(mods):
    seen, todo = set(), list(mods)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        text = open(os.path.join(REPO, src(m))).read()
        for imp in IMPORT.findall(text):
            if imp.startswith('PlasmaLean.') or imp == 'PlasmaLean':
                if os.path.exists(os.path.join(REPO, src(imp))):
                    todo.append(imp)
    return sorted(seen)


def outputs(mod):
    """all build files of a module: lib/lean/<path>.* and ir/<path>.*"""
    rel = os.path.join(*mod.split('.'))
    files = []
    for root in (LIB, IR):
        d = os.path.join(REPO, root, os.path.dirname(rel))
        base = os.path.basename(rel) + '.'
        if os.path.isdir(d):
            files += [os.path.join(root, os.path.dirname(rel), f) for f in sorted(os.listdir(d))
                      if f.startswith(base)]
    return files


def pack(archive, targets, only=False):
    os.chdir(REPO)
    tops = expand(targets)
    mods = sorted(set(tops)) if only else closure(tops)
    missing = [m for m in mods if not os.path.exists(os.path.join(LIB, *m.split('.')) + '.olean')]
    if missing:
        sys.exit('not built (run lake build first): ' + ', '.join(missing[:10]))
    commit = subprocess.run(['git', 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    manifest = {
        'created': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
        'host': os.uname().nodename, 'platform': ' '.join(os.uname()[i] for i in (0, 4)),
        'commit': commit, 'lean': lean_version(), 'lake_manifest': sha256('lake-manifest.json'),
        'targets': tops, 'modules': {m: sha256(src(m)) for m in mods},
    }
    n = 0
    with tarfile.open(archive, 'w:gz') as tar:
        data = json.dumps(manifest, indent=1).encode()
        info = tarfile.TarInfo('MANIFEST.json')
        info.size = len(data)
        tar.addfile(info, io.BytesIO(data))
        for m in mods:
            for f in outputs(m):
                tar.add(f)
                n += 1
    print(f'packed {len(mods)} modules ({n} files) into {archive} '
          f'({os.path.getsize(archive) / 2**20:.1f} MB)')


def read_manifest(archive):
    with tarfile.open(archive, 'r:gz') as tar:
        return json.load(tar.extractfile('MANIFEST.json'))


def unpack(archive):
    archive = os.path.abspath(archive)
    os.chdir(REPO)
    man = read_manifest(archive)
    problems = []
    if man['lean'] != lean_version():
        problems.append(f"Lean version differs: archive {man['lean']!r}, here {lean_version()!r}")
    if man['lake_manifest'] != sha256('lake-manifest.json'):
        problems.append('lake-manifest.json differs (different Mathlib or package versions)')
    for m, h in man['modules'].items():
        p = src(m)
        if not os.path.exists(p):
            problems.append('missing source here: ' + p)
        elif sha256(p) != h:
            problems.append('source differs here: ' + p)
    if problems:
        print('\n'.join(problems[:20]))
        sys.exit(f"refusing to unpack: this clone does not match the archive (built at commit "
                 f"{man['commit'][:10]}); check out that commit or pull, then retry")
    with tarfile.open(archive, 'r:gz') as tar:
        members = [x for x in tar.getmembers() if x.name != 'MANIFEST.json']
        for x in members:
            if not (x.isfile() and x.name.startswith('.lake/build/') and '..' not in x.name):
                sys.exit('unexpected entry in archive: ' + x.name)
        tar.extractall('.', members=members)
    print(f"unpacked {len(man['modules'])} modules from {man['host']} ({man['platform']}), "
          f"commit {man['commit'][:10]}")
    r = subprocess.run(['lake', '--no-build', 'build'] + man['targets'])
    if r.returncode != 0:
        sys.exit('lake reports the targets are NOT up to date after unpacking; '
                 'they will be rebuilt locally on the next lake build')
    print('lake: targets up to date (no rebuild needed)')


def main():
    if len(sys.argv) >= 5 and sys.argv[1] == 'pack' and sys.argv[2] == '--only':
        pack(sys.argv[3], sys.argv[4:], only=True)
    elif len(sys.argv) >= 4 and sys.argv[1] == 'pack':
        pack(sys.argv[2], sys.argv[3:])
    elif len(sys.argv) == 3 and sys.argv[1] == 'unpack':
        unpack(sys.argv[2])
    elif len(sys.argv) == 3 and sys.argv[1] == 'info':
        man = read_manifest(sys.argv[2])
        man['modules'] = f"{len(man['modules'])} modules"
        print(json.dumps(man, indent=1))
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
