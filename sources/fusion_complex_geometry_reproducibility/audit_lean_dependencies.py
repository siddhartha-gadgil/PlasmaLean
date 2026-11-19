"""Fetch and inspect the project import closure at a pinned commit; not a Lean rebuild."""
from pathlib import Path
import concurrent.futures as cf
import hashlib
import json
import re
import urllib.request

HERE = Path(__file__).resolve().parent
COMMIT = json.loads((HERE / "source_commit.json").read_text())["sha"]
BASE = f"https://raw.githubusercontent.com/siddhartha-gadgil/PlasmaLean/{COMMIT}/"
OUT = HERE / "lean_audit"
OUT.mkdir(exist_ok=True)
tree = json.loads((HERE / "source_tree.json").read_text())["tree"]
entries = {e["path"]: e for e in tree if e["type"] == "blob"}
roots = ["PlasmaLean.Design.DommaschkKamNested"]
seen, pending, records, errors = set(), set(roots), {}, {}

def fetch(module):
    relative = module.replace(".", "/") + ".lean"
    target = OUT / relative
    expected = entries[relative]["sha"]
    local = HERE / Path(relative).name
    raw = None
    if target.exists():
        raw = target.read_bytes()
    elif local.exists():
        b = local.read_bytes()
        if hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest() == expected:
            raw = b
    if raw is None:
        raw = urllib.request.urlopen(BASE + relative, timeout=30).read()
    actual = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    assert actual == expected, (relative, "git blob hash mismatch")
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)
    text = raw.decode()
    imports = []
    for match in re.finditer(r"^(?:(?:public|meta)\s+)*import\s+(.+)$", text, re.M):
        imports.extend(t for t in match[1].split() if t.startswith("PlasmaLean"))
    return module, relative, imports, len(raw), actual

with cf.ThreadPoolExecutor(max_workers=16) as pool:
    while pending:
        batch = sorted(pending - seen)
        pending.clear()
        if not batch:
            break
        futs = {pool.submit(fetch, m): m for m in batch}
        for fut in cf.as_completed(futs):
            m = futs[fut]
            try:
                _, path, deps, size, digest = fut.result()
                records[m] = {"path": path, "imports": deps, "bytes": size, "git_blob": digest}
                seen.add(m)
                pending.update(d for d in deps if d not in seen)
            except Exception as e:
                errors[m] = repr(e)
                seen.add(m)
        print(f"checked {len(records)} modules, pending {len(pending)}, errors {len(errors)}", flush=True)

(HERE / "lean_dependency_audit.json").write_text(json.dumps({
    "commit": COMMIT, "roots": roots, "modules": records, "errors": errors,
    "Lean_rebuilt": False
}, indent=2) + "\n")
print(json.dumps({"commit": COMMIT, "modules": len(records),
                  "MB": sum(r["bytes"] for r in records.values()) / 1e6,
                  "errors": errors, "Lean_rebuilt": False}, indent=2))
