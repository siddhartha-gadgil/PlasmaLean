#!/usr/bin/env python3
"""Evolutionary optimization of Lean packages on the PlasmaLean task server.

A problem asks for a term `candidate` of a given Lean type that satisfies constraints, stated as
propositions about `candidate`, and maximizes or minimizes a computable measure. A candidate
*package* is Lean code defining `candidate` and proving one theorem per constraint, named as in the
problem. Packages are checked and measured on the task server (task `assess`): the server checks
the proofs and the axioms they use, and evaluates the measure. Only the Python standard library is
used. Start the server first: scripts/theory_server/ensure_server.sh.

A run lives in a task folder (by convention notes/reasoning/<date>-evolve-<slug>/):

    problem.json        the problem: type, objective, measure, constraints, settings
    context.lean        Lean code placed before every candidate (definitions the problem uses)
    generations/gen-NNN/candidates/*.lean   candidate packages of generation NNN
    generations/gen-NNN/results.jsonl       their evaluations
    generations/gen-NNN/analysis.md         the analysis written before generating gen NNN+1
    generations/gen-NNN/population.json     the population selected after generation NNN
    population.json     the current population; best/  the best package so far
    archive.jsonl       every evaluation of the run

Commands:

    evolve.py init DIR                 create the folder with template problem.json and context.lean
    evolve.py evaluate DIR [--gen N]   evaluate the candidates of a generation (default: latest)
    evolve.py select DIR [--gen N]     update the population from a generation's results
    evolve.py next DIR                 create the next generation folder and list the parents
    evolve.py status DIR               progress per generation and the current best
    evolve.py package DIR ID           print the full package of a candidate (context, code, checks)
    evolve.py try DIR FILE             evaluate one candidate file without recording it

Candidate ids are `gen-NNN/<file stem>`. Candidates may start with metadata comment lines such as
`-- evolve: parents = gen-002/a1, gen-002/b3`, `-- evolve: strategy = proof-repair` and
`-- evolve: idea = ...`; these are recorded with the evaluation.
"""
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import sys
import urllib.error
import urllib.request
from fractions import Fraction

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Constructs a candidate may not use: they could fake a proof, hide computation, run arbitrary
# code on the server, make elaboration unbounded, or clash with the names of the harness. Checked
# on the code with comments removed. (Instances and notation cannot change the problem: the
# statements and the measure are elaborated in a preamble before the candidate.)
FORBIDDEN = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\bpartial\b", r"\bunsafe\b", r"\bopaque\b",
    r"\bimplemented_by\b", r"\bextern\b", r"\bnative_decide\b", r"#eval\b", r"#exit\b",
    r"#print\b", r"\brun_cmd\b", r"\brun_tac\b", r"\brun_elab\b", r"\belab\b", r"\belab_rules\b",
    r"\bmacro\b", r"\bmacro_rules\b", r"\bsyntax\b", r"\binitialize\b", r"\bbuiltin_initialize\b",
    r"^\s*import\b", r"\bmaxHeartbeats\b", r"\bmaxRecDepth\b", r"\bevolve_",
]

PROBLEM_TEMPLATE = {
    "name": "SHORT-NAME",
    "description": "What is being optimized, and why it matters for the project.",
    "objective": "maximize",
    "type": "List ℕ",
    "measure": "candidate.sum",
    "constraints": [
        {"name": "bounded", "statement": "∀ x ∈ candidate, x ≤ 10",
         "description": "every entry is at most 10"},
        {"name": "short", "statement": "candidate.length ≤ 5",
         "description": "at most five entries"},
    ],
    "context_file": "context.lean",
    "population_size": 8,
    "near_miss_size": 4,
    "forbidden": [],
}

CONTEXT_TEMPLATE = """/-
Context of the problem: Lean code placed before every candidate. Define here the functions and
predicates that the measure and the constraints use, so that candidates cannot change them. The
server environment already contains Mathlib and PlasmaLean; do not add imports.
-/
"""


# ---------------------------------------------------------------- files and problem

def die(msg, code=2):
    print(msg, file=sys.stderr)
    sys.exit(code)


def load_problem(d):
    path = os.path.join(d, "problem.json")
    if not os.path.exists(path):
        die(f"no problem.json in {d}; create one with: evolve.py init {d}")
    with open(path, encoding="utf-8") as f:
        p = json.load(f)
    for key in ("objective", "type", "measure", "constraints"):
        if key not in p:
            die(f"problem.json lacks '{key}'")
    if p["objective"] not in ("maximize", "minimize"):
        die("objective must be 'maximize' or 'minimize'")
    for c in p["constraints"]:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", c.get("name", "")):
            die(f"constraint name {c.get('name')!r} must be a simple Lean identifier")
    p.setdefault("population_size", 8)
    p.setdefault("near_miss_size", 4)
    p.setdefault("forbidden", [])
    ctx = ""
    if p.get("context_file"):
        cpath = os.path.join(d, p["context_file"])
        if os.path.exists(cpath):
            with open(cpath, encoding="utf-8") as f:
                ctx = f.read()
    p["_context"] = ctx
    return p


def gen_dir(d, n):
    return os.path.join(d, "generations", f"gen-{n:03d}")


def generations(d):
    root = os.path.join(d, "generations")
    if not os.path.isdir(root):
        return []
    out = []
    for name in os.listdir(root):
        m = re.fullmatch(r"gen-(\d{3})", name)
        if m:
            out.append(int(m.group(1)))
    return sorted(out)


def latest_gen(d):
    gens = generations(d)
    if not gens:
        die(f"no generations in {d}; put seed candidates in {gen_dir(d, 0)}/candidates/")
    return gens[-1]


def read_jsonl(path):
    if not os.path.exists(path):
        return []
    with open(path, encoding="utf-8") as f:
        return [json.loads(line) for line in f if line.strip()]


def write_json(path, obj):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write("\n")


# ---------------------------------------------------------------- packages

def strip_comments(code):
    code = re.sub(r"/-.*?-/", " ", code, flags=re.S)
    return re.sub(r"--[^\n]*", "", code)


def normalized(code):
    return re.sub(r"\s+", " ", strip_comments(code)).strip()


def metadata(code):
    meta = {}
    for line in code.splitlines():
        m = re.match(r"\s*--\s*evolve:\s*([A-Za-z_]+)\s*=\s*(.*)$", line)
        if m:
            meta[m.group(1)] = m.group(2).strip()
    return meta


def forbidden_in(code, problem):
    text = strip_comments(code)
    found = []
    for pat in FORBIDDEN + list(problem.get("forbidden", [])):
        if re.search(pat, text, flags=re.M):
            found.append(pat.replace("\\b", "").replace("^\\s*", ""))
    return found


def preamble(problem):
    """Statements and the measure, elaborated before the candidate, so that nothing the candidate
    declares (instances, notation, open namespaces) can change what they mean."""
    t = problem["type"]
    lines = ["-- evolve preamble: the measure and the constraint statements, fixed before the candidate",
             f"def evolve_measure_string (candidate : {t}) : String := toString ({problem['measure']})"]
    for c in problem["constraints"]:
        lines.append(f"def evolve_statement_{c['name']} (candidate : {t}) : Prop := {c['statement']}")
    return "\n".join(lines) + "\n\n"


def harness(problem):
    """Checks after the candidate: its type, and that each proof proves the fixed statement."""
    lines = ["", "-- evolve harness: the type of `candidate` and the statements of the proofs",
             f"def evolve_candidate_check : ({problem['type']}) := candidate"]
    for c in problem["constraints"]:
        lines.append(f"theorem evolve_constraint_{c['name']} : evolve_statement_{c['name']} candidate"
                     f" := {c['name']}")
    return "\n".join(lines) + "\n"


def package(problem, code):
    """The full package and the number of lines before the candidate's code."""
    ctx = problem["_context"].rstrip("\n")
    head = (ctx + "\n\n" if ctx else "") + preamble(problem)
    return head + code.rstrip("\n") + "\n" + harness(problem), head.count("\n")


# ---------------------------------------------------------------- server

def post(port, payload, timeout):
    req = urllib.request.Request(
        f"http://127.0.0.1:{port}/", data=json.dumps(payload).encode("utf-8"),
        headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as res:
            return json.loads(res.read().decode("utf-8"))
    except (urllib.error.URLError, ConnectionError) as e:
        die(f"theory_server not reachable on port {port} ({e}); "
            "run scripts/theory_server/ensure_server.sh")


def parse_score(output):
    """The measure is evaluated through `evolve_measure_string`: its repr is a quoted numeral."""
    try:
        text = json.loads(output) if output.startswith('"') else output
        return Fraction(text.strip())
    except (ValueError, ZeroDivisionError, json.JSONDecodeError):
        return None


def assess(problem, code, port, timeout):
    """Evaluate one candidate package and return its record (without id and file)."""
    rec = {"chars": len(normalized(code)), "sha": hashlib.sha256(normalized(code).encode()).hexdigest()[:16],
           "meta": metadata(code)}
    bad = forbidden_in(code, problem)
    rec["forbidden"] = bad
    if bad:
        rec.update(valid=False, reason="forbidden: " + ", ".join(bad))
        return rec
    full, offset = package(problem, code)
    cnames = [f"evolve_constraint_{c['name']}" for c in problem["constraints"]]
    payload = {"task": "assess", "code": full, "modify_env": False,
               "axioms": ["evolve_candidate_check"] + cnames,
               "require": ["evolve_candidate_check"],
               "term": "evolve_measure_string candidate"}
    out = post(port, payload, timeout)
    r = out.get("response", {})
    if out.get("status") != "ok" or r.get("result") != "ok":
        rec.update(valid=False, reason="server error: " + str(r.get("error") or out.get("message")))
        return rec
    code_lines = code.rstrip("\n").count("\n") + 1
    msgs = []
    for m in r.get("messages", []):
        line = m.get("line", 0) - offset
        where = "candidate" if 1 <= line <= code_lines else ("context" if line < 1 else "harness")
        msgs.append({"severity": m["severity"], "where": where,
                     "line": line if where == "candidate" else m.get("line"),
                     "column": m.get("column"), "text": m["text"]})
    rec["messages"] = msgs
    axioms = r.get("axioms", {})
    cand_ax = axioms.get("evolve_candidate_check")
    rec["candidate_ok"] = cand_ax is not None and set(cand_ax) <= STANDARD_AXIOMS
    constraints = {}
    for c, n in zip(problem["constraints"], cnames):
        ax = axioms.get(n)
        if ax is None:
            constraints[c["name"]] = "missing"
        elif "sorryAx" in ax:
            constraints[c["name"]] = "failed"
        elif not set(ax) <= STANDARD_AXIOMS:
            constraints[c["name"]] = "nonstandard axioms: " + ", ".join(sorted(set(ax) - STANDARD_AXIOMS))
        else:
            constraints[c["name"]] = "proved"
    rec["constraints"] = constraints
    rec["compiles"] = bool(r.get("compiles"))
    score = parse_score(r["output"]) if r.get("evaluated") else None
    rec["score"] = None if score is None else str(score)
    rec["score_float"] = None if score is None else float(score)
    if not r.get("evaluated"):
        rec["eval_error"] = r.get("eval_error")
    all_proved = all(v == "proved" for v in constraints.values())
    rec["valid"] = bool(rec["candidate_ok"] and all_proved and rec["compiles"] and score is not None)
    if not rec["valid"]:
        reasons = []
        if not rec["candidate_ok"]:
            reasons.append("candidate does not elaborate cleanly")
        reasons += [f"constraint {k}: {v}" for k, v in constraints.items() if v != "proved"]
        if score is None:
            reasons.append("measure not computed" + (f" ({rec.get('eval_error')})" if rec.get("eval_error") else ""))
        if not rec["compiles"] and not reasons:
            reasons.append("the package has errors or sorry elsewhere")
        rec["reason"] = "; ".join(reasons)
    return rec


# ---------------------------------------------------------------- selection

def better_key(problem):
    sign = -1 if problem["objective"] == "maximize" else 1
    return lambda r: (sign * Fraction(r["score"]), r["chars"])


def summary_line(r):
    s = r.get("score")
    status = "VALID" if r.get("valid") else "invalid"
    tail = "" if r.get("valid") else f"  [{r.get('reason', '')[:90]}]"
    return f"{r['id']:<28} {status:<8} score={s if s is not None else '-':<12} chars={r['chars']}{tail}"


def select(d, problem, n):
    results = read_jsonl(os.path.join(gen_dir(d, n), "results.jsonl"))
    current = {}
    pop_path = os.path.join(d, "population.json")
    if os.path.exists(pop_path):
        with open(pop_path, encoding="utf-8") as f:
            pop = json.load(f)
        for r in pop.get("members", []) + pop.get("near_misses", []):
            current[r["id"]] = r
    pool = list(current.values()) + [r for r in results if r["id"] not in current]
    key = better_key(problem)
    seen, members = set(), []
    for r in sorted([r for r in pool if r.get("valid")], key=key):
        if r["sha"] in seen:
            continue
        seen.add(r["sha"])
        members.append(r)
        if len(members) >= problem["population_size"]:
            break
    near = []
    candidates = [r for r in pool if not r.get("valid") and r.get("score") is not None
                  and r.get("candidate_ok") and not r.get("forbidden") and r["sha"] not in seen]
    for r in sorted(candidates, key=key):
        if r["sha"] in seen:
            continue
        seen.add(r["sha"])
        near.append(r)
        if len(near) >= problem["near_miss_size"]:
            break
    pop = {"generation": n, "objective": problem["objective"],
           "best": members[0] if members else None, "members": members, "near_misses": near,
           "updated": datetime.datetime.now().isoformat(timespec="seconds")}
    write_json(pop_path, pop)
    write_json(os.path.join(gen_dir(d, n), "population.json"), pop)
    if members:
        best = members[0]
        bdir = os.path.join(d, "best")
        os.makedirs(bdir, exist_ok=True)
        src = os.path.join(d, best["file"])
        shutil.copyfile(src, os.path.join(bdir, "candidate.lean"))
        with open(src, encoding="utf-8") as f:
            full, _ = package(problem, f.read())
        with open(os.path.join(bdir, "package.lean"), "w", encoding="utf-8") as f:
            f.write(full)
        write_json(os.path.join(bdir, "record.json"), best)
    return pop


# ---------------------------------------------------------------- commands

def cmd_init(a):
    d = a.dir
    os.makedirs(os.path.join(gen_dir(d, 0), "candidates"), exist_ok=True)
    pj = os.path.join(d, "problem.json")
    if os.path.exists(pj):
        die(f"{pj} exists; not overwriting")
    write_json(pj, PROBLEM_TEMPLATE)
    ctx = os.path.join(d, "context.lean")
    if not os.path.exists(ctx):
        with open(ctx, "w", encoding="utf-8") as f:
            f.write(CONTEXT_TEMPLATE)
    print(f"created {pj}, {ctx} and {gen_dir(d, 0)}/candidates/ (put seed candidates there)")


def evaluate_files(d, problem, n, port, timeout, force):
    gdir = gen_dir(d, n)
    cdir = os.path.join(gdir, "candidates")
    if not os.path.isdir(cdir):
        die(f"no candidates folder {cdir}")
    res_path = os.path.join(gdir, "results.jsonl")
    done = {r["id"]: r for r in read_jsonl(res_path)}
    out = []
    for name in sorted(os.listdir(cdir)):
        if not name.endswith(".lean"):
            continue
        cid = f"gen-{n:03d}/{name[:-5]}"
        if cid in done and not force:
            out.append(done[cid])
            continue
        with open(os.path.join(cdir, name), encoding="utf-8") as f:
            code = f.read()
        rec = assess(problem, code, port, timeout)
        rec = {"id": cid, "gen": n, "file": os.path.relpath(os.path.join(cdir, name), d), **rec,
               "evaluated": datetime.datetime.now().isoformat(timespec="seconds")}
        done[cid] = rec
        out.append(rec)
        with open(os.path.join(d, "archive.jsonl"), "a", encoding="utf-8") as f:
            f.write(json.dumps(rec, ensure_ascii=False) + "\n")
        print(summary_line(rec), flush=True)
    with open(res_path, "w", encoding="utf-8") as f:
        for r in sorted(done.values(), key=lambda r: r["id"]):
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    return out


def cmd_evaluate(a):
    problem = load_problem(a.dir)
    n = a.gen if a.gen is not None else latest_gen(a.dir)
    out = evaluate_files(a.dir, problem, n, a.port, a.timeout, a.force)
    valid = [r for r in out if r.get("valid")]
    print(f"generation {n}: {len(out)} candidates, {len(valid)} valid")
    if valid:
        best = sorted(valid, key=better_key(problem))[0]
        print(f"best this generation: {best['id']} score={best['score']}")


def cmd_select(a):
    problem = load_problem(a.dir)
    n = a.gen if a.gen is not None else latest_gen(a.dir)
    pop = select(a.dir, problem, n)
    print(f"population after generation {n} ({problem['objective']}):")
    for r in pop["members"]:
        print("  " + summary_line(r))
    if pop["near_misses"]:
        print("near misses (measure computed, some proof failed):")
        for r in pop["near_misses"]:
            print("  " + summary_line(r))
    if pop["best"]:
        print(f"best so far: {pop['best']['id']} score={pop['best']['score']} (best/package.lean)")
    else:
        print("no valid candidate yet")


def cmd_next(a):
    n = latest_gen(a.dir) + 1
    os.makedirs(os.path.join(gen_dir(a.dir, n), "candidates"), exist_ok=True)
    print(f"created {gen_dir(a.dir, n)}/candidates/")
    pop_path = os.path.join(a.dir, "population.json")
    if os.path.exists(pop_path):
        with open(pop_path, encoding="utf-8") as f:
            pop = json.load(f)
        print("parents (population):")
        for r in pop["members"]:
            print(f"  {r['id']:<28} score={r['score']:<12} {r['file']}")
        for r in pop["near_misses"]:
            print(f"  {r['id']:<28} near miss score={r['score']:<12} {r['file']}  [{r.get('reason', '')[:70]}]")
    print(f"write the analysis of the population to {gen_dir(a.dir, n - 1)}/analysis.md first")


def cmd_status(a):
    problem = load_problem(a.dir)
    key = better_key(problem)
    print(f"{problem.get('name', '')}: {problem['objective']} {problem['measure']} over {problem['type']}")
    for n in generations(a.dir):
        rs = read_jsonl(os.path.join(gen_dir(a.dir, n), "results.jsonl"))
        cands = os.path.join(gen_dir(a.dir, n), "candidates")
        total = len([x for x in os.listdir(cands) if x.endswith(".lean")]) if os.path.isdir(cands) else 0
        valid = [r for r in rs if r.get("valid")]
        best = sorted(valid, key=key)[0]["score"] if valid else "-"
        print(f"  gen {n:03d}: {total} candidates, {len(rs)} evaluated, {len(valid)} valid, best {best}")
    pop_path = os.path.join(a.dir, "population.json")
    if os.path.exists(pop_path):
        with open(pop_path, encoding="utf-8") as f:
            pop = json.load(f)
        if pop.get("best"):
            print(f"best so far: {pop['best']['id']} score={pop['best']['score']}")


def find_record(d, cid):
    for r in read_jsonl(os.path.join(d, "archive.jsonl"))[::-1]:
        if r["id"] == cid:
            return r
    return None


def cmd_package(a):
    problem = load_problem(a.dir)
    r = find_record(a.dir, a.id)
    path = os.path.join(a.dir, r["file"]) if r else None
    if not path:
        m = re.fullmatch(r"gen-(\d{3})/(.+)", a.id)
        if not m:
            die(f"unknown candidate {a.id}")
        path = os.path.join(gen_dir(a.dir, int(m.group(1))), "candidates", m.group(2) + ".lean")
    with open(path, encoding="utf-8") as f:
        full, _ = package(problem, f.read())
    sys.stdout.write(full)


def cmd_try(a):
    problem = load_problem(a.dir)
    with open(a.file, encoding="utf-8") as f:
        rec = assess(problem, f.read(), a.port, a.timeout)
    print(json.dumps(rec, indent=2, ensure_ascii=False))
    sys.exit(0 if rec.get("valid") else 1)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--port", type=int, default=int(os.environ.get("THEORY_SERVER_PORT", "8080")))
    p.add_argument("--timeout", type=float, default=600, help="seconds to wait for each response")
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("init"); s.add_argument("dir"); s.set_defaults(f=cmd_init)
    s = sub.add_parser("evaluate"); s.add_argument("dir"); s.add_argument("--gen", type=int)
    s.add_argument("--force", action="store_true", help="re-evaluate candidates already evaluated")
    s.set_defaults(f=cmd_evaluate)
    s = sub.add_parser("select"); s.add_argument("dir"); s.add_argument("--gen", type=int)
    s.set_defaults(f=cmd_select)
    s = sub.add_parser("next"); s.add_argument("dir"); s.set_defaults(f=cmd_next)
    s = sub.add_parser("status"); s.add_argument("dir"); s.set_defaults(f=cmd_status)
    s = sub.add_parser("package"); s.add_argument("dir"); s.add_argument("id"); s.set_defaults(f=cmd_package)
    s = sub.add_parser("try"); s.add_argument("dir"); s.add_argument("file"); s.set_defaults(f=cmd_try)
    a = p.parse_args()
    a.f(a)


if __name__ == "__main__":
    main()
