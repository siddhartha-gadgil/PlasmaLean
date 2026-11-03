#!/usr/bin/env python3
"""Classify PlasmaLean research notes by implementation, from their metadata tables.

usage: python3 scripts/notes/implementation_status.py [note.md ...]   (default: notes/theory/*.md)

For each note, reads the metadata rows `ID`, `Status` and `Lean evidence`, extracts the backticked
identifiers of the Lean evidence row and checks which of them are declared in `PlasmaLean/`
(theorem, lemma, def, abbrev, structure, class, inductive, instance) or are module names. Prints

  N-id  CLASS  file  (found k of n names)  status

with CLASS one of
  none      no compiled Lean evidence: the note may be modified in place;
  partial   some Lean evidence, and the status names open, blocked or partial parts;
  whole     Lean evidence, and the status names no open part;
  check     no metadata table, or no Lean name resolved although the status claims verified work
            or the note is a status log:
            read the note and decide (treat it as implemented if unsure).
The partial/whole split is a keyword heuristic on the status text; the skill
`plasmalean-modify-notes` treats both as implemented, so only `none` permits in-place edits.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|public)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([^\s:({\[]+)",
                  re.M)
OPEN_WORDS = ("open", "partly", "partial", "blocked", "not done", "todo", "lead", "conjectur",
              "parked", "pending", "in progress")


def lean_names():
    names, modules = set(), set()
    for f in (ROOT / "PlasmaLean").rglob("*.lean"):
        rel = f.relative_to(ROOT).with_suffix("")
        modules.add(".".join(rel.parts))
        modules.add("/".join(rel.parts[1:]))
        modules.add("/".join(rel.parts))
        for m in DECL.finditer(f.read_text(errors="ignore")):
            full = m.group(1)
            names.add(full)
            names.add(full.split(".")[-1])
    return names, modules


def row(text, field):
    m = re.search(r"^\|\s*" + re.escape(field) + r"\s*\|(.*)\|\s*$", text, re.M)
    return m.group(1).strip() if m else None


def classify(path, names, modules):
    text = path.read_text(errors="ignore")
    nid, status, lean = row(text, "ID"), row(text, "Status"), row(text, "Lean evidence")
    if nid is None or status is None or lean is None:
        return (nid or "?"), "check", 0, 0, status or "(no metadata table)"
    cands = [c.strip() for c in re.findall(r"`([^`]+)`", lean)]
    cands = [c for c in cands if re.fullmatch(r"[A-Za-z_][\w.'/₀-₉]*", c)]
    found = 0
    for c in cands:
        short = c.split(".")[-1]
        if c in names or short in names or c in modules or c.removeprefix("PlasmaLean.") in modules \
                or c.removesuffix(".lean") in modules:
            found += 1
    kind = (row(text, "Kind") or "").lower()
    if found == 0:
        claims = any(w in status.lower() for w in ("verified", "formalized", "[lean]", "compiled"))
        cls = "check" if claims or "status log" in kind else "none"
    else:
        low = status.lower()
        cls = "partial" if any(w in low for w in OPEN_WORDS) else "whole"
    return nid.strip("` "), cls, found, len(cands), status


def main():
    files = [pathlib.Path(a) for a in sys.argv[1:]] or sorted(
        p for p in (ROOT / "notes/theory").glob("*.md") if p.name != "README.md")
    names, modules = lean_names()
    rows = [(classify(p, names, modules), p) for p in files]
    rows.sort(key=lambda r: [int(x) if x.isdigit() else x for x in re.split(r"(\d+)", r[0][0])])
    for (nid, cls, found, n, status), p in rows:
        st = status if len(status) <= 90 else status[:87] + "..."
        print(f"{nid:6} {cls:8} {p.name:40} (found {found} of {n} names)  {st}")


if __name__ == "__main__":
    main()
