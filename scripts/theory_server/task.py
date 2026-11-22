#!/usr/bin/env python3
"""Send check and eval tasks to the PlasmaLean task server (theory_server).

Only the Python standard library is used. The server must be running: start it with
scripts/theory_server/ensure_server.sh. The JSON request is built here, so Lean code with quotes,
backslashes or newlines needs no escaping. Unless --keep is given, the server's environment is not
modified (the request has "modify_env": false).

    task.py check --code-file Candidate.lean      # does the code compile?
    task.py check --code 'def f (n : Nat) := n + 1'
    task.py eval --term 'f 3' --code-file Candidate.lean
    task.py eval --term 'PlasmaLean.Transport.svFloorF 10'
    task.py raw < request.json                    # send a JSON request as it is

The response JSON is printed on standard output. Exit status: for check, 0 if the code compiles
(no errors and no sorry) and 1 if not; for eval, 0 if a value was computed and 1 if not; for raw,
0 if the server answered; 2 if the server could not be reached or the request was invalid.
"""
import argparse
import json
import os
import sys
import urllib.error
import urllib.request


def read_code(args):
    if args.code is not None:
        return args.code
    if args.code_file is not None:
        if args.code_file == "-":
            return sys.stdin.read()
        with open(args.code_file, encoding="utf-8") as f:
            return f.read()
    return None


def post(port, path, payload, timeout):
    data = payload if isinstance(payload, bytes) else json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(
        f"http://127.0.0.1:{port}{path}", data=data,
        headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as res:
            return json.loads(res.read().decode("utf-8"))
    except (urllib.error.URLError, ConnectionError) as e:
        print(f"theory_server not reachable on port {port} ({e}); "
              "run scripts/theory_server/ensure_server.sh", file=sys.stderr)
        sys.exit(2)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--port", type=int, default=int(os.environ.get("THEORY_SERVER_PORT", "8080")))
    p.add_argument("--timeout", type=float, default=600, help="seconds to wait for a response")
    sub = p.add_subparsers(dest="cmd", required=True)
    for name in ("check", "eval"):
        s = sub.add_parser(name)
        g = s.add_mutually_exclusive_group(required=(name == "check"))
        g.add_argument("--code", help="Lean code as a string")
        g.add_argument("--code-file", help="file with Lean code, or - for standard input")
        s.add_argument("--keep", action="store_true",
                       help="keep the definitions in the server's environment (modify_env: true)")
        if name == "eval":
            s.add_argument("--term", required=True, help="the term to evaluate (needs a Repr instance)")
    sub.add_parser("raw", help="send the JSON request on standard input as it is")
    args = p.parse_args()

    if args.cmd == "raw":
        out = post(args.port, "/", sys.stdin.read().encode("utf-8"), args.timeout)
        print(json.dumps(out, indent=2, ensure_ascii=False))
        sys.exit(0)

    payload = {"task": args.cmd, "modify_env": args.keep}
    code = read_code(args)
    if code is not None:
        payload["code"] = code
    if args.cmd == "eval":
        payload["term"] = args.term
    out = post(args.port, "/", payload, args.timeout)
    print(json.dumps(out, indent=2, ensure_ascii=False))
    resp = out.get("response", {})
    if out.get("status") != "ok":
        sys.exit(2)
    if args.cmd == "check":
        sys.exit(0 if resp.get("compiles") else 1)
    sys.exit(0 if resp.get("result") == "ok" else 1)


if __name__ == "__main__":
    main()
