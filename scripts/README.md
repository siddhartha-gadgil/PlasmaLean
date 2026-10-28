# scripts/

| Script | Purpose |
| --- | --- |
| [`setup.sh`](setup.sh) | Idempotent setup (Linux/macOS): installs elan if missing, `lake exe cache get`, `lake build`; `--check-axioms` runs the axiom audit, `--python` creates the venv `.venv-ws` from `requirements.txt`, `--no-build`, `--help` |
| [`check_axioms.lean`](check_axioms.lean) | Axiom audit: `lake env lean scripts/check_axioms.lean` checks every declaration of the library (only `propext`, `Classical.choice`, `Quot.sound`) and prints the axioms of the main entry points; add new entry points here |
| [`audit_kernel_fact.py`](audit_kernel_fact.py) | Classifies the kernel-fact leaves of `kernel_fact` proofs (closed literal facts vs. opaque recursive evaluations), to find leaves that should become explicit certificates |
| [`requirements.txt`](requirements.txt) | Python packages for untrusted oracle scripts and the workstation pipeline |
| [`workstation/`](workstation/README.md) | Workstation pipeline: heavy numerics and builds on a big machine, re-checked on the laptop |

Oracle scripts (untrusted numerics that propose certificate data and emit Lean) go in their own
subfolder per family. They must validate every emitted bound in exact arithmetic before writing
Lean, and be run with `python3 -I` on any downloaded data.
