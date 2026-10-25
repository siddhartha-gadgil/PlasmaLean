# Task template for scripts/workstation/run.sh. Copy to tasks/<name>.sh and fill in.
# The file is sourced by bash (3.2-compatible); run.sh runs from the repository root and exports
#   WS_PY    the venv Python (numpy, scipy, gmpy2, sympy, mpmath; see scripts/requirements.txt)
#   WS_WORK  scratch directory for large intermediate data (not committed)
#   WS_JOBS  parallelism to use
#   WS_REPO  repository root

TASK_DESC="one line: what is computed and certified"

# Lean modules built (one at a time, measured), dependencies first. Their peak memory must fit
# the laptop (LAPTOP_MAX_RSS_GB, default 6): split large certificates over several modules.
TASK_MODULES="PlasmaLean.Design.ExampleData PlasmaLean.Design.ExampleCert"

# Main theorems; #print axioms must show only propext, Classical.choice, Quot.sound.
TASK_ENTRYPOINTS="PlasmaLean.Design.ExampleCert.example_theorem"

# Files committed to the results branch on success (the generated Lean and any small data the
# Lean files or later runs need). Large intermediates stay in $WS_WORK.
TASK_OUTPUTS="PlasmaLean/Design/ExampleData*.lean PlasmaLean/Design/ExampleCert.lean"

# Optional small files (<= 50 MB each) copied to workstation/artifacts/<task>/ for later runs.
TASK_ARTIFACTS=""

# default: imported by PlasmaLean.lean (<= 60 CPU-min); separate: on-demand top module.
TASK_TARGET="default"

# Untrusted numerics: searches, Newton refinement, interval data. Must be restartable.
task_numerics() {
  mkdir -p "$WS_WORK/example"
  "$WS_PY" -I scripts/example_oracle.py --jobs "$WS_JOBS" --out "$WS_WORK/example"
}

# Turn the numerical witness into Lean source (data defs + certificate modules).
task_emit() {
  "$WS_PY" -I scripts/example_emit_lean.py "$WS_WORK/example" PlasmaLean/Design/
}
