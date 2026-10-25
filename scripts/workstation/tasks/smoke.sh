# Pipeline test: checks the Python environment, builds one small module, checks its axioms and
# pushes a results branch. Takes a few minutes after setup.

TASK_DESC="pipeline smoke test (Python packages, one small Lean module, axioms, push)"
TASK_MODULES="PlasmaLean.SubsetSum"
TASK_ENTRYPOINTS="ConcLean.SubsetSum.subsetSum_correct"
TASK_OUTPUTS=""
TASK_TARGET="default"

task_numerics() {
  "$WS_PY" -I -c 'import numpy, scipy, gmpy2, sympy, mpmath; print("python packages ok")'
}
