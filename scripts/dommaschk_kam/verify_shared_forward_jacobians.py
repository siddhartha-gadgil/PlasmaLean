"""Check shared-power Jacobian proofs in the existing forward-Jacobian cache."""

from functools import partial

from emit_sparse_forward_jacobian import emit
import verify_sparse_forward_jacobians as verifier


# Set the emitter at import time so spawned verification workers use it too.
# The cache key authenticates the resulting Lean sources and their imports.
verifier.emit = partial(emit, shared=True)

if __name__ == '__main__':
    verifier.main()
