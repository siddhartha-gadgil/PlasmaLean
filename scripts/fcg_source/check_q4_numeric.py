"""Numeric check (N-42) of (Q4) [C,K] = S and the (Q7) cancellation, K v = v x b."""
import numpy as np
rng = np.random.default_rng(1)
def cross_mat_vxb(b):  # K v = v x b
    return np.array([[0, b[2], -b[1]], [-b[2], 0, b[0]], [b[1], -b[0], 0]])
for trial in range(4):
    b = rng.normal(size=3); b /= np.linalg.norm(b)
    K = cross_mat_vxb(b)
    v = rng.normal(size=3); assert np.allclose(K @ v, np.cross(v, b))
    S0 = rng.normal(size=(3, 3)); S0 = S0 + S0.T
    P = np.eye(3) - np.outer(b, b)
    S1 = S0 - (b @ S0 @ b) * np.outer(b, b)
    S = S1 - np.trace(S1) / 2 * P
    a = S @ b; Sp = P @ S @ P
    C = np.outer(b, K @ a) + np.outer(K @ a, b) - 0.5 * Sp @ K
    C1 = np.outer(b, K @ a) + np.outer(K @ a, b)
    comm = C @ K - K @ C
    print(trial, 'sym', np.allclose(C, C.T), '[C,K]-S', np.abs(comm - S).max(), '[C,K]+S', np.abs(comm + S).max(),
          '| [C1,K] vs ba+ab', np.abs(C1 @ K - K @ C1 - (np.outer(b, a) + np.outer(a, b))).max(),
          '| [-SpK/2,K] vs Sp', np.abs((-0.5*Sp@K)@K - K@(-0.5*Sp@K) - Sp).max(), np.abs((-0.5*Sp@K)@K - K@(-0.5*Sp@K) + Sp).max())
    # R_b(v^T C v) = (v x b).grad_v(v^T C v) = 2 (Kv)^T C v ; compare with v^T [C,K] v
    print('   R_b quad vs v^T[C,K]v:', 2*(K@v) @ C @ v, v @ comm @ v, ' v^T S v:', v @ S @ v)
    # Q7 cancellation: -eps v^T S v + 2 eps v^T D (v x B) with D=C/beta, v x B = beta K v
    print('   Q7 residual (-vSv + 2 v^T C K v):', -(v @ S @ v) + 2 * (v @ C @ K @ v))
