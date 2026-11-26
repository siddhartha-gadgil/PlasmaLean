# Lipschitz labels: guiding-centre drift without flow derivatives

**26 November 2026.** Method note for N-214, and a correction to it. A label defined through the field-line flow (the point where the field line meets a section) is naturally Lipschitz, with a constant from a Grönwall estimate; its derivative is not needed. Lean now proves the drift bound for such labels. The existing QA2R trajectory certificates do not supply the Lipschitz constant: they bound error growth away from the section only. C2 remains open.

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-215` |
| Title | Lipschitz labels: guiding-centre drift without flow derivatives |
| Kind | Method note and patch for N-214 (proof; assessment of certificates; untrusted computation) |
| Addresses | G-10, Q-35; RG.5 item 2 |
| Depends on | N-214; N-66 and the position-frame certificates (`Certificates.PositionFrameODE.FieldBounds`, `PositionFrameChain.Chain.trajectory`); `Fields.LogNormTrajectory.dist_le_of_residual` |
| Dependency requirement | The Littlejohn model (supplied); the statement of `FieldBounds` (which sign of the logarithmic norm is certified). |
| Produces | `Fields.LipschitzLabel.displacement_le`, `Kinetic.LabelDrift.lipschitz_displacement_le`; the precise missing certificate; untrusted values of the constants on the sector. |
| Difficulty | The theorem is moderate (a Dini-derivative argument). The missing certificate is a campaign: a lower logarithmic-norm bound on every slab of the traces used. |
| Status | General theorems verified (default build). QA2R instance: blocked on a backward (lower) logarithmic-norm certificate and on a label domain thicker than the present tubes. |
| Lean evidence | `PlasmaLean/Theory/Fields/LipschitzLabel.lean`: `InvariantOn`, `invariantOn_linear`, `eventually_abs_sub_le`, `displacement_le`. `PlasmaLean/Theory/Kinetic/LabelDrift.lean`: `curlb_vacuum`, `drift`, `velocity_vacuum`, `norm_drift_le`, `lipschitz_displacement_le`. Default build, standard axioms only. |
| Audit evidence | Not audited. Numerics: `scripts/dommaschk_kam/screen_label_drift.py`, `scripts/dommaschk_kam/results/label_drift_20261126.json`. |
| Last updated | 26 November 2026 (created) |
| Patches | N-214, section "What a usable certificate needs", item 1, and the first open question: the label gradients are **not** routine consequences of the existing Jacobian certificates. |

## Correction to N-214

N-214 said that certified label gradients are routine because "the variational matrices of the signed traces are already enclosed by the campaign". That is wrong. Each slab certificate (`FieldBounds.quadratic`) is an **upper** bound `⟪w, J̃ w⟫ ≤ μ ‖w‖²` for the Jacobian in the moving frame. With Grönwall it bounds how far two solutions separate when followed **away** from the section. A label is the map back to the section, so its Lipschitz constant needs the opposite inequality, `⟪w, J̃ w⟫ ≥ −μ′ ‖w‖²`, which no Step record contains and no generated module proves.

## The theorem (compiled Lean, default build)

Setting: a real Banach space, an open set U, a vector field V that is C¹ on U, and a function L.

- **`InvariantOn V L U`**: L takes the same value at both ends of every integral curve of V that stays in U.
- **`displacement_le`**: suppose L is invariant and every point of U has a neighbourhood on which L is K-Lipschitz. Let X have velocity λ(t) V(X) + w(t) on [0, T], stay in U, and satisfy K ‖w(t)‖ ≤ c. Then |L(X(t)) − L(X(0))| ≤ c t.
- **`velocity_vacuum`**: where B is nonzero, differentiable and curl-free, the Littlejohn velocity is (v∥/|B|) B + drift, with drift = (m v∥² + μ|B|)/(q|B|²) b × ∇|B|.
- **`norm_drift_le`**: for m, μ ≥ 0 the drift speed is at most 2H/(|q||B|²) ‖∇|B|‖.
- **`lipschitz_displacement_le`**: for a Littlejohn orbit in an open region where B is C¹, nonzero and curl-free, and an invariant locally K-Lipschitz label L: if K · 2H/(|q||B|²) ‖∇|B|‖ ≤ c at the states visited, then |L(X(t)) − L(X(0))| ≤ c t.
- **`invariantOn_linear`** (sanity): for a constant field, a continuous linear functional vanishing on the field direction is an invariant label.

Proof idea: compare the path just after time t with the field line through X(t), run for the parameter λ(t)(z − t). The two differ by w (z − t) + o(z − t); the label is constant on the field line and K-Lipschitz, so the right upper Dini derivative of L(X) is at most K ‖w‖. Mathlib's boundary comparison lemma then gives the linear bound. No derivative of L and no differentiability of the flow in the initial point is used.

Hypotheses to keep in view: the orbit is supplied; the label, its invariance and its Lipschitz constant are inputs. No label is constructed for QA2R.

## Constants on the sector (numerical observation, untrusted)

Units as in N-214 (lengths in R₀, ε = ρ/R₀). Label: section coordinates at φ = 0.

| Quantity | Value (u = 0.470 … 0.478) |
| --- | --- |
| Lipschitz constant of the label along the well (largest norm of the inverse variational matrix) | 1.86 |
| Largest drift speed across field lines | 0.617 ε |
| Integral of (local Lipschitz constant × drift speed) over a half bounce | 92 ε … 94 ε |
| Uniform bound K · (drift speed) · (half-bounce time) | 148 ε … 151 ε |
| Actual label motion per half bounce (N-214) | 25 ε radial excursion, 55 ε precession |

So the direct bound would overestimate the motion per half bounce by a factor of about 1.5 to 2.5 only. The label is well conditioned along the whole well; the obstacle for the sector is its size (N-214), not the constants.

## What a QA2R instance needs

1. **A backward bound on each slab.** Add a lower logarithmic-norm value to the Step record and a second inequality to `FieldBounds`, with the generated field enclosures proving both signs. The reduced Jacobian in the moving frame is small in both directions, so the values should be of the size of the present `mu`. This means regenerating and recompiling the slab proofs of every trace used (332 slabs per direction and label).
2. **A two-sided Grönwall step** in `LogNormTrajectory`: the present `dist_le_of_residual` applied to the time-reversed field gives the lower distance bound, hence the Lipschitz constant of the section map on a tube.
3. **The label on an open set.** The tube around one trace has physical radius below 1/300000, so a thermal guiding centre crosses it in about one percent of a half bounce. A useful domain needs traces on a grid in both section coordinates with overlapping tubes, as in N-214 items 2 and 3.

Item 3 dominates the cost. It is the same enlargement of the certified region that N-214 requires, so items 1 and 2 are best done as part of that campaign and for the population chosen for it.

## Reproduction

```bash
lake build PlasmaLean.Theory.Kinetic.LabelDrift
cd scripts/dommaschk_kam
../../.venv-ws/bin/python screen_label_drift.py --output results/label_drift_20261126.json
```
