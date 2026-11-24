# Full-trace Jacobian budgets and the physical chain criterion

| Field | Value |
| --- | --- |
| ID | N-66 |
| Kind | Exact numerical certificate screen and conditional physical theorem |
| Addresses | Q-35, Q-1, G-6, G-10 |
| Depends on | N-60 through N-65 |
| Dependency requirement | Each field bound must hold on the ball and clock defined by that same saved row. |
| Produces | A validated arithmetic route for all archived Jacobian budgets and a Lean theorem converting physical row bounds into a trace from a Q-16 birth. |
| Difficulty | Generating and composing the individual physical Lean proofs efficiently. |
| Status | All 6,256 sparse Jacobian budget checks pass externally. The projection, spatial-cover lemma, and conditional trace criterion are proved in Lean. |
| Lean evidence | `HilbertRetraction.radial_retraction`, `PositionFrameSlabs.physical_step_ball`, `TrajectoryTaylorModel.cover_spatial_radius`, `DommaschkMirrorLaunch.exists_nested_frame_paths` |
| Audit evidence | Default and heavy standard-axiom checks passed for 54,512 and 93,146 project declarations. |
| Last updated | 24 November 2026 |
| Patches | N-64 and N-65, coverage of the feasibility checks and remaining physical hypotheses |

## What the exact calculation establishes

The first-order spatial bound required on a trial tube is the upper bound on the largest eigenvalue of the *symmetric part* of the moving-frame Jacobian. Every archived budget passes for both directions at all eight endpoints. The calculations include the uncertainty in the two physical coordinates as well as the entire normalized time interval. The counts below record the first test that succeeds for each slab. [Reproducible checker](../../scripts/dommaschk_kam/screen_sparse_jacobians.py) · [Results and witness hashes](../../scripts/dommaschk_kam/results/bounce_sparse_jacobian_screen.json)

| Bound used | Additional directed slabs |
| --- | ---: |
| Half-trace and traceless-part bound on the whole slab | 5,446 |
| Positive-semidefinite test on eight time subintervals | 198 |
| Split the physical coordinate enclosure into 2 × 2 boxes | 602 |
| Split it into 4 × 4 boxes | 10 |
| **Total** | **6,256** |

Together with the central defect screen in N-65, this accounts for the two quantitative field estimates on every row in exact external arithmetic. The physical solution has a complete Lean enclosure on the first forward slab. Independent Lean workers build further rows and check the axioms of each result before retaining it. A checked defect on an isolated row does not extend the physically enclosed time interval. [Reference defect results](dommaschk-first-physical-step.md) · [Resumable Lean verifier](../../scripts/dommaschk_kam/verify_sparse_reference_slabs.py)

## What suffices for a physical long trace

Fix the single nested pair of Q-16 tori supplied by the theorem. Choose one of the eight endpoints, a birth in the corresponding small sector, an outward direction, and a prefix of $n$ saved rows. Suppose the scalar chain accepts those rows, and on each recorded trial ball the **actual** QA2R field satisfies the required continuity, spatial derivative, quadratic and reference-defect bounds. A physical solution then starts at the very state reached by the birth at the common section, obeys the field-line ODE through $n/64$ radians and belongs to each recorded tube including its endpoints. The final state is a member of the saved exit ellipsoid. At $n=391$ this is the desired sufficient statement for either long direction. The result accepts both directions; each has its own interval and reference. [Precise physical theorem](../../PlasmaLean/Design/DommaschkMirrorFramePath.lean)

Projection onto a closed ball is a 1-Lipschitz retraction in a real Hilbert space. Using this in the local existence proof allows continuity and the quantitative derivative checks to use the same ball. This removes the need for a second field calculation on an enclosing coordinate square. Lean also proves that smaller dyadic spatial intervals cover a larger trial interval, which supports the subdivided matrix tests above. [Hilbert-space retraction](../../PlasmaLean/Theory/Fields/HilbertRetraction.lean) · [Moving-frame step on the ball](../../PlasmaLean/Certificates/PositionFrameBall.lean) · [Dyadic spatial cover](../../PlasmaLean/Certificates/TrajectorySpatialSplit.lean)

## Reproduction on the workstation

```sh
.venv-ws/bin/python scripts/dommaschk_kam/screen_sparse_jacobians.py --workers 6 --panels 8 --spatial 4 scripts/dommaschk_kam/results/bounce_frame_q*_u*.json.gz
lake build PlasmaLean.Design.DommaschkMirrorFramePath
.venv-ws/bin/python scripts/dommaschk_kam/verify_sparse_reference_slabs.py --workers 6 --range 0 7
```

The last command checks the reference defect on both directions of the first eight slabs at radius 0.470. It retains generated sources, kernel artifacts and the per-theorem axiom audit under `.lake/trace-residual`. After a restart it can reuse an accepted result whose inputs and compiled artifacts match their recorded hashes. The target beyond local field-line geometry still needs the radial variation and action estimates, angular coverage, and a physical time and birth criterion. [Endpoint application](dommaschk-local-action-graphs.md)
