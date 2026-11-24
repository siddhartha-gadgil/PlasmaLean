# Observe a shorter interval on a full physical field line

Suppose a signed physical trajectory has been proved through $n$ outward slabs on each side of a section. An independent field or geometry certificate covers $m$ slabs. For any $1\le k\le\min(m,n)$, the first $k$ rows of each archive suffice to establish the observable on $[-k/64,k/64]$. The section crossing, both terminal states at $\pm n/64$, and the physical ODE on the full signed interval refer to the same trajectory. [Physical passage and observation theorem](../../PlasmaLean/Design/DommaschkSubmirrorPrefixObservation.lean)

This is a restriction theorem for an arbitrary pointwise predicate. An ordered tube certificate consists of a statement on the first closed slab and a certificate on the tail with the new start state and clock. Induction on the number of retained slabs proves `OnTubes.take`. Splitting the original physical list into `take` and `drop` then gives `OnTubes.on_initial`. An inverse of a field map, a new ODE solve, or recomputation of the scalar enclosure is unnecessary. [Ordered observation restriction](../../PlasmaLean/Certificates/PositionFrameObservationPrefix.lean)

The signed application checks the forward observable at $t$ and the backward observable at $-t$. One through-birth proof supplies the physical approach, common section state and full signed trajectory. The two original row lists are compared definitionally through exactly $k$ rows. The result chooses one pair of embedded nested KAM tori before every admissible birth azimuth. The generic theorem accommodates any section phase. The executable currently authenticates the phase-zero QA2R packets. [Physical archive consumer](../../scripts/dommaschk_kam/verify_submirror_prefix_projection.py)

## Checked differences in archive length

The complete 160-row physical path at $u=478/1000$ now carries the quantitative bound in both directions. For every $|\phi|\le2^{-19}$, its actual birth reaches the section and one signed physical trajectory satisfies $|B|<h_L-1/270000$ at every $t\in[-5/2,5/2]$, with its certified states at both endpoints. The 160-row signed path has key `6d3c4ccc2cf4302f47b2aa516889e35be9231d1c50e2b26b2276f58e2bcad72f`. The 317-row numerical parent has key `073471cfdf5da3891484ecdebfb9ed1927dde4092c20e6c55b6df1f2f90606b6`. Lean checked `DommaschkQ0R478Drop1Over270000Observation160On160From317.from_birth` and its entry-level companion in 6.855 seconds, proof key `8768e9cf95432ba2d173b1958a16f911d009d2d8e9a1462280c5da7a18c089e6`.

At $u=478/1000$ the complete 317-row archive from N-135 gives $|B|<h_L-1/270000$ on both sides. Restricting it to the 128-row actual trajectory yields the physical bound on $[-2,2]$ with both original terminal states. Its proof key is `e7f0870e9285f4fb5deceafcff4e14427dcd84130b37b8986ad0635a0372855b`. Compilation and axiom auditing took 6.04 seconds on the workstation. [Quantitative field archive](quantified-grouped-mirror-clearance.md)

The converse ordering was checked at $u=523/1000$. A five-row scalar archive gives $|B|<h_L$ for $|t|\le5/64$ on a 48-row physical trajectory, retaining both terminal states at $t=\pm3/4$. The proof key is `c2c68373546cc7e9f57668128f0d4bebce312bfe2acb195b9fc66c4de5f16ed8`, with 4.34 seconds for verification. The checker rejects a request to observe 129 slabs from a physical certificate of length 128. Each positive result uses only `propext`, `Classical.choice` and `Quot.sound`. [Original signed paths and submirror estimates](outer-phase-zero-submirror-births.md)

## Reproduction

```sh
lake build PlasmaLean.Design.DommaschkSubmirrorPrefixObservation
.venv-ws/bin/python scripts/dommaschk_kam/verify_submirror_prefix_projection.py \
  --launch 478 --archive /tmp/plasma-n135-q0r478-317.json \
  --signed .lake/secondary-trace-campaign/q0r478/prefixes/160.json \
  --output /tmp/observed-478-160.json
.venv-ws/bin/python scripts/dommaschk_kam/verify_submirror_prefix_projection.py \
  --launch 523 --archive /tmp/plasma-n131-q0r523-early005.json \
  --signed .lake/secondary-trace-campaign/q0r523/prefixes/048.json \
  --output /tmp/observed-523-5-on-48.json
```

The output records the physical horizon, the independent observable horizon and the observed length. Passing `--length` selects a smaller nonempty interval. The signed, numerical and generated Lean inputs are verified from their contents before compilation.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-141 |
| Kind | Reusable physical observation theorem and concrete signed archive reattachment |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-121, N-131, N-135, authenticated signed physical prefixes |
| Dependency requirement | The observed initial rows coincide in their chronological order and original physical entry state |
| Status | Implemented at three concrete archive-length combinations, including the 160-row two-sided physical trajectory |
| Lean evidence | `OnTubes.take`, `OnTubes.on_initial`, `DommaschkSubmirrorPrefixObservation.of_birth` and the two physical declarations in each generated package |
| Audit evidence | Both orderings of the independent horizons, the 160-row through-birth application, the overlength rejection and the three standard axioms |
| Last updated | 25 November 2026 |
