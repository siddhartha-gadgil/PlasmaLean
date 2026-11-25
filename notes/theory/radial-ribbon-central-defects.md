# Central ODE defects for the continuous radial birth interval

Four widened launch balls cover all labels \(u\in[0.470,0.478]\) in the phase-zero birth family. The radius of each ball in the section plane is \(2^{-16}\). The central polynomial used for the ODE enclosure differs between these four balls. We check the defect along each original central polynomial in its own time-dependent frame. These bounds supply the inhomogeneous term in the estimate for the entire surrounding tube. [Launch coverage and exterior signs](upper-radial-ribbon-entry-and-caps.md)

## The central estimate

On row \(i\), let \(s=128t-2i-1\), let \(x_i(s)\) be the stored signed centre and let \(P_i(s)\) be the original affine matrix. For time \(t\in[i/64,(i+1)/64]\), the checked statement reads
\[
 \left\|P_i(s)^{-1}\left(V_\sigma(t,x_i(s))-128\,x_i'(s)\right)\right\|_2
 \le d_{i,\sigma},
\]
where \(d_{i,\sigma}\) is the exact original rational defect budget and \(\sigma\) is the outward clock sign. The degree-twelve Horner model evaluates the three physical polynomials \(D,N_R,N_z\) in the QA2R field on a group clock. Affine substitution into the original row clock and outward rounding produce the three field models used in the inequality. The exact section-zero reflection identifies both centred error norms. The checker verifies the coordinate and moving-frame identities and then tests the bound against both original signed budgets. [Shared-clock theorem](grouped-physical-central-defects.md) · [Signed source data](../../scripts/dommaschk_kam/ribbon_central_data.py)

Every physical defect theorem in a group keeps its original mathematical namespace. One compiled module contains its row inputs, the field restrictions and all signed defect proofs. Lean audits every fully qualified theorem name individually. The cache binds those names, the source bytes, the original ribbon digest and the authenticated field proofs. The paired receipts give the trajectory consumer both the module to import and the original signed theorem to apply. [Grouped physical proof](../../scripts/dommaschk_kam/verify_ribbon_central_group.py)

## Coverage through the exterior mirror cap

The exact arithmetic screen covers all four pairs of traces through \(332/64=83/16\). Each tile has forty-one groups of eight and one group of four. The largest ratio of the proposed central defect to the smaller signed allowance on each tile is shown below, rounded upward. This ratio can exceed 99.9% because the interpolated radial references already use most of the archived defect allowance. [Exact planner](../../scripts/dommaschk_kam/plan_ribbon_central_groups.py)

| Radial labels | Interpolated center | Signed allowances | Largest ratio | Row |
| --- | ---: | ---: | ---: | ---: |
| [0.470, 0.472] | 0.471 | 664 | 0.999489 | 272 |
| [0.472, 0.474] | 0.473 | 664 | 0.999541 | 74 |
| [0.474, 0.476] | 0.475 | 664 | 0.999546 | 74 |
| [0.476, 0.478] | 0.477 | 664 | 0.999456 | 76 |

Lean verified all forward and backward central defects on rows 0–7 for each of the four tiles. These are 64 original signed claims on the first \(1/8\) radian of elapsed angle in each direction. The four group receipts, in increasing radial order, are `05a41b98a16f25bb04db979fe52475db44fa31c7847009449af4a2146ef804c5`, `3193fa2c1c3ab7ad26721066763530a43064798cb06fb76be0259ee1ad00e60f`, `b55df6ceefb981722617581cd51e0972237842addcf1cd367f3cb962968f9992` and `25214c3cfe9d26da95d5b71b0670d7251e2ff39293cc6469d818508858659156`. After compiling the three shared physical fields, the eight row restrictions and sixteen signed defect claims in each group took 38.7–47.9 seconds. Peak Lean process RSS in this stage was below 3.78 GiB. Each fully qualified theorem passed the `propext`, `Classical.choice` and `Quot.sound` audit.

The original four-ribbon input has SHA-256 `c4f65ab5d7727fc5fdbae645c6924ecde6b474f521663a8b1b9de6be8d45a486`. The verifier checks both signed references, frames and budgets directly from this witness, which can be regenerated from the two published endpoint packets. The long verification resumes from authenticated pairs of central theorems. It reuses the field proof when a group of row declarations needs to be split for a bounded-memory build. The spatial Jacobians and through-birth trajectory assembly have separate verification records. [Ribbon construction](../../scripts/dommaschk_kam/screen_radial_birth_ribbon.py) · [Resumable verifier](../../scripts/dommaschk_kam/run_ribbon_central_campaign.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkVariableHorner PlasmaLean.Design.DommaschkGroupedTrialJet \
  PlasmaLean.Design.DommaschkPhysicalCentralJet PlasmaLean.Design.DommaschkSectionReflection
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 LEAN_NUM_THREADS=1
"$py" "$dir/screen_radial_birth_ribbon.py" --stop 340 --output /tmp/four-radial-ribbons.json
"$py" "$dir/plan_ribbon_central_groups.py" --ribbon /tmp/four-radial-ribbons.json \
  --output /tmp/radial-central-plan.json
"$py" "$dir/verify_ribbon_central_group.py" --ribbon /tmp/four-radial-ribbons.json \
  --tile 0 --span 0 8 --handoff .lake/ribbon-central-campaign --output /tmp/radial-first-group.json
"$py" "$dir/run_ribbon_central_campaign.py" --ribbon /tmp/four-radial-ribbons.json \
  --plan /tmp/radial-central-plan.json --workers 3 --reserve-cores 3 --reserve-gib 40
~~~

## Metadata

| Field | Value |
| --- | --- |
| ID | N-173 |
| Kind | Original signed central ODE certificates for the four radial intervals |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-119, N-166, N-169 |
| Dependency requirement | Signed ribbon interpolation and frames, physical harmonic field identity, rational interval restrictions and complete original defect budgets |
| Status | 64 original signed inlet defects checked. The exact proposed cover spans all 2,656 signed original budgets through \(332/64\). Full slab-by-slab kernel verification is running. |
| Produces | Row-indexed physical central defects for the widened radial tubes, plus a resumable proof campaign to the common exterior time |
| Lean evidence | `DommaschkTraceResidualQ0R{471,473,475,477}{Forward,Back}000.physical_defect` and the corresponding signed declarations through 007 |
| Last updated | 25 November 2026 |
