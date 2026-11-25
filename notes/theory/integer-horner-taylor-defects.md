# An integer multiply-add certificate for Taylor models

For a univariate Taylor model with scale \(D=2^b\), let \(A\) be its integer coefficient vector, \(e_A\) its integer radius, and \(\|A\|_1\) the sum of the absolute values of its coefficients. Suppose \(A,X,Q\) enclose three real values \(a,x,q\) at a common normalized time \(s\in[-1,1]\). A proposed output \(V\), of any degree, encloses \(ax+q\) whenever
\[
  e_A(\|X\|_1+e_X)+e_X\|A\|_1+D e_Q
       + \|A*X + D(Q-V)\|_1 \ \le\ D e_V .
\]
The symbol \(*\) denotes exact integer coefficient convolution. Coefficients absent from a shorter vector are zero. In particular the last term charges all discarded coefficients, any changes in the retained coefficients, and signed cancellation from the added polynomial. The inequality uses only integers. It applies to any precision and any normalized time. [Generic soundness theorem](../../PlasmaLean/Certificates/DyadicHornerStep.lean)

To see the bound, write \(U(s)\) for a coefficient vector evaluated without dividing by \(D\). Then \(|Da-A(s)|\le e_A\), and \(|Dx|\le\|X\|_1+e_X\). Subtract \(D V(s)\) from the proposed physical result \(D^2(ax+q)\). The difference is
\[
 (Da-A(s))Dx +(Dx-X(s))A(s)+D(Dq-Q(s))
        +(A*X+D(Q-V))(s).
\]
Each of these four terms has the bound charged above. Dividing the resulting error estimate by \(D\) gives membership in the output Taylor model. The proof also covers negative coefficients and a zero polynomial. [Integer arithmetic and real membership](../../PlasmaLean/Certificates/DyadicHornerStep.lean)

## Field and trajectory application

The nested Horner evaluator applies this certificate to each radial, vertical and harmonic multiplication and addition. Lean recovers the input coefficient vectors from the actual preceding models. A closed natural-number equality, \(\max(L-R,0)=0\) for integer sides \(L,R\), proves the required scalar inequality. The accepted model and its remainder enter the analytic proof before the next multiplication. The sector, sparse field identities and shared real angle in all seven harmonic channels enter through the same physical terms used in the trajectory proof. [Harmonic theorem](../../PlasmaLean/Design/DommaschkDyadicHorner.lean) · [Physical emitter](../../scripts/dommaschk_kam/verify_native_action_models.py)

The benchmark uses the first widened radial tile, all eight original slabs \(0,\ldots,7\), and both clock directions. The input file to the field evaluator is byte-identical under both methods. All 1,081 stored Taylor models agree coefficient by coefficient and radius by radius, including 360 for \(D\), 383 for \(N_R\), and 338 for \(N_z\). The final generated source of the sixteen signed ODE defect theorems is byte-identical, including the original moving frames and both original rational budgets. Each build audits the fully qualified physical field and signed defect declarations for `propext`, `Classical.choice` and `Quot.sound`. [Input and proof comparison](../../scripts/dommaschk_kam/compare_ribbon_horner_checks.py) · [Original widened reference](radial-ribbon-central-defects.md)

At the same 75% single-CPU limit on the workstation, the original rational Horner field checks took 167.170 seconds. The integer checks took 96.192 seconds, a factor of 1.74. The original field key is `1055b484e7bf7e2f738f69ae1ba5fcf3828320124e98e589eb11778527a90690` and the integer field key is `a954bd8bd2a8bcb567b27a122bfa390ba4acf528d22782176ee724eebd9f0dba`. Separate arithmetic controls accepted \((-2)\cdot3+1=-5\) with zero error and a rounded half-scale product within one output tick. They rejected an uncharged rounding error and a discarded nonzero quadratic coefficient.

Including all sixteen signed original defect proofs, the total fell from 215.099 seconds to 142.558 seconds, a factor of 1.51. Peak process RSS over the group was 3,958,336 KiB for the rational method and 3,959,172 KiB for the integer method. The resulting signed group key is `e38319bfec630d11ad6fcd8709e8fd8c6db1bf2590ff5e503ce1765195e82c79`. The measured benefit justified enabling the integer proof for new groups in the four-ribbon and six-endpoint central campaigns. The selection checks the original packet digest and the compiled theorem digest before each group.

The separate spatial benchmark on the same initial eight slabs covers all four widened intervals with one common jet. Its nine field and gradient checks took 90.873 seconds with the integer rule and 171.807 seconds with the rational rule, a factor of 1.89. The nine models agree entry for entry and the ten ground declarations passed their audits. The spatial group key is `db6dc7766e8d471736c7c31d2d3d3fd431950706b72911c03c1ba56d70710624`. [Spatial field and derivative replay](../../scripts/dommaschk_kam/verify_ribbon_dyadic_jet.py)

## Replay

~~~bash
lake build PlasmaLean.Design.DommaschkDyadicHorner PlasmaLean.Design.DommaschkVariableHorner \
  PlasmaLean.Design.DommaschkGroupedTrialJet PlasmaLean.Design.DommaschkPhysicalCentralJet
py=.venv-ws/bin/python
dir=scripts/dommaschk_kam
export LEAN_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
"$py" "$dir/screen_radial_birth_ribbon.py" --stop 340 --output /tmp/four-radial-ribbons.json
"$py" "$dir/verify_ribbon_central_group.py" --ribbon /tmp/four-radial-ribbons.json --tile 0 \
  --span 0 8 --output /tmp/ribbon-rational.json
"$py" "$dir/verify_ribbon_central_group.py" --ribbon /tmp/four-radial-ribbons.json --tile 0 \
  --span 0 8 --integer --output /tmp/ribbon-integer.json
"$py" "$dir/compare_ribbon_horner_checks.py" --original /tmp/ribbon-rational.json \
  --integer /tmp/ribbon-integer.json --output /tmp/ribbon-comparison.json
~~~

To select the measured verifier in the ribbon campaign, add `--activate-ribbon .lake/ribbon-central-campaign` to the last command. The same comparison can select it in named endpoint campaign directories through `--activate-endpoints`. Previously accepted groups retain their own authenticated keys.

## Metadata

| Field | Value |
| --- | --- |
| ID | N-177 |
| Kind | Candidate-independent fixed-point Taylor multiply-add and physical performance measurement |
| Addresses | G-10, Q-16, Q-35 |
| Depends on | N-94, N-166, N-170, N-173 |
| Dependency requirement | A common dyadic scale, normalized time in the closed unit interval, three certified inputs and an exact integer error bound |
| Status | Generic inequality proved, 1,081 concrete model equalities and sixteen signed original theorems audited. Integer verification enabled for subsequent central groups. |
| Produces | A reusable kernel-checked Horner step for rounded physical field models and a same-input comparison on the widened radial birth family |
| Lean evidence | `DyadicHornerStep.Fits.mem`, `DyadicHornerStep.MulAdd.mem`, `DommaschkDyadicHorner.Run.mem`, `DommaschkDyadicHorner.channel_cons` |
| Last updated | 25 November 2026 |
