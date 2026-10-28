# Certificates/

Certificate formats: exact data, a checker or inductive certificate predicate, a **soundness
theorem** (certificate ⇒ the mathematical statement for every real point, mode or cell), and a
proof-term builder. Large checks are explicit proof terms whose leaves are kernel facts (the
SubsetSum pattern, `../SubsetSum.lean`); no `decide` of any kind.

How to choose: a few closed facts → `norm_num`/`rfl`; a closed conjunction or list quantifier →
`kernel_fact`; evaluation of a closed term (records, recursion, balls) → `eval_cert` /
`fiv_cert`; a Boolean checker over lists → `bool_cert`; a new large format → write it in the
SubsetSum pattern. `eval_decide` and `fiv_decide` are evaluation certificates of `decide p`
(the tactic `decide` itself is not used).

| Module | Content | Tactics |
| --- | --- | --- |
| [`BlockBounds`](BlockBounds.lean) | Exact rational certificates for two-block lower bounds |  |
| [`BoolCert`](BoolCert.lean) | Boolean checkers as explicit certificates (`bool_cert`) | `bool_cert` |
| [`Contraction`](Contraction.lean) | Local contraction validation and its equation bridge |  |
| [`ConvAlgebra`](ConvAlgebra.lean) | `ℓ¹(ℤ)` as a commutative Banach algebra, and its exponential |  |
| [`DigitSumCert`](DigitSumCert.lean) | Kronecker digit sums `l1Kron` as explicit certificates (`l1kron_cert`) | `l1kron_cert` |
| [`DiscreteMaxPrinciple`](DiscreteMaxPrinciple.lean) | Discrete maximum and comparison principles for the radial transport scheme |  |
| [`EvalCert`](EvalCert.lean) | Evaluation certificates for ball, interval and polynomial terms (`eval_cert`) |  |
| [`EvalCertFIv`](EvalCertFIv.lean) | Evaluation certificates for fixed-point interval checkers (`fiv_cert`) | `fiv_cert`, `fiv_decide` |
| [`Example`](Example.lean) | Certificate example: a verified amplitude bound for a family of oscillator states |  |
| [`FamPackCert`](FamPackCert.lean) | Kronecker images of families as explicit certificates (`fampack_cert`) | `fampack_cert` |
| [`FourierRegularity`](FourierRegularity.lean) | From Fourier-coefficient equations to classical solutions |  |
| [`IccListCert`](IccListCert.lean) | Finite sums and quantifiers over integer intervals as list computations (`icc_cert`) | `icc_cert`, `icc_close` |
| [`KernelFact`](KernelFact.lean) | Closed side conditions as explicit proof terms (`kernel_fact`) | `kernel_fact` |
| [`KronBall`](KronBall.lean) | Ball arithmetic in the strip algebra by Kronecker certificates |  |
| [`KronBallCheb`](KronBallCheb.lean) | Ball arithmetic for families: Chebyshev series in a parameter with ball coefficients |  |
| [`KronBallChebChain`](KronBallChebChain.lean) | Steps of family ball chains from kernel data |  |
| [`KronBallChebDigits`](KronBallChebDigits.lean) | Fast weighted digit sums of packed integers (kernel arithmetic) |  |
| [`KronBallChebEnv`](KronBallChebEnv.lean) | Environments of family ball chains |  |
| [`KronBallChebFam`](KronBallChebFam.lean) | Family environments: fast images, constants, embeddings |  |
| [`KronBallChebGrid`](KronBallChebGrid.lean) | Grid families: compact storage and fast Kronecker images |  |
| [`KronBallChebNorm`](KronBallChebNorm.lean) | Norms of families from Kronecker images |  |
| [`KronBallChebSpread`](KronBallChebSpread.lean) | Spreading and reversing digit expansions with masks |  |
| [`KronBallGrid`](KronBallGrid.lean) | Grid centres for the Kronecker ball arithmetic |  |
| [`KronBallLowMem`](KronBallLowMem.lean) | Soundness of the low-memory kernel quantities |  |
| [`KronChebCompute`](KronChebCompute.lean) | The kernel computations of family ball chains (light module) |  |
| [`KronExpr`](KronExpr.lean) | Weighted polynomial expression trees for Kronecker certificates |  |
| [`KronLowMemCompute`](KronLowMemCompute.lean) | Low-memory kernel computations of family ball chains (light module) |  |
| [`KronProof`](KronProof.lean) | Kronecker ball checks as explicit proof terms (SubsetSum pattern) | `kron_lt`, `kron_proof` |
| [`KronProof2D`](KronProof2D.lean) | Two-dimensional Kronecker ball checks as explicit proof terms (`kron2_proof`) | `kron2_proof` |
| [`Kronecker2D`](Kronecker2D.lean) | Exact ℓ¹ norms of bivariate integer polynomials by Kronecker substitution |  |
| [`Kronecker2DWeighted`](Kronecker2DWeighted.lean) | Weighted ℓ¹ norms of trigonometric polynomials by Kronecker substitution |  |
| [`PolyInterval`](PolyInterval.lean) | Exact polynomial positivity certificates on intervals |  |
| [`RadiiPolynomial`](RadiiPolynomial.lean) | The radii polynomial theorem (Newton-like form) |  |
| [`RationalIntervals`](RationalIntervals.lean) | Exact rational enclosure core |  |
| [`SBP`](SBP.lean) | Summation-by-parts (SBP) operators and the discrete energy law |  |
| [`SBPGeneral`](SBPGeneral.lean) | The classical second-order SBP operator on `N ≥ 3` points |  |
| [`ValidatedQuadrature`](ValidatedQuadrature.lean) | Validated quadrature: fixed-point interval arithmetic and sound cell sums |  |
| [`ValidatedQuadratureArcs`](ValidatedQuadratureArcs.lean) | Validated quadrature for periodic integrands with a sharp peak |  |
| [`ValidatedTrig`](ValidatedTrig.lean) | Validated transcendental functions on fixed-point enclosures |  |
| [`ValidatedTrigFast`](ValidatedTrigFast.lean) | Fast validated `arctan`, `arcsin`, `cosh`, `sinh` on fixed-point enclosures |  |
| [`WeightedEll1`](WeightedEll1.lean) | The weighted sequence space ℓ¹_ν(ℤ) and its Banach-algebra estimate |  |

`eval_cert` is defined in `LeanTheoryMeta/EvalCert.lean` (precompiled `meta` code) and
re-exported by `EvalCert.lean`. `Example.lean` is the end-to-end example of the template.
