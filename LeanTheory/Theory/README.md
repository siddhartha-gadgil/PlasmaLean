# Theory/

General, domain-independent mathematics used by bridges and certificates. Results here never
depend on a kernel law.

## KAM/ — strip algebras, Fourier analysis and Newton iterations

| Module | Content |
| --- | --- |
| `Diophantine`, `DiophantineB` | Diophantine frequencies, quadratic irrationals, explicit constants |
| `WeightedEll1Z2` | The Banach algebra `ℓ¹_r(ℤ²)` of analytic functions on the complex strip |
| `Cohomological` | The cohomological equation on the 2-torus in weighted `ℓ¹` norms |
| `Composition` | Composition of polynomials with Banach-algebra elements |
| `StripAlgebra`, `StripEval`, `StripSmooth` | Double Fourier series with bounds on several strips; evaluation; smoothness |
| `StripPaleyWiener`, `SampledBound` | Paley–Wiener bounds, certified aliasing, strip norms from samples |
| `FourierSumHolo`, `CauchyTwoVar`, `TorusFieldAna` | Joint holomorphy of Fourier series, two-variable Cauchy estimates, analytic fields along a complexified torus |
| `AnalyticComposition`, `AnalyticCompositionLip` | Analytic composition in Banach algebras and its Lipschitz bounds |
| `InvSqrt`, `InvSqrtApprox` | Inverse square roots in Banach algebras, a posteriori bounds |
| `PolyExprS`, `PolyExprSStrip`, `PolyExprSConstMono`, `PolyExprSMajQ`, `PolyExprSMajQG` | Expression trees with an inverse-square-root node and kernel-computable majorants |
| `ParamInterp` | Interpolation in a parameter with an analytic remainder bound |
| `KamSequence` | Convergence of KAM/Newton iterations with loss of analyticity |

## Stability/ — comparison and energy methods

| Module | Content |
| --- | --- |
| `Suydam` | Hardy inequality and a localized quadratic form (needed by `Newcomb`) |
| `Newcomb` | Picone–Riccati certificates for variable-coefficient radial quadratic forms |
| `RiccatiComparison` | Conditional Riccati comparison and exponential decay |
| `AbstractEnergy` | Conditional energy theorem on a real normed space |
| `BlockBounds` | Quantitative two-block and perturbation inequalities |

## Fields/ — vector calculus and ODE barriers

| Module | Content |
| --- | --- |
| `VectorCalculus` | `Space = ℝ³`, cross product, `divergence`, `curl`, the curl product rule, `IsForwardFieldLine`, complex vectors `CVec` |
| `LieGradient` | The Lie-derivative/gradient commutator |
| `InvariantBarrier` | Invariant level sets as all-time Grönwall barriers |
| `FieldLineExistence` | Global existence and uniqueness of solutions trapped in a compact set |
