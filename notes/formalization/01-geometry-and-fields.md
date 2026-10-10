# Geometry, magnetic fields, and coordinates

This is a formalization specification. The elementary deductions below are derived explicitly; the analytic/topological results are targets whose source hypotheses must be extracted before use.

## Contents

- [Euclidean foundations](#euclidean-foundations)
- [Pressure surfaces and topology](#pressure-surfaces-and-topology)
- [Flux coordinates and Boozer charts](#flux-coordinates-and-boozer-charts)
- [Field-line dynamics](#field-line-dynamics)
- [Quasisymmetry and near-axis theory](#quasisymmetry-and-near-axis-theory)
- [Theorem backlog](#theorem-backlog)

## Euclidean foundations

Start with bounded open `Ω ⊂ ℝ³` and explicitly stated boundary regularity, rather than requiring an entire manifold-with-boundary API immediately. Use `E = EuclideanSpace ℝ (Fin 3)` or the pinned Mathlib equivalent. Define smooth vector fields, weak fields when needed, `grad`, `div`, `curl`, and surface normals through reusable interfaces with concrete implementations.

Require an orientation and specify SI units. Model scalar fields with their dimensions and prove nondimensionalization identities, even if the first implementation uses ordinary real-valued functions with documented units.

Two useful divergence-free representations:

1. `B = curl A` locally or globally where an appropriate potential exists.
2. A flux 2-form `β = ι_B vol` with `dβ = 0`.

Prove the relation between these and `div B = 0` under the required smoothness. Keep nonexact closed forms and circulation/flux periods in multiply connected domains. A global vector/scalar potential has additional topological and boundary obligations.

For static isotropic MHD with `μ₀ > 0`:

$$
\nabla\cdot B=0,\qquad \nabla\times B=\mu_0J,\qquad J\times B=\nabla p.
$$

Dotting force balance with `B` and `J` gives

$$
B\cdot\nabla p=0,\qquad J\cdot\nabla p=0.
$$

This is an algebraic cross-product identity, independent of a foliation theorem.

## Pressure surfaces and topology

Let `Σ` be a connected, compact, boundaryless regular level surface of `p` in `ℝ³`. The gradient supplies an orientation. If `B` is nonzero everywhere on `Σ`, tangency yields a nowhere-vanishing tangent vector field. Poincaré–Hopf gives `χ(Σ)=0`; classification of compact orientable surfaces then gives genus one.

Do not omit the hypotheses. The argument fails at magnetic nulls, critical pressure levels, noncompact level sets, and surfaces with boundary. It proves the topology of each such component, not that every point belongs to one of a globally nested family.

To obtain a flux annulus, separately prove or supply a proper submersion

$$
\psi:\overline{\Omega}_{\rm ann}\longrightarrow[\psi_0,\psi_1],
$$

with compact connected torus fibres, no critical points, and compatible boundary fibres. Establish a product trivialization under an appropriate theorem. Handle the magnetic axis using a separate solid-torus/tubular-neighborhood construction. Avoid treating the radial label as a regular coordinate at the axis.

An early Lean development can use a `FluxAnnulus` structure containing a concrete parametrization and proofs of injectivity, nondegenerate Jacobian, and field tangency. Later prove that suitable equilibria supply such a structure.

## Flux coordinates and Boozer charts

Use `(ψ,θ,φ) ∈ (ψ₀,ψ₁) × 𝕋²`, with angles modulo `2π`. Define `ψ` as toroidal flux divided by `2π`. Let `x(ψ,θ,φ)` be an oriented regular embedding and

$$
\mathcal J=\partial_\psi x\cdot(\partial_\theta x\times\partial_\phi x)>0.
$$

A selected Boozer representation is

$$
B=\nabla\psi\times\nabla\theta
+\iota(\psi)\nabla\phi\times\nabla\psi
=K\nabla\psi+I(\psi)\nabla\theta+G(\psi)\nabla\phi.
$$

Here `I,G` are covariant coefficients with their associated SI factors; do not identify them with currents without proving the relevant Ampère integral and normalization.

Reciprocal-basis identities give

$$
B\cdot\nabla\phi=\mathcal J^{-1},\qquad
B\cdot\nabla\theta=\iota\,\mathcal J^{-1},\qquad
\mathcal J=\frac{G+\iota I}{|B|^2}.
$$

These algebraic identities require `|B|>0` and a valid chart. The difficult result is the chart's existence/regularity with the prescribed representations. Separate that result from checking the identities in a supplied chart. [Boozer 1981](09-literature.md#geometry-equilibrium-and-symmetry) is a source for conventions and rational-surface issues.

For any scalar `h`,

$$
V'(\psi)=\int_{\mathbb T^2}\mathcal J\,d\theta\,d\phi,\qquad
\langle h\rangle_\psi=\frac{1}{V'(\psi)}
\int_{\mathbb T^2}h\mathcal J\,d\theta\,d\phi.
$$

Prove `V' > 0`, `⟨1⟩=1`, positivity, and coordinate-change invariance under the specified measure convention.

## Field-line dynamics

The ODE `ẋ=B(x)` preserves the volume measure when `div B=0`. A return map on a transverse section preserves the flux measure `B·n dS`, rather than automatically preserving ordinary area. Prove this through the flow and flux theorem.

On an annulus where `B·∇φ` is nonzero, use `φ` as the time variable. Straight-field-line coordinates yield `dθ/dφ = ι(ψ)`. For nonintegrable fields, formulate a return map and its symplectic/area-preserving property.

An embedded invariant torus separating a region is a field-line barrier if the ODE is unique and tangent to it. This is not a barrier for all finite-gyroradius particle orbits.

For quantitative KAM work, record:

- a specified exact symplectic map or divergence-free flow;
- analytic strips or finite differentiability and their norm bounds;
- an invariant-torus approximation and its residual;
- twist/nondegeneracy conditions;
- a frequency satisfying an infinite Diophantine inequality;
- constants of a particular a posteriori theorem.

For a scalar rotation number `α`, use specified `γ>0` and `τ≥1`. One convention is `|qα-p| ≥ γ/|q|^τ` for all integers `p` and nonzero `q`. A finite resonance scan does not prove it. Rational decimal frequencies fail it. Quadratic irrational frequencies offer a tractable arithmetic lemma; the validated torus theorem must actually enforce that frequency.

Diophantine properties with a fixed constant are not robust over an arbitrary open frequency interval, because rationals are dense. A parameter-dependent KAM result must retain its nonresonant/Cantor restrictions or adjust parameters to preserve the selected frequency. See [Haro et al.](09-literature.md#validated-computation-and-analysis).

## Quasisymmetry and near-axis theory

In a chosen Boozer chart, define field-strength quasisymmetry by

$$
|B|=b(\psi,M\theta-N\phi),\qquad M,N\in\mathbb Z,\quad \gcd(M,N)=1.
$$

For a Fourier mode `e^{i(mθ-nφ)}`, the symmetry condition is `Nm-Mn=0`. Prove the equivalence of this mode condition and the PDE `(N∂θ+M∂φ)|B|=0` with the relevant regularity. Define symmetry-breaking norms including radial and Fourier tails, not merely values on selected surfaces.

Do not identify this scalar condition with every geometric/Hamiltonian definition of quasisymmetry without a bridge theorem. [Burby–Kallinikos–MacKay](09-literature.md#geometry-equilibrium-and-symmetry) separates the guiding-centre symmetry questions from MHD force balance.

For a magnetic axis `r₀(s)` use a smooth material/Bishop frame when curvature may vanish. The Frenet frame requires `κ>0`. Represent general near-axis surfaces by

$$
x=r_0+X(r,\theta,s)n_1(s)+Y(r,\theta,s)n_2(s)+Z(r,\theta,s)t(s),
$$

with Taylor–Fourier expansions and the source's chosen radial scaling. A circular normal tube is a geometric example, not the general Garren–Boozer construction.

Formal series agreement through order `k` is a useful algebraic result. A finite-radius design additionally needs

$$
\|F(x^{[k]})\|\le C r^{k+1}
$$

in a declared norm and a theorem producing an exact nearby solution or a controlled model error. Do not infer convergence of the infinite series from coefficient recursion. Extract the actual compatibility restrictions from [Garren–Boozer and Landreman–Sengupta](09-literature.md#geometry-equilibrium-and-symmetry).

## Theorem backlog

| ID | Target | Dependencies / useful scope |
| --- | --- | --- |
| G1 | Pressure tangency and uniform-field witness | Cross-product algebra; immediate kernel sanity |
| G2 | `div(curl A)=0` and reciprocal-basis identities | Concrete differentiability assumptions |
| G3 | Boozer Jacobian and average normalization | Supplied chart; no existence claim |
| G4 | Continuous Fourier surface regularity and clearance | Interval bounds; [05](05-verified-numerics.md) |
| G5 | Regular compact pressure component is a torus | Surface topology and Poincaré–Hopf |
| G6 | Field-line flow/return map preserves flux measure | ODE uniqueness and integration |
| G7 | Quasisymmetry Fourier characterization | Fourier convergence and circle actions |
| G8 | Near-axis recursion with remainder bounds | Analytic sequence spaces |
| G9 | One certified invariant torus and barrier | A posteriori KAM, embedding and separation |
| G10 | Quantitative perturbation theory over useful parameter sets | Research target; preserve resonance restrictions |
