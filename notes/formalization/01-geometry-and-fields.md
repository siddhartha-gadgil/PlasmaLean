# Geometry, magnetic fields, and coordinates

This chapter sets out the geometry of magnetic fields that the rest of the handbook uses: divergence-free fields and their potentials, pressure surfaces, flux coordinates, field-line dynamics and invariant tori, quasisymmetry and near-axis theory. The mathematical exposition is the specification. Each section ends with a **Status in PlasmaLean** paragraph saying what is compiled in Lean (declaration and module, default build or on demand), what is a supplied model or hypothesis, what is open (with its `Q-*` identifier in the [research graph](../implementation-plan.md#research-graph-added-29-october-2026)) and what was refuted or corrected. The summary is in [Status in PlasmaLean](#status-in-plasmalean). Status as of 30 October 2026, against the [stellarator contract](../implementation-plan.md#the-stellarator-contract-30-october-2026) and [progress report 15](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md).

"Default build" means the module is imported by `PlasmaLean.lean` and covered by `scripts/check_axioms.lean` (standard axioms only). "On demand" means a top module built and axiom-checked on the workstation under the policy of 25 October 2026.

## Contents

- [Role in the stellarator contract](#role-in-the-stellarator-contract)
- [Euclidean foundations](#euclidean-foundations)
- [Pressure surfaces and topology](#pressure-surfaces-and-topology)
- [Flux coordinates and Boozer charts](#flux-coordinates-and-boozer-charts)
- [Field-line dynamics](#field-line-dynamics)
- [Quasisymmetry and near-axis theory](#quasisymmetry-and-near-axis-theory)
- [Status in PlasmaLean](#status-in-plasmalean)
- [Theorem backlog](#theorem-backlog)

## Role in the stellarator contract

The project aims at a candidate that satisfies the contract clauses C1–C5 with common witnesses. This chapter supplies the geometric language of three of them.

- **C1, current-free rotational transform.** The net toroidal plasma current is zero or bootstrap-level, and ι ≥ ι_min > 0 on the confining surfaces comes from the external field. Vacuum fields (`J = 0`) are the limiting case, so the vacuum theory below (`VacuumField`, the maximum principle, the curvature obstruction) is C1 theory. An axisymmetric current-free field has ι = 0. Non-axisymmetry is therefore a *consequence* of C1, not a goal in itself.
- **C2, omnigeneity for thermal particles.** Quasisymmetry is one sufficient route to omnigeneity (quasi-isodynamic fields are another). The definitions of quasisymmetry here, and the bridge quasisymmetry ⇒ omnigeneity (Q-23), feed C2.
- **C4, existence.** Nested flux surfaces on the confining region: certified invariant tori (KAM) in the vacuum case, or flux functions of an exact equilibrium (see [chapter 02](02-plasma-models-and-equilibrium.md)).

C3 (stability) is [chapter 03](03-mhd-stability.md), C5 (thermal performance) is [chapter 04](04-particles-and-transport.md).

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

**Vacuum fields and the maximum principle.** In a current-free region `curl B = 0` and `div B = 0`, so each Cartesian component is harmonic and the Bochner identity gives

$$
\Delta|B|^2=2\sum_{i,j}(\partial_jB_i)^2\ \ge 0 .
$$

Hence `|B|²` is subharmonic: on a bounded region its maximum is attained on the boundary, and the difference of two vacuum fields is bounded in the volume by its values on the boundary surface. Subharmonicity forbids interior *maxima* of `|B|`, not minima. The obstruction to a minimum of `|B|` around a closed magnetic axis comes instead from the vacuum curvature identity `∇⊥|B| = |B| κ`: at a transverse minimum the field-line curvature vanishes, and a closed field line cannot have zero curvature everywhere.

**Status in PlasmaLean.**

- *Space and operators* (default build). Physical space is `Euclid3 := EuclideanSpace ℝ (Fin 3)` (Euclidean norm; definitionally `Fields.Space`). The algebraic kernel `Kernel/Equilibrium` uses `Vec3 := Fin 3 → ℝ`. Divergence and curl act on the actual Fréchet derivative (`Vacuum.fieldDiv`, `Vacuum.fieldCurl`). Units are SI throughout the kernel.
- *Pressure tangency* (kernel, default build). `field_tangency` and `current_tangency` in `Kernel/Equilibrium` prove `B · g = 0` and `J · g = 0` from the supplied law `ForceBalance B J g`. The audit sanity theorem `forceBalance_of_cross` shows the law has content only when `g` is identified with a real pressure gradient (see [chapter 02](02-plasma-models-and-equilibrium.md#static-equilibria-and-boundary-conditions)). `force_free_nonvacuum` (Sanity) separates force-free from vacuum.
- *Vacuum kernel* (default build). `VacuumField Ω B` in `Kernel/Vacuum` bundles: `Ω` open, `B` is `C²` on `Ω`, `div B = 0`, `curl B = 0`. It is a supplied law discharged per field, for example `RationalStellarator.field_vacuum` for the exact rational stellarator field.
- *Subharmonicity* (default build, `Theory/Fields/Subharmonic`). `laplacian_normSqField` (Bochner identity), `weak_maximum_principle`, `VacuumField.norm_le_of_frontier`, `VacuumField.error_le_of_frontier` (surface error controls volume error, the basis of coil-fit transfer) and `VacuumField.not_strict_local_max_norm`. The counterexample `hyperbolicField_strict_min` (`B = (x, y, −2z)`) has a strict interior minimum of `|B|`, which fixes the direction of the obstruction.
- *Curvature obstruction* (default build, `Theory/Fields/CurvatureObstruction`). `gradient_perp_norm_eq_curvature` (∇⊥|B| = |B|κ in vacuum) and `VacuumField.not_closed_fieldLine_minB`: no closed field line in a vacuum region along which every point is a minimum of `|B|`. Source: Helander 2014; note [toroidal-min-b-obstruction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/toroidal-min-b-obstruction.md).
- *Representations.* `clebsch_divergence_free` (`Theory/Fields/ClebschDivergence`): `∇ψ × ∇χ` is divergence-free for `C²` potentials. The flux 2-form is `magneticTwoForm` (`Theory/Fields/FluxSurfaceTwoForm`), and `magneticTwoForm_flux_surface` proves that it vanishes on the level sets of a flux function when `B · ∇ψ = 0` and `∇ψ ≠ 0`.
- *Open.* Closed but nonexact forms on multiply connected domains, global potentials, boundary regularity and a manifold-with-boundary API are not formalized.

## Pressure surfaces and topology

Let `Σ` be a connected, compact, boundaryless regular level surface of `p` in `ℝ³`. The gradient supplies an orientation. If `B` is nonzero everywhere on `Σ`, tangency yields a nowhere-vanishing tangent vector field. Poincaré–Hopf gives `χ(Σ)=0`; classification of compact orientable surfaces then gives genus one.

Do not omit the hypotheses. The argument fails at magnetic nulls, critical pressure levels, noncompact level sets, and surfaces with boundary. It proves the topology of each such component, not that every point belongs to one of a globally nested family.

To obtain a flux annulus, separately prove or supply a proper submersion

$$
\psi:\overline{\Omega}_{\rm ann}\longrightarrow[\psi_0,\psi_1],
$$

with compact connected torus fibres, no critical points, and compatible boundary fibres. Establish a product trivialization under an appropriate theorem. Handle the magnetic axis using a separate solid-torus/tubular-neighborhood construction. Avoid treating the radial label as a regular coordinate at the axis.

A Lean development can use a `FluxAnnulus` structure containing a concrete parametrization and proofs of injectivity, nondegenerate Jacobian, and field tangency, and later prove that suitable equilibria supply such a structure.

**Status in PlasmaLean.**

- *General theorem (G5): open.* Poincaré–Hopf and the classification of surfaces are not formalized, and no `FluxAnnulus` structure exists.
- *One explicit example* (default build, `Design/LandremanGradCounterexample`). For Landreman family 1, every level set `ψ = c`, `0 < c ≤ δ`, is homeomorphic to `Circle × Circle` through the explicit map `torusMap` (`fluxSurface_homeo_torus`), and `ψ = 0` is the axis circle (`axisSet_homeo_circle`). These are part of `family1_grad_counterexample`. The solid-torus topology of the plasma domain itself is not stated.
- *Invariant tori without a pressure function.* In the vacuum case the nested surfaces of C4 are certified KAM tori (see [Field-line dynamics](#field-line-dynamics)), not level sets of a pressure.

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

Here `I,G` are covariant coefficients with their associated SI factors; do not identify them with currents without proving the relevant Ampère integral and normalization. In vacuum `I = 0`; a nonzero `I(ψ)` is (up to normalization) the net toroidal current inside the surface, which is exactly the quantity C1 bounds.

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

**Periods and the conformal modulus.** On a flux torus the field-line form `β = ι_B σ` is closed, with periods given by the toroidal and poloidal flux derivatives, so `ι = Φ_p′/Φ_t′` is a ratio of periods. For a flat torus with conformal modulus `τ`, the Hodge decomposition (harmonic part plus exact part, with no cross term) gives the period inequalities

$$
\int_{T^2}|\beta|^2\,dA\ \ge\ \Phi_t'^2\,\frac{|\iota+\tau|^2}{\operatorname{Im}\tau},\qquad
\int_{T^2}|B^\flat|^2\,dA\ \ge\ \mu_0^2\,\frac{|G-\tau I|^2}{\operatorname{Im}\tau},
$$

with equality exactly for the harmonic (constant) form.

**Status in PlasmaLean.**

- *Boozer charts: supplied, not constructed.* No existence or regularity theorem for Boozer (or any straight-field-line) chart is formalized, and the reciprocal-basis identities (G2, G3) are not compiled. Boozer coordinates enter only through the vacuum Boozer guiding-centre model `BoozerField` (`Theory/Kinetic/BoozerGuidingCentre`, `I = 0`). The model audit (MA-L3) notes that `BoozerField` allows `G = 0` and `B ≤ 0`; every downstream theorem assumes `G ≠ 0` and `B ≥ B_min > 0`.
- *Flux-surface averages: a supplied class with proved instances.* `FluxGeometry.Laws` (`Theory/Transport/FluxGeometry`) records `V′ > 0` and the Gauss law `(V′g)′ = V′h`. It is proved, with coarea, for the Solov'ev geometry (`solovevFluxGeometry`, `solovev_one_plasma_actual_coarea`). For Landreman family 2, the fluxes, volume, current and Jacobian used by the Mercier certificate are derived from the field (`Design/LandremanFamily2Coarea`, inside `family2_mercier_stable_derived`).
- *Torus Hodge identity* (default build, `Theory/Geometry/TorusHodge`). `latticeMetric_tau`, `periodBound_eq`, `energy_ge`, `energy_eq_iff`, `fieldLine_energy_ge` and `currentForm_energy_ge`. **Scope:** a constant metric in the chosen angles. A non-constant induced metric needs uniformization (isothermal coordinates), which is not formalized. Note [flux-surface-holonomy](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/flux-surface-holonomy.md) (N-3).
- *Refuted.* The idea that the holonomy of the flat bundle on a flux surface encodes ι was refuted as not useful: it encodes the fluxes, with one gauge-ambiguous period. ι is the ratio of the periods of `β`. `magneticTwoForm_flux_surface` is the pointwise statement behind the "flat bundle" correction.

## Field-line dynamics

The ODE `ẋ=B(x)` preserves the volume measure when `div B=0`. A return map on a transverse section preserves the flux measure `B·n dS`, rather than automatically preserving ordinary area. Prove this through the flow and flux theorem.

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

**Status in PlasmaLean.**

- *Barriers* (default build, `Theory/Fields/InvariantBarrier`). `invariantBarrier_forever`: if `|DG · B| ≤ L|G|` on an open collar of the frontier of `Ω` and `G ≠ 0` inside, every two-sided field line starting in `Ω` stays in `Ω` for all time. The proof is a first-exit argument and needs neither uniqueness nor area preservation.
- *Existence of field lines* (default build, `Theory/Fields/FieldLineExistence`). `ODEGlobal.existsUnique_global`: global existence and uniqueness for a `C¹` field when a compact set is a priori invariant for local solutions. Together with `torus_trapping_Icc` this makes the confinement theorems non-vacuous.
- *Diophantine arithmetic* (default build, `Theory/KAM/Diophantine`). `goldenMean_diophantine`; `torusA_rotation_diophantine`: the rotational transform `ι = (75 + √5)/562` of torus A is `(γ, τ) = (0.1374, 1)`-Diophantine; `not_diophantine_of_rat`: a rational (for example dyadic) frequency is never Diophantine, so the KAM step uses the true `ι`, as the specification above requires.
- *A certified KAM torus, all-time confinement* (default build). For the exact rational vacuum stellarator field `RationalStellarator.field (1/4)` (`field_vacuum`, two field periods, stellarator-symmetric, not axisymmetric), an exact invariant torus with Diophantine rotation number (`torusA_exact`, `Design/KamTorusAExact`) gives `rationalStellarator_confined_forever_exists`: from every point inside the torus there is exactly one field line, defined for all time, and it stays inside. This is C1 + C4 in vacuum on the region inside **one** torus (ι ≈ 0.137).
- *Coil fields* (default build). `coil_stellarator_confined_concrete_N` (`Design/PolygonCoilCubicCover`): field-line confinement for 52 transits in the field of a concrete coil set, with field-line existence assumed. All-time coil confinement is blocked (Q-2): the on-demand `CoilKamCert` proves only a vacuous residual bound.
- *Open.* The flux-measure-preserving return map (G6) is not formalized. ι ≥ ι_min on a **nested family** of certified tori (the form C1 needs) is not stated in Lean. Parameter-robust KAM over useful sets (G10) is research.

## Quasisymmetry and near-axis theory

In a chosen Boozer chart, define field-strength quasisymmetry by

$$
|B|=b(\psi,M\theta-N\phi),\qquad M,N\in\mathbb Z,\quad \gcd(M,N)=1.
$$

For a Fourier mode `e^{i(mθ-nφ)}`, the symmetry condition is `Nm-Mn=0`. Prove the equivalence of this mode condition and the PDE `(N∂θ+M∂φ)|B|=0` with the relevant regularity. Define symmetry-breaking norms including radial and Fourier tails, not merely values on selected surfaces.

Do not identify this scalar condition with every geometric/Hamiltonian definition of quasisymmetry without a bridge theorem. [Burby–Kallinikos–MacKay](09-literature.md#geometry-equilibrium-and-symmetry) separates the guiding-centre symmetry questions from MHD force balance. A coordinate-free alternative is the *weak* quasisymmetry of Constantin–Drivas–Ginsberg: a nonvanishing divergence-free generator `ξ` with `B × ξ = −∇ψ` and `ξ · ∇|B| = 0`.

**Why quasisymmetry matters for the contract.** Quasisymmetry is wanted because it implies omnigeneity (C2): in an exactly quasisymmetric field the helical canonical momentum of a guiding centre is conserved, so trapped particles return to their flux surface after each bounce. The converse fails, since quasi-isodynamic fields are omnigenous without being quasisymmetric. Exact quasisymmetry in a volume, away from axisymmetry, is itself an open problem.

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

**Status in PlasmaLean.**

- *Weak quasisymmetry* (default build, `Theory/Fields/WeakQuasisymmetry`). `WeakQS B ξ ψ T` (the CDG definition, pointwise), the defect `qsDefect` with values in `ℝ≥0∞` and `qsDefect_eq_zero_iff`. Exact axisymmetry is a special case: `qsError_rotGen_eq_zero_of_axisymmetric`. The axis lemma `WeakQS.normB_const_of_gradient_eq_zero` says that `|B|` is constant along a field line on which `∇ψ = 0`. This is a different characterization from the Boozer–Fourier one, which (G7) is not formalized.
- *The Landreman barrier* (default build, `Design/LandremanNotQS`). Both Landreman families have non-constant `|B|` on the magnetic axis for every `ε ≠ 0`, so neither is weakly quasisymmetric with a generator that is nonvanishing on the axis (`family1_not_weakQS`, `family2_not_weakQS`). Generators vanishing on the axis are not excluded.
- *Scalar QS is not a PDE symmetry* (default build). `quasisymmetry_not_pde_symmetry` (`Sanity/QuasisymmetryNotSymmetry`): zero scalar QS error does not make the pressure force invariant. `lieBracket_gradient_of_contDiffAt` (`Theory/Fields/LieGradient`) is the supporting Lie-bracket identity.
- *Near-axis QA: a supplied model* (default build, `Design/NearAxisQA`). A second-order near-axis field strength fitted to the Landreman–Paul precise-QA configuration and inserted into the Boozer guiding-centre model: `nearAxis_epsQS` (`ε_QS(r) = 2|b₁|r²`, exact for the model), `preciseQA_epsQS`, `reactorQA_epsQS_edge`. It agrees with a real vacuum field only to the order of the expansion: the `O(r³)` remainder has no rigorous bound, and convergence of the series is open. The vacuum near-axis expansion is ill-posed without regularization (Ruth–Jorge–Bindel, arXiv:2411.04352), so the near-axis remainder route to Q-16 is not recommended.
- *Quasisymmetry ⇒ omnigeneity (Q-23, compiled in the Boozer model).* The mechanism is `helicalMomentum_conserved` and `boozerGC_trapped` (`Theory/Kinetic/BoozerGuidingCentre`). `Theory/Kinetic/Omnigeneity` (default build, standard axioms) states omnigeneity in the Boozer guiding-centre model (`OmnigenousOn`: zero net radial displacement per bounce), the exact bridge `omnigenousOn_of_exactQS` and the quantitative bound `approxOmnigenousOn_of_defect_le` (bounce-averaged drift linear in the QS defect, divided by `B_min ι_min`). All of it is inside the supplied Boozer model. Omnigeneity and ε_eff as contract predicates (Q-21) are specified in [00-model-contracts](00-model-contracts.md) but not yet in Lean.
- *Open.* Q-16: a quasisymmetric solution under the vacuum criterion (current-free field with certified tori, ι ≥ ι_min and a certified ε_QS small relative to ι). The recommended route is an explicit Dommaschk vacuum field fitted to a QA target. Q-24: existence of strongly quasisymmetric, non-symmetric fields in a volume, which is open mathematics and not on the design path. G8 (near-axis recursion with remainder bounds) is not started.

## Status in PlasmaLean

Summary of the sections above (30 October 2026). Every declaration named is in the default build unless marked.

| Topic | Compiled (declarations, module) | Supplied model or hypothesis | Open or corrected |
| --- | --- | --- | --- |
| Pressure tangency, force-free vs vacuum | `field_tangency`, `current_tangency` (`Kernel/Equilibrium`); `force_free_nonvacuum` | `ForceBalance` is a kernel law; `g` must be tied to ∇p (`Design/ForceBalanceGradient`) | none |
| Vacuum fields | `VacuumField` (`Kernel/Vacuum`); `laplacian_normSqField`, `weak_maximum_principle`, `VacuumField.error_le_of_frontier`, `VacuumField.not_strict_local_max_norm` (`Theory/Fields/Subharmonic`) | `VacuumField` discharged per field | Corrected: subharmonicity forbids maxima, not minima (`hyperbolicField_strict_min`) |
| Min-B around a closed axis | `gradient_perp_norm_eq_curvature`, `VacuumField.not_closed_fieldLine_minB` | none | none |
| Flux 2-form, Clebsch fields | `magneticTwoForm_flux_surface`, `clebsch_divergence_free` | none | Refuted: holonomy encodes ι |
| Torus Hodge | `periodBound_eq`, `energy_ge`, `energy_eq_iff`, `fieldLine_energy_ge`, `currentForm_energy_ge` (`Theory/Geometry/TorusHodge`) | constant metric in the angles | non-constant metrics (uniformization) |
| Torus topology of flux surfaces | `fluxSurface_homeo_torus`, `torusMap` (Landreman family 1 only) | none | general theorem G5 |
| Boozer charts, averages | `solovev_one_plasma_actual_coarea`; family-2 labels in `family2_mercier_stable_derived` | `BoozerField` (vacuum Boozer model), `FluxGeometry.Laws` | chart existence (G3) |
| KAM tori, field-line confinement | `torusA_exact`, `torusA_rotation_diophantine`, `rationalStellarator_confined_forever_exists`, `invariantBarrier_forever`, `ODEGlobal.existsUnique_global` | none (vacuum model field) | nested family with ι ≥ ι_min (C1); coil field all-time (Q-2) |
| Coil-field confinement | `coil_stellarator_confined_concrete_N` (52 transits) | field-line existence assumed | Q-2 |
| Weak quasisymmetry | `WeakQS`, `qsDefect`, `qsDefect_eq_zero_iff`, `WeakQS.normB_const_of_gradient_eq_zero`, `family1_not_weakQS`, `family2_not_weakQS` | none | Boozer–Fourier characterization (G7); Q-16; Q-24 |
| Near-axis QA | `nearAxis_epsQS`, `preciseQA_epsQS`, `reactorQA_epsQS_edge` | truncated near-axis field, Boozer GC model | remainder bounds (G8) |
| QS ⇒ omnigeneity (C2) | mechanism `helicalMomentum_conserved`, `boozerGC_trapped` | Boozer GC model | Q-23 compiled in the Boozer model (`omnigenousOn_of_exactQS`, `approxOmnigenousOn_of_defect_le`); ε_eff link and Q-21 definitions open |

**Against the contract.** C1: partial, vacuum only. The rational stellarator field is a vacuum field with one certified torus; ι ≥ ι_min on a nested family is not yet stated. C2: the geometric ingredients (weak QS, the defect, the omnigeneity bridge, compiled) exist only in the Boozer guiding-centre model, and nothing is certified for thermal particles on a candidate (Q-19, Q-21, Q-23). C4: satisfied in vacuum inside one certified torus.

## Theorem backlog

| ID | Target | Dependencies / useful scope |
| --- | --- | --- |
| G1 | Pressure tangency and uniform-field witness | Cross-product algebra; immediate kernel sanity |
| G2 | `div(curl A)=0` and reciprocal-basis identities | Concrete differentiability assumptions |
| G3 | Boozer Jacobian and average normalization | Supplied chart; no existence claim |
| G4 | Continuous Fourier surface regularity and clearance | Interval bounds; [05](05-verified-numerics.md) |
| G5 | Regular compact pressure component is a torus | Surface topology and Poincaré–Hopf; one explicit example compiled (Landreman family 1) |
| G6 | Field-line flow/return map preserves flux measure | ODE uniqueness and integration |
| G7 | Quasisymmetry Fourier characterization | Fourier convergence and circle actions; weak QS (CDG) compiled instead; feeds C2 through Q-23 |
| G8 | Near-axis recursion with remainder bounds | Analytic sequence spaces; vacuum expansion ill-posed without regularization |
| G9 | One certified invariant torus and barrier | A posteriori KAM, embedding and separation |
| G10 | Quantitative perturbation theory over useful parameter sets | Research target; preserve resonance restrictions; C1 needs a nested family with ι ≥ ι_min |
