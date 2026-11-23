# The form kernel after TauCeti v4.36.0, and its use for the complex-geometry notes

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-48` |
| Title | Which claims of the complex-geometry notes (N-42, N-43, N-44) can use the differential-form kernel, what TauCeti v4.36.0 adds to it, and a bridge to forms on manifolds |
| Kind | method (for N-45), with an assessment of N-42–N-44 and of TauCeti's symplectic files |
| Addresses | `G-11`; supports `Q-29` (step 1 of N-43), `Q-24`, `Q-16` |
| Depends on | N-45 (`Kernel/Forms`, `Theory/Fields/FormBridges`); N-42, N-43, N-44; TauCeti `v4.36.0` |
| Dependency requirement | the form kernel as compiled; from TauCeti: Cartan's formula (`lieDerivForm_eq_curryLeft_extDeriv_add`), the Poincaré lemma (`StarConvex.exists_contDiffOn_forall_extDeriv_eq`), forms on open subsets of a normed space (`isSmoothForm_opens_iff`, `mextDeriv_opens_eq_extDeriv`), exactness on simply connected manifolds (`exists_mextDeriv_eq_of_simplyConnectedSpace`), the wedge product and the linear contact criterion (`pairedWedge_wedgePow_ne_zero_iff`) |
| Produces | `Theory/Fields/FormCalculus`, `Theory/Fields/FormTopology`, `Theory/Fields/FormContact` and their `Sanity` modules; the fit table; the symplectic assessment |
| Difficulty | routine to moderate for what is done; hard for periods and surface geometry |
| Status | verified for the theorems listed under "What is compiled"; the rest stated |
| Lean evidence | default build, namespace `PlasmaLean.Forms` unless noted: `lieDerivForm_eq_zero_of_interior`, `FormWeakQS.lieDerivForm_eq_zero`, `PlasmaLean.Fields.WeakQS.lieDerivForm_flux_eq_zero`, `VacuumForm.exists_scalarPotential`, `VacuumForm.exists_vectorPotential`, `onOpens`, `isSmoothForm_onOpens_iff`, `mextDeriv_onOpens`, `VacuumForm.exists_scalarPotential_of_simplyConnected`, `not_simplyConnected_of_no_potential`, `wedge12_eq_wedge`, `isContactAt_iff_nondegenerate`, `IsBeltramiOn.reeb`; `PlasmaLean.Sanity.FormTopology.wireField_no_potential`, `wireRegion_not_simplyConnected`, `bentSet_not_starConvex`, `hyperbolic_scalarPotential_bent`; `lieDerivForm_flux`, `PlasmaLean.Fields.WeakQS.lieBracket_eq_zero`, `IsBeltramiOn.reeb_unique`, `pathIntegral_onOpens_flat`, `periodHom_onOpens_flat`, `PlasmaLean.Sanity.FormPeriods.wire_period`; `PlasmaLean.Kinetic.lorentzOrbit_eulerLagrange`, `noetherMomentum_translation_conserved`, `noetherMomentum_linear_gauge_conserved`, `canonicalMomentum_rotGenZ_conserved`; `loopCurrent_eq_periodHom_div`, `PlasmaLean.Vacuum.VacuumField.loopCurrent_eq_zero_of_simplyConnected`; `flatSmoothForm`, `isContactForm_flatSmoothForm_iff`, `IsBeltramiOn.reebVectorField_flatSmoothForm`; `PlasmaLean.Kinetic.canonicalForm_fderiv_kineticMomentumMap_flux`, `lorentzOrbit_hamilton`; `hymLift`, `extDeriv_hymLift_eq_zero_iff`, `hymLift_closed_iff_vacuumField`, `hymLift_isAntiSelfDual` |
| Audit evidence | not audited |
| Last updated | 23 November 2026: created; same day, the manifold bridge, the wedge and contact links, the wire fixture and the symplectic assessment; then periods, `[ξ, B] = 0`, uniqueness of the Reeb vector, a non-star-convex fixture and the Noether charge from TauCeti; phases 1 and 2 of the remaining tasks (rotational Noether, loop current as a period, bundled contact form; magnetic symplectic form, anti-self-dual lift); second round, phase 1 (finite symmetry and the direct proofs, periods on an interval, contact forms on an open subset) and phase 2 (Hamilton's equations with an electric field and the converse; Hodge star on `ℝ³ × ℝ` and the circle quotient); third round, phase 1 (piecewise `C¹` loops, convex regions and the contract's current clause, gauge terms) and phase 2 (the lift on `Ω × S¹`; crossed-field orbits, existence and uniqueness) |
| Patches | none (N-45 stands; this note adds to it) |

## Purpose and scope

Questions from the user (23 November 2026):

1. Can the new complex-geometry notes (N-42 with its method notes N-43, N-44) use the
   differential-form kernel of N-45?
2. What should change in the project's use of differential geometry and topology now that the
   dependency is TauCeti `v4.36.0`? In particular: a bridge for the topological statements, and
   an assessment of the symplectic geometry files.

Before this note the project imported nothing from TauCeti: the form kernel used only Mathlib's
`extDeriv`. This note records the first uses.

Setting, as in N-45: forms on `ℝ³ = Euclid3` with the Euclidean metric, `Form k` the space of
alternating `k`-linear maps, a differential form a function `Euclid3 → Form k`.

## What TauCeti v4.36.0 adds

File counts are from `git ls-tree` on the two tags.

| Area (TauCeti path) | v4.35.0 → v4.36.0 | Carrier | Use here |
| --- | --- | --- | --- |
| `Analysis/Calculus/DifferentialForm` | 5 → 29 files | forms on a normed space (the kernel's carrier) | **used**: `LieDeriv`, `Poincare` |
| `Analysis/Normed/Module/Alternating/Wedge` | present in both | alternating maps | **used**: `wedge12_eq_wedge` |
| `Geometry/Manifold/DifferentialForm` | 14 → 120 | `RoughForm`, `SmoothForm` on a manifold | **used**: `Opens/ModelSpace` is the bridge |
| `Geometry/Manifold/DeRham` | 0 → 36 | forms on a manifold | **used**: `SimplyConnected`; periods and the torus not yet |
| `Geometry/Contact` | 0 → 36 | `SmoothForm` on a manifold | **used**: the linear criterion of `Volume`; bundled contact forms not yet |
| `Geometry/Manifold/Riemannian` | 129 → 361 | Riemannian manifolds | not used; `Curl`, `HodgeStar`, `Codifferential`, `Killing` are new |
| `Geometry/Manifold/Complex` | 6 → 86 | complex manifolds | not used; `Isothermal` (isothermal charts) bears on the barrier of N-3 |
| `Geometry/Symplectic` | 64 → 650 | mostly symplectic manifolds | not used; assessed below |

The files under `Analysis/Calculus/DifferentialForm` work with functions
`E → E [⋀^Fin k]→L[ℝ] F`, which is exactly `Euclid3 → Form k`. They apply to the kernel with no
translation. The files under `Geometry/` work with forms on a manifold.

## The bridge to forms on manifolds

An open subset `U` of `ℝ³` is a manifold. In TauCeti a rough form on it is, by definition, a
field of alternating maps `U → Form k`. So the bridge is restriction
(`Theory/Fields/FormTopology`):

- `onOpens U β`: the manifold form on `U` with the values of `β : Space → Form k`.
- `isSmoothForm_onOpens_iff`: it is `C^n` on the manifold exactly when `β` is `C^n` on `U`.
- `mextDeriv_onOpens`: its manifold exterior derivative at `x ∈ U` is `extDeriv β x`, with no
  differentiability hypothesis.
- `mextDeriv_onOpens_eq_zero_iff`: closed on the manifold iff closed at every point of `U`.

The two comparison theorems are TauCeti's; the bridge adds only the definition and the
restatements. It carries forms of finite regularity (`C²` is what `VacuumForm` gives). TauCeti's
de Rham cohomology groups use smooth (`C^∞`) forms, so statements about cohomology classes need
smooth fields; statements about a single closed form, such as exactness, do not.

**Topological statements obtained through it.**

- `VacuumForm.exists_scalarPotential_of_simplyConnected`,
  `VacuumField.exists_scalarPotential_of_simplyConnected`: on a simply connected open region a
  vacuum field is the gradient of a `C²` function. This replaces star-convexity by the
  topological hypothesis.
- `not_simplyConnected_of_no_potential`: a vacuum field on `U` that is not a gradient shows that
  `U` is not simply connected.
- `wireField_no_potential` (`Sanity/FormTopology`): the field of a straight wire,
  `e_z × x/(x² + y²)`, is a vacuum field on the complement of its axis and is not a gradient
  there. The proof is elementary: a potential would increase strictly around the unit circle,
  which is a closed field line.
- `wireRegion_not_simplyConnected`: hence the complement of a line in `ℝ³` is not simply
  connected. This is a topological theorem proved from a magnetic field.

**Periods** (`Theory/Fields/FormPeriods`).

- `pathIntegral_onOpens_flat`: TauCeti's line integral of `B♭` along a curve in `U` equals the
  contract layer's circulation `Contract.lineIntegral B γ a b`. No hypothesis.
- `periodHom_onOpens_flat`: for a `C¹` curl-free field on `U` and a `C¹` loop, TauCeti's period
  homomorphism on the class of the loop is the circulation. So the Ampère current through a loop
  is `μ₀⁻¹` times a de Rham period and depends only on the homotopy class of the loop in `U`.
- `wire_circulation`, `wire_period`, `wire_periodHom_ne_zero` (`Sanity/FormPeriods`): the wire
  field has circulation and period `2π` on the unit circle; a uniform field has circulation `0`
  on the same loop (`uniform_circulation`).

**A simply connected region that is not star-convex** (`Sanity/FormTopology`): the region below
the sheet `z = x²` is homeomorphic to a half-space, hence simply connected, and is not
star-convex about any point (`bentSet_not_starConvex`). The hyperbolic vacuum field has a
potential on it by the simply connected theorem (`hyperbolic_scalarPotential_bent`).

**Not reached.** The de Rham
classes of a torus (`DeRham/Torus`) live on the abstract torus `∏ AddCircle`, not on an embedded
flux surface.

## Fit of the complex-geometry notes to the kernel

| Claim | Statement in form language | Fit |
| --- | --- | --- |
| N-43 step 1: weak QS gives `[B, u] = 0` | `L_u ω_B = 0`, from Cartan's formula | **done** (`WeakQS.lieDerivForm_flux_eq_zero`, `WeakQS.lieBracket_eq_zero`) |
| N-43: `div u = 0`, `B × u = ∇ψ`, `u·∇\|B\| = 0` | `d(ι_u vol) = 0`, `ι_u ω_B = dψ`, `d\|B\|(u) = 0` | this is `FormWeakQS` with `ξ = −u` |
| N-43 steps 2–5 (homological equation, certificate, hot core) | linear algebra in velocity space, orbit estimates | no: not statements about forms on `ℝ³` |
| N-42 S-2: the class `G dϑ + dF` | `B♭` closed; `dF` the exact part | **done** for the two extremes: no `G dϑ` term on a simply connected region; the wire field is a pure `G dϑ` term with no potential |
| N-42 S-3–S-6: harmonic polynomial families | `B♭ = dF`, `ΔF = 0` | available in vector language (`VacuumField`); the form version is one transport |
| N-42 S-13: Hermitian–Yang–Mills lift | `ℱ = ω_B − ⋆ω_B ∧ dτ` is closed on `Ω × ℝ` iff `dω_B = 0` and `d⋆ω_B = 0` | **done** (`extDeriv_hymLift_eq_zero_iff`, `hymLift_closed_iff_vacuumField`, `isAntiSelfDual_iff_liftStar`, `hymLiftRegionForm_closed_iff_vacuumField` on `U × S¹`, `integral_liftInner_hymLiftCircle`); the bundle and Yang–Mills minimality are not |
| N-42 S-32: constant `\|B\|` vacuum field is constant | Bochner identity | no gain: `laplacian_normSqField` is a vector-language theorem |
| N-42 S-14: subharmonic log-determinant | uses `∇B` as a symmetric matrix | no |
| N-42 S-15: no constant `\|B\|` on `∂Ω` | needs integration over `∂Ω` | no: no boundary integration for these forms |
| N-44: cylinder vacuum gap `B_e e_z + B_θ(a/r)e_θ` | closed, co-closed 1-form `B_e dz + B_θ a dϑ` | the `dϑ` part is the wire fixture above; the full gap field is not written |
| N-44: mode coefficient, window, gap | Bessel and algebraic inequalities | no |
| N-44, Q-31: `II(Y, g⁻¹d)` on an interface torus | second fundamental form of a surface | no: needs surface geometry (TauCeti `Riemannian/Induced`); not assessed further |
| N-42 S-7–S-10: KAM tori, torsion | invariant tori | no |

**Sign convention.** N-43 writes `B × u = ∇ψ`; `WeakQS` has `B × ξ = −∇ψ`. In forms these are
`ι_u ω_B = dψ` and `ι_ξ ω_B = −dψ` (`formWeakQS_flux_iff`), so `u = −ξ`.

**Summary.** The kernel fits the hypotheses of N-43 and the vacuum-family part of N-42. It does
not fit the stability benchmark of N-44 or the kinetic estimates, which are not statements in
exterior calculus.

## What is compiled

All in the default build, standard axioms only (`scripts/check_axioms.lean`, 134 entry points).

**Lie derivative** (`Theory/Fields/FormCalculus`).

- `extDeriv_formGrad_eq_zero`: `d(dψ) = 0` where `ψ` is `C²`.
- `lieDerivForm_eq_zero_of_interior`: if `ω` is differentiable and closed at `x`, `ξ` is
  differentiable at `x`, and `ι_ξ ω = −dψ` near `x` with `ψ` of class `C²` at `x`, then
  `L_ξ ω = 0` at `x`.
- `FormWeakQS.lieDerivForm_eq_zero`: the same on an open set `T`. Extra hypotheses beyond
  `FormWeakQS`: `T` open, `ω` differentiable and closed on `T`, `ψ` of class `C²` on `T`.
- `WeakQS.lieDerivForm_flux_eq_zero`: the vector-language version, with `∇ · B = 0` on `T`.

- `lieDerivForm_flux`: `L_ξ(ι_B vol) = ι_{[ξ,B] + (div ξ)B} vol` at every point, with no
  differentiability hypothesis.
- `WeakQS.lieBracket_eq_zero`: hence `[ξ, B] = 0` on `T` (same hypotheses as the previous
  item). This is step 1 of N-43 in vector language.

**Potentials on star-convex regions** (same file). `VacuumForm.exists_vectorPotential`
(`dA = ω`), `VacuumForm.exists_scalarPotential` (`dφ = ⋆ω`), and the `VacuumField` versions
(`B = ∇ × A`, `B = ∇φ`), with the potential `C²` and zero at the centre.

**Bridge and topology** (`Theory/Fields/FormTopology`): listed in the section above.

**Wedge and contact** (`Theory/Fields/FormContact`).

- `wedge12_eq_wedge`: the product `wedge12` of N-45 is TauCeti's
  `ContinuousAlternatingMap.wedge` of a 1-form and a 2-form.
- `isContactAt_iff_wedge`, `isContactAt_iff_nondegenerate`: `IsContactAt β x` holds iff
  `β x ≠ 0` and `dβ x` is nondegenerate on the plane `ker β x`. This is the intrinsic condition
  TauCeti uses for contact forms (`Module.Dual.IsContact`), obtained from its linear volume
  criterion in dimension three.
- `IsBeltramiOn.reeb`: for a Beltrami field with `B x ≠ 0`, the vector `R = B/‖B‖²` satisfies
  the Reeb equations `β(R) = 1`, `ι_R dβ = 0` for `β = B♭`. No hypothesis on `λ`; when `λ ≠ 0`
  the form is contact (`isContactAt_of_beltrami`).
- `IsBeltramiOn.reeb_unique`: for `λ(x) ≠ 0` and `B x ≠ 0` the Reeb equations have the single
  solution `B/‖B‖²`.

**Noether charge** (`Theory/Kinetic/NoetherLagrangian`), from TauCeti's
`noetherCharge_eq_of_eulerLagrange`.

- `lorentzLagrangian`: `L(x, v) = (m/2)‖v‖² + q⟪A(x), v⟫`.
- `lorentzOrbit_eulerLagrange`: a `LorentzOrbit` with `E = 0` solves the Euler–Lagrange equation
  of `L` when `B = ∇ × A` everywhere and `A` is differentiable.
- `noetherMomentum_translation_conserved`: if moreover `A` is invariant under translation along
  `e`, then `noetherMomentum m q (fun _ => e) (fun y => ⟪A y, e⟫)` is constant along the orbit.
  Translation symmetries only.
- `Sanity/NoetherLagrangian`: the Landau gauge `A = B₀ x e_y` has curl `B₀ e_z`
  (`curl_landau`); `m v_y + q B₀ x` is conserved along every Lorentz orbit in the uniform field
  (`landau_momentum_conserved`); the gauge is not invariant along `e_x`
  (`landau_not_invariant_x`).

**Sanity.**

- `Sanity/FormCalculus`: accepted `lieDerivForm_uniform`, `hyperbolic_scalarPotential`,
  `hyperbolic_vectorPotential`; rejected `lieDerivForm_dilation_ne_zero` (`L_ξ ω = 2ω` for the
  dilation field); hypothesis check `dilation_not_hamiltonian`.
- `Sanity/FormTopology`: the wire fixture and `wireRegion_not_simplyConnected`; bridge checks
  `wire_closed_onOpens`, `wire_isSmoothForm_onOpens`.
- `Sanity/FormContact`: accepted `helical_wedge_ne_zero`, `helical_nondegenerate`,
  `helical_reeb`; rejected `const_not_nondegenerate`, `const_wedge_eq_zero`.
- `Sanity/FormPeriods` and `Sanity/NoetherLagrangian`: listed above.

## Assessment of TauCeti's symplectic geometry files

`Geometry/Symplectic` grew from 64 to 650 files. Module documentation was read for the files
named below; proofs were not reviewed and nothing was compiled against them. Largest parts:
`Floer` (0 → 171), `Hamiltonian` (0 → 131), `Manifold` (4 → 79), `JHolomorphic` (25 → 69),
`Cotangent` (8 → 57), `Lagrangian` (3 → 34), `Liouville` (1 → 19).

| TauCeti file or directory | Content | Carrier | Bearing on PlasmaLean |
| --- | --- | --- | --- |
| `Hamiltonian/Noether` | Noether's theorem for a Lagrangian `L t (q, v)` with a gauge term: the charge `∂_v L(ξ) − B` is conserved | normed space | **direct**: the canonical momentum `m⟪K, v⟫ + qψ` of `Kinetic/Noether` is the Noether charge of `L = m\|v\|²/2 + q A·v`, with the gauge term coming from `L_K A`. Lean-ready, needs a vector potential (now available on star-convex regions) |
| `Cotangent/Fiberwise` | magnetic translation `(q, p) ↦ (q, p − σ_q)` carries the magnetic form `ω + π^*dσ` to the canonical one | linear cotangent space `V × V*` | **direct**: the symplectic form of a charged particle in `B = dA` (`Kinetic/FullOrbit`). Lean-ready |
| `Hamiltonian/Integrable`, `Involutive`, `LiouvilleArnold` | completely integrable systems; Liouville tori are Lagrangian embeddings of `ℝⁿ/Λ` | symplectic manifold | guiding-centre motion with exact quasisymmetry is integrable (N-29); needs the phase space as a manifold. Research |
| `Hamiltonian/CommutingFlow` | flows of fields with closed `ι_X σ` preserve `σ` (Cartan) | manifold | the manifold version of `lieDerivForm_eq_zero_of_interior`; integrates `L_ξ ω_B = 0` to invariance under the flow |
| `Hamiltonian/TimeDependent`, `ExtendedPhaseSpace` | time-dependent Hamiltonian flows | symplectic vector space | field lines as a 1½-degree-of-freedom system with the toroidal angle as time (Rosetta entry "field lines as a Hamiltonian system"). Lean-ready in principle |
| `Flux`, `Flux/Torus` | the flux class of a diffeotopy in `H¹` | manifold | zero flux is the exactness condition on a return map that KAM and intersection arguments need. Research |
| `Annulus` (twist bands, generating functions), `Hamiltonian/RadialTwist` | twist maps of an annulus or the plane | plane | related to return maps on a cross-section; not read in detail |
| `Hamiltonian/Stability` | Lagrange–Dirichlet: a strict minimum of the energy is Lyapunov stable | symplectic vector space | finite-dimensional analogue of an energy principle; no direct use for the continuum `δW` |
| `Hamiltonian/Reeb`, `Liouville/Reeb`, `Contact/StableHamiltonian` | Reeb dynamics; stable Hamiltonian structures | manifold | the pair `(B♭, ω_B)` of a steady field; needs bundled forms |
| `Floer`, `JHolomorphic`, `Capacity`, most of `Lagrangian` | Floer theory, pseudoholomorphic curves | manifold | none foreseen |

A text search of `Geometry/Symplectic` and `Dynamics` for "KAM", "Kolmogorov" and "Diophantine"
found no KAM theorem. The project's own KAM modules are not replaced by anything in TauCeti.

**Verdict.** Two files apply directly to compiled PlasmaLean theory and use carriers the project
already has (normed spaces): `Hamiltonian/Noether` and `Cotangent/Fiberwise`. Everything else
needs phase spaces as manifolds, which the project does not have. Both are now used
(`NoetherLagrangian`, `NoetherRotation`, `MagneticSymplectic`).

## Phase 1 of the remaining tasks (sub-agents, 23 November 2026)

Three modules were written by sub-agents in parallel, each with a sanity module, and then
rebuilt and axiom-checked in the main session (default build, standard axioms).

**Rotational symmetry and gauge terms** (`Theory/Kinetic/NoetherRotation`).

- `noetherMomentum_linear_gauge_conserved`: for a skew linear generator `K`, `B = ∇ × A`, and
  `DA(y)(K y) = K(A y) + ∇χ(y)`, every Lorentz orbit conserves
  `m⟪K x, v⟫ + q(⟪A x, K x⟫ − χ(x))`. Proved through TauCeti's Noether theorem with gauge term
  `qχ`. `noetherMomentum_linear_conserved` is the case `χ = 0`.
- `rotGenZ` (rotation about the z-axis), `noetherMomentum_rotGenZ` (the Noether momentum is the
  existing `canonicalMomentum`), `canonicalMomentum_rotGenZ_conserved` and its gauge version.
- `Sanity/NoetherRotation`: the symmetric gauge `(B₀/2)(−y, x, 0)` gives
  `m(x v_y − y v_x) + qB₀(x² + y²)/2` (`symGauge_angular_momentum_conserved`); the Landau gauge
  is not equivariant (`landau_not_equivariant`) but gives the same conserved quantity with the
  gauge term `χ = B₀(x² − y²)/2` (`landau_angular_momentum_conserved`).
- Not done: the equivariance hypothesis is infinitesimal only; the hypotheses of the direct
  proof `canonicalMomentum_conserved` (`AxisymmetricFlux`) are not derived from it.

**The contract's loop current as a period** (`Theory/Fields/FormLoopCurrent`).

- `lineIntegral_comp_affine`: affine reparametrisation of `Contract.lineIntegral`, with no
  hypothesis.
- `poloidalCirculation_eq_periodHom`, `loopCurrent_eq_periodHom_div`: for a `C¹` curl-free field
  on an open `U` and a `C¹` closed poloidal loop in `U`, the contract's circulation is TauCeti's
  period on the class of the loop, and the loop current is that period divided by `μ₀`.
  The loop must lie in `U` and be `C¹` for every real `θ`, not only on `[−π, π]`.
- `VacuumField.poloidalCirculation_eq_zero_of_simplyConnected`,
  `VacuumField.loopCurrent_eq_zero_of_simplyConnected`: a vacuum field on a simply connected
  region has zero net current through every such loop. Proved from the potential, not from
  triviality of the fundamental group.
- `Sanity/FormLoopCurrent`: the wire circulation over `[0, 2π]` and `[−π, π]` is `2π`;
  accepted: the hyperbolic field has zero loop current and zero period on a torus section in
  the bent region. There is no rejected case with a poloidal loop (the wire's circle is not
  one).

**TauCeti's bundled contact forms** (`Theory/Fields/FormContactManifold`).

- `flatSmoothForm B hB`: the smooth 1-form `B♭` on the manifold `ℝ³`, for `B` of class `C^∞`.
- `isContactFormAt_iff_isContactAt`, `isContactForm_flatSmoothForm_iff`: TauCeti's contact
  condition, pointwise and global, is `IsContactAt`.
- `IsBeltramiOn.isContactForm_flatSmoothForm`, `IsBeltramiOn.reebVectorField_flatSmoothForm`:
  a smooth Beltrami field with `λ ≠ 0`, `B ≠ 0` everywhere gives a TauCeti contact form whose
  Reeb vector field is `B/‖B‖²`.
- `Sanity/FormContactManifold`: the helical field is a contact form with Reeb field itself;
  a constant field is not a contact form.
- Not done: the version on an open subset.

## Phase 2 of the remaining tasks (sub-agents, 23 November 2026)

Two more modules, written by sub-agents in parallel and rebuilt and axiom-checked in the main
session.

**The magnetic symplectic form** (`Theory/Kinetic/MagneticSymplectic`), on the phase space
`Space × StrongDual ℝ Space` with TauCeti's canonical form.

- `kineticMomentumMap q A`: `(x, p) ↦ (x, p − qA(x)♭)`, TauCeti's magnetic translation
  (`cotangentFiberTranslate`) for the 1-form `q A♭`; it is bijective.
- `extDeriv_potentialForm`: `d(qA♭) = q · flux(∇ × A)`, with no hypothesis.
- `canonicalForm_fderiv_kineticMomentumMap_flux`: where `A` is differentiable, the canonical
  form pulled back by this map is `Ω + q π^*ω_B` with `B = ∇ × A`. The statement is pointwise,
  on derivatives.
- `magneticHamiltonian m q A` (`‖p♯ − qA(x)‖²/(2m)`, `magneticHamiltonian_eq`) and
  `lorentzOrbit_hamilton`: for `m ≠ 0`, `A` differentiable and `B = ∇ × A`, a Lorentz orbit with
  `E = 0`, lifted with canonical momentum `m v♭ + qA♭`, is an integral curve of TauCeti's
  Hamiltonian vector field of that Hamiltonian.
- `Sanity/MagneticSymplectic`: Landau gauge (`landau_magneticForm`, `landau_hamilton`); the
  explicit helix orbit satisfies the hypotheses (`helix_hamilton`); with `q = 0` the magnetic
  term vanishes, and for `q ≠ 0`, `B₀ ≠ 0` it cannot be dropped (`landau_not_symplectic`).
- Not done: the converse (integral curves are Lorentz orbits); an electric field or
  time-dependent `A`; the map bundled as a symplectomorphism; TauCeti's Hamiltonian flow.

**The anti-self-dual lift of a vacuum field** (`Theory/Fields/FormHYMLift`; N-42 S-13).

- `hymLift ω`: the 2-form `ℱ = π^*ω − π^*(⋆ω) ∧ dτ` on `Space × ℝ`, independent of `τ`. The
  sign is the source's (`continuation_geometry.tex`: `ℱ = β − α ∧ dt` with `α = B♭`,
  `β = ⋆₃α`, orientation `dx ∧ dy ∧ dz ∧ dt`), not the plus sign written earlier in this note.
- `extDeriv_hymLift_eq_zero_iff`: `dℱ = 0` at `(x, τ)` iff `dω = 0` and `d(⋆ω) = 0` at `x`.
  No differentiability hypothesis is needed.
- `hymLift_closed_iff_vacuumForm`, `hymLift_closed_iff_vacuumField`: for a `C²` field on an
  open `Ω`, the lift is closed on `Ω × ℝ` iff the field is a vacuum field.
- `hymLift_isAntiSelfDual`: `ℱ(eᵢ, e_τ) = −ℱ(eⱼ, eₖ)` for `(i, j, k)` cyclic. This is
  anti-self-duality written in components for that orientation; it is not derived from a Hodge
  star on `ℝ⁴`. It agrees with N-37.
- `Sanity/FormHYMLift`: accepted, constant and hyperbolic fields; rejected, the rotation field
  (fails Ampère; defect `−2`) and the identity field (fails Gauss; defect `3`); the opposite
  sign is not anti-self-dual (`wrong_sign_not_antiSelfDual`).
- Not done: the quotient to `Ω × S¹`; the complex structure, the line bundle and its Chern
  class, the energy identity and Yang–Mills minimality.

## Second round, phase 1 (sub-agents, 23 November 2026)

The limits recorded after the first round were taken up in two further phases. Phase 1, three
modules written in parallel and rebuilt and axiom-checked in the main session:

**Finite symmetry and the direct proofs** (`Theory/Kinetic/NoetherSymmetryBridge`).

- `fderiv_eq_of_equivariant`: equivariance of `A` under a one-parameter family `g s` with
  `g 0 y = y` and velocity `K` at `s = 0` gives the infinitesimal condition
  `DA(y)(K y) = K(A y)`. `fderiv_rotGenZ_of_rotZ_equivariant` is the case of the rotations
  `rotZ` about the z-axis; `canonicalMomentum_conserved_of_rotZ_equivariant` follows.
- `symmetryFluxGrad A K y = DA(y)†(K y) − K(A y)` is the gradient of `ψ = ⟪A, K x⟫`
  (`hasFDerivAt_symmetryFlux`, `K` skew).
- `symmetricFlux_symmetryFluxGrad_iff`: with `B = ∇ × A`, the hypothesis `SymmetricFlux` of
  the direct proof holds for this gradient **iff** `A` is infinitesimally equivariant.
  `axisymmetricFlux_iff_symmetricFlux_rotGenZ`: `AxisymmetricFlux` is `SymmetricFlux` for the
  z-rotation.
- `noetherMomentum_linear_conserved_direct`, `canonicalMomentum_rotGenZ_conserved_direct`: the
  same conservation laws proved from the direct theorems, without TauCeti. Each law now has two
  independent proofs.
- Sanity: the symmetric gauge is equivariant under all `rotZ s`; the Landau gauge is not
  equivariant under `rotZ (π/2)` and does not satisfy `SymmetricFlux`.
- Not done: the gauge-term case is not bridged; infinitesimal ⇒ finite equivariance.

**Periods for loops on an interval** (`Theory/Fields/FormLoopCurrentInterval`).

- `lineIntegral_eq_periodHom`: for a `C¹` curl-free field on `U` and a curve that is `C¹` on
  `[a, b]`, lies in `U` there and closes up, the circulation is the period on the class of the
  loop reparametrised by a smooth transition function (`smoothParam`, `intervalPath`). A corner
  at the closing point is allowed.
- `poloidalCirculation_eq_periodHom_of_Icc`, `loopCurrent_eq_periodHom_div_of_Icc`: the
  contract's loop current with hypotheses on `[−π, π]` only. `intervalPath_poloidal_homotopic`:
  the new loop is homotopic to the earlier `poloidalPath` when both are defined.
- `VacuumField.lineIntegral_eq_zero_of_simplyConnected`: zero circulation on a simply connected
  region, now derived from the period (the fundamental group is trivial).
- `FieldTorus.loopCurrent_eq_periodHom_div`, `FieldTorus.loopCurrent_eq_zero_of_simplyConnected`,
  `CurrentFreeTransform.current_eq_zero_of_simplyConnected`: the contract structures supply
  periodicity and regularity, so the only extra hypothesis is that the loop lies in `U`.
- Sanity: a poloidal loop around a straight wire has circulation and period `2π`
  (`ring_poloidalCirculation`, `ring_period`), the rejected case that was missing; the complement
  of that wire is not simply connected; a non-periodic profile does not close up.
- Not done: piecewise `C¹` loops; the field must be curl-free on all of `U`; the `FieldTorus`
  and `CurrentFreeTransform` corollaries have no concrete fixture.

**Contact forms on an open subset** (`Theory/Fields/FormContactOpens`).

- `flatSmoothFormOn U B hB`, `isContactFormAt_onOpens_iff`,
  `isContactForm_flatSmoothFormOn_iff`, `IsBeltramiOn.isContactForm_flatSmoothFormOn`,
  `IsBeltramiOn.reebVectorField_flatSmoothFormOn`: the statements of `FormContactManifold` on a
  region `U`, with hypotheses only on `U`; they agree with the `ℝ³` version for `U = ⊤`.
- Sanity: `shearField = (0, x²/2, 1)` has `⟪B, ∇ × B⟫ = x`, so it is a contact form on the
  half-space `x > 0` and not on `ℝ³`; a field equal to the helical field only on the half-space.
- Not done: smoothness of the Reeb vector field and its flow.

## Second round, phase 2 (sub-agents, 23 November 2026)

**Hamilton's equations with an electric field, and the converse**
(`Theory/Kinetic/MagneticHamiltonConverse`).

- `emHamiltonian m q A Φ = ‖p♯ − qA(x)‖²/(2m) + qΦ(x)`, with `E = −∇Φ` stated through the
  existing `IsPotential Φ E`.
- `hamiltonianVectorField_emHamiltonian`: Hamilton's equations in closed form,
  `x' = v`, `p' = q(DA)ᵀv + qE♭`, with `v = m⁻¹(p♯ − qA(x))`.
- `lorentzOrbit_emHamilton` (forward), `lorentzOrbit_of_emHamilton` (converse),
  `lorentzOrbit_iff_emHamilton` and `emHamilton_iff_exists_lorentzOrbit`: for `m ≠ 0`, `A`
  differentiable, `B = ∇ × A`, the Lorentz equations and Hamilton's equations are equivalent.
  The converse needs no more regularity than the forward direction.
- `emHamiltonian_conserved` (TauCeti's conservation along integral curves) and
  `emHamiltonian_canonicalCurve` (the Hamiltonian on the lift is the existing `orbitEnergy`).
- Sanity: uniform `E`, the uniformly accelerated orbit is an integral curve and is recovered by
  the converse; the free straight line is not an integral curve when `q ≠ 0`, `E₀ ≠ 0`, and is
  one when `q = 0`.
- Not done: an explicit orbit in crossed fields (the crossed-field statement has no fixture
  with `B₀ ≠ 0`); existence and uniqueness of integral curves; time-dependent potentials;
  orbits on a time interval.

**A Hodge star on `ℝ³ × ℝ` and the circle quotient** (`Theory/Fields/FormHYMStar`).

- `liftParts : LiftForm 2 ≃ₗ Form 2 × Form 1`: every 2-form is `π^*a + π^*e ∧ dτ`.
- `liftStar`, with `⋆(π^*a + π^*e ∧ dτ) = π^*(⋆₃⁻¹e) + π^*(⋆₃a) ∧ dτ`; `liftStar_liftStar`
  (`⋆⋆ = 1`); values on the coordinate 2-forms (`liftStar_dX_wedge_dX`,
  `liftStar_dX_wedge_dTau`).
- `euclidForm_liftStar`: `liftStar` is TauCeti's intrinsic Hodge star
  (`Orientation.formHodgeStar`) for the product Euclidean metric and the orientation of the
  frame `(e₀, e₁, e₂, e_τ)`; `wedge_liftStar_apply`: `F ∧ ⋆G = ⟨F, G⟩ vol`, evaluated on
  4-tuples. So the signs are checked against an independent definition.
- `isAntiSelfDual_iff_liftStar`: the component condition of `FormHYMLift` is exactly
  `⋆F = −F`. `liftStar_eq_neg_iff_exists`, `hymLiftEquiv`: the lift is a linear isomorphism
  from `Form 2` onto the anti-self-dual 2-forms. `finrank_antiSelfDualForms = 3`,
  `finrank_selfDualForms = 3`, and the two spaces are complementary.
- Circle: `hymLiftCircle ℓ ω` on `Space × AddCircle ℓ`, defined through periodicity, with
  `hymLiftCircle_coe` and uniqueness; `hymLiftCircleForm` is a rough 2-form on the manifold
  `Space × AddCircle ℓ` whose pullback along the covering map is `hymLift ω`
  (`mpullback_hymLiftCircleForm`).
- Sanity: basis values; the lift is anti-self-dual and not self-dual; the opposite-sign form is
  self-dual; a purely spatial form is neither; with the opposite orientation the lift is
  self-dual (agreeing with N-37).
- Not done: closedness and smoothness of the form on `Space × AddCircle ℓ` in terms of the
  manifold exterior derivative (closedness is proved only on `Space × ℝ`); an open `Ω` in place
  of `Space`; the complex structure, the line bundle, its Chern class, the energy identity and
  Yang–Mills minimality.

## Third round, phase 1 (sub-agents, 23 November 2026)

**Piecewise `C¹` loops and polygons** (`Theory/Fields/FormPiecewisePeriod`).

- `pathClassIntegral_arcPath`: for a curve `C¹` on `[a, b]` in `U` (not closed), TauCeti's
  integral over the path class is the line integral.
- `PiecewiseC1In U γ t n` (a partition `t 0 < … < t n` with `γ` `C¹` and in `U` on each piece),
  `lineIntegral_eq_periodHom_piecewise`: the circulation around a closed piecewise `C¹` loop is
  the period on the concatenated class (`chainLoop`). Any finite number of corners.
- `sum_lineIntegral_segCurve_eq_periodHom`: closed polygons, as the sum of the edge integrals.
- `VacuumField.lineIntegral_eq_zero_of_piecewise`: zero circulation on a simply connected
  region, from the period.
- Sanity: a square around the wire has edge integrals `π/2` each, circulation and period `2π`
  (`square_period`), and is proved not `C¹` at a vertex (`square_not_contDiffOn`), so it needs
  this theorem; a triangle in the bent region has zero circulation.
- Not done: the concatenated class is not compared with the affinely parametrised loop; no
  contract-clause version for piecewise loops.

**Convex regions and the contract's current clause** (`Theory/Fields/FormConvexRegion`,
`Sanity/ContractLoopCurrentFixture`).

- `simplyConnectedSpace_of_convex`: nonempty convex open sets are simply connected (balls, all
  of `ℝ³`). `VacuumField.lineIntegral_eq_zero_of_convex` and the poloidal versions.
- `meridianHalfSpace φ₀ = {x | 0 < x₀ cos φ₀ + x₁ sin φ₀}` is convex and misses the z-axis, and
  every poloidal loop at toroidal angle `φ₀` with `R > 0` lies in it
  (`poloidalLoop_mem_meridianHalfSpace`).
- **Consequence for contract clause C1.** `CurrentFreeTransform.imax_zero_of_meridianHalfSpace`:
  if `B` is a vacuum field on a region containing those half-spaces (for instance away from the
  z-axis), then any `CurrentFreeTransform` holds with current allowance `0`. For vacuum fields
  the net-current bound of C1 is therefore automatic; it has content only for fields with
  current. Zero poloidal circulation is compatible with `ι ≠ 0` in a non-axisymmetric field.
- Fixture with `ι > 0`: the rational stellarator field and its certified torus
  (`rationalStellarator_fixture`, `exactTorus_loopCurrent`, `exactTorus_period`); with `ι = 0`:
  the purely toroidal field (`toroidal_circ_loopCurrent`). Rejected: no convex region inside
  the ring wire's complement contains the torus section (`ring_no_convex_region`).
- Relation to the audit theorem `Sanity.AuditRefresh.CurrentFreeTransform.circulation_eq_zero`:
  that one assumes allowance `0` and no vacuum hypothesis; the new one assumes vacuum and any
  allowance. Neither implies the other; they compose (`circulation_eq_zero_via_audit`).
- Not checked in Lean: the same for the on-demand Dommaschk instances (their field is also
  vacuum away from the z-axis).

**Gauge terms and gauge invariance** (`Theory/Kinetic/NoetherGaugeBridge`).

- `symmetricFlux_gauge_iff`, `axisymmetricFlux_gauge_iff`: with `B = ∇ × A`, the hypothesis of
  the direct proof for `ψ = ⟪A, K x⟫ − χ` is equivalent to equivariance up to `G = ∇χ`.
  `noetherMomentum_linear_gauge_conserved_direct`: a second proof of the gauge-term law.
- Gauge transformation `A ↦ A + ∇Λ`: `fieldCurl_add_gradient` (the field is unchanged),
  `equivariant_gauge_add_gradient` (the defect becomes `G + D(∇Λ)(K y) − K(∇Λ)`), and the
  gauge term becomes `χ + ⟪∇Λ, K x⟫`. With that rule the conserved momentum is exactly
  unchanged (`noetherMomentum_add_gradient`); any other gauge term with the same gradient
  shifts it by a constant (`noetherMomentum_add_gradient_of_gauge_term`); dropping the gauge
  term shifts it by `q⟪∇Λ, K x⟫` (`noetherMomentum_add_gradient_naive`).
- `rotZ_equivariant_iff_commute`: for a continuous linear `A`, commuting with `rotGenZ` is
  equivalent to equivariance under every `rotZ s` (infinitesimal ⇔ finite, linear case).
- Sanity: the Landau gauge is the symmetric gauge plus `∇(B₀xy/2)`, and the rule reproduces its
  gauge term `B₀(x² − y²)/2`; with the wrong gauge term the hypothesis fails.
- Not done: infinitesimal ⇒ finite for nonlinear `A`; time-dependent gauge functions.

## Third round, phase 2 (sub-agents, 23 November 2026)

**The lift on the manifold `Ω × S¹`** (`Theory/Fields/FormHYMCircle`).

- `isSmoothForm_hymLiftCircleForm_iff`: the form on `Space × AddCircle ℓ` is `C^n` iff `ω` is.
- `mextDeriv_hymLiftCircleForm_eq_zero_iff`: where `ω` is `C¹`, the manifold exterior derivative
  vanishes at `(x, θ)` iff `dω = 0` and `d⋆ω = 0` at `x`.
  `hymLiftCircleForm_closed_iff_vacuumField`: for a `C²` field on `ℝ³`, closed iff vacuum.
- `circleRegion ℓ U`, `hymLiftRegionForm ℓ U ω`: the open submanifold `U × S¹` and the
  restricted form. `hymLiftRegionForm_closed_iff_vacuumForm`,
  `hymLiftRegionForm_closed_iff_vacuumField`: for `C²` data on `U`, the form on `U × S¹` is
  closed iff the field is a vacuum field on `U`. This is the statement of N-42 S-13 on the
  source's manifold.
- Energy: `liftInner_hymLiftAt_self` (`|ℱ|² = 2|B|²` pointwise),
  `integral_liftInner_hymLiftCircle` (`∫_{Ω×S¹}|ℱ|² = 2ℓ∫_Ω|B|²`).
- Sanity: constant and hyperbolic fields have closed lifts on the circle product; the rotation
  and identity fields do not; a discontinuous `ω` does not give a continuous form.
- Not done, with what TauCeti lacks (from a search of its declarations, not from building
  against them): the complex structure on `ℝ³ × S¹` and the `(1,1)` and primitivity statements;
  a line bundle with connection constructed from a closed 2-form with integral periods; a first
  Chern class and the Chern–Weil identification; a Yang–Mills functional and a minimality
  theorem. TauCeti does have curvature forms of connections, an Euler class, a manifold Hodge
  star and the identity `∫|F|² = 2∫|F⁺|² − ∫F∧F`.
- Limit: closedness on the circle product needs `ω` of class `C¹` at the point (from TauCeti's
  naturality of the exterior derivative); on `ℝ³ × ℝ` no regularity was needed.

**Crossed fields, existence and uniqueness** (`Theory/Kinetic/CrossedFieldOrbit`).

- `crossedField_orbit`: the explicit `E × B` drift orbit for `E = E₀e_x`, `B = B₀e_z`, with
  gyrofrequency `qB₀/m` and drift `driftVelocity E₀ B₀ = −(E₀/B₀)e_y = (E × B)/|B|²`, for all
  initial data (`crossedField_orbit_exists`). `crossedPosition_period`: per gyro-period the
  position advances by the period times the drift plus the parallel velocity.
- `crossedField_hamilton`, `crossedField_energy`: it is an integral curve of the Hamiltonian
  field and conserves energy; the crossed-field statement now has an instance with `B₀ ≠ 0`.
- `emHamilton_exists_local`, `emHamilton_unique`: for `A` of class `C²` and `E = −∇Φ` of class
  `C¹`, integral curves of the Hamiltonian field exist locally and are unique.
- `LorentzOrbitOn` (orbit equations on a set of times), `lorentzOrbitOn_iff_emHamilton`,
  `lorentzOrbitOn_exists_local`, `lorentzOrbit_unique`: local existence and uniqueness of
  Lorentz orbits under the same hypotheses and `m ≠ 0`.
- `exists_global_of_linear_growth`, `lorentzOrbit_existsUnique_linearGauge`,
  `lorentzOrbit_existsUnique_uniform`: for a linear vector potential and an electric field of
  linear growth, in particular for arbitrary uniform `E` and `B`, a unique Lorentz orbit exists
  for all time from every initial position and velocity.
- Relation to the existing `lorentzOrbit_exists` (`Theory/Kinetic/LorentzExistence`): that one
  has no electric field, allows any globally `C¹` `B`, and states no uniqueness; neither
  result contains the other. `lorentzOrbit_unique` supplies uniqueness for it when
  `B = ∇ × A` with `A` of class `C²`.
- Sanity: explicit values; uniform motion with the drift velocity is an orbit, and with the
  opposite velocity it is not (`opposite_drift_not_orbit`), which checks the sign.
- Not done: global existence for a general vector potential with an electric field (needs an
  a priori bound); uniqueness without potentials; regularity on an open subset only.

## Next steps

Three rounds of follow-up are complete. What remains is of a different kind:

1. The complex structure, line bundle, Chern class and Yang–Mills minimality of N-42 S-13:
   blocked on constructions that TauCeti does not have.
2. The de Rham classes of an embedded flux surface (needs flux surfaces as submanifolds).
3. Checking `CurrentFreeTransform.imax_zero_of_meridianHalfSpace` on the on-demand Dommaschk
   instances.
4. A strict audit of the modules added on 23 November 2026 (none has been audited).

## Barriers

- **Smoothness.** The kernel laws are `C²`. TauCeti's cohomology groups need `C^∞` forms.
  The polynomial and rational fixtures are smooth, but `VacuumField` does not say so.
- **Embedded surfaces.** Flux surfaces are parametrised tori in the contract layer
  (`FieldTorus`), not submanifolds. De Rham statements on a flux surface need them as manifolds.
- **Build cost.** TauCeti files are compiled locally the first time they are imported. The
  default build now has 11,123 jobs, up from 7,938; the increase is almost all TauCeti files.
- **Not checked.** TauCeti files were read for their statements; their proofs were not
  reviewed. The theorems listed above pass the project's axiom check (standard axioms only),
  which covers the TauCeti results they use.

## Outputs and next dependencies

- New modules `Theory/Fields/FormCalculus`, `FormTopology`, `FormContact`, `FormPeriods`,
  `Theory/Kinetic/NoetherLagrangian`, and a `Sanity` module for each, imported by
  `PlasmaLean.lean`.
- The Rosetta-stone page: nine entries extended (solenoidal field, vacuum field, net current,
  Beltrami fields, helicity, frozen-in flux, quasisymmetry, Noether symmetry, charged-particle
  motion).
- Pointers added in N-45, N-43 and N-42.
- Next: steps 1 and 3 above.
