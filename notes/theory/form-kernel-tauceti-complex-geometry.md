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
| Lean evidence | default build, namespace `PlasmaLean.Forms` unless noted: `lieDerivForm_eq_zero_of_interior`, `FormWeakQS.lieDerivForm_eq_zero`, `PlasmaLean.Fields.WeakQS.lieDerivForm_flux_eq_zero`, `VacuumForm.exists_scalarPotential`, `VacuumForm.exists_vectorPotential`, `onOpens`, `isSmoothForm_onOpens_iff`, `mextDeriv_onOpens`, `VacuumForm.exists_scalarPotential_of_simplyConnected`, `not_simplyConnected_of_no_potential`, `wedge12_eq_wedge`, `isContactAt_iff_nondegenerate`, `IsBeltramiOn.reeb`; `PlasmaLean.Sanity.FormTopology.wireField_no_potential`, `wireRegion_not_simplyConnected`, `bentSet_not_starConvex`, `hyperbolic_scalarPotential_bent`; `lieDerivForm_flux`, `PlasmaLean.Fields.WeakQS.lieBracket_eq_zero`, `IsBeltramiOn.reeb_unique`, `pathIntegral_onOpens_flat`, `periodHom_onOpens_flat`, `PlasmaLean.Sanity.FormPeriods.wire_period`; `PlasmaLean.Kinetic.lorentzOrbit_eulerLagrange`, `noetherMomentum_translation_conserved` |
| Audit evidence | not audited |
| Last updated | 23 November 2026: created; same day, the manifold bridge, the wedge and contact links, the wire fixture and the symplectic assessment; then periods, `[ξ, B] = 0`, uniqueness of the Reeb vector, a non-star-convex fixture and the Noether charge from TauCeti |
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

**Not reached.** The period statement is for loops parametrised over `[0, 1]`; the contract's
`loopCurrent` uses poloidal loops over `[-π, π]` and is not yet restated as a period. The de Rham
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
| N-42 S-13: Hermitian–Yang–Mills lift | `F = ω_B + ⋆ω_B ∧ dτ` is closed on `Ω × S¹` iff `dω_B = 0` and `d⋆ω_B = 0` | the two conditions are exactly `VacuumForm`; the 4-dimensional statement needs forms on `ℝ³ × ℝ` (lean-ready, moderate; not done) |
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

All in the default build, standard axioms only (`scripts/check_axioms.lean`, 35 entry points).

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
needs phase spaces as manifolds, which the project does not have. `Hamiltonian/Noether` is now
used (above); `Cotangent/Fiberwise` is not.

## Next steps

Done since the first version of this note: `[ξ, B] = 0`; uniqueness of the Reeb vector; periods
linked to circulation; a simply connected, non-star-convex fixture; a Noether charge from
TauCeti. Still open:

1. **Rotational symmetry from Noether.** `canonicalMomentum_conserved` (axisymmetry) needs a
   linear generator and in general a gauge term (`TauCeti.lagrangianVariation_comp_snd`); only
   translations are derived.
2. **Magnetic symplectic form** of a Lorentz orbit through `Cotangent/Fiberwise`.
3. **`loopCurrent` as a period**: reparametrise the contract's poloidal loops to `[0, 1]`.
4. **Bundled contact form** on `ℝ³` (`TauCeti.SmoothForm.IsContactForm`) for a smooth Beltrami
   field.
5. **The HYM lift** of N-42 S-13 as a statement about a 2-form on `ℝ³ × ℝ`.

## Barriers

- **Smoothness.** The kernel laws are `C²`. TauCeti's cohomology groups need `C^∞` forms.
  The polynomial and rational fixtures are smooth, but `VacuumField` does not say so.
- **Embedded surfaces.** Flux surfaces are parametrised tori in the contract layer
  (`FieldTorus`), not submanifolds. De Rham statements on a flux surface need them as manifolds.
- **Build cost.** TauCeti files are compiled locally the first time they are imported. The
  default build now has 10,413 jobs, up from 7,938; the increase is almost all TauCeti files.
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
