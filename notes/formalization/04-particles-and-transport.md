# Particle confinement, kinetic stability, and transport

Ideal-MHD stability addresses large-scale fluid perturbations. This parallel development addresses orbit loss, bootstrap current, neoclassical heat loss, and microinstabilities. References and source caveats are in [09-literature.md](09-literature.md).

The chapter was written on 12 October 2026 as a specification. Its exposition still describes the target mathematics. A status layer, last revised on 30 October 2026, records what has since been compiled, which model laws are supplied, what is open and what was corrected. The status layer follows the plan of record (the [implementation plan](implementation-plan.md), section "The stellarator contract", the research graph RG.1–RG.5 and the §13 log) and the [30 October progress report](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md). A declaration counts as evidence only when it is a named, compiled Lean declaration with standard axioms only. "Default build" means the module is imported by `PlasmaLean.lean`. "On demand" means a separate top module, built and axiom-checked on the workstation and spot-checked on the laptop.

## Contents

- [Status in PlasmaLean and the stellarator contract](#status-in-plasmalean-and-the-stellarator-contract)
- [Full-orbit dynamics](#full-orbit-dynamics)
- [Guiding-centre dynamics](#guiding-centre-dynamics)
- [Symmetry, omnigeneity, and finite-time bounds](#symmetry-omnigeneity-and-finite-time-bounds)
- [Drift-kinetic transport](#drift-kinetic-transport)
- [Gyrokinetic stability and turbulence](#gyrokinetic-stability-and-turbulence)
- [Profile evolution and reactor power](#profile-evolution-and-reactor-power)
- [Theorem backlog](#theorem-backlog)

## Status in PlasmaLean and the stellarator contract

Since 30 October 2026 the project is organized around the [stellarator contract](implementation-plan.md#the-stellarator-contract-30-october-2026). The clauses are C1 (current-free rotational transform), C2 (omnigeneity or bounded ε_eff for thermal ions and electrons), C3 (MHD stability at finite β), C4 (existence) and C5 (thermal performance on the same candidate). The normative specifications are in [00-model-contracts.md](00-model-contracts.md#stellarator-contract-c1-c2-and-c5). This chapter covers the particle and transport parts of the contract:

- **C2** is the kinetic core of the chapter. It concerns bounce-averaged radial drift, omnigeneity and effective ripple for *thermal* ions and electrons. **C2 is essentially open.** No bounce-averaged drift, omnigeneity predicate or ε_eff is yet a compiled contract predicate (Q-21). The bridge from quasisymmetry to omnigeneity (Q-23) is compiled in the supplied Boozer guiding-centre model (`omnigenousOn_of_exactQS`, `approxOmnigenousOn_of_defect_le`, `Theory/Kinetic/Omnigeneity`), but nothing yet links it to ε_eff or to thermal transport. Thermal neoclassical bounds (Q-22) have not been started.
- **Alpha confinement** is one part of C2, for one species. Most of the alpha results cover passing orbits. It does not substitute for C2.
- **C5** uses this chapter's transport and power-balance theory. It holds only for a tokamak model (Solov'ev, with a supplied transport solution) and in 0-D on stellarator parameters. C2 couples into C5: poor omnigeneity means large 1/ν losses, which can make burn inaccessible (Q-13).
- **C1** enters through the bootstrap current. The contract bounds the net toroidal current at bootstrap level, and the drift-kinetic solution below is what would supply that bound.

| Topic | Compiled evidence (module) | Build | Scope and supplied models |
| --- | --- | --- | --- |
| Full orbits | `kinetic_energy_conserved`, `energy_conserved`, `helix_orbit`, `larmor_radius_formula` (`Theory/Kinetic/FullOrbit`); `canonicalMomentum_conserved`, `orbit_trapped` (`Theory/Kinetic/CanonicalMomentum`) | default | Newton–Lorentz model `LorentzOrbit`; Noether invariant for an exact symmetry |
| Orbit existence | `ODEGlobal.exists_global_of_apriori` (`Theory/Fields/ODEContinuation`), `Kinetic.lorentzOrbit_exists` (`Theory/Kinetic/LorentzExistence`); `reactor_alpha_born_confined`, `reactor_alpha_confined_nonvacuous_35MeV` (`Design/SolovevAlphaExistence`) | default | C¹ field; the reactor field is Solov'ev, a tokamak model (audit MA-M2 closed) |
| Near-QA orbit existence | `boozerGCOrbitOn_exists_local`, `ODEGlobal.exists_forward_of_apriori`, `band_estimate`, `alpha_band_orbit_exists_005`, `alpha_orbit_exists_explicit`; obstructions `Dpsi_gt_psiStart`, `band_empty_Tav` (`Design/NearAxisQAExistenceFull`) | default | Boozer guiding-centre model, chart ψ > 0 (audit MA-M1) |
| Passing alphas, rational vacuum field | `alpha_gc_passing_confined_forever`, `alpha_gc_confined_forever_robust`, `alpha_gc_confined_forever_pm`; on demand `alpha_gc_passing_confined_forever_quarter`, `alpha_gc_confined_forever_energy_window` | default and on demand | Littlejohn guiding-centre model (supplied); vacuum field satisfying C1 in vacuum |
| Trapped alphas | `reference_kick_osc`, `exactQA_kick_osc` (`Design/NearAxisQATrappedOscCover`) | default | Single-bounce kick bound only; Q-1 open and parked |
| Quasisymmetry (adjacent to C2) | `WeakQS`, `qsDefect` (`Theory/Fields/WeakQuasisymmetry`); `family1_not_weakQS`, `family2_not_weakQS` (`Design/LandremanNotQS`) | default | Pointwise Constantin–Drivas–Ginsberg definition; not omnigeneity |
| Omnigeneity, ε_eff (C2) | none compiled | — | Specified in the model contracts (Q-21); Q-19, Q-22, Q-23 open |
| Transport and burn (C5) | `solovev_one_plasma_actual` (`Design/SolovevFluxGeometry`); `relEnt_pointwise_identity` (`Theory/Transport/RelativeEntropy`); `stellaris_measured_fren_no_access_steady` (`Design/BurnWindowStellarator`) | default | Transport solution supplied; Bosch–Hale enclosure and ISS04 scaling supplied |

## Full-orbit dynamics

For a nonrelativistic particle of mass `m>0` in specified fields:

$$
\dot x=v,\qquad m\dot v=q(E+v\times B).
$$

For a static magnetic field and `E=-∇Φ`, prove conservation of

$$
H=\tfrac12m|v|^2+q\Phi(x).
$$

For `q≠0`, `E=0` and uniform nonzero `B`, prove the helix solution and Larmor-radius formula. Include the straight-line `q=0` or `B=0` limit separately. These are useful nonvacuity and sign tests.

Define confinement as `x(t) ∈ Ω_safe` for all `t ∈ [0,T]` and all initial conditions in a declared set `K`. An invariant magnetic surface constrains field lines; full particle motion includes perpendicular velocity and does not automatically remain on that surface.

Possible first certificates are:

- interval-enclosed orbit integration for a compact initial set and finite time;
- an invariant energy or Lyapunov barrier separating initial states from a loss boundary;
- a reduced-orbit certificate with a proved full-orbit error smaller than the spatial margin.

Treat a probability of loss separately: define an initial probability measure and prove a measure bound. Tracking a sampled ensemble yields a numerical estimate, not a universal or measure theorem by itself.

**Status in PlasmaLean.** The basic theory is compiled in the default build. The model is the structure `LorentzOrbit` (`Theory/Kinetic/FullOrbit`). The module proves energy conservation, speed conservation in a pure magnetic field, the exact helix in a uniform field and the Larmor-radius formula, with physical sanity values (`alpha_3_5MeV_5T`, `deuteron_10keV_5T`). An exact Killing symmetry (rotation, translation or helix) gives a conserved canonical momentum (`canonicalMomentum_conserved`), which traps orbits between flux surfaces (`orbit_trapped`). A version with a symmetry defect gives finite-time trapping (`approx_flux_band`, `orbit_trapped_until`). These results realize the second item of the list above for symmetric fields.

The 30 October work proved that the orbits these theorems quantify over actually exist:

- `ODEGlobal.exists_global_of_apriori`: a C¹ field on an open set, together with a compact a-priori bound on every finite horizon, gives a global solution.
- `Kinetic.lorentzOrbit_exists`: in a C¹ field defined everywhere, Lorentz orbits exist for all time.
- For the reactor Solov'ev field, which is singular on the vertical axis, 3.5 MeV alpha orbits born in the core exist for all time and are all confined (`reactor_alpha_orbit_exists`, `reactor_alpha_born_confined`). An explicit witness at exactly 3.5 MeV is `reactor_alpha_confined_nonvacuous_35MeV`.

This closed audit finding MA-M2. Under the contract the Solov'ev field is a **tokamak model** (axisymmetric and current-carrying), so these results are technique test beds and inputs to the C5 model, not stellarator evidence.

Not done: no interval-enclosed full-orbit integration, no reduced-to-full-orbit error theorem (K10), and no probabilistic loss bound (the G-3 work packages P1–P4 are proposals only).

## Guiding-centre dynamics

Use [Littlejohn's variational formulation](09-literature.md#stability-and-kinetic-theory). For static fields, a chosen leading-order guiding-centre model uses `(X,v∥,μ)`, where `μ=m v⊥²/(2|B|)` and `b=B/|B|`. One convention is

$$
B^*=B+\frac{mv_\parallel}{q}\nabla\times b,\quad
B_\parallel^*=b\cdot B^*,\quad
E^*=E-\frac{\mu}{q}\nabla|B|,
$$
$$
\dot X=\frac{v_\parallel B^*+E^*\times b}{B_\parallel^*},\qquad
\dot v_\parallel=\frac q m\frac{B^*}{B_\parallel^*}\cdot E^*,\qquad
\dot\mu=0.
$$

Require `m>0`, `q≠0`, `|B|≥B_*>0`, and `|B∥*|≥b_*>0` on the certified phase-space set. Derive the equations from the chosen action/Poisson structure. With a time-independent, single-valued scalar potential `E=-∇Φ`, prove conservation of `H_gc=m v∥²/2+μ|B|+qΦ`. Static fields alone do not ensure a global scalar potential on a multiply connected domain. Time-dependent fields add terms and must have a separate interface.

Exact invariance of `μ` belongs to this reduced model. In full Lorentz motion it is an adiabatic approximation. A model-reduction theorem must include initial-data matching, regularity, the small-gyroradius regime, and a time-dependent error bound.

**Status in PlasmaLean.** Two guiding-centre models are compiled. Both are **supplied models**: their equations of motion are definitions, not consequences of the Lorentz force.

- **Littlejohn model.** `LittlejohnOrbit` (`Theory/Kinetic/GuidingCentreLittlejohn`) implements the equations above in the static magnetic case. Proved: energy conservation (`energy_const`), and the fact that a μ = 0 orbit follows a field line of the modified field B* (`littlejohn_mu0_isFieldLine`). The strict model audit (finding H-1) re-derived the definition against Littlejohn and found that it matches. A low finding (MA-L2) remains: totalizing (B*∥)⁻¹ admits motionless orbits where B*∥ = 0. It is recorded by a regression theorem in `Sanity/AuditModelGuidingCentre`.
- **Boozer model.** `BoozerField` and `BoozerGCOrbitOn` (`Theory/Kinetic/BoozerGuidingCentre`) give a guiding-centre model in Boozer coordinates. Proved: exact quasisymmetry conserves the helical momentum (`helicalMomentum_conserved`), which traps orbits (`boozerGC_trapped`). `BoozerGCOrbitOn` requires the orbit to stay off the magnetic axis (chart ψ > 0). The audit records that `BoozerField` admits G = 0 and B ≤ 0 (MA-L3).

**Orbit existence in the Boozer model (N-26).** Orbits exist locally (`boozerGCOrbitOn_exists_local`, `reactorQA_orbit_exists_local`). Forward continuation is `ODEGlobal.exists_forward_of_apriori`. For passing alphas a two-sided band estimate holds, ‖ψ(t) − ψ₀‖ ≤ 2.593 + 26.07 t T m² (`band_estimate`). This gives existence on the full horizon for births in a band:

- 2.75 ≤ ψ₀ ≤ 5.5 for 8·10⁻⁴ s (`alpha_band_orbit_exists_short`);
- 4 ≤ ψ₀ ≤ 4.3 for 0.05 s (`alpha_band_orbit_exists_005`, witness `alpha_band_nonvacuous_005`);
- every birth with 0 < ψ₀ ≤ psiStart, on an explicit horizon of about 1.5 μs (`alpha_orbit_exists_explicit`, `alpha_trapped_reactorQA_averaged_explicit`).

Proved obstructions limit this route. No band reaches ψ₀ ≤ psiStart (`Dpsi_gt_psiStart`), and no band survives for T ≥ 0.06 s (`band_empty_Tav`). Existence on the full 0.19 s horizon for the original class therefore needs coordinates through the magnetic axis. That would change the model statement, so it is a user decision (audit MA-M1).

Not done: the derivation from an action principle, conservation of μ as an adiabatic theorem (K10), electric fields, and time-dependent fields.

## Symmetry, omnigeneity, and finite-time bounds

For a genuine symmetry of the guiding-centre action, prove the corresponding Noether invariant. Extract the exact relation between Boozer field-strength quasisymmetry and this symmetry from [Burby–Kallinikos–MacKay](09-literature.md#geometry-equilibrium-and-symmetry). A spatial symmetry of `|B|` alone should not be used as a theorem about an arbitrary kinetic system.

For trapped reduced orbits define the bounce action

$$
\mathcal J_\parallel=\oint mv_\parallel\,dl
$$

at fixed energy and magnetic moment, specifying turning points, sign conventions, and regularity near the trapped–passing boundary. Omnigeneity concerns vanishing bounce-averaged radial drift; in an appropriate formulation it is expressed by independence of the bounce action from field-line label. [Cary–Shasharina](09-literature.md#stability-and-kinetic-theory) provides a starting point.

Keep quasisymmetry, omnigeneity, and quasi-isodynamic geometry as distinct predicates. None alone supplies all-mode MHD stability, all-time full-orbit confinement, or absence of turbulent heat transport.

An elementary approximate-invariant theorem is useful for imperfect designs. Require `K` along each trajectory to be continuously differentiable (or absolutely continuous with the bound almost everywhere):

$$
\left|\frac{dK}{dt}\right|\le\varepsilon
\quad\Longrightarrow\quad
|K(t)-K(0)|\le\varepsilon t.
$$

Take `ε≥0` and forward times `t≥0` in a connected interval on which the trajectory exists. Require initial states inside the safe region and a continuous trajectory so loss requires a first crossing of its boundary. Combine the bound with a proved separation condition: initial states satisfy `K≤k₀`, while every loss-boundary state in the relevant energy/phase-space set satisfies `K≥k_loss>k₀`. For `ε>0`, loss is impossible before `(k_loss-k₀)/ε` within the declared existence interval. For `ε=0`, it is impossible throughout that interval. Establish the separation, continuity, phase-space enclosure, and derivative bounds in the actual dynamics; the derivative bound must hold up to any possible first crossing.

Study tolerances in derivative-sensitive norms. A small Fourier or volume-averaged quasisymmetry residual does not automatically bound every orbit's drift, especially near resonances and separatrices.

**Status in PlasmaLean: the approximate invariant.** The scalar theorem above is compiled (`invariant_drift`, `excludes_loss`, `exact_invariant` in `Theory/Kinetic/ApproximateInvariant`). Its field-line analogue, `fieldLine_confined_of_defect` (`Theory/Fields/DefectConfinement`), is the mechanism behind the finite-transit field-line certificates of [06](06-coils-and-design.md).

**Status in PlasmaLean: alpha confinement.** These results are particle confinement for one species, 3.5 MeV alphas. All of them use the Littlejohn model (supplied), with no collisions and a static vacuum model field, `RationalStellarator.field (1/4)`. That field satisfies C1 in vacuum, so these are C1-compatible particle results. They are not C2.

- Default build:
  - `alpha_gc_passing_confined_forever`: passing guiding centres with λ ∈ [0, 1/16] (μ ≤ K/(16B₀)) at one energy and the design B₀R₀ ∈ [68.9, 69] T·m stay for all time inside an exact KAM torus within 0.255 R₀ of the axis.
  - `alpha_gc_confined_forever_robust`: μ = 0, for every B₀R₀ ∈ [67.95, 69.99] T·m.
  - `alpha_gc_confined_forever_pm`: both signs of v∥, each with its own torus. **v∥ < 0 is proved only at the design B₀R₀** (audit M-1 corrected an earlier claim that it held over the whole interval).
- On demand:
  - `alpha_gc_passing_confined_forever_quarter`: λ ∈ [0, 1/4] at one energy and one B₀R₀. λ = 1/4 is the limit of the passing argument with ‖B‖ ≤ 3B₀ (`quarter_passing_margin`, Q-5).
  - `alpha_gc_confined_forever_energy_window`: a genuine energy-by-pitch family, ±0.4 eV around 3.5 MeV with λ ∈ [0, 1/16]. Wider windows and a joint B₀R₀ range are Q-4.
- Near-axis QA: `alpha_trapped_reactorQA_averaged` bounds passing alphas (v∥² ≥ 0.81 v², despite the name; audit L-4) for 0.19 s in the Boozer model. It is about orbits that stay off the axis, and existence on the full horizon is proved only for the band above (MA-M1).

**Status in PlasmaLean: trapped alphas (Q-1, open and parked).** The single-bounce radial kick is bounded (`reference_kick_osc`: amplitude ≤ 0.0816 T m²; `exactQA_kick_osc`), and the bounce tools in `Theory/Kinetic/BounceOrbits` and `Theory/Kinetic/BounceIntegrals` are compiled. The barrier is the per-bounce remainder: Lipschitz–Grönwall bounds give factors of about e^29000, and re-anchoring with absolute amplitudes cannot close (see the [trapped-alpha status](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/trapped-alpha-status.md)). Under the contract the kick is the single-orbit form of the bounce-averaged radial drift, so Q-1 waits for the C2 definitions (Q-21) and should then be stated as an omnigeneity defect.

**Status in PlasmaLean: quasisymmetry and omnigeneity (C2).** The predicates are kept distinct, as above.

- **Weak quasisymmetry** is compiled (`WeakQS`, `qsDefect`, `qsDefect_eq_zero_iff`). Exact axisymmetry is a special case (`qsError_rotGen_eq_zero_of_axisymmetric`), and the module includes an axis lemma (`WeakQS.normB_const_of_gradient_eq_zero`).
- **Landreman barrier.** For ε ≠ 0 neither Landreman family is weakly quasisymmetric on a region containing the whole axis (`family1_not_weakQS`, `family2_not_weakQS`). Generators that vanish on the axis are not excluded.
- **QS is not a PDE symmetry.** `quasisymmetry_not_pde_symmetry` (`Sanity/QuasisymmetryNotSymmetry`) records that quasisymmetry is not a symmetry of the MHD equations.
- **Bounce action.** The definitions `NormalizedBounceAction` and `BounceActionRadialDeriv` (`Theory/Kinetic/AvailableEnergy`) follow a project note. They are not yet checked against the source.

**Omnigeneity, bounce-averaged radial drift and ε_eff are not compiled.** For thermal ions and electrons, C2 is essentially open. The open questions are:

- Q-21: the definitions, each with the sanity triad: axisymmetric ⇒ omnigenous; current-free axisymmetric ⇒ ι = 0; an explicit 3-D field that is not omnigenous.
- Q-23: quasisymmetry ⇒ omnigeneity, exact and quantitative, in the Boozer model: compiled (default build). Exact QS with twist gives zero net radial drift per bounce (`omnigenousOn_of_exactQS`); a QS defect ≤ δ gives a per-bounce drift linear in δ (`approxOmnigenousOn_of_defect_le`, sharp on an explicit counterexample); `exactQA` is omnigenous. Open: the ε_eff / 1/ν link and the quasi-isodynamic route.
- Q-19: bounce-averaged drift and ε_eff on the certified surfaces of the rational vacuum field. Its C2 status is unknown, and a large ε_eff is the likely outcome.
- Q-16: a Dommaschk QA vacuum field (C1 + C2), described in [06](06-coils-and-design.md).

Quasi-isodynamic fields are a second C2 route, which the project has not started.

## Drift-kinetic transport

Adopt a specified distribution perturbation `g_s` and a drift-kinetic equation schematically

$$
\mathcal T_s(B,E_r)g_s-\mathcal C_s(g)=S_s,
$$

where `T` includes the selected streaming, mirror, and drift terms and `C` is a specified linearized collision operator. Record boundary conditions, particle/momentum/energy conservation, nullspace constraints, and the thermodynamic drives in `S`.

[Landreman–Smith–Mollén–Helander/SFINCS](09-literature.md#stability-and-kinetic-theory) is a source for model choices, not a proof oracle.

Define radial particle and heat fluxes and parallel current through velocity integrals and flux-surface averages, using the chosen heat-flux convention. Prove:

- transport is zero for the correct source-free equilibria;
- conservation and entropy-production/dissipation identities;
- solvability conditions against collision invariants;
- uniqueness on an appropriate constrained quotient;
- an a posteriori bound `‖g-g_N‖ ≤ C‖residual‖` if the required operator stability estimate is proved;
- resulting flux/current errors through continuous functional bounds.

The `C` estimate is not automatic for a kinetic operator. Small collision frequency, trapped particles, and resonant precession can make it difficult.

For ambipolarity define `A(E_r)=Σ_s q_s Γ_s(E_r)`. If a theorem proves continuity, endpoint signs on an interval, and `A'≥a_*>0` there, then prove existence and uniqueness of an ambipolar root. If `|δA|≤η`, the shifted root has a displacement bound under the corresponding monotonicity/domain hypotheses. Do not assume one ambipolar root exists or is unique for every stellarator.

Feed the resulting bootstrap-current and electric-field envelopes back into equilibrium and stability. This closes a physics loop that a zero-current vacuum model omits.

**Status in PlasmaLean.** Nothing in this section is compiled: no drift-kinetic operator, collision operator, ambipolar root or bootstrap current. The contract gives the section two concrete uses:

- **C2 → C5 (Q-22).** The planned route is deliberately coarser than a drift-kinetic solution. A C2 bound (ε_eff or bounce-averaged drift) and a stated 1/ν scaling, χ ∝ ε_eff^{3/2} *supplied as a model law*, would give χ bounds for ions and electrons on stellarator geometry. These would feed the barrier theorems of Q-15.
- **C1 (Q-18, Q-20).** The bound ‖I_tor‖ ≤ I_max in C1 is meant to be bootstrap-level. A certified bootstrap-current envelope is the eventual justification of I_max. At present the only finite-β current-free route is Q-14 → Q-20 (stepped pressure across the certified torus).

## Gyrokinetic stability and turbulence

Select the gyrokinetic ordering, equilibrium, species, electrostatic/electromagnetic approximation, collision model, and field equations. Derive a free-energy balance of the form

$$
\frac{d\mathcal W}{dt}=\mathcal P_{\rm gradients}-\mathcal D_{\rm collisions}
                     +\mathcal P_{\rm sources}-\mathcal F_{\rm boundary},
$$

with exact definitions. Nonnegativity, nullspaces, and source signs must be proved for that model. [Brizard–Hahm](09-literature.md#stability-and-kinetic-theory) gives variational/energy foundations.

Formalize a restricted maximum-`J` trapped-particle stability theorem with its actual ordering and gradient conditions. [Proll et al. and Helander et al.](09-literature.md#stability-and-kinetic-theory) are useful sources; follow-up ion-driven modes demonstrate why this is not universal microstability.

Subsequent research targets:

1. Rigorous growth-rate bounds for a prescribed linear kinetic model including truncation errors.
2. A nonlinear free-energy estimate giving an absorbing bound or a finite-time bound under prescribed forcing.
3. A bound on time-averaged radial heat flux as a functional of free energy, with explicit averaging and initial-data dependence.
4. A useful coupling of orbit optimization, equilibrium, and turbulence suppression.

Do not equate linear microstability with a proved nonlinear turbulent transport law. A reactor can tolerate some turbulence if a sufficiently strong heat-loss bound is established.

**Status in PlasmaLean.** No gyrokinetic model is formalized. Two related pieces are compiled.

- **Available-energy kernel** (`Theory/Kinetic/AvailableEnergy`). The module proves nonnegativity, the exact zero set and monotonicity (`availableEnergyKernel_nonneg`, `availableEnergyKernel_eq_zero_iff_between`). It also corrects the source note: the kernel is *positive*, not zero, when the diamagnetic and precession frequencies have opposite signs (`availableEnergyKernel_pos_of_opposite_signs`). The Â bound itself is only stated (see the [microturbulence note](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/microturbulence-and-available-energy.md), N-20).
- **Max-J geometry** (N-1). The min-B side has a vacuum obstruction: ‖B‖² has no strict interior local maximum in a vacuum field (`VacuumField.not_strict_local_max_normSq`, `Theory/Fields/Subharmonic`). The finite-β curvature obstruction is open.

Under C5, anomalous (turbulent) transport is a **stated, supplied scaling** (ISS04 or an Â bound), never hidden. Research targets 1–4 above remain open research.

## Profile evolution and reactor power

For a simplified no-flow, prescribed-density model, use a radial volume label `r` with declared metric/area convention:

$$
\partial_t w_s+\frac1{V'(r)}\partial_r\!\left(V'(r)Q_s^r\right)=S_s,
\qquad w_s=\tfrac32 n_s\Theta_s.
$$

A phenomenological closure such as `Q_s^r=-n_sχ_s ∂_rΘ_s` needs a supplied interval law for `χ_s` and its regime. Add particle evolution, convection, interspecies exchange, and compression terms when moving beyond this restricted model. Prove conservation with boundary flux and comparison/positivity properties.

For distinct D and T species,

$$
R_{DT}=\int_\Omega n_Dn_T\langle\sigma v\rangle(T_i)\,dx.
$$

Use a verified enclosure of a sourced reactivity fit in its documented temperature domain, including the [Bosch–Hale corrigendum](09-literature.md#engineering-materials-and-experiment). A fit is empirical input, not a first-principles theorem. Track alpha deposition, escaping energetic particles, neutron power, radiation, conduction, auxiliary heating, cryogenics, and pumping.

Distinguish plasma gain `Q=P_fusion/P_aux` from net electrical output. Reactor feasibility requires the coupled thermal/power/tritium/component contracts in [07](07-materials-and-engineering.md).

**Status in PlasmaLean (C5).**

- **Kernel and comparison theory** (default build). The radial transport law lives in `Kernel/Transport`. Parabolic comparison for its quasilinear operator, for supplied classical solutions, is in `Theory/Transport/Comparison` (`first_crossing`, `lt_of_strictSubsolution`). Scalar barriers and invariant temperature windows for the 0-D power balance are in `Theory/Transport/PowerBalance` (`lower_barrier`, `upper_barrier`). There is also a discrete maximum principle for the radial scheme (`Certificates/DiscreteMaxPrinciple`). The kernel `PhysicalPlasma` now carries a quasi-neutral composition (`PhysicalPlasma.composition`; `Zeff_ge_one` is a theorem). This fixed audit finding F-1, which had admitted fuel fraction 1 with Z_eff = 2. No numeric result changed.
- **Bosch–Hale.** The reactivity enters as a supplied enclosure, the class `BoschHaleDT`, refined by `BoschHaleFine` (100 windows, `boschHaleFineWindows_length`). It is an empirical fit, as the paragraph above says. The model audit re-derived it against the source and found no discrepancy.
- **Solov'ev pressure budget.** `solovev_one_plasma_actual` (`Design/SolovevFluxGeometry`), with variants `solovev_one_plasma_highQ_actual` and `solovev_one_plasma_ignited_actual`. On the Solov'ev field, for **every supplied solution** of the radial transport model starting in a certified band, the core stays ≥ 10 keV for all time. The alpha conjunct is non-vacuous (`reactor_alpha_orbit_exists_label`). Corrected reading: this is "one field with a pressure-budget band", not "one consistent plasma". Existence of the transport solution is assumed (Q-10), and the pressure is bounded by a budget rather than equal to the force-balance pressure. Under the contract it is a **tokamak model** for C5, not a candidate.
- **Relative entropy (N-2).** The corrected 1-D identity is compiled in `Theory/Transport/RelativeEntropy`: pointwise (`relEnt_flux_identity`, `relEnt_pointwise_identity`, with the cross term and the source term) and integrated with explicit boundary terms (`RelEntSetup.integral_identity`). Dissipation bounds hold for a constant reference (`RelEntSetup.rate_le_neg_fisher_const_ref`) and a steady reference (`RelEntSetup.rate_le_neg_fisher_steady`). The identity without the cross term, as originally written, is false (`old_identity_false`). Coercivity is compiled too (`Theory/Transport/RelativeEntropyCoercive`: zero Fisher information forces T/T* constant, `RelEntSetup.relEnt_le_mul_fisher` with an endpoint condition that `no_coercivity_without_boundary` shows is necessary, and exponential decay `relEnt_exp_decay`). Open: the radial axis term; justifying dH/dt under the integral; and 2-D/3-D.
- **Burn window and Stellaris obstructions.** `m1_burn_window` is a 0-D window. `stellaris_window_steady` and `stellaris_window_loss` give windows on stellarator parameters with the ISS04 scaling supplied (`Design/BurnWindowStellarator`). At the measured renormalization factors burn is not accessible (`stellaris_measured_fren_no_access_steady`, `stellaris_measured_fren_no_access_loss`). Q-13 asks whether profile peaking removes this. Under C5 the question must be repeated with C2-derived neoclassical losses added (Q-22).
- **Transport barriers off the Solov'ev field.** Barriers also exist on cylinder and helical geometries (`helical_core_barrier`), with χ supplied. Barriers on a non-axisymmetric, C1-compatible geometry are Q-15.

**C5 on a stellarator candidate is essentially open.** It needs C2 bounds (Q-22), existence of the transport solution (Q-10) and a C1–C4 candidate.

## Theorem backlog

| ID | Target | Main dependency |
| --- | --- | --- |
| K1 | Full-orbit energy and uniform-field solution | ODE calculus |
| K2 | Reduced Hamiltonian and conserved quantities | Symplectic/Poisson formulation |
| K3 | Approximate-invariant finite-time confinement | Derivative bound and loss-boundary separation |
| K4 | Omnigeneity/action relation in a specified class; bounce-averaged drift and ε_eff for thermal ions and electrons (C2) | Bounce integrals and turning-point analysis; Q-21, Q-23 |
| K5 | Certified finite-time orbit bundle | ODE enclosures and geometry |
| K6 | Drift-kinetic conservation, solvability, and flux bounds | Collision operator and analytic estimates |
| K7 | Ambipolar root/current closure certificate | Root validation and coupled equilibrium |
| K8 | Source-specific maximum-`J` microstability | Gyrokinetic theorem extraction |
| K9 | Robust kinetic stability and heat-flux bounds | Major research target |
| K10 | Quantified reduced-to-full-orbit and kinetic-to-profile transfer | Major research target with finite-time alternatives |

The progress column is generated from `progress/status.json`; the status sections above give the reading of 30 October 2026. The contract priorities in this backlog are K4 (C2, the top priority for thermal particles) and the C5 inputs K6/K7, which feed Q-22 in their coarse, supplied-scaling form.
