# Particle confinement, kinetic stability, and transport

Ideal-MHD stability addresses large-scale fluid perturbations. This parallel development addresses orbit loss, bootstrap current, neoclassical heat loss, and microinstabilities. References and source caveats are in [09-literature.md](09-literature.md).

## Contents

- [Full-orbit dynamics](#full-orbit-dynamics)
- [Guiding-centre dynamics](#guiding-centre-dynamics)
- [Symmetry, omnigeneity, and finite-time bounds](#symmetry-omnigeneity-and-finite-time-bounds)
- [Drift-kinetic transport](#drift-kinetic-transport)
- [Gyrokinetic stability and turbulence](#gyrokinetic-stability-and-turbulence)
- [Profile evolution and reactor power](#profile-evolution-and-reactor-power)
- [Theorem backlog](#theorem-backlog)

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

## Theorem backlog

| ID | Target | Main dependency |
| --- | --- | --- |
| K1 | Full-orbit energy and uniform-field solution | ODE calculus |
| K2 | Reduced Hamiltonian and conserved quantities | Symplectic/Poisson formulation |
| K3 | Approximate-invariant finite-time confinement | Derivative bound and loss-boundary separation |
| K4 | Omnigeneity/action relation in a specified class | Bounce integrals and turning-point analysis |
| K5 | Certified finite-time orbit bundle | ODE enclosures and geometry |
| K6 | Drift-kinetic conservation, solvability, and flux bounds | Collision operator and analytic estimates |
| K7 | Ambipolar root/current closure certificate | Root validation and coupled equilibrium |
| K8 | Source-specific maximum-`J` microstability | Gyrokinetic theorem extraction |
| K9 | Robust kinetic stability and heat-flux bounds | Major research target |
| K10 | Quantified reduced-to-full-orbit and kinetic-to-profile transfer | Major research target with finite-time alternatives |
