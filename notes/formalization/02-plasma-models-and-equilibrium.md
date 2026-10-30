# Plasma models and equilibrium theory

Read [00-model-contracts.md](00-model-contracts.md) before using these specifications. References refer to [09-literature.md](09-literature.md). This chapter sets out the plasma models (ideal MHD, static equilibria, weak and stepped-pressure equilibria, extended and kinetic models) and the obligations a Lean statement about them must meet. The mathematical and physical exposition is the specification. Each section ends with a **Status in PlasmaLean** paragraph: what is compiled (declaration and module, default build or on demand), what is a supplied law or hypothesis, what is open (`Q-*` identifiers of the [research graph](../implementation-plan.md#research-graph-added-29-october-2026)) and what was corrected. The summary is in [Status in PlasmaLean](#status-in-plasmalean). Status as of 30 October 2026, against the [stellarator contract](../implementation-plan.md#the-stellarator-contract-30-october-2026), [progress report 15](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md) and the [kernel audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-kernel-audit.md).

"Default build" means imported by `PlasmaLean.lean` and covered by `scripts/check_axioms.lean` (standard axioms only).

## Contents

- [Role in the stellarator contract](#role-in-the-stellarator-contract)
- [State, scales, and units](#state-scales-and-units)
- [Ideal MHD](#ideal-mhd)
- [Static equilibria and boundary conditions](#static-equilibria-and-boundary-conditions)
- [Weak and stepped-pressure equilibria](#weak-and-stepped-pressure-equilibria)
- [Beyond ideal MHD](#beyond-ideal-mhd)
- [Kinetic reference and reduction contracts](#kinetic-reference-and-reduction-contracts)
- [Status in PlasmaLean](#status-in-plasmalean)
- [Theorem backlog](#theorem-backlog)

## Role in the stellarator contract

Equilibrium theory is clause **C4** (existence: nested surfaces and force balance `J × B = ∇p`, or `J = 0` in vacuum). It is constrained by **C1**: the net toroidal plasma current must vanish or be bootstrap-level, and ι ≥ ι_min > 0 must come from the external field. An equilibrium whose rotational transform comes from a large plasma current is tokamak-like under C1 however non-axisymmetric it is.

This reorders the exact equilibria in the library. The Solov'ev equilibrium is a **tokamak model**: axisymmetric, with a toroidal plasma current. It remains useful as a model for C5 and as a technique test bed. The Landreman families are smooth, non-axisymmetric, finite-β toroidal equilibria, but both carry net toroidal current (family 2 provably so). They are C3/C4 test beds, not candidates. The open target is a **current-free finite-β equilibrium** (Q-20), with stepped pressure across the certified KAM torus of the rational vacuum field (Q-14) as the lead route.

## State, scales, and units

Keep mass density `ρ`, number density `nₛ`, pressure `p`, temperature `Tₛ`, magnetic field `B`, current `J`, and fluid velocity `u` distinct. For a Maxwellian isotropic mixture use a specified equation of state

$$
p=\sum_s n_s k_BT_s,\qquad
\rho=\sum_s m_s n_s.
$$

If temperature is supplied as energy in keV, write `pₛ = nₛ Θₛ` with `Θₛ = k_B Tₛ` and perform the energy-to-joule conversion. Do not silently insert keV values into a kelvin formula.

Introduce reference scales `L₀, B₀, ρ₀` and derive the nondimensional equations. Track at least

$$
v_A=\frac{B_0}{\sqrt{\mu_0\rho_0}},\quad
\beta=\frac{2\mu_0p_0}{B_0^2},\quad
\epsilon_\rho=\frac{\rho_i}{L_0},\quad
\rho_i=\frac{\sqrt{2m_i\Theta_i}}{|q_i|B_0},
$$

and collision, resistive, thermal, orbit, and operating timescales. The thermal-speed convention is explicitly `v_th = √(2Θ/m)`. A model-validity interface should record the ordering parameters rather than treating “small” as a theorem.

For realistic case studies, import a documented experimental or reactor operating profile together with its geometry; use [W7-X transport data](09-literature.md#engineering-materials-and-experiment) or the [HELIAS engineering study](09-literature.md#engineering-materials-and-experiment) as entry points. Neither provides a universal minimum field, coil spacing, or material lifetime.

**Status in PlasmaLean.** The kernel is SI throughout. Temperatures in the transport and fusion kernels are energies in keV with explicit conversion (`Kernel/Fusion`, `Kernel/Transport`). The 0-D plasma state is `DTPlasma`/`PhysicalPlasma` in `Kernel/Fusion`. After audit finding F-1 (a kernel law change approved by the user), `PhysicalPlasma` carries the quasineutral composition law `QuasineutralComposition`, and `PhysicalPlasma.Zeff_ge_one`, `fuel_le_ions` and `ions_le_one` are now theorems. The exact equilibria have SI rescalings (`LandremanEquilibrium.force_balance_SI`, the family-2 `landreman2_force_balance_SI_gradient`, `helical_scaled_force_balance_gradient`). No general nondimensionalization or model-validity interface with ordering parameters exists yet.

## Ideal MHD

For a smooth isotropic adiabatic fluid without gravity, heating, or resistivity:

$$
\partial_t\rho+\nabla\cdot(\rho u)=0,
$$
$$
\rho(\partial_tu+u\cdot\nabla u)=-\nabla p+J\times B,
$$
$$
\partial_tB=\nabla\times(u\times B),\quad
\nabla\cdot B=0,\quad J=\mu_0^{-1}\nabla\times B,
$$
$$
(\partial_t+u\cdot\nabla)p+\Gamma p\,\nabla\cdot u=0,\qquad \Gamma>1.
$$

Equivalently, `D_t(pρ^{-Γ})=0` where `ρ>0`. Define solutions with a declared time interval, regularity, initial data, and boundary conditions. The source model [Freidberg, Ideal MHD](09-literature.md#stability-and-kinetic-theory) supplies the physical assumptions and variants.

First prove:

1. `div B` remains zero because `div curl=0`, in the chosen classical solution class.
2. Mass is conserved on a fixed impermeable boundary `u·n=0`.
3. For the appropriate closed conducting boundary, total energy
   $$
   E=\int_\Omega\left(\tfrac12\rho|u|^2+\frac{p}{\Gamma-1}
      +\frac{|B|^2}{2\mu_0}\right)dx
   $$
   is conserved; retain boundary fluxes in the general identity.
4. Smooth material magnetic flux is conserved under the ideal induction equation, with a proved flow map.
5. Positive initial density stays positive along a sufficiently regular flow for the existence interval.

Conservation identities alone do not establish global smooth existence or nonlinear stability in a strong norm.

**Status in PlasmaLean.** The time-dependent ideal-MHD system is not formalized, and the conservation identities 1–5 (E2) are open. What exists is algebraic or conditional: the Elsässer energy and cross-helicity identities with an *assumed* skew transport operator (`Theory/Stability/Elsasser`), and the conditional Riccati comparison `riccati_le_initial`, `riccati_exp_decay` (`Theory/Stability/RiccatiComparison`), whose differential inequality is a hypothesis, not proved for MHD (Q-9). Gates E2–E8 of the verified-evolution goal G-7 (Q-7, Q-8, Q-10, Q-11) are not started in Lean.

## Static equilibria and boundary conditions

For `u=0`, isotropic static equilibrium means

$$
J\times B=\nabla p,\qquad
\nabla\cdot B=0,\qquad
\nabla\times B=\mu_0J.
$$

Specify whether profiles, total currents, fluxes, helicity, or boundary shape are prescribed. Density is not determined by force balance alone; it enters stability through inertia and the operating model.

Under C1 the **net toroidal current** is a prescribed quantity, not an output: the current through a poloidal cross-section,

$$
I_{\rm tor}=\int_{S}J\cdot dS ,
$$

must satisfy ‖I_tor‖ ≤ I_max (bootstrap level; zero in vacuum). This is the first test to apply to any candidate equilibrium.

**Fixed boundary.** Require an appropriate magnetic boundary, often `B·n=0`. Initially analyze perturbations with zero boundary trace; later extend to the chosen conducting-wall condition.

**Free plasma–vacuum interface.** Include a vacuum region, its magnetic field, and coil/external wall boundary data. For an ideal magnetic interface `B·n=0` on both sides with no additional imposed traction, require continuity of total pressure:

$$
\left[p+\frac{|B|^2}{2\mu_0}\right]=0.
$$

Use normal-field continuity, tangential jump/current conditions, and the full stress formulation for more general interfaces. An equilibrium computed with a fixed plasma boundary does not supply a free-boundary stability certificate.

**Vacuum.** `J=0` gives `curl B=0`, in addition to `div B=0`. On a simply connected region with sufficient regularity, a scalar-potential theorem gives `B=∇Φ` and `ΔΦ=0`. On a toroidal region retain harmonic/circulation components.

**Force-free.** Constant pressure permits `J∥B` where `B≠0`. A useful exact counterexample to “zero pressure implies vacuum” uses `B₀,L₀>0` on a Cartesian domain periodic in `z` with period `2πL₀`:

$$
B=B_0(\cos(z/L_0),\sin(z/L_0),0),\quad
\nabla\times B=-B/L_0,\quad
J=-B/(\mu_0L_0),\quad p=0.
$$

This model has nonzero current and zero Lorentz force, with explicit field and length scales preserving SI dimensions. It is a kernel sanity witness, not a stellarator reactor.

**Axisymmetry.** With cylindrical coordinates and a selected poloidal flux convention,

$$
B=\frac1R\nabla\psi\times e_\phi+\frac{F(\psi)}R e_\phi,\quad p=p(\psi),
$$
$$
\Delta^*\psi=-\mu_0R^2p'(\psi)-F(\psi)F'(\psi),\qquad
\Delta^*=R\partial_R(R^{-1}\partial_R)+\partial_Z^2.
$$

Prove this reduction on `R>0` and track the sign/flux convention. Use it for verified manufactured equilibria and a simpler PDE existence milestone. Axisymmetric equilibria are tokamak models: a current-free axisymmetric field has ι = 0, so their confinement rests on plasma current, which C1 excludes. They provide infrastructure and sanity checks; the target is a current-free three-dimensional equilibrium.

**Status in PlasmaLean.**

- *Kernel laws* (default build). `ForceBalance B J g` (`J × B = g`, pointwise, `Kernel/Equilibrium`) with `field_tangency`, `current_tangency` and `gradient_zero_iff_force_free`; `StaticSlab` (`Kernel/Slab`) for `z`-dependent slab fields; `VacuumField` (`Kernel/Vacuum`). The strict kernel audit (all 52 kernel declarations, audited commit `cda8bd0`) found no critical issue. Its finding E-1 is that `ForceBalance B J (J × B)` holds for every `B, J` (`forceBalance_of_cross`), so a force-balance claim has content only when `g` is the gradient of a pressure.
- *E-1 fix* (default build, `Design/ForceBalanceGradient`). Every exact equilibrium is restated with `g` written as Mathlib's `gradient` of the explicit pressure and `J = (∇ × B)/μ₀` the actual Ampère current: `solovev_force_balance_gradient`, `solovev_reactor_force_balance_gradient`, `helical_force_balance_gradient`, `helical_scaled_force_balance_gradient`, `landreman1_force_balance_gradient`, `landreman1_force_balance_SI_gradient`, `landreman2_force_balance_gradient`, `landreman2_force_balance_SI_gradient` and `family2_lam200_force_balance_gradient`. All 14 force-balance users now tie the force to a real pressure gradient.
- *Force-free.* `force_free_nonvacuum` (`Sanity/Equilibrium`) is the algebraic witness `J ∥ B ≠ 0` with zero gradient. The periodic Beltrami example above is not compiled.
- *Solov'ev: a tokamak model* (default build, `Design/Solovev`). An exact finite-pressure axisymmetric equilibrium (`force_balance`, `field_divergence_free`, `field_flux_tangent`) with a purely toroidal plasma current (`field_curl`), and an ITER-like instance with β_axis ≈ 2.9 %. The `Δ*ψ = 3R²` reduction is checked by the force balance directly; general Grad–Shafranov equivalence (E3) is not formalized. The coupled result `solovev_one_plasma_actual` (`Design/SolovevFluxGeometry`) is **one field with a pressure-budget band**: for every *supplied* solution of the radial transport model starting in a certified band, the core stays ≥ 10 keV, with the pressure bounded by a budget, not equal to the force-balance pressure. Existence of the transport solution is assumed (Q-10). Under the contract this is a C5 model on a tokamak, not a candidate.
- *Helical equilibrium* (default build, `Design/HelicalEquilibrium`). An exact helically symmetric finite-pressure equilibrium solving the helical Grad–Shafranov (JFKO) equation (`force_balance`, `field_not_axisymmetric`; flux surfaces from `HelicalDivergence.field_firstIntegral`). It is a straight, infinite-aspect-ratio model of quasi-helical symmetry: toroidal curvature is absent, there are no coils, and it carries plasma current.
- *Landreman family 1* (default build, `Design/LandremanEquilibrium`, `Design/LandremanGradCounterexample`). A smooth non-axisymmetric toroidal equilibrium (Landreman, arXiv:2609.26742 v2, unrefereed; every identity re-proved) with `force_balance`, `psi_firstIntegral`, `pressure_pos`, and closed field lines (`fieldLine_closed`, ι ≡ 2). `family1_grad_counterexample` packages it as a counterexample to Grad's conjecture: smooth `B, J, p` on a toroidal domain, nested level sets homeomorphic to `Circle × Circle`, non-constant pressure, and no rotation, translation or screw-motion symmetry (`killing_trivial_of_axis`). Plane reflections are not covered. Under the contract this is **mathematical infrastructure**, not design progress (Q-17).
- *Landreman family 2* (default build, `Design/LandremanFamily2` and modules). The sheared family (`force_balance`, `family2_shear`, `fieldLine_confined`). The net toroidal current is computed: `torCurrent_eq` gives μ₀ I_tor(k₀)/2π = `curK`, an integral whose integrand is positive by `F1_pos` and `Eint_pos`. So **I_tor > 0 for 0 < k₀ < 19/20, and family 2 fails C1** unless that current is shown to be bootstrap-level. The positivity corollary and its ratio to the external current are not yet named declarations (Q-18). For family 1 the current has not been computed.
- *Validated slab equilibrium* (default build, `Design/ValidatedSlabEquilibrium`). A non-polynomial (Liouville–Bratu) slab Grad–Shafranov solution validated by a radii-polynomial argument in `ℓ¹(ℤ)`. This is the E5 pattern on a one-dimensional PDE.
- *Screw pinch.* `RadialBalance` (`Theory/Equilibrium/ScrewPinch`) is the cylindrical radial force balance used by the stability chapter. It is a current-carrying model problem.
- *Open.* Free-boundary equilibria (E7), scalar-potential theorems on toroidal domains, and a Lean predicate for net toroidal current through a cross-section of a general toroidal domain (Q-21, specified as `CurrentFreeTransform` in [00-model-contracts](00-model-contracts.md)).

## Weak and stepped-pressure equilibria

Define the static stress

$$
\mathsf S=\left(p+\frac{|B|^2}{2\mu_0}\right)\mathsf I
          -\frac{B\otimes B}{\mu_0}.
$$

For smooth divergence-free fields, `div S=0` is equivalent to force balance. For piecewise smooth fields formulate `div S=0` distributionally, `div B=0` distributionally, and the resulting interface jumps. This prevents multiplication of undefined distributional currents by discontinuous fields without a specified interpretation.

For a multi-region relaxed-MHD model:

- decompose the toroidal domain into regions separated by magnetic interfaces;
- use constant pressure within each relaxed region;
- impose `curl B = λᵢ B` within each region;
- impose interface force balance, flux and helicity/current constraints;
- permit islands and chaotic field lines within the regions.

The [SPEC/MRxMHD paper](09-literature.md#geometry-equilibrium-and-symmetry) supplies a candidate-generating formulation. Prove the appropriate existence and stability statements for that model; do not silently transfer them to smooth continuously nested ideal-MHD equilibrium.

Under C1 the interface sheet currents matter: a stepped-pressure equilibrium carries surface currents, and their **net toroidal part** must be bounded for the result to count as current-free.

[Enciso–Luque–Peralta-Salas](09-literature.md#geometry-equilibrium-and-symmetry) prove piecewise smooth nonconstant-pressure equilibria under nondegenerate toroidal-domain hypotheses. Extract their actual theorem, including the Beltrami/KAM assumptions. This is a substantial existing theorem to formalize, rather than an assertion that all nonaxisymmetric equilibria are unknown.

Smooth nonaxisymmetric equilibrium with a nonconstant pressure profile and a complete prescribed surface foliation raises small-divisor and resonance questions. VMEC/DESC representations impose nested surfaces; a converged finite representation alone is not an existence proof for a classical continuum solution. Research should target a specified class with constructive constants, allow weaker/stepped-pressure alternatives where appropriate, and account for obstructions. [Constantin–Drivas–Ginsberg](09-literature.md#geometry-equilibrium-and-symmetry) construct equilibria with a small additional force; that force must remain in their conclusion. Explicit smooth non-axisymmetric solutions do exist (Landreman 2026, Gómez-Serrano–Liehr–Taylor 2026, Issan et al. 2026, all preprints); the open question for a stellarator is one that is also current-free.

**Status in PlasmaLean.** No distributional stress, interface jump condition or relaxed-MHD model is formalized (E4, E6 piecewise part). The smooth explicit Landreman families stand in for E6 as sourced non-axisymmetric existence results, but both carry net current. **Stepped pressure across the exact KAM torus of the rational vacuum field (Q-14)** is the lead route to a current-free finite-β equilibrium (**Q-20**). It is a plan only (notes [after-kam](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/after-kam.md) §3 and [finite-beta-stellarator](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/finite-beta-stellarator.md)). The alternative route is a finite-β equilibrium near a Dommaschk QA vacuum field (Q-16). The non-stellarator-symmetric τ-extension of Issan–Citrin–Landreman–Tracey (arXiv:2610.07304) is open.

## Beyond ideal MHD

Keep separate interfaces for:

- resistive Ohm law `E+u×B=η_e J`, where `η_e` is electrical resistivity, and induction with magnetic diffusivity `η_e/μ₀`;
- generalized Ohm law with Hall, electron-pressure, and inertia terms;
- anisotropic stress `P=p_⊥ I+(p_∥-p_⊥)bb`, `b=B/|B|`;
- viscosity, heat conduction, sources, and losses;
- equilibrium flows and resistive walls.

In an isothermal/constant-resistivity incompressible toy model with closed boundaries, magnetic plus kinetic energy decreases through resistive and viscous dissipation. In a thermodynamically closed resistive model, Joule heating transfers electromagnetic energy into internal energy rather than destroying total energy. State which balance is being proved.

Static no-flow self-adjoint MHD stability machinery does not automatically apply to a flowing equilibrium or a dissipative nonself-adjoint operator.

**Status in PlasmaLean.** None of these interfaces is formalized. The only non-ideal content is flux-surface-averaged heat transport (`Kernel/Transport`, with supplied solutions) and the 1-D relative-entropy identity (`Theory/Transport/RelativeEntropy`), both covered in [chapter 04](04-particles-and-transport.md). The ideal–resistive comparison (E9) is research.

## Kinetic reference and reduction contracts

A multispecies nonrelativistic kinetic model is

$$
\partial_tf_s+v\cdot\nabla_xf_s
+\frac{q_s}{m_s}(E+v\times B)\cdot\nabla_vf_s
=C_s(f)+S_s,
$$

with Maxwell equations and explicitly chosen collision/source operators. Specify decay or velocity boundaries so that moments and integration by parts are legitimate. Define `ρ_c=Σqₛ∫fₛdv` and `J=Σqₛ∫vfₛdv`.

Prove moment identities under collision conservation hypotheses. Closure of the pressure tensor and heat flux is an additional assumption or reduction theorem, not a consequence of taking moments alone.

A useful reduction contract has the form

$$
\|{\cal O}(z_{\rm full}(t))-{\cal O}(z_{\rm reduced}(t))\|
\le \varepsilon_{\rm model}(t)
$$

for specified initial data, observables, parameters, and times. Plasma stability in a reduced model transfers only through such a contract and a sufficient robustness margin. Proving useful kinetic-to-fluid and orbit-reduction error bounds is part of the ambitious roadmap.

**Status in PlasmaLean.** The Vlasov–Maxwell system and moment identities are not formalized. Single-particle dynamics is: Newton–Lorentz orbits (`Kinetic.LorentzOrbit`) exist for all time in a `C¹` field under a compact a-priori bound (`ODEGlobal.exists_global_of_apriori`, `Kinetic.lorentzOrbit_exists`). The Littlejohn and Boozer guiding-centre models are **supplied** reductions, audited against their sources in the [model audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md), with no derivation from the Lorentz force. A crude finite-time full-orbit versus guiding-centre bound exists. Details are in [chapter 04](04-particles-and-transport.md).

## Status in PlasmaLean

Summary (30 October 2026). All named declarations are in the default build.

| Topic | Compiled (declarations, module) | Supplied law or hypothesis | Contract role and open items |
| --- | --- | --- | --- |
| Kernel laws | `ForceBalance`, `field_tangency`, `current_tangency` (`Kernel/Equilibrium`); `StaticSlab`; `VacuumField` | all three are kernel laws, audited (`cda8bd0`) | E-1: `g` must be ∇p, fixed by `Design/ForceBalanceGradient` |
| Solov'ev | `Solovev.force_balance`, `solovev_force_balance_gradient`, `solovev_one_plasma_actual` | transport solution supplied; pressure bounded by a budget | tokamak model (C5 model, test bed); Q-10 |
| Helical | `HelicalEquilibrium.force_balance`, `helical_force_balance_gradient` | straight helical model, no toroidal curvature | test bed |
| Landreman family 1 | `landreman1_force_balance_gradient`, `family1_grad_counterexample`, `fieldLine_closed` | unrefereed source, every identity re-proved | infrastructure (Q-17); ι ≡ 2; I_tor not computed (Q-18) |
| Landreman family 2 | `landreman2_force_balance_gradient`, `family2_shear`, `torCurrent_eq`, `F1_pos`, `Eint_pos` | same | I_tor > 0: fails C1; positivity corollary not named (Q-18) |
| Validated slab | `Design/ValidatedSlabEquilibrium` (radii polynomial) | none | E5 pattern in 1-D |
| Screw pinch | `RadialBalance` | current-carrying model | stability test bed (see [chapter 03](03-mhd-stability.md)) |
| Current-free finite β | none | none | Q-20, lead route Q-14 (stepped pressure); C1 predicate Q-21 |
| Time-dependent MHD, weak equilibria, kinetic moments | `riccati_le_initial` (conditional) | Riccati inequality is a hypothesis | E2, E4, E9; Q-7–Q-11 |

**Against the contract.** C4 holds at finite β only for the symmetric models and for the Landreman families, which fail or probably fail C1. In vacuum it holds for the rational stellarator field inside one certified torus (see [chapter 01](01-geometry-and-fields.md#field-line-dynamics)). No current-free finite-β equilibrium exists in Lean.

## Theorem backlog

| ID | Target | Dependency / status |
| --- | --- | --- |
| E1 | Force balance implies tangency; force-free/vacuum distinction | Elementary existing theory; exact equilibria restated with the actual ∇p |
| E2 | MHD conservation identities on smooth closed domains | Calculus, divergence theorem, ODE flow |
| E3 | Grad–Shafranov equivalence and explicit examples | Cylindrical calculus; Solov'ev is a tokamak model |
| E4 | Distributional stress and magnetic interface jump conditions | Weak derivatives and traces; needed for Q-14 |
| E5 | Validated equilibrium in a specified simpler PDE class | Contraction/inverse bounds, [05](05-verified-numerics.md) |
| E6 | Formalize a sourced piecewise smooth nonaxisymmetric existence theorem | Beltrami fields, KAM, analytic estimates |
| E7 | Certified finite-pressure free-boundary equilibrium for external coils | Coupled interior/vacuum fields and interface |
| E8 | Constructive smooth/weak equilibrium branches over useful uncertainty sets | Research target with specified admissible class; must be current-free (C1) |
| E9 | Quantified kinetic/fluid or resistive/ideal model comparison | Research target; singular limits and time horizon |
