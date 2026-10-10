# Plasma models and equilibrium theory

Read [00-model-contracts.md](00-model-contracts.md) before using these specifications. References refer to [09-literature.md](09-literature.md). All proposed Lean declarations and solver bridges remain to be implemented.

## Contents

- [State, scales, and units](#state-scales-and-units)
- [Ideal MHD](#ideal-mhd)
- [Static equilibria and boundary conditions](#static-equilibria-and-boundary-conditions)
- [Weak and stepped-pressure equilibria](#weak-and-stepped-pressure-equilibria)
- [Beyond ideal MHD](#beyond-ideal-mhd)
- [Kinetic reference and reduction contracts](#kinetic-reference-and-reduction-contracts)
- [Theorem backlog](#theorem-backlog)

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

## Static equilibria and boundary conditions

For `u=0`, isotropic static equilibrium means

$$
J\times B=\nabla p,\qquad
\nabla\cdot B=0,\qquad
\nabla\times B=\mu_0J.
$$

Specify whether profiles, total currents, fluxes, helicity, or boundary shape are prescribed. Density is not determined by force balance alone; it enters stability through inertia and the operating model.

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

Prove this reduction on `R>0` and track the sign/flux convention. Use it for verified manufactured equilibria and a simpler PDE existence milestone. Axisymmetric examples provide infrastructure and sanity checks, while the practical target remains a three-dimensional stellarator.

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

[Enciso–Luque–Peralta-Salas](09-literature.md#geometry-equilibrium-and-symmetry) prove piecewise smooth nonconstant-pressure equilibria under nondegenerate toroidal-domain hypotheses. Extract their actual theorem, including the Beltrami/KAM assumptions. This is a substantial existing theorem to formalize, rather than an assertion that all nonaxisymmetric equilibria are unknown.

Smooth nonaxisymmetric equilibrium with a nonconstant pressure profile and a complete prescribed surface foliation raises small-divisor and resonance questions. VMEC/DESC representations impose nested surfaces; a converged finite representation alone is not an existence proof for a classical continuum solution. Research should target a specified class with constructive constants, allow weaker/stepped-pressure alternatives where appropriate, and account for obstructions. [Constantin–Drivas–Ginsberg](09-literature.md#geometry-equilibrium-and-symmetry) construct equilibria with a small additional force; that force must remain in their conclusion.

## Beyond ideal MHD

Keep separate interfaces for:

- resistive Ohm law `E+u×B=η_e J`, where `η_e` is electrical resistivity, and induction with magnetic diffusivity `η_e/μ₀`;
- generalized Ohm law with Hall, electron-pressure, and inertia terms;
- anisotropic stress `P=p_⊥ I+(p_∥-p_⊥)bb`, `b=B/|B|`;
- viscosity, heat conduction, sources, and losses;
- equilibrium flows and resistive walls.

In an isothermal/constant-resistivity incompressible toy model with closed boundaries, magnetic plus kinetic energy decreases through resistive and viscous dissipation. In a thermodynamically closed resistive model, Joule heating transfers electromagnetic energy into internal energy rather than destroying total energy. State which balance is being proved.

Static no-flow self-adjoint MHD stability machinery does not automatically apply to a flowing equilibrium or a dissipative nonself-adjoint operator.

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

## Theorem backlog

| ID | Target | Dependency / status |
| --- | --- | --- |
| E1 | Force balance implies tangency; force-free/vacuum distinction | Elementary existing theory |
| E2 | MHD conservation identities on smooth closed domains | Calculus, divergence theorem, ODE flow |
| E3 | Grad–Shafranov equivalence and explicit examples | Cylindrical calculus |
| E4 | Distributional stress and magnetic interface jump conditions | Weak derivatives and traces |
| E5 | Validated equilibrium in a specified simpler PDE class | Contraction/inverse bounds, [05](05-verified-numerics.md) |
| E6 | Formalize a sourced piecewise smooth nonaxisymmetric existence theorem | Beltrami fields, KAM, analytic estimates |
| E7 | Certified finite-pressure free-boundary equilibrium for external coils | Coupled interior/vacuum fields and interface |
| E8 | Constructive smooth/weak equilibrium branches over useful uncertainty sets | Research target with specified admissible class |
| E9 | Quantified kinetic/fluid or resistive/ideal model comparison | Research target; singular limits and time horizon |
