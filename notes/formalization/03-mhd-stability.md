# Ideal-MHD stability: from energy identities to useful certificates

This note separates directly derived algebraic identities, established source theory to formalize, and new research targets. Read [00](00-model-contracts.md), [02](02-plasma-models-and-equilibrium.md), and the stability entries in [09](09-literature.md#stability-and-kinetic-theory).

## Contents

- [Start with an abstract energy theorem](#start-with-an-abstract-energy-theorem)
- [The continuum MHD bridge](#the-continuum-mhd-bridge)
- [Elementary sufficient bounds](#elementary-sufficient-bounds)
- [Neutral modes and continuous spectrum](#neutral-modes-and-continuous-spectrum)
- [Free boundaries and local criteria](#free-boundaries-and-local-criteria)
- [Discretization and nonlinear targets](#discretization-and-nonlinear-targets)
- [Theorem backlog](#theorem-backlog)

## Start with an abstract energy theorem

Let `H` be a real Hilbert space and `V` a real normed displacement space continuously embedded in `H`. Let `m:H×H→ℝ` be a continuous, symmetric, time-independent positive bilinear inertia form, and `a:V×V→ℝ` a continuous, symmetric, time-independent bilinear potential-energy form. On a connected time interval containing `0`, take `ξ∈C¹(I,V)` whose embedded curve is `C²(I,H)`. Thus `ξ̇∈V` is an admissible test vector. For a solution of

$$
m(\ddot\xi,\eta)+a(\xi,\eta)=0\qquad(\eta\in V),
$$

prove

$$
\frac{d}{dt}\left[\tfrac12m(\dot\xi,\dot\xi)
                  +\tfrac12a(\xi,\xi)\right]=0.
$$

If `m(v,v) ≥ m₀ ‖v‖²_H` and `a(ξ,ξ) ≥ c ‖ξ‖²_V` with positive constants, then

$$
\|\dot\xi(t)\|_H^2\le 2E(0)/m_0,\qquad
\|\xi(t)\|_V^2\le 2E(0)/c.
$$

State this conditional on existence and regularity first; prove evolution well-posedness separately. This theorem can be formalized before any continuum MHD PDE.

For a self-adjoint realization `A` of the form with inertia normalized to the Hilbert inner product, distinguish:

- `a≥0` and no negative spectral part;
- absence of exponentially growing modes;
- uniform boundedness in a specified norm;
- a positive spectral gap/coercivity;
- decay or asymptotic stability.

They are different conclusions. A conservative positive system oscillates; energy conservation alone gives no decay.

## The continuum MHD bridge

Choose a static isotropic equilibrium `(ρ,p,B,J)` with `ρ ≥ ρ_* >0`, `μ₀>0`, and `Γ>1`. Start with a bounded smooth fixed domain and displacements of zero boundary trace, so the boundary terms can be handled explicitly.

The Eulerian perturbations are

$$
\delta B=Q=\nabla\times(\xi\times B),\quad
\delta\rho=-\nabla\cdot(\rho\xi),\quad
\delta p=-\xi\cdot\nabla p-\Gamma p\,\nabla\cdot\xi.
$$

The no-flow linearized force is

$$
F\xi=\frac{(\nabla\times Q)\times B}{\mu_0}
      +J\times Q
      +\nabla\!\left(\xi\cdot\nabla p+\Gamma p\,\nabla\cdot\xi\right),
\qquad \rho\ddot\xi=F\xi.
$$

Derive rather than postulate these expressions from the selected MHD model. Define

$$
q(\xi)=-\int_\Omega \xi\cdot F\xi\,dx,\qquad
\delta W(\xi)=\tfrac12 q(\xi).
$$

Integration by parts under the stated boundary conditions gives

$$
q(\xi)=\int_\Omega\left[
\frac{|Q|^2}{\mu_0}
-\xi\cdot(J\times Q)
+\Gamma p\,(\nabla\cdot\xi)^2
+(\xi\cdot\nabla p)\nabla\cdot\xi
\right]dx.
$$

Prove symmetry of the polarized form using equilibrium and boundary conditions. Symmetry of a formal differential expression is not already a self-adjoint operator theorem: specify the closed form/domain, density, and analytic realization before invoking spectral theory.

The abstract theorem then applies with `m(v,v)=∫ρ|v|²` and `a` the polarization of `q`. The [Bernstein–Frieman–Kruskal–Kulsrud energy principle](09-literature.md#stability-and-kinetic-theory) is the historical source; [Freidberg](09-literature.md#stability-and-kinetic-theory) gives the broader model context.

### Sign sanity check

For `ξ(t)=e^{λt}ξ₀`, the equation is `Fξ₀=λ²ρξ₀`. Multiplication by `ξ₀` gives

$$
q(\xi_0)=-\lambda^2\int_\Omega\rho|\xi_0|^2dx.
$$

Thus positive `q` corresponds to oscillatory time dependence. Equivalently define the positive stability operator `A=-ρ^{-1}F` and write `Aξ₀=ω²ξ₀`. Do not label positive eigenvalues of `F` as stable.

## Elementary sufficient bounds

Let `p≥p_*>0`, `J_∞=‖J‖_∞`, `P_∞=‖∇p‖_∞`. Put `d=div ξ`. Two applications of Young's inequality yield

$$
q(\xi)\ge
\frac{1}{2\mu_0}\|Q\|_2^2
+\frac{\Gamma p_*}{2}\|d\|_2^2
-C_{\rm drive}\|\xi\|_2^2,
$$
$$
C_{\rm drive}=
\frac{\mu_0J_\infty^2}{2}
+\frac{P_\infty^2}{2\Gamma p_*}.
$$

This is a concrete early theorem. If a separate geometry theorem establishes, on the chosen admissible quotient,

$$
\frac{1}{2\mu_0}\|Q\|_2^2
+\frac{\Gamma p_*}{2}\|d\|_2^2
\ge C_{\rm geom}\|\xi\|_2^2,
$$

then `C_geom > C_drive` supplies an `L²` coercivity margin. The missing geometry inequality is the central difficulty, and may be false for the full displacement space. Do not insert it as an unnamed universal law.

More useful bounds may exploit parallel/perpendicular decomposition, field-line derivatives, pressure/curvature cancellation, square completion, or a stable reference form:

$$
q=q_{\rm ref}+r,\quad
q_{\rm ref}\ge c_{\rm ref}\|\xi\|_V^2,\quad
|r|\le c_{\rm err}\|\xi\|_V^2.
$$

Then `c_ref > c_err` certifies stability in that norm. State which norm controls the physical perturbation and prove the necessary comparison. Seeking sharp geometry-sensitive versions of these estimates is a useful AI theory-discovery task.

## Neutral modes and continuous spectrum

For a uniform nonzero field, constant pressure, and constant positive density on a periodic domain, put `b₀=B/|B|` and choose a nonzero constant speed `v₀`. The displacement `ξ(t)=t v₀b₀` has `Q=0` and `div ξ=0`. It solves the linearized equation and grows as a displacement, while the Eulerian magnetic/density/pressure perturbations vanish and the velocity is constant. This example uses periodic boundary conditions rather than the zero-trace fixed boundary above; nonconstant density would additionally require `B·∇ρ=0` for the density perturbation to vanish.

This exact example shows why nonnegative `q` does not imply bounded displacement in every norm. Clarify whether the theorem controls physical Eulerian observables, a quotient by relabelings, or the full Lagrangian displacement.

On quasiperiodic field lines, small denominators can destroy a simple Poincaré inequality for the field-aligned derivative in a strong isotropic norm. Ideal MHD can have Alfvén/slow continua and singular modes; do not assume a compact resolvent, uniform ellipticity, or a discrete complete eigenbasis merely to use finite-element spectral machinery.

Develop a correct energy space and a justified closed operator realization. Alternatives to a positive gap include:

- nonnegative form plus a characterization of its kernel;
- coercivity on a symmetry-reduced subspace;
- control of an observable rather than every derivative;
- finite-time bounds for the relevant initial class;
- a rigorous negative-energy test displacement demonstrating failure of a proposed stability condition.

## Free boundaries and local criteria

For a moving plasma–vacuum interface, the potential energy contains

$$
\delta W=\delta W_{\rm plasma}+\delta W_{\rm interface}
          +\delta W_{\rm vacuum},
\qquad
\delta W_{\rm vacuum}
=\frac1{2\mu_0}\int_{\Omega_v}|\delta B_v|^2dx,
$$

with the appropriate vacuum constraints, interface displacement, pressure jump derivatives, and outer wall conditions. Extract and formalize the interface term from the chosen source; it cannot be dropped because the vacuum term is nonnegative.

A resistive wall and plasma flow require their own dynamical analysis. A fixed perfectly conducting wall changes the perturbation class and can change stability.

Formalize Mercier/Suydam/ballooning results as separate local or asymptotic theorems with precise hypotheses and sign conventions. A magnetic well is one ingredient, not an all-mode sufficient criterion. A rational-surface current singularity requires its actual compatibility analysis; do not assume every such singularity produces a negative Mercier discriminant.

Use local criteria to eliminate candidates and sharpen global estimates. Use the full energy/operator theorem for any advertised global ideal-MHD conclusion.

## Discretization and nonlinear targets

For `V_N ⊂ V`,

$$
\inf_{\xi\in V\setminus\{0\}}\frac{q(\xi)}{m(\xi,\xi)}
\le
\inf_{\xi\in V_N\setminus\{0\}}\frac{q(\xi)}{m(\xi,\xi)}.
$$

A positive trial-space minimum is therefore insufficient. A rigorously evaluated admissible negative test direction, however, establishes a negative form value. Turning that into dynamical instability needs the appropriate energy-principle/operator hypotheses.

[05-verified-numerics.md](05-verified-numerics.md) gives a retained/tail block criterion and error budget. Prove it for the correct MHD space; a high-mode elliptic tail estimate may not be available.

For nonlinear stability, specify dynamically accessible perturbations or a constrained energy/Casimir construction. If a proved conserved functional `ℰ` satisfies, for a distance `d` to the equilibrium orbit,

$$
c_- d(z,z_*)^2\le \mathcal E(z)-\mathcal E(z_*)
\le c_+ d(z,z_*)^2
$$

on an admissible neighborhood of radius `r`, with `0<c_-≤c_+`, conservation and continuity give an energy barrier. Initial distance less than `r√(c_-/c_+)` cannot reach the neighborhood boundary while the solution exists continuously in this class; within it, `d(t)≤√(c_+/c_-)d(0)`. Prove continuation/global existence separately if claiming an all-time theorem. A positive Hessian without a remainder bound, constraint treatment, and norm control does not supply this conclusion. See [Morrison–Greene](09-literature.md#stability-and-kinetic-theory) for the Hamiltonian starting point, not a ready-made stellarator stability theorem.

## Theorem backlog

| ID | Target | Main missing ingredient |
| --- | --- | --- |
| S1 | Abstract energy conservation and coercivity bound | Hilbert-space differentiation |
| S2 | Linearized MHD identities and fixed-boundary energy | Calculus and justified integration |
| S3 | Young-inequality drive bound above | Exact norm inequalities |
| S4 | Neutral-mode counterexample and quotient definition | Admissible-space characterization |
| S5 | Self-adjoint realization and precise energy principle | Closed forms, domains, spectral/evolution theory |
| S6 | Source-specific local stability criteria | Exact hypotheses and normalization |
| S7 | All-mode certified bound for a restricted useful configuration | Tail/coupling analysis; potentially research |
| S8 | Free-boundary certificate with coils/vacuum/wall | Interface operator and trace bounds |
| S9 | Nonlinear orbital stability with quantitative basin | Conservation, constraints, remainders, continuation |
| S10 | Finite-beta robust stability for a constructible 3-D family | Major research target; may require a weaker stability notion |
