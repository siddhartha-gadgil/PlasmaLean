# A Formal Lean 4 Framework for the Geometry, Dynamics, and Design of Stellarators

## Introduction: The Mathematical Imperative for Stellarator Verification

The pursuit of controlled thermonuclear fusion represents one of the most formidable scientific and engineering challenges of the modern era. At the heart of magnetic confinement fusion is the requirement to trap a high-temperature plasma—a highly conductive fluid of ions and electrons—within a finite volume using intense magnetic fields. Among the leading paradigms for achieving this is the stellarator. Conceived in the 1950s by Lyman Spitzer, the stellarator distinguishes itself from the axisymmetric tokamak by relying entirely on external, non-planar modular coils to generate the complex, three-dimensional magnetic field geometry necessary for plasma confinement. Because stellarators do not rely on a continuous internal plasma current to generate their poloidal magnetic field, they are theoretically immune to current-driven disruptions, rendering them exceptionally well-suited for steady-state fusion reactors. However, the absence of continuous spatial symmetry in a generic stellarator introduces profound physical and mathematical complications. In an axisymmetric device like a tokamak, Noether's theorem guarantees the conservation of canonical toroidal angular momentum, which strictly bounds the radial excursions of particle drift orbits. In a generic 3 D stellarator, this conservation law is broken, leading to unacceptably high levels of neoclassical transport and the rapid loss of fusion-born alpha particles. To mitigate this, modern stellarator design is predicated on the concept of "quasisymmetry"—the realization of a magnetic field whose strength exhibits a continuous symmetry in magnetic coordinates, despite the physical geometry lacking such symmetry. Designing a quasisymmetric stellarator that also maintains robust magnetohydrodynamic (MHD) stability and satisfies stringent engineering constraints constitutes a highly non-convex, infinite-dimensional optimization problem. Traditional numerical solvers often rely on floating-point approximations and truncated basis sets, leaving the strict existence of a stable, smooth equilibrium mathematically unproven. To transition stellarator design from numerical approximation to absolute mathematical certainty, we propose the construction of a formally verified domain library using the Lean 4 interactive theorem prover. This report outlines the architecture and mathematical foundations of a Lean 4 library dedicated to the geometry and dynamics of stellarators. By integrating existing topological and geometric formalizations from Lean's Mathlib with the rigorous physics of MHD, this library serves a dual purpose: it establishes an unassailable mathematical bedrock for proving that a proposed magnetic configuration can stably trap a plasma, and it provides an audited, machine-checkable environment to facilitate Artificial Intelligence (AI) assisted discovery of novel stellarator configurations. Architectural Principles of the Lean 4 Domain Library To cleanly separate the fundamental physics of plasma confinement from the heuristic algorithms used to discover new stellarator shapes, the formal domain library must adhere to a strict structural hierarchy. This architecture ensures that the foundational truths of the system are insulated from the phenomenological approximations used in engineering optimization. The library is integrated into the Lean ecosystem via a [[lean_lib]] entry in the lakefile.toml configuration, drawing heavily upon Mathlib's extensive formalizations of smooth manifolds, vector bundles, and functional analysis.

The architecture is explicitly partitioned into three distinct layers: the Kernel, the Sanity Checks, and the Verified Library.

### Library Layer

**Mathematical Purpose**

## Lean 4 Implementation Strategy

### The Kernel

Defines the exact, foundational physics and geometric domain space. Contains the unyielding laws of the system. Utilizes Structures, Inductive Types, and Typeclasses. Never introduces unverified axioms. Kept deliberately minimal.

### Sanity Checks

Mathematically validates the Kernel by proving known limits, boundary behaviors, and degenerate states. Uses theorem proving to demonstrate that exact topological constraints, vacuum limits, and axisymmetry hold under Kernel definitions.

### Verified Library

Contains derived theorems, numerical approximations, stability evaluations, and engineering optimization functions. Formulates API functions with fully verified def and lemma statements. Uses characterizing properties to avoid deep term unfolding.

By adhering to this structure, the Lean 4 library guarantees that any stellarator design resulting from AI-driven search algorithms must satisfy the rigid proofs demanded by the Kernel. The AI acts as a "creative agent" navigating the design space, while Lean acts as the "audit agent," demanding rigorous interval arithmetic and logical proofs before certifying a design as stable.

### The Kernel: Precise Mathematical Foundations of Confinement

The Kernel layer models the domain with absolute precision. In the context of plasma physics, the underlying reality is governed by the kinetic Vlasov-Maxwell equations; however, for the macroscopic design of stellarators, the appropriate foundational domain is Ideal Magnetohydrodynamics (MHD). While Ideal MHD is physically a long-wavelength approximation of kinetic theory, within the formal Lean Kernel, the Ideal MHD equations are established as the precise foundational axioms of the macroscopic model.

The Geometry of the Confinement Domain To make the library accessible and rigorous to mathematicians, the stellarator plasma is modeled fundamentally using differential geometry. The confinement region $\Omega$ is defined in Lean 4 as a smooth, compact, three-dimensional Riemannian manifold with a boundary ($\partial \Omega$), embedded within the Euclidean space $\mathbb{R}^3$. The magnetic field $\mathbf{B}$ and the current density $\mathbf{J}$ are defined as smooth vector fields on $\Omega$. Using Mathlib's Differential Geometry module, the magnetic field can equivalently be formalized as a differential 2-form $\beta$ where the exact physical requirement of a divergence-free magnetic field is expressed precisely by the condition that $\beta$ is a closed form ($d\beta = 0$).## The Exact Ideal MHD Equilibrium Equations

The Kernel defines a macroscopic plasma equilibrium as a state where the fluid velocity is identically zero and the pressure gradient is exactly balanced by the Lorentz force. The precise modeling equations inside the Kernel are the static Ideal MHD equilibrium equations:

$$\mathbf{J} \times \mathbf{B} = \nabla p

$$

$$\nabla \cdot \mathbf{B} = 0

$$

$$\nabla \times \mathbf{B} = \mu_0 \mathbf{J}

$$

Here, $p$ is the scalar plasma pressure, and $\mu_0$ is the vacuum permeability. These equations are precise definitions within the Kernel. By taking the inner product of the force balance equation with both $\mathbf{B}$ and $\mathbf{J}$, the Kernel trivially derives the exact consequences:

$$\mathbf{B} \cdot \nabla p = 0

$$

$$\mathbf{J} \cdot \nabla p = 0

$$

These precise deductions dictate that the magnetic field lines and current density lines lie entirely on isosurfaces of constant pressure. Topologically, for a non-trivial confined plasma where $\nabla p \neq 0$, the Poincaré-Hopf theorem dictates that these isosurfaces must be nested tori. Therefore, the Kernel establishes the existence of nested magnetic flux surfaces, indexed by a radial label $\psi$, representing the enclosed toroidal magnetic flux. Magnetic Coordinates: The Boozer Representation To evaluate particle transport and stability, the Kernel must formally define a system of straight-field-line coordinates. Boozer coordinates $(s, \theta, \phi)$ are mathematically mandated because they possess the unique geometric property that both the magnetic field lines and the current density lines are rectified (appear as straight lines) when mapped to the poloidal angle $\theta$ and the toroidal angle $\phi$.

The formalization of Boozer coordinates in Lean 4 requires defining a global diffeomorphism mapping the Cartesian space to the flux space. The Kernel dictates the precise contravariant representation of the magnetic field:

$$\mathbf{B} = \nabla \psi \times \nabla \theta + \iota(\psi) \nabla \phi \times \nabla \psi

$$

where $\iota(\psi)$ is the rotational transform, representing the precise average topological twist of the magnetic field lines. Correspondingly, the exact covariant representation utilizing Clebsch potentials is formalized as:

$$\mathbf{B} = K(\psi, \theta, \phi) \nabla \psi + I(\psi) \nabla \theta + G(\psi) \nabla \phi

$$
where $2\pi I(\psi)$ is the total toroidal current inside the flux surface, and $2\pi G(\psi)$ is the total poloidal current outside the surface. A critical theorem derived directly within the Kernel is the evaluation of the Jacobian $\sqrt{g}$ for Boozer coordinates. By taking the dot product of the contravariant and covariant forms, the Kernel formally proves:

$$\sqrt{g} = \frac{G(\psi) + \iota(\psi) I(\psi)}{B^2}

$$
This precise equation demonstrates that the volume element of the coordinate system is inversely proportional to the square of the magnetic field strength, an elegant geometric property that dramatically simplifies the Vlasov operator in subsequent transport libraries.

The Biot-Savart Law for External Coils Because stellarators rely on external modular coils, the Kernel must include the precise mapping from coil geometries to the resulting vacuum magnetic field. This is governed by the Biot-Savart law. For a set of one-dimensional superconducting filaments carrying current $I_c$, the precise magnetic field at a position $\mathbf{r}$ is formalized via the line integral:

$$\mathbf{B}(\mathbf{r}) = \frac{\mu_0 I_c}{4\pi} \oint_C \frac{d\mathbf{l} \times (\mathbf{r} - \mathbf{r}')}{\vert{}\mathbf{r} - \mathbf{r}'\vert{}^3}

$$
In the Lean 4 Kernel, this is modeled exactly using measure theory and line integration over parameterized continuous curves $C$ in $\mathbb{R}^3$. This exact formulation provides the basis for evaluating whether a designed coil set can accurately reproduce the required boundary magnetic field of the plasma.

Sanity Checks for the Kernel: Degeneracies and Topological Constraints To ensure the flawless integrity of the definitions housed within the Kernel, a suite of sanity checks must be mathematically established. These are explicitly proved theorems demonstrating that the generalized 3 D Kernel equations correctly degrade into known, simplified limits and obey overriding topological boundaries.

The Axisymmetric Limit: Grad-Shafranov Collapse The most paramount sanity check is the reduction of the 3 D Ideal MHD equations to 2 D axisymmetry—the tokamak limit. The library defines axisymmetry as the exact condition where the Lie derivative of all physical scalar and vector fields with respect to the toroidal basis vector vanishes ($\partial / \partial \phi = 0$).

The Lean 4 sanity check must mathematically prove that under this precise assumption, the complex 3 D force balance equations collapse exactly into the elliptic Grad-Shafranov equation:

$$\Delta^* \psi = -\mu_0 R^2 \frac{dp}{d\psi} - F(\psi) \frac{d F}{d\psi}

$$
where $\Delta^*$ is the specialized Grad-Shafranov differential operator, $R$ is the major radius, and $F(\psi) = R B_\phi$. Formally proving this reduction validates the covariant and contravariant coordinate structures defined in the Kernel, demonstrating that the geometric Jacobian formulations are mathematically sound.

Vacuum Magnetic Fields and Irrotational Limits A second mandatory sanity check investigates the limit of a zero-beta plasma—a vacuum field where plasma pressure $p = 0$ and internal plasma current $\mathbf{J} = 0$. In this precise limit, the Kernel must prove that the magnetic field becomes both divergence-free and curl-free:

$$\nabla \cdot \mathbf{B} = 0

$$

$$\nabla \times \mathbf{B} = 0

$$
By invoking Poincaré's lemma within Mathlib's differential geometry framework, the sanity check proves that a curl-free vector field on a simply connected domain can be expressed as the gradient of a scalar magnetic potential, $\mathbf{B} = \nabla \varphi$. Consequently, the theorem must prove that this scalar potential exactly satisfies Laplace's equation:

$$\nabla^2 \varphi = 0

$$
This sanity check isolates the externally applied magnetic fields from the internal plasma dynamics, ensuring that the modular coil modeling (via the Biot-Savart law) integrates cleanly with the equilibrium equations.

The Garren-Boozer Overdetermination Proof A critical topological sanity check involves the limits of quasisymmetry. The mathematical theory of stellarators relies heavily on the Near-Axis Expansion (NAE) to construct initial geometries. However, Garren and Boozer proved mathematically that global, exact quasisymmetry is impossible in an asymmetric device.

The Lean sanity check must formally expand the NAE equations (detailed in the next section) to the third order in the minor radius expansion parameter, $O(\rho^3)$. The proof must demonstrate that at this order, the number of independent physical constraint equations strictly exceeds the available degrees of freedom (the surface shape Fourier harmonics). By successfully proving the Garren-Boozer overdetermination theorem as a sanity check, the Lean library mathematically justifies why the subsequent Verified Library must utilize phenomenological least-squares optimization rather than exact algebraic solvers for global stellarator boundary generation.

The Verified Library: Approximation, Optimization, and Design With the exact physics and limits certified by the Kernel and Sanity Checks, the Verified Library layer provides the operational infrastructure for actual stellarator design. This layer contains the asymptotic expansions, phenomenological objective functions, and stability criteria required to evaluate a configuration. Functions in this library are rigorously proven to relate back to the Kernel, but they explicitly model approximations or engineering targets.

The Near-Axis Expansion (NAE) Solving the full 3 D Ideal MHD equations for a global domain is computationally daunting. Therefore, the Verified Library implements the Near-Axis Expansion (NAE), an approximate asymptotic framework valid in the immediate vicinity of the magnetic axis.

The magnetic axis is a closed curve $\mathbf{r}_0(s)$ parameterized by arc length $s$, governed by its precise curvature $\kappa(s)$ and torsion $\tau(s)$. The position vector $\mathbf{r}$ of an arbitrary point near the axis is expanded using the orthonormal Frenet-Serret frame (tangent $\mathbf{t}$, normal $\mathbf{n}$, binormal $\mathbf{b}$):

$$\mathbf{r} = \mathbf{r}_0(s) + \rho (\cos \theta \mathbf{n} + \sin \theta \mathbf{b})

$$
where $\rho$ is the distance to the axis, and $\theta$ is a poloidal angle. The library formalizes the physical scalar fields (pressure, field strength) as Taylor-Fourier series expansions in the small parameter $\rho \sim (r/\mathcal{R})$, where $\mathcal{R}$ is the characteristic major radius.

The NAE equations are formulated as approximate differential equations solvable order-by-order. At $O(\rho^0)$, the equations determine the magnetic field on the axis. At $O(\rho^1)$, the equations dictate the elliptical elongation of the flux surfaces. By building the NAE up to arbitrary order in Lean 4, researchers can rapidly generate analytically guaranteed quasisymmetric core geometries, which are then passed to global solvers to generate the finite-minor-radius boundary shape.

Formulating Quasisymmetry Objectives Because the Sanity Checks prove that exact global quasisymmetry is impossible, the Verified Library treats quasisymmetry as a target for optimization. Quasisymmetry requires that the magnitude of the magnetic field, $B = \vert{}\mathbf{B}\vert{}$, depends on the Boozer coordinates only through a linear combination of the poloidal and toroidal angles:

$$B = B(\psi, M\theta - N\phi)

$$
where $M$ and $N$ are integers (e.g., $M=1, N=0$ yields Quasi-Axisymmetry).

The library introduces a phenomenological objective function, $f_{QS}$, designed to penalize deviations from exact quasisymmetry across the plasma volume. This objective is defined precisely in Lean as the flux-surface-averaged squared residual of the symmetry condition:

$$f_{QS} = \sum_{s_j} w_j \left\langle \left( \frac{1}{B^3} \left[ (N - \iota) \mathbf{B} \times \nabla B \cdot \nabla \psi - (G + N I) \mathbf{B} \cdot \nabla B \right] \right)^2 \right\rangle

$$
where $w_j$ are discrete radial weighting factors, and the angle brackets $\langle \dots \rangle$ denote a flux surface average, computed via $\langle Q \rangle = (1/V') \int \int \sqrt{g} Q \, d\theta \, d\phi$. The Lean library provides verified numerical integration routines to compute these surface averages rigorously, ensuring the objective function behaves predictably during AI-driven gradient descent.

Engineering Constraints for Practical Construction A mathematically optimized stellarator shape is useless if the required external coils are physically impossible to build. The Verified Library must encode computable metrics for engineering feasibility, formulated as phenomenological penalty functions added to the overarching optimization objective. Engineering Constraint Phenomenological Metric Mathematical Implication Minimum Radius of Curvature$\rho_{min} > 0.52 \text{ m}$Prevents infinitely sharp bends in superconducting filaments, ensuring physical manufacturability. Coil-to-Coil Distance$d_{c-c} > 0.83 \text{ m}$Ensures sufficient spatial volume for structural support casing and neutron shielding between adjacent modular coils. Plasma-to-Coil Distance$d_{p-c} > 1.4 \text{ m}$Prevents the extreme concentration of magnetic fields near the plasma boundary and provides space for the blanket and divertor systems. These geometric constraints require the library to calculate the exact Euclidean distances between discretized 3 D parametric curves (the coils) and the plasma boundary surface, utilizing Lean's Euclidean geometry packages to maintain strict verification.## Proving Plasma Stability: Exact Criteria and Quadratic Forms

Designing the geometric shape of the stellarator is only the first step; the overriding objective is to mathematically prove that the plasma remains stable against both microscopic and macroscopic perturbations. The Verified Library handles stability by translating physical perturbation theory into exact functional analysis.### Local Stability: The Mercier Criterion

Local interchange instabilities are driven by plasma pressure gradients interacting with regions of unfavorable magnetic curvature. The threshold for these instabilities is evaluated using the Mercier Criterion, an exact analytic boundary limit.

The library defines the Mercier Criterion as a precise mathematical condition that must be evaluated on every rational flux surface. Linear stability against localized modes is guaranteed if the Mercier sum $\Omega > 0$, defined as:

$$\Omega = \Omega_s + \Omega_w + \Omega_c > 0

$$
Here, $\Omega_s$ represents the stabilizing effect of magnetic shear (the radial derivative of the rotational transform, $\iota'$). The term $\Omega_w$ measures the presence of a "magnetic well" (favorable average curvature, proportional to $-V''/V'$, where $V$ is the volume enclosed by a flux surface). Finally, $\Omega_c$ accounts for the destabilizing parallel Pfirsch-Schlüter currents. If the un-filtered parallel current exhibits singularities at rational surfaces ($\iota = n/m$), the Mercier criterion violently diverges, yielding negative (unstable) values due to Schwarz's inequality. The Lean formalization strictly evaluates this algebraic sum, providing a hard, binary operational boundary during the optimization phase. Global Stability: The Ideal MHD Energy Principle ($\delta W$) While the Mercier criterion handles localized perturbations, the library must also guarantee stability against global, low-n macroscopic instabilities (e.g., external kink and ballooning modes). This is achieved by formalizing the Ideal MHD Energy Principle. The fundamental theorem states that a static equilibrium is linearly stable if and only if the change in potential energy, $\delta W$, is positive definite for all possible smooth, physically allowable plasma displacement vectors $\boldsymbol{\xi}$.

The exact mathematical formulation of the total perturbed potential energy is formalized in Lean 4 as a self-adjoint quadratic form, split into plasma and vacuum contributions ($\delta W = \delta W_p + \delta W_v$). The internal plasma energy integral is precisely:

$$\delta W_p = \frac{1}{2} \int_V \left( \frac{\vert{}\mathbf{Q}\vert{}^2}{\mu_0} - \boldsymbol{\xi} \cdot (\mathbf{J} \times \mathbf{Q}) + \Gamma p (\nabla \cdot \boldsymbol{\xi})^2 + (\boldsymbol{\xi} \cdot \nabla p)(\nabla \cdot \boldsymbol{\xi}) \right) d^3x

$$
where $\mathbf{Q} = \nabla \times (\boldsymbol{\xi} \times \mathbf{B})$ is the perturbed magnetic field vector, and $\Gamma$ is the ratio of specific heats. In Lean 4, proving $\delta W > 0$ is framed as a functional analysis problem. By extending existing Mathlib structures for linear elliptic partial differential equations (such as the Lax-Milgram theorem and Poincaré inequalities), the energy principle is mapped to an eigenvalue equation for the force operator $\mathbf{F}(\boldsymbol{\xi}) = \lambda \rho_m \boldsymbol{\xi}$. The library must utilize pseudospectral discretization or finite-element differentiation matrices to construct the response matrix for $\delta W$. If Lean can verify that the lowest eigenvalue of the system is strictly positive, the configuration is mathematically proven to be macroscopically stable. Rigorous Numerics: Bridging Theory and Computation A profound challenge in formal verification is connecting continuous analytical theory to the discretized numerical frameworks required for engineering design. Standard stellarator optimization codes (like VMEC or DESC) rely on iterative, floating-point minimization algorithms. While these codes produce configurations with very low force-balance errors, they do not constitute a mathematical proof that a true, exact equilibrium exists nearby. To satisfy the user's requirement for a verified stable plasma, the library must implement rigorous computer-assisted proofs (CAP).## The KAM Theorem and Interval Arithmetic

The structural integrity of the stellarator confinement region relies on the absolute persistence of nested magnetic flux surfaces. Mathematically, these flux surfaces are Hamiltonian invariant tori. When a symmetric configuration is subjected to non-axisymmetric 3 D perturbations, the Poincaré-Birkhoff theorem shows that rational tori break into island chains, and overlapping islands generate chaotic, stochastic field lines where plasma confinement is lost.

The survival of the highly irrational (Diophantine) tori is governed by the Kolmogorov-Arnold-Moser (KAM) theorem. The KAM theorem dictates that if the perturbation is sufficiently small and the rotational transform satisfies a precise Diophantine condition, the tori persist.

To formally prove that a specific numerical stellarator design satisfies the KAM theorem bounds, the Lean 4 library must utilize interval arithmetic. Standard floating-point numbers are replaced by upper and lower bounding intervals that strictly contain the true real numbers, guaranteeing that rounding and truncation errors never compromise the logic of the proof. Using packages like Lean Cert, the library rigorously computes the KAM small-denominator bounds and confirms they lie within the safe region.

The Radii Polynomial Method To certify the existence of true solutions to the nonlinear differential equations governing the Near-Axis Expansion and global MHD equilibrium, the Lean 4 library implements the radii polynomial method. This framework translates the differential initial value problem into a fixed-point equation within a weighted Banach space of sequence algebras (specifically, Fourier-Taylor coefficients). The process involves:Ingesting an approximate numerical solution (e.g., from a Python-based optimizer). Formulating a Newton-like fixed-point operator around this approximate solution. Using interval arithmetic to rigorously evaluate a finite-dimensional projection of this operator. Constructing a "radii polynomial" that estimates the truncation and bounding errors for the infinite-dimensional tail. If the radii polynomial exhibits a negative root, it constitutes a mathematically rigorous, machine-checked proof that a unique, true solution exists within a tightly bounded neighborhood of the numerical approximation. Integrating this capability into Lean 4 bridges the gap between fast heuristic discovery and absolute mathematical certainty.

Facilitating AI-Assisted Mathematical Discovery The formalized environment described above serves as an ideal, audited staging ground for AI-accelerated physics discovery. Designing stellarators requires navigating an exceptionally vast and rough high-dimensional parameter space of boundary Fourier harmonics ($R_{m,n}, Z_{m,n}$) and axis shapes.

The library architecture naturally supports an adversarial, two-team agent system.

The Creative Agent: Operates outside of the strict Lean environment. It leverages generative AI, neural network surrogates (like GS-Deep Net), and heuristic optimizers (like DESC or py QSC) to rapidly scan the parameter space, seeking configurations that minimize the phenomenological $f_{QS}$ penalty and maximize the $\delta W$ stability criteria.

The Audit Agent: Is the Lean 4 environment itself. Once the Creative Agent proposes a candidate configuration, it synthesizes a formal proof script detailing the exact geometric bounds. Lean ingests this candidate, utilizes interval arithmetic to check the radii polynomials, rigorously evaluates the Mercier criterion on rational surfaces, and attempts to compile the proof term. Because the Kernel relies entirely on strictly defined typeclasses and the Verified Library demands rigid satisfaction of exact physical laws, AI hallucinations are structurally impossible to validate. If Lean compiles the proof without invoking the sorry axiom, a mathematically guaranteed stable stellarator design has been discovered.## Conclusion

The construction of a Lean 4 verified mathematical library for the geometry and dynamics of stellarators represents a transformative intersection of differential geometry, plasma physics, and formal logic. By strictly partitioning the domain architecture into a minimalist, axiom-free Kernel representing exact Ideal MHD, and a robust Verified Library containing phenomenological optimization targets and rigorous stability criteria, researchers can ensure the absolute physical integrity of their models. The integration of interval arithmetic, KAM theory, and the radii polynomial method provides the crucial mathematical bridge, converting approximate numerical equilibria into unassailable proofs of stable, trapped plasma. As this Lean library matures alongside Mathlib, it establishes the ultimate audited framework for AI-assisted discovery, enabling the definitive mathematical design of continuous, steady-state fusion reactors capable of practical construction.