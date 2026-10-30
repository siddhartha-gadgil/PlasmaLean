# Ideal-MHD stability: from energy identities to useful certificates

This chapter separates directly derived algebraic identities, established source theory to formalize, and new research targets. Read [00](00-model-contracts.md), [02](02-plasma-models-and-equilibrium.md), and the stability entries in [09](09-literature.md#stability-and-kinetic-theory). The exposition is the specification. Each section ends with a **Status in PlasmaLean** paragraph: what is compiled (declaration and module, default build or on demand), which reduction or formula is supplied, what is open (`Q-*` identifiers of the [research graph](../implementation-plan.md#research-graph-added-29-october-2026)) and what the audits corrected. The summary is in [Status in PlasmaLean](#status-in-plasmalean). Status as of 30 October 2026, against the [stellarator contract](../implementation-plan.md#the-stellarator-contract-30-october-2026), [progress report 15](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md) and the [model audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md).

"Default build" means imported by `PlasmaLean.lean` and covered by `scripts/check_axioms.lean` (standard axioms only).

## Contents

- [Role in the stellarator contract](#role-in-the-stellarator-contract)
- [Start with an abstract energy theorem](#start-with-an-abstract-energy-theorem)
- [The continuum MHD bridge](#the-continuum-mhd-bridge)
- [Elementary sufficient bounds](#elementary-sufficient-bounds)
- [Neutral modes and continuous spectrum](#neutral-modes-and-continuous-spectrum)
- [Free boundaries and local criteria](#free-boundaries-and-local-criteria)
- [Discretization and nonlinear targets](#discretization-and-nonlinear-targets)
- [Status in PlasmaLean](#status-in-plasmalean)
- [Theorem backlog](#theorem-backlog)

## Role in the stellarator contract

This chapter is clause **C3**: MHD stability at a stated β > 0. That means Mercier (interchange), ideal ballooning and, where available, global ideal modes, with every reduction named. C1 changes what C3 has to cover. A current-free equilibrium has no current-driven kinks or tearing driven by a net toroidal current, so the **pressure-driven** modes (interchange, ballooning, pressure-driven global modes) are what remains. A stability result counts toward the contract only on an equilibrium that also satisfies C1 and C4.

Under this criterion the compiled stability results are technique results. The Solov'ev certificates concern a tokamak model. The screw pinch is a current-carrying model problem. Landreman family 2 has a certified Mercier-stable band, but it carries a positive net toroidal current (Q-18), so it fails C1. **Nothing is certified at finite β for a current-free candidate**, because no such equilibrium exists in Lean yet (Q-20). The checkers (Picone/Barta certificates, the general Mercier evaluation, the surface ballooning certificate) are built to transfer to one.

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

**Status in PlasmaLean.** Compiled in the default build (`Theory/Stability/AbstractEnergy`): `energy_hasDerivAt_zero`, `energy_conserved`, `displacement_bound` and `velocity_bound`. These are conditional on a differentiable solution on `[0, T]`, in the same-space variant (position and velocity in one normed space). The `V ⊂ H` embedding variant, evolution existence and the MHD bridge are open (S1).

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

The term `−ξ·(J×Q)` is the current drive. In a current-free (vacuum-like) region it vanishes, which is why C1 removes the kink drive. In a finite-β stellarator the diamagnetic and Pfirsch–Schlüter currents remain, so this term does not vanish identically.

**Status in PlasmaLean.** The continuum bridge (S2) and the self-adjoint realization and precise energy principle (S5) are **not formalized**. Every compiled stability criterion below therefore starts from a *supplied* reduced form of δW: Newcomb's reduced form for a cylindrical mode, the Connor–Hastie–Taylor ballooning reduction, or the Landreman–Jorge Mercier formula. Each is named in the scope of the claims that use it.

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

**Status in PlasmaLean.** `young_drive` and `two_channel_drive` (`Theory/Stability/YoungBounds`) prove the scalar pointwise algebra. The integral MHD identity and any geometric coercivity constant are open (S3). The reference-plus-perturbation margin is `perturbation_margin` and `combined_error_margin` (`Theory/Stability/BlockBounds`), which take the retained, tail and coupling bounds as hypotheses.

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

**Status in PlasmaLean.** The neutral-drift counterexample is compiled (`neutral_solution`, `neutral_energy_does_not_control_displacement`, `Sanity/NeutralMode`, default build). The MHD quotient by relabelings and the admissible-space characterization are open (S4). Negative-energy test displacements are used as rigorous instability witnesses: `suydam_necessary` (an explicit logarithmic mode) and the Sturm conjugate-point theorems below.

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

**The local criteria in brief.** In a cylinder the energy of a localized interchange near a resonant surface reduces to `∫(F x²ξ′² + G ξ²)dx`. Suydam's criterion `F + 4G ≥ 0` is exactly the sharp Hardy inequality `∫ξ² ≤ 4∫x²ξ′²`. For a single cylindrical mode, Newcomb's reduced form `∫(fξ′² + gξ²)` is nonnegative when a Picone (Riccati) certificate exists. The three-dimensional generalization of Suydam is the Mercier criterion: shear, current, well and geodesic terms evaluated by surface integrals. High-mode-number ballooning reduces along each field line to the Sturm–Liouville form `∫(PX′² + QX²)` on the covering line, with the bad-curvature drive in `Q`. A positive Barta (Jacobi) supersolution certifies stability, and a conjugate point refutes it.

**Status in PlasmaLean.** Free-boundary terms (S8) are not formalized. The local criteria are (all default build unless stated):

- *Suydam* (`Theory/Stability/Suydam`). `hardy`, `suydamForm_coercive` (sufficiency with an explicit `L²` margin), `suydam_necessary` and `suydam_unstable_near_resonance` (necessity: a logarithmic mode with negative energy). Proved both ways.
- *Newcomb and Sturm* (`Theory/Stability/Newcomb`, `Theory/Stability/SturmNecessity`). `picone_certificate` and `jacobi_certificate` (sufficiency, allowing `f` to vanish at a resonant surface); `ConjugatePoint.energy_lt` and `ConjugatePoint.no_bartaCertificate` (necessity in conjugate-point form; the Jacobi field is supplied, for example by a validated ODE enclosure).
- *Screw pinch* (`Design/ScrewPinchModes`, `Design/ScrewPinchModesHighM`). `stable_all_modes_equilibrium` combines the radial force balance `RadialBalance` with `ModeStable` for **every mode with m ≠ 0** and every axial wavenumber in the example. Newcomb's reduced form is supplied (`NewcombReduction`), and `energy_nonneg_all_modes` is conditional on it. The m = 0 modes are not covered. Earlier wording "all-mode" was corrected (audit M-3), and the radial balance was added to the headline (model audit MA-L6). The pinch is current-carrying, so this is a model problem, not C3 for a candidate.
- *Mercier, cylindrical and large-aspect-ratio* (`Theory/Stability/Mercier`). `mercier_iff_suydam` (Greene–Johnson index `D_I` in the cylinder is Suydam), `mercierTokamak_of_safetyFactor_ge_one`.
- *Mercier, general three-dimensional* (`Theory/Stability/MercierGeneral`). `mercierIndex` and `MercierStable` encode the Landreman–Jorge 2020 eq. (3.1) formula. **The formula is supplied**: its derivation from δW is not formalized. Proved checks: `mercierIndex_vacuum`, `mercierIndex_cylinder_eq_suydam` and `cylinder_mercier_neg_of_shearless`. `mercierIndex_neg_of_forceBalance` (`Theory/Stability/MercierShearless`): a shearless surface without a magnetic well, with force balance and ∇p ≠ 0, is Mercier-unstable (Cauchy–Schwarz).
- *Mercier, applications.* `family2_mercier_stable_derived` (`Design/LandremanFamily2MercierDerived`): Landreman family 2 at λ = 200 is Mercier-stable on the band k ∈ [0.7, 0.9]. The fluxes, volume, current and Jacobian are derived from the field (cite this version, not the older `family2_mercier_stable` with supplied labels). The certificates are explicit (Q-6 done: all 136 outer-arc checks use `f2_arc_cert`). `family1_mercier_unstable` (`Design/LandremanMercier`, closed field lines, no shear); `zero_mercier_unstable` (`Design/HelicalMercier`, the a = 0 helical member); `reactor_mercier_stable` (`Design/SolovevMercierCertified`, the Solov'ev tokamak model). Family 2 carries net toroidal current, so its stable band is a C3 technique result on a test bed that fails C1.
- *Ballooning* (`Theory/Stability/Ballooning`, `BallooningReduction`, `BallooningInfinite`, `BallooningSurface`, `BallooningSecular`). The reduction to `P = ‖k‖²/(ℓ‖B‖²)` and the bad-curvature drive `Q` is **supplied** (Connor–Hastie–Taylor; Dewar–Glasser), with `ballooningQ_clebsch`, `noPressure_energy_nonneg` and the cylinder-equals-Suydam checks. Certificates: `BartaCertificate.lower_bound`, piecewise gluing on the infinite line (`FluxBound.glue`), the transported eikonal on a general surface, and `jpar_transport` (the secular drive is the parallel derivative of `J∥ = J·B/‖B‖²`, for a general three-dimensional equilibrium). Applications: `reactor_ballooning_all` (every flux surface of the reactor Solov'ev equilibrium, a tokamak model); for family 2, `family2_stable_of_cert` and `family2_stable_of_secular_cert` reduce ballooning stability to **one pointwise inequality** on surface × ℝ. That inequality is numerically stable (tail margin ×2.36–×9.39) but **not certified (Q-3)**: linear-in-s certificates and the B-spline × rational basis fail at k = 0.9, and the checker is not written.

**Model-audit findings** (30 October, [model audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md), sanity theorems in `Sanity/AuditModelStability`, default build). No critical or high findings for the stability models. The transcriptions of Mercier, ballooning and Newcomb were re-derived against the sources. The Mercier well and geodesic terms are validated only through the cylinder reduction plus a field-reversal check (`mercierIndex_reverseField`), since the source PDF was not re-read. Low findings, each with a regression theorem and none affecting a current headline:

- MA-L4: `MercierSurfaceData` does not force `s_G, s_ψ ∈ {±1}` or `∫B²w > 0` (`mercier_negative_B2_stable`, `mercier_sG_zero`). The headline uses supply these.
- MA-L5: `LineData` does not require `k ⊥ B`, so a parallel component of `k` is spuriously stabilizing (`ballooningP_add_parallel`). Both applications prove orthogonality (`family2Line_k_perp`).
- MA-L6: `ModeStable` does not require radial balance (`modeStable_nonequilibrium`). Fixed in the headline by `stable_all_modes_equilibrium`.
- MA-L7: `NewcombReduction` holds vacuously for an empty admissible class (`newcombReduction_empty`).

Adversarial checks confirm the physics: `mercier_hill_unstable`, `ballooningQ_neg_of_bad` (bad curvature destabilizes) and `badLine_not_stable`.

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

**Status in PlasmaLean.** The square-completion inequalities `two_block_nonneg` and `two_block_margin` (`Theory/Stability/BlockBounds`) are compiled with supplied block bounds. No MHD tail estimate, Galerkin bound or nonlinear (Casimir) stability theorem exists (S7, S9). The certified stability results are the local and one-mode results listed above, all with a supplied reduction.

## Status in PlasmaLean

Summary (30 October 2026). All named declarations are in the default build.

| Topic | Compiled (declarations, module) | Supplied reduction or hypothesis | Contract role and open items |
| --- | --- | --- | --- |
| Abstract energy | `energy_conserved`, `displacement_bound`, `velocity_bound` (`AbstractEnergy`) | differentiable solution | S1 embedding variant; S2, S5 open |
| Drive bounds | `young_drive`, `two_channel_drive`, `perturbation_margin` | block bounds supplied | geometric coercivity open (S3) |
| Neutral modes | `neutral_solution`, `neutral_energy_does_not_control_displacement` | none | quotient space open (S4) |
| Suydam, Newcomb, Sturm | `suydamForm_coercive`, `suydam_necessary`, `picone_certificate`, `ConjugatePoint.no_bartaCertificate` | Jacobi field supplied (Sturm) | technique |
| Screw pinch | `stable_all_modes_equilibrium`, `energy_nonneg_all_modes` | Newcomb reduced form | m ≠ 0 only; current-carrying model problem |
| Mercier (general) | `mercierIndex_cylinder_eq_suydam`, `mercierIndex_neg_of_forceBalance`, `family2_mercier_stable_derived`, `family1_mercier_unstable`, `reactor_mercier_stable` | Landreman–Jorge formula | family 2 fails C1 (Q-18); Solov'ev is a tokamak model |
| Ballooning | `BartaCertificate.lower_bound`, `jpar_transport`, `reactor_ballooning_all`, `family2_stable_of_cert`, `family2_stable_of_secular_cert` | Connor–Hastie–Taylor reduction | family-2 certificate open (Q-3) |
| Global, free-boundary, nonlinear | `two_block_margin` (algebra only) | none | S5, S7–S10 open |

**Against the contract.** C3 is not met for any current-free candidate. The certified Mercier band and the ballooning reduction concern Landreman family 2, which carries net toroidal current. The all-surface ballooning and Mercier certificates concern the Solov'ev tokamak model. The next C3 step is to transfer these checkers to a current-free finite-β equilibrium once one exists (Q-20, Q-14). Q-3 remains useful as technique.

## Theorem backlog

| ID | Target | Main missing ingredient |
| --- | --- | --- |
| S1 | Abstract energy conservation and coercivity bound | Hilbert-space differentiation |
| S2 | Linearized MHD identities and fixed-boundary energy | Calculus and justified integration |
| S3 | Young-inequality drive bound above | Exact norm inequalities |
| S4 | Neutral-mode counterexample and quotient definition | Admissible-space characterization |
| S5 | Self-adjoint realization and precise energy principle | Closed forms, domains, spectral/evolution theory |
| S6 | Source-specific local stability criteria | Exact hypotheses and normalization; derivation of the supplied Mercier formula |
| S7 | All-mode certified bound for a restricted useful configuration | Tail/coupling analysis; potentially research |
| S8 | Free-boundary certificate with coils/vacuum/wall | Interface operator and trace bounds |
| S9 | Nonlinear orbital stability with quantitative basin | Conservation, constraints, remainders, continuation |
| S10 | Finite-beta robust stability for a constructible 3-D family | Major research target; must be on a current-free (C1) equilibrium; may require a weaker stability notion |
