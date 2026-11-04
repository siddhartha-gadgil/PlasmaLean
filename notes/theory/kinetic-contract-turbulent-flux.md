# Kinetic model contract and a turbulent heat-flux bound from gyrokinetic free energy

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-40` |
| Title | Kinetic parent-model contract and the free-energy route to a turbulent flux bound (method note for N-20) |
| Kind | method (research approach; lean-ready fixtures) |
| Addresses | `Q-28` (new); `G-2` (C5 anomalous transport), `G-11` (contract infrastructure), `G-3`; supports `Q-15`, `Q-22` |
| Depends on | N-20 (available energy, maximum-J), N-2 (relative entropy), N-36 (claims 6, 8, 14, 16, 17, 24, 32, 33, 35, 37); Lean: `Theory/Kinetic/AvailableEnergy`, `Theory/Transport/RelativeEntropyCoercive`, `Kernel/Transport` (supplied D) |
| Dependency requirement | none compiled for (a); (b) needs a gyrokinetic model contract that does not exist yet |
| Produces | Q-28 (a)–(c) statements; Lean targets for (a) |
| Difficulty | routine (a); research (b), (c) |
| Status | stated; (a) lean-ready; (b), (c) open research |
| Lean evidence | none yet |
| Audit evidence | not audited |
| Last updated | 4 November 2026: created from N-36 |
| Patched by / Alternatives | method for N-20 (its compiled kernel lemmas and the unchecked-formula caveat stand) |

## Purpose and scope

Under the contract, C5 takes anomalous transport as a **supplied scaling**: ISS04, or an
available-energy bound Â (N-20). The radial transport kernel accepts any D ≥ 0. The kinetic/coil
brief (N-36) makes the main structural point. A thermal barrier with an assumed coefficient is one
module; the producer of the turbulent flux is a separate module that must actually be supplied.
It also observes that a heat-flux bound does not by itself preserve a pointwise barrier: one needs
a bound on the operator defect, a monotone conservative scheme or strong state control (claim 17).

This note records the route to such a producer, in three layers. Available energy stays what N-20
says it is, a screening proxy: Â bounds releasable energy, not flux, and its formula is still
unchecked against Mackenbach–Proll–Helander (KB-P5 = N-20's open part).

## Theory development

**(a) Kinetic model contract and fixtures (lean-ready).** These are algebraic and kernel-level
statements of the parent system (brief §§2–3, 5, App. B), not existence theorems:
- the Landau kernel: U(z)z = 0 and a·U(z)a ≥ 0 (`landauKernel_mul_self`, `landauKernel_psd`);
- the weak-form conservation identities for a symmetric pair kernel on finite (discrete) velocity
  measures: mass, momentum and energy (`pairCollision_conserves_*`);
- the moment algebra: F = (½mn|u|² + (3/2)nT)u + Πu + q (`energyFlux_decomposition`);
- negative fixtures:
  - a non-constant local Maxwellian is not an exact zero-flow source-free stationary solution
    (`not_stationary_of_nonconstant_maxwellian`; the cubic coefficient forces ∇T = 0);
  - a vacuum field with static force balance forces ∇p = 0 (`gradient_pressure_eq_zero_of_vacuum`;
    from `VacuumField` and `ForceBalance` with an actual pressure gradient, cf. E-1);
- reaction counting for D + T → α + n: moments (−1, −1, +1, +1), charge preserved
  (`dt_reaction_moments`).

These go in a new `Theory/Kinetic/ParentModel.lean` (or `Sanity/KineticFixtures.lean`) in the
default build. Choosing a kernel-level kinetic law is a material commitment, so it is not proposed
here.

**(b) Free energy and a flux bound (research; brief §8.2–8.3, Research target 1).**
- In the local electrostatic gyrokinetic pilot (brief §6.2), the free energy W = Σ_k W_k with

  W_k = ½⟨Σ_s T_s ∫|η_{s,k}|²/F₀ₛ + (n_s q_s²/T_s)(1 − Γ₀ₛ)|ϕ_k|²⟩ ≥ 0

  equals the |h|² form under quasineutrality (re-derived exactly, N-36 check 7). Its balance is
  dW/dt = P_gradients + P_sources − D_coll − F_boundary.
- Cauchy–Schwarz gives |Q_s| ≤ (∫T_s h_s²/F₀ₛ)^{1/2} (∫E²F₀ₛ|v̄_E·∇ψ|²/T_s)^{1/2}. The second factor
  contains field gradients.
- **Target:** |Q_s| ≤ C_Q W together with Ẇ ≤ −λW + C W^{3/2} + ε(t), for a stated perturbation
  class, with every constant derived. An alternative valid target is bounded turbulence with a
  small time-averaged flux.
- Barriers:
  - W does not control field gradients (an L² amplitude does not bound ∇ϕ);
  - gradients drive instability, so decay may be false;
  - the Landau operator lacks a uniform spectral gap without weights;
  - Helander–Plunk bounds are growth bounds, not saturation bounds.

**(c) Interface to transport (research).** Turn a flux bound into a transport statement usable by
the barrier theorems (`Theory/Transport/Comparison`). Either:
- bound the defect of the radial operator, i.e. the divergence of the flux and not only the flux
  (claim 17); or
- use a monotone conservative finite-volume comparison with a justified face-flux dependence.

Then the supplied D in `Kernel/Transport` is replaced by a produced flux. That closes the
"supplied scaling" gap of C5 for anomalous transport; Q-22 does the same for neoclassical
transport.

## Claims and evidence

- (a): standard identities, three of them re-derived exactly in N-36 (checks 1–5); not in Lean.
- (b): the free-energy identity is re-derived exactly; the flux inequality (8.5) is elementary; the
  target is an open research question.
- (c): open.

## Difficulty, barriers and readiness

(a) is lean-ready and light: finite-dimensional algebra and a symbolic Maxwellian computation with
`Real.exp` derivatives. (b) and (c) are research. They are deliberately not on the critical path
before a finite-β current-free candidate exists (Q-20): a flux bound is only useful on the geometry
of the candidate. The numerical gyrokinetic programme of the brief (KB-P4) needs external codes and
compute outside the laptop and workstation budget; it is not planned.

## Outputs and next dependencies

Q-28. The fixtures of (a) also serve as sanity checks for any later kinetic module (brief App. B
items 1, 4 and 6).
