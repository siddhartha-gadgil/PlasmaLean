# Approximate momentum on a band of trapped particles

[N-53](hamiltonian-bounce-band-test.md) specifies the physical comparison and birth coverage.

For a regular annulus of periodic orbits, the averaged perturbation determines a radial label and a finite-time confinement bound. [N-51](annulus-averaged-flux.md)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-49` |
| Title | Approximate momentum, period obstructions and finite-time particle loss |
| Kind | Method for N-34, N-43 and N-48 |
| Addresses | G-6, G-10, G-3 (P1), Q-1, Q-23, Q-29(c) |
| Depends on | N-43 for the exact weak-QS corrector, N-48 for Hamiltonian and period identities, N-34 for the Dommaschk test geometry |
| Dependency requirement | A supplied regular Hamiltonian orbit model on the region visited. The candidate application also needs orbit existence, a core and exit set, and uniform estimates throughout that region. |
| Produces | A finite-time exit criterion, a test for the solvability of a periodic correction, and a route to energy-weighted birth losses |
| Difficulty | Research. The pointwise identity is elementary. The challenge is a useful momentum gap and drift bound on one physical field. |
| Status | Exploratory. The conditional estimates below have paper proofs. The field-specific construction is open. |
| Lean evidence | N-51 proves the single-orbit periodic obstruction, its optimal residual, and finite-time exit estimates when the band has its common-volume annular structure. Constructing a physical band is open. |
| Audit evidence | Not audited |
| Last updated | 23 November 2026. Proposed after discussion of conceptual alternatives to per-surface certificates. |

## Purpose and scope

Work on a compact band of regular trapped orbits for one prescribed field. Fix the species, energy and pitch range, birth region, loss surface and time unit. Use either a specified Hamiltonian guiding-centre reduction or the full nonrelativistic Lorentz system. Each requires its own orbit and boundary interpretation. Start with zero electric field and collisionless motion. A finite-time exit estimate is an observable for G-6. Thermal transport and the field-level C2 contract require further results.

## Dependencies

For the magnetic Lorentz model, `magneticForm_lorentzForceField` identifies contraction of the kinetic phase-space form with the differential of the free Hamiltonian (default build, use positive mass). N-43 supplies a concrete candidate momentum under exact weak QS, with its higher-order corrector still on paper. N-34 supplies a vacuum field and two certified surfaces through the on-demand `dommaschk_Q16_vacuum`. The space between the surfaces needs its own estimates. [Lorentz identity](../../PlasmaLean/Theory/Kinetic/MagneticSymplectic.lean) · [N-43](weak-qs-corrected-flux.md) · [N-34](dommaschk-qs-defect.md)

## Theory development and claims

**Complete mathematical proof — exit bound.** Choose the convention $ι_Xω=dH$ and a single-valued function $P$ and vector field $U$ satisfying $ι_Uω=dP+r$. Evaluating on $X$ gives $X(P)=-U(H)-r(X)$ by antisymmetry. Suppose every continuous orbit from the birth set exists up to first exit or time $T$. Let $Δ=\inf_{\rm exit}P-\sup_{\rm birth}P>0$ and bound $|U(H)+r(X)|≤η$ throughout the accessible region. Integration up to a putative first exit gives $Δ≤ηt$. Hence $ηT<Δ$ excludes exits through time $T$, including when $η=0$. Include every way to leave the region of validity in the exit set, or bound the other exits independently. If $P$ approximates a flux label to error $A$, subtract up to $2A$ from the flux gap before using it. The ratio $Δ/η$ has units of time.

**Complete mathematical proof — obstruction on a closed leading orbit.** To remove a leading drift $f$ by a periodic correction $g$, one needs $X_0g=-f$ for the unperturbed bounce flow. Integrating once around a periodic orbit gives $\int_0^{T_b} f\,dt=0$. Conversely on that single orbit, integrating $-f$ defines a periodic primitive if the mean vanishes. A nonzero mean bounds the residual from below in supremum norm by the absolute mean for every periodic correction. Uniform smooth dependence on a band and control of the perturbed flow remain additional requirements.

**Sourced theorem — period test.** If $ω$ is closed and $U$ preserves it, Cartan's formula makes $ι_Uω$ closed. A smooth closed one-form has a global primitive exactly when its periods on first homology vanish, by the de Rham theorem. Identify the generators of the *particle phase-space region* before applying this test. On a parameterized spatial torus there is a relevant compiled special case: `PeriodicC2Torus.exists_periodic_potential_of_curl_eq_zero` removes both periods from the pullback of a curl-free C¹ field on a C² periodic surface (default build). For an approximate symmetry, also estimate $dι_Uω$ and the residual along $X$. [Torus-period theorem](../../PlasmaLean/Theory/Fields/FormFluxSurfacePeriods.lean)

## Sources and prior work

Burby, Kallinikos and MacKay treat approximate symmetries in guiding-centre phase space. Burby, MacKay and Naik relate the longitudinal action to transitions between classes of guiding-centre motion, and derive a first-order Melnikov test. These provide separate models for a regular bounce and for the approach to a separatrix. [Approximate symmetries](https://arxiv.org/abs/2010.08968) · [Isodrastic magnetic fields](https://arxiv.org/abs/2211.13367)

## Difficulty, barriers and readiness

1. Fix a symmetry benchmark with a known conserved momentum and an actual trapped bounce. Then test one compact band on Dommaschk and one published quasi-isodynamic comparator in the same normalized energy, pitch and radial range. Compare against direct accumulation of absolute radial drift on that band. Record both the bound and the energy weight of births covered. A positive gap rules out a constant momentum. [Quasi-isodynamic comparators](https://arxiv.org/abs/2211.09829)
2. Seek a phase-space generator or corrector with a small bounce mean. For an approximate flux chart, include parallel streaming across its proposed surfaces. For a physical-coordinate calculation, include its own reduction errors when inferring full-orbit behavior. Test the signed bounce integral before enlarging a basis of correctors.
3. For well integrals, try analytic continuation on a specified complex neighborhood with uniform field bounds, separated simple turning points and a controlled endpoint substitution. Cauchy bounds could then control derivative or Fourier tails. When roots coalesce, isolate that pitch range and account for its weight or transition dynamics separately. Ill-posedness of the high-order vacuum near-axis expansion makes a convergent domain and remainder essential. [Ruth, Jorge and Bindel, §§3–4](https://arxiv.org/abs/2411.04352)

## Outputs and next dependencies

The first deliverable is a useful certified horizon on a stated band, or a verified nonzero mean ruling out the proposed periodic correction there. Use that band as input to the [P1 energy-loss estimate](../goals/probabilistic-goals-and-techniques.md#32-first-technique-deterministic-orbit-enclosures-plus-integration). With collisions, a new stopped-process argument must control the generator, including its diffusion term. The loss fraction, a bounce-drift bound and a neoclassical heat flux have different dependencies.
