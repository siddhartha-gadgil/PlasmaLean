# Annular stream functions and second-order confinement for periodic flows

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-51` |
| Title | A radial invariant constructed from the averaged flux |
| Kind | Method and formalization for N-49 |
| Addresses | Q-35, Q-1, Q-29(c), G-6 |
| Depends on | N-49 for the periodic correction and the physical motivation |
| Dependency requirement | The geometric theorem starts from smooth fields, common invariant volume and a regular annulus of oriented periodic orbits. It has no stellarator or numerical input. |
| Produces | A normalized stream function, an obstruction to a separating invariant curve, and a quantitative exit estimate |
| Difficulty | Moderate in periodic coordinates. Application to a physical band requires separate geometric evidence. |
| Status | Lean verified for periodic phase coordinates. The flux and stream also descend from local phase charts. The physical application is open. |
| Lean evidence | Default library, declarations and examples below |
| Audit evidence | Default build and axiom audit passed (52,887 project declarations). Uniform and oscillatory fields test the flux sign and cancellation. The last repository-wide domain audit predates N-51. |
| Last updated | 23 November 2026. Proved the annulus results and the sharp obstruction to a periodic correction. |

## Purpose and hypotheses

Let the oriented periodic orbits of a smooth nowhere-zero vector field X₀ form the fibres of a smooth circle bundle over the closed annulus A. The physical period T is smooth and positive. Work on a collar so smooth data and trajectories extend up to both edges. Let Y and X₀ preserve a positive smooth volume form ν. For each fibre take the physical time average of the projected Y to obtain a vector W on A. Angles below are in turns. The exit event is reaching either edge in the base.

## Theory development and claims

1. **Complete mathematical proof — radial coordinate.** Fibre integration gives an area form σ on A. In phase coordinates (θ,r,s), the fast field is ∂s/T and the volume density is independent of s by invariance. The flux one-form obtained by integrating the contraction of ν by Y along the phase is the contraction of σ by W (base orientation dθ∧dr). The divergence equation integrates to closedness because the s-derivative of the phase flux has zero integral. If W is tangent to both edges, the period of this closed one-form vanishes on a boundary circle, which generates first homology. Its primitive J is constant on each edge. If W is nowhere zero, J has no critical point, so compactness implies distinct boundary values. Normalize J to obtain ψ with range [0,1] and edge values 0 and 1. Its differential annihilates W. On the angular cover, the change of J across a deck turn is exactly the core period. This gives the primitive and the obstruction using the same calculation.
2. **Complete mathematical proof — corrector and exit.** Pull ψ back to Ψ on the total space and put f=YΨ. Its fibre mean is zero by the preceding identity. Let g be the zero-mean periodic primitive solving X₀g=−f. In the phase lift integrate the centred drift and subtract the resulting primitive’s mean, then multiply by the physical period. The intrinsic circle-action version integrates against the phase over a full turn. For Xε=X₀+εY the derivative of Ψ+εg is exactly ε²Yg. If δ≤Ψ(0)≤1−δ, then the strict bound 2|ε| sup|g|+t ε² sup|Yg|<δ excludes a first hit through time t. The bounds are required only up to a putative first hit. The estimate applies first to partial solutions. In a periodic phase chart their lifted speed is bounded on the closed band. Through a finite horizon they therefore stay in a compact ball intersected with that band. Forward ODE continuation gives an actual solution through the full budgeted time.
3. **Complete mathematical proof — obstruction.** Without tangency, the period of the same closed flux form pairs with the oriented homology class of a core circle. Along a lifted winding-one invariant loop its integral vanishes pointwise. Nonzero flux therefore rules out such a loop. In the product example X₀=∂s and Y=∂r, the core period is −1 for the stated base orientation. The perturbed radial speed is ε and crossing the unit interval takes 1/ε for ε>0.

## Sources and related work

The three statements were proposed in the PlasmaLean discussion of 23 November 2026. The first and third use fibre integration, closed one-forms and the annulus period. The periodic homological equation is classical. See Avendaño Camacho and Vorobiev, *Homological Equation for Tensor Field and Periodic Averaging*, for the averaging operator and its inverse on zero-mean data. Burby and Squire treat higher-order invariants in nearly periodic Hamiltonian systems. The present first correction requires common invariant volume and the averaged tangency hypotheses. [Periodic averaging](https://arxiv.org/abs/1302.3635) · [Hamiltonian adiabatic invariants](https://arxiv.org/abs/2005.00634)

## Application and readiness

A field-specific result needs a regular annular family of mirror bounces, a smooth positive period and common invariant volume for the chosen splitting, and two bounding curves tangent to the averaged drift. Excluded pitch ranges, degenerating wells and separatrices need their own exit analysis. Compare a resulting scaled horizon with accumulation of instantaneous radial drift for the same birth set. These are open tasks. [N-49](trapped-particle-momentum.md)

## Choosing what to compute

For a proposed annulus, test the signed radial flux through one core torus first. A certified nonzero value rules out every winding-one invariant curve of the averaged field in that collar. A zero value gives a single-valued primitive. One must still find two regular bounding levels and check that the averaged field has no zero between them. Requiring tangency on two arbitrarily chosen radii would be unnecessarily restrictive. If two regular bounding curves can be exhibited, straighten them and apply the theorem in that annulus.

For a proposed label on an individual bounce orbit, the absolute mean drift is exactly the smallest possible uniform first-order residual over periodic corrections. Improving a trial function beyond that bound requires changing the label or the orbit family. Once a band passes both geometric tests, bound the correction and its derivative there and compare the resulting time with the direct first-order estimate. An abstract finite bound by compactness gives a scaling law. A time in seconds requires numerical or analytic bounds in physical units.

The local kinetic brief supplies a complementary way to aggregate a deterministic exit guarantee over a birth distribution. The geometric theorem supplies the deterministic event only. The brief’s split into a controlled core and tails becomes relevant once a band, time, birth energy weight and model errors have all been specified. [Local kinetic source, deterministic certificate](../../sources/fusion_complex_geometry_reproducibility/continuation_kinetic.tex) · [Birth distributions and loss](../goals/probabilistic-goals-and-techniques.md)

## Implementation record

The following declarations enter through the default `PlasmaLean` import.

| Result | Lean declaration and evidence |
| --- | --- |
| A winding-one lift measures the core period. A nonsingular closed flux with tangential kernel on both edges gives a smooth submersion with edge values 0 and 1. | `ClosedFlux.integral_eq_period_of_winding`, `ClosedFlux.exists_normalized_stream`. [AnnulusStream](../../PlasmaLean/Theory/Geometry/AnnulusStream.lean) |
| Averaging the three-dimensional continuity equation gives the closed form. Its core period is minus the signed radial volume flux with the stated orientation. | `VolumeChart.fibreMean_eq_timeAverage`, `VolumeChart.closedFlux_apply`, `VolumeChart.period_eq_torusFlux`, `VolumeChart.torusFlux_zero_of_winding`. [AnnulusFibreFlux](../../PlasmaLean/Theory/Geometry/AnnulusFibreFlux.lean) |
| The form and the stream can be constructed from local phase charts. The averaged field and form agree across choices of phase origin and atlas. | `VolumeAtlas.eqOn_of_phaseMatch`, `VolumeAtlas.exists_normalized_invariant`. The assumptions specify an open cover and the transformation law for projected velocity and density. With equal physical periods on overlaps, `VolumeAtlas.corrector_overlap` and `corrector_deck` also identify the zero-mean local corrections. [AnnulusFluxDescent](../../PlasmaLean/Theory/Geometry/AnnulusFluxDescent.lean) |
| Periodic correction and optimal residual | `PhaseAction.hasDerivAt_corrector_physical` and `Lifted.exists_periodic_residual_bound_iff`. Smooth dependence is proved for the circle action on a boundaryless manifold and separately on the lifted collar. [PeriodicOrbitCorrector](../../PlasmaLean/Theory/Geometry/PeriodicOrbitCorrector.lean) |
| Construction and exact dynamics | `VolumeChart.exists_correctedStream` constructs ψ and g. `CorrectedStream.orbit_derivative` gives the exact second-order identity and `CorrectedStream.excludes_first_hit` tests a proposed edge hit. `CorrectedStream.exists_uniform_birth_margin` gives every closed interior radial subband a common positive margin across all initial angles. [AnnulusConfinement](../../PlasmaLean/Theory/Geometry/AnnulusConfinement.lean) · [Integrated displacement](../../PlasmaLean/Theory/Geometry/AveragedConfinement.lean) |
| Horizon for every supplied solution | `VolumeChart.exists_confinement_window` chooses ψ and constants G,K before the initial orbit and perturbation. `ConfinementWindow.inverse_square` gives the whole interval for perturbation magnitude below δ/(4G) and 0 ≤ t ≤ δ/(2ε²K) for ε ≠ 0. The first-hit argument only uses the ODE while the trajectory is in the closed band. [AnnulusConfinementBounds](../../PlasmaLean/Theory/Geometry/AnnulusConfinementBounds.lean) |

**Uniform existence and confinement.** Fix 0 < a ≤ b < 1 under the volume, tangency and nonsingularity hypotheses above. There exist c > 0 and ε₀ > 0 such that for each 0 < |ε| < ε₀ and *every* initial state over a ≤ r ≤ b, the lifted ODE has a solution through time c/ε² and its radius stays in (0,1) throughout. The constants precede the choice of perturbation, initial angle and initial phase. One can take c = δ/(2K) and ε₀ = δ/(4G) for the common birth margin δ. The additive-budget theorem also covers ε = 0. These are `VolumeChart.exists_inverse_square_orbits` and `VolumeChart.exists_confined_orbits`. The full orbit theorem is formulated in a periodic phase chart. An intrinsic total-space formulation for trajectories crossing arbitrary charts is open. [AnnulusOrbitExistence](../../PlasmaLean/Theory/Geometry/AnnulusOrbitExistence.lean)

For a uniform radial perturbation of speed v and unit volume density, `uniformDrift_period` gives core period −v. In `oscillatoryShear`, Y has radial component cos(2πs), which is 1 at phase zero and has mean zero. With fast phase speed 1, `oscillatoryShear_corrected_constant` proves exact conservation of r−ε sin(2πs)/(2π). Both examples use analytic identities. [Examples](../../PlasmaLean/Theory/Geometry/AnnulusFibreFlux.lean)
