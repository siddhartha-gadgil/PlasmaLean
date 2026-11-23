# Annular averaged flux and finite-time confinement, 23 November 2026

## Outcome

A general confinement theorem now connects the volume-preservation equations of a periodic flow to a bound on radial motion. It applies on a regular annulus of periodic leading orbits. The averaged perturbation must have no zeros and must be tangent to the two bounding circles. For every closed interior radial birth band, the theorem constructs trajectories through time c/ε², uniformly in starting angle and phase for sufficiently small nonzero ε. [Research note N-51](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/annulus-averaged-flux.md)

## New checked results

- **Topology.** The signed radial volume flux across a core torus is the period of a closed one-form on the base annulus, up to the chosen orientation. A nonzero period rules out a winding-one invariant curve of the averaged field. With boundary tangency and nonsingularity, integrating the one-form instead constructs a smooth radial label ψ with values 0 and 1 on the two edges.
- **Averaging.** The zero-mean periodic correction g solves X₀g = −Yψ. The corrected label ψ + εg then has derivative exactly ε²Yg for X₀ + εY. For an arbitrary proposed label, the least achievable uniform first-order residual on one orbit equals the absolute value of its mean drift.
- **Choice of phase.** The flux and label descend from local charts even when the phase origin depends on position. The local corrections agree under the same rotations when the charts give the same physical period. The dynamical theorem uses a periodic coordinate representation of the total space. [Local phase charts](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusFluxDescent.lean)

## Quantitative certificates

Let G bound |g| and K bound |Yg|. If the initial label is at least δ from both edge values, then 2|ε|G + tε²K < δ excludes an exit through time t. The model gives finite constants uniform in the initial phase and angle. In particular, for 0 < |ε| < δ/(4G), the bound holds through t = δ/(2ε²K). Every closed radial subband strictly inside the annulus has a uniform positive birth margin. [Time bound](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusConfinementBounds.lean)

On the lifted annulus, periodicity also bounds the full speed. Any partial solution inside the band stays in a compact set on a finite interval. ODE continuation therefore supplies an orbit through the full budgeted time from every permitted initial state. [Orbit existence and confinement](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusOrbitExistence.lean)

## Corrections and challenged claims

The flux obstruction concerns curves of the **averaged** field. A constant radial perturbation v gives period −v for unit volume density and illustrates the obstruction. A different example has unit instantaneous radial speed at phase zero and zero mean radial speed. For that field Lean proves that r−ε sin(2πs)/(2π) is exactly conserved. The existence of a smooth periodic phase on a particular trapped-particle band, its period, the common invariant volume and the tangency of the bounding curves all require field-specific evidence. [Computed examples](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusFibreFlux.lean)

## Earlier results retained

The Dommaschk vacuum candidate has certified tori and bounds on quasisymmetry defect at those tori. A theorem on thermal or trapped particles throughout a volume requires further geometric and dynamical input. [Candidate evidence](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-qs-defect.md)

### Results from earlier runs

The October report gives the existing passing-particle, stability, vacuum fixture and synthetic slab results, including the synthetic thermal margin of 998/45 K. [October evidence and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md)

## Validation

The default Lean build passed (11,679 jobs). The repository axiom audit checked 52,887 project declarations. All used only the permitted foundations, propext, Classical.choice and Quot.sound. The full orbit-existence and confinement statements are both in the default import. The research note lists the individual declarations and their hypotheses. [Implementation record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/annulus-averaged-flux.md#implementation-record)

## Next boundary

The most informative candidate calculation is a signed flux or bounce-mean test on a regular band with a known period and volume. A nonzero result can eliminate a whole class of proposed corrections. A band that passes the test needs two regular bounding curves, quantitative bounds on G and K, and an estimate of the birth population it covers before it yields a physical loss time. [Trapped-particle application N-49](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/trapped-particle-momentum.md)
