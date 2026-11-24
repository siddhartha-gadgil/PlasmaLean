# Annular averaged flux and finite-time confinement, 23 November 2026

## Outcome

Both stellarator vacuum examples satisfy C1 on embedded invariant tori. For the Dommaschk field, a single pair of surfaces realizes the current, transform, nesting and quasi-axisymmetry bounds. For the rational stellarator, the exact KAM torus realizes the current and transform bounds. [Embeddedness proof and applications](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/irrational-return-embedding.md)

A general confinement theorem now connects the volume-preservation equations of a periodic flow to a bound on radial motion. It applies on a regular annulus of periodic leading orbits. The averaged perturbation must have no zeros and must be tangent to the two bounding circles. For every closed interior radial birth band, the theorem constructs trajectories through time c/ε², uniformly in starting angle and phase for sufficiently small nonzero ε. [Research note N-51](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/annulus-averaged-flux.md)

## New checked results

- **Topology.** The signed radial volume flux across a core torus is the period of a closed one-form on the base annulus, up to the chosen orientation. A nonzero period rules out a winding-one invariant curve of the averaged field. With boundary tangency and nonsingularity, integrating the one-form instead constructs a smooth radial label ψ with values 0 and 1 on the two edges.
- **Averaging.** The zero-mean periodic correction g solves X₀g = −Yψ. The corrected label ψ + εg then has derivative exactly ε²Yg for X₀ + εY. For an arbitrary proposed label, the least achievable uniform first-order residual on one orbit equals the absolute value of its mean drift.
- **Choice of phase.** The flux and label descend from local charts even when the phase origin depends on position. The local corrections agree under the same rotations when the charts give the same physical period. The dynamical theorem uses a periodic coordinate representation of the total space. [Local phase charts](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusFluxDescent.lean)

### Embedded invariant tori

A torus parametrization that follows the field lines with an irrational transform is a C² embedding if its profiles are C², its poloidal angle winds once, and the field is locally C¹ at every point of the torus. A Grönwall bound on the distance between field lines carries coincident points forward by one turn. Irrational rotation and continuity turn a coincidence into a period of the entire section. Winding one forces that period to be a multiple of 2π. Applying the same bound to a difference quotient propagates a zero section tangent, which would force a constant section. [FieldTorus.embeddedTorus_of_irrational](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Contract/IrrationalTorus.lean)

| Surface | Certified absolute transform bound | Certified off-QA spectral defect |
| --- | --- | --- |
| Dommaschk C | ≥ 0.24 | ≤ 0.0063 times its absolute transform |
| Dommaschk A | ≥ 0.2386 | ≤ 0.0090 times its absolute transform |
| Rational stellarator torus A | (75+√5)/562 ≈ 0.1374 | Open for this example |

Each torus has zero net toroidal current. The Dommaschk Q-16 theorem gives embeddedness, ray ordering, both surface Boozer chart hypotheses and both defect estimates on the same pair of exact witnesses. The theorem retains the 10⁻¹² strip-distance bounds for both profiles and the common transform bound 0.2386. The rational stellarator has a separate all-time field-line confinement theorem. [Dommaschk Q-16 and singleton theorems](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/DommaschkKamEmbedded.lean) · [Rational stellarator theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Design/RationalStellaratorEmbedded.lean)

## Quantitative certificates

Let G bound |g| and K bound |Yg|. If the initial label is at least δ from both edge values, then 2|ε|G + tε²K < δ excludes an exit through time t. The model gives finite constants uniform in the initial phase and angle. In particular, for 0 < |ε| < δ/(4G), the bound holds through t = δ/(2ε²K). Every closed radial subband strictly inside the annulus has a uniform positive birth margin. [Time bound](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusConfinementBounds.lean)

On the lifted annulus, periodicity also bounds the full speed. Any partial solution inside the band stays in a compact set on a finite interval. ODE continuation therefore supplies an orbit through the full budgeted time from every permitted initial state. [Orbit existence and confinement](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusOrbitExistence.lean)

## Corrections and challenged claims

The flux obstruction concerns curves of the **averaged** field. A constant radial perturbation v gives period −v for unit volume density and illustrates the obstruction. A different example has unit instantaneous radial speed at phase zero and zero mean radial speed. For that field Lean proves that r−ε sin(2πs)/(2π) is exactly conserved. The existence of a smooth periodic phase on a particular trapped-particle band, its period, the common invariant volume and the tangency of the bounding curves all require field-specific evidence. [Computed examples](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Geometry/AnnulusFibreFlux.lean)

## Trapped birth populations

Lean now states the finite-time band form of C2 for one Littlejohn species in a specified field. It requires a positive fraction of a finite trapped birth population, existence through a positive horizon and radial control for every partial trajectory. The fraction that can exceed the tolerance is at most the uncovered fraction. A time in seconds and a fraction for the actual Dommaschk field still require physical inputs and orbit estimates. [Contract and loss bound](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Theory/Contract/TrappedBirthBand.lean)

The positive band test follows a harmonic oscillator in a synthetic quadratic mirror. An independent audit also corrected a coil claim: a circular filament can lie entirely outside a specified meridian half-space, and its field is vacuum throughout that half-space. [Model fixture](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/PlasmaLean/Sanity/TrappedBirthBand.lean) · [Audit and coil counterexample](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-11-23-annulus-embedding-audit.md)

## Dommaschk bounce screen

Refining the launch phase exposed a change of mirror well that the first 128 phases missed. A deeper pair of heights at the same action j = 1.35992219 passed two strip resolutions and gave a sampled minimum separation of 0.0523 in the launch coordinate. Lean proves the continuous crossing and winding-graph criteria. Bounding their hypotheses for every launch and selecting thermal coverage remain open. [Results, inputs and source](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-mirror-screen.md)

Over the entire deeper strip, 32,768 outward-rounded boxes establish a nonzero transverse launch flux. A separate 131,072-tube check encloses the field lines for ±1/8 geometric toroidal radian with field strength below 1.057107, clear of the lower mirror height 1.05959233. Lean proves the geometric flux formula and the ODE enclosure theorem; the candidate numbers are checked externally. [Launch and continuation bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-launch-collar.md)

On one small positive-width cell a centred polynomial trajectory now reaches the first turning points in both directions. At two mirror heights the enclosed actions lie on opposite sides of the prescribed j=1.3599221876644974. Each launch in the cell therefore has a unique mirror height at that action. Moving the launch points to a common field-line section verifies the same conclusion for a 524,288-fold wider phase interval. The full-circle construction still needs transverse action bounds. [Regular mirror cell and proof methods](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-regular-mirror-cell.md)

## Earlier results retained

The original Dommaschk certificate provides the quasi-axisymmetry estimates on each torus. Constructing a family of flux surfaces or a field-level Boozer chart throughout the intervening volume remains open. Applying the annular theorem to trapped particles also requires identifying a regular physical bounce family. [Surface defect estimates](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-qs-defect.md)

### Results from earlier runs

The October report gives the existing passing-particle, stability, vacuum fixture and synthetic slab results, including the synthetic thermal margin of 998/45 K. [October evidence and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/progress/2026-10-30-progress-15.md)

## Validation

The annular-confinement stage passed the default Lean build (11,679 jobs). Its repository axiom audit checked 52,887 project declarations. All used only the permitted foundations, propext, Classical.choice and Quot.sound. The full orbit-existence and confinement statements are both in the default import. The research note lists their declarations and hypotheses. [Annular-confinement implementation record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/annulus-averaged-flux.md#implementation-record)

For embedded C1, the default build passed with 11,731 jobs. The default axiom audit checked 53,360 project declarations. The separate on-demand build and audit included the Dommaschk applications and checked 59,706 project declarations in its import closure. The two closures overlap. Both audits allowed only `propext`, `Classical.choice` and `Quot.sound`. [Embedding proof and checks](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/irrational-return-embedding.md)

## Next boundary

The most informative candidate calculation is a signed flux or bounce-mean test on a regular band with a known period and volume. A nonzero result can eliminate a whole class of proposed corrections. A band that passes the test needs two regular bounding curves, quantitative bounds on G and K, and an estimate of the birth population it covers before it yields a physical loss time. [Trapped-particle application N-49](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/trapped-particle-momentum.md)


## Finite-pressure interface benchmark

For a periodic cylinder, the normalized interface energy of every mode is at least s²(1+|m|+κ)/80 under the close-wall and mode-multiplier hypotheses. The constant is independent of the axial period. The formulas for the Bessel ratio, exterior impedance and reduced energy enter as inputs. Transferring the bound to a torus requires a period-uniform estimate of the change in the reduced energy. [Cylinder benchmark](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/cylinder-interface-stability.md)

On the embedded Dommaschk torus A, Lean finds a point where every tangent variation with positive first-order pressure has positive mixed curvature. The proposed stability test requires negative mixed curvature everywhere. A separate external interval calculation gives the same obstruction on torus C. A different interface or control of the full quadratic energy would be needed for this finite-pressure route. [Pressure-step obstruction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-interface-obstruction.md)

## Confinement from radial face values

For one regular bounce family, two face bounds and a finite-time action budget exclude radial escape. This theorem allows several roots at the target action. A separate theorem gives a winding graph under positive radial derivative at every target crossing. Both criteria are proved in the default Lean library. The physical orbit must still be related to the chosen action and radial observable. [Face estimates and winding graphs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/action-faces-and-winding.md)

Two radial face estimates hold on six positive-width launch sectors in the physical Dommaschk field. The interval calculation uses a moving frame to control trajectory error and can use one-sided action bounds even on sectors where turning-point orientation is unresolved. A compiled counterexample shows that well mergers can make the launch-connected action jump. [Candidate results and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-phase-faces.md)

## Fixed-action curves on two phase sectors

For every phase within 1/4096 radian of 0 or π/2, two unique roots in disjoint radial brackets realize the prescribed action. Their radial separation exceeds 9/200. The abstract continuity and secant theorems are compiled in Lean, and sixteen external interval tubes plus eight endpoint calculations supply the candidate data. The two sectors have total angular length 1/1024 radians in the period π. The dimensional excursion, thermal birth fraction and physical time remain open. [Intervals, audit and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-local-action-graphs.md)

## Mirror certificate replay, 24 November 2026

All 28 endpoint modules passed the workstation replay. Building in memory-aware batches of six after splitting the large declarations gave a measured service peak of 2.8 GiB with existing compiled dependencies. The default and on-demand axiom audits passed for 53,987 and 80,912 declarations respectively.

The nested Dommaschk launch theorem now reaches 1/64 geometric radian from every point in each of the two specified symmetry sectors. For a complete mirror passage, Lean checks 28 directed quadrature comparisons from pointwise field and arclength bounds. The four radial brackets use 16 tiles and 12,512 directed time slabs. Identifying the physical trajectory and its first variation on the full 6.1-radian trace remains open. [Verification record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-mirror-certificate-replay.md)

### Long-trace witness

For the phase-zero radius 0.470, exact external replay covers 391 slabs in each direction. The general Lean gluing theorem passes the actual exit of each slab to the next one. The physical tangent theorem identifies the arclength density used by the action. Linking every slab to the physical trajectory in Lean remains open. [Long-trace verification record](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-long-trace-witness.md)

At all eight local-action endpoints, 16 independent directed traces now reproduce the archived crossings and action bounds over 6,256 exact steps. The physical Lean theorem still reaches 1/64 radian in both directions across both launch sectors. [Eight-endpoint verification](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-eight-long-traces.md)

Lean now verifies physical entry on sub-sectors at all eight radii, the 6,256 scalar frame steps, and the angular harmonics through 391/64 radians. On the first forward slab at radius 0.470 it proves the discrepancy between physical velocity and the reference derivative is at most 10⁻¹² radially and 10⁻¹³ vertically. The spatial Jacobian on the trial tube is the next physical estimate. [Physical proof and exact scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-physical-frame-trace.md)
