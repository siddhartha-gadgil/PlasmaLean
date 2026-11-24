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

The first forward tube now contains a true solution from the actual Q-16 section state at u=0.470. Lean bounds the dimensionless reference error by 1.23 × 10⁻⁶ throughout [0,1/64]. Two further endpoint defect proofs cover separated slabs. Exact external arithmetic passes all 6,256 central defect budgets. [First physical moving-frame step](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-first-physical-step.md)

All 6,256 Jacobian budgets pass an exact sparse-polynomial screen on their full trial tubes. A Hilbert-space projection now lets the Lean step use this same ball for both regularity and the quantitative bound. [Screen and sufficient long-trace theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-full-frame-budgets.md)

A single Q-16-launched physical solution now traverses two consecutive forward slabs at radius 0.470. It reaches 1/32 radian, stays within 1.232 × 10⁻⁶ of the corresponding dimensionless coordinates, and satisfies the ODE at the internal join. [Two-slab theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-two-physical-slabs.md)

The connected forward proof now reaches 1/4 geometric radian at radius 0.470. Lean bounds the reference error by 1.344 × 10⁻⁶ across 16 consecutive slabs. A separate two-sided signed-angle solution covers [−1/64,1/64]. [Sixteen-slab theorem and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-quarter-radian-trace.md)

At the same radius the verified forward trajectory now reaches 21/32 radian through 42 slabs with error below 1.817 × 10⁻⁶. One signed trajectory covers [−1/32,1/32] with error at most 1.232 × 10⁻⁶. Both estimates are for the magnetic field line in dimensionless coordinates. [Signed passage and 42-slab replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-signed-four-slab-trace.md)

At the same endpoint all 782 central reference defects have passed Lean. A true field line now reaches one radian forward, and a joined solution follows 64 slabs in each direction from one birth on [−1,1]. Both dimensionless position errors are below 2.166 × 10⁻⁶. [Proofs and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-one-radian-and-signed-trace.md)

On any two finite measured wells, the clipped single-passage action difference is at most the largest sublevel-length difference times the largest possible parallel speed. The theorem is sharp and yields an action derivative bound under a local Lipschitz hypothesis on the sublevel lengths. [Theorem and hypotheses](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/bounce-action-sublevel-arclength.md)

The finite-sample theorem gives an explicit mesh correction for comparing well actions. A counterexample has identical lengths at two thresholds and different actions. Exact regrouping of the eight N-60 endpoint packets retained all directed action comparisons using 253–433 adaptive speed intervals. [Finite estimates, example and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/finite-sublevel-action-comparison.md)

The three projected Jacobian certificates on rows 69–71 extend the physical solution to 9/8 radian. The uniform position error is below 2.214 × 10⁻⁶. [One-and-one-eighth-radian theorem and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-projected-physical-trace.md)

The backward proof reuses the projected rectangles via a reflection lemma. A single signed trajectory now covers [−9/8,9/8] with the same uniform error bound. [Signed theorem and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-signed-projected-trace.md)

The signed trajectory reaches ±3/2 radians across 192 slabs. The physical steps on the isolated slab 226 also pass in both directions with two closed vertical half-boxes. [Signed interval, spatial cover and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-signed-trace-spatial-split.md)

Both proposed mirror heights now have actual field-line level contacts from their local entrance ellipsoids in both clock directions. A proved criterion expresses earliest contact from launch in terms of the intervening tube signs. [Four local contacts and their hypotheses](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-mirror-level-contact.md)

Lean checks the widths and strict action comparisons for all eight adaptive speed grids, totaling 2,655 cells. Each physical action conclusion assumes directed arclength bounds at its own nodes. [Exact tables, assumptions and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-adaptive-action-grids.md)

Every admitted Q-16 birth stays below both mirror heights on one physical field line throughout [−3/2,3/2]. The theorem joins 192 closed-tube signs, including their common endpoints. A 128-slab-per-direction trajectory also reaches ±2 radians with the same position-error cap. [Signed submirror trajectory and exact replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-signed-submirror-trace.md)

A measured-partition theorem bounds sublevel arclength directly from panel speeds and weights. Two actual grid thresholds now follow from the original directed time-panel cover, with all 31,200 and 31,392 time cells included respectively. [Threshold ties, hypotheses and proofs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/physical-sublevel-arclength-from-time-panels.md)

Outward growth of squared field strength now makes all four local level crossings unique and transverse. The signed trajectory stays below both heights through ±2 radians. [Quantitative slopes, uniqueness and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-transverse-physical-mirror-brackets.md)

A verified threshold tree now connects all 250,848 original time cells to every adaptive action node at all eight endpoints. The physical estimates still required are precisely the original per-panel speed and arclength-density bounds. [Complete archive-to-action implications](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-complete-sublevel-archive.md)

Both signed first-slab reference curves now meet their ODE defect budgets in Lean at all eight launches, including the opposite symmetry section. Jacobian transfer between neighbouring launches passed only 32 of 88 sampled cases. [Eight-launch results and proof commands](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-eight-reference-defects.md)

All 648 directed spatial signs up to the two mirror brackets have passed Lean. The remaining premise for the signed first-crossing application is physical propagation from the launch. A separate profile stability theorem localizes mirror roots and gives a sharp action estimate even at flat critical levels. [Complete signs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-complete-pre-mirror-signs.md) · [Action stability](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/mirror-profile-stability.md)

On a single physical Q-16 field line the two packed action cells beside the launch hold. The earliest cell also holds from each local backward entry. A new action estimate requires regularity only close to the mirror height and allows a critical well bottom. [Physical action cells](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-first-physical-action-cells.md) · [Mirror collar estimate](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/mirror-action-collar.md)

For field lines with distinct arclength densities, the action comparison now charges their integrated absolute density difference times maximum clipped speed. A label derivative may likewise be bounded by separate field-profile and density terms. [Changing arclength theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/mirror-action-changing-arclength.md)

The physical phase-zero trajectory from every admitted radius-0.470 birth reaches [−5/2,5/2], stays below both mirror heights and has position error below 2.216 × 10⁻⁶. [Five-radian certificate and exact replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-five-radian-birth-trace.md)

The two complete upper action blocks straddling the radius-0.470 launch now hold on one physical trajectory. All 96 original panels satisfy their pointwise physical bounds, including the version using the Cartesian derivative for actual arclength. [Complete block proofs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-two-physical-action-blocks.md)

At all eight action endpoints, one pair of certified Q-16 tori now supports the signed physical first rows. Every admissible birth reaches its section and has a single field line in the original two moving tubes for angles [−1/64,1/64]. [Signed launch theorem and exact replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-eight-signed-launches.md)

The signed radius-0.470 path reaches [−3,3] with the same error bound and remains below both mirror heights. Its dimensionless physical action on [−1/64,1/64] is less than 0.005587. For a pair of curves on a common angular interval, the norm of their cylindrical tangent discrepancy now bounds the extra action error caused by changing physical arclength. [Signed integral](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-signed-action-integral.md) · [Geometric stability](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/cylindrical-action-sensitivity.md)

Lean recovers the original rounded speed and arclength digits on both signed physical tubes at outward row 16 (blocks 308 and 341). A shared seven-harmonic model can enclose both directions. An independent exact replay preserves every digit on all 31,200 archived cells at this endpoint. [Physical panel certificates](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-native-action-panels.md)

### First regular physical mirror births at the Dommaschk pilot

For each admitted initial angle at u=0.470, the same physical field line turns at the lower and upper archived heights on both sides of the launch. Its one-way action exceeds 0.2765 between the true upper mirrors. Lean identifies the actual birth position and both accessible components and verifies the oriented arclength contract at both heights. A transport bound and thermal birth fraction remain open. [First mirror contacts from a physical birth](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-first-mirrors-from-birth.md) · [Physical action between the first upper mirrors](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-first-well-action-floor.md) · [Connected wells and actual regular mirror births](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/regular-mirror-births-and-components.md)

At both heights the one-way flight time is finite and positive. Lean proves integrability of inverse parallel speed against physical arclength, including the neighborhoods of the turning points. A numerical time interval and a conversion to seconds remain open. [Theorem and reproduction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/finite-transverse-mirror-bounce-time.md)

The same trajectory now supplies first mirrors and a finite positive one-way time at every height between the archived values. Both outward turning positions increase Lipschitz-continuously. The physical action between them equals a clipped integral on a fixed angular interval and increases strictly with height. [Uniform height-band theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-mirror-height-band.md)

On the fixed pilot launch curve, the certified rectangle of toroidal angles and mirror heights has area 1292367655761/655360000000000000000. For a family of physical field lines, a new compactness theorem shows how one transverse bracket gives positive mass when the strength and its time derivative vary continuously and the birth distribution charges open sets. Extending the physical chart to a radial and velocity range is still open. [Parameter-area and persistence theorems](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/open-mirror-wells-and-birth-area.md)

Two nonpilot launch families now have certified trajectories on both sides of their sections for 1/32 radian. They are u=0.478 near angle zero and u=0.456 near π/2. Each can be compared to the pilot using exactly the same nested tori. [Reusable continuation and proof receipts](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/continuing-endpoint-field-lines.md)

For the QA2R pilot, one-way flight time is greater than 5.925 on the whole certified height interval and less than 34000 on its upper half. The upper estimate bounds the integrable singularity at both moving first mirrors. These quantities use the normalized parallel speed and physical arclength in archive units. [Numerical flight bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quantitative-first-mirror-flight-times.md)

The two additional zero-section labels u=0.523 and u=0.531 now have two physical slabs in both directions. One spatial rectangle and one field evaluation support four signed ODE branches, with separate frame bounds for each launch. The u=0.478 trajectory reaches four verified slabs each way. [Shared harmonic Jacobians and single-core benchmark](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/shared-harmonic-endpoint-jacobians.md)

The height derivative of the physical action is the actual one-way time between the first mirrors. On every subband, integrating those times gives the exact action increment. The general compact-window theorem permits exceptional critical heights, and a flat-bottom example exhibits one. [Action, time and regularity theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/mirror-action-flight-identity.md)

At the opposite section the two archived moving frames first differ by one tick at row 129 for u=0.456. Separate signed matrices over one shared spatial field bound now certify the actual backward ODE step from every admissible row entrance. The exact external matrix screen passes all 6,256 individual cases across eight labels and both directions. [Unequal-frame theorem and its scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/independent-signed-endpoint-frames.md)

A global Bφ > 7/8 estimate on ten spatial rectangles lowers the numerical flight-time ceiling from 34000 to 592 on the upper half of the height band, and raises the lower bound from 5.925 to 14 at every height. The proof controls every angle in the entire pilot region. [Uniform field and time bounds](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/toroidal-field-and-flight-bounds.md)

At every height, including the lowest, Lean bounds the dimensionless one-way flight time between 14 and 4450. All 316 physical core slabs in each direction have positive clearance, and the two outer collars contribute less than 40 together. [Full-band flight-time proof and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/full-band-first-mirror-flight-times.md)

The second phase-zero radial label, u=0.478, now reaches six physical slabs in each direction. A verified reflection transfers the central defect while preserving the independently archived backward allowance. The corresponding test succeeds on all 391 rows in exact arithmetic. [Signed defect and physical trace](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/reflected-secondary-defect-budget.md)

Resolving the central flight-time integral one signed slab at a time gives **14 < T < 264** on the entire closed pilot height band. The 316 reciprocal-speed ceilings sum to 5916 on each branch. With the arclength factor, the central time is at most 223.986 and the two endpoint collars add less than 40. [Rowwise proof and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/rowwise-first-mirror-flight-budget.md)

At u=0.470 the full signed trajectory through every admitted birth reaches ±391/64 radians. On all 782 original slabs the Euclidean coordinate error is below 3.327 × 10⁻⁶, and the same field line has both pairs of first transverse mirrors. A fresh compilation reproduced the concrete proof. [Full signed trajectory and four contacts](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/full-signed-pilot-birth.md)

One regular field-line window for a locally smooth, nonvanishing field with transverse mirror contacts yields an open neighborhood in the full four-dimensional position-height space. Any measure that charges open sets gives these regular births positive mass. Lean constructs the neighboring trajectories by ODE existence and uniqueness. [Local smooth-flow and positive-measure theorem](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/local-flow-persistence-of-physical-births.md)

On any one of the admitted pilot trajectories, each attainable first-well action determines exactly one height in the closed band. An action difference ΔJ > 0 gives ΔJ/264 < Δh < ΔJ/14. The full action width lies strictly between 0.0072372588722616 and 0.1364740244483616. [Inverse action coordinate](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/first-well-action-height-inverse.md)

At the phase-zero pilot, the dimensionless physical action between the first upper mirrors satisfies **0.2765 < J ≤ 1146552112157123/844424930131968**, about 1.35779045744 at the upper end. All 31,200 original cells are now in the Cartesian action proof. The upper bound clears the archived target by more than 0.00213. [Complete action enclosure, exact margin and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/dommaschk-native-first-well-action-enclosure.md)

For the actual QA2R field, every admitted original pilot birth at every height in the closed band lies in the interior of the regular-birth set in Cartesian position and height. The interior therefore has strictly positive four-dimensional Lebesgue measure. A numerical volume or thermal fraction requires additional information. [Cartesian pilot application and independent replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/cartesian-open-regular-pilot-births.md)

The QA2R trapped reference now contains an open set in the five guiding-centre birth coordinates for each sign of parallel velocity. The lift works for any positive particle mass and compatible positive energy at an admitted pilot height. A birth law that charges open sets assigns each such population positive mass. The numerical fraction and radial survival time remain open. [Birth-coordinate lift, cuts and proof](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/qa2r-trapped-birth-coordinates.md)

For a family of field lines at fixed height, Lean now proves the launch-label derivative of action with both a strength term and an arclength term. Representative bounds on these derivatives give |∂ₛJ| ≤ A J + B T, where T is the one-way flight time. Evaluating these transverse derivatives on QA2R remains open. [First variation and precise regularity assumptions](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/first-variation-across-mirror-field-lines.md)

The full upper action enclosure and the 316 signed central speed bounds now meet on a single physical pilot trajectory. On it **54.98668 < T < 264** throughout the closed height band, and **T > 57.80606** at the upper height. The action cap holds at every height on the same first well. [Joint bounds, exact quotients and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/action-floor-for-first-mirror-flight-time.md)

At u=0.478 both signed physical tubes bracket the lower mirror level between 317/64 and 318/64, and the upper between 325/64 and 327/64. Along any enclosed solution the squared field magnitude increases at rate greater than 1/400 on the bracket rows. The through-birth first-contact theorem at this label still requires its full incoming trace. [Secondary mirror brackets and gradient proofs](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-qa2r-mirror-brackets.md)

An exact seven-harmonic proof checks the two physical central defects on the same u=0.478 slab in 66.50 seconds. The previous sparse forward check and its reflected partner took 166.95 seconds on that slab. The long secondary trace is using the new proof builder. The opposite section can now also run with separate certified forward and backward frames. [Harmonic defect construction, measurements and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/native-harmonic-central-defects.md)

On the pilot well, a decrease of field strength of at least 1/144 per unit radial label and a relative arclength change above −1/32 would force the radial action derivative above 1/3. Lean proves this implication. A floating-point variational screen meets both input bounds on two radial labels at the sampled angles and heights. The input bounds still require physical variational certificates. [Signed criterion and reproducible screen](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/pilot-radial-action-slope-criterion.md)

A single theorem now fixes one nested pair of physical tori for all eight endpoint sectors and their 974 signed slabs. All reach at least 5/64 radian each way, and the second pilot at u=0.478 reaches 48/64. [Eight signed traces and independent replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/eight-signed-traces-on-common-tori.md)

Each sign of the five-dimensional trapped reference contains an open set whose births admit actual local Littlejohn solutions on a positive time interval. The proof uses the identity between the effective parallel field and the strength of a nonzero vacuum field at every velocity. An application-scale horizon and the thermal fraction remain open. [Model, assumptions and independent replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/vacuum-local-littlejohn-births.md)

At u=0.478 Lean excludes a mirror throughout all 317 incoming tubes per direction. Joining the first 64 each way to the original birth proves the true field strength stays below both mirror levels throughout [−1,1] radian. The full incoming path to the brackets is still being verified. [Certificates and scope of the physical result](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-qa2r-submirror-exclusion.md)

The two signed trapped populations now share one strictly positive local time. Given any positive displacement cap, every trajectory from either selected neighborhood stays within it. For a finite measurable trapped reference, a law charging open sets and a compact nonempty axis, the covered fraction is positive. Numerical lower bounds for the time and fraction remain open. [Common local band and double replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-local-littlejohn-time.md)

The rigorously calibrated action on the pilot changes by more than 0.0284 between the archived heights. Comparing that pilot at a shifted height against the u=0.478 field line reduces a finite radial action difference to two explicit profile inequalities. Exact external arithmetic passes on all 325 pairs of original tubes, including the narrow margin on row 324. Full physical attachment and kernel replay of the paired inequalities are underway. [Finite comparison, sharp height inverse and checks](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/finite-radial-action-comparison.md)

At the original u=0.470, φ=0 birth, increasing the radial label decreases the field strength at rate at least 1/144 and increases arclength per radian. Lean attaches these physical derivatives to the same embedded tori and the same 391-slab-per-direction field line. [Radial tangent, certified signs and scope](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/pilot-radial-birth-variation.md)

All ten outer rows at u=0.478 now have verified squared-strength derivative greater than 1/400 in both directions. Any enclosed path that extends past 327/64 has two first mirrors throughout the archived height band. Each moves outward by more than 7/64 and less than 10/64 radian from the lower height to the upper height. The original birth still needs the full signed propagation to get there. [Signed slope proofs, branches and inverse derivative](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-first-mirror-height-band.md)

The original action and time bounds for the full 391-row pilot now hold on the very same embedded surfaces as all seven neighboring sectors. The common 1,046-slab snapshot includes the u=0.478 path through one radian each way. This fixes the physical geometry before any choice of launch sector or pilot angle. [Shared geometry, exact calibration and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/common-torus-pilot-action.md)

The two finite radial comparison inequalities now hold in Lean on true physical field lines through both original births for every common angle in [−1/64,1/64]. The outer strength decreases by at least 1/18000, and outer arclength per radian is at least 3999/4000 of the inner value. [Checked ranges, embedded surfaces and replay](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/paired-physical-launch-profiles.md)

Two more phase-zero radii now have true signed birth trajectories below both mirror heights. On the same embedded tori the certified half-widths are one radian at u=0.478, one half radian at u=0.523 and 5/64 radian at u=0.531. [Shared surfaces and original signed paths](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/outer-phase-zero-submirror-births.md)

Near the pilot upper mirror, row 324 had the smallest margin in the two-label screen. Lean now proves its squared-strength drop is at least 17/144000 on the true signed tubes in both directions. The external calculation passes the same physical test on all 325 rows. [Centered bound and kernel receipt](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/centered-strength-separation.md)

All eight radial and angular sectors now have a verified initial physical interval below mirror strength. At the opposite section the new intervals cover ±1/4 radian at 0.456 and ±5/64 radian at the other three radii, for every admitted launch angle. The same enclosure covers 16 original tubes each way at each of the four radii. [Opposite-section theorem and reproduction](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/opposite-section-submirror-births.md)

At the pilot upper-mirror slab, 324, Lean now proves both the field drop of 1/18000 and the arclength ratio of 3999/4000 for all pairs of points in the two physical tubes at the same angle, in both directions. The sparse arclength estimate also passed at its least favorable row, 296. [Physical arclength and field comparison](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/paired-physical-arclength.md)

For the upper-height action at u=0.478, Lean verifies that the central 322 slabs each way already carry enough archived lower mass to exceed the target by 0.00015632. Four pairs of physical tube rows, 384 original cells, now have kernel proofs. Of those, 192 are attached to the same true birth trajectory. The remaining central cells and the final passage to the first mirrors are under verification. [Exact lower quadrature and proof receipts](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/secondary-native-lower-action-cells.md)
