# Literature and source-extraction guide

These are entry points for a coding agent, organized around the theorem backlogs in this directory. Prefer the primary paper, author's manuscript, publisher record, or official software documentation. Read the source before importing a theorem: a review, numerical demonstration, or bibliography entry does not supply missing hypotheses.

The guide was assembled on 2026-10-10. Publication metadata and primary entry points were checked where accessible; it is not a claim that every full text has been audited. Exact theorem/equation locators must be recorded during extraction, rather than invented from an abstract. Links to arXiv are unversioned entry points: pin the version actually used.

**Revision of 30 October 2026.** The guide is now organized also by clause of the stellarator contract (C1–C5; see the [implementation plan](../implementation-plan.md#the-stellarator-contract-30-october-2026)). It adds the 2026 Grad counterexamples, the quasisymmetry and omnigeneity sources, and a list of the sources the compiled library actually depends on, with the declarations that use them. **Locator convention:** a locator (theorem, equation, page) is marked *verified* only when a project note or audit record states that it was read in the source. Otherwise it is marked *locator not verified*. Bibliographic details marked *unverified* are from memory or secondary notes and must be checked against the publisher record before a Lean statement cites them.

## Contents

- [Source extraction protocol](#source-extraction-protocol)
- [Literature by contract clause](#literature-by-contract-clause)
- [Sources the compiled library uses](#sources-the-compiled-library-uses)
- [Geometry, equilibrium, and symmetry](#geometry-equilibrium-and-symmetry)
- [Grad conjecture counterexamples and quasisymmetry (2026 sources)](#grad-conjecture-counterexamples-and-quasisymmetry-2026-sources)
- [Omnigeneity and thermal-particle transport (contract clause C2)](#omnigeneity-and-thermal-particle-transport-contract-clause-c2)
- [Evolution, regularity, and turbulence proxies](#evolution-regularity-and-turbulence-proxies)
- [Stability and kinetic theory](#stability-and-kinetic-theory)
- [Validated computation and analysis](#validated-computation-and-analysis)
- [Design algorithms and software](#design-algorithms-and-software)
- [Engineering, materials, and experiment](#engineering-materials-and-experiment)
- [Reading order and theorem targets](#reading-order-and-theorem-targets)

## Source extraction protocol

For each imported result, record:

1. Authors, title, year, DOI/arXiv version, stable URL, and access date.
2. Exact theorem, section, equation, or page, including any erratum.
3. Model, units, coordinate normalization, domain, boundary conditions, regularity, and parameter range.
4. All quantifiers and nondegeneracy/positivity assumptions; identify hidden existence, uniqueness, spectral, or convergence assumptions.
5. The precise conclusion and whether it is exact, asymptotic, conditional, numerical, or empirical.
6. The proposed Lean statement, definition correspondence, required Mathlib lemmas, and a sanity example.
7. Any gap between the source result and the desired design contract.

For data, additionally record material grade, experimental conditions, processing/version, uncertainty interpretation, interpolation domain, and conservative envelopes. For software, pin the release/commit, input conventions, normalization, and source of numerical error. A solver's self-reported residual is candidate data until its enclosure is checked.

## Literature by contract clause

The table maps each clause to the entries below and to the open questions of the research graph (plan RG.2). An entry can serve several clauses.

| Clause | Main sources (keys below) | PlasmaLean status (30 October 2026) |
| --- | --- | --- |
| **C1** current-free rotational transform | Boozer81, Dommaschk86, LS19, LP22, Helander14 | Vacuum C1 witness compiled (`RationalStellarator.field_vacuum`, `rationalStellarator_confined_forever_exists`, KAM sources FHL17 and ELPS Thm 6.2). ι on a family of tori and net current are open (Q-21); Landreman families carry net current (Q-18) |
| **C2** omnigeneity for thermal particles | Helander14, CS97, HM75, LC12, PLH19, NKKH99, SFINCS14, BKM20, CDG21 | Adjacent only: `WeakQS`, `qsDefect` (after CDG21 Definition 1), `boozerGC_trapped`, `helicalMomentum_conserved`. Bounce-averaged drift, omnigeneity and ε_eff not in Lean (Q-21, Q-19); bridge QS ⇒ omnigeneity open (Q-23) |
| **C3** MHD stability at finite β | BFKK58, Freidberg14, LJ20, CHT78, DG83, Newcomb60 | Mercier, ballooning (reductions supplied) and Newcomb (reduced form supplied) compiled on test beds that fail C1 |
| **C4** existence | ELPS, Landreman26, GLT26, ICLT26, MRxMHD12, CDG21, FHL17 | KAM torus of the vacuum field; Landreman families 1 and 2 (current-carrying); stepped pressure (Q-14) and current-free finite β (Q-20) open |
| **C5** thermal performance | BH92-reactivity, ISS04, IPB98, MPH22, W7X-transport21, NKKH99 (via ε_eff) | Tokamak model (Solov'ev) and 0-D windows; Stellaris ISS04 obstructions proved; C2-derived neoclassical losses open (Q-22); wall limits in [07](07-materials-and-engineering.md) |
| Infrastructure (not design progress) | Landreman26, GLT26, ICLT26, ELPS | `family1_grad_counterexample` (Q-17) |
| Evolution (G-7) | PT19, KSY25 | Not started (Q-7, Q-8) |

## Sources the compiled library uses

These sources stand behind compiled definitions or supplied model laws. The model audit of 30 October re-derived each model definition against its source ([model audit](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/audit/2026-10-30-model-audit.md)). A model law is a hypothesis of every claim that uses it.

| Source | Used for (Lean) | Locator |
| --- | --- | --- |
| **Littlejohn83**; Cary–Brizard (2009), Reviews of Modern Physics 81, 693 (*unverified*) | `LittlejohnOrbit` (guiding-centre equations, supplied model) | equations re-derived in the model audit; page/equation locators not verified |
| White–Boozer (1982), Boozer guiding-centre Lagrangian in magnetic coordinates (*bibliographic details unverified*); **Boozer81** | `BoozerGCOrbit`, `BoozerGCOrbitOn`, `BoozerField` | Euler–Lagrange equations re-derived in the model audit; locator not verified |
| **LJ20.** M. Landreman and R. Jorge (2020), *Magnetic well and Mercier stability of stellarators near the magnetic axis*, Journal of Plasma Physics 86, 905860510 (*journal details unverified*) | `mercierIndex`, `MercierStable` | eq. (3.1), as recorded in the model audit |
| **CHT78.** Connor, Hastie and Taylor (1978), Physical Review Letters 40, 396; **DG83.** Dewar and Glasser (1983), Physics of Fluids 26, 3038 (*both unverified*) | ballooning `LineData`, `LineData.Stable` (reduction supplied) | locator not verified |
| **Newcomb60.** W. A. Newcomb (1960), *Hydromagnetic stability of a diffuse linear pinch*, Annals of Physics 10, 232 (*unverified*); **Freidberg14** | `coefF`, `coefG`, `ModeStable`, `NewcombReduction` (screw pinch) | Freidberg's form checked in the model audit; chapter/equation locator not verified |
| **BH92-reactivity** | `BoschHaleDT`, `BoschHaleFine` (D-T reactivity enclosures, supplied data) | fit recomputed from the published coefficients in the model audit |
| **ISS04.** H. Yamada et al. (2005), Nuclear Fusion 45, 1684, [DOI: 10.1088/0029-5515/45/12/024](https://doi.org/10.1088/0029-5515/45/12/024); **IPB98.** ITER Physics Basis (1999), Nuclear Fusion 39 (*page unverified*) | `ConfinementLaw`, `stellarisLaw` (`Design/BurnWindowStellarator`); IPB98(y,2) in the M1 burn window | ISS04 from [stellarator-burn-parameters.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/stellarator-burn-parameters.md); IPB98 eq. (20) as recorded in the model audit |
| **Landreman26** | `LandremanEquilibrium.family1`, family-2 modules, `family1_grad_counterexample` | formulas checked by compiling them; section locators in [grad-conjecture.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grad-conjecture.md) |
| **CDG21** | `WeakQS`, `qsDefect` | Definition 1, eqs. (1.7)–(1.9): verified (N-27) |
| **FHL17**, **ELPS** Thm 6.2 | explicit-constant KAM theorem behind `torusA_exact` and `rationalStellarator_confined_forever_exists` | verified in [kam-route.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/kam-route.md) |

## Geometry, equilibrium, and symmetry

- **Boozer81.** A. H. Boozer (1981), *Plasma equilibrium with rational magnetic surfaces*, Physics of Fluids 24, 1999–2003. [DOI: 10.1063/1.863297](https://doi.org/10.1063/1.863297). Starting point for magnetic-coordinate conventions. Translate flux and angle normalization explicitly; construct charts on an annulus and handle the axis separately. In PlasmaLean the Boozer guiding-centre model is stated on the chart ψ > 0. Orbits that reach the axis are excluded (audit MA-M1), so coordinates through the axis remain open.

- **GB91-field.** D. A. Garren and A. H. Boozer (1991), *Magnetic field strength of toroidal plasma equilibria*, Physics of Fluids B 3, 2805–2821. [DOI: 10.1063/1.859915](https://doi.org/10.1063/1.859915). Extract near-axis expansion equations, ordering, and equilibrium compatibility conditions.

- **GB91-existence.** D. A. Garren and A. H. Boozer (1991), *Existence of quasihelically symmetric stellarators*, Physics of Fluids B 3, 2822–2834. [DOI: 10.1063/1.859916](https://doi.org/10.1063/1.859916). Extract the actual source-specific restrictions; do not turn a generic overdetermined expansion into a universal nonexistence claim.

- **LS19.** M. Landreman and W. Sengupta (2019), *Constructing stellarators with quasisymmetry to high order*. [arXiv:1908.10253](https://arxiv.org/abs/1908.10253); [publisher full text](https://www.cambridge.org/core/journals/journal-of-plasma-physics/article/constructing-stellarators-with-quasisymmetry-to-high-order/A7D61D398C54B95EB3881F499457D4B7). Use the explicit near-axis construction and **Appendix A**, which identifies corrections and convention changes relative to the original Garren–Boozer formulas. Prove coefficient identities first; convergence and remainder bounds are separate targets. Under the contract, the plan does not pursue a near-axis remainder route to exact quasisymmetry (see RJB25). The near-axis QA field `reactorQA` is used as a model field for the passing-alpha results.

- **BKM20.** J. W. Burby, N. Kallinikos, and R. S. MacKay (2020), *Some mathematics for quasi-symmetry*, Journal of Mathematical Physics 61, 093503. [arXiv:1912.06468](https://arxiv.org/abs/1912.06468). Useful for geometric definitions, reduced dynamics, and conservation laws. Extract which notion of quasisymmetry and which guiding-centre approximation each theorem uses. Frames quasisymmetry as an integrability property; the Garren–Boozer conjecture is neither proved nor disproved there.

- **ELPS.** A. Enciso, A. Luque, and D. Peralta-Salas, *MHD equilibria with nonconstant pressure in nondegenerate toroidal domains*, Journal of the European Mathematical Society 27 (2025), 2251–2291. [DOI: 10.4171/JEMS/1410](https://doi.org/10.4171/JEMS/1410); [arXiv:2104.08149](https://arxiv.org/abs/2104.08149). A rigorous existence reference involving piecewise-smooth equilibria and invariant structures. Preserve the interface regularity and nondegeneracy assumptions instead of claiming a global smooth nested equilibrium.

- **CDG21.** P. Constantin, T. D. Drivas, and D. Ginsberg (2021), *On quasisymmetric plasma equilibria sustained by small force*, Journal of Plasma Physics 87, 905870111. [Publisher record](https://www.cambridge.org/core/journals/journal-of-plasma-physics/article/abs/on-quasisymmetric-plasma-equilibria-sustained-by-small-force/AAB0DCC82FDBD028AE1F26841E583CA1); [arXiv:2009.08860](https://arxiv.org/abs/2009.08860). The additional force is part of the result. Quantifying or removing it requires another argument. Theorems 1.1–1.2 and eq. (1.24) give the small-force near-quasisymmetric equilibria; the weak-quasisymmetry definition used in PlasmaLean (`WeakQS`) follows its Definition 1. The paper states (p. 7) that it is unknown whether quasisymmetry can be achieved in a volume. This open problem is Q-24 in the research graph; the design path does not depend on it.

- **MRxMHD12.** S. R. Hudson et al. (2012), *Computation of multi-region relaxed magnetohydrodynamic equilibria*, Physics of Plasmas 19, 112502. [DOI: 10.1063/1.4765691](https://doi.org/10.1063/1.4765691); [arXiv:1211.3072](https://arxiv.org/abs/1211.3072). Defines a useful stepped-pressure/relaxed model and SPEC computation. Formalize interface conditions and distinguish this model from smooth ideal MHD.

- **LP22.** M. Landreman and E. Paul (2022), *Magnetic fields with precise quasisymmetry for plasma confinement*, Physical Review Letters 128, 035001. [DOI: 10.1103/PhysRevLett.128.035001](https://doi.org/10.1103/PhysRevLett.128.035001); [arXiv:2108.03711](https://arxiv.org/abs/2108.03711). Numerical candidates and useful quantitative targets; numerical precision does not establish exact quasisymmetry or an all-orbit confinement theorem.

- **EPS-relaxation.** A. Enciso and D. Peralta-Salas, *Obstructions to Topological Relaxation for Generic Magnetic Fields*. [arXiv:2308.15383](https://arxiv.org/abs/2308.15383); [DOI: 10.1007/s00205-024-02078-5](https://doi.org/10.1007/s00205-024-02078-5). Read the precise genericity, topology, and relaxation class before assuming arbitrary magnetic data can be relaxed to the desired equilibrium.

## Grad conjecture counterexamples and quasisymmetry (2026 sources)

Collected from [grad-conjecture.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/grad-conjecture.md) and [quasisymmetric-solution.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quasisymmetric-solution.md) (30 October 2026). Under the stellarator contract (see the [implementation plan](../implementation-plan.md#the-stellarator-contract-30-october-2026)), Grad counterexamples are mathematical infrastructure: non-axisymmetry is a consequence of a current-free rotational transform, not a design goal. Exact quasisymmetry on a volume remains open (CDG21, BKM20).

- **Landreman26.** M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces*. [arXiv:2609.26742](https://arxiv.org/abs/2609.26742) (v1 22 September, v2 28 September 2026); code at [landreman/analytic_3d_equilibria](https://github.com/landreman/analytic_3d_equilibria). Explicit elementary closed-form non-axisymmetric MHS equilibria with exact nested flux surfaces (family 1 with ι = 2 and a non-planar axis, family 2 with sheared ι); states that it refutes Grad's conjecture as formulated in Conjecture 2.5 of Cardona et al. (2025). In PlasmaLean: `LandremanEquilibrium.family1`, `LandremanGradCounterexample.family1_grad_counterexample`, and family-2 force balance and Mercier results. Both families carry net toroidal current (plan Q-18), so they are not stellarator candidates under contract clause C1.

- **GLT26.** J. Gómez-Serrano, L. Liehr, and M. A. Taylor, *Counterexamples to Grad's conjecture*. [arXiv:2609.24739](https://arxiv.org/abs/2609.24739) (21 September 2026). Smooth MHS solutions in an embedded solid torus with nested toroidal pressure levels, symmetry group exactly the cyclic group C_N, the field vanishing on a circular axis; Nash–Moser construction. Includes a Lean 4 formalization of the main theorem at [lukasliehr/Grad-Conjecture](https://github.com/lukasliehr/Grad-Conjecture) (pins Lean v4.33.1, as recorded in grad-conjecture.md; not re-verified in this revision). PlasmaLean does not import it: its toolchain differs from PlasmaLean's (Lean v4.34.1). Its field vanishes on the circular axis, so the axis lemma `WeakQS.normB_const_of_gradient_eq_zero` (which needs B ≠ 0) does not apply, and its quasisymmetry status is unknown.

- **ICLT26.** O. Issan, J. Citrin, M. Landreman, and B. Tracey, *Analytic non-axisymmetric 3D MHD equilibria without stellarator symmetry*. [arXiv:2610.07304](https://arxiv.org/abs/2610.07304) (5 October 2026). Adds a parameter τ to both Landreman families that breaks stellarator symmetry while keeping the equilibria exact (τ = 0 recovers Landreman26). Not yet checked in PlasmaLean.

- **ELPS** (listed above). Enciso–Luque–Peralta-Salas: piecewise-smooth (stepped-pressure) MHS equilibria far from symmetry, counterexamples to Grad in the stepped-pressure setting, not smooth.

- **RJB25.** Ruth, Jorge, and Bindel, Journal of Plasma Physics 91 (2025) E73. [arXiv:2411.04352](https://arxiv.org/abs/2411.04352). The vacuum near-axis expansion is ill-posed (Theorem 3.10 in the arXiv HTML version); a regularized expansion converges (Theorem 3.13, Corollary 3.15). Check the theorem numbering against the pinned version. Reason the plan does not pursue a near-axis remainder route to quasisymmetry (Q-16 route i).

- **QS-existence (formal and partial results), from [quasisymmetric-solution.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/quasisymmetric-solution.md).** Plunk and Helander, Journal of Plasma Physics 84 (2018) 905840205, [arXiv:1801.02990](https://arxiv.org/abs/1801.02990): no global quasi-axisymmetry in a weakly non-axisymmetric vacuum expansion (abstract and conclusion read). Burby, Kallinikos, MacKay, Perrella and Pfefferlé, [arXiv:2403.03352](https://arxiv.org/abs/2403.03352): admissible quasisymmetries characterized. N. Sato, Scientific Reports 12 (2022) 11322, [arXiv:2204.09241](https://arxiv.org/abs/2204.09241): weakly QS non-symmetric fields with zero rotational transform in anisotropic MHD (outside the contract, since C1 needs ι > 0). Rodríguez, Helander and Bhattacharjee, [arXiv:2004.11431](https://arxiv.org/abs/2004.11431): weak quasisymmetry. Together with GB91-existence, these support the statement that exact QS in a volume is open (Q-24), with formal evidence pointing to non-existence for isotropic MHS.

- **Dommaschk86.** W. Dommaschk, *Representations for vacuum potentials in stellarators*, Computer Physics Communications 40 (1986) 203 (*bibliographic details from memory in quasisymmetric-solution.md; unverified*). Basis of explicit harmonic (vacuum) potentials, polynomial in (R, z, ln R); the proposed route (ii) to a quasisymmetric vacuum field fits a finite Dommaschk sum to a QA target. This is item 1 of the current priority order (Q-16). A vacuum field is current-free by construction (C1), and harmonicity is an identity, so only the tori, ι and the QS defect need certificates.

## Omnigeneity and thermal-particle transport (contract clause C2)

Sources for the definitions specified in [00-model-contracts.md](00-model-contracts.md) (`BounceAveragedDrift`, `Omnigenous`, `EffectiveRippleBound`; specifications, not yet compiled Lean definitions, Q-21). C2 must hold for thermal ions **and electrons**. Alpha-particle results (G-6) are one part of C2 and do not substitute for it.

- **Helander14** and **CS97** (listed under Stability and kinetic theory) are the entry points for omnigeneity and its relation to quasisymmetry.

- **NKKH99.** Nemov, Kasilov, Kernbichler, and Heyn (1999), Physics of Plasmas 6, 4622. Definition of the effective ripple ε_eff. Copy the definition exactly, including the field-line length and the normalization (reference field B₀, major radius R₀). The link from ε_eff to a 1/ν-regime diffusivity (χ ∝ ε_eff^{3/2}) is a supplied model law.

- **HM75.** J. R. Hall and B. McNamara (1975), Physics of Fluids 18, 552 (*unverified*). Usually cited as the origin of omnigeneity (the bounce-averaged radial drift vanishes for all trapped particles). *Locator not verified*; extract the definition before a Lean statement depends on it.

- **LC12.** M. Landreman and P. J. Catto (2012), *Omnigenity as generalized quasisymmetry*, Physics of Plasmas 19, 056103 (*unverified*). Characterizes omnigenous fields in Boozer coordinates. It is a candidate source for the equivalence ⟨ψ̇⟩_bounce = 0 ⟺ ∂J/∂α = 0 stated in Q-21. *Locator not verified.*

- **PLH19.** G. G. Plunk, M. Landreman and P. Helander, *Direct construction of optimized stellarator shapes. Part 3. Omnigenity near the magnetic axis*, Journal of Plasma Physics 85 (2019) 905850602, with Camacho Mata, Plunk and Jorge, Journal of Plasma Physics 88 (2022) 905880503 (journal details from N-4). Near-axis quasi-isodynamic fields. QI fields have no continuous symmetry, so no Noether invariant; they are the second C2 route besides quasisymmetry.

- **QS ⇒ omnigeneity (Q-23).** Quasisymmetry implies omnigeneity, but not conversely. The plan's route proves the exact bounce-average statement and a quantitative defect bound in the Boozer guiding-centre model, using the compiled `helicalMomentum_conserved` and `boozerGC_trapped`. Helander14 (section on omnigeneity) and LC12 are the sources to compare against; *locators not verified*. Burby, Kallinikos and MacKay, *Approximate symmetries of guiding-centre motion*, Journal of Physics A 54 (2021) 125202, [arXiv:2010.08968](https://arxiv.org/abs/2010.08968), Theorem 6.1, is the source to extract for a guiding-centre Noether theorem under approximate symmetry (locator from N-27).

## Evolution, regularity, and turbulence proxies

Status: none of the sources in this section is used by compiled Lean yet.

- **PT19.** Pizzocchero and Tassi (2019), *On approximate solutions of the equations of incompressible magnetohydrodynamics*. [arXiv:1905.13722](https://arxiv.org/abs/1905.13722). Proposition 4.3 is the a posteriori bridge from an approximate solution to an exact one used for the periodic evolution benchmark (plan gate E2, question Q-7). Not started in Lean.

- **KSY25.** Kozono, Shimizu, and Yanagisawa (2025), *Stability of harmonic vector fields as an equilibrium of the 3D MHD equations in bounded domains with arbitrary geometry*, Mathematische Annalen 393. [DOI: 10.1007/s00208-025-03223-5](https://doi.org/10.1007/s00208-025-03223-5). Small-data stability around harmonic fields on toroidal domains (plan gate E4, question Q-8). Extract the exact hypotheses; do not transfer a small-background theorem to a reactor-strength field.

- **MPH22.** Mackenbach, Proll, and Helander (2022), Physical Review Letters 128, 175001. [arXiv:2109.01042](https://arxiv.org/abs/2109.01042); erratum Physical Review Letters 130, 239901 (2023); follow-up Journal of Plasma Physics 89, 905890513 (2023). Available energy Â of trapped particles. Â bounds the energy available for release under constrained rearrangements; it is a proxy correlated with turbulent transport, not a transport bound. The formula quoted in the project notes is unchecked against these papers; extract it with equation numbers before any Lean statement depends on it (plan N-20).

## Stability and kinetic theory

- **BFKK58.** I. B. Bernstein, E. A. Frieman, M. D. Kruskal, and R. M. Kulsrud (1958), *An energy principle for hydromagnetic stability problems*, Proceedings of the Royal Society A 244, 17–40. [DOI: 10.1098/rspa.1958.0023](https://doi.org/10.1098/rspa.1958.0023); [institution-hosted scan](https://www.hao.ucar.edu/people/phil-judge/Book/preparations/bernstein58.pdf). Start with **Section 2** for linearization and **Section 3** for the energy principle, including plasma, surface, and vacuum terms. Convert its rationalized Gaussian units to SI. Supply a modern functional-analytic treatment where the source's modal reasoning requires one.

- **Freidberg14.** J. P. Freidberg (2014), *Ideal MHD*, Cambridge University Press. [DOI: 10.1017/CBO9780511795046](https://doi.org/10.1017/CBO9780511795046). Main textbook entry point for equilibrium, energy-principle derivations, boundary conditions, and restricted stability criteria. Record the actual chapter/equation and sign conventions used.

- **MG80.** P. J. Morrison and J. M. Greene (1980), *Noncanonical Hamiltonian Density Formulation of Hydrodynamics and Ideal Magnetohydrodynamics*, Physical Review Letters 45, 790. [Original DOI](https://doi.org/10.1103/PhysRevLett.45.790); [erratum, Physical Review Letters 48, 569](https://doi.org/10.1103/PhysRevLett.48.569). An entry point for Hamiltonian/Casimir methods. A bracket or conserved functional alone does not prove coercivity, a nonlinear basin, or global existence.

- **Littlejohn83.** R. G. Littlejohn (1983), *Variational principles of guiding centre motion*, Journal of Plasma Physics 29, 111–125. [DOI: 10.1017/S002237780000060X](https://doi.org/10.1017/S002237780000060X). Extract the variational model, ordering, symplectic structure, and reduced conservation laws. A guiding-centre theorem must retain its reduction assumptions. In use: `LittlejohnOrbit` is the supplied guiding-centre model of the all-time passing-alpha results (`alpha_gc_passing_confined_forever` and variants).

- **Helander14.** P. Helander (2014), *Theory of plasma confinement in non-axisymmetric magnetic fields*, Reports on Progress in Physics 77, 087001. [Original DOI](https://doi.org/10.1088/0034-4885/77/8/087001); [2018 corrigendum](https://doi.org/10.1088/1361-6633/aac9f0). Main review for stellarator confinement, omnigenity, symmetry, and neoclassical theory. Use it to locate primary results and definitions; read the corrigendum before copying formulas.

- **CS97.** J. R. Cary and S. G. Shasharina (1997), *Helical Plasma Confinement Devices with Good Confinement Properties*, Physical Review Letters 78, 674. [DOI: 10.1103/PhysRevLett.78.674](https://doi.org/10.1103/PhysRevLett.78.674). Starting point for omnigenity and its relationship to quasisymmetry. Follow the primary derivation of bounce-action constraints and the treatment of trapped/passing particles.

- **BH07.** A. J. Brizard and T. S. Hahm (2007), *Foundations of nonlinear gyrokinetic theory*, Reviews of Modern Physics 79, 421–468. [DOI: 10.1103/RevModPhys.79.421](https://doi.org/10.1103/RevModPhys.79.421). Extract ordering, field equations, polarization, and energy identities for one explicitly chosen gyrokinetic model; do not mix equations from different truncation orders.

- **SFINCS14.** M. Landreman, H. M. Smith, A. Mollén, and P. Helander (2014), *Comparison of particle trajectories and collision operators for collisional transport in nonaxisymmetric plasmas*, Physics of Plasmas 21, 042503. [DOI: 10.1063/1.4870077](https://doi.org/10.1063/1.4870077); [SFINCS source](https://github.com/landreman/sfincs). Concrete drift-kinetic models, collision choices, and transport calculations. Prove nullspace/solvability and error bounds for the selected operator before certifying a flux.

- **MaxJ12.** J. H. E. Proll et al. (2012), *Resilience of Quasi-Isodynamic Stellarators against Trapped-Particle Instabilities*, Physical Review Letters 108, 245002. [DOI: 10.1103/PhysRevLett.108.245002](https://doi.org/10.1103/PhysRevLett.108.245002). A restricted kinetic stability result: extract species, gradient, frequency, and ordering assumptions rather than asserting stability to all microinstabilities.

- **TP13.** P. Helander, J. H. E. Proll, and G. G. Plunk (2013), *Collisionless microinstabilities in stellarators. I. Analytical theory of trapped-particle modes*, Physics of Plasmas 20, 122505. [arXiv:1311.3095](https://arxiv.org/abs/1311.3095); [2017 erratum, 24, 039901](https://doi.org/10.1063/1.4977907). Read both before deriving a sign or stability criterion.

- **TP17.** G. G. Plunk, J. H. E. Proll, and P. Helander (2017), *Collisionless microinstabilities in stellarators. IV. The ion-driven trapped-electron mode*. [arXiv:1708.04085](https://arxiv.org/abs/1708.04085). A useful check on the scope of simplified “maximum-J implies stability” claims.

## Validated computation and analysis

- **Rump10.** S. M. Rump (2010), *Verification methods: Rigorous results using floating-point arithmetic*, Acta Numerica 19, 287–449. [DOI: 10.1017/S096249291000005X](https://doi.org/10.1017/S096249291000005X); [author PDF](https://www.tuhh.de/ti3/rump/intlab/ActaNumerica2010.pdf). Basis for interval verification and matrix enclosures. An external verified numerical routine still needs a sound import/checker boundary in Lean.

- **NPW19.** M. T. Nakao, M. Plum, and Y. Watanabe (2019), *Numerical Verification Methods and Computer-Assisted Proofs for Partial Differential Equations*. [DOI: 10.1007/978-981-13-7669-6](https://doi.org/10.1007/978-981-13-7669-6). Source for analytic error bounds and verified PDE methods. Check whether the specific operator is coercive/elliptic; ideal MHD does not inherit that property automatically.

- **FHL17.** J.-Ll. Figueras, À. Haro and A. Luque (2017), Foundations of Computational Mathematics 17, 1123–1193, Theorem 2.5, with explicit constants in eqs. (72)–(73) (locator verified in [kam-route.md](https://github.com/siddhartha-gadgil/PlasmaLean/blob/main/notes/theory/kam-route.md)). An a posteriori KAM theorem with explicit constants for exact symplectic maps. With ELPS Theorem 6.2 (invariant tori of divergence-free fields in ℝ³), it guided the explicit-constant KAM theorem compiled for the rational vacuum field (`torusA_exact`).

- **Parameterization16.** À. Haro, M. Canadell, J.-L. Figueras, A. Luque, and J. M. Mondelo (2016), *The Parameterization Method for Invariant Manifolds: From Rigorous Results to Effective Computations*. [DOI: 10.1007/978-3-319-29662-3](https://doi.org/10.1007/978-3-319-29662-3). Entry point for constructive invariant-manifold methods. For a KAM certificate, select a precise a posteriori theorem and extract every regularity, twist, and small-divisor constant.

- **Lessard-tutorial.** J.-P. Lessard's [computer-assisted proof tutorial entry point](https://www.math.mcgill.ca/jplessard/Publications_files/compuproofsDEs.pdf). Use to locate explicit Newton/radii-polynomial arguments and their hypotheses. Retrieve the full document and establish the exact bibliographic/theorem locator before use; the existence of a tutorial does not validate an MHD operator.

- **Ciarlet88.** P. G. Ciarlet (1988), *Mathematical Elasticity, Volume I: Three-Dimensional Elasticity*, North-Holland. [Publisher entry](https://www.elsevier.com/books/three-dimensional-elasticity/ciarlet/978-0-444-70259-3). Functional-analytic foundation for elasticity, boundary conditions, and existence questions. Use a linear supported-body submodel first; nonlinear/contact problems need their own assumptions.

## Design algorithms and software

- **Hirshman83.** S. P. Hirshman and J. C. Whitson (1983), *Steepest-descent moment method for three-dimensional magnetohydrodynamic equilibria*, Physics of Fluids 26, 3553–3568. [DOI: 10.1063/1.864116](https://doi.org/10.1063/1.864116). VMEC's variational/computational starting point. Nested-surface assumptions and a computed stationary point do not supply continuum existence or stability.

- **REGCOIL17.** M. Landreman (2017), *An improved current potential method for fast computation of stellarator coil shapes*, Nuclear Fusion 57, 046003. [arXiv:1609.04378](https://arxiv.org/abs/1609.04378); [official documentation](https://regcoil.readthedocs.io/en/latest/). Surface-current inverse design and regularization. Keep normal-field mismatch, current density, and realizable finite-coil geometry as separate quantities.

- **Coils22.** F. Wechsung, M. Landreman, A. Giuliani, A. Cerfon, and G. Stadler (2022), *Precise stellarator quasi-symmetry can be achieved with electromagnetic coils*, PNAS 119, e2202084119. [Primary article](https://pmc.ncbi.nlm.nih.gov/articles/PMC9060451/); [reproduction repository](https://github.com/florianwechsung/CoilsForPreciseQS). Useful candidate-generation and finite-coil examples. Recheck continuous clearance, finite conductor field, tolerance, and orbit claims.

- **SingleStage22.** A. Giuliani, F. Wechsung, A. Cerfon, G. Stadler, and M. Landreman (2022), *Single-stage gradient-based stellarator coil design: Optimization for near-axis quasi-symmetry*. [Publisher article](https://www.sciencedirect.com/science/article/pii/S0021999122002091). Shows an optimization route coupling coil design and near-axis objectives; optimizer convergence is evidence about a candidate rather than a proof certificate.

- **Direct23.** A. Giuliani, F. Wechsung, A. Cerfon, M. Landreman, and G. Stadler, *Direct stellarator coil optimization for nested magnetic surfaces with precise quasi-symmetry*. [arXiv:2210.03248](https://arxiv.org/abs/2210.03248). Check the nested-surface representation and residual measure before choosing what to certify.

- **DESC23.** D. Panici, R. Conlin, D. W. Dudt, K. Unalmis, and E. Kolemen (2023), *The DESC stellarator code suite. Part 1. Quick and accurate equilibria computations*, Journal of Plasma Physics 89, 955890303. [DOI: 10.1017/S0022377823000272](https://doi.org/10.1017/S0022377823000272); [arXiv:2203.17173](https://arxiv.org/abs/2203.17173). An equilibrium candidate generator with explicit discretization conventions, not a checked continuum proof.

Official implementation/documentation entry points:

| Tool | Primary entry point | Role in PlasmaLean |
| --- | --- | --- |
| Lean/Mathlib | [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/) | Search the pinned source before relying on current online API names |
| SIMSOPT | [Documentation](https://simsopt.readthedocs.io/en/latest/) | Candidate optimization, geometry, coils, diagnostics |
| DESC | [Documentation](https://desc-docs.readthedocs.io/en/stable/) | Spectral equilibrium candidates and residuals |
| REGCOIL | [Documentation](https://regcoil.readthedocs.io/en/latest/) | Surface-current inverse design |
| SFINCS | [Source](https://github.com/landreman/sfincs) | Selected neoclassical transport models |
| OpenMC | [Documentation](https://docs.openmc.org/en/stable/) | Neutron transport, material definitions, tally normalization and uncertainty |

Pin versions and read their conventions. None is automatically part of the trusted Lean theorem path.

## Engineering, materials, and experiment

- **KMM16.** J. Knaster, A. Moeslang, and T. Muroga (2016), *Materials research for fusion*. [DOI: 10.1038/nphys3735](https://doi.org/10.1038/nphys3735); [author-institution record](https://publikationen.bibliothek.kit.edu/1000054752). Map irradiation, thermal, and mechanical challenges to material-law inputs and explicit validity limits.

- **DEMO18.** J.-H. You et al. (2018), *European divertor target concepts for DEMO: Design rationales and high heat flux performance*, Nuclear Materials and Energy 16, 1–11. [DOI: 10.1016/j.nme.2018.05.012](https://doi.org/10.1016/j.nme.2018.05.012); [author-institution record](https://publikationen.bibliothek.kit.edu/1000085927). A concrete source for component models, cooling concepts, and load tests. Transfer a numerical limit only with the original geometry/material/operation assumptions.

- **REBCO25.** P. Huslage et al. (2025), *Strain optimisation for ReBCO high-temperature superconducting stellarator coils in SIMSOPT*, Journal of Plasma Physics 91, E71. [DOI: 10.1017/S0022377825000224](https://doi.org/10.1017/S0022377825000224); [arXiv:2409.01925](https://arxiv.org/abs/2409.01925). Source for tape-frame, hard-way bending, and torsion objectives. Full conductor critical-surface, irradiation, pack mechanics, and quench constraints still require additional data/models.

- **HELIAS13.** F. Schauer et al. (2013), *HELIAS 5-B magnet system structure and maintenance concept*. [DOI: 10.1016/j.fusengdes.2013.01.035](https://doi.org/10.1016/j.fusengdes.2013.01.035); [author-institution record](https://pure.mpg.de/pubman/item/item_2145357). Reactor magnet/support/maintenance integration; source design-specific requirements instead of imposing universal clearances.

- **ISS04** and **IPB98**: see [Sources the compiled library uses](#sources-the-compiled-library-uses). Both are empirical confinement scalings. Under C5, anomalous transport is a stated, supplied scaling (`ConfinementLaw`), never hidden. With ISS04 the burn window on Stellaris parameters needs renormalization factors above measured values (`stellaris_measured_fren_no_access_steady`, `stellaris_measured_fren_no_access_loss`, Q-13).

- **W7X-transport21.** C. D. Beidler et al. (2021), *Demonstration of reduced neoclassical energy transport in Wendelstein 7-X*, Nature 596, 221–226. [DOI: 10.1038/s41586-021-03687-w](https://doi.org/10.1038/s41586-021-03687-w); [primary article](https://pmc.ncbi.nlm.nih.gov/articles/PMC8357633/). Validation evidence for selected transport predictions and regimes, not a theorem for arbitrary future stellarators.

- **W7X-divertor21.** M. Jakubowski et al. (2021), *Overview of the results from divertor experiments with attached and detached plasmas at Wendelstein 7-X and their implications for steady-state operation*, Nuclear Fusion 61, 106003. [DOI: 10.1088/1741-4326/ac1b68](https://doi.org/10.1088/1741-4326/ac1b68); [author-institution record](https://www.ornl.gov/publication/overview-results-divertor-experiments-attached-and-detached-plasmas-wendelstein-7-x-0). Source edge/exhaust operating envelopes and their measured conditions.

- **BH92-reactivity.** H.-S. Bosch and G. M. Hale (1992), *Improved formulas for fusion cross-sections and thermal reactivities*, Nuclear Fusion 32, 611–631. [Original DOI](https://doi.org/10.1088/0029-5515/32/4/I07); [1993 corrigendum](https://doi.org/10.1088/0029-5515/33/12/513). Useful fit for a declared fuel/temperature domain. Preserve units, species conventions, coefficients, and fit uncertainty; do not treat the fit as an exact physical law.

- **FENDL-data.** IAEA, [Fusion Evaluated Nuclear Data Library](https://www-nds.iaea.org/fendl/). Pin the dataset release, nuclide files, processing, energy groups, and response definitions. Evaluated cross sections are supplied physical data; a deterministic proof needs declared envelopes, while a probabilistic claim needs its statistical assumptions.

Status: of this section only BH92-reactivity (alpha heating, C5) and the confinement scalings are used by compiled Lean. The engineering sources (KMM16, DEMO18, REBCO25, HELIAS13, FENDL-data) are not yet used; the only compiled component result uses invented inputs ([07](07-materials-and-engineering.md)).

These references establish starting points rather than a complete component qualification dataset. For a chosen material/device, additionally retrieve the primary conductivity, critical-current, fracture/fatigue, irradiation, coolant, and joint data. Formalize the envelope interpretation before consuming it in a design proof.

## Reading order and theorem targets

| First target | Read first | Follow-on obligation |
| --- | --- | --- |
| Force-balance tangency and a vacuum/force-free distinction | Freidberg14; [02](02-plasma-models-and-equilibrium.md) | Construct consistent instances in Lean |
| Static fixed-boundary quadratic energy | BFKK58; Freidberg14; [03](03-mhd-stability.md) | Boundary terms, operator domain, quotient and all-mode bound |
| Boozer/near-axis coefficient identities | Boozer81; GB91-field; GB91-existence; LS19 Appendix A | Annular chart, regularity and series remainder |
| Invariant barrier or approximate-invariant loss time | BKM20; Littlejohn83; Helander14; [04](04-particles-and-transport.md) | Particle initial set, reduction error and horizon |
| Exact retained-mode / continuous-clearance checker | Rump10; [05](05-verified-numerics.md) | Infinite tails and full domain coverage |
| Validated equilibrium or invariant torus | ELPS; Parameterization16; NPW19 | Source-specific constructive constants and derivative loss |
| Coils producing the intended field | REGCOIL17; Coils22; DESC23; [06](06-coils-and-design.md) | Finite conductor, plasma-current response and tolerances |
| Slab heat, ribbon strain, and dump-energy margins | DEMO18; REBCO25; Ciarlet88; [07](07-materials-and-engineering.md) | Primary material data and coupled PDE/ODE extensions |
| Fuel, shielding, lifetime, and practical integration | BH92-reactivity; FENDL-data; KMM16; HELIAS13 | Neutronics, inventory, degradation and net-power certificates |

The rows above date from 12 October; the progress column of the generated page gives their Lean status. The contract adds the following reading order, in the priority order of the plan (RG.5):

| Contract target | Read first | Follow-on obligation |
| --- | --- | --- |
| QS ⇒ omnigeneity, exact and quantitative (Q-23, C2) | Helander14; LC12; CDG21; BKM20; the Boozer model sources | Bounce-average statement in the Boozer guiding-centre model; defect bound with explicit constant; then ε_eff |
| Dommaschk QA fit with certified tori and ι (Q-16, C1 + C2) | Dommaschk86; LP22; LS19; FHL17; ELPS Thm 6.2 | Fit as an untrusted oracle; KAM certificates; Boozer angles; certified non-QS part of ‖B‖ |
| Bounce-averaged drift and ε_eff on the rational field (Q-19, C2) | NKKH99; Helander14; SFINCS14 | Definitions of Q-21 first; numerical oracle; decide whether a certified bound is reachable |
| Net toroidal current of the Landreman families (Q-18, C1) | Landreman26; ICLT26 | Named positivity corollary of `torCurrent_eq`; ratio to the external current; family 1 |
| Definitions for C1 and C2 (Q-21) | HM75; LC12; NKKH99; [00](00-model-contracts.md) | Each definition with the sanity triad |
| Current-free finite β (Q-20, Q-14) | ELPS; MRxMHD12 | Control the net toroidal part of the sheet currents |
| Thermal neoclassical bounds for C5 (Q-22) | NKKH99; Helander14; SFINCS14; ISS04 | 1/ν scaling as a supplied law; χ bounds for ions and electrons |

Use [08-roadmap.md](08-roadmap.md) to select a milestone. Existing literature supports substantial parts of the program; the research targets require separate novelty review and new mathematics where the available hypotheses or quantitative conclusions fall short.
