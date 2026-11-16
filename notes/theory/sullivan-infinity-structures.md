# Sullivan's combinatorial and eigenspace fluid models: applicability to MHD and stellarators

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-42` |
| Title | Assessment of Sullivan's L∞ (combinatorial) and eigenspace models of 3D fluids for MHD and stellarator design |
| Kind | source synthesis (source assessment) |
| Addresses | `G-9`, `G-11` (infrastructure); `Q-29` (new); contract clauses C1–C5 as a test of expressiveness |
| Depends on | `sources/SullivanFluids.pdf`; N-41 (`Kernel/Forms`, `Theory/Fields/FormBridges`); `Theory/Stability/Elsasser` |
| Dependency requirement | the source as published; the compiled declarations named below |
| Produces | this assessment; `PlasmaLean/Theory/Fluids/EulerianODE.lean` (a check of Part 2 of the source); question `Q-29` |
| Difficulty | moderate (reading and comparison); the open items are research |
| Status | stated (assessment complete); one claim of the source verified in Lean; no design consequence |
| Lean evidence | default build: `PlasmaLean.Fluids.EulerianODE`, `EulerianODE.energy_conserved`, `EulerianODE.helicity_conserved`, `rigidBody_eulerian`, `eulerianODE_zero`, `not_eulerianODE_id` |
| Audit evidence | not audited |
| Last updated | 16 November 2026: created; corrected the same day from four properties to five (C5 added) at the user's request |

## Purpose and scope

The user asked (16 November 2026) for a detailed study of the ideas in D. Sullivan, *3D
incompressible fluids: combinatorial models, eigenspace models, and a conjecture about
well-posedness of the 3D zero viscosity limit*, J. Differential Geom. 97 (2014) 141–148
(`sources/SullivanFluids.pdf`), with three questions:

1. Would infinity structures (L∞ algebras) help in MHD?
2. Can the five properties required of stellarator solutions be expressed well in these terms?
   They are the contract clauses C1 (current-free rotational transform), C2 (omnigeneity), C3
   (MHD stability), C4 (existence of an equilibrium with nested surfaces) and C5 (thermal
   performance and stability: the core temperature stays in the burn band). The user's first
   message said four properties and was corrected to five, including the thermal one, on the
   same day.
3. Are there possible gains over the present style of numerics?

The user's framing is that the ideas are innovative and may or may not work in practice. This
note is an assessment, not a formalization plan. Nothing here changes a contract clause.

## Dependencies

- The source paper (published; its Part 1 is a programme with stated facts and two standard
  theorems of homotopical algebra, its Part 2 has one proposition with proof, one theorem with a
  proof sketch in which the word "follows" is in quotation marks, and a conjecture).
- Compiled: `Kernel/Forms`, `Theory/Fields/FormBridges` (N-41); `Theory/Stability/Elsasser`
  (`IsSkewTransport`, conservation of the Elsässer energies under a supplied skew transport).

## Sources and prior work

Checked by web search on 16 November 2026 unless marked *(from memory)*.

**Sullivan's programme.**
- D. Sullivan, J. Differential Geom. 97 (2014) 141–148 (the source).
- N. Ranade, D. Sullivan, *The cumulant bijection and differential forms*, arXiv:1407.0422.
- D. Sullivan, *Lattice hydrodynamics*, arXiv:1811.00086; Astérisque 415 (2020) 215–222. A model
  on two interpenetrating face-centred cubic lattices; two formulations (momentum, vorticity).
- R. Lawrence, N. Ranade, D. Sullivan, *Quantitative towers in finite difference calculus
  approximating the continuum*, Q. J. Math. 72 (2021) 515–545, arXiv:2011.07505. Finite
  commutative algebras of chains and cochains on periodic cubical lattices at several scales;
  the failure of the Leibniz rule is measured by higher brackets, and **the (k+1)-th bracket is
  divisible by `h^k`** (their Theorems 1.2A, 1.3A). No fluid computation.
- D. Sullivan, *Computing three-dimensional fluid motion* (Balzan Prize forum lecture). States the
  aim of the Balzan project: to have algorithms with the hierarchy of corrections programmed and
  tested. It reports a remark of J. Terilla that cell integrals of true solutions satisfy the
  combinatorial evolution with the whole hierarchy.
- **No implementation, numerical experiment, stability or convergence theorem for the fluid
  algorithms was found** in these sources or by search. This is an absence of evidence from a
  limited search, not a proof of absence.

**Cochain algebra and convergence.**
- S. O. Wilson, *Cochain algebra on manifolds and convergence under refinement*, Topology Appl.
  154 (2007) 1898–1920, arXiv:math/0505227: the cochain product and any C∞ extension of it
  converge to the wedge product under refinement, measured through Whitney's embedding.
- The discrete wedge product of discrete exterior calculus is Wilson's cochain product
  (arXiv:2310.00725).
- X. Z. Cheng, E. Getzler, *Transferring homotopy commutative algebraic structures*, J. Pure
  Appl. Algebra 212 (2008) 2535 *(from memory)*.

**Structure-preserving discretization of fluids and MHD.**
- D. Pavlov, P. Mullen, Y. Tong, E. Kanso, J. E. Marsden, M. Desbrun, *Structure-preserving
  discretization of incompressible fluids*, Physica D 240 (2011) 443, arXiv:0912.3989.
- E. Gawlik, P. Mullen, D. Pavlov, J. E. Marsden, M. Desbrun, *Geometric, variational
  discretization of continuum theories*, Physica D 240 (2011) 1724, arXiv:1010.4851 (MHD).
- K. Hu, Y.-J. Lee, J. Xu, *Helicity-conservative finite element discretization for
  incompressible MHD systems*, J. Comput. Phys. 436 (2021) 110284: magnetic and cross helicity,
  the energy law and `div B = 0` hold exactly; error estimates for a related scheme in
  arXiv:2407.19748.
- M. He, P. E. Farrell, K. Hu, B. D. Andrews, *Helicity-preserving finite element discretization
  for magnetic relaxation*, arXiv:2501.11654 (SIAM J. Sci. Comput.): a discrete Arnold inequality,
  so that relaxation cannot destroy the field topology; local helicities in arXiv:2603.12134.
- Zeitlin-type matrix models: exact finite-dimensional Lie–Poisson structure with Casimirs for
  2D flows on the sphere (K. Modin, M. Viviani, arXiv:1812.11055), for 2D MHD, and in 3D only for
  axially symmetric flows. A paper of that line states that finite element and discrete exterior
  calculus discretizations do not admit a finite-dimensional Lie–Poisson formulation.
- C. R. Evans, J. F. Hawley, Astrophys. J. 332 (1988) 659 (constrained transport); D. N. Arnold,
  R. S. Falk, R. Winther, Acta Numer. 15 (2006) 1 (finite element exterior calculus) *(both from
  memory)*.

**Curl eigenfunctions and truncated ideal systems.**
- P. D. Mininni, D. C. Montgomery, *Magnetohydrodynamic activity inside a sphere*,
  arXiv:physics/0602147: a Galerkin code in Chandrasekhar–Kendall curl eigenfunctions; energy,
  magnetic helicity and cross helicity are quadratic sums of the coefficients and are conserved.
- T. D. Lee, Q. Appl. Math. 10 (1952) 69; R. H. Kraichnan, J. Fluid Mech. 59 (1973) 745; U. Frisch,
  A. Pouquet, J. Léorat, A. Mazure, J. Fluid Mech. 68 (1975) 769; F. Waleffe, Phys. Fluids A 4
  (1992) 350 (absolute equilibria of truncated Euler and MHD; helical decomposition) *(from
  memory)*.

**Stellarator equilibrium codes.** VMEC and DESC assume nested flux surfaces; SPEC (stepped
pressure, Beltrami fields in each volume), HINT and SIESTA do not (DESC paper, arXiv:2203.17173;
a VMEC–HINT comparison, arXiv:2606.10490). The near-axis quasisymmetry equations are
overdetermined from third order (Garren–Boozer; arXiv:1911.02659, arXiv:2110.13703).

## Theory development

### 1. What the source proposes

**Part 1 (combinatorial models).** Multivector fields `V` on a manifold with a volume form are a
chain complex: `∂` is the exterior derivative transported by the volume form, so `∂X = div X` on
vector fields. With the Schouten bracket, `(V, ∂, [ , ])` is a differential graded Lie algebra,
encoded as a square-zero coderivation `∂_∞ = ∂₁ + ∂₂` on the symmetric coalgebra `SV`. The Euler
equation is `Ẏ = [X, Y]`, `Y = curl X`, `∂X = 0`. Choose a cubical lattice on the 3-torus; a
smoothing map and integration give a deformation retraction of `V` onto the cellular chains `C`.
The homotopy transfer theorem then gives an L∞ structure `∂_∞^C` on `C`, with brackets `l_k`
given by sums over trees whose internal edges carry the chain homotopy. On the cubical lattice
the Poincaré dual complex is a translate of the original, which gives a combinatorial Hodge star
and curl `D`. The discrete equations are `∂_∞ X = 0`, `Ẏ = Ad_X Y`, `DX = Y`. Two parameters:
mesh, and the number of brackets kept. The section ends "Now we need to compute!".

**Part 2 (eigenspace models).** A quadratic ODE `ẋ = Q(x)` on a finite-dimensional inner product
space is *Eulerian* if `⟪Q x, z⟫ = {x, D x, z}` for a self-adjoint invertible `D` and a totally
skew 3-form. These preserve `|x|²` and Lebesgue measure, hence the Gaussian measure
(Proposition 7.3). Truncating to curl eigenvalues `|λ| ≤ n` gives Eulerian ODEs converging to
the Euler equation (Theorem 7.5, sketched). Conjecture: for almost every initial condition with
respect to the Gaussian measure, 3D ideal or viscous flow is uniquely defined for all time.

### 2. Translation to MHD

- **Induction equation.** For incompressible ideal MHD, `∂_t B = curl(v × B) = -[v, B]`, the Lie
  bracket of two divergence-free vector fields. This has exactly the form of Sullivan's vorticity
  equation, with `B` in place of `Y` and `v` in place of `X`, and it needs no metric: it is the
  statement that the flux 2-form is Lie-transported (frozen-in flux). So the L∞ machinery applies
  to the kinematic half of MHD at least as directly as to the Euler equation.
- **Momentum equation.** The Lorentz force `J × B` with `J = curl B / μ₀` uses the metric twice
  (the Hodge star in the curl and in the interior product; in `Kernel/Forms`:
  `FormForceBalance`, `extDeriv_flat`). In Sullivan's scheme the metric enters only through the
  combinatorial star `D`, which is the least developed part (Remark 7.1 relies on the cumulant
  bijection to make `D` commute with `∂_∞`).
- **Part 2.** Ideal MHD in Elsässer variables has the same shape as an Eulerian ODE, with a
  trilinear form that is skew in its last two arguments. This abstract structure is already in
  the library: `Theory/Stability/Elsasser` proves conservation of `‖z₊‖²` and `‖z₋‖²` from the
  supplied hypothesis `IsSkewTransport`.

### 3. What homotopy transfer does and does not preserve

**Observation 1 (complete proof).** On the flat torus `𝕋³` the dg Lie algebra `(V, ∂, [ , ])`
is quasi-isomorphic, as a dg Lie algebra, to the abelian graded Lie algebra `Λ*ℝ³` with zero
differential.
*Proof.* Multivector fields with constant coefficients form a subspace closed under `∂` (which
vanishes on it, since constants are divergence free) and under the Schouten bracket (which
vanishes on it). The inclusion is a strict map of dg Lie algebras. Under the volume form it is
the inclusion of constant-coefficient forms into the de Rham complex of `𝕋³`, which is an
isomorphism on cohomology. ∎

Consequences.
- Every L∞ structure produced on cellular chains by Theorem 4.5 of the source is, **for every
  mesh including the coarsest**, quasi-isomorphic to the same trivial object. Homotopy invariance
  therefore guarantees exactly the preservation of the homology classes: the mean flow, the
  net fluxes, and in MHD the net fluxes and (on a domain with a hole) the net currents. It
  guarantees nothing about the dynamics.
- All dynamical content lies in the chosen representative: the particular smoothing map and
  homotopy at scale `h`. Its accuracy is an analytic question. The quantitative paper of
  Lawrence, Ranade and Sullivan supplies the first such statement (the (k+1)-th bracket is
  `O(h^k)`), which says that keeping brackets up to arity `k + 1` removes the algebraic
  inconsistency to order `h^k`. This is the real content of the programme for numerics: a
  hierarchy of corrections that restores the continuum identities (Leibniz, Jacobi) order by
  order in the mesh. It is a consistency statement, not a stability or convergence theorem.

**Observation 2 (closure).** The integration map from fields to cell averages is many-to-one,
and the Euler flow does not factor through it: two fields with the same cell averages have
different futures. So no closed autonomous ODE on the finite-dimensional space `C` reproduces
cell averages of all true solutions; any closed finite model is an approximation whose error
depends on the unresolved scales. The L∞ hierarchy organizes corrections in powers of `h` for
smooth fields; it does not remove this closure problem. Terilla's remark reported in the Balzan
lecture (cell integrals of true solutions are computed by the combinatorial model with the whole
hierarchy) could not be located in print and is recorded as **unverified**; in view of this
observation it cannot mean a closed finite system of fixed order.

**Observation 3 (the gap is real).** The defect that Sullivan addresses is acknowledged in
numerical analysis: discrete products and Lie derivatives on cochains or finite elements satisfy
`d ∘ d = 0` exactly but not associativity, graded commutativity, Leibniz or Jacobi, and no
finite-dimensional Lie algebra approximates the volume-preserving diffeomorphisms of a 3-manifold
in the way `su(N)` does for the sphere. Existing remedies:
1. keep the exact cochain complex (constrained transport, finite element exterior calculus) and
   prove conservation of selected invariants directly (energy, magnetic and cross helicity,
   `div B = 0`, a discrete Arnold inequality), with error estimates;
2. discrete diffeomorphism groups with a nonholonomic constraint (Pavlov et al.; Gawlik et al.
   for MHD), which give a discrete Kelvin theorem;
3. matrix (Zeitlin) models in special geometries.
The L∞ hierarchy is a fourth remedy. It is the only one that treats the failure of the Jacobi
identity as structure and not as error, and it is the only one without an implementation.

### 4. Part 2 is classical in plasma physics

- An Eulerian ODE in the curl eigenbasis is a Galerkin truncation in Chandrasekhar–Kendall
  (helical, Beltrami) modes. Such truncations of the Euler equations conserve energy and helicity
  (Kraichnan; Waleffe), and of ideal MHD conserve energy, magnetic helicity and cross helicity
  (Frisch et al.; implemented by Mininni and Montgomery in a sphere).
- The invariant Gaussian measure of Proposition 7.3 is the equipartition "absolute equilibrium"
  of the truncated system (Lee; Kraichnan), a standard object in turbulence theory.
- **Lean check.** `PlasmaLean/Theory/Fluids/EulerianODE.lean` formalizes the definition and
  proves `EulerianODE.energy_conserved` (Proposition 7.3 (1)) and
  `EulerianODE.helicity_conserved`: `⟪x, D x⟫` is also conserved. The source states only the norm;
  helicity follows from the same skew-symmetry in one line
  (`d/dt ⟪x, Dx⟫ = 2 {x, Dx, Dx} = 0`). Sanity instance: on `ℝ³` with the triple product the
  Eulerian ODE is `ẋ = x × Dx`, the free rigid body (`rigidBody_eulerian`), in agreement with
  Arnold's analogy between the rigid body and ideal fluids.
- What is new in the source is the characterization of this class by invariance properties (cited
  to another paper, not checked here) and the conjecture. In three dimensions the Gaussian
  measure with covariance the identity on `L²` is carried by distributions far rougher than `L²`,
  on which the quadratic term has no evident meaning; the conjecture is about statistical
  solutions of turbulence type. It has no bearing on equilibrium design.
- Relevance to stellarators: a Taylor-relaxed state is a single curl eigenfield, and SPEC computes
  Beltrami fields in each volume, so the curl eigenbasis is already the working language of
  stepped-pressure equilibria. In a non-axisymmetric toroidal domain the eigenfunctions are not
  explicit, so a truncation "by eigenvalue" needs a numerical eigen-solve first.

### 5. The five properties in these terms

| Clause | Content | In dg Lie / L∞ terms | Assessment |
| --- | --- | --- | --- |
| C1 | zero net toroidal current, `ι ≥ ι_min` | net currents and fluxes are periods of the closed forms `B♭`, `ω_B` over cycles: homology classes of the chain complex | **expressed well and exactly**. These are the only homotopy-invariant data (Observation 1), preserved by any chain map. The library already uses this form (`loopCurrent`, `netToroidalCurrent_eq_loopCurrent`). `ι` as a ratio of fluxes is of this kind; `ι` on each torus presupposes the tori |
| C4 | force balance and nested surfaces | `∂B = 0`, `∂J = 0`, and where `dp ≠ 0`, `[B, J] = 0`: two commuting cycles; `J = curl B/μ₀` needs the star | the algebraic part is expressible (`form_field_tangency`, `form_current_tangency`, `IsBeltramiOn.formForceBalance` are its compiled forms on `ℝ³`). Existence of nested surfaces is a small-divisor (KAM) question and is invisible to the homotopy type |
| C2 | omnigeneity / quasisymmetry | a divergence-free `u` with `[u, B] = 0` (compiled: `FormWeakQS`), plus `u(\|B\|) = 0`, which needs the metric; omnigeneity proper is a statement about bounce integrals along field lines | partly expressible (the symmetry), the essential part (the condition on `\|B\|`, bounce averages) is not |
| C3 | MHD stability | positivity of the second variation of the energy on the orbit of the equilibrium | not expressible in a useful way: it is spectral and metric. The Lie–Poisson picture names the orbit, the L∞ picture adds nothing to the estimate |
| C5 | thermal performance and stability: temperature in the burn band over the operating interval, from power balance and radial heat transport | none in Part 1: heat transport is dissipative (a parabolic equation in the flux label with collisional and turbulent fluxes), not transport by a Lie bracket, and its coefficients are flux-surface averages (a coarea construction, supplied data in `FluxGeometry`). Part 2 is adjacent only by analogy: its invariant Gaussian measure is a statistical equilibrium of a truncated *ideal* system, whereas the heat flux is set by driven, dissipative turbulence | **not expressible**. The source's statistical ideas are the nearest point of contact with turbulent transport, but an ideal equipartition state has zero mean flux and says nothing about the driven state. The library's tools for C5 are of a different kind: comparison and barrier arguments, relative entropy and Fisher information (N-2), the kinetic contract (N-40) |

So one clause of five is natural in these terms, and it is the one that is already elementary.
The clause furthest from the source is C5, which is not a statement about ideal dynamics at all.

**A different use: deformation theory (conjectural, origin: this assessment).** L∞ algebras are
the standard language for deformation problems: infinitesimal deformations and obstructions are
cohomology groups of a complex attached to the equations. The quasisymmetric near-axis
expansion is solvable to second order and overdetermined from third order. That is the typical
shape of an obstructed deformation problem, and a complex whose cohomology counts the free
functions and the constraints order by order would organize it. No such formulation was found in
the literature search. It is recorded as question `Q-29`; nothing is claimed.

### 6. Gains over the present numerics

- **Present style.** Spectral energy minimization with nested surfaces assumed (VMEC, DESC);
  stepped pressure (SPEC); relaxation without the assumption (HINT, SIESTA); none gives error
  bounds. This project adds a posteriori validation: interval arithmetic and Newton–Kantorovich
  or KAM arguments applied to a candidate found by untrusted numerics.
- **L∞ scheme as a solver.** No demonstrated gain: no implementation, no stability or
  convergence theory, a periodic cubical lattice in a Euclidean background (the self-duality by
  translation and the explicit cumulants both use it), whereas the plasma domain is a curved solid
  torus with a boundary and a magnetic axis. The cost of the tree sums at higher arity is
  unquantified.
- **Where structure preservation matters for stellarators** is magnetic relaxation to an
  equilibrium without assuming surfaces, where numerical reconnection can change the topology.
  That need is being met by helicity-preserving finite element exterior calculus, which has
  proofs of the conserved quantities, a discrete Arnold inequality and error estimates.
- **For verified numerics** the algebraic quality of a discretization is not what a proof uses.
  An a posteriori argument needs a residual bound in a norm and a stability constant for the
  linearization; these are indifferent to whether the discrete bracket satisfies the Jacobi
  identity up to homotopy. The L∞ hierarchy supplies no enclosure.

## Claims and evidence

1. *Sourced (published):* the constructions and Proposition 7.3 of the source.
2. *Compiled Lean theorem (default build):* `EulerianODE.energy_conserved`,
   `EulerianODE.helicity_conserved`, for a supplied differentiable solution; `rigidBody_eulerian`;
   `eulerianODE_zero`; `not_eulerianODE_id`. The second is an addition to the source.
3. *Complete mathematical proof (short, above):* Observation 1.
4. *Proof sketch:* Observation 2 (the flow does not factor through cell averages).
5. *Sourced:* the (k+1)-th bracket is divisible by `h^k` on periodic cubical lattices
   (Lawrence–Ranade–Sullivan), read from the paper's introduction through a summary, not checked
   line by line.
6. *Sourced, with the limits stated above:* the comparison with structure-preserving methods.
7. *Literature observation (limited search):* no implementation of the L∞ fluid algorithm.
8. *Conjecture (this assessment):* a deformation complex for quasisymmetric equilibria explains
   the third-order overdetermination (`Q-29`).

**Answers.**
1. *Would infinity structures help in MHD?* As a language, partly: the induction equation is
   exactly of Sullivan's form and the invariants that are exact (fluxes, net currents) are the
   homological ones. As a numerical method, not on present evidence.
2. *Are the five properties expressed well?* Only C1. C4 and C2 are expressible in their
   algebraic part while their content is analytic; C3 and C5 are not.
3. *Gains over present numerics?* None demonstrated. The need that structure preservation serves
   in this field is met by methods with proofs and codes. The one speculative opening is
   conceptual (`Q-29`).

## Difficulty, barriers and readiness

- Barriers to using Part 1: no convergence or stability theory; geometry restricted to periodic
  cubical lattices; the metric (star) is the weakest part and MHD needs it twice; cost unknown.
- Nothing here is needed by a contract clause. No Lean work is proposed beyond the check already
  made.
- The smallest step that would change this assessment: a published or reproducible computation
  with the L∞ hierarchy on the periodic Euler or induction equation, compared with a
  helicity-preserving finite element scheme at equal cost.

## Outputs and next dependencies

- New module `Theory/Fluids/EulerianODE` (default build).
- New question `Q-29` (deformation complex for quasisymmetric equilibria; speculative, low
  priority).
- No change to goals. `sources/SullivanFluids.pdf` is assessed by this note.
