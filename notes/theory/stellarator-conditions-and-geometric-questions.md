# Stellarator conditions C1–C5 and three geometric research questions

**Assessment of 24 November 2026.** The Dommaschk QA2R vacuum field satisfies C1 on two nested embedded tori and meets the vacuum version of C4. Thermal-particle confinement (C2), equilibrium and stability at finite pressure (C4 and C3), and thermal performance (C5) remain open on a common candidate. The largest gap is between knowing the geometry of two surfaces and controlling a plasma throughout the region between them. [Stellarator contract](../formalization/00-model-contracts.md)

## Progress on one stellarator

| Condition | Established | What remains |
| --- | --- | --- |
| **C1 — current-free rotational transform** | Lean proves that both Dommaschk tori have zero net toroidal current and that the magnitude of the rotational transform is at least 0.2386 on each. Their sections are disjoint and ordered. A second, rational vacuum stellarator also satisfies C1. | A finite-pressure construction must retain both the transform and the net-current bound. [Dommaschk theorem](../../PlasmaLean/Design/DommaschkKamEmbedded.lean) · [Rational stellarator theorem](../../PlasmaLean/Design/RationalStellaratorEmbedded.lean) |
| **C2 — thermal-particle confinement** | Both Dommaschk tori have certified small departures from quasi-axisymmetry. There are local mirror wells and action comparisons. Lean proves a finite-time radial barrier given an action-drift bound and action inequalities on the two radial boundaries. At launch radius 0.470 in a small sector around phase zero, a workstation proof follows a physical **field line** through 20 forward slabs, or 5/16 radian. The archived 16-slab theorem reaches 1/4 radian. | A trapped guiding centre bounces and drifts across field lines. We need a bound for that dynamics over a stated time and radial excursion, covering a specified fraction of thermal ion and electron births. The physical operating targets remain open by choice. [Action barrier](action-faces-and-winding.md) · [Archived trace and scope](dommaschk-quarter-radian-trace.md) · [Prefix proof generator](../../scripts/dommaschk_kam/verify_physical_trace_prefix.py) |
| **C3 — finite-pressure MHD stability** | The project has stability results on current-carrying test cases and a cylinder benchmark. On the exact Dommaschk torus A, Lean proves that one sufficient curvature condition for a pressure interface fails at a point. | We need a stability estimate for a qualifying finite-pressure stellarator. The stability of an interface on A remains open. [Geometric obstruction](dommaschk-interface-obstruction.md) · [Cylinder benchmark](cylinder-interface-stability.md) |
| **C4 — equilibrium and nested surfaces** | The smooth Dommaschk vacuum field satisfies force balance and has the two certified invariant tori. | A foliation of the intervening volume and a finite-pressure equilibrium there compatible with C1 are both open. Two boundary tori alone give neither conclusion. [Candidate results and scope](../../README.md) |
| **C5 — thermal performance** | A Solov’ev tokamak benchmark preserves a burn-temperature band for every supplied solution of its transport model. Zero-dimensional stellarator models also have operating windows and exclusions. | We need a power balance for the same stellarator, with dimensional operating data, heat losses derived from particle transport, and a stated model of anomalous transport. [Thermal-performance contract](../formalization/00-model-contracts.md) |

## Where more computation pays off

Finish the long field-line certificates and start the geometric work in parallel. Extending a trace with an established margin is largely proof engineering. It can certify mirror locations, arclengths and action integrals for the actual field. Even a complete set of those traces would leave two distinct questions. Does the selected well persist as the launch phase goes around the torus? How accurately does its action control a guiding centre over many bounces?

C1 gives a precedent. For a sufficiently regular invariant torus parametrization, irrational field-line flow and poloidal winding one imply embeddedness. That single theorem resolved the same issue in two examples. The most promising places to look for a comparable result are C2 and the first pressure deformation in C4. [Reusable embeddedness theorem](../../PlasmaLean/Theory/Contract/IrrationalTorus.lean)

## 1. What is the topology and metric geometry of a family of magnetic wells?

Fix a mirror height $h=E/\mu$, where $E$ is the energy and $\mu>0$ is the magnetic moment. Over an annulus of launch labels, follow consecutive simple mirror points enclosing a well. A first theorem to prove is that the space of selected wells projects to the label annulus as a finite covering. The hypotheses should ensure that the mirror points stay uniformly transverse, the selected pairs stay isolated, and continuation is proper. Once these hold, going around the annulus induces a permutation of the wells. A particular well returns to itself precisely when the permutation fixes its sheet. Computing this permutation would distinguish a genuinely returning well from two local branches with similar action values.

On a returning sheet, write $L_\alpha(b)$ for the arclength of the part of the well on which the field strength is at most $b$, with $\alpha$ the field-line label on a fixed flux surface. Extend $L_\alpha$ by zero below the well minimum. With the full-bounce convention and particle mass $m$, the action at a regular height is

$$
J_\alpha(h)=2\sqrt{2m\mu}\int_{-\infty}^{h}\sqrt{h-b}\,dL_\alpha(b).
$$

A quantitative theorem would bound $\partial_\alpha J$ from bounds on the label dependence of these sublevel lengths. For instance, a bound on $\partial_\alpha L_\alpha(b)$ that is integrable against $(h-b)^{-1/2}$ gives a direct estimate after integration by parts. A bound on the oscillation of the lengths alone controls action differences but need not control the derivative. The application requires one further theorem connecting this estimate to the radial motion of the physical guiding centre, with a time scale and averaging error. The exact relationship between well geometry and omnigeneity is classical. The research target is a quantitative version with hypotheses accessible to certificates. [Landreman and Catto on omnigeneity](https://arxiv.org/abs/1112.5725) · [Guiding-centre averaging](guiding-centre-averaging.md)

## 2. Which vacuum fields admit a pressure deformation with small net current?

Let $B_0$ be a smooth nonsingular vacuum field on a toroidal shell with constant background pressure. Seek a differentiable family of ideal-MHD equilibria there, and write $p_1$ and $j_1$ for the first variations of pressure and current density. Linearized force balance requires $B_0(p_1)=0$. Wherever $dp_1\ne0$, the level sets of $p_1$ therefore give an invariant foliation. There is a second necessary condition. The equations $j_1\times B_0=\nabla p_1$ and $\operatorname{div}j_1=0$ imply

$$
j_1=\frac{B_0\times\nabla p_1}{|B_0|^2}+\lambda B_0,
\qquad
B_0(\lambda)=-\operatorname{div}\!\left(\frac{B_0\times\nabla p_1}{|B_0|^2}\right).
$$

Along every closed field line parametrized by $\dot x=B_0(x)$, the right-hand side must integrate to zero over one period. Can the foliation and period conditions, together with boundary, curl and net-current constraints, give a checkable obstruction or a sufficient linear solvability theorem? Either result could guide the choice of a vacuum field. A complementary approach uses pressure jumps on selected tori. Enciso, Luque and Peralta-Salas prove existence of piecewise-smooth equilibria in nondegenerate toroidal domains. Applying their construction here would also require control of transform, net current and stability. [Enciso, Luque and Peralta-Salas](https://doi.org/10.4171/jems/1410)

## 3. Can a toroidal pressure interface be stable with adverse curvature on part of it?

Let an embedded torus $\Sigma$ separate two equilibrium regions, and let $f$ be an admissible normal displacement. Seek geometric hypotheses on the magnetic fields tangent to its two sides, the second fundamental form of $\Sigma$, and the conducting wall that give a positive lower bound for the interface energy $\delta^2 W[f]$ in an appropriate norm, after removing neutral motions.

The question on torus A is whether magnetic bending over the whole surface can compensate for the adverse patch already certified in Lean. The cylinder theorem provides a benchmark with explicit hypotheses. Either a positive toroidal estimate or a localized displacement of negative energy would help decide whether to retain this interface. A proof of interface stability would still leave the bulk modes to control. [Cylinder interface energy](cylinder-interface-stability.md) · [Obstruction on torus A](dommaschk-interface-obstruction.md)

## Research priorities

Pursue well continuation and quantitative action control for C2 alongside the infinitesimal pressure-deformation test for C4. Both can change which examples merit expensive certificates. C3 becomes better posed once a viable pressure equilibrium is in hand. Progress on C5 depends most strongly on a transport model and an operating point.

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-69` |
| Title | Stellarator conditions C1–C5 and three geometric research questions |
| Kind | Research assessment |
| Addresses | G-8, Q-20, Q-31, Q-35 |
| Depends on | N-33, N-34, N-44, N-51, N-55, N-58, N-60, N-68 and the stellarator contract |
| Dependency requirement | Use the same field for a combined claim. Thermal C2 additionally requires a physical dynamics model and population. |
| Produces | A condition-by-condition assessment and three proposed mathematical research directions. |
| Difficulty | Research. The outstanding steps concern global well continuation, quantitative physical averaging, pressure solvability and toroidal interface energy. |
| Status | Exploratory. N-72 proves the sublevel-length comparison and derivative estimate in the first research direction. Its physical hypotheses and the other two directions remain open. [Compiled action theorem](bounce-action-sublevel-arclength.md) |
| Lean evidence | Existing on-demand candidate results include `dommaschk_nested_embedded_C1`, `dommaschk_Q16_embedded` and `DommaschkPhysicalPrefix016.exists_nested_prefix`. The reusable results include `FieldTorus.embeddedTorus_of_irrational` and `FaceBounds.stays_inside`. |
| Audit evidence | [23 November audit](../audit/2026-11-23-refresh-audit.md), especially AV-M7 and AV-M8 on the scope of C2. The 20-slab workstation snapshot used prefix key `c9d961f1b210`. |
| Last updated | 24 November 2026. Assessment requested in discussion of the C1–C5 conditions and priorities for geometry and topology. |
