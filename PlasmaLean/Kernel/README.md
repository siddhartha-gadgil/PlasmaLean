# Kernel/

The domain model: definitions and external laws, kept small. Each law is a **typeclass** or a
structure with explicit fields, passed as a hypothesis, never an `axiom`; theorems hold for every
object satisfying it. Each module docstring says it is a kernel file. All six modules are in the
default build.

| Module | Content |
| --- | --- |
| [`Equilibrium`](Equilibrium.lean) | Algebraic static MHD at a point: `Vec3`, the law `ForceBalance B J g` (`J × B = ∇p`) |
| [`Slab`](Slab.lean) | Static MHD in a Cartesian slab: `StaticSlab B J p μ₀` |
| [`ThermalSlab`](ThermalSlab.lean) | Supplied steady slab heat laws `SteadySlab` (an engineering slab, not plasma transport) |
| [`Transport`](Transport.lean) | Flux-surface-averaged radial heat transport: `RadialCoefficients` (regular or degenerate axis, `D(ψ, T) ≥ 0`, kernel K2), `TransportLaws`, `ClassicalRadialSolution`, `RadialHeatTransport` (solutions are supplied, not constructed) |
| [`Vacuum`](Vacuum.lean) | Vacuum magnetic fields on open sets of `Euclid3`: `VacuumField Ω B` (C², div = 0, curl = 0) |
| [`Fusion`](Fusion.lean) | 0-D D-T burning plasma: `DTPlasma`, `PhysicalPlasma`, `ReactivityWindow`, `BoschHaleDT` (cited rational enclosures of ⟨σv⟩), `PowerBalance` |

Rules: keep the kernel small; record every change in the module docstring and the assumption
ledger (`notes/formalization/00-model-contracts.md`); give every law the sanity triad and
risk-specific adversarial checks in `Sanity/`; a strict audit reviews every declaration here
(skill `plasmalean-audit-domain`). Guiding-centre models (Littlejohn, Boozer) and stability
reductions are supplied as hypotheses in `Theory/`, not in this folder.
