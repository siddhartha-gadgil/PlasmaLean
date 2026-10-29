# Design/

Concrete candidates and their certificates: exact fields and equilibria, decoded data emitted by
the oracles in `scripts/`, and the theorems composing kernel laws, theory, bridges and
certificates into claims about a specific candidate (skill `plasmalean-design-stellarator`).
About 1,280 modules, of which about 520 are in the default build; most of the rest are generated
check modules of the on-demand KAM families.

## Families (default build unless marked)

| Family (module prefix) | Content | Headline declarations |
| --- | --- | --- |
| `Solovev*` | Reactor-scale Solov'ev equilibrium: alphas, transport bands, Mercier and ballooning on every surface (reductions supplied), coarea and flux geometry | `reactor_alpha_confined`, `solovev_one_plasma_actual` (transport solution supplied, pressure budget), `reactor_mercier_stable`, `reactor_ballooning_all` |
| `Helical*`, `ScrewPinch*`, `SlabExample`, `PolyTokamak`, `Clebsch*` | Exact symmetric equilibria, transport barrier on the helical geometry, helical Mercier instability, screw-pinch modes | `stable_uniform` (Newcomb, all modes m ≠ 0) |
| `BurnWindow*`, `TransportBarrier`, `QuasilinearBarrier` | 0-D burn windows (IPB98, ISS04/Stellaris) and radial transport barriers | `m1_burn_window`, `stellaris_measured_fren_no_access_steady` |
| `Validated*`, `ScalarRoot` | Radii-polynomial validation: BVP and slab Grad–Shafranov | `validated_bvp`, `validated_slab_equilibrium` |
| `RationalStellarator*` (field, axis, cover, confined, forever, field lines) | Exact rational vacuum stellarator field; 95-transit certificate; all-time field-line confinement | `rationalStellarator_confined`, `rationalStellarator_confined_forever_exists` |
| `Kam*` (`KamTorusA*`, `KamFlow*`, `KamNewton*`, `KamIteration`) | The explicit-constant KAM theorem applied to torus A; generic `FlowField` version | `KamTorusAExact` |
| `RationalStellaratorGC*` | Guiding-centre KAM for 3.5 MeV alphas (Littlejohn model supplied): Torus/NegTorus, Fam (B₀R₀ range), Mu (λ ∈ [0, 1/16]), Box; on demand: Mu2–Mu5, MuWide, MuQuarter, Ew1–4/EwComb/EwFamily | `alpha_gc_confined_forever_pm`, `alpha_gc_confined_forever_robust`, `alpha_gc_passing_confined_forever`, `alpha_gc_confined_forever_velocity_set` |
| `NearAxisQA*` | Near-axis QA reactor model: passing alphas by averaging, trapped-alpha bounce, cells and oscillatory kick | `alpha_trapped_reactorQA_averaged` (passing, 0.19 s), `reference_kick_osc` |
| `PolygonCoil*`, `RationalStellaratorCoils*` | Polygonal and cubic coil sets, line/chunk/filament certificates, transfer to field-line confinement | `coil_stellarator_confined_concrete` (1 transit), `coil_stellarator_confined_concrete_N` (52 transits; field-line existence assumed) |
| `CoilKam*`, `CoilField*` | Coil-field KAM tools (default build); demonstration residual certificate (on demand, vacuous bound) | — |
| `Landreman*` | Landreman finite-β families 1 and 2: force balance, Mercier (index supplied), ballooning reduction, quadrature certificates | `family1_mercier_unstable`, `family2_mercier_stable_derived`, `family2_stable_of_cert`, `family2_stable_of_secular_cert` |
| `Vacuum*` | Tolerance-aware two-coil vacuum fixture (`notes/design/vacuum-demonstrator.md`) | `VacuumPair.robust_probe_field` |

## On-demand top modules (not imported by `PlasmaLean.lean`)

| Top module | Result | Notes |
| --- | --- | --- |
| `RationalStellaratorGCMuQuarter` | `alpha_gc_passing_confined_forever_quarter`: λ ∈ [0, 1/4], one energy and B₀R₀ | combines Mu–Mu5 (Mu2–Mu5 built on the workstation) |
| `RationalStellaratorGCMuWide` | `alpha_gc_passing_confined_forever_wide`: λ ∈ [0, 1/8] | |
| `RationalStellaratorGCEwFamily` | `alpha_gc_confined_forever_energy_window`, `alphaEwVel_volume_pos`: ±0.4 eV × λ ∈ [0, 1/16], positive measure | ≈ 70 CPU-min, 343 modules |
| `CoilKamCert` | coarse sampled residual certificate of a coil-refitted torus | vacuous (≈ 10⁹ vs ≈ 10⁻³⁰ needed); ≈ 830 CPU-s |

Build with `lake build PlasmaLean.Design.<Top>`, after building stale dependencies one at a time;
axioms in `scripts/check_axioms_heavy.lean`. They are verified under the workstation policy
(workstation build, laptop spot checks; `workstation/REVIEWED.md`) and are stale after the Phase 16
stage 8–9 changes until rebuilt (`Workstation.md`, Next Commands).

Conventions: generated data in their own modules (≤ 6 GB peak per module; private oleans of the
explicit certificates count against the approved disk budget); main theorems registered in
`scripts/check_axioms.lean`; every design claim names its supplied laws and reductions.
