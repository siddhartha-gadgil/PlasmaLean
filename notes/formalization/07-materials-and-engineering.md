# Materials, component physics, and engineering constraints

Practical stellarator design requires coupled thermal, mechanical, electromagnetic, nuclear, and lifetime models. This note gives explicit model interfaces and theorem targets. Empirical constitutive data remain supplied hypotheses with provenance and applicability envelopes.

This chapter was first written on 12 October 2026 as a planning specification. It was revised on 30 October 2026 against the current library and the stellarator contract (clauses C1–C5; see the [implementation plan](../implementation-plan.md#the-stellarator-contract-30-october-2026)). The equations and theorem targets below are unchanged. Each section now says what is compiled, what is supplied and what is open. Engineering is the least developed part of PlasmaLean: one exact thermal model, one synthetic component margin and the coil-tube clearance of the vacuum demonstrator are compiled, and everything else in this chapter is open.

## Contents

- [Status in PlasmaLean](#status-in-plasmalean)
- [Relation to the stellarator contract](#relation-to-the-stellarator-contract)
- [Material laws and validity envelopes](#material-laws-and-validity-envelopes)
- [Heat loads and cooling](#heat-loads-and-cooling)
- [Mechanical support and stress](#mechanical-support-and-stress)
- [Superconducting magnets and tape strain](#superconducting-magnets-and-tape-strain)
- [Quench and electrical protection](#quench-and-electrical-protection)
- [Neutron transport, shielding, and breeding](#neutron-transport-shielding-and-breeding)
- [Damage, erosion, fatigue, and service life](#damage-erosion-fatigue-and-service-life)
- [Power and maintainability](#power-and-maintainability)
- [Theorem backlog](#theorem-backlog)

## Status in PlasmaLean

Status on 30 October 2026, checked against the Lean sources. All compiled items are in the default build and use standard axioms only.

| Topic | Compiled (Lean declarations) | Supplied (hypotheses) | Open |
| --- | --- | --- | --- |
| Steady slab heat (M2) | Kernel law `SteadySlab` (`Kernel/ThermalSlab.lean`); `slabTemperature`, `slabMaximum`, `slab_solution`, `slab_unique`, `slab_le_maximum`, `slabMaximum_mono`, `slab_model_bound` (`Theory/Engineering/SlabHeat.lean`) | Constant `k`, `h_c`, uniform `Q`, 1-D geometry; applicability to a real component | Interface resistance, temperature-dependent `k`, 2-D/3-D comparison theorem, coolant enthalpy identity |
| Synthetic component margin | `synthetic_slab_bound`, `synthetic_slab_margin`, `synthetic_corner_exact`, `synthetic_slab_model_margin` (`Design/SlabExample.lean`): every input in the box and every point of the slab is at least `998/45 K` below an invented `1000 K` limit | All inputs and the limit are invented test values, not material data | A sourced load envelope and a sourced allowable temperature |
| Slab audit (strict audit, 30 October) | `steadySlab_unloaded`, `steadySlab_rejects_isothermal`, `steadySlab_energy_balance`, `steadySlab_cold_face_ge`, `steadySlab_zero_thickness`, `steadySlab_zero_thickness_exists` (`Sanity/AuditThermalSlab.lean`) | — | Recorded low finding T-1: `SteadySlab` admits zero thickness (regression theorems `steadySlab_zero_thickness`, `steadySlab_zero_thickness_exists`) |
| Coil clearance (vacuum demonstrator) | `coil_clearance` (0.4 m between centrelines), `perturbed_clearance`, `WithinTolerance`, `manufactured_tube_clearance` (5 mm tube envelopes with 1 mm centreline errors stay at least 388 mm apart), `combined_field_error`, `robust_probe_field` (`Design/VacuumPair.lean`, `Design/VacuumTolerance.lean`) | Invented tolerance budget (1 mm, 1 %, 5 mm); filament field | Embedded winding packs, finite-conductor field, peak field in the conductor, strain |
| Power to the wall | `m2_exhaust_power`, `m2_exhaust_power_numeric` (`Design/TransportBarrier.lean`): on the idealized cylinder of rung M2, the conductive power to the wall lies between 83 MW and 1.12 GW for every supplied solution between the barriers | Transport model, χ range, Bosch–Hale enclosures (`BoschHaleDT`), cylinder geometry | A wall heat flux in W/m² on a stellarator candidate, and its link to the slab bound |
| D–T energy constants | `alphaEnergy` (3500 keV) and `fusionEnergy` (17589 keV) in `Kernel/Fusion.lean` | Bosch–Hale reactivity (`BoschHaleDT`, `BoschHaleFine`) | Neutron source, transport, heating, breeding |
| Mechanics, magnets, quench, neutronics, damage, power, maintenance (M3–M10) | none | — | all |

No question in the research graph (plan RG.2) is yet dedicated to engineering. The engineering targets of this chapter enter the graph through goal G-8 (the integrated candidate) and through the wall-limit part of clause C5 (goal G-2). They should be registered as `Q-*` questions when a candidate makes them concrete.

**Corrected or clarified since 12 October.** The slab "first exact thermal theorem" is now compiled rather than planned. The synthetic box is a checker fixture, not a material qualification; this caveat is also stated in the Lean module docstring. The vacuum-demonstrator tubes are enclosing sets, not proved embedded winding packs, and the field still uses filaments.

## Relation to the stellarator contract

Clause C5 (thermal performance; goal G-2) requires the core temperature to stay above a burn threshold **and below wall and material limits** on the same candidate that satisfies C1–C4. This chapter provides the second half of that requirement:

- **Wall heat flux.** The plasma side must deliver a certified heat flux `q''` or a load envelope at the wall (from a transport or exhaust certificate). The component side must then show that the wall stays below a sourced allowable temperature and stress, for example with the slab bound of this chapter or a later PDE certificate. Both sides exist only in model form today. The power to the wall is bounded on the idealized cylinder (`m2_exhaust_power_numeric`), and the slab margin is proved for invented inputs. Neither is on a stellarator candidate.
- **Neutron loads.** C5 uses alpha heating from Bosch–Hale. The same reactions carry 14.1 MeV neutrons, whose wall and blanket loads belong to this chapter (open).
- **Coils.** C1 asks for rotational transform from the external field, so the coils carry the whole confining field. Their conductor margin, strain, stress and quench protection (sections below) are part of goal G-8, not of C1 itself.
- **Integrated candidate (G-8).** G-8 asks for C1–C5 with common witnesses and then coils and engineering margins on the same decoded candidate (rung M6). The composition layer `Bridge/Contracts` (`DesignContracts`, `compose_branch`, `incompatible_witnesses`) is the only compiled part of that integration.

Engineering margins never upgrade a plasma claim, and a plasma theorem never certifies a component. The two meet only through explicit interface data (loads, geometry, temperatures) attached to one candidate.

## Material laws and validity envelopes

Describe a material by composition, grade, manufacturing history, orientation, joint/interface construction, and evolving state. Possible state variables are temperature `T`, strain `ε`, stress `σ`, irradiation dose `d`, helium/hydrogen content, cycle count, and accumulated plastic strain.

Source lower/upper envelopes for:

| Law | Inputs | Output / theorem use |
| --- | --- | --- |
| Thermal conductivity `k`, heat capacity `c_p`, density | Temperature, composition, dose | Heat equation, positive capacity/conductivity |
| Elasticity tensor `C`, thermal expansion `α` | Temperature, orientation, dose | Coercivity, displacement/stress bounds |
| Allowable stress/strain/fracture response | Temperature, dose, load history | Margin against specified failure model |
| Critical current density `J_crit` or current `I_c` | `T`, `‖B‖`, field angle, strain, degradation | Superconducting operating margin |
| Electrical resistivity and power-law response | Temperature, current, field, state | Joule heating and quench |
| Fatigue/creep/erosion response | Cyclic load, time, temperature, particle spectra | Service-life envelope |
| Nuclear reaction/damage coefficients | Isotope, neutron energy, temperature | Heating, breeding, activation, dose |

Represent these as explicit law bundles with a validity predicate and interval bounds. Keep deterministic envelopes distinct from a confidence statement about a fitted model. Do not extrapolate unirradiated room-temperature properties into hot irradiated operation.

**Status.** Open. No material law bundle exists in Lean yet. The only constitutive inputs in the library are the constants `k` and `h_c` of the slab model, passed as explicit parameters.

[Knaster–Moeslang–Muroga](09-literature.md#engineering-materials-and-experiment) surveys fusion-material challenges. [DEMO divertor work](09-literature.md#engineering-materials-and-experiment) provides concrete component/load examples. [Huslage et al.](09-literature.md#engineering-materials-and-experiment) connects REBCO tape mechanics to stellarator optimization. None makes one scalar limit universal for every grade or device.

## Heat loads and cooling

Distinguish plasma-facing boundary heat flux `q''` in `W/m²`, volumetric neutron/Joule heating `Q` in `W/m³`, and total component power in `W`. Obtain the first from a transport/exhaust certificate or a supplied worst-case envelope, and the second from neutron/electromagnetic models.

For a solid body,

$$
\rho_m c_p(T,d)\partial_tT
=\nabla\cdot(k(T,d)\nabla T)+Q_{\rm neutron}+Q_{\rm Joule}.
$$

Use tensor `k` for anisotropic materials. Specify initial temperatures, material interfaces, thermal contact resistance, radiation, cooling, and applied heat boundary conditions. Prove energy balance, positivity/comparison statements, and temperature bounds with the needed regularity.

**Status.** Only the steady 1-D slab below is compiled. On the plasma side, the conductive power to the wall is bounded on the idealized cylinder (`m2_exhaust_power`, `m2_exhaust_power_numeric`), but it is a total power on a test-bed geometry, not a heat-flux distribution on a stellarator wall. Turning a C5 transport certificate into a wall load `q''` is open.

### First exact thermal theorem

Take a steady one-dimensional slab `0≤x≤h` with `h>0`, constant `k>0`, uniform `Q≥0`, incoming heat flux `q''≥0` at `x=h`, and convective cooling at `x=0` with `h_c>0` and coolant temperature `T_c`. Assume all generated/applied heat exits through the cooled face. The boundary laws are `kT'(h)=q''` and `kT'(0)=h_c(T(0)-T_c)`. Solving `-kT''=Q` gives

$$
T_{\max}=T(h)
=T_c+\frac{q''+Qh}{h_c}
       +\frac{q''h}{k}+\frac{Qh^2}{2k}.
$$

**Compiled.** The kernel law `SteadySlab` states the model for a classical solution with explicit derivative and boundary laws. `Theory/Engineering/SlabHeat.lean` proves the solution formula (`slab_solution`), uniqueness of classical solutions (`slab_unique`), the boundary fluxes (`slab_hot_flux`, `slab_cold_flux`), the maximum at the loaded face (`slab_at_hot_face`, `slab_le_maximum`), monotonicity in every input (`slabMaximum_mono`) and the bound for every solution of the model (`slab_model_bound`). The text below is the specification these declarations implement.

Prove the solution, boundary fluxes, monotonicity, and maximum location. With conservative `k≥k_min`, `h_c≥h_c,min` and upper input bounds in this constant-coefficient family, certify a temperature margin against a supplied lower allowable-temperature limit. Do not substitute this formula into arbitrary 3-D or variable-coefficient geometry without a comparison theorem.

A synthetic exact-arithmetic test fixture uses the entire parameter box

| Input | Interval | SI unit |
| --- | --- | --- |
| `T_c` | `[300,330]` | K |
| `q''` | `[8×10⁶,10⁷]` | W/m² |
| `Q` | `[0,2×10⁷]` | W/m³ |
| `h` | `[3/1000,1/250]` | m |
| `k` | `[90,110]` | W/(m K) |
| `h_c` | `[50000,80000]` | W/(m² K) |

Monotonicity selects the upper `T_c,q'',Q,h` and lower `k,h_c` corner. The maximum is `44002/45 K`, less than an illustrative `1000 K` limit by `998/45 K`. These inputs and limit are invented for a checker/sanity example; they are not sourced material qualification data. The mathematical bound covers the whole stated box, conditional on the slab model.

**Compiled.** `synthetic_slab_bound` and `synthetic_slab_margin` prove the bound and the `998/45 K` margin for every input in the box and every point of the slab. `synthetic_corner_exact` shows that the corner attains `44002/45 K`, so the bound is sharp. `synthetic_slab_model_margin` gives the same margin for every classical solution of `SteadySlab`, not only for the closed-form profile.

For a simplified fully conducting interface resistance `R_th` at the cooling side, add `R_th(q''+Qh)` under its own boundary law. (Open: not in Lean.)

For a steady single coolant stream with specific enthalpy `h_f(T)` satisfying `dh_f/dT=c_p(T)`, no energy storage or other work, and negligible kinetic/potential-energy changes, prove

$$
P_{\rm removed}
=\dot m\int_{T_{\rm in}}^{T_{\rm out}}c_p(T)\,dT.
$$

**Status.** The coolant energy identity is open; it is the remaining part of backlog item M2.

A network model can give an early flow/temperature certificate. Boiling, critical heat flux, pumping limits, coolant transients, leakage and flow interruption require additional explicit models; a minimum mass-flow assumption cannot simultaneously describe a pump-failure event.

Model an island divertor and detachment as a distinct plasma-edge/exhaust problem (open). Extract useful measured envelopes from [W7-X divertor literature](09-literature.md#engineering-materials-and-experiment), keeping operating conditions and transfer assumptions.

## Mechanical support and stress

For small-strain quasi-static elasticity use

$$
\epsilon(u)=\tfrac12(\nabla u+\nabla u^\mathsf T),
$$
$$
\sigma=C(T,d):
\left(\epsilon(u)-\epsilon_{\rm thermal}
                  -\epsilon_{\rm irradiation}
                  -\epsilon_{\rm plastic}\right),
$$
$$
\nabla\cdot\sigma+J_{\rm cond}\times B+f_{\rm pressure}+f_{\rm other}=0.
$$

Define supported boundaries and traction interfaces. For a linear elastic submodel set plastic strain to zero explicitly. Require uniform positivity of the elasticity tensor, remove rigid motions with justified constraints, and prove the relevant Korn/trace estimates before existence or a posteriori stress bounds.

An early theorem can analyze a fully axially restrained uniform bar with spatially uniform temperature change `ΔT`, constant Young modulus `E` and expansion coefficient `α`:

$$
\sigma=-E\alpha\Delta T.
$$

Prove this from the bar model; it is not the stress tensor of every heated coil or wall. For an otherwise load-free constant-section bar restrained only at its ends, with spatially varying temperature and constant `E,α`, the uniform axial stress instead uses the length average: `σ=-Eα L⁻¹∫₀ᴸ ΔT(s) ds`. A later beam model should distinguish bending, torsion, deflection, and local buckling.

For an isotropic ductile failure proxy define

$$
\sigma_{\rm vm}=\sqrt{\tfrac32\,s:s},\qquad
s=\sigma-\tfrac13\operatorname{tr}(\sigma)I.
$$

A feasible pointwise contract is `σ_vm ≤ σ_allow(T,d)/SF` with declared `SF>1` and sourced allowables. This does not automatically cover brittle fracture, REBCO delamination, fatigue, contact, anisotropic failure, or irradiated tungsten fracture. Use separate predicates/constitutive laws for those mechanisms.

Manufacturing and thermal deformations change both clearances and magnetic geometry. Carry a proved displacement/strain bound back into [06-coils-and-design.md](06-coils-and-design.md).

**Status.** Mechanics is open (backlog M3, M7). The nearest compiled result is geometric: in the vacuum demonstrator, `perturbed_clearance` and `manufactured_tube_clearance` show that coil centrelines displaced by a stated amount keep a stated clearance. A future displacement bound from an elastic model would supply exactly the displacement hypothesis of those theorems (`WithinTolerance`).

## Superconducting magnets and tape strain

Distinguish operating plasma field from peak field inside the conductor. The superconducting margin requires the latter and its orientation. A useful contract is

$$
|I|\le \eta\, I_{c,\min}(T,|B|,\vartheta,\epsilon,d),\qquad 0<\eta<1,
$$

throughout the conductor and operating envelope, together with a thermal margin and a valid conductor/current-sharing model. Use specified NbTi, Nb₃Sn, or REBCO data rather than one generic superconductor threshold.

Represent a winding pack as

$$
X(s,a,b)=r(s)+a\,d_1(s)+b\,d_2(s),
$$

where `r` is arclength-parametrized and `(d₁,d₂,d₃=r')` is a material frame. Prove embedding, positive volume Jacobian, and clearance. For a straight reference fibre with coordinate `s`, its geometric longitudinal stretch is

$$
\lambda(s,a,b)=|\partial_sX(s,a,b)|,\qquad
\epsilon_{\rm geom}=\lambda-1.
$$

The stress-free/reference geometry and fabrication strain must be specified; this geometric stretch alone is not the full constitutive strain of a manufactured tape.

For planar pure bending, the small-strain maximum is proportional to half-width times hard-way curvature, or half-thickness times easy-way curvature. For pure uniform twist of a straight axis at offset radius `r_f`,

$$
\epsilon_{\rm geom}=\sqrt{1+(r_f\tau)^2}-1.
$$

**Status.** Open (backlog M4, M5). No winding-pack frame, strain or critical-surface model is in Lean. The vacuum demonstrator encloses each filament in a 5 mm tube (`manufactured_tube_clearance`), but proves neither embedding of a winding pack nor any conductor margin.

Prove these special cases from the frame formula. Certify the full geometry for combined bend/twist and across every tape/turn, rather than adding approximate strain formulas without an error estimate. Account for winding angle, joints, pack deformation, cooldown, preload, and irreversible degradation. [Huslage et al.](09-literature.md#engineering-materials-and-experiment) is a concrete implementation reference.

## Quench and electrical protection

Use a specified electric/thermal constitutive law. A simplified superconducting power law is

$$
E=E_c\left(\frac{|J_{\rm cond}|}{J_{\rm crit}}\right)^n
     \frac{J_{\rm cond}}{|J_{\rm cond}|}
$$

away from `J_cond=0`, extended by `E(0)=0`, with `E_c,J_crit,n>0`. Here `J_cond` is vector conductor current density and `J_crit` the scalar critical density. Its dissipation `J_cond·E≥0` is an elementary theorem; the law's empirical applicability is separate.

For a lumped coil with constant `L>0`,

$$
L\dot I+(R(T)+R_d)I=V_s,\qquad
\frac{d}{dt}\left(\tfrac12LI^2\right)
=V_sI-(R(T)+R_d)I^2.
$$

Prove stored-energy and dump-energy bounds. Couple resistive heat to

$$
C(T)\dot T=R(T)I^2+P_{\rm nuclear}-P_{\rm cooling}
$$

with `C(T)>0` and validated coefficients. A multi-coil model needs an appropriate positive inductance matrix and mutual-coupling dynamics.

First certify the zero-supply dump case with fixed coefficients. Then include detection delay, hotspot temperature, terminal/inter-turn voltage, current sharing, and thermal diffusion. A normal-operation current margin does not prove survival of a quench; quench protection has its own event and time horizon.

**Status.** Open (backlog M6). Neither the dissipation lemma `J_cond·E≥0` nor the lumped dump-energy identity is in Lean yet; both are short first targets.

## Neutron transport, shielding, and breeding

For D–T fusion, track approximately `17.6 MeV` per reaction partitioned into alpha and neutron energy (approximately `3.5` and `14.1 MeV` respectively). Use exact model constants or declared input intervals and a reaction-rate envelope from [04](04-particles-and-transport.md).

**Status.** The kernel fixes `fusionEnergy` = 17589 keV and `alphaEnergy` = 3500 keV (`Kernel/Fusion.lean`), and the reaction rate is enclosed by the supplied Bosch–Hale windows (`BoschHaleDT`, `BoschHaleFine`). These feed alpha heating in the burn theorems (C5). The neutron share, the transport equation, heating, breeding and shielding are open (backlog M8, M9).

A linear neutron-transport model for angular flux `ψ_n(x,\omega,E,t)` is

$$
\frac1{v(E)}\partial_t\psi_n+\omega\cdot\nabla\psi_n
+\Sigma_t\psi_n
=\int\Sigma_s(E',\omega'\to E,\omega)\psi_n(E',\omega')\,dE'd\omega'
+Q_n,
$$

with explicit incoming boundary conditions and additional neutron-producing reaction terms where needed. Supply microscopic/macroscopic cross-section conventions, isotope densities, and uncertainty from a pinned [IAEA FENDL](09-literature.md#engineering-materials-and-experiment) dataset.

Define nuclear heating, dose, and reaction rates as positive integrals of the certified flux against the relevant response kernels. Establish source normalization, centimetre/metre and eV/joule conversions, and any group/mesh error. [OpenMC documentation](09-literature.md#design-algorithms-and-software) describes simulation/tally conventions; Monte Carlo confidence intervals are statistical statements rather than guaranteed deterministic enclosures.

For a monoenergetic directed beam with constant macroscopic attenuation `Σ≥0`, no scattering or other sources, and path-length coordinate `x` (for example normal incidence on a uniform slab),

$$
\Phi_{\rm beam}(x)=\Phi_{\rm beam}(0)e^{-\Sigma x}.
$$

Prove attenuation and use upper source/lower attenuation bounds. General angular scalar flux need not obey this formula even without scattering; scattering and streaming through ports require a transport estimate.

Define breeding by

$$
\mathrm{TBR}=
\frac{\text{tritium production rate in blanket}}
     {\text{D--T tritium consumption rate}},
$$

assuming positive consumption. Require a specified margin above the consumption and losses relevant to the plant, rather than imposing a universal chosen number. Couple it to a tritium-inventory model with extraction, decay, retention, processing delay, and reserve constraints.

## Damage, erosion, fatigue, and service life

Using energy-dependent scalar neutron flux `Φ(E,t)` and a displacement cross section per atom `σ_dpa(E)`, one damage model is

$$
d(t)=\int_0^t\int\Phi(E,\tau)\sigma_{\rm dpa}(E)\,dE\,d\tau.
$$

Do not divide by atomic density again if the cross section already describes displacements per target atom. Specify the displacement model and its conventions; dose is not itself a complete material-degradation law.

Use a nonnegative activation/transmutation inventory ODE `N'=A(Φ,T)N+s`. Under Metzler/nonnegative-source conditions, prove nonnegative inventories and selected bounds. Track helium/hydrogen production and link it to sourced constitutive envelopes.

For a simplified erosion law,

$$
\dot h_{\rm loss}
=\frac{\Gamma_{\rm incident}Y(E,\vartheta,T,\text{state})}{n_{\rm solid}},
$$

where `Y` is sputter yield and `n_solid` atomic number density. Add redeposition, transients, chemical effects, and mixed-material evolution only through defined extensions. Couple eroded thickness to temperature, strength, and clearance.

For an explicitly assumed cumulative fatigue law such as `D_f=Σ_i n_i/N_i`, prove the arithmetic implication from a cycle/load envelope to `D_f≤D_allow`. Its empirical predictive validity is not proved by that arithmetic. Brittle-fracture and creep models require separate load-history/degradation laws.

**Status.** Open (backlog M8–M10). None of these laws is in Lean.

A service-life theorem should quantify over the stated operation history, source envelopes, temperatures, irradiation state, and uncertainty. Return a conservative time/cycle bound and the active limitation. Use repair/replacement schedules as part of the state evolution where relevant.

## Power and maintainability

Define gross electrical output using a specified heat-conversion law and subtract auxiliary heating, cryogenic refrigeration, coolant pumping, current supply, fuel processing, and other recirculating loads. Certify a positive net-power margin only for the coupled model; a plasma triple product or ideal-MHD stability proof is insufficient.

Maintenance requires access volume and collision-free removal paths for blankets, divertor units, coils, and supports, accounting for activation/cooldown constraints where modelled. These geometric constraints may limit design before a physics optimum is reached.

**Status.** Open. A net-power margin depends on C5 (thermal performance) holding on the same candidate, and C5 is shown today only on a tokamak model (Solov'ev, `solovev_one_plasma_actual`) and in 0-D on stellarator parameters (`Design/BurnWindowStellarator`).

## Theorem backlog

The progress column of the generated page reports Lean status. Only M2 has compiled content (slab part done; coolant identity open). The contract column says where each item enters the stellarator contract or the goal registry.

| ID | Target | Scope / main dependency | Contract link |
| --- | --- | --- | --- |
| M1 | Material envelope semantics and consistent examples | Data provenance and parameter domains | C5 (material limits), G-8 |
| M2 | Exact slab heat bound and coolant energy identity | Elementary calculus; first realistic-margin API | C5 (wall limits) |
| M3 | Restrained-bar stress and elastic-energy positivity | Simplified mechanics | G-8 |
| M4 | Ribbon stretch, bend/twist cases, continuous strain bounds | Material frames and interval geometry | G-8 (coils producing the C1 field) |
| M5 | Current/temperature/field critical-surface margin | Finite conductor field and sourced conductor data | G-8 (coils producing the C1 field) |
| M6 | Lumped dump/quench energy and hotspot bound | Coupled ODEs and event timing | G-8 |
| M7 | Thermal/elastic PDE a posteriori certificates | Coercivity, trace, regularity and verified FEM | C5 (wall limits), G-8 |
| M8 | Absorption shield, inventory positivity, erosion/fatigue arithmetic | Explicit reduced laws | C5 (material limits), G-8 |
| M9 | Full neutronics/breeding/damage certificate | Transport analysis, data, geometry and uncertainty | C5, G-8 |
| M10 | Robust lifetime and net-power design contract | Coupled sources, material evolution and service schedule | G-8 |

Suggested first steps, none of them started: the coolant enthalpy identity (completes M2); the dissipation lemma and lumped dump energy (M6); the restrained-bar stress (M3). Each is elementary and needs a sanity triad (a consistent instance, a degenerate case, a rejected input). The skill `plasmalean-model-materials` describes the method: sourced law bundles as hypotheses, margins over whole operating sets, and explicit interface data to the plasma side.
