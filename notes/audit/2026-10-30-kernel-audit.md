# Strict kernel audit (lane E), 30 October 2026

First strict audit of the PlasmaLean domain kernel under `plasmalean-audit-domain`.

| Item | Value |
| --- | --- |
| Audited commit | `cda8bd0` (default build current at that commit) |
| Toolchain | Lean `v4.34.1`, Mathlib `v4.34.1` (lake manifest) |
| Scope | `PlasmaLean/Kernel/{Equilibrium, Slab, ThermalSlab, Transport, Vacuum, Fusion}.lean` and their sanity coverage in `PlasmaLean/Sanity/*`. The rest of the repository is audited separately (`2026-10-30-repository-audit.md`) |
| Inventory | **52 declarations**: 28 data definitions, 11 laws (Prop classes or structures, 48 fields in total), 3 Prop predicates, 10 theorems; no instances apart from the derived `DecidableEq AxisKind`. Nothing was sampled |
| Findings | critical 0, high 0, **medium 1** (F-1), **low 9**, informational 3 |
| New sanity files | `PlasmaLean/Sanity/Audit{Equilibrium, ThermalSlab, Vacuum, Transport, Fusion}.lean`: 59 theorems and instances. Each module built on its own; all have standard axioms only; zero warnings; no `decide` of any kind; no `sorry` |
| Not edited | every existing Lean file, `PlasmaLean.lean`, the plan and the README. The new modules are **not yet imported** by `PlasmaLean.lean` (for the integrator) |

## 1. Inventory

Status: **def** = definition; **law** = supplied law (Prop class or structure, taken as a hypothesis); **cons** = proved consequence. "Users" counts files outside `Kernel/` (from `rg -lw`), not counting the new `Sanity/Audit*`. Sanity coverage: D = degenerate case, I = concrete instance, C = counterexample, R = risk-specific check. Items marked **new** were added by this audit.

### 1.1 `Kernel/Equilibrium` (algebraic static MHD)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `Vec3` | `Fin 3 → ℝ`, Cartesian data | def | carries Mathlib's sup norm (the docstring says "no norm convention", finding D-1) | 4 | n/a |
| `ForceBalance B J g` | `J × B = g` (field `balance`) | law | pointwise; `g` is free data and must be proved to be `∇p` separately; no Ampère link, no `μ₀` | 17 (Solov'ev family, Landreman families 1–2, helical, slab, screw pinch) | D `zeroBalance`, `uniformBalance`; I `parallelBalance`, `force_free_nonvacuum`, `slab_forceBalance`; C **new** `forceBalance_rejects_perp`; R **new** `pinch_force_inward`, `forceBalance_rejects_reversed` (orientation), `forceBalance_of_cross` (vacuity, E-1), `forceBalance_smul_field`, `forceBalance_smul_current` (scaling) |
| `field_tangency` | `B · g = 0` | cons | as the law | 4 | (follows from the law) |
| `current_tangency` | `J · g = 0` | cons | as the law | 2 | — |
| `gradient_zero_iff_force_free` | `g = 0 ↔ J × B = 0` | cons | as the law | 0 | — |

### 1.2 `Kernel/Slab` (one-coordinate static MHD)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `slabCurl B z` | `(−B_y', B_x', 0)`, the curl of a `z`-dependent field (checked against the Cartesian curl) | def | `deriv` is totalized; the law requires differentiable `B` | 2 | used in all slab checks |
| `StaticSlab B J p μ₀` | `μ₀ > 0`; `B`, `p` differentiable; `J × B = (0,0,p')`; `B_z' = 0`; `slabCurl B = μ₀ J` | law | SI; slab geometry only; **no `p ≥ 0`** (S-1) | 2 (`Theory/Equilibrium/Slab`, `Design/ValidatedSlabEquilibrium`) | D `uniform_slab`; I `helicalSlab_equilibrium`, **new** `slab_negative_pressure` (nonzero gradient); C **new** `slab_rejects_compressive`; R **new** `slab_total_pressure_deriv` (conservation of `p + |B_⊥|²/2μ₀`), `slab_negative_pressure` (missing bound) |

### 1.3 `Kernel/ThermalSlab` (steady slab heat conduction)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `SteadySlab T dT Tc q Q h k hc` | `0 ≤ h`, `k > 0`, `hc > 0`; `T' = dT`, `dT' = −Q/k` on `[0,h]`; `k T'(h) = q`; `k T'(0) = hc (T(0) − Tc)` | law | SI; constant coefficients; derivatives two-sided even at the faces (stronger than needed); **`h = 0` admitted** (T-1) | 2 (`Theory/Engineering/SlabHeat`, `Design/SlabExample`) | I `slab_solution`, uniqueness `slab_unique`; D **new** `steadySlab_unloaded`; C **new** `steadySlab_rejects_isothermal`; R **new** `steadySlab_energy_balance` (conservation `hc (T(0) − Tc) = q + Qh`), `steadySlab_cold_face_ge` (sign), `steadySlab_zero_thickness`, `steadySlab_zero_thickness_exists` (endpoint) |

Signs and units checked: `−kT'' = Q`, the loaded face at `x = h` receives `q` (`kT'(h) = q`), and the cooled face at `x = 0` removes `hc(T(0) − Tc)`. Global balance (`steadySlab_energy_balance`) confirms the orientation.

### 1.4 `Kernel/Vacuum` (current-free magnetostatics)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `Euclid3` | `EuclideanSpace ℝ (Fin 3)` | def | Euclidean norm | 5 | — |
| `coordVec i` | unit vector `eᵢ` | def | — | 5 | — |
| `divOp L` | `∑ᵢ (L eᵢ)ᵢ` | def | — | 5 | `divOp_eq_divergence`, `divOp_id`; **new** `divOp_smul` |
| `curlOp L` | `(∂_yB_z − ∂_zB_y, ∂_zB_x − ∂_xB_z, ∂_xB_y − ∂_yB_x)` | def | — | 7 | `curlOp_eq_curl`; **new** `curlOp_smul` |
| `fieldDiv B x`, `fieldCurl B x` | `divOp (fderiv ℝ B x)`, `curlOp (fderiv ℝ B x)` | def | `fderiv` is totalized (`0` where `B` is not differentiable) | 6, 7 | R **new** `absField_fieldDiv_zero`, `absField_fieldCurl_zero` (totalization) |
| `VacuumField Ω B` | `Ω` open; `B` is `C²` on `Ω`; `∇·B = 0` and `∇×B = 0` on `Ω` | law | no boundary data, no circulation or topology conditions, `μ = μ₀`; **true for every `B` when `Ω = ∅`** (V-1) | 10 (rational stellarator, polygon coils, vacuum pair, curvature obstruction, subharmonic) | D `zero_vacuum`, `const_vacuum`; I `hyperbolic_gradient_vacuum`, `filamentField_vacuumField` (C² supplied), `wireField_vacuum`; C `rotationField_not_vacuum`, **new** `id_not_vacuum`; R **new** `fieldCurl_id`/`fieldDiv_rotationField` (independence of the two laws), `vacuumField_empty`, `rotationField_vacuum_empty` (empty domain), `absField_not_vacuum` (the open-set and C² laws are load-bearing), `VacuumField.const_smul` (linearity) |
| `divOp_apply` | coordinate formula | cons | — | 4 | — |
| `curlOp_eq_zero_iff` | curl free ⇔ symmetric Jacobian | cons | — | 3 | used in `fieldCurl_id` |

### 1.5 `Kernel/Transport` (radial heat transport, K2)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `AxisKind` | `regular` (Neumann) or `degenerate` (`D(0,·) = 0`, no axis condition) | def | — | 1 | `linField_*`; **new** `mislabelled_not_transportLaws` |
| `RadialCoefficients` | `V'`, `V''`, `D(ψ,T)`, `∂ψD`, `∂TD`, `R`, `Tdom`, axis | def (data) | — | 9 | — |
| `RadialCoefficients.op` | `D u'' + (∂ψD + ∂TD u' + D V''/V') u' + R` | def | the division by `V'` is guarded by `Vp_pos` on `[0,1]` only; equals the divergence form only under a chain-rule hypothesis (documented, I-1) | (via `ClassicalRadialSolution`) | `op_divergence_form`, `quasiCyl_divergence_form`, `op_uniform` |
| `RadialCoefficients.semilinear` | `D(ψ,T) := D ψ`, `∂TD := 0` | def | — | via `semilinear_op` | `unitCoefficients`, `cylUnitCoefficients` |
| `semilinear_op`, `semilinear_isSemilinear`, `IsSemilinear.op_sub_op` | operator identities for semilinear coefficients | cons | — | 3, 1, 2 | — |
| `IsSemilinear` | `D`, `∂ψD` independent of `T` and `∂TD = 0` on `[0,1]` | def (Prop) | — | 6 | `quasiCyl_not_semilinear` (C) |
| `UniformlyParabolic c Dmin` | optional floor `0 < Dmin ≤ D` | def (Prop) | — | 1 | `unitCoefficients_uniformlyParabolic` (I), `cylUnit_not_uniformlyParabolic` (C) |
| `UniformlyParabolic.D_nonneg`, `.D_axis_pos` | consequences of the floor | cons | — | 1 | — |
| `RadialField` | `T`, `Tψ`, `Tψψ`, `Tt` (supplied derivatives) | def (data) | — | 11 | — |
| `RadialField.Regular τ u` | joint continuity on `[0,1]×[0,τ]`; one-sided derivative laws | law | `deriv_t` is taken within `Icc 0 τ`; for `τ = 0` this is a singleton and **every value is a derivative** (R-1) | (via the solution class) | `modeField_regular`, `linField`; R **new** `hasDerivWithinAt_Icc_self` |
| `TransportLaws c` | `V' > 0`; derivative laws for `V'`, `D` (both partials); `D ≥ 0`; `D(0,·) = 0` (degenerate); `D(0,·) > 0` (regular); `Tdom` open; `R` continuous on `[0,1] × Tdom` | law | no joint regularity of `D` (I-1); **`D ≡ 0` admitted** (R-3) | 9 | I `unitCoefficients`, `cylUnitCoefficients`, `quasiCylCoefficients`, **new** `posDomainCoefficients`, `noDiffusionCoefficients`; C **new** `mislabelled_not_transportLaws` |
| `ClassicalRadialSolution c Tedge τ u` | `0 ≤ τ`; `Regular`; PDE on the closed rectangle; Neumann at a regular axis; Dirichlet at the edge | law | solutions are supplied (no existence); `τ = 0` gives a vacuous rate (R-1); **values need not lie in `Tdom`** (R-2) | 11 | D `constField_solution`; I `cosMode_radialHeatTransport`, `linField_radialHeatTransport`; C **new** `constField_rejects_source` (PDE), `cosMode_rejects_edge` (edge), `slopeField_rejects_axis` (axis); R `rate_nonpos_of_max`, `axis_rate_nonpos`, `degenerate_axis_rate`, **new** `fakeField_zero_duration`, `fakeField_not_solution` (zero duration), `solution_outside_Tdom` (source domain), `noDiffusion_frozen` (zero parameter) |
| `RadialHeatTransport` | `TransportLaws ∧ ClassicalRadialSolution` | law | as its parts | 2 | as above |

PDE check: `(1/V')(V' D(ψ,T) T')' + R = D T'' + (∂ψD + ∂TD T' + D V''/V') T' + R` (with the chain rule), forward parabolic for `D ≥ 0`. At a degenerate axis the drift `∂ψD(0,·)` is at least `0` (`TransportLaws.degenerateAxis`), so the axis is a Fichera outflow boundary and no condition is posed there. The edge carries Dirichlet data. The statement matches the advertised model.

### 1.6 `Kernel/Fusion` (0-D D-T burn)

| Declaration | Meaning | Status | Validity envelope | Users | Sanity |
| --- | --- | --- | --- | --- | --- |
| `keV` | `1.602176634e-16` J | def (exact SI) | — | 21 | **new** `keV_eq` |
| `alphaEnergy`, `fusionEnergy` | 3.5 MeV and 17.589 MeV | def | — | 7, 5 | `fusionPower_eq`; **new** `neutron_energy` (14.089 MeV) |
| `bremsCoeff` | `5.35e-37 W m³ keV^(-1/2)` (Wesson) | def (empirical) | — | 7 | **new** `bremsCoeff_matches_NRL` (NRL conversion, 1 %) |
| `DTPlasma` | `n, V, Z_eff, f_fuel, r_i` | def (data) | — | 8 | — |
| `PhysicalPlasma p` | `n, V > 0`, `Z_eff ≥ 1`, `0 < f ≤ r_i ≤ 1` | law | **does not link `Z_eff` to `f_fuel`, `r_i`** (F-1) | 5 | I `impurity_physical`, `carbon_fixture`; C **new** `not_physical_zero_density`; R `impurity_consistency`, **new** `inconsistentPlasma_physical`, `fuel_one_forces_Zeff_one`, `carbon_fuel_fraction_two` |
| `impurityFuelFraction`, `impurityIonRatio` | single-impurity `f = 1 − (Z_eff − 1)/(Z − 1)`, `r_i = f + (1 − f)/Z` | def | `Z > 1` (at `Z = 1`, division by zero gives `1`) | 3, 3 | `impurity_consistency`; R **new** `impurityFuelFraction_Z_one` |
| `thermalEnergy` | `(3/2) n (1 + r_i) T keV V` | def | `T_i = T_e` | 7 | `thermalEnergy_zero_density`, `thermalEnergy_pure` |
| `alphaPower`, `fusionPower` | `(E/4)(f n)² ⟨σv⟩ V` | def | — | 8, 5 | zero density, nonnegativity, monotonicity |
| `bremsPower` | `C_br n² Z_eff √T V` | def | `√T = 0` for `T ≤ 0` | 7 | `bremsPower_nonneg`; R **new** `bremsPower_of_nonpos` |
| `lossPower` | `W/τ_E` | def | **`τ_E = 0` gives `0`** (F-3); guarded only inside `PowerBalance` | 6 | R **new** `lossPower_zero_tau` |
| `netHeating` | `P_α + P_aux − P_br − W/τ_E` | def | as `lossPower` | 6 | `steady_state_iff`, Lawson; R **new** `netHeating_zero_tau` |
| `ReactivityWindow`, `.Holds` | rational enclosure on a keV window | def, def (Prop) | — | 4 | `WindowsCert.sound` |
| `boschHaleWindows` | 61 windows, 1–100 keV | def (supplied data) | Bosch–Hale 1992, ±1 % | 11 | `boschHaleWindows_consistent`; R **new** `boschHaleWindows_contiguous`, `boschHaleWindows_cover`, `boschHaleWindows_svLo_pos`; external validation §5 |
| `BoschHaleDT sv` | `sv ≥ 0` for `T ≥ 0`; continuous on `T > 0`; monotone on `[1,60]`; the windows | law (empirical) | `[1,100]` keV; unconstrained below 1 keV except `≥ 0` | 15 | I `bhSv_boschHaleDT`, `bhFineSv_boschHaleFine`; C `zero_not_boschHaleDT`, `boschHale_rejects_large_value`; R **new** `BoschHaleDT.pos_of_mem` |
| `PowerBalance p sv Paux τE T` | `τ_E > 0` and `dW/dt = netHeating` for `t ≥ 0` | law | **satisfied by every trajectory when `n = 0`** (F-2) | 6 | I `steady_state_iff`, `ignited_steady_state_iff`; D `noAlpha_strictAnti`; C **new** `powerBalance_rejects_zero_tau`; R **new** `powerBalance_zero_density`, `powerBalance_zero_density_rising` |

## 2. Findings by severity

No critical or high findings. No kernel statement contradicts its advertised physics. The defects are missing bounds and vacuity hazards; for each one I checked how its downstream users stand.

### Medium

**F-1. `Fusion.PhysicalPlasma` admits contradictory composition fields.** The class is named and documented as "physical admissibility", but nothing links `Z_eff` to `f_fuel` and `r_i`. The module docstring itself states that quasineutrality forces `f_fuel < 1` whenever `Z_eff > 1`.
- Counterexample: `⟨1e20, 1, 2, 1, 1⟩` (`f = r_i = 1`, `Z_eff = 2`) is an instance (`inconsistentPlasma_physical`). With `n_fuel = n_e`, quasineutrality forces `Z_eff = 1` (`fuel_one_forces_Zeff_one`). For carbon at `Z_eff = 2` the consistent value is `f = 4/5` (`carbon_fuel_fraction_two`).
- Direction: optimistic. An inconsistent `(f, Z_eff)` overstates the alpha power by up to `1/f²` (`25/16` in the example) against the radiation it carries.
- Downstream: theorems quantified over all `[PhysicalPlasma p]` stay sound, since the class is weaker. The concrete plasmas `m1Plasma` (`Design/BurnWindow`), `stellarisPlasma` (`Design/BurnWindowStellarator`) and `m2Plasma` (`Design/TransportBarrier`) use the carbon-consistent values `(1.7, 0.86, 53/60)`, proved for the first two (`m1Plasma_carbon`, `stellarisPlasma_carbon`). `m2Plasma` has no consistency theorem; it is in the re-audit list.
- Proposed fix: add a law with a declared maximal impurity charge `Zmax ≥ 2`, namely `Zeff − 1 ≤ (Zmax − 1)(1 − f)` and `f + (1 − f)/Zmax ≤ r_i`. Alternatively, a minimal law `Zeff = 1 ∨ f < 1`. Or derive `f`, `r_i` from an explicit species list.

### Low

**E-1. `ForceBalance` constrains nothing until `g` is identified with `∇p`.** `forceBalance_of_cross : ForceBalance B J (J ⨯₃ B)` holds for every `B, J`.
- The module docstring documents this. In the downstream designs I spot-checked (`Design/Solovev`, `Design/LandremanEquilibrium`, `Design/HelicalEquilibrium`), `pressure_hasFDerivAt` proves that `g` is the Fréchet derivative of the pressure, and `J` is the actual Ampère current.
- Fix: none in the kernel. Optionally add a bundled `PressureEquilibrium` structure with fields `g = ∇p` and `J = curl B/μ₀`, so that claims cannot cite `ForceBalance` alone.
- Re-audit: every headline claim citing `ForceBalance` must also cite the derivative theorem (17 user files, §4).

**S-1. `StaticSlab` does not require `p ≥ 0`.** `slab_negative_pressure` gives `B = (0,z,0)`, `J = (−1,0,0)`, `μ₀ = 1`, `p = −z²/2`.
- Downstream: `Design/ValidatedSlabEquilibrium` imposes `p ≥ a/μ₀ > 0` itself. `Theory/Equilibrium/Slab.uniform_slab` accepts any constant `p₀` (harmless).
- Fix: add `pressure_nonneg : ∀ z, 0 ≤ p z`, or a separate `PhysicalSlab` predicate.

**T-1. `SteadySlab` admits zero thickness (`thickness_nonneg : 0 ≤ h`).** At `h = 0` the laws reduce to `hc (T(0) − Tc) = q` (`steadySlab_zero_thickness`, inhabited by `steadySlab_zero_thickness_exists`). This is not contradictory, but it is a degenerate witness.
- Also, the derivative laws are two-sided `HasDerivAt` at the faces, which assumes `T` is defined beyond the slab (harmless).
- Fix: `0 < h`, if no user needs `h = 0` (`Design/SlabExample` uses positive `h`).

**V-1. `VacuumField ∅ B` holds for every `B`** (`vacuumField_empty`, `rotationField_vacuum_empty`). This is expected for a region-based law, but theorems whose conclusions do not mention a point of `Ω` can be vacuous.
- Fix: none in the kernel. Downstream statements should exhibit a point of `Ω` or a nonempty region.
- Re-audit list: `Design/RationalStellarator*`, `PolygonCoil*Confined`, `VacuumPairVolumeError`, `Theory/Fields/{Subharmonic, CurvatureObstruction}`.

**R-1. Zero-duration witness in `ClassicalRadialSolution` / `RadialField.Regular`.** With `τ = 0`, `deriv_t` is a derivative within `Icc 0 0 = {0}`, where every value is a derivative (`hasDerivWithinAt_Icc_self`).
- Counterexample: the time-independent profile `1 − ψ²` with the false rate `−2` is a classical solution of the unit problem (`fakeField_zero_duration`), but it is a solution on no interval of positive length (`fakeField_not_solution`).
- Downstream: the headline transport results (`solovev_one_plasma_actual`, `solovev_one_plasma_actual_coarea`, and the band and barrier theorems I inspected) assume `∀ τ ≥ 0, ClassicalRadialSolution … τ u`, which includes `τ > 0`, so they are unaffected.
- Fix: `tau_pos : 0 < τ`. Alternatively, document that statements must quantify over all `τ`, or assume some `τ > 0`.

**R-2. Solutions are not required to stay in the source domain `Tdom`.** `R_cont` only constrains `R` on `[0,1] × Tdom`, but the PDE evaluates `R` wherever the solution goes. `solution_outside_Tdom` gives a classical solution `T ≡ −1` with `Tdom = (0, ∞)`.
- Downstream: the comparison theorems (`Theory/Transport/Comparison`) assume that the barriers lie in `Tdom` (`hdom`), and a touching point lies on the barrier, so the barrier conclusions are unaffected.
- Fix: add an explicit range predicate (`∀ ψ t, u.T ψ t ∈ c.Tdom`) wherever continuity of `R` along `u` is used, or prove it from the barrier band.
- Re-audit: barrier designs with `Tdom ≠ univ` (`QuasilinearBarrier`, `HelicalTransportBarrier`, the `SolovevBand*` family).

**R-3. Zero-parameter witness: `D ≡ 0` satisfies `TransportLaws` (degenerate kind).** The equation then becomes the ODE `∂ₜT = R` on each surface, and the edge datum is no longer a boundary condition. With `R = 0`, the frozen profile `T = ψ` is a solution for every horizon (`noDiffusion_frozen`). The docstring motivates `D ≥ 0` only by axis degeneracy.
- Fix (optional): require `0 < D(ψ,T)` for `ψ ∈ (0,1]` ("parabolic away from the axis"), or add an optional predicate and use it in any future existence or strong-maximum-principle result.

**R-4. Hygiene: `Sanity/Transport.lean` uses plain `by decide` four times** (`absurd h (by decide)` for `AxisKind` constructor distinctness, lines 179, 229, 268, 294), against the no-`decide` policy.
- Fix: `fun h => nomatch h` (as in `Sanity/AuditTransport`).

**F-2. `PowerBalance` alone is satisfied by every trajectory when `n = 0`** (`powerBalance_zero_density`; for example, a linearly rising temperature with no heating, `powerBalance_zero_density_rising`).
- Downstream: all the substantive `PowerBalance` theorems (`Theory/Transport/PowerBalance` barriers and window, `Theory/Transport/ConfinementScaling` windows, `Sanity/Fusion.noAlpha_*`) also assume `[PhysicalPlasma p]`. `PowerBalance.hasDerivAt` and `LossScaling.loss_eq` do not, but they are identities and stay valid.
- Fix: make `PowerBalance` extend `PhysicalPlasma`, or keep it as is and add this regression to the documentation.

**F-3. Totalized operations in the 0-D definitions.**
- `lossPower p 0 T = 0`, i.e. perfect confinement instead of infinite loss (`lossPower_zero_tau`, `netHeating_zero_tau`).
- `bremsPower` is `0` for `T ≤ 0` (`bremsPower_of_nonpos`).
- `impurityFuelFraction Zeff 1 = 1` (`impurityFuelFraction_Z_one`).
- `sv` is unconstrained for `T < 0`.

`PowerBalance` guards `τ_E > 0`. The standalone uses in `Design/BurnWindowScaling` use positive scaling-law values of `τ_E`.
- Fix: none required. Statements using `netHeating`/`lossPower` outside `PowerBalance` should assume `τ > 0` (as `lawson_ignition_iff` does).

### Informational

- **I-1 (documented).** The expanded transport operator equals the divergence form only under a chain-rule hypothesis for `ψ ↦ D(ψ,T(ψ))`. The separate partial-derivative laws do not imply it, and there is no joint regularity law. This is already stated in the kernel docstring and handled by `Sanity.op_divergence_form`. No regression theorem was added; a non-jointly-differentiable counterexample was judged not worth its cost.
- **D-1 (documentation).** The `Kernel/Equilibrium` docstring says `Vec3` imposes "no norm convention", whereas `Fin 3 → ℝ` carries Mathlib's sup norm (as `Kernel/Vacuum` states). The kernel uses no norm, so this has no logical effect.
- **F-4 (validated, no defect).** The Bosch–Hale table matches the fit formula (§5): all 61 windows contain the minimum and maximum of the fit over 2001 samples per window, the outward margins are 0.989–0.990 and 1.010–1.011 relative, the peak is at 66.6 keV (so it is monotone on `[1, 60]`), and the windows are contiguous on `[1, 100]` keV (`boschHaleWindows_contiguous`). The keV, `E_α`, `E_fus` and `C_br` constants are correct (`keV_eq`, `neutron_energy`, `bremsCoeff_matches_NRL`).

## 3. Sanity coverage: missing checks and the ones added

Before the audit, the kernel laws lacked the following:
- counterexamples for `ForceBalance`, `StaticSlab`, `SteadySlab`, `TransportLaws`, `ClassicalRadialSolution`, `PhysicalPlasma` and `PowerBalance`;
- any sanity module for `SteadySlab` or `StaticSlab` beyond the theory-layer instances;
- risk-specific checks for orientation, conservation, endpoints, empty domain, totalization, zero duration, source domain and composition consistency.

All of these are now added (each defect has a regression theorem):

| File | Declarations |
| --- | --- |
| `Sanity/AuditEquilibrium.lean` | `forceBalance_rejects_perp`, `pinch_force_inward`, `forceBalance_rejects_reversed`, `forceBalance_of_cross` (E-1), `forceBalance_smul_field`, `forceBalance_smul_current`, `slab_total_pressure_deriv`, `slab_rejects_compressive`, `shearField`, `shearCurrent`, `shearPressure`, `slab_negative_pressure` (S-1) |
| `Sanity/AuditThermalSlab.lean` | `steadySlab_unloaded`, `steadySlab_rejects_isothermal`, `steadySlab_energy_balance`, `steadySlab_cold_face_ge`, `steadySlab_zero_thickness` (T-1), `steadySlab_zero_thickness_exists` |
| `Sanity/AuditVacuum.lean` | `fderiv_idField`, `fieldDiv_id`, `fieldCurl_id`, `id_not_vacuum`, `fieldDiv_rotationField`, `vacuumField_empty` (V-1), `rotationField_vacuum_empty`, `absField`, `absField_not_differentiableAt`, `absField_fieldDiv_zero`, `absField_fieldCurl_zero`, `absField_not_vacuum`, `divOp_smul`, `curlOp_smul`, `VacuumField.const_smul` |
| `Sanity/AuditTransport.lean` | `mislabelledCoefficients`, `mislabelled_not_transportLaws`, `sourceCoefficients`, `constField_rejects_source`, `cosMode_rejects_edge`, `slopeField`, `slopeField_rejects_axis`, `fakeField`, `hasDerivWithinAt_Icc_self`, `fakeField_zero_duration` (R-1), `fakeField_not_solution`, `posDomainCoefficients` (+ `TransportLaws` instance), `solution_outside_Tdom` (R-2), `noDiffusionCoefficients` (+ instance), `frozenField`, `noDiffusion_frozen` (R-3) |
| `Sanity/AuditFusion.lean` | `keV_eq`, `neutron_energy`, `bremsCoeff_matches_NRL`, `Contiguous`, `boschHaleWindows_contiguous`, `Contiguous.cover`, `boschHaleWindows_head_lo`, `boschHaleWindows_getLast_hi`, `boschHaleWindows_cover`, `boschHaleWindows_svLo_pos`, `BoschHaleDT.pos_of_mem`, `not_physical_zero_density`, `powerBalance_rejects_zero_tau`, `inconsistentPlasma`, `inconsistentPlasma_physical` (F-1), `fuel_one_forces_Zeff_one`, `carbon_fuel_fraction_two`, `powerBalance_zero_density` (F-2), `powerBalance_zero_density_rising`, `lossPower_zero_tau` (F-3), `netHeating_zero_tau`, `bremsPower_of_nonpos`, `impurityFuelFraction_Z_one` |

All of these are in the namespace `PlasmaLean.Sanity.Audit`. Note that `Audit.BoschHaleDT.pos_of_mem` and `Audit.VacuumField.const_smul` live in that namespace, so dot notation on the kernel types does not reach them.

Still missing (not added): a non-jointly-differentiable `D` showing that I-1 is a real gap; linearity and time-translation checks for transport solutions; and a check that `m2Plasma` is carbon-consistent (downstream, not kernel).

## 4. Downstream claims needing re-audit

1. **F-1:** any claim built on a concrete `DTPlasma` must cite a composition-consistency theorem. `m1Plasma` and `stellarisPlasma` have one; `m2Plasma` (`Design/TransportBarrier`, and through it the barrier designs using `alphaRate`/`bremsRate`) does not (its values are the same carbon-consistent triple).
2. **E-1:** the 17 `ForceBalance` user files (`Design/{HelicalEquilibrium, HelicalReactorScale, LandremanEquilibrium, LandremanFamily2, LandremanFamily2MercierStable, Solovev, SolovevAlpha, SolovevBand, SolovevBandHighQ, SolovevBandIgnited, SolovevCoarea, SolovevFluxGeometry, SolovevOnePlasma, ValidatedSlabEquilibrium}`, `Theory/Equilibrium/{ScrewPinch, Slab}`, `Sanity/Equilibrium`): check that each advertised equilibrium pairs `ForceBalance` with a proved `g = ∇p` (and the Ampère current). I spot-checked Solov'ev, Landreman family 1 and helical; the others are not checked.
3. **R-1, R-2:** transport results using `ClassicalRadialSolution` (`Design/{HelicalTransportBarrier, QuasilinearBarrier, SolovevBand, SolovevBandHighQ, SolovevBandIgnited, SolovevCoarea, SolovevFluxGeometry, TransportBarrier}`, `Theory/Transport/{BarrierCheck, Comparison}`): confirm they quantify over all `τ ≥ 0` or assume `τ > 0` (true for `solovev_one_plasma_actual` and `_coarea`), and that every use of `R` continuity along a solution has a domain hypothesis.
4. **V-1:** vacuum-field results (`Design/{RationalStellarator, RationalStellaratorCoilsTransfer, PolygonCoilConfined, PolygonCoilCubicConfined, VacuumPairVolumeError}`, `Theory/Fields/{Subharmonic, CurvatureObstruction}`): check that the region is nonempty, or that the conclusions are pointwise in `Ω`.
5. **S-1, T-1:** `Design/ValidatedSlabEquilibrium` (it imposes `p > 0`) and `Design/SlabExample` (it uses `h > 0`); no action expected.
6. **F-2, F-3:** `Design/BurnWindowScaling` (standalone `lossPower`/`netHeating` with scaling-law `τ_E`); `Theory/Transport/ConfinementScaling.LossScaling.loss_eq` (no `PhysicalPlasma`; an identity).

Until F-1 is resolved, a claim that relies on a `PhysicalPlasma` instance without a consistency theorem should not be advertised as physically admissible.

## 5. Commands run

All commands ran on the laptop at commit `cda8bd0`, with free memory at 65–68 % (`memory_pressure`) throughout.

- Read: `.claude/skills/plasmalean-audit-domain/SKILL.md`, `.claude/skills/plasmalean-lean-proofs/SKILL.md`, `notes/formalization/00-model-contracts.md`, `notes/implementation-plan.md` (Research graph, RG.1–RG.5), all six kernel modules, `Sanity/{Equilibrium, Transport, Vacuum, Fusion}.lean` and parts of the theory and design users.
- Users: `rg -lw <name> PlasmaLean -g '*.lean'` for every kernel declaration.
- Policy grep: `rg -n "decide|sorry|admit|axiom |native" PlasmaLean/Kernel PlasmaLean/Sanity`. The kernel is clean. The only hits are the 4 plain `decide` in `Sanity/Transport` (R-4) and the Boolean `decide (v ≤ w)` inside the computable checker `nonDecrB` (`Sanity/BoschHaleFineInstance`, a function body, not a proof).
- Bosch–Hale validation: `python3 -I /tmp/kaudit/bh.py PlasmaLean/Kernel/Fusion.lean`. This uses the D-T fit of Bosch–Hale 1992 (Table VII: `B_G = 34.3827`, `m_rc² = 1124656`, `C1…C7`) with 50-digit `decimal` and 2001 samples per window. Result: 61 windows, 0 bad, peak at 66.6 keV.
- Lean checks, one file at a time: `lake env lean PlasmaLean/Sanity/Audit<X>.lean`.
- Builds, one module at a time: `lake build PlasmaLean.Sanity.AuditEquilibrium`, `…AuditThermalSlab`, `…AuditVacuum`, `…AuditTransport`, `…AuditFusion`. All succeeded with zero warnings (after replacing flexible `simp … at` calls flagged by `linter.flexible`).
- Axioms: `lake env lean /tmp/kaudit/ax.lean` (`#print axioms` for all 59 new theorems and named instances). All 59 depend on `[propext, Classical.choice, Quot.sound]` only.
- Not run: full `lake build`, `scripts/check_axioms.lean`, `scripts/audit_kernel_fact.py` (outside lane E's scope and budget; the new modules are not yet imported by `PlasmaLean.lean`).
