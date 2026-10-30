# Strict audit, outward part: repository scans, headline claims, links, composition, certificates (30 October 2026)

Audited commit `cda8bd0` (Lean v4.34.1, Mathlib v4.34.1). Scope: everything outside
`PlasmaLean/Kernel/*` and its sanity coverage, which a separate kernel audit covers
(`notes/audit/2026-10-30-kernel-audit.md`). Read-only audit: no Lean file was changed.

**Checks run.** Source scans (comment-aware Python scanner over all 1,438 `.lean` files in
`PlasmaLean/` and `PlasmaLeanMeta/`); the default-build set was computed as the transitive import
closure of `PlasmaLean.lean` (674 modules plus the root; 764 modules are on-demand only). Every
headline declaration was located and its statement read in the source. **Not run:** `lake build`,
`scripts/check_axioms.lean`, `scripts/check_axioms_heavy.lean`, `scripts/audit_kernel_fact.py`
(the caller reports that the default build is current and that the 122-entry axiom check passed;
this audit did not repeat either). No `lake env lean` check was needed.

Untracked file seen but not audited: `PlasmaLean/Sanity/AuditEquilibrium.lean`, added by the kernel
audit. It is not imported by `PlasmaLean.lean` yet.

---

## 1. Scan results

Counts are lines of code with comments and docstrings stripped (raw `grep` counts in brackets).
"Default" means the module is imported, directly or indirectly, by `PlasmaLean.lean`.

| Pattern | Default | On-demand | Modules | Verdict |
| --- | --- | --- | --- | --- |
| `axiom` declarations | 0 | 0 | 0 | OK |
| `sorry` / `admit` | 0 / 0 | 0 / 0 | 0 | OK |
| `native_decide`, `ofReduceBool`, `trustCompiler` | 0 | 0 | 0 | OK |
| `implemented_by`, `@[extern]` | 0 | 0 | 0 | OK |
| `addDecl`, `addDeclWithoutChecking`, `setEnv`, `modifyEnv` in builders | 0 | 0 | 0 | OK: builders only assign goals, so every term goes through the kernel |
| `unsafe` | 8 | 0 | 4 | OK: all are `unsafe evalExpr` inside `meta` builders (`KronProof` ×6, `KronProof2D`, `SurfaceCover`, `SolovevBallooningDefs`); they compute values that only choose the shape of a certificate, which the kernel then checks |
| `partial def` | 31 | 0 | 14 | OK: all `meta partial def` (builders, parsers) |
| `set_option debug.*` / `skipKernelTC` | 0 | 0 | 0 | OK |
| `set_option maxHeartbeats 0` | 13 | 0 | 3 | Legacy, low (L-3): `KamTorusAWeightedCheck` (4), `RationalStellaratorCoilsGrad` (8), `CoilKamSeg` (1); affects elaboration resources, not soundness |
| other `set_option` | — | — | 920 | OK: `maxRecDepth` 10,297, `linter.style.longLine` 7,263, `exponentiation.threshold` 5,807, `linter.unusedSimpArgs` 677, `Elab.async` 666, `linter.unusedVariables` 416, `maxHeartbeats N` 42, `linter.flexible` 2. None disables a check |
| `decide +kernel` | 268 [297] | 1,797 [1,817] | 37 default / 45 on-demand | Legacy, medium (RG.4 #4, Q-12). The raw counts match the plan (297 / 2,114). Top default modules: `LandremanFamily2Cert1–7` (136), `KamTorusASurrogateCheck` 22, `KamTorusACheck` 14, `KamTorusAFrameCheck` 13, `NearAxisQAAveraged` 9. On-demand: Mu2–Mu5/Ew1–Ew4 `Rel*` and `CoilKamPts*` |
| `decide_cbv` | 0 | 93 | 3 | OK: permitted by policy (Mu3–Mu5 Adm) |
| plain `decide` (tactic) | 7 | 0 | 3 | Legacy, low (L-2): `absurd h (by decide)` on a disequality of a small geometry enumeration in `Theory/Transport/BarrierCheck.lean:109`, `Theory/Transport/Comparison.lean:1176,1244`, `Sanity/Transport.lean:179,229,268,294` |
| plain `decide` (Bool function in checkers) | 213 | 5 | 48 | OK: `decide (x ≤ y)` as a value inside Boolean checkers, certified by `bool_cert`/`eval_cert`; not a tactic |
| `instance` declarations | 47 | 0 | 21 | OK, see below |
| `open Classical` | 2 | 0 | 1 | OK (`Theory/KAM/StripAlgebra`, a definition by cases) |
| certificate tactics (uses) | `kernel_fact` 7,539, `bool_cert` 1,063, `kron_proof` 993, `fiv_cert` 518, `eval_cert` 132 | `kernel_fact` 13,660, `kron_proof` 3,264 | — | OK (kernel-checked proof terms). Opaque `kernel_fact` leaves were not re-measured (`audit_kernel_fact.py` not run; the plan's figure is 6,098 class-b leaves) |

**Instances.** None is universal or unconditional for a law typeclass. The law instances are for
concrete objects and carry proofs: `iterLaw.Admissible`, `stellarisLaw.Admissible`,
`PhysicalPlasma m1Plasma`, `PhysicalPlasma stellarisPlasma`, `IsSolovevGeometry modelGeometry`,
`solovevFluxGeometry.Laws`, `IsSolovevGeometry solovevFluxGeometry`,
`IsHelicalGeometry witnessGeometry`, `cylGeometry.Laws`, `TransportLaws relaxCoefficients`,
the `Sanity/Transport` instances, `BoschHaleDT bhSv`, `BoschHaleFine bhFineSv`. The one
parametric law instance, `TransportLaws.neg` (`Theory/Transport/Comparison.lean:940`), is
conditional on `[TransportLaws c]` and re-proves each field. The others are `Decidable` instances
on certificate predicates (`KronBall*`, `KronChebCompute`), algebra instances on the type synonym
`WEll1Z2 r`, `scoped` instances in `ConvAlgebra`, `DecidableEq FBall` and
`Fact ((0 : ℝ) ≤ 0)`. No `attribute [instance]` and no local instance tricks.

**Axiom scripts.** `scripts/check_axioms.lean` walks **every** constant owned by a `PlasmaLean*`
module imported by `PlasmaLean` and fails on anything other than `propext`, `Classical.choice` and
`Quot.sound`. Every default-build headline declaration is therefore covered, including those
without a `#print axioms` line (`solovev_one_plasma_highQ_actual`,
`family2_mercier_stable_derived`, `reference_kick_osc`, `exactQA_kick_osc`,
`rationalStellarator_confined`, the Stellaris obstructions, `VacuumField.*`, `boozerGC_trapped`).
`scripts/check_axioms_heavy.lean` only **prints** axioms; it does not fail. The on-demand top
modules are `RationalStellaratorGCEwFamily`, `…MuWide`, `…MuQuarter` (all imported by the heavy
script) and `Design/CoilKamCert` (not covered by any script; low, L-12).

---

## 2. Headline claims trace

Sources: README.md (Progress bullets), `progress/2026-10-26-progress-14.md`,
`progress/slideshow.json` (slide 0 and the result slides), and plan RG.1–RG.3. "D" means the
default build; "OD" means on-demand.

| Claim (text) | Declaration | Scope in Lean | Kernel laws used | Build | Verdict |
| --- | --- | --- | --- | --- | --- |
| One field with a pressure-budget band: force balance with p_eq + 40 kPa, core alphas confined forever, every band solution keeps T ≥ 10 keV and p ≤ p_eq + 40 kPa | `SolovevFluxGeometry.solovev_one_plasma_actual` | One μ₀ ∈ [1.2566, 1.2567]·10⁻⁶. (1) `ForceBalance` of `reactorField`, J = ∇×B/μ₀ (`Solovev.current`), ∇(p_eq + 40 kPa), on `label ≤ 1` (the R = 0 singular axis is excluded, since label = 4.36 there). (2) Every `LorentzOrbit` with E ≤ 3.5 MeV and label(x₀) ≤ 3/11 has label ∈ [0, 1] for all t ∈ ℝ. (3) ∀ `BoschHaleDT sv`, χ₀ ∈ [1.6, 1.65], ∀ u with `ClassicalRadialSolution` on every [0, τ] (**supplied**), band data at t = 0, T_edge ∈ [1, 1.5] keV: two-sided band, T ≥ 10 keV on s ≤ 0.3, and n(1 + 53/60)T·keV ≤ p_eq + 40 kPa, for all t ≥ 0 | `ForceBalance` (Equilibrium); `ClassicalRadialSolution`, `TransportLaws` (Transport); `BoschHaleDT` (Fusion) | D | Accurate. The same field, μ₀ and label are used in all three conjuncts (`label = psiT 10 / psiB`, matching L = 10 in `field (7/4) 10 50`) |
| … with the coarea step derived | `SolovevCoarea.solovev_one_plasma_actual_coarea` | The above plus the V′, V′g, V′h of `solovevFluxGeometry` equal to s-derivatives of Lebesgue integrals over `{label ≤ s}` | as above | D | Accurate |
| … at high Q | `SolovevBandHighQ.solovev_one_plasma_highQ_actual` | Same form, `BoschHaleFine`, χ₀ ∈ [0.78, 0.84], `highQ_aux`; Q itself is not in the statement (oracle only, disclosed on slide 15) | as above + `BoschHaleFine` (Theory) | D | Accurate; docstring stale (L-9) |
| … ignited, zero auxiliary heating, 90 kPa offset | `SolovevBandIgnited.solovev_one_plasma_ignited_actual` | `ignited_aux = []` (zero), offset 90,000 Pa, χ₀ ∈ [0.63, 0.64] | as above | D | Accurate; docstring stale (L-9) |
| First stellarator field: field lines near the axis confined for all time; field lines exist and are unique; vacuum model field | `RationalStellarator.rationalStellarator_confined_forever_exists` | ∃ ρ (`TorusProfile`, 0.077 ≤ ρ ≤ 0.19): ∃! field line of `field (1/4)` from every point of the region, and every `IsFieldLine` starting inside stays inside for all t ∈ ℝ. The vacuum property is a separate theorem (`field_vacuum`, kernel `VacuumField domain`) | `VacuumField` (Vacuum), via `field_vacuum` | D | Accurate |
| 95 transits (slide 16) | `RationalStellarator.Confined.rationalStellarator_confined` | Forward field line from `startTube`: in `tubeT` on s ∈ [0, 750] and ∫φ̇ ≥ 2π·95 | — | D | Accurate (superseded by the all-time result) |
| Passing alpha GCs, μ = 0, **either sign of v∥**, Littlejohn, **for every B₀R₀ ∈ [67.95, 69.99]** (README l. 38–40; slide 25 lead) | `alpha_gc_confined_forever_robust`; `RationalStellaratorGCNeg.alpha_gc_confined_forever_pm` | `robust`: B₀R₀ ∈ [67.95, 69.99], ∀ B₀R₀ ∃ P, **v∥(0) = +√(2K/m) only**. `pm`: both signs with separate tori ρp, ρn, uniform in (m, e) but **only at the design B₀R₀ = 256 m v/(2e)** | none in Kernel (`LittlejohnOrbit`, Theory) | D | **Overclaim (M-1)**: the v∥ < 0 case is not proved over the B₀R₀ range |
| μ > 0, λ ∈ [0, 1/16], one energy, one B₀R₀ | `alpha_gc_passing_confined_forever` | ∀ μ ∈ [0, K/(16B₀)] ∃ P; passing orbits with H = K stay inside and passing; existence from every interior point; B₀R₀ ∈ [68.9, 69] | Theory only | D | Accurate |
| λ ∈ [0, 1/4], one energy, one B₀R₀ | `alpha_gc_passing_confined_forever_quarter` | Same form with μ ∈ [0, K/(4B₀)] | Theory only | OD (heavy script) | Accurate; on-demand and spot-checked, stated as such |
| λ ∈ [0, 1/8] | `alpha_gc_passing_confined_forever_wide` | μ ∈ [0, K/(8B₀)] | Theory only | OD | Accurate |
| Energy window \|E − 3.5 MeV\| ≤ 0.4 eV × λ ∈ [0, 1/16] | `alpha_gc_confined_forever_energy_window` | ∀ E with \|E − K\| ≤ 0.4e, ∀ μ ∈ [0, E/(16B₀)] ∃ P; design B₀R₀ only | Theory only | OD | Accurate |
| Positive measure in 3-D velocity space | `alphaEwVel_volume_pos`, `alpha_gc_ew_confined_forever_velocity_set` | For x₀ with rt(x₀/R₀) < 0.03 only; velocity set: energies in [(1 − 2⁻²⁴)²K, (1 + 2⁻²⁴)²K] (≈ ±0.417 eV), ⟨w, b⟩ > 0, sin²χ ≤ \|B(x₀)\|/(16B₀); ∀ w ∃ P | Theory only | OD | Accurate; the texts omit "starting within 0.03 R₀ of the axis" (low, part of L-5) |
| Coils: closed polygonal coils, field lines confined for 52 transits | `PolygonCoil.coil_stellarator_confined_concrete_N` | γ is **assumed** to satisfy γ′ = `coilField polyCoilFieldC` on [0, 416]; `coilField = tfField + polyCoilFieldC`, where `tfField` is a closed rectangular filament with corners at (0, 0, ±10⁶) and (10⁶, 0, ±10⁶) (central post plus a return path at 10⁶ R₀) | `VacuumField` via the transfer chain | D | Accurate as a universal statement; README omits the field-line-existence assumption and the idealized TF return loop (L-5). The plan's G-5 entry states the assumption |
| Family 1 Mercier unstable | `LandremanMercier.family1_mercier_unstable` | Every surface of Ω_δ, every I′, sG, sψ, p′ and weight; ι′ = 0, V″ = 0 | `mercierIndex` (Theory; Landreman–Jorge, supplied) | D | Accurate |
| Family 2 Mercier-stable band, λ = 200, k ∈ [0.7, 0.9], labels derived | `family2_mercier_stable_derived` | ∀ μ₀ > 0, ∀ pa (an additive pressure constant, so negative pressures are included), sG = ±1: labels equal physical fluxes, volume and current; Jacobian and coarea; `MercierStable`; ι′ > 0, V″ > 0 | `mercierIndex` (supplied) | D | Accurate; README should say the Mercier formula is supplied (L-6) |
| Family 2 ballooning reduced to one certificate; no certificate found | `family2_stable_of_cert`, `family2_stable_of_secular_cert` | Conditional: from a C¹ Φ satisfying the pointwise inequality on the line × ℝ, `(family2Line …).Stable` for every c | `LineData.Stable` (Theory, supplied reduction) | D | Accurate; correctly stated as not certified |
| Solov'ev Mercier stable on every surface | `SolovevMercierCertified.reactor_mercier_stable` | ∀ μ₀ > 0, 0 < s ≤ 25 | `mercierIndex` (supplied) | D | Accurate |
| Solov'ev ideal ballooning on every surface | `SolovevBallooning.reactor_ballooning_all` | ∀ 0 < s ≤ 25, ∀ c: `(reactorLine …).Stable` (every compactly supported C¹ mode has nonnegative line energy) | `LineData.Stable` (supplied reduction) | D | Accurate, "reductions supplied" stated |
| Near-QA alphas held for 0.19 s (passing) | `NearAxisQAAveraged.alpha_trapped_reactorQA_averaged` | **Supplied** `BoozerGCOrbitOn` on [0, Tav], E = E_α, v∥² ≥ 0.81·2E/m (passing), ψ(0) ≤ psiStart ⇒ ψ(t) ≤ 8.2 on [0, Tav] | `BoozerGCOrbitOn` (Theory) | D | Accurate as text; the name says "trapped" for a passing result (L-4) |
| Every 3.5 MeV alpha born in the core stays in (slide 12) | `SolovevAlpha.reactor_alpha_confined` | Every `LorentzOrbit` with E ≤ 3.5 MeV and psiT(x₀) ≤ ψ_edge/4: psiT ≤ (11/12)ψ_edge and R² ≥ 50 for all t | `LorentzOrbit` (Theory) | D | Accurate (non-vacuity: `reactor_alpha_confined_nonvacuous`) |
| Screw pinch: **all-mode** Newcomb stability (README l. 58) | `ScrewPinchModesHighM.stable_all_modes` (plan RG.1 cites `stable_uniform`) | ∀ (m, n) ∈ ℤ², **m ≠ 0**: `ModeStable` (Newcomb's reduced energy, wall at a); the full energy only under a supplied `NewcombReduction` (`energy_nonneg_all_modes`). `stable_uniform` covers only the families \|m\| ≥ 2 with nm ≥ 0, or 9m² ≤ 5n² | `NewcombReduction` (Theory, supplied) | D | **Overclaim (M-3)**: m = 0 is excluded and the reduction is supplied; RG.1 cites the partial theorem |
| Burn windows from IPB98 and ISS04 | `BurnWindowScaling.m1_scaling_window_*`, `m1_scaling_satisfiable`, `Design/BurnWindowStellarator` | 0-D power balance, supplied `PowerBalance` and scaling-law classes | `PowerBalance`, `BoschHaleDT` (Fusion); `SteadyScaling`/`LossScaling` (Theory) | D | Accurate (0-D) |
| M1 burn window [10, 30] keV | `BurnWindow.m1_burn_window` | Supplied degradation τ_E ≤ 1.8 s for T ≥ 30 keV | `PowerBalance`, `BoschHaleDT` | D | Accurate (the degradation hypothesis is disclosed on slide 10) |
| Stellaris obstruction at measured f_ren | `stellaris_measured_fren_no_access_steady`/`_loss` | Flat 0-D model, f_ren ≤ 1.3, P_aux ≤ 70 MW ⇒ T ≤ 10 keV | as above | D | Accurate |
| Trapped kick amplitude ≤ 0.0816 T m² (Q-1) | `reference_kick_osc`, `exactQA_kick_osc` | For every orbit satisfying `Setup` (supplied exact-QA reference), bounce data and bounds | `BoozerGCOrbitOn` | D | Accurate |
| E1: QS is not a PDE symmetry; Lie bracket of gradients | `quasisymmetry_not_pde_symmetry`, `lieBracket_gradient_of_contDiffAt` | Explicit B, X, p | — | D | Accurate |
| Conditional Riccati | `riccati_le_initial`, `riccati_exp_decay` | The inequality is a hypothesis | — | D | Accurate ("conditional" stated) |
| N-1 min-B | `Vacuum.VacuumField.not_strict_local_max_normSq`, `exists_vacuum_strict_interior_min` | — | `VacuumField` | D | Exists; the note uses another name (L-7) |
| N-3 2-form | `magneticTwoForm_flux_surface` | — | — | D | Exists |
| N-4 Boozer GC | `boozerGC_trapped_until`, `boozerGC_trapped` | supplied Boozer GC model | — | D | Exists |
| Kernel-check memory "peak 4.3 GB, 6 GB target met" (README l. 62–63; slide 0 metric; slide 32 card) | — | RG.4 #1: 6.17 GB peak in `LandremanFamily2MercierStable` in the stage-9 rebuild | — | — | **Stale or contradictory (M-2)** |
| `decide +kernel` "≈ 2,500 lines, 690 default" (README l. 64–65; slide 32) and the slide title "No decide +kernel" | — | 2,114 raw lines (297 default) at `cda8bd0`; 2,065 (268) in code | — | — | Stale, and the title overclaims (L-1) |

**Kernel-law dependence.** Only the Solov'ev pressure-budget theorems, the 0-D burn windows and
the vacuum-field chain (`field_vacuum`, coil transfer) use `Kernel/*` laws (`ForceBalance`,
`ClassicalRadialSolution`/`TransportLaws`, `BoschHaleDT`/`PowerBalance`, `VacuumField`). All alpha,
Mercier, ballooning, screw-pinch and near-QA claims rest on model definitions in `Theory/`, which
the kernel audit does not cover (H-1).

---

## 3. Broken and stale links

All declaration names cited in RG.1–RG.3, README, progress report 14 and the slides exist (the
non-declaration tokens are tactics: `kernel_fact`, `eval_cert`, `fiv_cert`, `bool_cert`,
`kron_proof`, `kron_lt`, `kron2_proof`, `l1kron_cert`, `bl_cert`, `oned_cert`, `decide_cbv`,
`ballooning_cover`). Module paths cited in the registries exist. Problems:

| Where | Name | Problem |
| --- | --- | --- |
| plan RG.1 G-1 (line 33) | `stable_uniform` | Exists, but covers only part of the spectrum; the all-mode result is `ScrewPinchModesHighM.stable_all_modes` |
| plan RG.3 N-8 | `reactor_alpha_confined` | Ambiguous: `Design.SolovevAlpha.reactor_alpha_confined` and `Design.HelicalReactorScale.reactor_alpha_confined`; qualify it |
| `notes/theory/toroidal-min-b-obstruction.md:19` | `vacuum_normSq_no_strict_interior_max` ("Lean: …") | Does not exist; the compiled result is `Vacuum.VacuumField.not_strict_local_max_normSq`. The §2 target table (l. 127–135) still marks `vacuum_minB_counterexample`, `grad_normSq_half_eq_directional`, `closed_axis_not_minB` "ready now"/"in plan", although N-1 is verified (`exists_vacuum_strict_interior_min`, `Theory/Fields/CurvatureObstruction`) under other names |
| `notes/theory/flux-surface-holonomy.md:12`, `README.md:28` | `Challenge6_ConformalTorusModulus` | No such declaration in the repository |
| `notes/theory/README.md:26–44` ("recommended next Lean targets") | `vacuum_minB_counterexample`, `closed_axis_not_minB`, `ordered_pair_gain_bound`, `PolyBox3`, `Fields.fieldLine_confined_of_proportional_defect`, `trapped_of_invariant_frontier`, `Design/LandremanStretched` | None exist; most targets were completed under other names (Phases 4–10). The list is stale |
| `notes/theory/transport-mhd-coupling.md:4` | "Nothing here is a compiled Lean theorem" | N-6 is verified (`solovev_one_plasma_actual` …); the proposed names `SolovevBurn`, `burnCoeffs`, `solovevVp_bounds` were not used |
| `notes/theory/kam-route.md:349,372`, `first-stellarator-rung.md:336,356,390`, `near-axis-quasisymmetry.md:275,289`, `robust-alpha-confinement.md:300–319`, `coil-kam-status.md:145–147`, `after-kam.md:336–418`, `finite-beta-stellarator.md:156–168` | `InvariantTorusTrap.lean`, `RationalStellaratorTorus.lean`, `Certificates/WeightedEll1Z2.lean`, `RationalStellarator/AxisMonodromy.lean`, `ApproxFirstIntegral.lean`, `Certificates/PolyBox3`, `boozerGC_energy_conserved`, `ToroidalHarmonic.lean`, `GuidingCentreEnergy`, `Bd_evCheb`, `mul_interp`, `kamH_of_rho_near`, `coilTorus_exact`, `coilStellarator_confined_forever`, `rationalStellarator_stepped`, `weak_forceBalance` | Proposal sections with planned names. Acceptable as plans (the open targets are correctly open), but the completed ones should point to the actual names |
| `PlasmaLean/Certificates/EvalCert.lean:54` | module docstring | Still says the heavy leg checks are "left to `decide +kernel` for now" (RG.4 #5, unresolved) |
| `Design/SolovevBandHighQ.lean:21,902`, `Design/SolovevBandIgnited.lean:18,436` | docstrings | "Remaining unformalized link: the coarea formula", which has been proved (`SolovevCoarea.solovevFluxGeometry_coarea`) |

No registry entry claims a statement stronger than its declaration, apart from the G-1 citation
above. The quantitative descriptions in RG.1/RG.2 (52 transits with existence assumed, band
k ∈ [0.7, 0.9], ±0.4 eV × λ ≤ 1/16, 0.0816 T m², 0.19 s passing) match the statements.

---

## 4. Bridge/Contracts and composed theorems

`Bridge/Contracts.lean` (69 lines, default build) is a purely logical interface:
`DesignContracts`, `RobustDesign` (∀ θ ∈ U ∃ e, all four contracts), `compose_branch`,
`robust_mono`, `compose_of_unique` and the warning example `incompatible_witnesses`. It is sound,
and the quantifier order (existence inside the uncertainty quantifier) is right. **It is not
instantiated anywhere**, so G-8's evidence is an interface, not a result (the registry says
"`Bridge/Contracts` … only"; correct).

The composed theorems were checked for common witnesses:

- `solovev_one_plasma_*`: one μ₀; the same `reactorField = Solovev.field (7/4) 10 50`, Ampère
  current, and `offsetPressure μ₀ Δ = reactorPressure μ₀ + Δ` in the force balance and in the
  pressure budget; the same `label = psiT 10 / psiB` for the domain, the alpha conjunct and the
  transport geometry (`_coarea` ties `solovevFluxGeometry.Vp/g/h` to `label`). Compatible. The
  highQ and ignited variants use the same `solovevFluxGeometry` but do not restate the coarea
  conjunct (it applies, since the object is the same).
- GC theorems (`…_passing_confined_forever*`, `…_energy_window`, `…_robust`): the same
  `fieldSI B₀ R₀`, (m, e, μ, E) and torus `P` across the confinement and existence conjuncts.
  `P` depends on μ (or E, B₀R₀, w), as the texts say ("for every μ there is a torus").
- `alpha_gc_confined_forever_pm`: separate tori for the two signs (disclosed in the docstring and
  on slide 24); `∃ ρp ρn` comes before `∀ m e B₀ R₀`, so it is uniform in the constants.
- `rationalStellarator_confined_forever_exists`: the same ρ for existence/uniqueness and
  confinement.
- `family2_mercier_stable_derived`: the same λ = 200, ε = 1/4, S = 4 and k in all conjuncts.

No incompatible witnesses were found.

---

## 5. Certificates

| Predicate | Soundness theorem | Statement | Builder | Verdict |
| --- | --- | --- | --- | --- |
| `KronProof.SCert x s m` | `SCert.sound : SCert x s m → x = ⟨s, m⟩` | Syntactic evaluation of a sign–magnitude Kronecker image; the semantic link is `chebKV_le_of_cert` (`chebKV … ≤ Kb` from `SCert`, `gSel … = g`, `PCert`, `Nat.ble tot Kb = true`) plus the KronLowMem bridge lemmas | `mkSCert`/`evalSI` (`meta partial`, `unsafe evalExpr` for values); terms assigned to the goal | OK |
| `KronProof.PCert` | `PCert.sound : … → pdigL bw leaf d off c T = s` | Digit reading by halving; the `split` constructor matches `pdigL_succ` (proved by `rfl`) | `mkPCert` | OK |
| `BoolCert.BCert b v` | `BCert.sound : BCert b v → b = v` | One constructor per connective; `ite`/`dand`/`dor` steps use `of_decide_eq_true/false` correctly; leaves are kernel equalities | `bcertTerm`, which uses `Kernel.whnf` only to choose branches | OK. The semantic fact comes from each checker's own soundness theorem (`check = true → …`) |
| `EvalCert.ECert e v` | `ECert.sound : ECert e v → e = v` | `lit`, `leaf`, `op₁–op₃`, `arg`, `unfold` (needs a proof `e = e'`), `ite`/`dite` | `PlasmaLeanMeta.EvalCert` (native, precompiled); it produces terms only | OK; docstring stale (L-8) |
| `IccListCert` | `sum_Icc_eq_list`, `sum_range_eq_list`, `forall_Icc_of_all`, `forall_range_of_all`, `ite_mem_Icc` | Proved general lemmas; `icc_cert` = `simp only` with these lemmas, then `eval_cert` | macro | OK; accepted and rejected fixtures present |
| `FamPackCert.FPCert`, `RowsEq` | `famPack_eq_of_cert : FPCert … k l v → famPack … k l = v`; `RowsEq.sound` | Each `cons` carries `Nat.ble (2·Mj + 1) (2^dr) = true`, which `bsplit_eq_rowsVal` needs | `kList` builder | OK |
| `KernelFact` (`kernel_fact`) | no predicate; produces a term per goal shape (`And.intro`, `Nat.le_of_ble_eq_true`, `lt_of_ble_succ`, `Nat.ne_of_beq_eq_false`, `forall_*'` lemmas, `imp_of_*'`; ℚ `≤`/`<` as `Eq.refl false/true` against the definitional unfolding of `Rat` order; `=` as `Eq.refl`) | Each auxiliary lemma is proved; any wrong defeq is rejected by the kernel | `kernelFactTerm` with `mkExpectedTypeHint` | OK for soundness. `Eq.refl` leaves on whole checks are the known opaque-leaf issue (Q-12), a policy matter only |

No builder calls `addDecl` or changes the environment, and there is no `ofReduceBool` or
`native_decide`. So the only trusted components are Lean's kernel and the standard axioms. The
native-code builder (`precompileModules`) is untrusted and cannot affect soundness.

---

## 6. Findings by severity

**Critical:** none. No axiom, `sorry`, native trust or kernel bypass. No headline declaration is
missing, and no composed theorem mixes witnesses.

**High**

- **H-1 Model laws outside `Kernel/`, outside the strict audit.** Every alpha, Mercier, ballooning,
  screw-pinch and near-QA claim rests on supplied model definitions in `Theory/`:
  `Kinetic.GCLittlejohn.LittlejohnOrbit` (`Theory/Kinetic/GuidingCentreLittlejohn.lean:94`, with
  the `(B*_∥)⁻¹` totalization), `Kinetic.LorentzOrbit` (`Theory/Kinetic/FullOrbit.lean:43`),
  `Kinetic.Boozer.BoozerGCOrbitOn` (`Theory/Kinetic/BoozerGuidingCentre.lean:129`),
  `mercierIndex`/`MercierStable` (`Theory/Stability/MercierGeneral.lean:93–97`, the Landreman–Jorge
  formula as transcribed), `LineData.Stable` and the ballooning reduction
  (`Theory/Stability/BallooningReduction.lean:254`), `ModeStable`/`NewcombReduction`
  (`Theory/Stability/ScrewPinchModes.lean:84,318`), `BoschHaleFine`
  (`Theory/Transport/BoschHaleFine.lean:164`), `ConfinementLaw.Admissible`/`SteadyScaling`/
  `LossScaling` (`Theory/Transport/ConfinementScaling.lean:106,312,328`), `FluxGeometry.Laws`,
  `IsSolovevGeometry`, `IsHelicalGeometry`, and `IsFieldLine`/`IsForwardFieldLine`. The kernel
  audit covers none of these, so a clean kernel audit would not support G-1/G-4/G-6. **Fix:** add a
  "model-law layer" inventory to RG.4 and audit these definitions with the same red-team checklist
  (transcription against the source equations, totalized `⁻¹`, sign conventions, sanity triad),
  or move them into `Kernel/`. Until then, record the claims as resting on unaudited model laws.

**Medium**

- **M-1 Overclaim, sign of v∥ over the B₀R₀ range.** README.md:38–40 ("μ = 0, either sign of v∥ …
  for every B₀R₀ ∈ [67.95, 69.99]") and the slide 25 lead. `alpha_gc_confined_forever_robust` is
  for v∥ > 0 only; v∥ < 0 (`alpha_gc_confined_forever_pm`) is at the design B₀R₀ only. **Fix:**
  "μ = 0: v∥ > 0 for every B₀R₀ ∈ [67.95, 69.99]; both signs at the design B₀R₀".
- **M-2 Contradictory resource claim.** README.md:62–63, the slide 0 metric and the slide 32 card
  say the peak is 4.3 GB and the 6 GB target is met; RG.4 #1 records 6.17 GB
  (`LandremanFamily2MercierStable`) in the stage-9 rebuild. **Fix:** state the measured peak and
  the open split.
- **M-3 "All-mode" screw pinch.** README.md:58 says all-mode Newcomb stability; the theorem
  (`stable_all_modes`) excludes m = 0 and works in Newcomb's reduced energy (the full energy only
  under a supplied `NewcombReduction`). Plan line 33 (G-1) cites `stable_uniform` (partial).
  **Fix:** "every (m, n) with m ≠ 0, in Newcomb's reduced form" and cite `stable_all_modes`.
- **M-4 On-demand trust (carried, RG.4 #3).** `check_axioms_heavy.lean` only prints and does not
  fail; `Design/CoilKamCert` (an on-demand top) is in no axiom script; the on-demand families are
  stale after stages 8–9. **Fix:** make the heavy script assert (the same `run_cmd` loop) and add
  `CoilKamCert`.
- **M-5 Legacy `decide +kernel` (carried, RG.4 #4).** 268/1,797 code lines (297/2,114 raw).

**Low**

- **L-1** README.md:64–65 and slide 32 give ≈ 2,500/690 `decide +kernel` lines (actual 2,114/297),
  and the slide 32 title "No decide +kernel" overclaims.
- **L-2** Seven tactic `by decide` uses in the default build (§1). Replace them with
  `nofun`/`by simp` or `Geometry.noConfusion`.
- **L-3** `set_option maxHeartbeats 0` at 13 sites (§1). Use finite budgets.
- **L-4** `alpha_trapped_reactorQA_averaged` proves a *passing*-alpha bound (v∥² ≥ 0.81 v²).
  Add an alias such as `alpha_passing_reactorQA_averaged` and cite it in the claims.
- **L-5** The README coil bullet (l. 45–46) omits the field-line existence assumption and that the
  "closed polygonal" TF coil is a rectangle with a return leg at 10⁶ R₀ (not constructible). The
  positive-measure texts omit "from points within 0.03 R₀ of the axis".
- **L-6** The README family-2 bullet (l. 47–52) omits "Mercier formula supplied". The theorem holds
  for every additive pressure constant `pa`, including negative pressures (harmless, but say "for
  the physical pa").
- **L-7** Stale note names (§3): the toroidal-min-b note, `Challenge6_ConformalTorusModulus`, the
  theory README target list, and the transport-mhd-coupling status line.
- **L-8** The `EvalCert.lean:54` docstring is stale (RG.4 #5).
- **L-9** The highQ/ignited docstrings call the coarea link unformalized.
- **L-10** RG.3 N-8 cites the ambiguous `reactor_alpha_confined`.
- **L-11** README.md:18 (14 October paragraph) says no all-mode stability or alpha confinement is
  certified, which later bullets contradict. Mark it as historical, or drop it.
- **L-12** `Bridge/Contracts` is not instantiated. That is correct as recorded, but G-8 has no
  composed instance yet.

Downstream claims to re-audit after H-1: G-1, G-4, G-6 (and the corresponding README bullets and
slides 0, 12, 22–31).
