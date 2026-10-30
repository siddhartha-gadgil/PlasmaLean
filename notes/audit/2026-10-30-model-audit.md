# Strict audit, part 3 (lane E): the model layer outside `Kernel/` (30 October 2026)

Audited commit `cda8bd0` (Lean v4.34.1, Mathlib v4.34.1). This audit addresses finding **H-1** of
`notes/audit/2026-10-30-repository-audit.md`: the alpha-confinement, Mercier, ballooning,
screw-pinch, near-QA and burn-window claims rest on model definitions in `Theory/` that the
kernel audit does not cover. No existing file was edited. New files:

- `PlasmaLean/Sanity/AuditModelGuidingCentre.lean` (Littlejohn, Newton–Lorentz, Boozer GC);
- `PlasmaLean/Sanity/AuditModelStability.lean` (Mercier, ballooning, Newcomb);
- `PlasmaLean/Sanity/AuditModelTransport.lean` (flux geometry, Bosch–Hale fine data,
  confinement scaling);
- this note.

**Checks run.** `lake build PlasmaLean.Sanity.AuditModelGuidingCentre`, `…AuditModelStability`,
`…AuditModelTransport`, one at a time, after checking that no other `lake build` was running
(free memory 65 %). All three built with **zero warnings**. An axiom walk over every constant owned by
the three modules (the `collectAxioms` loop of `scripts/check_axioms.lean`, run with
`lake env lean` on a scratch file outside the repository) passed for **110 declarations**, axioms used
`propext`, `Classical.choice`, `Quot.sound` only. No `sorry` and no `decide` tactic of any kind.
`decide (…)` occurs only as a Boolean value inside the checker `fineChain`, and `bool_cert` certifies it.
**Not run:** the full `lake build`, `scripts/check_axioms.lean` (the new modules are not imported by
`PlasmaLean.lean`, which this lane may not edit; add them to `PlasmaLean.lean` to bring them under
the default axiom check). An untrusted Python oracle (`/tmp/maudit`, outside the repository)
recomputed the Bosch–Hale fit and the IPB98/ISS04 laws (results in §2).

Scope traced from the claims table of the repository audit (§2 there): every model predicate or
structure that appears as a *hypothesis* or as the *conclusion predicate* of a headline theorem.

---

## 1. Inventory

S = supplied (enters as a hypothesis, typeclass or definition that is not derived from a more basic
law); P = proved instance or derived. Coverage counts the sanity triad
(degenerate / instance / counterexample) plus risk-specific (R) checks; "before" is the coverage
in the source modules at `cda8bd0`, "after" adds this audit.

| Definition (file) | Encodes | Source | S/P | Before | After |
| --- | --- | --- | --- | --- | --- |
| `Kinetic.GCLittlejohn.LittlejohnOrbit` (`Theory/Kinetic/GuidingCentreLittlejohn.lean:94`) | `B*_∥ Ẋ = v_∥B* + (μ/q) b×∇|B|`, `m B*_∥ v̇_∥ = −μ B*·∇|B|`, `B* = B + (m v_∥/q)∇×b`, static `B`, `E = 0`, SI; stated with `(B*_∥)⁻¹` | Littlejohn 1983; Cary–Brizard 2009 | S (orbits supplied; existence constructed in the GC headlines) | degenerate (`modField_zero`), instance (`uniform_orbit`), R: energy (`energy_const`) | + regression `littlejohn_zero_field_static`, counterexample `littlejohn_static_not_orbit`, R: charge conjugation `LittlejohnOrbit.charge_conj`, R: exact grad-B drift `gradB_drift_orbit` |
| `Kinetic.LorentzOrbit` (`Theory/Kinetic/FullOrbit.lean:43`) | `x' = v`, `m v' = q(E + v×B)` for all `t ∈ ℝ`, SI | Newton–Lorentz | S (orbit supplied) | instance `helix_orbit`, R: energy/speed conservation, Larmor radius | + degenerate `lorentz_free_particle`, R: orientation `cross_e1_e3`, counterexample `lorentz_straight_not_orbit` |
| `Kinetic.Boozer.BoozerGCOrbit`, `BoozerGCOrbitOn` (`Theory/Kinetic/BoozerGuidingCentre.lean:116,140`), `BoozerField` | Euler–Lagrange equations of `L = qψθ̇ + q(Gρ − ψ_p)φ̇ − q²ρ²B²/2m − μB`, vacuum Boozer (`I = 0`) | White–Boozer 1982; White ch. 3 | S (orbits supplied, no existence) | degenerate `constField`, instance `constField_orbit`, R: energy, helical momentum (Noether) | + characterization `BoozerGCOrbit.toroidal_rate`, R: units `constField_transit_rate`, regression `boozer_G_zero_static`, counterexample `boozer_static_not_orbit`, R: radial drift ∝ `∂_θB` `psi_const_of_Btheta_zero` |
| `Stability.MercierGeneral.mercierIndex`, `MercierStable`, `MercierSurfaceData` (`Theory/Stability/MercierGeneral.lean:93–97`) | `(2π)⁶D = [s_G 2π²ι' − ∫B·Ξ/|∇ψ|³]² + [s_ψ μ₀p'V'' − ∫|Ξ|²/|∇ψ|³]∫B²/|∇ψ|³`, stable iff `D > 0` | Landreman–Jorge 2020 eq. (3.1) | S (formula); data computed by callers | degenerate `mercierIndex_vacuum`, R: cylinder = Suydam (`mercierIndex_cylinder_eq_suydam`), counterexample `cylinder_mercier_neg_of_shearless` | + R: field reversal `mercierIndex_reverseField`, counterexample `mercier_hill_unstable`, regressions `mercier_negative_B2_stable`, `mercier_sG_zero` |
| `Stability.BallooningReduction.ballooningP/Q`, `LineData`, `LineData.Stable` (`Theory/Stability/BallooningReduction.lean:94–254`) | `δW = ∫(P X'² + Q X²)dt`, `P = |k|²/(ℓ|B|²)`, `Q = −2ℓ(B×k·μ₀∇p)(B×k·κ)/|B|⁴`; stability of a surface ⇔ `Stable` on every line and `θ_k` | Connor–Hastie–Taylor 1978; Dewar–Glasser 1983 | S (reduction) | degenerate `noPressure_energy_nonneg`, R: Clebsch form (`ballooningQ_clebsch`), cylinder = Suydam, fixtures | + R: bad-curvature sign (`ballooningQ_binormal`, `_neg_of_bad`, `_pos_of_good`), R: quadratic in `k` (`ballooningP_smul`, `ballooningQ_smul`), regressions `ballooningP_add_parallel`, `ballooningQ_add_parallel`, counterexample `badLine_not_stable` |
| `Stability.ScrewPinchModes.coefF/coefG`, `ModeStable` (`…/ScrewPinchModes.lean:84–100`) | Newcomb reduced energy `∫₀ᵃ(fξ'² + gξ²)`, `f = r³F²/μ²`, `g = 2k²r²μ₀p'/μ² + (μ²−1)rF²/μ² + 2k²r³(k²Bz² − m²b²)/μ⁴`, wall at `a` | Newcomb 1960; Glasser et al. 2020 eq. (2); Freidberg 2014 | S (extracted formula) | R: Freidberg form (`coefF/G_textbook`), Suydam limit, `(−m,−k)` symmetry, degenerate `uniform_vacuum_stable`, `zero_k_stable` | + R: field reversal `modeStable_reverseField`, regression `modeStable_nonequilibrium`, counterexample `modeStable_pressure_drive_fails` |
| `Stability.ScrewPinchModes.NewcombReduction` (`:318`) | full `W ≥ C·(reduced form)` on admissible displacements | Newcomb 1960 | S (interface) | instance `newcombReduction_self` | + regression `newcombReduction_empty` |
| `Transport.BoschHaleFine` (`Theory/Transport/BoschHaleFine.lean:164`) | 100 quarter-keV D-T reactivity enclosures on [5, 30] keV with ±1 % margin, plus `BoschHaleDT` | Bosch–Hale 1992 | S (data) | instance `Sanity.BoschHaleFineInstance`, R: refines coarse (`fine_refines_coarse`), fixtures | + R: gap-free increasing chain `fine_chain_check`, span `fine_span_check`, counterexample `zero_not_boschHaleFine`; oracle recomputation (§2) |
| `Fusion.ConfinementLaw`, `.Admissible`, `.tau`, `SteadyScaling`, `LossScaling` (`Theory/Transport/ConfinementScaling.lean:106–328`) | `τ_E = H C (P/1 MW)^(−α)`, `0 < α < 1`; IPB98(y,2), ISS04 coefficients; steady and loss-power conventions | ITER Physics Basis 1999 eq. (20); Yamada et al. 2005 | S (empirical fit) | R: power degradation, `H` monotonicity, power scaling, instances `ipb98/iss04_admissible`, `m1_scaling_satisfiable` | + regression `tau_zero_power`, R: units `tau_megawatt`; oracle check of the coefficients (§2) |
| `Transport.FluxGeometry.Laws` (`Theory/Transport/FluxGeometry.lean:148`) | `V' > 0`, derivatives, `g(0) = 0`, Gauss `(V'g)' = V'h` | divergence theorem + coarea (not proved in general) | S (class); proved for `solovevFluxGeometry` (+ coarea, `solovev_one_plasma_actual_coarea`) and `cylGeometry` | instance `modelGeometry`, enclosure theorems | + regressions `zeroGeom_laws`, `negGeom_laws`/`negGeom_g_neg`, counterexample `noGauss_not_laws`, R: `g_nonneg_of_h_nonneg` |
| `IsSolovevGeometry` (`Design/SolovevBand.lean:109`), `IsHelicalGeometry` (`Design/HelicalFluxGeometry.lean:237`) | `Laws` + enclosures of `⟨|∇s|²⟩`, `⟨Δs⟩` (Solov'ev); mean-value links (helical) | — | Solov'ev: P for `solovevFluxGeometry`; helical: S | instance `modelGeometry` | unchanged (inherits the `Laws` checks above) |
| `Fields.IsFieldLine` / `IsForwardFieldLine` | `γ' = B(γ)` on ℝ / `t ≥ 0` | — | definition | reverse, forward, constructed lines (`FieldLineExistence`) | unchanged (correct as stated) |

Derived helpers that appear inside proofs (`GuidingCentrePassing.rhoE`, `modFieldFn`, `GuidingCentre.*`)
are not hypotheses of any headline statement. The headline statements are in terms of `LittlejohnOrbit` and
`hamiltonian` only, so these helpers do not need a separate model audit.

## 2. Transcription checks against the sources

- **Littlejohn.** Re-derived from the phase-space Lagrangian (SI): `E* = −(μ/q)∇|B|`, so
  `E* × b = (μ/q) b × ∇|B|` and `m v̇_∥ = qE*·B*/B*_∥ = −μB*·∇|B|/B*_∥`. Both match the
  structure, and `ρ = m v_∥/q` has units T·m. Compiled evidence: `gradB_drift_orbit` reproduces the
  textbook grad-B drift `(μ/(qB)) b×∇B` with sign and magnitude exactly, and `LittlejohnOrbit.charge_conj`
  checks the relative signs of the three terms.
- **Boozer.** Re-derived the four Euler–Lagrange equations of the stated Lagrangian
  (`qψ̇ = −H_θ`, `qθ̇ − qιφ̇ = H_ψ`, `qGρ̇ − qιψ̇ = −H_φ`, `qGφ̇ = H_ρ`). All four match `BoozerGCOrbit`.
  `toroidal_rate`/`constField_transit_rate` give `φ̇ = v_∥B/G = v_∥/R₀` for `G = B₀R₀`, consistent with
  the Littlejohn model. `reactorQA.G = 58.1 T m ≈ B₀R₀` and `ψ_edge = B₀a²/2` are consistent.
- **Mercier.** Expanding `X²/(2π)⁶` gives `D_Shear = ι'²/(16π²)` and
  `D_Curr = −s_G ι'∫B·Ξ/|∇ψ|³/(2π)⁴`, the Landreman–Jorge decomposition. The well/geodesic terms are
  validated only through the proved cylinder reduction (`s_G = s_ψ = 1`). The new field-reversal
  invariance covers the sign conventions with `s_G, s_ψ = −1`. The source PDF was not re-read in this
  audit, so the well and geodesic terms in the non-cylindrical case rest on the transcription plus the
  cylinder check.
- **Ballooning.** From `B·∇(|k|²/B² B·∇X) + 2μ₀p'(B×κ·k)/B² X = 0` with `dl = ℓ|B|dt`:
  `P = |k|²/(ℓ|B|²)`, `Q = −2ℓμ₀p'(B×κ·k)/|B|²`. This matches `ballooningP` and `ballooningQ_clebsch`.
  `ballooningQ_neg_of_bad` confirms that bad curvature (`κ·∇p > 0` along the binormal) is destabilizing.
- **Newcomb.** `coefF/coefG` match Freidberg's `f = rF²/k₀²` and
  `g = 2k²μ₀p'/k₀² + ((k₀²r²−1)/(k₀²r²)) rF² + 2k²(k²Bz² − m²Bθ²/r²)/(r k₀⁴)` term by term (also proved,
  `coefF/G_textbook`).
- **Bosch–Hale (oracle, untrusted).** All 100 fine windows were recomputed from the published D-T
  parametrization (`BG = 34.3827`, `mrc² = 1124656`, `C1…C7`) with 50-digit `decimal` and 21 samples per
  window. Every window encloses the fit (minimum relative margin 1.0000 %). The fit is monotone on
  [1, 60] keV (step 0.01 keV). `BH(10) = 1.136e-22`, `BH(20) = 4.330e-22` m³/s.
- **Scaling laws (oracle).** The IPB98(y,2) and ISS04 exponents match the cited formulas. For ITER
  (15 MA, 5.3 T, 10.1·10¹⁹ m⁻³, M = 2.5, R = 6.2 m, ε = 0.323, κ_a = 1.7, 87 MW) IPB98 gives
  τ_E ≈ 3.6 s, the design value.

## 3. Findings by severity

**Critical:** none. **High:** none new (H-1 is discharged for the definitions in §1, apart from the
open items below).

**Medium**

- **MA-M1 Supplied Boozer orbits: no existence, and axis-crossing orbits are excluded by
  hypothesis.** Affected: `NearAxisQAAveraged.alpha_trapped_reactorQA_averaged` (and `_of_le`, `_011`),
  `NearAxisQA.alpha_trapped_reactorQA`, and `NearAxisQATrappedOscCover.reference_kick_osc` / `exactQA_kick_osc`
  (through `Setup.orbit`). `BoozerGCOrbitOn … T` includes `pos : ∀ t ∈ [0, T], 0 < ψ t`. Every passing alpha
  whose guiding centre reaches the magnetic axis within 0.19 s therefore falls outside the theorem. No witness
  shows that the hypothesis bundle (`E = E_α`, `v_∥² ≥ 0.81·2E/m`, `ψ(0) ≤ psiStart`, orbit on
  `[0, Tav]`) is satisfiable for `reactorQA`; the only Boozer instances are in `constField`. **Fix:** state
  the claims as "every supplied passing orbit that stays off the axis on [0, 0.19 s]". Add a
  Picard–Lindelöf existence theorem for the Boozer system on `{ψ ≥ ψ_min > 0}` (the coefficients are
  polynomial in `√ψ`, so locally Lipschitz there). With the proved upper bound, extend existence until the
  first axis approach, as `Theory/Fields/FieldLineExistence` does for field lines.
- **MA-M2 `reactor_alpha_confined` is non-vacuous only at zero energy.** `reactor_alpha_confined_nonvacuous`
  uses the alpha at rest on the axis (`axis_rest_orbit`, a zero-parameter witness). No 3.5 MeV
  all-time `LorentzOrbit` of `reactorField` is constructed. The claim "every 3.5 MeV alpha born in the
  core stays in" (slide 12) is therefore unwitnessed for the advertised energy. It is physically plausible,
  since the confinement bound gives `R² ≥ 50` and the field is smooth there. **Fix:** prove global existence
  from local Picard–Lindelöf plus the a-priori bound, or state the witness limitation next to the claim.
  The same applies to the `LorentzOrbit` conjunct of `solovev_one_plasma_*`.

**Low** (definition-level gaps; none affects a current headline statement, since every
downstream use supplies the missing condition; each has a compiled regression theorem)

- **MA-L2** `LittlejohnOrbit` uses the totalized `(B*_∥)⁻¹`. Where `B*_∥ = 0` (for example `B = 0`), every
  motionless state with any `v_∥` is an orbit (`littlejohn_zero_field_static`). Downstream:
  universal statements become only stronger, and the existence conjuncts construct orbits with
  `B*_∥ = |B| > 0` (`BstarPar_fieldSI`). **Fix:** add `BstarPar_ne : ∀ t, BstarPar … ≠ 0` to the structure.
- **MA-L3** `BoozerField` allows `G = 0`, which gives division by zero, and every constant state is then an
  orbit (`boozer_G_zero_static`). It also allows `B ≤ 0`. Downstream theorems assume `G ≠ 0` and
  `B ≥ B_min > 0`. **Fix:** add `G_ne : G ≠ 0` and positivity of `B` on the chart to `BoozerField`.
- **MA-L4** `MercierSurfaceData` does not constrain `sG, sψ ∈ {±1}`, `intB2 > 0` or `intXi2 ≥ 0`. A hill
  with `intB2 < 0` is "stable" (`mercier_negative_B2_stable`), and `sG = 0` deletes the shear term
  (`mercier_sG_zero`). Downstream: `family2_mercier_stable_derived` has `sG = ±1`, and
  `reactor_mercier_stable` proves `intB2_pos`. `family1_mercier_unstable` quantifies over all reals, which is
  stronger. **Fix:** an `Admissible` predicate on the data, required by `MercierStable` claims.
- **MA-L5** `LineData` does not require `k ⊥ B`. `P` uses the full `|k|²`, so a parallel component of `k`
  is spuriously stabilizing while `Q` is unchanged (`ballooningP_add_parallel`, `ballooningQ_add_parallel`).
  Downstream: both lines prove orthogonality (`family2Line_k_perp`, `lnB_inner_lnEik`). **Fix:** add
  `k_perp : ∀ t, ⟪k t, B t⟫ = 0` to `LineData`.
- **MA-L6** `ModeStable` and `coefG` take `p', Bz, b` independently and do not require radial force balance.
  The non-equilibrium profile `B = 0`, `μ₀p' = 1` is "stable" (`modeStable_nonequilibrium`). Downstream:
  the screw-pinch example proves `RadialBalance` separately (`ScrewPinchExample`), but `stable_all_modes`
  does not restate it. **Fix:** state the headline as `RadialBalance … ∧ ∀ m ≠ 0, ∀ n, ModeStable …`.
- **MA-L7** `NewcombReduction` holds vacuously for an empty admissible class, even with `W ≡ −1`
  (`newcombReduction_empty`). Downstream: `energy_nonneg_all_modes` is conditional on the reduction anyway.
  **Fix:** require that the admissible class contains every displacement of the mode with the wall
  condition, or a surjectivity field for `radial`.
- **MA-L8** `FluxGeometry.Laws` admits `g ≡ 0` (no transport, `zeroGeom_laws`) and `g < 0`
  (`negGeom_laws`). Downstream: `coeffs_transportLaws` assumes `g ≥ 0`, and `IsSolovevGeometry` has the
  lower enclosure. `g_nonneg_of_h_nonneg` shows that `h ≥ 0` would suffice. **Fix:** add `g_nonneg` to `Laws`
  (it follows from `h ≥ 0`).
- **MA-L9** `ConfinementLaw.tau` returns `0` at `P = 0` (`tau_zero_power`), the opposite of the physical
  limit, and `W/τ_E` would then vanish. Downstream: guarded by `SteadyScaling.P_pos`, and the loss-power form
  likewise. Recorded so that new users keep the guard.

## 4. Theorems added (all built, zero warnings; axioms `propext`, `Classical.choice`, `Quot.sound`)

`AuditModelGuidingCentre` (22 theorems, 1 definition): `littlejohn_zero_field_static`,
`littlejohn_static_not_orbit`, `bhat_neg`, `curlb_neg`, `gradAbsB_neg`, `Bstar_charge_conj`,
`BstarPar_charge_conj`, `cross_neg_left`, `LittlejohnOrbit.charge_conj`, `gradBField` (def),
`bhat_gradBField`, `curlb_gradBField`, `gradAbsB_gradBField`, `cross_e3_e1`, `gradB_drift_orbit`,
`lorentz_free_particle`, `cross_e1_e3`, `lorentz_straight_not_orbit`, `BoozerGCOrbit.toroidal_rate`,
`constField_transit_rate`, `boozer_G_zero_static`, `boozer_static_not_orbit`,
`BoozerGCOrbit.psi_const_of_Btheta_zero`.

`AuditModelStability` (22 theorems, 2 definitions): `reverseField` (def), `mercierIndex_reverseField`,
`mercier_hill_unstable`, `mercier_negative_B2_stable`, `mercier_sG_zero`, `cross_add_parallel`,
`cross_smul_right`, `ballooningP_add_parallel`, `ballooningQ_add_parallel`, `ballooningP_smul`,
`ballooningQ_smul`, `ballooningQ_binormal`, `ballooningQ_neg_of_bad`, `ballooningQ_pos_of_good`,
`badLine` (def), `badLine_P`, `badLine_Q`, `badLine_not_stable`, `coefF_reverseField`,
`coefG_reverseField`, `modeStable_reverseField`, `modeStable_nonequilibrium`,
`modeStable_pressure_drive_fails`, `newcombReduction_empty`.

`AuditModelTransport` (10 theorems, 4 definitions): `zeroGeom`, `negGeom`, `noGauss`, `fineChain` (defs),
`zeroGeom_laws`, `negGeom_laws`, `negGeom_g_neg`, `noGauss_not_laws`, `g_nonneg_of_h_nonneg`,
`fine_chain_check`, `fine_span_check`, `zero_not_boschHaleFine`, `tau_zero_power`, `tau_megawatt`.

All live in namespace `PlasmaLean.Sanity.AuditModel`. Every Low finding has a regression theorem
(MA-L2 … MA-L9). MA-M1 and MA-M2 are existence gaps with no compiled regression: a regression would
need the missing existence theorem.

## 5. Downstream claims needing re-audit

- **G-6 / near-QA** (`alpha_trapped_reactorQA_averaged*`, `alpha_trapped_reactorQA`, `reference_kick_osc`,
  `exactQA_kick_osc`; README near-QA bullet, slides 26–31): restate per MA-M1 and add a non-vacuity or
  existence result.
- **Slide 12 / N-8** (`SolovevAlpha.reactor_alpha_confined`) and the alpha conjunct of
  `solovev_one_plasma_actual`, `…_coarea`, `…_highQ_actual`, `…_ignited_actual`: per MA-M2.
- **G-1 screw pinch** (`stable_all_modes`, README l. 58): restate with `RadialBalance` (MA-L6) in addition
  to the repository audit's M-3.
- If the proposed fixes for MA-L2 … MA-L8 are adopted (new structure fields), re-check:
  `alpha_gc_confined_forever_robust`, `_pm`, `alpha_gc_passing_confined_forever*`,
  `_energy_window`, `_velocity_set` (Littlejohn); `boozerGC_trapped*` and all near-QA users (Boozer);
  `family1_mercier_unstable`, `family2_mercier_stable_derived`, `reactor_mercier_stable` (Mercier);
  `reactor_ballooning_all`, `family2_stable_of_cert`, `family2_stable_of_secular_cert` (ballooning);
  `stable_all_modes`, `energy_nonneg_all_modes` (Newcomb); `solovev_one_plasma_*` transport conjuncts
  (flux geometry).
- Add the three `Sanity/AuditModel*` modules to `PlasmaLean.lean` so that `scripts/check_axioms.lean` covers
  them, and record this audit in the strict-audit table of `notes/implementation-plan.md` (not done here,
  by lane restriction).
