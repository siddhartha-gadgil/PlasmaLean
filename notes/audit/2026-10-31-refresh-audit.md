# Strict audit refresh, 31 October 2026

Skill: `plasmalean-audit-domain`, proof policy `plasmalean-lean-proofs`.

| Item | Value |
| --- | --- |
| Previous audited commit | `cda8bd0` (records `2026-10-30-{kernel,repository,model,docs}-audit.md`) |
| Audited commit | `921a8c3` (HEAD, 31 October 2026), working tree clean apart from the new sanity file below |
| Toolchain | Lean `v4.34.1`, Mathlib `v4.34.1` (`lean-toolchain`, `lakefile.toml`) |
| Scope | everything changed in `PlasmaLean/` and `scripts/check_axioms*.lean` since `cda8bd0` (62 commits, 58 files, +12,164 / −632 lines); new top-level claims first; the README, slideshow, plan and theory-note claims that cite them |
| Kernel | only `Kernel/Fusion.lean` (F-1 fix) and `Kernel/README.md` changed. Confirmed with `git diff --stat cda8bd0..HEAD -- PlasmaLean/Kernel` |

## Commands run

All Lean processes ran one at a time (checked first with `pgrep -x lake` and `pgrep -x lean`).

- `git log --oneline cda8bd0..HEAD` and `git diff --stat cda8bd0..HEAD -- PlasmaLean scripts/check_axioms*.lean`.
- `lake build --no-build PlasmaLean`: all 3,854 targets up to date.
- `lake env lean scripts/check_axioms.lean`: passed. "Axiom audit passed for 48258 PlasmaLean declarations"; every `#print axioms` line is a subset of `[propext, Classical.choice, Quot.sound]`. 56.7 s, 4.39 GB peak RSS.
- `lake env lean PlasmaLean/Sanity/AuditRefreshContract.lean`: no errors, no warnings. Peak below 1.6 GB.
- `lake build PlasmaLean.Sanity.AuditRefreshContract`, then `#print axioms` on its two main theorems: standard axioms only.
- Scans of the diff for `sorry`, `admit`, `axiom`, `native_decide`, any `decide` variant, `maxHeartbeats 0`, `unsafe`, `implemented_by` and `extern`. Results:
  - No new `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or `maxHeartbeats 0`.
  - No `decide` tactic in new code.
  - `Sanity/AuditModelTransport.lean:110–112` uses `decide` only as the Bool coercion inside the computable checker `fineChain`, closed by `bool_cert`. This is acceptable.
  - `decide +kernel` lines in `LandremanFamily2Cert1–7` went from 143 to 0. In `LandremanFamily2MercierStable` they went from 3 to 1, and the remaining one is docstring text.
- `scripts/check_axioms_heavy.lean` was not run (on-demand modules are unchanged by this diff).

Two read-only sub-audits (orbit existence, relative entropy and TorusHodge; weak QS, Grad, the family-2 certificate refactor and axiom coverage) reported findings. I spot-checked their key claims against the source: `family1_not_weakQS` hypotheses, `alpha_orbit_exists_explicit` horizon, and the stale `lorentz_apriori_of_contDiff`.

## Findings

| ID | Severity | Location | Summary |
| --- | --- | --- | --- |
| AR-H1 | **high** | `Theory/Contract/StellaratorContract.lean:508–531` (`SurfaceData.Spans`, `CurrentFreeTransform`) | The C1 current clause has no content: a degenerate spanning section gives zero current for every field |
| AR-M1 | medium | `StellaratorContract.lean:531` (`iota_ge`) | C1 fixes the handedness, `ι ≥ ι_min > 0`, so left-handed fields such as Dommaschk runs with `ι ≈ −0.22` fail C1 while their mirror images pass |
| AR-M2 | medium | `Theory/Kinetic/Omnigeneity.lean:144–149`; README:19–21; plan contract table | `OmnigenousOn` is exact return of the guiding-centre orbit (all orders), which is stronger than standard omnigeneity, so QI fields are not "special cases" of the exact clause |
| AR-M3 | medium | `Design/NearAxisQAOmnigeneity.lean:42, 65, 73` | No `TrappedBounce` is constructed for `exactQA` or `reactorQA`, so these instances are not shown to be non-vacuous |
| AR-M4 | medium | `Design/RationalStellaratorQAObstruction.lean:69–82`; `notes/theory/dommaschk-qa.md:30–32` | The QA obstruction prose overclaims ("impossible", "needs a non-planar axis") |
| AR-M5 | medium | plan l.203, 233, 1247; slideshow l.565, 1129, 1495, 1507; `notes/formalization/04-particles-and-transport.md:104` | The near-axis existence horizon is stated as "≈ 1.5 μs near the axis". It is `r₀/285000`, at most 1.49 μs, and it tends to 0 at the axis |
| AR-M6 | medium | `NearAxisQAExistenceFull.lean:45–48`; plan l.203, 233; slideshow l.1495, 1507; 04-particles l.31, 106 | `Dpsi_gt_psiStart` and `band_empty_Tav` are called "proved obstructions". They are limits of the band method |
| AR-M7 | medium | README:51, 108; plan:75; slideshow:25, 1535 | "Not weakly quasisymmetric" is stated without its hypotheses (axis ⊆ T, ∇ψ = 0 on the axis) |
| AR-M8 | medium | README:107; `docs/index.html` (~936); `docs/progress.html:22` | The Grad-counterexample headline omits that all field lines are closed (ι ≡ 2) and omits the formulation used |
| AR-L1 | low | README:49–50, 62–63; plan:55–58, 74–77; slideshow:26, 80, 1541, 1635 | Stale text: C1/C2 are described as "not in Lean", though they now are. Slide 1635 promises "ε_eff in Lean" and "a generic 3-D field is not omnigenous" |
| AR-L2 | low | `Theory/Fields/CylAlgebra.lean:429–483` | `_root_.PlasmaLean.Vacuum.VacuumField.{differentiableAt, zero, add, smul, sum}` are declared in the kernel namespace outside `Kernel/` |
| AR-L3 | low | `Design/DommaschkQA3.lean`, `DommaschkQA3Data.lean` | Non-triviality of the candidate is not checked in Lean. The match with `basis.py` is checked only in Python |
| AR-L4 | low | `StellaratorContract.lean:263–279` | It is not proved that ι is independent of the parametrization or of the reference circle. A fixed reference circle excludes strongly shaped tori |
| AR-L5 | low | `StellaratorContract.lean:65–86, 617–620` | C1 (Cartesian `B`) and C2 (`BoozerField`) concern different objects, so there is no common witness |
| AR-L6 | low | plan l.1257 | "exact QS iff zero, `qsDefect_eq_zero_iff`" overclaims |
| AR-L7 | low | several docstrings | Stale names and wording (list below) |
| AR-L8 | low | `notes/audit/2026-10-30-model-audit.md:95, 106`; plan N-8 row (l.185) | The resolution status of MA-M1/MA-M2 is not recorded there |
| AR-L9 | low | `docs/plasma-models-and-equilibrium.html:93`; slideshow l.1547 | "Toroidal domain" (Grad) and "torus Hodge identity" wording |

No critical findings. Kernel: the F-1 fix is verified correct (below). No new kernel finding.

### AR-H1 (high): the C1 current clause has no content

`SurfaceData.Spans` (l.510) constrains only the outer edge `k = k₀` (the poloidal loop) and the inner edge `k = 0` (a point) of the section `X`. Nothing requires:
- the seams `χ = −π` and `χ = π` to agree;
- `X` to be `C¹` or an immersed disc;
- `B` to be regular on the section.

So `netToroidalCurrent` through a section that satisfies `Spans` is not the Ampère circulation `μ₀⁻¹ ∮ B · dl`. The normative specification (`00-model-contracts.md`, C1 table: "Equivalently, by Stokes, μ₀ I_tor = ∮ B·dl") is therefore not implemented. Because the section is part of the existentially chosen `S`, the clause is vacuous.

Compiled regression: `PlasmaLean/Sanity/AuditRefreshContract.lean` (new, not imported by `PlasmaLean.lean`).
- `pinchSection R z φ₀ k₀` is `X(k, χ) = loop(−π + (χ + π)k/k₀)`.
- `pinch_spans`: it satisfies `Spans`.
- `netToroidalCurrent_pinch`: the flux of **every** field through it is 0, because `∂_k X ∥ ∂_χ X`.
- `currentFreeTransform_of_tori`: every field with a nonempty family of invariant tori (`IotaOnTorus`, differentiable poloidal loops) with `ι ≥ ι_min > 0` satisfies `CurrentFreeTransform μ₀ B S 0 ι_min`, whatever plasma current it carries.
- `rotation_pinch_current_zero`: a concrete instance with the uniform-current field `B = e_z × x`.

Affected claims:
- The positive vacuum witnesses are **not** affected: `rationalStellarator_currentFreeTransform`, `candidate_currentFree` and `currentFreeTransform_of_vacuum` are true because the field is a vacuum field.
- The tokamak exclusion is not affected, since it uses the ι clause.
- The *negative* claims are affected:
  - `LandremanNetCurrent.lean:146` ("family 2 is never a current-free (C1) candidate");
  - slideshow l.56 ("Landreman family 2 … fails C1");
  - `00-model-contracts.md` ("family 2 fails C1 for every I_max < I_tor(k₀)").
  
  The Lean theorems `family2_not_currentFreeTransform(_zero)` are correct as stated: they assume `s.X = coordMap λ`. But they do not show that family 2 fails C1, because another section of the same loop gives `I = 0`.

Recommended fix (coordinator):
1. Define the net current intrinsically, as the circulation `μ₀⁻¹ ∮ B · dl` around the poloidal loop `χ ↦ cylPoint (R χ φ₀) φ₀ (z χ φ₀)` (needs only continuity of `B` and a `C¹` loop). Keep `netToroidalCurrent` as the section flux, with a Stokes theorem for regular sections (seams matched, `X` and `B` `C¹`).
2. Alternatively, strengthen `Spans` with seam matching, `ContDiffOn ℝ 1 X` on a neighbourhood of the section and `ContDiffOn ℝ 1 B` there. Even then, without a Stokes theorem a non-differentiable `X` gives junk `fderiv = 0`, so the regularity must be explicit.
3. Until then, restate the family-2 result as "positive net current through the family-2 coordinate section" and remove "fails C1".
4. Then move `currentFreeTransform_of_tori` to a negative fixture: after the fix it should become false for a current-carrying field.

### AR-M1 (medium): handedness of ι in C1

`IotaOnTorus` fixes the orientation. `PoloidalAngle.wind_θ` makes `Θ` increase with `θ`, counter-clockwise in the `(R, z)` half-plane, and `φ` is the geometric toroidal angle. So `ι` is a signed, intrinsic quantity, and `iota_ge : ι_min ≤ s.iota` with `ι_min > 0` admits only one handedness.

`notes/theory/dommaschk-qa.md:125` uses `|ι|` ("the sign depends on orientation"). Line 238 reports a Dommaschk run whose ι locks at −2/9. Such a candidate would fail C1 as defined, while its mirror image passes.

Fix: use `ι_min ≤ |s.iota|`, or state the handedness in C1 and add a mirror lemma (`B ↦ σ_* B` flips the sign of ι). Note also that `twistOn_qa_of_iota_ge` (C2 bridge) assumes `ι ≥ ι_min`. Add the `ι ≤ −ι_min` version, which is immediate because `TwistOn` uses `|f(x) − f(y)|`.

### AR-M2 (medium): exact `OmnigenousOn` is stronger than omnigeneity

`OmnigenousOn F c` requires `ψ(τ) = ψ(0)` exactly, for every exact guiding-centre orbit, every species, every μ and every energy. Standard omnigeneity (Hall–McNamara; Cary–Shasharina) is the vanishing of the *leading-order* bounce-averaged radial drift.
- Quasisymmetric fields satisfy the exact version (`omnigenousOn_of_exactQS`, via the conserved helical momentum).
- Generic omnigenous non-QS fields, in particular quasi-isodynamic ones, satisfy it only to leading order in ρ*. They can satisfy at most `ApproxOmnigenousOn` with `κ > 0`.

The contract text (plan C2 row, README:21 "Quasisymmetric and quasi-isodynamic fields are special cases") is right about *omnigeneity*, but the Lean clause `OmnigeneityContract F c 0` is "exact guiding-centre omnigeneity". Fix the prose:
- Omnigeneity.lean module doc and the `OmnigenousOn` docstring: "exact (all-order) return of the guiding-centre flux label per bounce; QS fields satisfy it; QI fields are expected to satisfy only the approximate form".
- StellaratorContract l.73–75 (`κ_max = 0` is exact omnigeneity): add the same qualifier.

### AR-M3 (medium): exactQA / reactorQA instances not shown non-vacuous

`TrappedBounce` is used only in `Omnigeneity.lean` (the `driftMirror` fixture) and `NearAxisQAOmnigeneity.lean`. No trapped bounce of `exactQA` or `reactorQA` is constructed, so `exactQA_omnigenousOn` and `reactorQA_approxOmnigenousOn` hold vacuously if no such bounce exists.
- The hypotheses of `reactorQA_alpha_bounce_drift` (a full bounce in `0 < ψ ≤ ψ_a` at energy E_α) are not shown satisfiable.
- The pieces exist: `exactQA_band`, `exactQA_turning_points` (supplied orbits) and `boozerGCOrbitOn_exists_of_region` (`BoozerGCForward`).
- The bound `4182 T m²/s`, against `ψ_a = 8.24 T m²`, allows crossing the plasma in about 2 ms. The docstring already says it is "not a transport estimate", and the prose should keep that.

Fix: construct one trapped bounce of `exactQA`: orbit existence on the band, then turning points, then `IsBounce`. Or add to the module doc and the N-29 note: "non-vacuity for these fields (existence of a trapped bounce) is not proved; the definitional non-vacuity is the `driftMirror` fixture".

### AR-M4 (medium): QA-obstruction prose

What Lean proves:
- `b1_not_quasiSymmetric` (general `N`, pure algebra on the modelled `b1`).
- `rationalStellarator_firstOrder_not_QS` and `_QA_defect` (the actual field, `N = 2` only). These concern the first-order coefficient of `‖B‖` on the linearized tori, in the straight-field-line angles of the linearized flow. The agreement with Boozer angles to `O(r²)` is informal (disclosed).

The docstring "Contract reading" (l.69–82) says:
- "a C2 certificate through the quasisymmetry bridge … is impossible for every member of this planar-axis family". Three problems:
  - the bridge (`approxOmnigenousOn_of_defect_le`) is stated for a `BoozerField`, and no Boozer model of the rational field exists in Lean;
  - the bridge gives a bound for every δ, so a large bound, not an impossible one;
  - only `N = 2` is tied to an actual field.
- "a C2 candidate needs a non-planar axis". This is not proved. The Garren–Boozer statement concerns QS, and omnigeneity (for example QI) is not addressed.

The skill's checklist says: "Treat the Garren–Boozer expansion as a source-specific compatibility result, not a universal impossibility theorem."

Suggested wording: "so the quasisymmetry route to C2 (Q-23) cannot give a small relative defect for this field: at first order the QA defect is the fraction √(ι₀/2) of the first-order variation. A QS-based C2 candidate therefore needs a different axis geometry (Garren–Boozer suggests a non-planar axis; not proved here)". Apply the same change to `notes/theory/dommaschk-qa.md:30–32`.

### AR-M5, AR-M6 (medium): near-axis orbit-existence prose (sub-audit, spot-checked)

AR-M5. `alpha_orbit_exists_explicit` (`NearAxisQAExistenceFull.lean:532–534`) has the hypothesis `T ≤ radius (57/10) ψ₀ / 285000`. The horizon is proportional to `r₀`. It is 1.49 μs only at `ψ₀ = psiStart` and tends to 0 at the axis, so slideshow l.1495 ("≈ 1.5 μs near the axis") has it backwards. Suggested wording: "for every birth 0 < ψ₀ ≤ psiStart, on the explicit horizon r₀/285000 s (r₀ = √(2ψ₀/B₀); 1.49 μs at ψ₀ = psiStart, shrinking to 0 at the axis)".

AR-M6. `Dpsi_gt_psiStart` and `band_empty_Tav` compare the certified constant `D(T)` with `psiStart` and `ψ_a`. They are limits of the band method. No Lean theorem shows that an orbit of the original class leaves the chart before 0.19 s. Suggested wording: "proved limits of the band method (…). Whether orbits of the original class leave the chart before 0.19 s is not proved; coordinates through the axis are the proposed route." MA-M1 should read "partially resolved".

The band results also need passing pitch (`81/100 · 2E_α/m_α ≤ v∥²`), energy exactly E_α and μ ≥ 0. State these where "full horizon" is claimed (slideshow l.565, 1129).

### AR-M7, AR-M8 (medium): weak QS and Grad prose (sub-audit, spot-checked)

AR-M7. `family1_not_weakQS` and `family2_not_weakQS` (`LandremanNotQS.lean:85, 164`) assume `∀ ζ, axis ζ ∈ T` and `∇ψ = 0` on the axis. Suggested wording: "neither family is weakly quasisymmetric on any region containing its magnetic axis, for any potential ψ critical on the axis (e.g. a function of the flux label)".

AR-M8. `family1_grad_counterexample` is strong:
- `C^∞` `B`, `J = curl B/μ₀` and `p` on an open `𝒰 ⊂ ℝ³`;
- kernel `ForceBalance` with `g = gradient p`;
- level sets that are tori;
- non-constant `p`;
- no Killing field of ℝ³ is a symmetry.

But family 1 has ι ≡ 2 (all field lines closed, `fieldLine_closed`; non-generic, disclosed at `LandremanGradCounterexample.lean:61`). Suggested README wording: "family 1 satisfies in Lean the hypotheses of a Grad counterexample in the formulation of Cardona et al. (Conj. 2.5): smooth MHS, toroidal level sets, non-constant pressure, no continuous Euclidean symmetry. All its field lines are closed (ι ≡ 2), so it is non-generic." The solid-torus topology of `Ω_δ` is not proved (AR-L9).

### Low findings, detail

- **AR-L1** (stale or underclaiming prose; replace with the current Lean status):
  - README:49–50 ("omnigeneity, bounce-averaged drifts and ε_eff are specified but not defined in Lean"). Correct: "omnigeneity and bounce-averaged drift are defined in the Boozer GC model (`OmnigenousOn`, `bounceAvgDrift`), and QS ⇒ omnigeneity is proved; ε_eff is not in Lean".
  - README:62–63 ("Lean definitions for C1 and C2" listed as next).
  - Plan l.55–58 ("not yet in Lean as contract predicates (Q-21)") and l.74–77 ("No bounce-averaged drift, omnigeneity or ε_eff is defined in Lean").
  - Slideshow l.26 ("specified but not in Lean") and l.80 ("not yet Lean definitions").
  - Slideshow l.1541 (the positivity corollary "not yet a named declaration"; it is `family2_net_current_pos`).
  - Slideshow l.1635 (a "next" item that lists "ε_eff in Lean" and "a generic 3-D field is not omnigenous" (only one fixture field, `driftMirror`, is proved non-omnigenous); mark the done parts done and drop "generic").
- **AR-L2**: move the `VacuumField` closure lemmas to `Kernel/Vacuum.lean` (a kernel change, user decision) or into a `Theory/Fields/VacuumClosure` namespace. Not a soundness issue.
- **AR-L3**:
  - `field_vacuum` holds for every coefficient vector, so the vacuum claim is robust. But nothing in Lean shows that `field candidate` differs from `∇φ` (a purely toroidal field fails C1).
  - Cheap check: at a point with `r₂ = 1` all `log r₂` monomials vanish, so `B_z` is an exact rational sum. Prove it nonzero.
  - Every field-line, ι and QA property of the candidate is untrusted numerics (disclosed).
- **AR-L4**: the uniqueness of ι is not proved. It follows from field-line uniqueness plus a π₁ argument in the twice-punctured plane. The fixed-circle convention excludes tori with large helical axis excursion (disclosed as "reference curves that are not fixed circles").
- **AR-L5**: the docstring "consistency check: an axisymmetric current-free field passes C2 and fails C1" combines a `BoozerField` statement with a Cartesian one. Add "in the respective models; no common witness yet".
- **AR-L6**: plan l.1257. Correct: "`qsDefect = 0` iff `ξ·∇|B| = 0` on T; exact weak QS iff `WeakQSDefect` with zero defects (`weakQS_iff_defect_zero`); `qsDefect` depends on the normalization of ξ".
- **AR-L7** (docstrings):
  - `Theory/Kinetic/LorentzExistence.lean:31` cites the non-existent `lorentz_apriori_of_contDiff`. The declaration is `lorentz_apriori_univ` (l.227, no C¹ needed).
  - `RelativeEntropyCoercive.lean:15–18` ("dH/dt = …" proved). What is proved is the integrated pointwise rate `∫ n(1 − T*/T)∂ₜT`.
  - `relEnt_exp_decay`(`_const_ref`) does not link the time family `S t` (same `T*`, `κ`; `Tt = ∂ₜT`). It is honest as conditional, but add the links.
  - `NearAxisQAExistence.lean:31–35` is superseded by `…Full`.
  - `TorusHodge.lean:447–449, 468–470` attaches physics labels (∫|B|²…) that no Lean `B` supports.
  - `LandremanFamily2MercierStable.lean:36` and `LandremanFamily2Quad.lean:1701` still mention `decide +kernel`.
- **AR-L8**: add the MA-M1/MA-M2 status lines to the model-audit record, and the off-axis scope to the N-8 row.
- **AR-L9**: Grad "toroidal domain" should read "open neighbourhood 𝒰 ⊂ ℝ³ of the compact plasma Ω_δ whose regular level sets are tori (solid-torus topology not proved)". The slide's "torus Hodge identity" should read "Hodge period inequality for a constant metric (energy ≥ |b − aτ|²/Im τ, equality iff constant)".

## Checked and OK

- **Kernel (F-1)**: `QuasineutralComposition` (fuel charge 1, finitely many species with `Z_i ≥ 1`, `c_i ≥ 0`, quasineutrality, `Z_eff`, ion ratio) is correct. `PhysicalPlasma` keeps `n, V, f_fuel > 0` and adds `composition`. The old fields become theorems (`Zeff_ge_one`, `fuel_le_ions`, `ions_le_one`, `fuel_le_one`, `Zeff_eq_one_of_fuel_one`). `quasineutralComposition_of_impurity` and `physicalPlasma_of_impurity` are correct (`1 ≤ Z_eff < Z`). The change strengthens the law. The users (`BurnWindow`, `BurnWindowStellarator`, `TransportBarrier`, `Sanity/Fusion`) now build their instances through `physicalPlasma_of_impurity` (carbon, `Z_eff = 1.7`). The regression `inconsistentPlasma_not_physical` is in `Sanity/AuditFusion`. No other kernel module changed.
- **C1 definitions apart from AR-H1/M1**:
  - `ampereCurrent` is the curl of the same field (actual `fderiv`).
  - `FieldTorus.flow` forces `B ≠ 0` on the torus (`φ̇ = 1`).
  - `PoloidalAngle` excludes θ-degenerate "tori" (a constant cross-section cannot carry a continuous angle winding once) and fixes the integer ambiguity of ι (`θ ↦ θ + nφ` breaks `wind_φ`).
  - `IotaOnTorus.tendsto` is correct.
  - The tokamak exclusion `iota_eq_zero_of_purelyToroidal` is correct and non-vacuous (`circTorus_iotaOnTorus`, ι = 0 attained).
  - Sanity triad present: zero field, vacuum, purely toroidal, `e_z × x`.
- **C1 witness**:
  - `ExactTorus.fieldTorus` and `poloidalAngle` use the KAM torus `torusA_exact`.
  - `fillSection` lies in `R > 0`.
  - `rationalStellarator_currentFreeTransform` holds as stated, with a one-surface family. The "not nested" caveat is disclosed.
- **C2 bridge**:
  - `IsBounce` (ρ changes sign; `IsBounce.unique`), `TrappedBounce`, `bounceAvgDrift` (= time average of ψ̇, `bounceAvgDrift_eq_avg_radialDrift`).
  - `psi_return_of_QS`: conservation of the helical momentum plus injectivity of `Nψ − Mψ_p`.
  - `psi_drift_le_of_defect` and the per-bounce and averaged corollaries.
  - The `driftMirror` counterexample has an explicit orbit, bounce and displacement `−2πk` (`dm_quantitative_check`: bound 8πk against actual 2πk, so the theorem is non-vacuous and linear in δ).
  - `omnigenousOn_of_axisymmetric_iota_zero` is honestly labelled vacuous.
  - Model laws are named in scope: supplied vacuum Boozer guiding-centre model, chart `ψ > 0`, `B` and `ι` independent inputs.
- **CylAlgebra**:
  - The formal derivatives are correct, including the `ℕ`-subtraction cases, where the coefficient is 0.
  - `hasFDerivAt_eval` proves that the formal partials are the actual Fréchet partials off the axis.
  - `nf` is sound (`eval_nf`, only the sound direction used).
  - `gradField_vacuum` is sound: open domain `r₂ > 0`, `C²` from `contDiffAt_eval`, divergence equal to the evaluated formal Laplacian, curl zero by Schwarz (`eval_d_comm`).
  - `eval` is total but only used on `r₂ ≠ 0`.
- **DommaschkQA3**:
  - `field_vacuum` holds for every `a : Fin 24 → ℚ` (`∇φ` plus finite sums of harmonic gradients).
  - `candidate_vacuum`, `candidate_netToroidalCurrent_eq_zero` and `candidate_currentFree` are stated over sections lying in `r₂ > 0` (the correct domain: the `∇φ` coil current sits on the z-axis).
  - `field_stellSym` is proved for all `a`.
  - The harmonicity leaves are `kernel_fact` (`Eq.refl`), as the policy allows.
  - The docstring correctly lists what is not proved (NFP-3 rotation symmetry, axis, ι, QA).
- **Family-2 net current**: `torCurrent_eq_netToroidalCurrent` (rfl), `curK_pos`, `curK_ge_curInf` and `family2_net_current_pos`/`_ge` are correct statements about the coordinate section (see AR-H1 for what they do not imply).
- **QA obstruction (Lean)**:
  - `b1_not_quasiSymmetric` is correct for every helicity `(M, K) ≠ (0, 0)`.
  - `rotatingEllipse_firstOrder_QA_defect` gives an exact sup-distance with attainment.
  - `firstOrderNormB_eq_b1` ties the actual field's derivative to `b1 2 ε`.
  - Sanity: `b1_zero_iota` (axisymmetric limit).
  - `nonQA_fraction_quarter` is a numeric instance.
- **Orbit existence**: `exists_global_of_apriori`, `lorentzOrbit_exists` (C¹ field on all of space; non-relativistic, E = 0), `solovev_orbit_exists`, `reactor_alpha_born_confined`, `reactor_alpha_confined_nonvacuous_35MeV` and `reactor_alpha_orbit_exists_label` construct solutions. The MA-M2 text matches. The Boozer forward bootstrap handles the `ψ ≤ 0` totalization correctly.
- **Relative entropy**: the identity, the two dissipation cases and the counterexample `old_identity_false` are correct. "Coercive" means an entropy–dissipation inequality with a Dirichlet match at one end. Decay is conditional (disclosed). The sanity fixture is non-degenerate.
- **TorusHodge**: the period inequality for a constant metric and the equality case are correct. It is not a Hodge decomposition (the notes say so).
- **Weak QS / Grad**: `WeakQS` follows CDG Def. 1 without boundary tangency (disclosed). `family1_grad_counterexample` excludes all continuous Euclidean isometries (the full Killing algebra `r × x + t`), on genuine ℝ³, with `g = gradient p`.
- **Family-2 certificate refactor**:
  - The 34 `cellN` statements are byte-identical, now spread over Cert1–7 and Cert2b/5b/6b.
  - `family2_mercier_stable(_derived)` are unchanged.
  - The rejected fixtures `cellCheck_rejects_axis` and `cellCheck_rejects_lam15` are unchanged (now in MercierStableA/B, re-exported).
- **Small diffs** (`BarrierCheck`, `Comparison`, `Sanity/Transport`: `nomatch` replacing `by decide`; `ScrewPinchModesHighM.stable_all_modes_equilibrium`, MA-L6; `ForceBalanceGradient`, E-1): no change of meaning.
- **Axiom coverage**: every new module is in the default build, imported directly or through `LandremanFamily2MercierStable`. The `run_cmd` loop of `check_axioms.lean` covers all of them. The new headline names also have explicit `#print axioms` lines.

## New sanity file

`PlasmaLean/Sanity/AuditRefreshContract.lean` (namespace `PlasmaLean.Sanity.AuditRefresh`) is the regression for AR-H1. It contains `loopPt`, `pinchArg`, `pinchSection`, `tripleFlux_smul_smul`, `netToroidalCurrent_pinch`, `pinch_spans`, `currentFreeTransform_of_tori` and `rotation_pinch_current_zero`. It compiles with zero warnings and uses standard axioms only. It is **not** imported by `PlasmaLean.lean`, so the coordinator should add it there. After AR-H1 is fixed, `currentFreeTransform_of_tori` should fail to typecheck, or be restated as a negative fixture.

## Downstream claims to re-audit after fixes

- After AR-H1: every C1 claim (`CurrentFreeTransform`, `family2_not_currentFreeTransform*`, slideshow C1 card, `00-model-contracts.md` Lean-status block, `LandremanNetCurrent` module doc).
- After AR-M1: the C1 status of the Dommaschk candidates (N-31), once ι is certified.
- After AR-M2/M3: the C2 status rows (plan RG.1 G-10, N-29, slideshow C2 card).

## Next theorem target

The smallest step that restores C1 content is `poloidalCirculation μ₀ B R z φ₀ := μ₀⁻¹ ∫_{-π}^{π} B(loop χ) · loop'(χ) dχ`, with:
- vacuum ⇒ 0 for loops that do not link the coil current. For the rational field this needs `B = ∇Φ` single-valued on a neighbourhood of the poloidal disc; `∇φ` itself is curl-free but its circulation is 0 only for loops not encircling the z-axis, which holds for poloidal loops;
- `e_y × x` through a circular poloidal loop gives `2πa²/μ₀ ≠ 0` (counterexample);
- Stokes agreement with `netToroidalCurrent` for `C¹` seam-matched sections.

## Resolution (31 October 2026)

- **AR-H1 resolved.** C1 uses the poloidal-loop circulation (`loopCurrent`), with a Stokes theorem
  for regular sections (`Theory/Contract/SectionStokes`); family 2 fails C1 again. Regressions are
  in `Sanity/AuditRefreshContract.lean`; `currentFreeTransform_of_tori` is removed.
- **AR-M1 resolved** in C1 (ι_min ≤ |ι|). The negative-ι version of the C2 twist lemma is still open.
- **AR-M2–M8, AR-L1, AR-L6, AR-L8, AR-L9: prose fixed** (commit fc82e6b).
- **AR-L2:** the `VacuumField` closure lemmas stay in `CylAlgebra` (theorems only; no kernel change).
- **AR-L7 and the Lean-side wording of AR-M2/M3/M4/M6: fixed** (31 October). This covers the
  docstrings of `LorentzExistence`, `RelativeEntropyCoercive`, `NearAxisQAExistence(Full)`,
  `TorusHodge`, `Omnigeneity`, `NearAxisQAOmnigeneity` and `RationalStellaratorQAObstruction`. The
  `decide +kernel` mentions in `LandremanFamily2MercierStable.lean:36`/`Quad.lean:1701` are left,
  because they are heavy certificate modules; batch them with their next rebuild.
- **Open:** AR-L3 (Dommaschk non-triviality fixture), AR-L4, AR-L5, and the AR-M3 Lean fixture (a
  trapped bounce for `exactQA`).

## Follow-up (31 October 2026): AR-L4 raised

The fixed reference circle of `PoloidalAngle` (AR-L4) is a blocker, not a disclosure: for the
Dommaschk target (non-planar axis wandering ≈ 0.11 × 0.13 in (R, z), nested region r_eff ≤ 0.053) at
most 73 of 256 cross-sections of torus A enclose any common fixed point (N-33 §2.2), so no surface
of that field can satisfy `IotaOnTorus`. Fix in progress: a continuous 2π-periodic reference curve.
The `DommaschkQA2R` docstring claim "C1 reduces to certified tori" holds only after this fix.

