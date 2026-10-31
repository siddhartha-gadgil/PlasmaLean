# Dommaschk quasi-axisymmetric fit (Q-16, route ii)

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-31` |
| Title | Dommaschk quasi-axisymmetric fit: an explicit vacuum field with a non-planar axis, fitted for small QA defect relative to ι |
| Kind | computation / design (untrusted numerical search feeding a later certificate) |
| Addresses | `Q-16` (route ii, N-27 §4 and §6.2 item 2); contract clauses C1 and C2; `G-1`, `G-10` |
| Depends on | N-27 (`quasisymmetric-solution.md`, route (ii-EXP)); N-30 (`rational-field-c2.md`: exact vacuum Boozer angles, validated Nemov ε_eff code, planar-axis obstruction); N-29 (`omnigeneity-bridge.md`: QS defect ⇒ per-bounce drift). Lean: `Kernel` `VacuumField`; `RationalStellarator` (pattern); `Kinetic.Boozer.approxOmnigenousOn_of_defect_le`; the `KamTorusA*` / `KamFlow*` pipeline; `Theory/KAM/Cohomological.cohSol_estimate` |
| Dependency requirement | Harmonicity of the basis: exact symbolic identity (checked here in sympy; in Lean, a polynomial normal-form check). Boozer facts for B = ∇Φ: proved informally (N-30 §2). Everything optimised or measured here: **untrusted numerics** |
| Produces | Scripts `scripts/dommaschk_qa/`; the workstation task `dommaschk-qa`; a candidate format (exact rational coefficients plus an explicit potential); success tiers for the decided Q-16 criterion; a smoke-test candidate |
| Difficulty | moderate (numerics), hard (certification of the low-shear tori, barrier B2 of N-27) |
| Status | exploratory: pipeline validated, smoke test done; medium workstation run (ι_min 0.2, r ≤ 0.06) missed the moderate tier; diagnostic run at r ≤ 0.045 reaches the moderate tier on the nested region (defect/ι 0.021–0.038, ε_eff 0.6–1.0 %, |ι| ≈ 0.24) but nesting stops at the ι = 2/9 island chain (r_eff ≈ 0.019); nmax 3 (42 coefficients) reaches the **moderate tier**: defect/ι 0.009–0.023 at |ι| ≈ 0.24 with low shear inside (2/9, 1/4), ε_eff 0.08–0.13 %, regular to r_eff ≈ 0.037 (§10) |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 30 October 2026: created (pipeline, validation, smoke test, workstation commands); medium workstation run reviewed (§7) |

## Purpose and scope

Find an explicit **vacuum** field that satisfies C1 + C2 of the stellarator contract in the form
decided for Q-16:
- vacuum, so zero net toroidal current;
- nested surfaces;
- ι ≥ ι_min on them, provided by the 3-D shape;
- a quasi-axisymmetry defect that is small **relative to ι**.

The field must then be certifiable by the existing KAM pipeline. N-30 showed that the circular,
planar axis of `RationalStellarator.field` forces an O(r) QA defect fraction sqrt(ι₀/N)
(Garren–Boozer: a planar axis in vacuum admits no QS with ι ≠ 0). So the candidate here has a
**non-planar** magnetic axis.

- **Model.** `B = ∇Φ`, `Φ = φ + Σ_k a_k V_k`, cylindrical (R, φ, z), R₀ = B₀R₀ = 1. The V_k are
  stellarator-symmetric Dommaschk potentials with N = 2 field periods.
- **Particles.** Collisionless guiding centres, through the QS defect and the 1/ν functional ε_eff.
- **Out of scope.** Finite β, coils (Q-2), the volume version of `WeakQSDefect`, and alphas.

## Dependencies

- **Exact vacuum by construction.** Each V_k is harmonic. G = ∮B·dl/2π = 1 on toroidal loops,
  because Φ − φ is single-valued. So J = 0 and I_tor = 0 exactly. This is a symbolic identity for
  every coefficient vector, so it does not depend on the fit.
- **Exact Boozer angles (N-30 §2, proved informally).** `φ_B = Φ`, `θ_B = θ_s + ι(Φ − φ)`, with
  Jacobian `|B|²/B^φ`. Along the field line launched at θ_s = 0 this gives `θ_B = ιΦ`.
- **Nemov ε_eff** (`scripts/c2_diagnostics/nemov.py`). A sourced definition, validated there on the
  classical-stellarator limit. It is not in Lean.
- **The bridge from QS defect to drift** (N-29, compiled in the Boozer guiding-centre model, with
  orbits supplied). Its worst-case factor κ = 2δ/(B_min ι) is reported here.

## Sources and prior work

- **Dommaschk potentials.** W. Dommaschk, *Comput. Phys. Commun.* 40 (1986) 203. The structure
  follows that paper, a z-polynomial of degree l with coefficients in R^p (ln R)^q. The
  normalisation is **reconstructed** here and checked symbolically:
  - `D_{m,l}(1, z) = z^l/l!` and `∂_R D_{m,l}(1, z) = 0`;
  - the reverse for N_{m,l}.
  It may differ from the paper's by a basis change with the same span.
- **Seed axis.** The near-axis QA example of M. Landreman, W. Sengupta, G. G. Plunk, *J. Plasma
  Phys.* 85 (2019) 905850103, §5.1:
  - `R = 1 + 0.045 cos 2φ`, `z = −0.045 sin 2φ`;
  - η̄ = 0.9 and ι ≈ 0.42, recalled, not re-checked.
  Only the axis is used.
- **Garren–Boozer** (*Phys. Fluids B* 3 (1991) 2805, 2822) and **Landreman–Sengupta** (*J. Plasma
  Phys.* 84 (2018) 905840616): first-order QS needs a constant |B| on the axis and, in vacuum, a
  non-planar axis.

## Theory development

### 1. Basis (exact; `scripts/dommaschk_qa/basis.py`)

- **Radial functions.** `L_m = ∂²_R + R⁻¹∂_R − m²R⁻²`. The coefficients satisfy
  `L_m C_{m,0} = 0` and `L_m C_{m,k} = −C_{m,k−1}`.
  - Particular solutions are found exactly by a triangular solve in the ln R power, including the
    resonant cases p = ±m.
  - Homogeneous parts are added so that C_{m,k}(1) = C'_{m,k}(1) = 0 for k ≥ 1.
- **Potentials.** `D_{m,l} = Σ_k z^{l−2k}/(l−2k)! C^D_{m,k}`, and N_{m,l} likewise. Both are
  multiplied by cos mφ or sin mφ.
- **Stellarator symmetry,** `Φ(R, −φ, −z) = −Φ`. It keeps sin(mφ) × (l even) and cos(mφ) × (l odd).
  m = 0 leaves only the odd-l terms (vertical-field type). An axisymmetric quadrupole is therefore
  excluded.
- **Order.** m = 2i with i ≤ nmax, and l ≤ lmax. This gives 12, 24, 42 and 62 coefficients for
  (nmax, lmax) = (1, 3), (2, 4), (3, 5), (4, 6).
- **Self-test.** Every potential up to (2, 5) is harmonic, stellarator-symmetric and normalised,
  checked exactly in sympy.

### 2. Evaluation (`fieldeval.py`)

- Each gradient component is `F(x)·(A a)`, where F are the monomials R^p (ln R)^q z^j trig(mφ) and
  A is an exact table.
- Many coefficient vectors are integrated in one vectorised RK4 run. This is how the
  finite-difference Jacobian is computed: all columns in one batched integration.
- **Axis.** Newton on the period map, with a finite-difference monodromy M. Then
  |ι_axis| = (N/2π) arccos(tr M/2).
- **Surfaces.** Lines launched at distances r_j outboard of the axis on φ = 0.
  - ι comes from a weighted Birkhoff average of the angle about the axis, with the half/half
    difference as a convergence estimate.
  - The Boozer coefficients
    `c_mn = ⟨|B| Jac e^{−i(mι − nN)Φ}⟩` are weighted Birkhoff averages along **one** line. The line
    average equals the (θ_s, φ) torus average, and the mean Jacobian is a check.
- The QA defect is `sqrt(Σ_{n≠0} A_mn²)/B₀₀`, the convention of `c2_diagnostics/boozer.qs_defect`.

### 3. Objective and constraints (`optimize.py`)

Each start runs two `scipy.optimize.least_squares` stages (trust-region reflective). The trust
region is scaled in field units, s_k = RMS |∇V_k| near the seed axis.

- **Stage A, axis only (cheap).**
  - The on-axis transform: `|ι_axis| ≥ 1.2 ι_min`, as a hinge.
  - Non-planarity: `z_rms(axis) ≥ z_min`, as a hinge. With stellarator symmetry and N ≥ 2, the
    axis is planar exactly when z_axis ≡ 0.
  - **Constant |B| on the axis**, the first-order QA requirement.
  - Regularisation.
- **Stage B, full objective, on the surfaces r_j.**
  - The main term is `Σ_j Σ_{n≠0} |2c_mn/c₀₀|² / max(|ι_j|, ι_min)²`. This is (defect/|ι|)²,
    the Q-16 ratio itself, whenever ι_j ≥ ι_min.
  - Hinges on ι_j ≥ ι_min and on the axis terms of stage A.
  - A small penalty on the Birkhoff convergence error, against chaotic lines.
  - Regularisation λ Σ s_k² (a_k − a_seed,k)².
  - A lost surface contributes a constant penalty, and the other surfaces stay live.
- **Seed.** A linear least-squares problem: B parallel to the target axis, with |B| constant on it.
  B is linear in a.
  - Random starts add field-scaled perturbations and re-project onto the same linear conditions.
  - Start 0 is the unperturbed seed.
- **Sign convention.** The sign of ι depends on orientation (mirror images), so constraints use |ι|.
- **Selection.** Feasible starts come first (all surfaces regular, |ι| ≥ ι_min, non-planar axis),
  ranked by the worst defect/|ι|. Infeasible starts are ranked by cost.

### 4. Export and diagnostics (`diagnostics.py`)

The best coefficients are rounded to decimal rationals, 10 digits by default, and **every
diagnostic is recomputed on the rounded field**. That rounded field is the candidate.

- `candidate.json` contains:
  - the exact basis terms;
  - the rational coefficients;
  - a SHA-256 of both, the candidate identity.
- The field is rebuilt independently in sympy, and the fast evaluator must agree with it
  (≈ 10⁻¹⁵).
- Axis diagnostics: curvature and torsion, and non-planarity (z_max, z_rms, torsion).
- Poincaré sections at φ = 0 and φ = π/N.
- Nested-surface check: no line lost, Birkhoff error ≤ 10⁻⁶, and increasing section areas.
- The ι profile.
- QS defects for all helicities in `boozer.HELICITIES`, and the Lean-form δ = sup|∂_{φ_B}B| with
  κ = 2δ/(B_min|ι|).
- ε_eff from Nemov's formula, with 8 lines per surface started on the section conjugacy.
- `summary.json` and three PNG plots.

### 5. Validation

`validate.py` checks the pipeline against the rational field of N-30, which can be written exactly
in the non-symmetric basis (nmax = 1, lmax = 3; fit residual 3×10⁻¹⁶). The results agree with
`scripts/c2_diagnostics` to all quoted digits:
- ι = 0.1344898, 0.1374307, 0.1510525;
- A₁₀/B₀₀ = 0.0549 and A₁₁/B₀₀ = 0.0147;
- QA fraction 0.259 / 0.258 / 0.260;
- mean Jacobian 1.

The task runs this check first.

### 6. Smoke test (laptop, 30 October 2026; NOT a result)

The parameters were:
- nmax = 1, lmax = 3, so 12 coefficients;
- 2 starts, 2 processes;
- ι_min = 0.15, surfaces r = 0.015, 0.03, 0.045;
- 30 evaluations per stage B, 150 periods;
- 56 s wall in total.

The best start, recomputed on the rounded coefficients:

| r (launch) | r_eff | ι | QA defect / B₀₀ | defect / ι | QA fraction | κ | ε_eff |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0.015 | 0.019 | −0.180 | 0.0025 | 0.014 | 0.12 | 0.26 | 0.10 % |
| 0.030 | 0.037 | −0.173 | 0.0036 | 0.021 | 0.089 | 0.43 | 0.095 % |
| 0.045 | 0.054 | −0.162 | 0.0047 | 0.029 | 0.083 | 0.69 | 0.11 % |

- **Axis.** Non-planar, with z_max = 0.065 and |ι_axis| = 0.18. |B| on the axis varies by 0.4 %.
- **Surfaces.** Nested and regular out to r ≈ 0.048 (r_eff ≈ 0.055). They break up beyond that.
- **Comparison with the rational field (N-30)** at a similar radius:

  | | defect/ι | ε_eff |
  | --- | --- | --- |
  | rational field | 0.27 | ≈ 1 % at r_eff 0.05 |
  | this smoke candidate | 0.01–0.03 | ≈ 0.1 % |

  The improvement is about tenfold on both, with only 12 coefficients and a short search.
- **Caveats.**
  - These are smoke-test numbers: few coefficients, short traces and small aspect.
  - The volume is small (r_eff ≈ 0.05 at R ≈ 0.85).
  - ι = 0.16–0.18 is below typical QA values (≈ 0.4).
  - The shear is strongly negative.
  - The tier is only "moderate" (see below).

### 7. Medium workstation run (30 October 2026; untrusted, did not reach a tier)

Run `workstation/dommaschk-qa-20261030T112135Z` (hornbill, 16 jobs, 4.2 min wall), with results in
`scripts/dommaschk_qa/results/20261030T112135Z/`. The parameters were:
- nmax = 2, lmax = 4, so 24 coefficients;
- 16 starts;
- ι_min = 0.2;
- surfaces r = 0.02, 0.04, 0.06.

Outcome:
- **Every start missed the moderate tier.** The 7 starts that kept all three surfaces regular
  have defect/|ι| ≥ 0.12.
- **The best start (9)** has |ι_axis| = 0.25 and defect/|ι| = 0.12–0.13 on the inner surfaces.
  Its surfaces are nested only out to r = 0.032, ε_eff = 4.5 % at r = 0.02, and QA is not the best
  helicity on every surface. The summary's Q-16 checks fail: `nested`, `iota_ge_iota_min` and
  `qa_best_helicity`.
- **Starts with a low inner defect broke up at the outer surface.** For example, start 2 has
  defect/ι 0.028 and 0.059 at r = 0.02 and 0.04, and lost r = 0.06.
- **Compared with the smoke test** (12 coefficients, ι_min 0.15, surfaces at 0.015–0.045, defect/ι
  0.014–0.029, ε_eff 0.1 %), this is worse by about 5× in defect/ι and by about 40× in ε_eff.

Reading (numerical observation, not a theorem): the outer surfaces at r = 0.04–0.06 lie at or
beyond the nested region of these fields. The objective is then dominated by penalties for
broken surfaces, and the trade-off between ι ≥ 0.2, nested volume and QA defect is not resolved
by 24 coefficients. The run mixes two changes from the smoke test, ι_min (0.15 → 0.2) and the
surface radii. The next runs separate them: nmax 2 at the smoke surfaces (0.015, 0.03, 0.045)
with ι_min 0.15 and with 0.2. The larger run (ι_min 0.3, wider surfaces) is postponed until a
medium run reaches the moderate tier.

### 8. Diagnostic run at the smoke surfaces, ι_min 0.15 (30 October 2026; untrusted)

Run `workstation/dommaschk-qa-20261030T115455Z`: nmax 2 (24 coefficients), 16 starts, ι_min 0.15,
surfaces r = 0.015, 0.03, 0.045; 5.1 min wall on 16 jobs, results in
`scripts/dommaschk_qa/results/20261030T115455Z/`.

- **15 of 16 starts kept all three surfaces regular**, against 7 of 16 in the medium run. The
  surface radii, not ι_min, caused the earlier failure: with ι_min = 0.15 the optimiser still
  reached |ι| ≈ 0.24.
- **The best start (3)** has |ι| = 0.246 on the axis and 0.243 and 0.232 on the two inner
  surfaces. On those surfaces defect/|ι| is 0.021 and 0.038 (the moderate tier) and ε_eff is
  0.56 % and 0.96 % (W7-X level), with κ = 0.34 and 0.59 (< 1, as the N-29 bridge needs). QA is
  the best helicity.
- **What limits the volume: the ι = 2/9 island chain.** At high resolution the surfaces are nested
  only to r = 0.030 (r_eff ≈ 0.019). From r = 0.036 outward, ι locks at −0.2222 = −2/9, which is
  ι/NFP = 1/9: a resonant island chain, crossed because the shear is negative. Field lines are
  lost beyond r ≈ 0.048. The third surface lies in the island chain, so the summary's tier is
  "not small" even though the nested region meets the moderate tier.
- **Reading (numerical observation).** Defect/ι at the moderate level is attainable with 24
  coefficients. The obstacle is the volume: the ι profile has to avoid low-order resonances
  (2/9, 1/4 = 2/8, 2/7) across the target surfaces, so low shear or a placed ι window should
  enter the objective. A larger basis alone may not suffice.

### 9. Diagnostic run at the smoke surfaces, ι_min 0.2 (30 October 2026; untrusted)

Run `workstation/dommaschk-qa-20261030T120025Z`: as §8 but with ι_min 0.2; 2.7 min wall on 16
jobs, results in `scripts/dommaschk_qa/results/20261030T120025Z/`.

- **13 of 16 starts kept all three surfaces regular.** Nine of them have defect/ι ≤ 0.031 on the
  inner surface. Start 14 has |ι| = 0.32–0.34 with defect/ι 0.056–0.065 on all three surfaces.
- **The best start (4)** has |ι| = 0.258, 0.250 and 0.238, with defect/ι 0.020 on the inner
  surface and 0.051 on the outer one, ε_eff 0.66 % and κ 0.48.
- **The middle surface again sits on a resonance**, this time ι = 1/4 (2/8): r_eff blows up at
  r = 0.030. The tori on both sides are regular: r_eff 0.014 inside, 0.020–0.025 outside, out to
  r = 0.048, and field lines are lost from r = 0.054. So the summary reports nesting only to
  r = 0.024.
- **Conclusion from §§7–9 (numerical observation).** ι_min = 0.2 costs nothing: defect/ι of
  0.02–0.05 is reached at |ι| ≈ 0.25. Low-order resonances ι = 2/m (NFP = 2: 2/9, 1/4, 2/7, 1/3)
  crossing the target surfaces set the nested volume, together with outright loss of field lines
  near r ≈ 0.05.
- **Next steps.**
  - (a) More coefficients at the same surfaces (larger runs are cheap: 3–5 min wall for 24
    coefficients).
  - (b) An objective term keeping ι on all target surfaces inside a window free of low-order
    rationals (or penalising low shear less than resonance proximity). This needs a change to
    `optimize.py`.

### 10. Larger basis, nmax 3 (30 October 2026; untrusted): the moderate tier reached

Run `workstation/dommaschk-qa-20261030T120952Z`: nmax 3, lmax 5 (42 coefficients), 48 starts on
24 jobs, ι_min 0.2, surfaces r = 0.015, 0.03, 0.045, 100 evaluations per stage; 11.4 min wall,
0.8 GB peak. Results in `scripts/dommaschk_qa/results/20261030T120952Z/`.

**The best start (23)**, recomputed on the rounded rational coefficients at high resolution:

| r (launch) | r_eff | ι | defect/ι | ε_eff | κ |
| --- | --- | --- | --- | --- | --- |
| 0.015 | 0.011 | −0.246 | 0.009 | 0.08 % | 0.11 |
| 0.030 | 0.020 | −0.241 | 0.015 | 0.13 % | 0.20 |
| 0.045 | 0.029 | −0.235 | 0.023 | — | 0.37 |

- **Tier: moderate** (worst defect/ι 0.023). The inner surface is at the strong level, and QA is
  the best helicity.
- **Low shear.** ι runs from 0.248 on the axis to 0.227 at r = 0.06, inside the resonance-free
  window (2/9, 1/4) = (0.222, 0.25). So no low-order island chain crosses the region.
- **Volume.** Diagnostic lines are regular and r_eff increases out to r = 0.06 (r_eff ≈ 0.037).
  The strict nesting test (Birkhoff error ≤ 10⁻⁶) passes to r = 0.042 (r_eff ≈ 0.027), and lines
  are lost from r = 0.066. The summary's `nested` flag is false only because of those outer lines.
- **Axis.** Non-planar, with z_max = 0.051, R between 0.90 and 1.00, curvature 0.62–1.21.
- **Other starts.**
  - Start 9: |ι| = 0.42–0.40 with defect/ι 0.007 and 0.008 on the two inner surfaces. Its outer
    surface sits on ι = 2/5. This is a high-ι family worth a windowed run.
  - Start 34: defect/ι 0.007–0.017, but |ι| 0.12–0.17 < ι_min.
- **Reading (numerical observation).** Going from 24 to 42 coefficients improved the best worst
  defect/ι from 0.05 to 0.023 and the clean volume from r_eff ≈ 0.019 to about 0.027–0.037. The
  best candidate is the one whose low shear keeps ι between 2/9 and 1/4, which confirms §9.
  `candidate_for_certification` is false only because of the strict nesting flag. Before any
  certification, a run with the ι window and the outer surface moved to r ≈ 0.06 should make the
  whole optimised region strictly nested.

### 11. Larger basis, nmax 4 (30 October 2026; untrusted): no improvement

Run `workstation/dommaschk-qa-20261030T122122Z`: nmax 4, lmax 6 (62 coefficients), 48 starts on
24 jobs, ι_min 0.2, surfaces r = 0.015, 0.03, 0.045, 150 evaluations per stage and 300 periods;
40.6 min wall, 1.5 GB peak. Results in `scripts/dommaschk_qa/results/20261030T122122Z/`.

- **26 of 48 starts were regular at optimiser resolution.** The best of them (start 39) had a worst
  defect/ι of 0.041. Its middle surface had |ι| = 0.2222 = 2/9, and four other starts were in the
  0.044–0.052 range.
- **The high-resolution diagnostics (96 steps per period, 600 periods) reject it.**
  - The middle surface lies in the 2/9 island chain, and the outer surface is lost.
  - Strict nesting holds only to r = 0.015, with κ ≈ 1.
  - The QA defect is not the best helicity on every surface.
  - Tier "not small".
  - Some traced lines left the domain of the potentials (`log R` of a negative number in the
    log), so the field does not extend to the outer region.
- **Reading (numerical observation).** With 62 coefficients the optimiser exploits the coarse
  resolution of its objective (48 steps per period): results that look good at that resolution do
  not survive the high-resolution check. The nmax 3 candidate of §10 remains the best. If larger
  bases are tried again, the optimiser resolution (`DQA_EXTRA="--ns 96"`) and the ι window should
  go with them.

### 12. Windowed run at larger radii (31 October 2026; untrusted): worse

Run `workstation/dommaschk-qa-20261031T034330Z`: nmax 3 (42 coefficients), 48 starts on 24 jobs,
ι_min 0.2, `--iota-window 0.226,0.248`, surfaces r = 0.02, 0.04, 0.06; 19.5 min wall. Results in
`scripts/dommaschk_qa/results/20261031T034330Z/`.

- **38 of 48 starts were regular, but every one has defect/ι ≥ 0.08.** The best by defect is start
  1, at 0.046–0.082, but its |ι| = 0.221 is just outside the window. The selected start 7 has
  defect/ι 0.12–0.17 and ε_eff ≈ 5 %, and QA is not the best helicity on every surface.
- **The window does not hold at r = 0.06.** In the high-resolution check, ι reaches 2/9 from
  r ≈ 0.048 (island chain). Strict nesting holds to r = 0.040 (r_eff ≈ 0.021), which is no larger
  than the §10 candidate's.
- **Reading (numerical observation).** At 42 coefficients the trade-off between volume and
  quasi-axisymmetry is steep. Moving the optimised surfaces from r ≤ 0.045 to r ≤ 0.06 raises
  defect/ι from 0.009–0.023 (§10) to above 0.08. The window keeps the selection honest but
  cannot remove the shear that carries ι through 2/9 at larger radius. The §10 candidate remains
  the best. Further gains in volume probably need more field periods or a different seed axis
  rather than more coefficients at NFP = 2.

### 13. Windowed high-ι run (31 October 2026; untrusted): failed

Run `workstation/dommaschk-qa-20261031T040304Z`: nmax 3, 48 starts, ι_min 0.38,
`--iota-window 0.405,0.44`, surfaces r = 0.015, 0.03, 0.045; 12.6 min wall. Results in
`scripts/dommaschk_qa/results/20261031T040304Z/`.

- **Only 2 of 48 starts kept all surfaces regular.** The selected one (start 28) has |ι| 0.385–0.364,
  below the window, with defect/ι 0.11, ε_eff ≈ 10 % and κ > 1. Its outer surface sits on
  ι = 4/11, and strict nesting holds only to r = 0.015.
- **Reading.** The random starts around the NFP-2 seed axis rarely reach |ι| ≈ 0.4. The high-ι
  start of §10 (start 9) was a lucky outlier, and the optimiser cannot be warm-started from it (no
  such option yet). Forcing ι up through the window makes the objective much harder.

**Summary of §§7–13.** At NFP = 2 the best candidate is the nmax 3 one of §10:
- defect/ι 0.009–0.023 at |ι| ≈ 0.24, with ε_eff ≈ 0.1 %;
- strictly nested to r_eff ≈ 0.027.

Larger bases, larger radii and higher ι all made things worse. Two directions remain open:
- three field periods (a quick laptop test with NFP 3 and 2 starts already gave |ι| ≈ 0.33 with
  defect/ι 0.04–0.05);
- a warm-start option, to refine the §10 candidate and the high-ι outlier.

### 14. Warm start (`--init`), 31 October 2026

`optimize.py --init FILE` restarts from an earlier field instead of the seed (`DQA_EXTRA="--init …"`
in the task). FILE is either:
- a `candidate.json`: coefficients are matched by basis name, so a smaller basis embeds into a
  larger one, and the exact rationals are used;
- a work-directory `start_NNN.json`, with the same basis size.

How it runs:
- Start 0 is the field itself. Start k ≥ 1 adds a field-scaled perturbation of size
  `--init-sigma` (default 0.001), without re-projection.
- Stage A is skipped, the regularisation pulls towards the initial field, and the field's axis
  is the first axis guess.
- The configuration records the file's SHA-256, so a changed file is not silently resumed.

Default behaviour is unchanged: residuals and start points are bit-identical without `--init`.

Laptop check (untrusted, 2 starts, not a committed result):
- Restarting from the §10 candidate with no optimisation reproduces its metrics exactly.
- A perturbed restart with 4 stage-B evaluations moved to |ι| ≈ 0.32, almost shearless.
- At high resolution that restart has defect/ι 0.013, 0.016 and 0.021 (moderate tier),
  ε_eff 0.3 % and 1.0 %, κ 0.41–0.70, and strict nesting to r = 0.036. Its r_eff ≈ 0.016 at
  r = 0.045 is smaller than the §10 candidate's 0.029, and lines are lost from r = 0.048, where ι
  meets 2/7.

So restarting with small perturbations explores a family of low-shear QA fields around the §10
candidate, with |ι| from about 0.23 to 0.32. Workstation refinement runs come next.

### 15. Three field periods, nmax 2 (31 October 2026; untrusted): first certification candidate

Run `workstation/dommaschk-qa-20261031T044845Z`: NFP 3 (`DQA_EXTRA="--nfp 3"`), nmax 2, lmax 4
(24 coefficients), 48 starts on 24 jobs, ι_min 0.25, surfaces r = 0.015, 0.03, 0.045; 9.6 min wall.
Results in `scripts/dommaschk_qa/results/20261031T044845Z/`.

**43 of 48 starts kept all surfaces regular.** The best start (43), on the rounded rational
coefficients at high resolution:

| r (launch) | r_eff | ι | defect/ι | ε_eff | κ |
| --- | --- | --- | --- | --- | --- |
| 0.015 | 0.008 | −0.294 | 0.007 | 0.13 % | 0.14 |
| 0.030 | 0.015 | −0.283 | 0.013 | 0.25 % | 0.21 |
| 0.045 | 0.020 | −0.268 | 0.020 | 0.47 % | 0.40 |

- **Tier: moderate** (worst defect/ι 0.020), with the inner surface at the strong level. The
  summary's Q-16 checks all pass, and **`candidate_for_certification` is true**, for the first
  time.
- **Regularity.** Diagnostic lines are regular out to r = 0.066 (r_eff ≈ 0.025, Birkhoff errors
  10⁻⁸–5×10⁻⁶). The first island chain is at r = 0.072, where ι ≈ 0.214 = 3/14.
  - The strict "nested up to" figure reads 0 only because the innermost line (r = 0.006)
    converges slowly: Birkhoff error 5.7×10⁻⁶ against the 10⁻⁶ tolerance. This is the known
    near-axis artefact; the lines outside it are regular.
- **The ι profile** falls from 0.298 on the axis to 0.235 at r = 0.066. With NFP 3 the low-order
  resonances 3k/m are sparser in this range (3/10 lies above, 3/13 = 0.231 and 3/14 below).
- **Axis.** Weakly non-planar: z_max 0.016, R between 1.065 and 1.076.
- **Comparison with the NFP-2 candidate of §10** (42 coefficients):
  - similar defect/ι;
  - higher ι (0.27–0.29 against 0.24);
  - ε_eff 0.1–0.5 %;
  - κ ≤ 0.40;
  - a slightly larger regular region;
  - **half the coefficients**, which makes the Lean certification (exact field, harmonicity,
    KAM tori) cheaper.

This is now the lead candidate for the certification path below. Untrusted numerics.

### 16. Three field periods, nmax 3 (31 October 2026; untrusted): worse than nmax 2

Run `workstation/dommaschk-qa-20261031T045824Z`: NFP 3, nmax 3 (42 coefficients), 48 starts,
ι_min 0.25, surfaces r = 0.015, 0.03, 0.045; 21.4 min wall. Results in
`scripts/dommaschk_qa/results/20261031T045824Z/`.

- **45 of 48 starts were regular at optimiser resolution.** The best worst defect/ι was 0.045.
- **The selected start (4) fails the high-resolution check.** Its ι falls from 0.351 to 0.300 and
  crosses the resonances 1/3 (r ≈ 0.024) and 3/10 (the outer surface sits on it). That gives
  defect/ι 0.054 and ε_eff 1.1–2.1 %, and strict nesting only to r = 0.018. Tier "not small".
- **The pattern of §11 repeats.** The larger basis buys more shear and overfits the coarse
  objective, and does not improve on the smaller basis. The NFP 3, nmax 2 candidate of §15
  remains the lead.

## Claims and evidence

1. **Complete mathematical proof (symbolic, sympy).** The basis potentials are harmonic and
   stellarator-symmetric. Every candidate is therefore an exact vacuum field with zero net
   toroidal current.
2. **Numerical observation (validated).** The pipeline reproduces the N-30 numbers for the rational
   field.
3. **Numerical observation (smoke test).** A 12-coefficient Dommaschk field with a non-planar axis
   reaches QA defect/ι ≈ 0.014–0.029 with ι ≈ 0.16–0.18 on nested surfaces up to r_eff ≈ 0.05,
   and ε_eff ≈ 0.1 %. This is about 10× better than the planar-axis rational field. Untrusted, and
   preliminary.

## Difficulty, barriers and readiness

**Success under the Q-16 criterion.** The decided criterion is qualitative: "defect small relative
to ι". The tiers below are a proposal and still need the user's decision. A candidate counts
when, on all optimised surfaces:
- the field is vacuum (automatic);
- the surfaces are nested and regular;
- |ι| ≥ ι_min;
- the axis is non-planar;
- QA is the best helicity;
- and defect/|ι| is at most
  - **strong**: 0.01, consistent with N-27's ε_S ≤ 10⁻³ B₀ at ι ≈ 0.1–0.4;
  - **moderate**: 0.05, a 5× improvement on the rational field's 0.27.

`summary.json` reports the tier, ε_eff and κ. ε_eff ≲ 1 % is W7-X level. A useful C2 bound through
the N-29 bridge also needs κ < 1.

**Barriers.**
- **Optimiser quality.** Chaotic outer surfaces make the objective rugged. The workstation runs use
  many starts and more evaluations.
- **Volume against defect.** The smoke candidate is nested only out to r_eff ≈ 0.05.
- **B2 of N-27, low shear or here strong shear.** The KAM twist constant must be bounded away from
  0 and the strip must be wide enough.
- **Coefficient size.** Some high-l coefficients are O(10–30), because z^l/l! is small near the
  axis. This is harmless for exact rationals but matters for the Lean majorants. If it becomes a
  problem, raise λ.

**Readiness.**
- No Lean yet.
- The smallest next step is the workstation medium run (`Workstation.md`, Next Commands). Then the
  larger run with ι_min = 0.3 and wider surfaces, if the medium run reaches the moderate tier.

## Outputs and next dependencies

**Path to certification** after a successful workstation candidate, as an on-demand top module:

1. **Exact field in Lean.** Define the potential from `candidate.json`, with exact rational
   coefficients and terms R^p (ln R)^q z^j trig(mφ). Prove harmonicity by a polynomial normal-form
   checker over ℚ[R, R⁻¹, ln R, z] ⊗ trig (the `RationalStellarator` pattern, `eval_cert`). This
   gives `VacuumField`, J = 0 and I_tor = 0, so C1 except for ι.
2. **KAM tori.** Certify one torus per optimised surface with the flow-form a posteriori pipeline
   (`KamFlow*`, `KamTorusA*`). This needs:
   - new holomorphy and majorant constants for ln R near R ≈ 1;
   - a Diophantine ι_j with |ι_j| ≥ ι_min, giving C4 and the ι part of C1 on the surfaces;
   - the twist bound, which is the main risk.
3. **Boozer angles.** One cohomological equation per torus:
   `(∂_φ + ι ∂_θ) η = |B|²/B^φ ∘ K − 1`. It has the same divisor as the KAM step
   (`cohSol_estimate`, `StripAlgebra.Bd.coh`), and φ_B = Φ is exact in vacuum.
4. **QS defect.** A certified ℓ¹ bound on the non-QA Boozer part of |B| on each torus (`KronBall`,
   `StripPaleyWiener`), compared with ι_j. This gives the vacuum Q-16 criterion.
5. **C2.** Through the N-29 bridge (`approxOmnigenousOn_of_defect_le`): a per-bounce drift bound,
   useful once κ < 1 (the smoke candidate has κ = 0.26–0.69). An ε_eff bound needs Q-21/Q-23.

**Suggested registry updates** (for the coordinator):
- Q-16: "route (ii) stage 1: pipeline built and validated (N-31); smoke candidate defect/ι ≈ 0.02;
  workstation runs pending".
- N-31 row in the research graph.
- An edge N-30 → N-31 → Q-16.
