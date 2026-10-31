# Dommaschk KAM certificate: design study for certification step 2

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-33` |
| Title | Design of a Lean certificate of one exact invariant torus (a posteriori KAM) of the Dommaschk QA target, and the path to C1 |
| Kind | research approach / certificate design (with untrusted estimates and a Lean cost prototype) |
| Addresses | `Q-16` (route ii, step 2), `G-1`, contract clause C1 (`Contract.CurrentFreeTransform` through `DommaschkQA2R.candidate_currentFreeTransform`) |
| Depends on | N-31 (`dommaschk-qa.md` §20, §24, §25: the target and the oracle); `kam-route.md`, `kam-k3-plan.md`, `after-kam.md`, `gc-kam-status.md` (the two certified KAM pipelines). Lean: `Design/KamFlowIteration` (`FlowField.KamH.kam_flow_torus`), `KamFlowStep` (`SC`, `StepH.kam_step`), `KamFlowFrame`, `KamFlowField` (`FlowField`), `KamTorusAExact.torusA_exact`, `RationalStellaratorGCTorusExact.gc_exact_torus`, `Certificates/KronBall`, `KronBallGrid`, `KronProof2D`, `Kronecker2DWeighted`, `Theory/KAM/{StripAlgebra, Cohomological, KamSequence, Composition, Diophantine}`, `DommaschkQA2R.candidate_currentFreeTransform`, `Contract.IotaOnTorus`/`PoloidalAngle` |
| Dependency requirement | The compiled generic KAM theorem for polynomial flow forms (`kam_flow_torus`, standard axioms) and the ball-arithmetic certificate machinery (`KronBall*`, `kron2_proof`) are used as they are. The oracle numbers of N-31 §25 and everything computed here are **untrusted numerics**. |
| Produces | This design; the untrusted estimator `scripts/dommaschk_kam/kam_constants.py`; the on-demand cost prototype `PlasmaLean/Design/DommaschkKamProto.lean` (not imported by `PlasmaLean.lean`); three structural findings (§2.2), one of them at contract level; a module plan (§6) and a list of gaps (§7) |
| Difficulty | hard: no new analysis is needed, but the KAM interface must be generalised in three places, one contract definition must change, and the residual certificate is about 10× the guiding-centre certificate per node |
| Status | proof-ready design (conditional go, §8) |
| Lean evidence | prototype only: `PlasmaLean.Design.DommaschkKamProto.protoBig`, `protoSmall` (on demand, not imported; axioms `[propext]`) |
| Audit evidence | not audited; §2.2 (O3) is a candidate audit finding for `Theory/Contract/StellaratorContract` |
| Last updated | 31 October 2026: created |

## Purpose and scope

Certification step 1 of the Dommaschk target is done: `Design/DommaschkQA2R` proves
`candidate_vacuum`, `candidate_loopCurrent_eq_zero` and `candidate_currentFreeTransform`. The last
of these reduces C1 to a nonempty family of tori with `IotaOnTorus (field candidate) R z ι`, `C¹`
poloidal loops and `|ι| ≥ ι_min`. Step 2 must supply one such torus. This note designs the Lean
certificate of one exact invariant torus by the a posteriori KAM theorem already in the library,
and estimates its cost against the laptop budget:
- ≤ 6 GB per Lean process;
- a default build of ≤ 60 CPU-min;
- an on-demand top module of ≤ 240 CPU-min;
- the workstation for first builds.

**Model.** Vacuum field `B = ∇(φ + V)` of `DommaschkQA2R` (NFP 2, 42 potentials, the 9 log
potentials exactly 0). Cylindrical `(R, φ, z)`. Field lines are parametrised by `φ`, with
frequency vector `(ι, 1)`. The oracle's flow form is

    D 𝓛R − 2R·Ps = 0,   D 𝓛z − s·Pz = 0,   𝓛 = ∂_φ + ι∂_θ,

with `s = R²`, `D = s³(1 + ∂_φV) = s⁴B^φ`, `Ps = s⁴∂_sΦ` and `Pz = s³∂_zΦ`. These are exact rational
polynomials of degree 8 in `s` and 5 in `z`, and of degree 3 in `cos ψ, sin ψ` (`ψ = 2φ`).

**Out of scope.** C2, coils, the trapping theorem (C1 does not need it), and tori other than
one per surface.

## Dependencies

- **Compiled (default build, standard axioms).**
  - The generic KAM theorem `FlowField.KamH.kam_flow_torus` (`Design/KamFlowIteration`), with
    its step `FlowField.StepH.kam_step` (`Design/KamFlowStep`) and frame identities
    (`Design/KamFlowFrame`).
  - The instances `KamTorusAExact.torusA_exact` (rational field) and `gc_exact_torus`
    (guiding-centre field, the `FlowFieldS` variant; on demand).
  - The KronBall chain (`Certificates/KronBall`, `KronBallGrid`, `KronProof2D`).
  - `DommaschkQA2R` (step 1).
- **Sourced, used only as design input.** FHL 2017 and ELP-S 2025 (`kam-route.md` §2). The
  Lean theorem is a self-contained explicit-constant version, so no sourced theorem enters
  as a premise.
- **Untrusted numerics.** The oracle `scripts/dommaschk_kam/` (N-31 §25) and the estimator
  `kam_constants.py` (§3). The estimator is checked against one certified number: fed the
  certified inputs of torus A, its transcription of `SC.cK` gives 10 748.5, and
  `KamTorusAExact.cA_cK` certifies `cK ≤ 10 800`.

## Sources and prior work

- Figueras–Haro–Luque, *FoCM* 17 (2017) 1123, Thm 2.5 and Lemma 4.3 (the ad hoc Rüssmann
  estimate with finitely many divisors treated exactly).
- Enciso–Luque–Peralta-Salas, *JEMS* 27 (2025), Thm 6.2 and Def. 6.1 (the flow form and the
  twist).
- The repository's two instances of the generic theorem: `kam-route.md` §2–§5 and
  `gc-kam-status.md` §5 (the KronBall chain, costs in §5.3).

## Theory development

### 1. What gives the exact torus for the rational field

**The theorem.** `FlowField.KamH.kam_flow_torus` (`Design/KamFlowIteration`) concludes:

    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ F.resR ι u z = 0 ∧ F.resZ ι u z = 0 ∧
      Close (rInf c) ι u z u₀ z₀ μ

It holds for every `F : FlowField`. The data are:
- polynomials `D, n_R, n_z` (`PolyExpr ℂ (Fin 6)` in `u = R − 1, z, c = cos 2φ, s = sin 2φ, w_R, w_z`);
- flux-primitive numerators `P_a, P_b` and the torsion numerator `P`;
- the interface identities `divFree`, `flux_a/b/c` and `torsion_poly`;
- the frame vector `V₀ = (u, z)`, with exponent 3 in `w = D/R³` and `R = 1 + u`.

The rational instance is `field14` (`Design/KamNewtonField`, `KamIteration`). Its hypotheses
`KamH` are:

| Hypothesis | Content | For torus A (`KamTorusAExact`) |
| --- | --- | --- |
| `G.dio` | `Diophantine (ι/2) γ 1` | `γ = 0.0687` (`torusA_period_diophantine`) |
| `e0R`, `e0Z` | `Bd ρ₀ (resR/Z(K₀)) e₀`: weighted ℓ¹ norm `Σ|f_km| e^{ρ₀(|k|+|m|)}` of the polynomial residual | `e₀ = 5.83e-22`, `ρ₀ = r_A = 0.1257` (`KamTorusAStrip.Bd_resR₀` ← `KamTorusAWeighted`, Kronecker) |
| `hadm` | `AdmBounds` for every analytic torus `μ`-close to `K₀` on all strips in `[ρ∞, ρ₀]`: torus norms; `‖D‖, ‖∂D‖, ‖n‖, ‖∂n‖`; `‖D⁻¹‖`, `‖R⁻¹‖`, `‖W₀⁻¹‖` (`W₀ = ∂_θK × V₀`); `‖T₀‖` and the twist `|⟨T₀⟩| ≥ τ` | `torusA_adm` (`KamTorusAAdm`, surrogate and frame/twist modules) |
| `hC2R/Z` (in `G`) | `½ majD2(res) ≤ C₂`: a crude polynomial majorant at `avec + Tq·mvec` | `C₂ ≤ 6e9` (`cA_C2R`) |
| `hsmall` | `32 κ e₀/δ₀⁴ ≤ 1`, `δ₀ = ρ₀/7`, with `κ = SC.kap` explicit in the above | `κ ≈ 5.7e9`, margin ≈ 900 |
| `hμK/t/L` | displacement budget `≤ μ` | `μ = 1e-10` |
| reality and analyticity of `K₀` | | `KamTorusAStrip` |

**Field-independent parts.**
- The whole generic layer: `KamFlowField` (operators and the interface), `KamFlowFrame`,
  `KamFlowStep` and `KamFlowIteration`.
- The theory: `Theory/KAM/StripAlgebra`, `Cohomological`, `KamSequence`, `Composition`
  (majorants), `Diophantine` (the conjugate-norm method).
- The certificates: `Kronecker2D`, `Kronecker2DWeighted`, `KronProof2D`, `KronBall`,
  `KronBallGrid`, `KronExpr`, `PolyExprSMajQ`, and `eval_cert`/`kernel_fact`.

**Field- or torus-specific parts.**
- The `FlowField` instance (polynomials, flux primitive, identities).
- The torus data, the residual certificate, the admissibility bounds (frame, inverses,
  twist), `C₂` and the Diophantine instance.
- The passage to the contract: `RationalStellaratorForever.ExactTorus` →
  `RationalStellaratorContract.iotaOnTorus`.

**The second instance is the template here.** The guiding-centre torus (`gc-kam-status.md` §5)
replaced the exact Kronecker residual by a **KronBall chain**:
- every intermediate quantity is a ball `‖X − x‖_r ≤ ε` with a rounded trigonometric-polynomial
  centre;
- one kernel check per node (`node_full`, `kron2_proof`) bounds the exact truncation-and-rounding
  remainder;
- a high-resolution chain (40 × 30, `2^-101`, about 60 nodes) gives `e₀ = 3.7e-23`;
- a low-resolution chain (16 × 12, about 110 nodes) gives every admissibility bound at once for
  **all** `μ`-close tori, with no Lipschitz transport.

The cost was about 35 min sequential, with a peak of 5.5 GB, 16 + 4 check modules and 1 MB data
modules.

### 2. What transfers, what must be re-instantiated, what is new (question 1)

#### 2.1 Summary

| Part | Status for the Dommaschk field |
| --- | --- |
| `StripAlgebra`, `Cohomological`, `KamSequence`, `Composition`, `Kronecker2D*`, `KronProof2D`, `KronBall`, `KronBallGrid`, `KronExpr`, `kernel_fact`/`eval_cert` | **unchanged** |
| Diophantine instance | **re-instantiate**: `ι_A/2 = −(19+√5)/178` is a root of `89x² − 19x + 1` (discriminant 5), so the `DiophantineB` pattern applies verbatim; `γ = 0.1193` (attained at `k = 1`) |
| Torus data, residual certificate | **re-instantiate on the GC pattern** (KronBall chain), at about 10× the size per node (§4); new emitter (port `scripts/gc_kam/{ballcert,slp,emit_lean}.py`) |
| Admissibility (`AdmBounds` for all `μ`-close tori) | **re-instantiate on the GC pattern** (low-resolution chain about 24 × 20). Approximate inverses (surrogate method) are needed for `D` (Neumann ratio 0.92, §2.3) and for the twist (`D³W₀²`, ratio 1.9); Neumann is enough for `R` (0.15) and, more crudely, for `W₀` (0.60) |
| `C₂` | **re-instantiate** (`PolyExpr.majD2` of the new polynomials in `u = R − R₀`; `eval_cert`) |
| Generic `FlowField` layer | **generalise** (new, §2.2: O1, O2) |
| Rüssmann constant | **improve** (new, small: §3.3) — optional, but it decides the mode count |
| Field identification (`D, n` ↔ `field candidate`, flux primitive) | **new instance work**, routine (§2.4) |
| Exact torus → `IotaOnTorus` | **blocked by the contract definition** (§2.2, O3) |
| `StripPaleyWiener`, `AnalyticComposition`, `InvSqrt`, `PolyExprS` | **not needed**: the field is polynomial after clearing `s³`, with no log, no node and no Biot–Savart |

#### 2.2 Three structural obstacles (numerical observations, `kam_constants.py`, torus A at 40 × 32)

**(O1) The frame vector of the interface fails for this torus.**
- `FlowField` uses `V₀ = (u, z) = (R − 1, z)`: the radial vector from the circle `R = 1, z = 0`,
  which is the exact magnetic axis of the rational field.
- The Dommaschk axis is non-planar: `R ∈ [0.852, 0.965]`, `|z| ≤ 0.066`. Torus A has minor
  radius 0.018–0.051.
- On torus A the winding form `W₀ = ∂_θK × V₀` changes sign, both for `V₀ = (R − 1, z)` and for
  any fixed centre `(R₀, 0)`. So `‖W₀⁻¹‖` does not exist (FFT: `sW ≈ 3e12`).
- **Remedy: a moving centre.** Take `V₀ = K − A(φ)`, where `A` is a trigonometric
  approximation (4 harmonics in `ψ`) of the magnetic axis. Then `W₀ ∈ [−1.13e-3, −7.5e-4]`.
- Alternatives are worse:

  | `V₀` | `sW` | `tT` | `⟨T₀⟩` |
  | --- | --- | --- | --- |
  | radial from the axis approximation | 1.8e3 | 2.4e3 | 14.06 |
  | radial from the θ-centroid | 2.2e3 | 2.7e3 | 14.06 |
  | curve normal `J∂_θK` | 7.5e3 | 2.8e4 | 14.06 |

  The average torsion 14.06 is the same for every frame, as it must be.
- **Effect on the Lean proofs.** Only the torsion and frame part changes. `𝓛V₀ = X + Ê − A'`, so
  the torsion numerator becomes `P = (D²(X − A' − DX·V₀)) × V₀`, still a polynomial in
  `(u, z, c, s)`. The flux identity and `⟨η₂⟩ = 0` do not involve `V₀`.

**(O2) `R = 1 + u` and the exponent 3 are hard-coded.**
- **The density.** The invariant area density is `w = R B^φ = G/R`. With the minimal polynomial
  clearing `D = s³G`, this gives `w = D/R⁷`, so the exponent is **k = 7** and not 3. The
  divergence identity becomes `R∂_φD − k n_R + R∂_u n_R + R∂_z n_z = 0`.
- **In the constants:** `h = R^k/(DW₀)`, `T₀ = R^k P/(D³W₀²)`, `sR³ → sR^k`, `3sR → k sR`.
- **The centre.** The polynomials should use `u = R − R₀` with `R₀ ≈ 0.91`, the middle of the
  `R`-range `[0.816, 1.001]` of the torus. The oracle shows (N-31 §25) that majorants in
  unshifted or far-off variables are large: `ℓ¹(D) = 1.9e3` in `s`.
- **Majorants at the strip norms** (`au = ‖R − R₀‖ = 0.16`, `az = 0.14`, `r = 0.063`):

  | | value | `∂_u` | `∂_z` | `∂_u²` |
  | --- | --- | --- | --- | --- |
  | `D` | 3.2 | 26 | 22 | 263 |
  | `n_R` | 4.1 | 46 | 48 | 685 |

  The sharp FFT values are `‖D(K)‖ = 1.26` and `‖∂_RD(K)‖ = 7.0`.

**(O3) The contract cannot hold for any torus of this field: the poloidal angle needs a fixed
circle.**
- **The definition.** `IotaOnTorus B R z ι` requires `PoloidalAngle R z R₀ z₀ Θ`: a polar angle
  of `(R − R₀, z − z₀)` about a fixed circle `R = R₀, z = z₀` that winds once in `θ`. Its
  `polar` field requires the torus to avoid the circle, and `wind_θ` requires one turn per
  section.
- **Torus A fails it.** A grid search over fixed points `(R₀, z₀)` finds at most **73 of 256**
  cross-sections enclosing a common point, at (0.958, 0). All 256 would be needed.
- **Every surface of this field fails it.** The axis projection spans about
  0.11 × 0.13 in the `(R, z)` plane, while the nested region has `r_eff ≤ 0.053`. So no
  certifiable surface of this field satisfies `IotaOnTorus`.
- **Consequence.** `candidate_currentFreeTransform` is correct but its torus hypothesis is
  unreachable for this candidate. Its docstring says C1 "reduces to certified tori"; that is
  true only after the contract fix.
- **Remedy (a coordinator and audit decision).** Allow a continuous, 2π-periodic reference curve
  `(R₀(φ), z₀(φ))` in `PoloidalAngle`:
  - a constant curve gives the present definition back, so the existing instances survive;
  - `IotaOnTorus.tendsto` carries over, because along a field line the angles about two
    admissible reference curves differ by a bounded continuous periodic function;
  - an honesty sanity theorem should accompany the change: the transform does not depend on
    the admissible reference curve;
  - for the Dommaschk torus, the reference curve is the axis approximation `A` of (O1), and
    the winding follows from the certified `W₀ < 0`.
- This is a definitional change to a contract clause. It needs the audit lane.

#### 2.3 Denominators and inverses on torus A (`r = 0.063`)

| quantity | range on the torus | best Neumann ratio `min_c ‖F − c‖/|c|` | sharp `‖F⁻¹‖` |
| --- | --- | --- | --- |
| `D` | [0.262, 1.042] | 0.918 (`c = 0.658`) | 4.23 |
| `W₀` | [−1.13e-3, −7.5e-4] | 0.604 | 1.76e3 |
| `R` | [0.816, 1.001] | 0.153 | 1.26 |
| `D³W₀²` | | 1.89 | 7.4e7 |

- **`D` is bounded away from 0** (min 0.26), but a Neumann bound about a constant loses about
  4× (`1/(0.658·0.082) = 18.5` against 4.23). Use an approximate inverse `q_D`, as
  `KamTorusASurrogate` does for `D³W₀²`.
- **The twist.** Its certificate needs `‖q D³W₀² − 1‖ ≲ τ/(10 tT) ≈ 6e-4`. The weighted tail of
  `1/(D³W₀²)` outside the box is 4.8e-4 (16 × 12), 5.1e-5 (20 × 16) and 5.5e-6 (24 × 20), so `q`
  needs about 20 × 16 modes.

#### 2.4 Field identification and flux primitive (checked on the exact data)

- **The flux primitive.** `FlowField` needs polynomial `P_a, P_b` with
  `dα = (flux 2-form)`. For `B = ∇Φ` the homotopy formula gives `A_R = −∫₀^z R B^φ dz'` and
  `A_φ = ∫₀^z R B^R dz' + g(R, φ)`, and then a gauge `χ = ∫A_φ dφ`.
- **Where a log could appear.** A `ln R` would come from an axisymmetric term `R^{−2}z` in `V`.
  A `dφ`-component that no gauge removes would come from a non-constant axisymmetric part
  `⟨R∂_RV⟩_φ`.
- **The exact data have neither.** The only `m = 0` term of `V` (61 terms) is `c·z`. So a
  Laurent-polynomial primitive **without** `dφ`-component exists, and the plain `FlowField`
  form (not `FlowFieldS`) suffices after (O2).
- **What remains is routine.** Emit `D, n_R = 2R·Ps, n_z = s·Pz, P_a, P_b` as `PolyExpr` in
  `(u, z, c, s)`. Prove `divFree` and `flux_*` by sliced polynomial normal forms (`sliceCheck`,
  as `DommaschkQA2RDataCheck*`, ≤ 3.1 GB). Identify them with `field candidate` at real points.

### 3. KAM constants for the Dommaschk torus (untrusted estimate)

#### 3.1 Method

`scripts/dommaschk_kam/kam_constants.py` transcribes `SC.cK`, `SC.cL` and `SC.kap` of
`KamFlowStep` formula by formula, generalised as in (O1) and (O2) (`R₀`, `k = 7`, moving centre).
- **Inputs.** The strip norms are FFT values on the oracle torus (sharp, as a ball chain gives
  them). `C₂` is the crude polynomial majorant, as in the existing proofs.
- **Validation.** With the certified torus-A inputs and `k = 3` it reproduces `cK = 10 748.5`
  (certified `≤ 10 800`).
- **Run on the torus.** The torus is the double-precision 40 × 32 one. The constants depend
  only on low modes, so they are stable under refinement.

```
python run.py --work W --results X --tori A --N 40 --M 32        # 55 s, laptop
python kam_constants.py --work W [--tag C] [--gamma 0.3646] [--russmann exact]
```

#### 3.2 Results, torus A (`δ₀ = r/7`, Rüssmann constant `1/(eγδ)` with `γ = 0.1193`, as in Lean today)

| r | `sD` | `sW` | `tT` | `τ` | `cK` | `cL` | `κ` | `e₀` needed (margin 1) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0.030 | 4.08 | 1665 | 1987 | 14.06 | 2.1e5 | 7.9e6 | 1.1e14 | 9.7e-26 |
| 0.045 | 4.15 | 1706 | 2165 | 14.06 | 2.9e5 | 1.2e7 | 2.3e14 | 2.3e-25 |
| 0.063 | 4.23 | 1759 | 2404 | 14.06 | 4.1e5 | 1.8e7 | 5.8e14 | 3.5e-25 |
| 0.080 | 4.31 | 1818 | 2669 | 14.06 | 6.0e5 | 2.9e7 | 1.5e15 | 3.7e-25 |
| 0.100 | 4.42 | 1897 | 3036 | 14.06 | 9.4e5 | 5.0e7 | 4.5e15 | 2.9e-25 |

**Comparison with the rational torus A.** There `κ = 5.7e9` and `e₀ ≤ 5.8e-22`; for the
Dommaschk torus `κ` is about 10⁵ times larger.
- **Why.** The Dommaschk torus is small (minor radius ≈ 0.035, against 0.13), so
  `W₀ ~ r²` is small (`sW ≈ 1.7e3`, against 71).
- **The torsion oscillates.** It ranges over ±600 about the mean 14 (`tT/τ ≈ 170`, against 90).
  This oscillation is intrinsic to the rotating elongated QA cross-section in any of the frames
  tried.
- **Twist is not the problem.** The oracle's large relative ELP-S twist (+0.147) appears as
  `⟨T₀⟩ = 14`, but `cK` and `cL` scale with `tT/τ`, not with `τ` alone.
- **Dominant terms.** `κ ≈ C₂ ≈ cK·cL·(D̂_u + D̂_z)`. With sharp `‖∂D‖` (7.6) instead of the
  majorant (48.5), `κ` would drop about 6×.

#### 3.3 The Rüssmann constant decides the mode count

- **Today's estimate.** `Cohomological.cohSol_estimate` uses
  `sup_k |k| e^{−δ|k|}/γ ≤ 1/(eγδ)` with `γ = 0.1193`.
- **Where that is loose.** `γ` is attained at `k = 1` (`|ω| = 0.119`), where the exact factor is
  `e^{−δ}/0.119 ≈ 8.4`, not `1/(eγδ) ≈ 480`. For `|k| ≥ 2`, `γ₂ = 0.3646`.
- **The FHL Lemma 4.3 variant.** Treat the finitely many low divisors exactly and use `γ₂`
  otherwise. This gives `γ_eff = min(γ₂, 1/(eδ₀L))`, where `L` is the largest exact low-mode
  factor; here that is `γ₂ = 0.3646`.
- **Effect.** This lowers `κ` about 80×. With the full sup
  `sup e^{−δ(|k|+|m|)}/|m + kω|`, it is about 300×.

| r | `κ` (`γ₂`) | `e₀` needed (`γ₂`) | `κ` (exact sup) | `e₀` needed (exact sup) |
| --- | --- | --- | --- | --- |
| 0.045 | 2.8e12 | 1.9e-23 | 7.3e11 | 7.3e-23 |
| 0.063 | 7.2e12 | 2.8e-23 | 2.1e12 | 9.8e-23 |
| 0.080 | 1.8e13 | 2.9e-23 | 5.3e12 | 1.0e-22 |

**Torus C** (`ι = −(85+√5)/361`, r ≈ 0.027): at `r = 0.045`, `κ = 3.0e13` (crude) or `1.3e12`
(`γ₂ = 0.267`), so `e₀` needed is 1.8e-24 or 4.1e-23. That is about 2× **easier** than A, if its
asymptotic Fourier decay matches A's: 0.75 against 0.73 per θ-mode at 48 × 40 (N-31 §25). The
choice between A and C should be made on the 80 × 64 workstation runs.

#### 3.4 Modes needed

**The error model** is extrapolated from N-31 §25 and README:
- sup residual `≈ 1e-19 · 10^{−0.24(N−64)}` for `M ≈ 0.8N`;
- weighted norm `≈ 3 · sup · e^{rN}`, the mass sitting at the truncation edge (asymptotic θ-decay
  0.65 per mode).

| N × M | sup (extrap.) | weighted, r = 0.045 | margin (crude γ) | margin (`γ₂`) |
| --- | --- | --- | --- | --- |
| 80 × 64 | 1.4e-23 | 1.5e-21 | 1.5e-4 | 0.013 |
| 88 × 70 | 1.6e-25 | 2.5e-23 | 0.009 | 0.8 |
| 96 × 80 | 2.1e-27 | 4.7e-25 | 0.5 | 40 |
| 104 × 84 | 2.5e-29 | 8e-27 | 29 | 2400 |
| 112 × 90 | 3.0e-31 | 1.4e-28 | 1600 | 1e5 |

**Verdict on modes.**
- The README's 80 × 64 is **not** enough under the Lean constants.
- **Plan for 104 × 84 with the `γ₂` Rüssmann constant** (margin about 10²–10³, robust to a 10×
  error in the extrapolation), or for 112 × 90 without it.
- Coefficients need about 128 bits: rounding contributes about 3e-30.
- **The strip.** The optimum strip is `r ≈ 0.045`: the needed `e₀` is nearly flat in `r` while
  the edge weighting `e^{rN}` grows. The limit strip is `r/7`.

### 4. Certifying the invariance error within the budget (question 2)

#### 4.1 The exact Kronecker route (`KamTorusA`) is infeasible

- **Size.** The residual has degree 17 in the torus series. For 104 × 84 its exact image has
  about `(34·104)(34·84) ≈ 1.0e7` slots of about `17·128 + 30 ≈ 2200` bits, about 2.2e10 bits
  (2.8 GB) for one integer. At 80 × 64 it is still 1.2e10 bits.
- **Memory.** By the measured memory law (§4.3) this is far beyond 6 GB.
- **Comparison.** `KamTorusA`'s residual images are `2^17 · 656 ≈ 86` Mbit; its weighted
  Kronecker module `KamTorusAWeightedCheck` takes 84–93 s CPU and 5.5 GB, with a 127 MB olean.

#### 4.2 Recommended architecture: a KronBall chain (the GC pattern), one product per node

- **Inputs.** The exact torus centres `R`, `z` (packed rows, `2^-128`). `∂_θ`, `∂_ψ`, `𝓛`
  (`dS_ctr_grid`) and `ι_q∂_θ` are exact with radius 0. The trigonometric coefficients
  `c_ij(ψ)` of `D, Ps, Pz` are exact polynomials in the variables `cos 2φ, sin 2φ` of the
  environment.
- **Nodes.** Each node has tree degree 2 in the large grids: products plus linear combinations
  with exact small trigonometric factors. Every node rounds to `2^-S`, `S ≈ 128`, and truncates
  to an intermediate box `(N+8) × (M+6)`. The exact remainder, truncation tail and rounding
  together, is the radius, read from one Kronecker image (`node_full`, `kron2_proof`). So no
  analytic tail estimates are needed.
- **Why a larger box.** Intermediate quantities decay like the torus, so a box the size of the
  torus would drop tails of the order of the residual itself.
- **The chain:**
  1. `s = R·R` (1 node);
  2. `u_s = s − s₀` is folded into the next nodes;
  3. `z², z³, z⁴, z⁵` (4 nodes);
  4. Horner in `u_s`, `h_i = h_{i+1}·u_s + Σ_j c_ij(ψ) z^j`, for `D`, `Ps`, `Pz` (3 × 8 = 24
     nodes);
  5. the residuals `D·𝓛R − 2R·Ps` and `D·𝓛z − s·Pz` (2 nodes, **not truncated**: their weighted
     norms are read exactly);
  6. the `ι − ι_q` correction as in `KamTorusAWeighted`.

  In total about **31–40 product nodes**, against about 60 (heavier) nodes for GC high
  resolution.
- **Error budget.** The rounding radius per node is
  `2^-128 · Σ_box e^{r(|k|+|m|)} ≈ 3e-39 · (2e^{rN}/r)(2e^{rM}/r) ≈ 1e-32` at `r = 0.045`.
  Over about 40 nodes, with Horner gain `‖u_s‖ ≈ 0.3 < 1`, this stays ≤ 1e-30, against the
  target `e₀ ≈ 1e-26`.
- **Admissibility: a low-resolution chain about 24 × 20.** About 120–150 nodes, images
  ≤ 5 Mbit. It covers:
  - `D, ∂D, n, ∂n`;
  - `W₀` with the moving centre;
  - `q_D`, `q_W` and `q ≈ 1/(D³W₀²)`;
  - the torsion `Y = R^7 P q`, `X = qD³W₀² − 1`, with `τ' ≥ Re⟨Y⟩ − ‖Y‖‖X‖/(1 − ‖X‖)`.

  It is the GC `AdmL` pattern. The low-resolution torus must be about 1e-8 close to `K₀`.
  `C₂` comes from `PolyExpr.majD2` by `eval_cert` (the `…Maj` pattern).

#### 4.3 Prototype measurement of the critical cost (`Design/DommaschkKamProto.lean`)

**The kernel cost of one node** is dominated by two steps:
- the Kronecker image of a product of two centres;
- the weighted digit reading of that image (`kron2_proof`, the `pdig` divide and conquer).

The prototype states exactly this step, `wl1KronP b W dc dr R wA wB (A * B) ≤ Kb`, with strip
weights `kwtS 74315 16`, for two dense `N × M` grids. Each was measured as its own file
(`lake env lean`, `/usr/bin/time -l`, laptop, one process; the imports alone take about 1.6 s
and 1.5 GB):

| grids N × M | coeff bits | b | product image | user CPU | peak RSS |
| --- | --- | --- | --- | --- | --- |
| 40 × 30 (GC size) | 101 | 219 | 4.3 Mbit | 1.9 s | 1.73 GB |
| 64 × 52 | 110 | 238 | 12.8 Mbit | 3.6 s | 2.23 GB |
| 72 × 60 | 110 | 239 | 16.6 Mbit | 4.5 s | 2.47 GB |
| 80 × 64 | 120 | 259 | 21.4 Mbit | 5.4 s | 2.74 GB |
| 92 × 76 | 128 | 275 | 30.9 Mbit | 7.2 s | 3.19 GB |
| **104 × 88** | **130** | **280** | **41.2 Mbit** | **8.8 s** | **3.72 GB** |
| 128 × 104 | 136 | 292 | 62.5 Mbit | 13.1 s | 4.79 GB |

**The library file** holds the 40 × 30 and 104 × 88 checks and a rejected fixture: 9.7 s user,
13.7 s wall, 3.75 GB, no warnings, axioms `[propext]`.

**Cost law.** Peak ≈ 1.5 GB + 54 MB per Mbit of image; time ≈ 0.2 s per Mbit for the core step.
- So a node fits in 6 GB if its image is ≲ 80 Mbit.
- This agrees with GC: its CheckH peaks of 5.5 GB correspond to tree images of about 70 Mbit,
  with degree-4–6 trees at 40 × 30.

**Kernel limit found.** The kernel refuses `Nat.pow` results above `2^25` bits
(`LEAN_NAT_MAX_SIZE`), but not products, shifts or `land`.
- Every image above 4 MB must therefore be built with `<<<`. `offs`, `rowOffs` and `pdig`
  already are; a new emitter must not use `2 ^ (b*n)` for large exponents.
- Raising the environment variable instead would change the build environment and is not
  recommended.

#### 4.4 Estimates for the full certificate (104 × 84 torus, intermediates about 112 × 90, S = 128)

| component | count | per unit | total CPU | peak |
| --- | --- | --- | --- | --- |
| residual check nodes (images about 45 Mbit; core 9 s, with the GC overhead for tree images, data unpacking and norms 2–4×) | 35–40 | 20–40 s | 15–25 min | 4.0–4.8 GB |
| residual data (rounded centres: about 18.9k coefficients × 130 bits ≈ 0.75 MB decimal per grid) | 35–40 grids → 26–30 modules of about 1 MB | 6–10 s | 3–5 min | ≤ 1.5 GB |
| node identities (`RelH`, `ring` pointwise) | 1–2 modules | | 5–15 min | ≤ 4 GB |
| env/trees/chain/out | 5 | | 3 min | ≤ 2.5 GB |
| low-res admissibility chain (24 × 20, images ≤ 5 Mbit) | 120–150 nodes, 6–8 check modules | | 10–20 min | ≤ 3 GB |
| `Maj` (`C₂`), `Adm`, `Exact`, `Real`, Diophantine | 5 | | 3–5 min | ≤ 2.5 GB |
| field identification (sliced normal forms) | 3–5 | | 5–10 min | ≤ 3.5 GB |
| **total (on-demand top module)** | about 90 modules | | **≈ 45–85 CPU-min** | **≤ 5 GB** |

This is within the on-demand budget of 240 CPU-min. It is about 2–3× the GC torus (35 min), and
comparable to the GC energy window (70 CPU-min, 343 modules).
- **Source and olean.** About 30 MB of data source; the private oleans, at roughly twice that,
  stay well inside the 40 GB olean budget.
- **Node-level risk.** If a node's overhead pushes it above 5.5 GB, split the node by ψ-halves
  of one factor (`‖P − Q‖ ≤ ‖A₁B − Q₁‖ + ‖A₂B − Q₂‖`): twice the nodes, half the image.
- **Alternatives considered:**
  - *Sampling plus aliasing*, as in `CoilKam` with `StripPaleyWiener`: separable exact DFTs on
    about 240 × 200 points cost about 3e7 big-integer operations in `kernel_fact` leaves. That
    is costlier per coefficient than GMP products of packed images, so it is a fallback only.
  - *Exact Kronecker*: infeasible (§4.1).
  - *In-kernel rounding* of centres by masks (`land`/shift on the offset image) would remove the
    30 MB of centre data, but each check would recompute the chain prefix (O(n²) work). Use it
    only as checkpoints, if data size matters.

### 5. Surrogates and trade-offs (question 3)

- **Surrogate torus (the `KamTorusASurrogate` / GC low-resolution pattern): yes, for
  admissibility.** Frame, inverses, torsion and twist are computed on a low-mode torus `K_S`
  (about 24 × 20) whose balls contain every `μ`-close torus. This is what makes the twist cheap
  despite `tT/τ ≈ 170`.
- **Surrogate field: no.** C1 is about `field candidate` itself, and KAM needs the exact field (a
  Taylor remainder breaks exact convergence; `after-kam.md` §2.4).
  - A simpler nearby field is a new candidate, with its own step 1.
  - Reducing the polynomial degree (degree 17 against, say, 11) would save only about 30% of
    the nodes. The node count is not the bottleneck; the precision (modes) is.
- **Fewer modes with a weaker bound: no free trade.**
  - The smallness `32κe₀/δ₀⁴ ≤ 1` fixes `e₀`.
  - The strip optimum is flat (`r ≈ 0.045–0.08`).
  - The decay rate of about 0.65 per θ-mode is set by the 6/25 resonance (margin 0.0014), so it
  is intrinsic to A.
- **The lever is `κ`.** Each factor of 10 in `κ` saves about 4 θ-modes and about 30% of the
  certificate size. In order of value:
  1. the exact low divisors in the Rüssmann constant (×80, §3.3);
  2. approximate inverses for `D` and `W₀` instead of Neumann (×4–16);
  3. a sharper `C₂` from ball bounds of second derivatives at all `μ`-close tori instead of
     polynomial majorants (×≤6; needs a variant of `StepH.hC2R`);
  4. choosing torus C if its decay holds (×2).
- **Not useful.** The curve-normal frame is worse (`tT` 10× larger), and a fixed centre is
  impossible (O1).

### 6. Module plan (question 4)

All modules are new; none is imported by `PlasmaLean.lean`. The order is the dependency order.
"WS" marks a first build on the workstation.

| # | Module(s) | Content | Where |
| --- | --- | --- | --- |
| 0 | — (numerics) | Workstation runs of A and C at 80 × 64 and 96 × 80, dps 50. Then `kam_constants.py` with the measured decay, to choose the torus and `N × M`. **New oracle code:** a low-memory multiprecision refinement at ≥ 104 × 84 (frozen 64 × 52 Jacobian plus a diagonal for the high modes; the dense Jacobian would be about 20 GB) | WS |
| 1 | `Theory/Contract` change (coordinator) | `PoloidalAngle` about a periodic reference curve, the constant special case, an independence-of-reference sanity theorem, `IotaOnTorus.tendsto` | laptop, audit lane |
| 2 | `Theory/KAM/CohomologicalLow` | `cohSol_estimate_low`: Rüssmann constant with the divisors `|k| < K` exact and `γ_K` beyond; the Diophantine-for-`|k| ≥ K` predicate | laptop, light |
| 3 | `Design/KamFlowFieldG`, `KamFlowFrameG`, `KamFlowStepG`, `KamFlowIterationG` | `FlowFieldG`: `R = R₀ + u`, exponent `k`, moving frame centre `A(φ)` (polynomials in `c, s`), the Rüssmann constant as a parameter. Copies of the `KamFlow*` proofs (about 3,500 lines, as the `S` variant). **Sanity:** `field14` as an instance (`R₀ = 1`, `k = 3`, `A = 0`) | laptop, light (5–10 s each, as `KamFlow*S`) |
| 4 | `Design/DommaschkKamDio` | `Diophantine (ι_A/2) 0.1193 1` and the `|k| ≥ 2` constant 0.3646 (`DiophantineB` pattern) | laptop |
| 5 | `Design/DommaschkKamField`, `…FieldCheck0–k` | `dkField : FlowFieldG`: `D, n_R, n_z, P_a, P_b, P` in `(u, z, c, s)` with `u = R − R₀`; `divFree` and `flux_*` by sliced normal forms; identification with `field candidate` at real points; emitter `scripts/dommaschk_kam/emit_field.py` | laptop (≤ 3.5 GB each) |
| 6 | `Design/DommaschkKamAData` (2 modules) | the torus (packed rows, `2^-128`, the Lean phase convention `ψ_L = 2φ − π/2`), `ι_q` | WS, then laptop |
| 7 | `Design/DommaschkKamEnvH`, `TreesH`, `DataH1–30`, `CheckH1–40`, `RelH`, `ChainH`, `OutH` | the residual chain (§4.2): `Bd r_A (resR/Z(K₀)) e₀` | **WS** first build; laptop spot-check |
| 8 | `Design/DommaschkKamEnvL`, `TreesL`, `DataL1–4`, `CheckL1–8`, `RelL`, `ChainL`, `OutL`, `AdmL` | low-resolution chain: all `AdmBounds` at every `μ`-close torus | WS, then laptop |
| 9 | `Design/DommaschkKamMaj`, `DommaschkKamAdm`, `DommaschkKamExact` | `C₂`; `cDK : SC`; `dk_exact_torus` from `FlowFieldG.KamH.kam_flow_torus` | laptop |
| 10 | `Design/DommaschkKamReal`, `DommaschkKamContract` | the real `C²` torus (GC `Real` pattern), `FieldTorus` from `D𝓛K = n` and `D > 0`, `PoloidalAngle` about `A(φ)` from `W₀ < 0`; **`dommaschk_C1`** via `candidate_currentFreeTransform` with `ι_min = 0.2386` | laptop |
| top | `Design/DommaschkKamCert` | on-demand top module; `scripts/check_axioms_heavy.lean` | WS, then laptop |

Generators (untrusted; each must validate every emitted bound in exact rationals before writing
Lean):
- `scripts/dommaschk_kam/emit_field.py`;
- `refine_hr.py`, the high-resolution oracle;
- `ballcert.py` and `emit_lean.py`, ports of `scripts/gc_kam/`;
- `kam_constants.py`, present.

### 7. Open gaps

1. **(O3) Contract.** `PoloidalAngle` about a fixed circle cannot hold for any surface of this
   field. This is a definitional change in `Theory/Contract` and needs the audit lane. **It
   blocks C1 even with a certified torus.**
2. **(O1)/(O2) KAM interface.** A moving frame centre, `R = R₀ + u` and the density exponent
   `k`. This is new Lean, but the mathematics is the existing frame algebra with the extra term
   `A'` in `𝓛V₀`.
3. **The Rüssmann constant with exact low divisors** (FHL Lemma 4.3). Not in
   `Theory/KAM/Cohomological`. It is small, and it decides 80 × 64-class against 112 × 90-class
   certificates.
4. **(Optional) A sharper Taylor constant.** `StepH` takes `C₂` only as a `PolyExpr.majD2`
   bound. A variant taking ball bounds of second derivatives at all `μ`-close tori would gain up
   to ×6 in `κ`.
5. **Field identification and flux primitive for the Dommaschk potential.** Routine; checked on
   the data to be log-free and `dφ`-free (§2.4).
6. **The oracle at ≥ 104 × 84 and 128 bits with bounded memory**, and the emitter: the Lean phase
   convention and stellarator symmetry about `φ = 0` instead of `φ = π/4`. Untrusted code.
7. **Nothing else.** In particular there is no log enclosure, no inverse-square-root node, no
   Paley–Wiener sampling and no new analytic theorem.

### 8. Go/no-go and risks

**Verdict: conditional GO.**
- **The certificate fits the budget.** Single nodes at the needed size cost about 9 s and
  3.7 GB in the core step (measured). The full certificate is estimated at 45–85 CPU-min with a
  peak ≤ 5 GB, as an on-demand top module, first built on the workstation.
- **No new analysis is needed.**
- **Condition: two decisions must come first.**
  1. The contract change (O3). Without it no torus of this field can satisfy C1.
  2. The mode count, confirmed by the 80 × 64 and 96 × 80 workstation runs and
     `kam_constants.py`.

**Risks, in order:**
1. **The contract change is not accepted.** C1 is then unreachable for every non-planar-axis
   candidate whose axis excursion exceeds the minor radius. This is a property of the
   definition, not of the field.
2. **The `κ` and mode-count extrapolation.** The required `e₀` (1e-23 to 3e-25) is certain to a
   factor of about 3, since the estimator is validated against torus A. The decay extrapolation
   is weaker: one mode is worth about ×1.8. Without the `γ₂` improvement the certificate needs
   about 112 × 90.
3. **Per-node memory of 4–5 GB.** The fallback is splitting by ψ-halves.
4. **The effort of the interface generalisation**, gap 2: about 1–2 agent-weeks.
5. **The high-resolution oracle**: memory, and multiprecision time at 104 × 84 × degree 17.
6. **Data volume**: about 30 MB of Lean source.

**Total effort:** about 3–5 agent-weeks. Steps 1–5 on the laptop: 1.5–2.5 weeks. Steps 6–10:
1.5–2.5 weeks, plus workstation time.

## Claims and evidence

1. **Numerical observation (untrusted, `kam_constants.py`).**
   - The frame vector `V₀ = (R − 1, z)` of `FlowField` has a sign-changing winding form on
     Dommaschk torus A.
   - A frame about a 4-harmonic axis approximation has `W₀ ∈ [−1.13e-3, −7.5e-4]`.
   - No fixed point lies inside all cross-sections (at most 73 of 256).
2. **Complete mathematical argument (short).** The flux primitive of the target exists as a
   Laurent polynomial without `dφ`-component: the only axisymmetric term of `V` is `c·z`, read
   off the exact data.
3. **Numerical observation (untrusted).**
   - The generalised `SC` constants of torus A are `κ ≈ 2.3e14` at `r = 0.045` with today's
     Rüssmann constant, and `2.8e12` with exact low divisors.
   - The required `e₀` is 2.3e-25 and 1.9e-23 respectively.
   - The estimator reproduces the certified `cK` of the rational torus A (10 748.5 against
     `≤ 10 800`).
4. **Compiled Lean (on demand, not imported).** `DommaschkKamProto.protoBig` and `protoSmall`:
   the weighted digit-sum bound of the product image of two 104 × 88 (resp. 40 × 30) grids, by
   `kron2_proof`. Axioms `[propext]`. Costs as in §4.3.
5. **Observation (Lean kernel).** The kernel refuses `Nat.pow` results above `2^25` bits but
   evaluates larger products and shifts (41–62 Mbit images measured).

## Difficulty, barriers and readiness

- **Difficulty.** Engineering-heavy, mathematically routine, except the contract question.
- **The main barriers:**
  - (O3), a definition;
  - the precision demanded by `κ ≈ 1e12`–`1e14`, set by a small torus with strongly
    oscillating torsion;
  - the size of the KronBall chain at about 104 × 84.
- **Lean-ready now:**
  - gap 3 (`CohomologicalLow`);
  - the `FlowFieldG` generalisation (gap 2);
  - the Diophantine instance;
  - the field identification (gap 5).
- **Not ready.** The residual chain waits for the high-resolution oracle (step 0).

**Smallest next step:** the workstation runs at 80 × 64 for A and C, then `kam_constants.py` on
them. In parallel, the coordinator decides on (O3).

## Outputs and next dependencies

**Files:**
- this note;
- `scripts/dommaschk_kam/kam_constants.py` (new, untrusted);
- `PlasmaLean/Design/DommaschkKamProto.lean` (new, on demand, prototype).

**Suggested registry updates** (for the coordinator):
- **N-33 row.** Design of the step-2 certificate; conditional go; depends on N-31.
- **Q-16.** "Step 2 designed (N-33). Blocked on the contract poloidal-angle definition (O3) and
  on the 80 × 64 oracle runs."
- **New audit item.** `PoloidalAngle` requires a fixed reference circle. That is unsatisfiable
  for tori around a non-planar axis whose excursion exceeds the minor radius, including every
  surface of the Dommaschk target. Proposed fix in §2.2 (O3). The `DommaschkQA2R` docstring
  claim "C1 reduces to certified tori" should carry this caveat.
- **New ready notes or tasks:**
  - `CohomologicalLow` (gap 3);
  - `FlowFieldG` (gap 2);
  - the Dommaschk Diophantine instance;
  - the field identification;
  - the high-resolution oracle (workstation task `dommaschk-kam`, extended with 96 × 80 and the
    refinement of §6 step 0).
- **Edge.** N-31 → N-33 → Q-16 / C1.

## Update (31 October 2026): O3 resolved

The contract now measures the poloidal angle about a continuous 2π-periodic reference curve
(`PoloidalAngle R z R₀ z₀ Θ` with `R₀ z₀ : ℝ → ℝ`; `poloidalAngle_const_iff` recovers the fixed
circle). The tokamak exclusion `iota_eq_zero_of_purelyToroidal` is re-proved, and there are new
fixtures: the wandering torus `Sanity.AuditRefresh.wander_poloidalAngle` /
`wander_not_poloidalAngle_const`, and `twistTorus_not_iotaOnTorus`. The blocker of §2.2 (O3) is
gone. The torus certificate must supply a reference curve inside each cross-section, e.g. the axis
approximation A(φ) of (O1).

