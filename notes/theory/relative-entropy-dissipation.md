# Relative-entropy dissipation for the heat equation with fixed n, T*

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-2` |
| Title | Corrected relative-entropy identity for heat transport with fixed n, T* |
| Kind | proof / counterexample / formalization |
| Addresses | `G-2`, `G-7`, `Q-10`; track T3, gate E6 (plan §1.5, §11) |
| Depends on | none (self-contained calculus); Mathlib FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) |
| Dependency requirement | supplied classical solutions (`HasDerivAt` data); no existence theorem used |
| Produces | the 1-D pointwise and integrated identity, the case 1 and case 2 sign theorems, the counterexample to the BKM §3.1 identity |
| Difficulty | moderate (bookkeeping of cross and boundary terms; 2-D/3-D needs divergence-theorem infrastructure) |
| Status | verified (1-D pointwise and integrated identity, cases 1–2, counterexample; 1-D equality case, coercivity H ≤ C𝓕 and conditional exponential decay); 2-D/3-D and the justification of `dH/dt` (differentiation under the integral) open |
| Lean evidence | default build: `PlasmaLean.Theory.Transport.RelativeEntropy` (`hasDerivAt_relEntDensity_time`, `relEnt_flux_identity`, `relEnt_flux_identity_unintegrated`, `relEnt_pointwise_identity`, `RelEntSetup.integral_identity`, `RelEntSetup.rate_eq`, `RelEntSetup.rate_le_neg_fisher_const_ref`, `RelEntSetup.rate_le_neg_fisher_steady`, `cexSetup_fisher_pos`, `cexSetup_cross_eq_fisher`, `old_identity_false`, `old_rate_identity_false`); sanity: `PlasmaLean.Sanity.RelativeEntropy` (`setup_self`, `const_ref_identity`, `constRef_rate`, `reaction_sign_fails_increasing`); coercivity: `PlasmaLean.Theory.Transport.RelativeEntropyCoercive` (`RelEntSetup.ratio_eq_of_fisher_eq_zero`, `RelEntSetup.exists_const_of_fisher_eq_zero`, `phi_le_half_mul_sq_log`, `sq_integral_le`, `RelEntSetup.sq_log_ratio_le`, `RelEntSetup.relEnt_le_mul_fisher`, `exp_decay_of_deriv_le_neg_fisher`, `RelEntSetup.relEnt_exp_decay`, `RelEntSetup.relEnt_exp_decay_const_ref`, sanity `constSetup_one_equality`, `sq_integral_const`, `constSetup_two_other_hyps`, `no_coercivity_without_boundary`); standard axioms only |
| Audit evidence | audit confirmed the corrected identity (cross term, boundary terms, Q not ΔQ); Lean module not audited |
| Last updated | 2026-10-30: 1-D identity, integrated form, sign theorems and counterexample formalized; coercivity step (equality case, H ≤ C𝓕, exponential decay) formalized |

**Lane:** A, Cycle 1 (track T3, implementation plan §1.5). **Date:** 2026-10-20.
**Checks:** `/tmp/lanea/relent.py`, `/tmp/lanea/cex.py` (sympy, outside the repo). All residuals are 0.
**Verdict:** the identity in `bkm-regularity-and-perelman-burn-bounds.md` §3.1 is **refuted** for non-constant
T* (exact counterexample below). The corrected identity and the regime where dissipation holds are stated here.
Status: **proved informally + symbolically checked**; 1-D version **[Lean]** (2026-10-30, see the metadata).

## Setting and hypotheses

* M ⊂ ℝ^d bounded with Lipschitz boundary and outward normal ν (or a radial interval; see the end).
* n(x) > 0, T*(x) > 0 fixed (time-independent) and C¹; χ(x) a symmetric, positive-semidefinite matrix field, C¹,
  **independent of T** (if χ depends on T the cross-term argument below fails).
* T(x,t) > 0 a classical solution (C^{2,1}) of n ∂_t T = ∇·(nχ∇T) + Q(x,T).
* H[T|T*] = ∫_M n T* φ(T/T*), with φ(s) = s − 1 − ln s ≥ 0, φ(1) = 0.

## Identity (exact)

Write s = T/T*. Then d/dt (nT*φ(s)) = n(1 − T*/T) ∂_tT, and pointwise (sympy-checked in 2-D with a full
symmetric χ):

(1 − T*/T) ∇·(nχ∇T) = − nT* ⟨∇ln s, χ∇ln s⟩ + ln s · ∇·(nχ∇T*) + ∇·[ (1 − T*/T) nχ∇T − ln s · nχ∇T* ].

Hence

**dH/dt = − 𝓕 + 𝓒 + 𝓡 + 𝓑**, where
* 𝓕 = ∫ nT* ⟨∇ln(T/T*), χ ∇ln(T/T*)⟩ ≥ 0 (Fisher-type information),
* 𝓒 = ∫ ln(T/T*) ∇·(nχ∇T*) (**cross term, no sign**),
* 𝓡 = ∫ (1 − T*/T) Q(x,T) (reaction; the note's "ΔQ" is a typo for Q),
* 𝓑 = ∮ [ (1 − T*/T) nχ∇T − ln(T/T*) nχ∇T* ]·ν.

Equivalent un-integrated form (also checked): (1−T*/T)∇·(nχ∇T) = −nT*⟨∇T,χ∇T⟩/T² + n⟨∇T*,χ∇T⟩/T + ∇·[(1−T*/T)nχ∇T].
So the dissipation is ∫ nT*|∇T|²_χ/T², and there is a cross term ∫ n⟨∇T*,χ∇T⟩/T. The note's claim (dH/dt = −𝓕 + reaction) is
exactly the claim 𝓒 + 𝓑 = 0.

## Counterexample to the note's version (exact)

M = [0,1], n = χ = 1, Q = 0, T* = 1 + x², and at some instant T = 1 + x. Then T = T* at x = 0, 1, so 𝓑 = 0.
True: dH/dt = ∫(1 − T*/T) T'' dx = 0 (T'' = 0). Note's formula: −𝓕 ≈ −0.2447 < 0. (𝓒 ≈ +0.2447.)

## When the negative-definite structure holds

The generalized relative entropy mechanism (cross-term = ∫ G(s) ∇·(nχ∇T*) with G' = sφ''(s) = 1/s) gives:

1. **T* constant**, Q = 0, and either Dirichlet T = T* or no-flux nχ∇T·ν = 0: dH/dt = −𝓕 ≤ 0. Equality holds iff T is
   constant on each component, where χ is positive definite.
2. **T* steady and Dirichlet-matched.** Suppose ∇·(nχ∇T*) + Q(x,T*) = 0 in M and T = T* on ∂M (then 𝓑 = 0). Then
   dH/dt = −𝓕 + ∫ [ (1 − 1/s − ln s) Q(x,T*) + (1 − 1/s)(Q(x,T) − Q(x,T*)) ].
   Since 1 − 1/s − ln s ≤ 0 (maximum 0 at s = 1) and 1 − 1/s has the sign of T − T*:
   **dH/dt ≤ −𝓕 ≤ 0 whenever Q(x,T*) ≥ 0 and T ↦ Q(x,T) is non-increasing** (fixed heating minus a monotone loss).
3. **Fails when ∂_TQ > 0** (alpha heating exceeding losses, i.e. the thermally unstable branch). The second reaction term
   can then be positive, and H can grow. This is exactly the physics of thermal runaway. So the Perelman-style claim
   that diffusion "strongly damps toward T*" holds only on the stable branch, and the stable branch is an extra hypothesis.
4. With non-matching boundary data, or a T* that is not steady, 𝓒 + 𝓑 is generally non-zero and of either sign.

Literature: this is an instance of the general relative entropy principle (Michel, Mischler & Perthame,
J. Math. Pures Appl. 84 (2005) 1235–1260) **[lead: standard reference, not re-checked here]**.

## Radial (flux-surface-averaged) version for `Kernel/Transport`

With M = [0,1] in ψ, measure V′(ψ)dψ, and n∂_tT = (1/V′)∂_ψ(V′ n D ∂_ψT) + Q (D = χ⟨|∇ψ|²⟩ > 0), the same identity
holds with ∇ → ∂_ψ and dV → V′dψ. The axis boundary term vanishes if V′(0) = 0 and the fluxes stay bounded (the
axis-regularity hypothesis). The edge term vanishes under matched Dirichlet data T(1) = T*(1).

## Lean targets

* **Now:** the pointwise 1-D identity as a `HasDerivAt`/`deriv` computation
  (`(1 - Ts/T) * (a*T')' = -a*Ts*((log(T/Ts))')^2 + log(T/Ts)*(a*Ts')' + (flux)'` for C² functions with T, Ts > 0),
  and the scalar lemma `1 - 1/s - log s ≤ 0`, together with the sign lemma for case 2.
* **Cycle 2:** integrate on [0,1] (FTC, `intervalIntegral`) to get `dH/dt ≤ -𝓕` under the hypotheses of case 2, plus the
  counterexample as a `decide`-free exact sanity theorem (T* = 1+x², T = 1+x).

## Lean status (2026-10-30)

Module `PlasmaLean/Theory/Transport/RelativeEntropy.lean` (namespace
`PlasmaLean.Transport.RelativeEntropy`, default build, standard axioms only, no `decide`):

* `hasDerivAt_relEntDensity_time`: ∂ₜ(nT*φ(T/T*)) = n(1 − T*/T)∂ₜT.
* `relEnt_flux_identity`: (1 − T*/T)F′ = −κT*(∂ₓ log(T/T*))² + log(T/T*)F*′ + ∂ₓ[(1 − T*/T)F − log(T/T*)F*]
  for F = κT′, F* = κT*′ (κ independent of T); `relEnt_flux_identity_unintegrated` is the second form above.
* `relEnt_pointwise_identity`: the space-time identity with n∂ₜT = F′ + Q (reaction (1 − T*/T)Q).
* `RelEntSetup` (supplied data on `uIcc a b`), `integral_identity` (∫(1 − T*/T)F′ = −𝓕 + 𝓒 + 𝓑) and
  `rate_eq` (∫ n(1 − T*/T)∂ₜT = −𝓕 + 𝓒 + 𝓡 + 𝓑), by the fundamental theorem of calculus for the flux.
* `rate_le_neg_fisher_const_ref` (case 1: T*′ = 0, Q = 0, matched Dirichlet or no-flux at each end: rate = −𝓕 ≤ 0)
  and `rate_le_neg_fisher_steady` (case 2: steady matched T*, Q(x,T*) ≥ 0, Q non-increasing in T: rate ≤ −𝓕 ≤ 0).
* `old_identity_false`, `old_rate_identity_false`: the counterexample T* = 1 + x², T = 1 + x on [0, 1];
  𝓒 = 𝓕 > 0 (`cexSetup_cross_eq_fisher`, `cexSetup_fisher_pos`), boundary term 0.

### Coercivity step (2026-10-30)

Module `PlasmaLean/Theory/Transport/RelativeEntropyCoercive.lean` (default build, standard axioms, no `decide`).
Write ℓ = log(T/T*), H = ∫ₐᵇ nT*φ(T/T*), 𝓕 = ∫ₐᵇ κT*(ℓ′)².

* **Equality case** (`RelEntSetup.ratio_eq_of_fisher_eq_zero`, `exists_const_of_fisher_eq_zero`): a < b,
  κ > 0 on [a, b], 𝓕 = 0 ⇒ T = cT* on [a, b] with c = T(a)/T*(a) > 0 (continuous nonnegative integrand
  with zero integral vanishes on (a, b); mean value theorem for ℓ).
* **Scalar bound** (`phi_le_half_mul_sq_log`): φ(s) ≤ (M/2)(log s)² for 0 < s ≤ M, M ≥ 1 (from
  eˣ − 1 − x ≤ x²/2 for x ≤ 0 and ≤ eˣx²/2 for x ≥ 0).
* **Wirtinger/Poincaré step** (`sq_integral_le`, `RelEntSetup.sq_log_ratio_le`): (∫ₐˣ g)² ≤ (x − a)∫ₐˣ g²;
  with T(a) = T*(a), ℓ(x)² ≤ (x − a)∫ₐᵇ(ℓ′)². Mathlib (pinned) has no 1-D Poincaré/Wirtinger inequality.
* **Coercivity** (`RelEntSetup.relEnt_le_mul_fisher`): if T(a) = T*(a), k₀ ≤ κT*, nT* ≤ N, T ≤ MT* on [a, b]
  (k₀ > 0, N ≥ 0, M ≥ 1), then **H ≤ C𝓕 with C = N M (b − a)²/(4k₀)**. The ratio bound T ≤ MT* is needed for
  a quadratic bound (φ(eˡ) grows exponentially); the constant (b − a)²/2 in the Poincaré step is not sharp
  (optimum 4(b − a)²/π² for one Dirichlet end).
* **Exponential decay** (`exp_decay_of_deriv_le_neg_fisher`, `RelEntSetup.relEnt_exp_decay`,
  `RelEntSetup.relEnt_exp_decay_const_ref`): dH/dt ≤ −𝓕 and H ≤ C𝓕 ⇒ H(t) ≤ H(0)e^{−t/C}, via
  `Stability.riccati_exp_decay` with no quadratic term. In the constant-reference version the rate
  ∫n(1 − T*/T)∂ₜT = −𝓕 comes from `rate_le_neg_fisher_const_ref`; the **hypothesis** that H has this right
  derivative (differentiation under the integral) and continuity of H in t remain assumptions.
* **Sanity**: `constSetup_one_equality` (T = T*: H = 0 = C·𝓕), `sq_integral_const` (equality in the
  Wirtinger step for constant g), `no_coercivity_without_boundary` with `constSetup_two_other_hyps`:
  T = 2T* constant has 𝓕 = 0 but H = 1 − log 2 > 0 and satisfies every hypothesis except T(a) = T*(a),
  so the endpoint condition is necessary.

Remaining: the 2-D/3-D identity (divergence theorem on a Lipschitz domain, matrix χ), the radial
version with the degenerate axis (V′(0) = 0) made explicit, dH/dt itself (differentiation under the
integral, discharging the decay hypothesis), the steady-reference (case 2) decay (H ≤ C𝓕 holds by the same
theorem, but needs a Dirichlet match and the uniform ratio bound along the flow, e.g. from a maximum principle),
a zero-mean (Neumann) variant of the Poincaré step, a sharp constant, and the case 3 failure as an integrated example.
