# Residual-based invariant neighbourhoods and the norm-to-observable step

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-39` |
| Title | Additive-residual comparison, inward radii and the norm-to-observable step (method note for N-19) |
| Kind | method (research approach; lean-ready scalar part) |
| Addresses | `G-7`, `Q-27` (new); supports `Q-7`, `Q-9`, `Q-11`, `G-2` |
| Depends on | N-19 §2.3 (Pizzocchero–Tassi supersolution, gates E2–E3), §3.2 (yield target); N-36 (claims 19, 20, 44–46); Lean: `Theory/Stability/RiccatiComparison` (`riccati_le_initial`, `riccati_exp_decay`) |
| Dependency requirement | compiled: `riccati_le_initial` (the comparison pattern); Mathlib `image_le_of_deriv_right_le_deriv_boundary` |
| Produces | Q-27 (a)–(c) statements and Lean targets |
| Difficulty | routine (a); moderate (b); research (c, the PDE producer) |
| Status | stated; (a) lean-ready |
| Lean evidence | none yet |
| Audit evidence | not audited |
| Last updated | 4 November 2026: created from N-36 |
| Patched by / Alternatives | method for N-19 (its plan and compiled parts stand) |

## Purpose and scope

N-19 §2.3 fixes the first evolution target. A smooth approximate trajectory with a certified
continuum residual and a scalar supersolution R′ ≥ −μR + (…)R + ĜR² + ϵ_s certifies existence and
an error bound. The compiled comparison `riccati_le_initial` covers only Y′ ≤ −νY + CεY², with a
multiplicative small parameter and **no additive residual**, and only for a monotone bound.

The kinetic/coil brief (N-36, §10) states the same architecture for a general model:
D⁺‖e‖ ≤ a‖e‖ + b‖e‖² + ϵ. It adds two things this note records as method:
1. **An inward-radius criterion** for the all-time variant D⁺r ≤ −λr + Lr² + ϵ. For L > 0, any
   r* > 0 with −λr* + Lr*² + ϵ ≤ 0 is inward-pointing. Such r* exist iff λ² ≥ 4Lϵ, with the best
   radius at r = λ/(2L) and the smallest at r₋ = (λ − √(λ² − 4Lϵ))/(2L) (exact check: N-36, checks
   9–10).
2. **The norm-to-observable step.** A stability theorem certifies a burn only if its norm controls
   the operating observables with margins. Example: reference core temperature ≥ T_burn + ΔT and
   error ≤ ΔT give T ≥ T_burn. For kinetic states, the weighted norm
   sup_x ‖⟨v⟩^ℓ(f − f̂)‖_{L²_v} with ℓ > 9/2 controls the moments up to order 3, hence n, u, T (given
   n ≥ n_min) and the energy flux (N-36, claims 19–20).

## Theory development

**(a) Scalar inward-radius lemma (lean-ready).**
- Let Y ≥ 0 be continuous on [0, T] with right derivative Y′ ≤ −λY + LY² + ϵ(t) on [0, T), where
  λ > 0, L ≥ 0 and 0 ≤ ϵ(t) ≤ ϵ.
- Suppose r* > 0 satisfies −λr* + Lr*² + ϵ < 0, and Y(0) ≤ r*.
- Then Y(t) ≤ r* on [0, T].
- With the non-strict inequality (≤ 0), the conclusion holds by approximation: a fence at every
  r > r* close to r*, as in `riccati_le_initial`.
- Companion: `exists_inward_radius_iff`: ∃ r > 0, −λr + Lr² + ϵ ≤ 0 ↔ λ² ≥ 4Lϵ (L > 0, λ > 0,
  ϵ ≥ 0).
- Lean module: `Theory/Evolution/ControlInequality.lean`, the module N-19 §2.3 already names.
  Declarations: `le_inward_radius`, `exists_inward_radius_iff`.

**(b) Finite-horizon variant with time-dependent coefficients.**
- D⁺Y ≤ a(t)Y + b(t)Y² + ϵ(t) with certified continuous a, b, ϵ ≥ 0.
- A supersolution R with R(0) ≥ Y(0) bounds Y on the horizon of R. Certifying R on [0, τ + δ] gives
  the closed interval [0, τ].
- This generalises `riccati_le_initial` and is exactly the scalar part of N-19 §2.3. It is
  routine, except that the upper Dini derivative of a norm at its zeros needs care. N-19 §2.3
  already flags this.

**(c) The producer (research).** Derive the inequality for a stated PDE, norm and admissible set.
- For the periodic incompressible MHD benchmark this is Pizzocchero–Tassi (Q-7).
- For kinetic models it is open (Q-28).
- The brief stresses, as N-19 does, two cautions: the residual must be a continuum residual, and a
  sum of residuals of uncoupled models is not a residual of the coupled evolution.

**Norm-to-observable lemmas (part of Q-27).**
- `moment_le_of_weighted_L2`: |∫|v|^k g| ≤ C(k, ℓ)‖⟨v⟩^ℓ g‖₂ for 2(ℓ − k) > 3.
- `temperature_lipschitz_of_moments`: T is Lipschitz in (n, nu, K) on {n ≥ n_min}, with an explicit
  constant.
- These turn an invariant neighbourhood into a temperature band. Composed with Q-26 (c), they give
  a yield bound.

## Claims and evidence

- (a): complete mathematical proof (elementary; the algebra re-derived exactly in N-36); not yet in
  Lean.
- (b): complete mathematical proof modulo the Dini-derivative detail; not in Lean.
- Moment lemmas: complete mathematical proofs (Cauchy–Schwarz and the integrability of ⟨v⟩^{−2s},
  s > 3/2, in ℝ³); not in Lean.
- (c): open (Q-7 for the benchmark, Q-28 for kinetic models).

## Difficulty, barriers and readiness

(a) is lean-ready and light. The moment lemmas need the integrability of ⟨v⟩^{−2s} on ℝ³ in
Mathlib, which is available through `integrable_one_add_norm` (check the name before use).
Smallest next step: `le_inward_radius` and `exists_inward_radius_iff`.

## Outputs and next dependencies

Q-27. Ready afterwards: the scalar part of gate E3 (N-19), and a norm-to-temperature corollary for
any future invariant-neighbourhood theorem.
