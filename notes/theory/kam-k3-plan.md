# K3: an explicit a posteriori KAM theorem for torus A (plan after stage K3a)

Status: plan. Stage K3a is compiled. Everything in §2–§4 is a proposal and is **not** a Lean theorem.
Input: `kam-route.md` §2.2–2.5 and §5 (FHL 2017 Thm 2.5 / Lemma 2.8; ELP-S 2025 Thm 6.2), K2
(`Design/KamTorusA*.lean`), the oracle (`scripts/kam_oracle/`).

## 1. What K3a proves (compiled, sorry-free, standard axioms)

`PlasmaLean/Theory/KAM/Diophantine.lean`
- `Diophantine ω γ τ :≡ ∀ k ≠ 0, ∀ m, γ/|k|^τ ≤ |kω − m|` (τ : ℕ). Basic API: `mono`, `add_int`, `neg`,
  `abs_divisor_ge` (|m + kω| ≥ γ/|k|^τ), `divisor_ne_zero`, `le_half` (γ ≤ 1/2), and
  `not_diophantine_of_rat`.
- `one_le_mul_conj`: for x = (a+√5)/b, x' = (a−√5)/b and g | (qa−pb)² − 5q² we have (b²/g)|qx−p||qx'−p| ≥ 1.
- `diophantine_one_of_conj`: the conjugate bound plus A(γ²/Q² + γ|x−x'|) ≤ 1 plus a check of |q| < Q gives
  `Diophantine x γ 1`.
- `goldenMean_diophantine : Diophantine ((1+√5)/2) ((3−√5)/2) 1`. This is the classical optimal constant.
- `torusA_rotation_diophantine : Diophantine ((75+√5)/562) (687/5000) 1`, so γ = 0.1374. The optimum is
  ι ≈ 0.137431, at k = 1. `torusA_not_diophantine_large` shows that 0.1375 fails.
- `torusA_period_diophantine : Diophantine (ι/2) (687/10000) 1`, so γ = 0.0687 (the oracle has 0.069).
  `torusA_divisor_ge` gives |2m + kι| ≥ 0.1374/|k|.

`PlasmaLean/Theory/KAM/Cohomological.lean`. Coefficients are `f : ℤ×ℤ → ℂ`, with mode (k,m) = e^{i(kθ+mψ)}. The
norm is `wnorm r f = Σ |f_km| e^{r(|k|+|m|)}`, with r = 2πρ for ρ in turns (the oracle's weight).
- `pow_mul_exp_neg_le`: x^τ e^{−δx} ≤ (τ/(eδ))^τ.
- `cohSol ω f = f_km / (i(m + kω))`. `cohSol_spec` shows it solves L_ω u = f (with L_ω = ∂_ψ + ω∂_θ), and
  `cohSol_unique` shows it is unique among zero-mean solutions.
- `cohSol_estimate`: ‖u‖_{r−δ} ≤ max(1, (τ/(eδ))^τ/γ)‖f‖_r. `cohSol_estimate_one` is the τ = 1 case:
  ‖u‖_{r−δ} ≤ ‖f‖_r/(eγδ) for δ ≤ 2/e.
- `dθ_estimate`, `dψ_estimate` (Cauchy): ‖∂u‖_{r−δ} ≤ (eδ)⁻¹‖u‖_r.
- `hasDerivAt_fourierSum_cohSol`: the Fourier series is a classical solution, ∂_ψU + ω∂_θU = F pointwise.
- Counterexamples: `no_solution_of_rat` and `divisor_lower_of_estimate` / `not_estimate_of_rat`. Any
  estimate forces |m + kω| ≥ e^{−δ(|k|+|m|)}/C, which is false for rational ω.

**How ι_q enters.** K2 bounds the residual `E_q` computed with the dyadic ι_q (|ι − ι_q| ≤ 10⁻²⁹). The KAM
iteration must use the true ι, because ι_q is rational and therefore not Diophantine. The true residual is
`E = E_q + (ι − ι_q)·D·∂_θK`. Hence ‖E‖_r ≤ ‖E_q‖_r + 10⁻²⁹‖D‖_r‖∂_θK‖_r, and the second term is about 10⁻²⁹,
which is negligible.

## 2. The proposed K3 theorem (flow form, field lines parametrized by φ)

**Setting.** X(R,z,φ) = R²ε(∂_R h, ∂_z h)/(1 + ε∂_φh) is the φ-parametrized field-line vector field. It is
π-periodic in φ and preserves the flux form Ω = R B^φ dR∧dz (div B = 0). Write ψ = 2φ − π/2, ω = ι/2 and
L = ∂_ψ + ω∂_θ, so that ∂_φ + ι∂_θ = 2L. The unknown is K : 𝕋² → ℝ², and the error is
E(K) = 2LK − X(K, φ). In polynomial form, D·E with D = R²(1 + ε∂_φh) is what K2 certifies.

**Theorem K3 (`kam_flow_torus`, proposed).** Let K be given by finitely many Fourier coefficients, and let
0 < r, with δ₀ = r/8. Suppose:
1. (H-Dioph) `Diophantine ω γ 1` with γ > 0. For torus A, γ = 0.0687 from K3a.
2. (H-frame) The normal is N = J∂_θK/(B^φ R |∂_θK|²), and the frame is M = (∂_θK, N). Assume
   ‖∂_θK‖_r ≤ σ₁, ‖1/(B^φ R |∂_θK|²)‖_r ≤ σ_G and ‖M‖_r, ‖M⁻¹‖_r ≤ σ_M.
3. (H-twist) T = Ω-torsion = N^⊤(L-transport of N) satisfies |⟨T⟩| ≥ T₀ > 0. The oracle value is ≈ 9.7×10⁻⁴.
4. (H-field) The second derivatives of X on the complex r-neighbourhood of K are bounded,
   ‖D²X‖ ≤ c₂. For polynomial or rational X this follows from Banach-algebra bounds and a Neumann bound for
   1/D.
5. (H-small) 32 Ĉ ‖E‖_r / (γ⁴ δ₀⁴) ≤ 1, where Ĉ = Ĉ(σ₁, σ_G, σ_M, T₀, c₂) is explicit (§3).

Then there is K_∞ with ‖K_∞ − K‖_{r/2} ≤ C₂‖E‖_r/(γ²δ₀²) and 2LK_∞ = X(K_∞, φ) exactly, so K_∞ is an
invariant torus with rotational transform exactly ι.

**Newton step (Lemma `kam_step`).** Given K with error E on strip r and 0 < δ < r/2:
- (a) Approximate reducibility: M⁻¹(2LM − DX(K)M) = [[0, T],[0, 0]] + R_E with ‖R_E‖_{r−δ} ≤ c_R(eδ)⁻¹‖E‖_r.
  The upper-left 0 holds because ∂_θK solves the linearized equation up to ∂_θE. The lower-right 0 holds
  by the trace identity that follows from Ω-preservation (div B = 0).
- (b) Write ΔK = Mξ and η = M⁻¹E, and solve the two cohomological equations (each by `cohSol_estimate_one`,
  with the factor 1/2 from 2L):
  - 2Lξ₂ = −η₂ + ⟨η₂⟩. Lemma `flux_average`: ⟨η₂⟩ = O(‖E‖²), which comes from exactness (the zero-flux
    identity for the polynomial field). Alternatively, add a translation counterterm λN (Rüssmann/Herman
    translated torus) and prove λ = 0 a posteriori by the same flux identity.
  - 2Lξ₁ = −η₁ − Tξ₂, with ⟨ξ₂⟩ chosen = −⟨η₁ + Tξ₂⁰⟩/⟨T⟩ (this uses the twist).
- (c) The new error is E' = E(K + ΔK). By Taylor's formula and (a)–(b),
  ‖E'‖_{r−2δ} ≤ Ĉ γ⁻⁴ δ⁻⁴ ‖E‖_r² and ‖ΔK‖_{r−δ} ≤ Ĉ' γ⁻² δ⁻² ‖E‖_r.
- (d) The frame constants degrade by at most a factor (1 + O(‖ΔK‖/δ)), which is absorbed in a fixed
  margin, as in FHL Lemma 2.8.

**Convergence lemma (`kam_sequence`, pure real analysis; the first piece to formalize).** Let
δ_j = δ₀2^{−j} and r_{j+1} = r_j − 2δ_j, so that r_∞ = r − 4δ₀ = r/2. Suppose
e_{j+1} ≤ κ δ_j^{−4} e_j² with κ = Ĉ/γ⁴, and 32 κ e₀/δ₀⁴ ≤ 1. Put ε_j := 16κδ_j^{−4}e_j. Then
ε_{j+1} ≤ ε_j², so ε_j ≤ 2^{−2^j}, e_j → 0 superexponentially, and Σ_j Ĉ'γ⁻²δ_j^{−2}e_j ≤ 2Ĉ'e₀/(γ²δ₀²).
It is a two-line induction (`fun_induction`/`Nat.rec` plus `nlinarith`). The limit then uses completeness of
ℓ¹_{r/2}. The library's `Contraction`/`RadiiPolynomial` handle each finite step's linear algebra, such as
‖M⁻¹‖ bounds by a radii-polynomial certificate, but **not** the iteration itself (`kam-route.md` §2.4).

## 3. Constant budget for torus A

Oracle values are ‖E‖_ρ ≈ 5.8×10⁻²² at ρ = 0.02 turns, so r = 2πρ = 0.1257 and δ₀ = r/8 = 0.0157. The
certified γ is 0.0687.

| quantity | value |
| --- | --- |
| γ⁴ | 2.23×10⁻⁵ |
| δ₀⁴ | 6.09×10⁻⁸ |
| 32‖E‖_r/(γ⁴δ₀⁴) | 1.37×10⁻⁸ |
| **admissible Ĉ** (H-small) | **≤ 7.3×10⁷** |
| FHL form ‖E‖/(γ⁴r⁴), r in radians | 1.0×10⁻¹³ (C₁ ≤ 9.6×10¹²) |
| FHL form ‖E‖/(γ⁴ρ⁴), ρ in turns (oracle) | 1.6×10⁻¹⁰ |
| one cohomological solve, δ = δ₀ (`cohSol_estimate_one`, with the ½ of 2L) | 1/(2eγδ₀) ≈ 170 |
| one Cauchy loss (`dθ_estimate`) | 1/(eδ₀) ≈ 23.4 |
| ι_q contribution to ‖E‖ | ≲ 10⁻²⁹·‖D‖‖∂_θK‖ ≈ 10⁻³⁰ |

An a priori estimate of Ĉ comes from the step's factors. The two solves and two Cauchy losses contribute
1/(2eγδ) and 1/(eδ) each, which is ≈ 1.6×10⁷ at δ₀. Their γ⁴δ⁴ part is already in the normalization, so they
put only (2e)⁻²e⁻² ≈ 4.6×10⁻³ into Ĉ. On top of that come σ_M² ≲ 10², 1/T₀ ≈ 10³, c₂ = O(10) and a
combinatorial factor of 10–10³ from the Taylor and frame terms. So Ĉ is roughly in 10⁴–10⁶, under the
7.3×10⁷ budget. The margin is one to three orders of magnitude, not a wide one. If it fails, the remedies are:
- Spend more strip. Take δ₀ = r/6, since only r_∞ > 0 is needed for K4's C¹ bound.
- Use the FHL "ad hoc" treatment of the low modes in place of the crude sup bound.
- Reduce ‖E‖ by one more refinement of K2, since the oracle residual is dominated by the truncation tail.

## 4. Lemmas remaining after K3a (dependency order)

1. **`kam_sequence`** (real sequences; §2). Independent; 1 day.
2. **`WeightedEll1Z2`**: ℓ¹_r(ℤ²) as a Banach algebra, i.e. ‖f g‖_r ≤ ‖f‖_r‖g‖_r. This is the ℤ² analogue of
   `Certificates/WeightedEll1` + `ConvAlgebra`, using the submultiplicative weight e^{r(|k|+|m|)}. It also
   needs the completeness of {f : InWeighted r f} and the bound sup ≤ ‖·‖_r on the complex strip. 3–5 days.
3. **Weighted K2 certificate**: ‖E_q‖_r ≤ 5.8×10⁻²²(1+margin) at r = 0.1257, proved in Lean (weighted
   Kronecker digit sums, `Certificates/Kronecker2D` with weights 2^{⌈r/ln2⌉(|k|+|m|)}-type dyadic
   overestimates), plus the ι − ι_q term (§1). K2 only certifies r = 0.
4. **Composition/Neumann bounds** for X∘K in ℓ¹_r: polynomial in (R, z, cos2φ, sin2φ), with 1/D by a
   Neumann series (`NormedRing.inverse`), giving (H-field).
5. **Frame and twist certificate**: σ_M, σ_G and T₀ for torus A (finite Fourier computations; radii-polynomial
   for M⁻¹).
6. **`flux_average`**: ⟨η₂⟩ = O(‖E‖²) (or the translated-torus counterterm with λ = 0 a posteriori).
7. **`kam_step`**: approximate reducibility (a), the two solves (b) using `cohSol_estimate_one`, and the
   quadratic estimate (c)–(d) with explicit Ĉ, Ĉ'.
8. **`kam_flow_torus`**: iterate 7 using 1 and 2, then pass to the limit.
9. **Classical regularity**: a 2-D `FourierRegularity` showing that the limit is a C¹ torus, so that K1/K4
   apply. The pointwise part is essentially `hasDerivAt_fourierSum_*` from K3a.
