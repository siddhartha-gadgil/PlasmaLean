# Flux-surface holonomy, rotational transform and conformal modulus (T10 verdict)

**Lane:** A, Cycle 1, track T10 (implementation plan §1.2). **Date:** 2026-10-20.

| Field | Value |
| --- | --- |
| ID | `N-3` |
| Title | Flux-surface holonomy, periods, τ and Hodge bounds |
| Kind | proof / formalization |
| Addresses | G-7 (T10), plan §1.2, §11.6 |
| Depends on | `magneticTwoForm_flux_surface` (compiled) |
| Difficulty | moderate (constant metric done); hard for a non-constant metric (uniformization) |
| Status | verified for the constant-metric model (P2 and its corollaries); holonomy ↔ ι refuted; P1 proved informally only |
| Lean evidence | `PlasmaLean.Theory.Fields.FluxSurfaceTwoForm` (`magneticTwoForm_flux_surface`); `PlasmaLean.Theory.Geometry.TorusHodge` (default build, §6) |
| Audit evidence | not audited |
| Last updated | 2026-10-30: constant-metric τ/energy identity and Hodge period inequality formalized (§6) |
**Checks:** `/tmp/lanea/hodge.py`, `/tmp/lanea/tau.py` (sympy, outside the repo). All residuals are 0.

## 1. Setting

Σ = Σ_ψ is a regular flux torus with B·∇ψ = 0 and ∇ψ ≠ 0. Take a basis of H₁(Σ;ℤ): γ_p is the poloidal meridian
(it bounds a disc in the plasma) and γ_t is a toroidal longitude (defined up to γ_t ↦ γ_t + kγ_p). The induced metric gives a
conformal structure Σ ≅ ℂ/(ℤ + τℤ), with γ_p ↦ 1 and γ_t ↦ τ, Im τ > 0. For a metric with constant coefficients (E, F, G) in
angles (θ, φ) with θ ↔ γ_p, this gives **τ = (F + i√(EG − F²))/E** (sympy-checked against the energy formula below).
This is the object behind `Challenge6_ConformalTorusModulus`.

## 2. The holonomy claim: what is true

* ω_B|_Σ = 0 (B is tangent), so a connection A with ∇×A = B restricts to a **flat** U(1) connection on Σ.
* Its periods are ∮_{γ_p} A = Φ_t(ψ), the toroidal flux (Stokes on the meridian disc, gauge invariant), and
  ∮_{γ_t} A = Φ_p(ψ) + c, the poloidal flux **up to an additive constant c**. The constant is fixed by neither B nor the
  plasma domain, because the gauge A ↦ A + c∇φ is allowed in the torus.
* The *holonomy* is exp(i k (Φ_t, Φ_p + c)) ∈ U(1)², which is a point of the dual torus ≅ Pic⁰(E_τ) ≅ E_τ. The scale k is
  arbitrary: there is no flux quantum in classical MHD, and "up to flux normalization" in the original note means exactly this.

**Correction to "holonomy encodes ι(ψ)".** The holonomy at one ψ encodes the two fluxes, modulo an arbitrary lattice and
with one period defined only up to a constant. It does **not** encode ι. The rotational transform is the **slope** of the
curve ψ ↦ (Φ_t, Φ_p) in the universal cover, ι = dΦ_p/dΦ_t. Equivalently, ι is the ratio of the periods of the closed
1-form

  β := ι_B σ on Σ, where σ is the Leray area form (dψ ∧ σ = vol, so σ = dA/|∇ψ|).

β is closed because L_Bσ|_Σ = 0 (from div B = 0 and L_Bψ = 0). Its kernel is B, and
[β] ∈ H¹(Σ;ℝ) is the Schwartzman asymptotic cycle of the field-line flow.

**Orientation conventions (fixed here and used in §3).** Use angles (θ, φ) on Σ with (ψ, θ, φ) right-handed, i.e.
Jacobian 𝒥 = 1/(∇ψ × ∇θ · ∇φ) > 0, so that σ = 𝒥 dθ∧dφ on Σ and Σ is oriented by dθ∧dφ. Orient γ_p by increasing θ at fixed
φ and γ_t by increasing φ at fixed θ (this orientation is the one for which γ_p ↦ 1, γ_t ↦ τ has Im τ > 0). Define the fluxes
with the same orientations, Φ_t(ψ) = (1/2π)∫_{ψ′<ψ} B·∇φ dV and Φ_p(ψ) = (1/2π)∫_{ψ′<ψ} B·∇θ dV, so that
Φ_t′ = (1/2π)∬ 𝒥 B^φ dθ dφ and Φ_p′ = (1/2π)∬ 𝒥 B^θ dθ dφ, where B^θ = B·∇θ, B^φ = B·∇φ and ′ = d/dψ.

**Periods, with signs.** Since i_B(𝒥 dθ∧dφ) = 𝒥 (B^θ dφ − B^φ dθ),

  ∮_{γ_p} β = −∮ 𝒥 B^φ dθ = −Φ_t′,  ∮_{γ_t} β = ∮ 𝒥 B^θ dφ = Φ_p′

(each loop integral is independent of the other angle because β is closed, so it equals its average). With these orientations
**ι = dΦ_p/dΦ_t = Φ_p′/Φ_t′ = −∮_{γ_t}β / ∮_{γ_p}β**, and ι = B^θ/B^φ for straight-field-line angles. Reversing the
orientation of γ_p (or of the poloidal angle) gives periods (Φ_t′, Φ_p′) but flips the sign of Im τ. The reduction mod a lattice destroys the
information, and the arbitrary scale k makes the reduced point physically meaningless. **Verdict on the holonomy as
stated: not useful.**

## 3. What is useful: periods + τ (Hodge / Riemann bilinear)

There is a second closed 1-form, α := B♭|_Σ. Here dα = μ₀ (J·n) dA, so α is closed **iff J·∇ψ = 0** (true in MHS and in vacuum).
Its periods are ∮_{γ_p}α = μ₀ I (toroidal current enclosed) and ∮_{γ_t}α = μ₀ G (poloidal current linking Σ, coils plus plasma).
Pointwise |α| = |B|, |β| = |B|/|∇ψ|, and α∧β = (|B|²/|∇ψ|) dA.

**(P1) Riemann bilinear identity — [proved informally; reproduces a known identity].**
∫_Σ α∧β = P_p(α)P_t(β) − P_t(α)P_p(β), which gives, with the periods of §2 (P_p(β) = −Φ_t′, P_t(β) = Φ_p′),
  **V′(ψ)⟨B²⟩ = μ₀ (G Φ_t′ + I Φ_p′) = μ₀ Φ_t′ (G + ιI).**
This is the familiar Boozer-coordinate identity V′⟨B²⟩ = 4π²(G + ιI) in the normalization ψ = Φ_t/2π with covariant
B = I∇θ + G∇φ + …. It is a good sanity theorem, but **not new**.

**(P2) Hodge period inequalities — [proved informally, sympy-checked].** In 2-D the Dirichlet energy of 1-forms is
conformally invariant. A closed 1-form on ℂ/(ℤ+τℤ) with periods a (on 1) and b (on τ) has energy at least that of its
harmonic (constant) representative, |b − aτ|²/Im τ. Equality holds iff the form is harmonic, and the excess is ∫|∇u|² for the
exact part du. Applying this to β with ψ = Φ_t (periods (−1, ι) in the orientation of §2) and to α:

  ∫_Σ |B|²/|∇Φ_t|² dA ≥ |ι + τ|² / Im τ,  ∫_Σ |B|² dA ≥ μ₀² |G − τI|² / Im τ  (the latter needs J·∇ψ = 0).

Both right-hand sides are invariant under γ_t ↦ γ_t + kγ_p, because τ ↦ τ+k and ι ↦ ι−k (the new poloidal angle is θ − kφ). (An earlier version wrote |ι − τ|² with periods (1, ι); that matches the opposite orientation of γ_p, under which Im τ < 0. The two agree when Re τ = 0, as in the sanity check below.) Sanity check, thin circular torus
(minor radius a, major radius R, τ ≈ iR/a) with uniform toroidal field B₀ and poloidal field ιaB₀/R: both sides equal
R/a + ι²a/R exactly (sympy). The vacuum 1/R field with I = 0 also saturates the second inequality to leading order:
μ₀²G²a/R.

**Interpretation.** The second inequality is a conformal-geometry lower bound on the surface-integrated magnetic pressure
for a given linking coil current and surface shape. The first says that a surface with modulus τ needs a field-line
"energy" of at least |ι + τ|²/Im τ to carry transform ι. The defect (LHS − RHS) ≥ 0 measures how far the field-line
1-form is from being harmonic (straight and uniform in conformal coordinates). We have **no evidence yet** that this defect
correlates with any confinement figure of merit.

## 4. Verdict

* **Holonomy ↔ ι (as in the holomorphic note): not useful.** It is false as stated, and the corrected version just re-encodes
  the fluxes.
* **Periods + τ (P1, P2): useful later.** P1 is a correct sanity theorem tying the geometry layer to Boozer quantities.
  P2 is a cheap, rigorous inequality usable as a consistency check on oracle equilibria (DESC/VMEC output must satisfy it)
  and as a design bound linking coil current G, surface shape τ and boundary |B|. Neither is needed on the G1/G2 critical path now.
* **Positive degree / theta functions / h⁰ = m·deg:** refuted (the bundle is flat of degree 0).

## 5. Concrete Lean targets (if/when scheduled)

1. **Done (30 October, §6), in the form below with `E, F, G` a `ConstMetric`:** for `SurfaceMetricCoeffs` (E, F, G), define
   `constFormEnergy m a b := (G*a^2 - 2*F*a*b + E*b^2) / √(EG−F²)` (times 4π² for 2π-periodic angles), and prove
   `constFormEnergy m a b = |b − a τ|² / Im τ` with `τ = (F + i√(EG−F²))/E`. Also prove invariance under
   (a, b, τ) ↦ (a, b + k a, τ + k).
2. **Done for constant metrics (§6),** with the fundamental square `[0,1]²` instead of `AddCircle`, and for every
   closed periodic form rather than only `c + ∇u` (formalized as `ClosedPeriodicForm.energy_ge`; planned name `flatTorus_energy_ge_period`): for c ∈ ℝ² and periodic C¹ u,
   ∫_{[0,1]²} ‖c + ∇u‖²_g ≥ ‖c‖²_g · area. The cross term vanishes by periodicity. This is P2 in flat coordinates.
3. **Later:** P1 as a theorem about Boozer-coordinate fields, `boozer_Vprime_avg_B2`.

## 6. Lean evidence (30 October 2026): constant-metric model

Module `PlasmaLean.Theory.Geometry.TorusHodge` (default build, zero warnings, standard axioms only; 17 entries in
`scripts/check_axioms.lean`). Model: lattice coordinates `(x, y) ∈ ℝ²/ℤ²` on `ℂ/(ℤω₁ + ℤω₂)`, a **constant** metric
`E dx² + 2F dx dy + G dy²` (`ConstMetric`, `E > 0`, `EG − F² > 0`), `τ = (F + i√(EG − F²))/E` (`ConstMetric.tau`). A
closed 1-form is `α = f dx + g dy` with `f, g` continuous and 1-periodic and `∂_y f = ∂_x g = d` continuous
(`ClosedPeriodicForm`); periods are the line integrals `a = ∫₀¹ f(x, 0) dx` (γ_p ↦ ω₁) and `b = ∫₀¹ g(0, y) dy`
(γ_t ↦ ω₂); energy `= ∫∫_{[0,1]²} (G f² − 2F fg + E g²)/√(EG − F²)` (`ClosedPeriodicForm.energy`).

* `latticeMetric_tau`: for `E = |ω₁|²`, `F = Re(ω̄₁ω₂)`, `G = |ω₂|²` and `Im(ω̄₁ω₂) > 0`, `τ = ω₂/ω₁`.
* (a) `ConstMetric.periodBound_eq`: `|b − aτ|²/Im τ = (G a² − 2F ab + E b²)/√(EG − F²)`; `energy_constForm`: the
  harmonic form `a dx + b dy` has exactly this energy; `ConstMetric.periodBound_shift`: invariance under
  `(b, τ) ↦ (b + ka, τ + k)`.
* Periods are well defined: `lineIntegral_const` (Fubini + FTC from closedness and periodicity), `periodP_eq`,
  `periodT_eq`; they equal the averages over `[0,1]²` (`avg_f`, `avg_g`).
* (b) `integral_dens_decomp` (any probability measure: the cross term vanishes), `energy_eq_add` (energy = harmonic
  energy + `∫ Q(f − a, g − b)/√det`), `energy_ge` (**energy ≥ |b − aτ|²/Im τ**), `energy_eq_iff` (equality iff
  `f ≡ a` and `g ≡ b`).
* (c) `fieldLine_energy_ge`: periods `(−Φ_t′, Φ_p′)`, `ι = Φ_p′/Φ_t′` ⇒ energy ≥ `Φ_t′² |ι + τ|²/Im τ`;
  `fieldLine_energy_ge_normalized` (`ψ = Φ_t`, periods `(−1, ι)`): energy ≥ `|ι + τ|²/Im τ`;
  `currentForm_energy_ge`: periods `(μ₀I, μ₀G)` ⇒ energy ≥ `μ₀²|G − τI|²/Im τ`.
* Sanity: `squareMetric_tau` (`τ = i`), `energy_constForm_square` (`a² + b²`), `cosForm_energy_gt` (the closed
  non-constant form `(a + cos 2πx) dx + b dy` has strictly larger energy on every constant metric).

**Scope and what remains.** The metric is constant in the chosen angles (the model case). The identification of the
physical energies (`∫|B|²/|∇ψ|² dA`, `∫|B|² dA`) with `energy` holds only when the induced metric has constant
coefficients in `(θ, φ)`. For a general flux surface one needs conformal invariance of the 1-form energy plus
uniformization of the induced metric (isothermal coordinates), not available in Mathlib; this is the next step. P1
(Riemann bilinear / Boozer identity) is not formalized.
