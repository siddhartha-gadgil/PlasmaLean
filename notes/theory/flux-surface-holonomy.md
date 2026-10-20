# Flux-surface holonomy, rotational transform and conformal modulus (T10 verdict)

**Lane:** A, Cycle 1, track T10 (implementation plan §1.2). **Date:** 2026-10-20.
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

β is closed because L_Bσ|_Σ = 0 (from div B = 0 and L_Bψ = 0). Its periods are (dΦ_t/dψ, dΦ_p/dψ), its kernel is B, and
[β] ∈ H¹(Σ;ℝ) is the Schwartzman asymptotic cycle of the field-line flow. The reduction mod a lattice destroys the
information, and the arbitrary scale k makes the reduced point physically meaningless. **Verdict on the holonomy as
stated: not useful.**

## 3. What is useful: periods + τ (Hodge / Riemann bilinear)

There is a second closed 1-form, α := B♭|_Σ. Here dα = μ₀ (J·n) dA, so α is closed **iff J·∇ψ = 0** (true in MHS and in vacuum).
Its periods are ∮_{γ_p}α = μ₀ I (toroidal current enclosed) and ∮_{γ_t}α = μ₀ G (poloidal current linking Σ, coils plus plasma).
Pointwise |α| = |B|, |β| = |B|/|∇ψ|, and α∧β = (|B|²/|∇ψ|) dA.

**(P1) Riemann bilinear identity — [proved informally; reproduces a known identity].**
∫_Σ α∧β = P_p(α)P_t(β) − P_t(α)P_p(β), which gives (up to orientation conventions)
  **V′(ψ)⟨B²⟩ = μ₀ (G Φ_t′ + I Φ_p′) = μ₀ Φ_t′ (G + ιI).**
This is the familiar Boozer-coordinate identity V′⟨B²⟩ = 4π²(G + ιI) in the normalization ψ = Φ_t/2π with covariant
B = I∇θ + G∇φ + …. It is a good sanity theorem, but **not new**.

**(P2) Hodge period inequalities — [proved informally, sympy-checked].** In 2-D the Dirichlet energy of 1-forms is
conformally invariant. A closed 1-form on ℂ/(ℤ+τℤ) with periods a (on 1) and b (on τ) has energy at least that of its
harmonic (constant) representative, |b − aτ|²/Im τ. Equality holds iff the form is harmonic, and the excess is ∫|∇u|² for the
exact part du. Applying this to β with ψ = Φ_t (periods (1, ι)) and to α:

  ∫_Σ |B|²/|∇Φ_t|² dA ≥ |ι − τ|² / Im τ,  ∫_Σ |B|² dA ≥ μ₀² |G − τI|² / Im τ  (the latter needs J·∇ψ = 0).

Both right-hand sides are invariant under γ_t ↦ γ_t + kγ_p, because τ ↦ τ+k and ι ↦ ι+k. Sanity check, thin circular torus
(minor radius a, major radius R, τ ≈ iR/a) with uniform toroidal field B₀ and poloidal field ιaB₀/R: both sides equal
R/a + ι²a/R exactly (sympy). The vacuum 1/R field with I = 0 also saturates the second inequality to leading order:
μ₀²G²a/R.

**Interpretation.** The second inequality is a conformal-geometry lower bound on the surface-integrated magnetic pressure
for a given linking coil current and surface shape. The first says that a surface with modulus τ needs a field-line
"energy" of at least |ι − τ|²/Im τ to carry transform ι. The defect (LHS − RHS) ≥ 0 measures how far the field-line
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

1. **Now (pure algebra, extends Challenge 6):** for `SurfaceMetricCoeffs` (E, F, G), define
   `constFormEnergy m a b := (G*a^2 - 2*F*a*b + E*b^2) / √(EG−F²)` (times 4π² for 2π-periodic angles), and prove
   `constFormEnergy m a b = |b − a τ|² / Im τ` with `τ = (F + i√(EG−F²))/E`. Also prove invariance under
   (a, b, τ) ↦ (a, b + k a, τ + k).
2. **Later (needs torus integration over `AddCircle`):** `flatTorus_energy_ge_period`: for c ∈ ℝ² and periodic C¹ u,
   ∫_{[0,1]²} ‖c + ∇u‖²_g ≥ ‖c‖²_g · area. The cross term vanishes by periodicity. This is P2 in flat coordinates.
3. **Later:** P1 as a theorem about Boozer-coordinate fields, `boozer_Vprime_avg_B2`.
