# A finite-β, non-axisymmetric equilibrium with proofs: which route?

Lane-A discovery note (Phase 8 input). Status tags follow `README.md`. **Nothing here is a compiled Lean
theorem.** Symbolic checks: sympy in `/tmp/laneA7/scripts/landreman1.py` and `landreman1b.py`. The literature
was checked on 20 October 2026, and three of the most relevant papers are preprints from September–October 2026.

## 0. Verdict

1. **The landscape changed in September–October 2026.** Three new results bear directly on this question.
   - **Landreman** (arXiv:2609.26742, preprint, Sept 2026) gives *explicit, elementary-function*,
     non-axisymmetric solutions of `J × B = ∇p`, `∇·B = 0`. They have smooth field, current and pressure on a
     bounded solid torus, exact nested flux surfaces, two field periods and stellarator symmetry, and ∇p vanishes
     only on the axis. There are two families:
     - family 1 has uniform ι = 2 (closed field lines);
     - family 2 has a weakly sheared ι(ψ).
   - **Gómez-Serrano–Liehr–Taylor** (arXiv:2609.24739, Sept 2026) prove, by Nash–Moser, the existence of smooth
     MHS solutions on solid tori. Their symmetry group is only C_N, they have nested pressure tori, and B
     vanishes on a round axis. The main theorem is **formalized in Lean 4** (github.com/lukasliehr/Grad-Conjecture,
     Lean 4.33.1, ≈ 5.8k modules). That library includes Nash–Moser iteration, Fourier norms, analytic weights
     and Neumann/perturbation inverses. No licence file was found, so ask before reusing any code.
   - **Issan–Citrin–Landreman–Tracey** (arXiv:2610.07304, Oct 2026) add a parameter that breaks stellarator
     symmetry in both Landreman families.
2. **Most feasible target: formalize Landreman family 1 now (stage F1, ≈ 1–2 agent-days).** It is an *exact*,
   smooth, finite-β, non-axisymmetric MHS equilibrium with nested surfaces.
   - Every identity is algebraic in (x, y, z, F), with F = √(1 − (1−s)² − 4z²).
   - The proof pattern is that of `Design/HelicalEquilibrium` and `Design/Solovev`. I checked (sympy, at random
     points) that `(∇×B)×B = ∇p` holds, that `B·∇ψ = 0`, and that **`(B·∇)B = −(x, y, 4z)`** exactly. So field
     lines are explicit harmonic oscillators, which makes the force balance proof short.
   - It would be the first non-axisymmetric finite-pressure equilibrium with toroidal topology in the library.
     `HelicalEquilibrium` is helically symmetric and straight.
   - The honest label is *idealized*. Family 1 has ι ≡ 2 (every surface rational, zero shear). Its
     non-axisymmetry is a linear stretch `B(x) = A B₀(A⁻¹x)`, `A = diag(√(1+ε), √(1−ε), 1)`, of an axisymmetric
     Solov'ev-type field. (Correction: in family 1 the axis is non-planar, of constant radius √(1−ε²); see below.) It is a genuine counterexample to Grad's conjecture but
     not a realistic stellarator.
3. **Next: family 2 (stage F2, ≈ 1 week).** It has sheared ι (ι(0) ≈ 2.287, ι(δ) ≈ 2.288 in the paper's
   example), so most surfaces are irrational. It needs complex `sqrt` with a branch condition and the identity
   `(B·∇)B = −∇Q`. A different-mechanism alternative is the GSLT C_N family, which is already in Lean but
   would have to be imported or re-proved.
4. **Options (i)–(iii) of the brief, assessed (§2–§4).**
   - **(i) Near-axis (Garren–Boozer) with a validated remainder** yields only an approximate equilibrium,
     `J×B − ∇p = F` with explicit `|F| = O(r³)`. The expansion is overdetermined at third order, so it is not an
     exact equilibrium. Useful only as a "small-force" statement in the sense of Constantin–Drivas–Ginsberg.
   - **(ii) Perturbing the rational vacuum field by a small smooth pressure with a radii polynomial is blocked.**
     p must be constant on a neighbourhood of every rational surface (the Pfirsch–Schlüter divisor `n − mι`). The
     linearized operator has small divisors, so a fixed-space contraction cannot close: one needs Nash–Moser/KAM
     with loss of analyticity, the same obstruction as in `kam-route.md` §2.4.
   - **(iii) Stepped pressure across an invariant torus of the rational vacuum field** is the right *long-term*
     target for **our** field. It is exactly the Enciso–Luque–Peralta-Salas construction (JEMS 27 (2025) 2251).
     Its three analytic steps are a KAM torus, a Hamilton–Jacobi equation on T², and Cauchy–Kovalevskaya, and the
     first is the subject of `kam-route.md`. The cost is at least that of the KAM route plus two further
     KAM-class arguments. §4.3 gives a staged plan and a minimal statement.
5. **Recommended plan:** F1 (Landreman family 1) → F1′ (its stability and confinement corollaries) → F2 (family 2)
   in parallel with the KAM route K0–K3 → F4 (single-jump stepped pressure on our vacuum field, after K3).

---

## 1. The obstruction, stated precisely

- **Magnetic differential equation.** Suppose B has a flux function ψ and p = p(ψ). The current must be
  `J = B × ∇p / B² + λB` with `B·∇λ = −∇·(B × ∇p/B²) = 2 p′(ψ) B × ∇ψ · ∇B / B³`. On a rational surface
  ι = n/m this is solvable only if the right-hand side averages to zero along every closed field line, so that
  ∮ dl/B is the same on every line (the Hamada/Newcomb condition). Generically it is not. Then λ has a `1/(n − mι)`
  singularity (Pfirsch–Schlüter) together with a δ-function current sheet on the surface. Loizu et al.
  (Phys. Plasmas 22 (2015) 090704) computed such sheets explicitly in ideal 3-D equilibria.
- **Grad's conjecture (1967).** Smooth non-symmetric MHS equilibria with nested surfaces and non-constant
  pressure do not exist (or, in later formulations, exist only isolated, with no families). The September 2026
  preprints **disprove** the commonly stated version, with solutions that are smooth, non-symmetric and come in
  families. They do so in **non-generic** ways:
  - closed field lines everywhere (Landreman family 1; poloidally closed lines with B = 0 on the axis in GSLT);
  - or an explicitly integrable structure (Landreman family 2).

  So the generic obstruction for a field like our rational stellarator still stands: shear plus chaos means
  rational surfaces in every interval.
- **Generic metrics (Cardona–Duignan–Perrella, ARMA 2025, arXiv:2312.14368).** For an open dense set of metrics
  adapted to a given MHS solution, the equilibrium has no continuous Killing symmetry. This is a non-Euclidean
  contrast to Grad, not an existence result in ℝ³.
- **Positive results that avoid smoothness:**
  - Bruno–Laurence (CPAM 49 (1996) 717–764): stepped pressure for small perturbations of axisymmetry;
  - Enciso–Luque–Peralta-Salas (JEMS 2025; arXiv:2104.08149): stepped pressure in *any* nondegenerate analytic
    toroidal domain, including knotted ones, and free-boundary versions;
  - Hudson–Dewar MRxMHD / SPEC (Hudson et al., Phys. Plasmas 19 (2012) 112502);
  - Hudson–Kraus (JPP 83 (2017) 715830403): continuous-B equilibria alternating ideal (irrational) and relaxed
    regions;
  - Constantin–Drivas–Ginsberg (JPP 87 (2021) 905870111): smooth non-symmetric, nearly quasisymmetric equilibria
    *with a small force*.

## 2. Option (i): near-axis expansion with a validated remainder

- Garren–Boozer (Phys. Fluids B 3 (1991) 2805, 2822) carry the finite-β expansion to second order. At third
  order the system is overdetermined, so an exact equilibrium does not follow. Landreman–Sengupta (JPP 2019)
  and Rodríguez–Bhattacharjee (2021) remove the overdetermination with anisotropic pressure or extra freedom.
- **What Lean could prove.** Truncate (B, p) to second order as explicit polynomials in near-axis coordinates.
  `∇·B = 0` can be imposed exactly through a Clebsch form `B = ∇ψ × ∇α`, and that form also gives exact nested
  surfaces (the pattern of `ClebschTorus`). One then proves `‖J × B − ∇p‖ ≤ C r³` on a tube r ≤ r₀ with C
  explicit, by polynomial cover.
- **Value.** It is an exact flux-surface field with explicit force residual, a small-force equilibrium in the
  CDG sense. It does not prove existence of an exact equilibrium, and the existing near-axis note already gives
  the formal content.
- **Verdict:** useful as a design-side consistency check; not the headline.

## 3. Option (ii): small pressure on the rational vacuum field by a validated fixed point

- **Formal first order.** Take B = B₀ + βB₁ and p = βp₁(ψ). This needs an *exact* flux function ψ of B₀. The
  rational field has none: it has islands (1/6, 2/11) and chaos beyond the 2/11 chain. ψ exists only on the
  Cantor family of KAM tori, so p₁′ must vanish off that family (a "devil's staircase" pressure, as in Hudson–Kraus).
- **Why a radii-polynomial certificate cannot close.** On a fixed analytic space the inverse of `B₀·∇` has symbol
  ~ `1/(k₁ι + k₂)`, which is unbounded. A Newton–Kantorovich contraction in one Banach space therefore fails for
  the same reason as in `kam-route.md` §2.4. One needs either a loss-of-analyticity (Nash–Moser/KAM) scheme or a
  degenerate structure without small divisors.
  - GSLT use closed poloidal field lines (a vanishing axis field), so their divisors are integers.
  - Landreman's family 1 has ι ≡ 2.
- **Verdict:** blocked for our field without KAM-class machinery. A *finite-length* or *small-force* version is
  feasible: a Clebsch field fitted to the approximate first integral I of `RationalStellaratorConfined`, with a
  certified force residual. It proves nothing about exact existence.

## 4. Option (iii): stepped pressure across an invariant torus (links to the KAM route)

### 4.1 Gluing lemma (ELP-S Lemma 2.1; proved informally there)

Let Ω₁ ⊂ Ω₂ be toroidal domains. Let B₁ be Beltrami (`∇×B₁ = λ₁B₁`) on Ω₁ and B₂ Beltrami on Ω₂ \ Ω̄₁, both
tangent to ∂Ω₁. Suppose `|B₁|² − |B₂|²` is **constant** on ∂Ω₁. Then B := B₁ on Ω₁ and B₂ on Ω₂ \ Ω₁, with
p := p₁ on Ω₁ and p₂ on Ω₂ \ Ω₁ (with p₂ − p₁ = (|B₁|² − |B₂|²)/2 in μ₀ = 1 units), is a **weak** MHS
equilibrium on Ω₂. A curl-free field is Beltrami with λ = 0, so vacuum fields qualify.

### 4.2 The instance for our field

- **Ω₁** = the solid torus bounded by an invariant torus S of `field (1/4)` with Diophantine ι_S (from the KAM
  route, e.g. ι_S = [0;6,1,1,1,…] ≈ 0.1511 at r ≈ 0.29). B₁ = the rational vacuum field itself, and p₁ = Δp > 0.
- **B₂** = a curl-free field in an exterior collar of S, B₂ = ∇Φ₂. Its Cauchy data on S are:
  - `∂_n Φ₂ = 0`;
  - `|∇_S Φ₂|² = |B|²|_S + 2Δp`. This is the Hamilton–Jacobi equation on S ≅ T². Sign: total pressure
    balance p + |B|²/2 with the higher pressure inside makes the outer field stronger (diamagnetic).
- **Linearization.** At Δp = 0, Φ₂ = Φ|_S solves it, because B is tangent to S. Writing Φ₂ = Φ + δΦ, the first
  order equation is `B·∇_S δΦ = Δp` (a constant). A periodic δΦ cannot satisfy it, because the average of a
  constant is non-zero. It **is** solvable once δΦ is allowed a multi-valued part a·θ + b·φ with
  `a ω₁ + b ω₂ = Δp` (this changes the cohomology class, i.e. the currents linking the torus). That is ELP-S's
  nondegeneracy, and their Theorem 5.1 solves the nonlinear equation by a Newton scheme on top of the
  Diophantine cohomological equation on S.
- **Collar.** Cauchy–Kovalevskaya for the harmonic potential with analytic data on the analytic surface S gives
  Φ₂ in a collar of explicit (majorant) thickness.
- **Outer boundary.** A KAM torus S₂ of B₂ in the collar (ELP-S Theorem 6.2/Corollary 6.3, the same theorem as
  K3 in `kam-route.md`) bounds Ω₂. Alternatively, stop at a *local* statement on Ω₁ ∪ collar.

### 4.3 Minimal statements (proposed; none exists yet)

```lean
/-- Weak MHS for piecewise-smooth data with one interface: each side is a classical equilibrium, the field is
tangent to the interface from both sides, and the total pressure p + |B|²/2 is continuous across it. -/
structure SteppedEquilibrium (Ω₁ Ω₂ : Set Space) (B₁ B₂ : Space → Space) (p₁ p₂ : ℝ) : Prop where
  inner : ∀ x ∈ interior Ω₁, ForceBalance' B₁ p₁ x          -- J × B = ∇p with p constant ⇒ J ∥ B
  outer : ∀ x ∈ Ω₂ \ Ω₁, ForceBalance' B₂ p₂ x
  tangent₁ : ∀ x ∈ frontier Ω₁, inner (B₁ x) (normal x) = 0
  tangent₂ : ∀ x ∈ frontier Ω₁, inner (B₂ x) (normal x) = 0
  jump : ∀ x ∈ frontier Ω₁, p₁ + ‖B₁ x‖ ^ 2 / 2 = p₂ + ‖B₂ x‖ ^ 2 / 2

theorem SteppedEquilibrium.weak_forceBalance : SteppedEquilibrium Ω₁ Ω₂ B₁ B₂ p₁ p₂ →
    ∀ v ∈ testFields Ω₂, ∫ x in Ω₂, (stress B p x) ⬝ (fderiv ℝ v x) = 0   -- needs a divergence theorem

theorem rationalStellarator_stepped (hS : IsInvariantTorus (field (1/4)) S ι_S) (hι : Diophantine ι_S γ τ)
    (hΔ : Δp ≤ Δp_max) : ∃ U B₂, IsOpen U ∧ S ⊆ U ∧ VacuumField (U \ Ω₁ S) B₂ ∧
      SteppedEquilibrium (Ω₁ S) U (field (1/4)) B₂ Δp 0
```

**Lean cost.**
- The structure and the jump bookkeeping are cheap.
- `weak_forceBalance` needs a divergence theorem on a domain with a curved torus boundary. That is not available
  in Mathlib beyond boxes, so state the weak form on the interface only, or skip it.
- `rationalStellarator_stepped` needs three things:
  - K3 of `kam-route.md`;
  - a Hamilton–Jacobi Newton scheme in ℓ¹_ν(ℤ²): the same small-divisor estimate as KAM, with no twist step;
  - a quantitative Cauchy–Kovalevskaya for Laplace, i.e. a majorant series in the normal variable with nested
    strips (Ovsyannikov). The ℓ¹ framework handles this, but it is new.

Estimate: ≥ 2× the KAM route. **Do not start before K3.**

## 5. Recommended stage F1: Landreman family 1 in Lean

> **Correction (2026-10-20, from the F1 formalization, `PlasmaLean/Design/LandremanEquilibrium.lean`):** the paper's
> family 1 is §2, eqs. (2.1)–(2.29), not "Eqs. 10–30". The family-1 magnetic axis (2.19) is **not planar**: it has
> constant radius √(1−ε²) (`axis_nonplanar`); the planar elliptic axis belongs to family 2. On the axis ψ = 0 and the
> plasma is Ω_δ = {0 ≤ ψ ≤ δ}; the ellipse (a cos t, b sin t, 0) with ψ = ε²/4 is an ordinary field line, not the axis.
> The statements below that say otherwise are superseded by the Lean file.

**Data.** These are the paper's family-1 formulas (Eqs. 10–30 of arXiv:2609.26742 v2, as extracted 20 Oct 2026;
re-check the locators before docstrings), checked here by sympy.

```
a = √(1+ε), b = √(1−ε), 0 < ε < 1,  s = x²/a² + y²/b²,  F = √(1 − (1−s)² − 4z²),
B = ( (2zx − (a/b) F y)/s,  (2zy + (b/a) F x)/s,  1 − s ),
ψ = (x² + y² + 4z² + |B|² − 2 + ε²)/4,   p = p_a − 2ψ   (μ₀ = 1).
```

**Checks performed** (sympy, random points with ε = 0.3, residuals ≤ 10⁻¹⁵): `∇·B = 0`,
`(∇×B)×B − ∇p = 0` and `B·∇ψ = 0`. Also `(B·∇)B = −(x, y, 4z)` (the parameter is the field-line parameter of
`IsForwardFieldLine`, with no rescaling), and ψ = ε²/4 on the axis `(a cos t, b sin t, 0)`.

**Domain.** The radicand is positive on 𝒰_ε = {1 − (1−s)² − 4z² > 0}. The plasma is Ω_δ = {ψ < ε²/4 + δ}, a
bounded solid torus for 0 < δ < (1−ε)²/4 (paper). With p vanishing on ∂Ω_δ, β_V = 2δ/(1 − ε²/2 + δ); for
ε = 1/2 and δ = 1/64 this is ≈ 3.5 %.

```lean
namespace PlasmaLean.Design.LandremanStretched
def sF (ε : ℝ) (x : Space) : ℝ := x 0 ^ 2 / (1 + ε) + x 1 ^ 2 / (1 - ε)
def rad (ε) (x : Space) : ℝ := 1 - (1 - sF ε x) ^ 2 - 4 * x 2 ^ 2
def field (ε) (x : Space) : Space := toLp 2 ![ (2*x 2*x 0 - √((1+ε)/(1-ε)) * √(rad ε x) * x 1) / sF ε x,
                                               (2*x 2*x 1 + √((1-ε)/(1+ε)) * √(rad ε x) * x 0) / sF ε x,
                                               1 - sF ε x ]
def psi (ε) (x : Space) : ℝ := (x 0 ^ 2 + x 1 ^ 2 + 4 * x 2 ^ 2 + ‖field ε x‖ ^ 2 - 2 + ε ^ 2) / 4
def domain (ε) : Set Space := {x | 0 < rad ε x ∧ 0 < sF ε x}

theorem field_divergence_free (hε : 0 < ε ∧ ε < 1) : ∀ x ∈ domain ε, divergence (field ε) x = 0
theorem field_transport (hε) : ∀ x ∈ domain ε, fderiv ℝ (field ε) x (field ε x) = -toLp 2 ![x 0, x 1, 4 * x 2]
theorem force_balance (hε) (pa : ℝ) : ∀ x ∈ domain ε,
    ForceBalance (field ε x) (curl (field ε) x) (gradient (fun y => pa - 2 * psi ε y) x)
theorem psi_firstIntegral (hε) : ∀ x ∈ domain ε, inner (field ε x) (gradient (psi ε) x) = 0
theorem field_not_axisymmetric (hε : 0 < ε ∧ ε < 1) : ¬ ∀ α x, field ε (rotZ α x) = rotZ α (field ε x)
theorem field_rotPi (ε x) : field ε (rotPi x) = rotPi (field ε x)        -- two field periods
theorem fieldLine_explicit : IsForwardFieldLine (field ε) γ → ∀ t, γ t = harmonicSolution (γ 0) (field ε (γ 0)) t
theorem fieldLine_closed : IsForwardFieldLine (field ε) γ → γ (t + 2 * π) = γ t        -- ι = 2, all lines closed
theorem fieldLine_confined (δ) (hδ : 0 < δ ∧ δ < (1 - ε) ^ 2 / 4) : psi ε (γ 0) < ε^2/4 + δ → ∀ t ≥ 0, psi ε (γ t) < ε^2/4 + δ
theorem beta_volume : ... = 2 * δ / (1 - ε ^ 2 / 2 + δ)      -- optional: needs the volume integrals
```

**Proof notes.**
- Use `force_balance` via the identity `(∇×B)×B = (B·∇)B − ∇|B|²/2`, together with `field_transport` and
  `∇(x² + y² + 4z²)/2 = (x, y, 4z)`. Every derivative is a rational function of (x, y, z, √rad), and
  `HasFDerivAt` of `Real.sqrt` needs rad > 0 (in `domain`).
- `fieldLine_explicit` follows from `field_transport`: γ″ = −(γ₀, γ₁, 4γ₂), so ODE uniqueness for the linear
  oscillator gives the explicit cos/sin solution. The library already has Grönwall uniqueness.
- `fieldLine_confined` is immediate from `psi_firstIntegral`, as in `HelicalEquilibrium.fieldLine_confined`.
- Showing that the sublevel set lies in `domain` needs a short inequality (the separating-shell trick of
  `HelicalEquilibrium`).

**Stage F1′ corollaries.**
- Mercier: with zero shear (ι ≡ 2), the criterion reduces to well and current terms. Check it before claiming
  anything. Closed-line equilibria have their own (Kadomtsev/Lortz-type) interchange criteria.
- Guiding-centre confinement is open: there is no Noether symmetry, but every field line is closed.

**Why F1 before our own field.** It gives the library a certified non-axisymmetric finite-β equilibrium now,
with all-time field-line confinement. It exercises a `ForceBalance`-with-√ pipeline that F2 and any later
stepped-pressure work reuse. And the cost is low.

## 6. Counterexample and honesty checks

- Each sympy check was at random interior points (three per identity, residuals ≤ 10⁻¹⁵), not a symbolic
  simplification. The Lean proof will be the real check.
- Family 1 is a linear image of an axisymmetric equilibrium. The paper says the map preserves the equations
  because field lines are harmonic oscillators; a general linear stretch does **not** preserve MHS.
- Do not describe F1 as "a stellarator equilibrium" without qualification. It has ι ≡ 2 (no shear, every surface
  rational) and a planar elliptic axis, and is not optimized in any sense. Family 2 has ι′ ≈ 10⁻³, which is
  nearly shearless.
- All three 2026 papers are preprints (not refereed as of 20 Oct 2026). Record their arXiv versions in the
  docstrings.

## 7. Sources

- M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with invariant surfaces*,
  arXiv:2609.26742 (v1 22 Sep 2026, v2 28 Sep 2026).
- J. Gómez-Serrano, L. Liehr, M. A. Taylor, *Counterexamples to Grad's conjecture*, arXiv:2609.24739 (21 Sep 2026);
  Lean: github.com/lukasliehr/Grad-Conjecture.
- O. Issan, J. Citrin, M. Landreman, B. Tracey, *Analytic non-axisymmetric 3D MHD equilibria without stellarator
  symmetry*, arXiv:2610.07304 (5 Oct 2026).
- A. Enciso, A. Luque, D. Peralta-Salas, *MHD equilibria with nonconstant pressure in nondegenerate toroidal
  domains*, J. Eur. Math. Soc. 27 (2025) 2251–2291; arXiv:2104.08149. Gluing Lemma 2.1; Hamilton–Jacobi
  Theorem 5.1; KAM Theorem 6.2, Definition 6.1 (twist) and Corollary 6.3.
- O. P. Bruno, P. Laurence, Comm. Pure Appl. Math. 49 (1996) 717–764.
- P. Constantin, T. D. Drivas, D. Ginsberg, J. Plasma Phys. 87 (2021) 905870111; arXiv:2009.08860.
- R. Cardona, N. Duignan, D. Perrella, *Asymmetry of MHD equilibria for generic adapted metrics*, ARMA (2025);
  arXiv:2312.14368.
- S. R. Hudson, B. F. Kraus, J. Plasma Phys. 83 (2017) 715830403.
- S. R. Hudson et al., Phys. Plasmas 19 (2012) 112502 (SPEC/MRxMHD); J. Loizu et al., Phys. Plasmas 22 (2015)
  090704 (current sheets). Both are from memory; verify the locators.
- D. A. Garren, A. H. Boozer, Phys. Fluids B 3 (1991) 2805 and 2822 (from memory).
- H. Grad, Phys. Fluids 10 (1967) 137 (from memory).

Novelty: none claimed. The note's contributions are the routing decision, the sympy checks, the explicit
linearized Hamilton–Jacobi computation for our field (§4.2) and the Lean statements.

## 8. Phase 14B follow-up: family-2 labels derived from the field (21 Oct 2026)

The Mercier band `family2_mercier_stable` (ε = 1/4, S = 4, λ = 200, k ∈ [0.7, 0.9]) used labels
ψ_t, ψ_p, V, I defined as primitives of hand-derived 1-D integrals, and the area element `JacR` from
paper (3.18). These are now theorems about the actual field:

- `LandremanFamily2Coords`: the coordinate map `(k, χ, ζ) ↦ surfPt` (ψ = k²/2) has Fréchet derivative
  `jacMatrix`; the σ-derivatives are handled abstractly and the needed combination
  `z_k σ_χ − z_χ σ_k = k/(λ cos λz T)` comes from differentiating `Re v ∘ x = k cos χ` (uniqueness of
  derivatives). `coordDeriv_det`: det = k·JacR; `coordDerivPsi_det`: det in `(ψ, χ, ζ)` is JacR.
  Injective on the box (explicit inverse via `Complex.arg`), image = shell `0 < ψ ≤ k₀²/2` of the region
  `R` (`|σ − 4| < π/2`, `|λz| < π/2`, k₀ ≤ 19/20); the axis is null.
- `LandremanFamily2FluxLabels`: Lebesgue volume of `{x ∈ R | ψ ≤ k₀²/2}` = `volK`; flux of B through the
  section ζ = 0 (parametrized surface, `fderiv` partials, Mathlib `⨯₃`) = 2π `psiT`; flux through the
  ribbon χ = 0 from the axis = 2π `psiP`; μ₀ × (flux of J = curl B/μ₀ through ζ = 0)/2π = `curK`.
  The key analytic step is `∫∫ JacR dχ dζ = Z E/(2λ)`: the `ε cos 2ζ/(2h)` part of G/h integrates to 0
  by `u = sin 2ζ`.
- `LandremanFamily2Coarea`: for continuous f, `d/dψ ∫_{ψ' ≤ ψ} f = ∫∫ f JacR dζ dχ`, so JacR dχ dζ is
  the coarea measure dS/|∇ψ|.
- `LandremanFamily2SignCert`: 10 cells, 1-D quadratures only, give ι′ > 0 and V″ > 0 on the band
  (λ-independent numerators). So the band has a certified magnetic hill, stabilized by shear.
- `LandremanFamily2MercierDerived.family2_mercier_stable_derived`: the band restated for
  `family2DataPhys` (built from the fluxes, Lebesgue volume, current and |det Dx|/k), proved equal to
  `family2Data`.

Still assumed: the Landreman–Jorge Mercier formula itself, and the choice of the cross-sections ζ = 0
and χ = 0. We did not formalize that ∇·B = 0 makes the fluxes independent of the section.

## 9. Ideal ballooning of the family-2 Mercier band (25 Oct 2026)

**Target.** Ideal ballooning on the Mercier-stable band `k ∈ [0.7, 0.9]` of Landreman family 2
(`ε = 1/4`, `S = 4`, `λ = 200`; `family2_mercier_stable_derived`).

**Supplied reduction (not formalized).** This is the interface of `BallooningReduction`
(Connor–Hastie–Taylor; Dewar–Glasser). A surface is ballooning stable iff, on every field line
and for every eikonal `S` (`B·∇S = 0`), `∫(P X'² + Q X²) dt ≥ 0` for every compactly supported
`X`, where `P = |k|²/(ℓ|B|²)`, `Q = −2ℓ(B×k·μ₀∇p)(B×k·κ)/|B|⁴` and `k = ∇S` along the line.
The equivalence is assumed. Everything below is proved.

**Verdict: numerically stable; no certificate.** Source: the untrusted
`scripts/landreman_family2_ballooning_oracle.py`. It uses exact forward-mode AD of the Lean
field formula. Along each line it integrates the field line, the transported eikonal and a
Prüfer angle together, and checks the Jacobi condition.
- Coverage: 16 × 8 starting points × 3 eikonal angles = 384 samples on each surface
  `k = 0.70, 0.75, 0.80, 0.85, 0.90`.
- Result: no Jacobi zero on `[−60, 60]`, at the physical pressure and at twice it.
- Finite-length critical pressure multipliers (`T = 100`): ≈ 4.7 (k = 0.7), 7.7 (0.8), 14.8 (0.9).
- The binding constraint is the large-σ tail, which is of Mercier type. Its flux-surface-averaged
  condition gives γ_c = 2.36, 3.13, 4.26, 6.07, 9.39 for k = 0.70 … 0.90. It is marginal at
  k ≈ 0.54, which matches the independent Mercier threshold k_c ≈ 0.53.
- So ballooning adds nothing beyond Mercier here. Finite-σ modes are far more stable, because the
  local shear is strong at the flat cross-section's tips and in its flats.

**Why there is no certificate.**
- A Riccati flux on `surface × ℝ` must contain `a σ` with `B·∇a = q₁` exactly. Numerically
  `a = −J∥ + const`.
- The certificates affine in σ are therefore `F = aσ + b`. They reduce to an auxiliary
  1-D problem, `∫ ξ'²/|∇ψ|² + Q̂ ξ²`, which has a Jacobi zero every half poloidal turn
  (oracle `affine`). That class is infeasible.
- A working flux needs genuine σ-dependence on a 2-torus where `|∇ψ|` has `O(1/λ)` tip
  structure. Its numerator must solve the tail's magnetic differential equation to about
  1e-3 relative accuracy. Building it, plus a 3-D interval cover, is beyond this phase.

**Proved in Lean (new files; standard axioms; zero warnings).**
- `Theory/Stability/BallooningSurface`: general 3-D field with a flux function, no symmetry and
  no straight-field-line coordinates.
  - Base eikonal and local Clebsch form: `k₀ = B×∇ψ/|∇ψ|²` with `∇ψ × k₀ = B`.
  - Local shear `shearRate = (⟪k₀,M∇ψ⟫ + ⟪Mk₀,∇ψ⟫)/|∇ψ|²`. It needs first derivatives only.
  - `transport_identity`, `hasDerivAt_eik`: the family `k₀ − (σ−c)∇ψ` with `σ' = shearRate` is
    transported (`k' = −Mᵀk`). This uses `tr M = 0`.
  - `eik_complete`: every transported `k ⊥ B` equals `m k₀ − s∇ψ` with `m` constant and
    `s' = m·shearRate`, so the family covers all θ_k.
  - `transport_of_hessian`: a symmetric Hessian gives `D∇ψ·B = −Mᵀ∇ψ`.
  - `ballooningP_eik`: `P = 1/|∇ψ|² + s²|∇ψ|²/|B|²`.
  - `ballooningQ_eik`: normal plus geodesic drive.
  - `eikLine`, `eikLine_stable_of_surfaceCert`: a pointwise transport–Riccati inequality
    `DΦ(B, d) + Φ²/P ≤ Q` on the points of a line gives stability for every shift.
  - `eikLine_noDrive_stable`: sanity check.
- `Design/LandremanFamily2Ballooning`:
  - `C^∞` of the field and ψ on 𝒰, and `isOpen_U`.
  - `hessian_transport`.
  - `family2_eik_transport`: the eikonal is the true covering-space gradient.
  - `field_ne_of_shell`, `gradPsi_ne_of_shell`: `B, ∇ψ ≠ 0` on the shell.
  - `family2Line`: the line data from the actual field, `DB`, `pressureGrad` (`family2Line_gp`)
    and curvature `kappa2`.
  - `family2Line_P`, `family2Line_Q`, and `eikP_surfPt` (`P` in the closed forms `gp2`, `Bsq`).
  - `family2_stable_of_cert`: the reduction to a single surface inequality.

**Status.** There is no `family2_ballooning_stable` and no `family2_ballooning_unstable`. An
instability witness is excluded numerically.

**Next step.** Prove `B·∇J∥ = −q₁` (from `∇·J = 0`, which needs `C²`, now available). Then build
an explicit σ-dependent flux using the scaled variable `u = σ|∇ψ|²/|B|`, with the tail fixed by
the averaged condition.
