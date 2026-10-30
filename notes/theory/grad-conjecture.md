# Grad's conjecture and its recent disproofs

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-28` |
| Title | Grad's conjecture: recent counterexamples and their use in PlasmaLean |
| Kind | source synthesis |
| Addresses | `G-4`, `Q-14`, `Q-16`, `Q-17` |
| Depends on | `N-12` (finite-β routes), `N-27` (quasisymmetric solution); Lean: `LandremanEquilibrium.family1`, `LandremanFamily2*`, `family2_lam200_equilibrium`, `LandremanGradCounterexample.family1_grad_counterexample` |
| Dependency requirement | compiled force balance, invariant flux function and non-axisymmetry of the Landreman families (present) |
| Produces | registry updates (Q-17), work items below |
| Difficulty | routine (synthesis); moderate to hard for the Lean items |
| Status | Q-17 formalized for family 1 (30 October 2026); plane reflections, solid-torus topology of the domain and family 2 open |
| Lean evidence | `PlasmaLean.Design.LandremanGradCounterexample.family1_grad_counterexample` (default build, zero warnings, standard axioms); family 2: force balance, invariant surfaces, non-axisymmetry only |
| Audit evidence | not audited |
| Last updated | 30 October 2026: created from a literature search; Q-17 Lean statement for family 1 added |

## Purpose and scope

Grad (1967, 1985) conjectured that smooth toroidal magnetohydrostatic (MHS) equilibria with
nested flux surfaces and non-constant pressure exist only with a continuous symmetry (axial,
helical or planar reflection). This note records the September–October 2026 counterexamples,
their exact scope, and what they mean for PlasmaLean's goals. All sources are preprints
unless stated; locators were taken from abstracts and repository pages, not checked against the
full texts (marked "unverified" where it matters).

## Sources

- **[GLT]** J. Gómez-Serrano, L. Liehr, M. A. Taylor, *Counterexamples to Grad's conjecture*,
  arXiv:2609.24739 (21 September 2026), 147 pp. For every sufficiently large N: smooth MHS
  solutions in an embedded solid torus, regular pressure levels nested tori, the field vanishing
  exactly on a circular magnetic axis, Euclidean symmetry group exactly the cyclic group C_N (no
  reflection, axial or helical symmetry); smooth one-parameter families. Method: an exactly
  solvable straight-axis model with rotating elliptical sections, bent and corrected by a
  Nash–Moser iteration. **Lean 4 formalization** of the main theorem:
  github.com/lukasliehr/Grad-Conjecture (pins Lean v4.33.1; `Showcase.lean`, Nash–Moser,
  Fourier and Banach-calculus libraries; standard axioms only, per the paper's appendix).
- **[L]** M. Landreman, *Analytic toroidal 3D MHD equilibria and steady Euler flows with
  invariant surfaces*, arXiv:2609.26742 (v1 22 September, v2 28 September 2026). Explicit
  elementary closed forms, non-axisymmetric, exact nested flux surfaces, smooth field, current
  and pressure, ∇p = 0 only on the axis; family 1 with ι = 2 and a non-planar axis, family 2
  with sheared ι. Found with GPT-6 Astra Pro, checked by hand and with DESC; code at
  github.com/landreman/analytic_3d_equilibria. States that it refutes Grad's conjecture as
  formulated in Conjecture 2.5 of Cardona et al. (2025).
- **[ICLT]** O. Issan, J. Citrin, M. Landreman, B. Tracey, *Analytic non-axisymmetric 3D MHD
  equilibria without stellarator symmetry*, arXiv:2610.07304 (5 October 2026): a parameter τ
  added to both Landreman families that breaks stellarator symmetry and keeps the equilibria
  exact (τ = 0 recovers [L]).
- **[ELP]** A. Enciso, A. Luque, D. Peralta-Salas, J. Eur. Math. Soc. (2025): piecewise smooth
  (stepped-pressure) MHS equilibria far from symmetry, counterexamples to Grad in the
  stepped-pressure setting (not smooth).
- **[CDG]** P. Constantin, T. Drivas, D. Ginsberg, arXiv:2009.08860: smooth non-symmetric
  equilibria with nested surfaces sustained by a small force; quasisymmetry in a volume open.
- Earlier: Lortz (1970) mirror-symmetric equilibria with ι = 0; Sorokina–Ilgisonis, Phys.
  Rev. E (December 2024), which claims analytical counterexamples (status in the literature
  unverified here).

## What this means for PlasmaLean

1. **We already verify much of [L] in Lean.** `LandremanEquilibrium.family1` proves, for the
   paper's family 1, ∇·B = 0, the kernel law J × B = ∇p with the actual Ampère current,
   invariance B·∇ψ = J·∇ψ = 0, non-axisymmetry (not invariant under the rotation `rotQ`), a
   non-planar magnetic axis, and confinement of forward field lines (closed, ι = 2). Family 2
   (`LandremanFamily2*`, `family2_lam200_equilibrium`) adds sheared ι, derived flux labels and
   a certified Mercier-stable band. What is missing for a full Lean statement of a Grad
   counterexample is (a) nested toroidal surfaces on a smooth domain as one statement,
   (b) non-constant pressure, and (c) the absence of **every** continuous Euclidean symmetry
   (axial, helical, reflection), not only of the rotation `rotQ`. This is question **Q-17**;
   (a)–(c) are now formalized for family 1, except reflections (see the Q-17 section below).
2. **[ICLT] (no stellarator symmetry)** is a cheap extension target: the same closed-form
   verification pattern with one more parameter τ.
3. **Quasisymmetry (Q-16).** None of these papers claims quasisymmetry. The N-27 axis lemma
   (a generator nonvanishing on the axis forces constant ‖B‖ there) applies to the τ-families
   as it does to [L]; checking it is part of the N-27 Lean unit. Grad counterexamples and
   quasisymmetry are different questions: [CDG] and Burby–Kallinikos–MacKay leave exact
   quasisymmetry in a volume open.
4. **Stepped pressure (Q-14).** [ELP] is a published theorem for piecewise smooth equilibria
   far from symmetry: a source for route A of Phase 14 (stepped pressure across the exact KAM
   torus) and possibly a template for its statement.
5. **[GLT]'s field vanishes on the magnetic axis.** That is unusual for confinement design
   (no guiding-centre picture near the axis) but it is the first fully formalized (Lean)
   counterexample. Its library (Nash–Moser, analytic weights) may be reusable. It pins Lean
   v4.33.1 against PlasmaLean's v4.34.1, so reuse means porting, not importing.

## Claims and evidence

| Claim | Evidence |
| --- | --- |
| Smooth non-symmetric MHS equilibria with nested surfaces exist | sourced theorem ([GLT], with a Lean proof in its own repository); explicit solutions [L] |
| Landreman family 1: force balance, invariant ψ, non-axisymmetric, non-planar axis | compiled Lean theorem `LandremanEquilibrium.family1` |
| Landreman family 1 is a Grad counterexample (smooth, MHS, nested torus surfaces, non-constant p, no continuous Euclidean symmetry) | compiled Lean theorem `LandremanGradCounterexample.family1_grad_counterexample` (scope in the section below) |
| Absence of continuous symmetries for family 2; absence of plane-reflection symmetry (either family) | not formalized |
| Landreman families not quasisymmetric (axis-nonvanishing generator) | N-27 argument; Lean unit in progress |

## Lean statement for family 1 (Q-17, 30 October 2026)

Module `PlasmaLean/Design/LandremanGradCounterexample.lean` (default build, zero warnings,
`propext`/`Classical.choice`/`Quot.sound` only). `family1_grad_counterexample` states, for
`0 < ε < 1`, `0 < δ < (1-ε)²/4`, `μ₀ > 0`, `a = √(1+ε)`, `b = √(1-ε)`, pressure
`p = (2δ - 2ψ)/μ₀` and plasma domain `Ω_δ = {x ∈ 𝒰 | ψ x ≤ δ}`:

1. **Smooth.** `𝒰 ⊇ Ω_δ` is open; `B`, `J = (∇ × B)/μ₀` (actual derivative) and `p` are
   `ContDiffOn ℝ ∞` on `𝒰`.
2. **MHS.** On `𝒰`: `∇ · B = 0` and the kernel law `J × B = ∇p` with `∇p = gradient p`.
3. **Nested toroidal surfaces.** `ψ` is a first integral and `ψ ≥ 0` on `𝒰`; the sublevel sets
   `{x ∈ 𝒰 | ψ ≤ c}`, `c ≤ δ`, are compact and increase with `c`; for every `0 < c ≤ δ` the level
   set `{x ∈ 𝒰 | ψ = c}` is homeomorphic to `S¹ × S¹` through an explicit map `torusMap`
   (`fluxSurface_homeo_torus`); `{ψ = 0}` is homeomorphic to `S¹` and contains the magnetic
   axis (`axisSet_homeo_circle`). The parametrization comes from new labels
   `P + iQ = (2q² - w + i zF)/s` with `(u + iv) s = (P + iQ)(x/a + i y/b)²`; it formalizes
   the paper's claim (below (2.11)) that the surfaces are tori.
4. **Non-constant pressure**: `2δ/μ₀` on the axis, `0` on the torus `ψ = δ`.
5. **No continuous Euclidean symmetry.** For every Killing field `K x = r × x + t` with
   `(r, t) ≠ 0` (rotations, translations, screw motions; so axial and helical generators) there
   is a point of `Ω_δ` with `L_K B = (DB) K - r × B ≠ 0`. In fact `L_K B = 0` at the two axis
   points `ζ = 0, π/2` already forces `r = t = 0` (`killing_trivial_of_axis`): six linear
   equations, the last pair giving `2t₂ = ±2ε r₂`.

Sanity contrast: at `ε = 0` the rotation `e_z × x` satisfies `L_K B = 0` on all of `𝒰`
(`axisymmetric_limit_lie_zero`).

**Weakened or omitted.** (a) The solid-torus topology of `Ω_δ` is not stated (only
compactness and the decomposition into the axis circle and the tori). (b) Only continuous
symmetries are excluded; family 1 keeps its discrete symmetries (two field periods,
stellarator symmetry: `field_rotPi`, `field_flipX`), and plane-reflection symmetry is not
addressed (arbitrary planes give nonlinear conditions). (c) `ι ≡ 2`: all field lines are
closed, so the example is non-generic. (d) Family 2 is not treated.

## Difficulty, barriers and readiness

Q-17 is done for family 1 (section above). Remaining: the same statement for family 2 (its
closed forms and flux labels are compiled), plane-reflection symmetry, and the solid-torus
topology of the plasma domain. [ICLT] is
lean-ready once its closed forms are transcribed. Porting [GLT] is large.

## Outputs and next dependencies

- New question Q-17 (a Lean statement of a Grad counterexample) and the work items 1–4 above.
- Feeds G-4 (finite-β non-axisymmetric equilibria), Q-14 ([ELP]) and Q-16 (barrier check on
  the τ-families).
