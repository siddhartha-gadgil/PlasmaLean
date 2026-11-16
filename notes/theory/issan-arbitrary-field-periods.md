# Closed-form equilibria with any number of field periods (Issan et al.): assessment

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-43` |
| Title | Assessment of "Non-axisymmetric MHD equilibria with an arbitrary number of field periods" (Issan, José, Landreman, Citrin, Tracey) |
| Kind | source synthesis (source assessment) |
| Addresses | `G-4`, `Q-17`, `Q-18`, `Q-20`; contract clauses C1–C5 as a test |
| Depends on | `sources/Non-AxisymmetricMHD.pdf` (arXiv:2611.07672v1, 5 November 2026); N-28 (Grad's conjecture), N-27 (weak quasisymmetry); Lean: `LandremanEquilibrium`, `LandremanGradCounterexample`, `Contract.CurrentFreeTransform`, `Fields.WeakQS.normB_const_of_gradient_eq_zero` |
| Dependency requirement | the preprint as posted; the compiled declarations named |
| Produces | this assessment; `scripts/issan_equilibria/` (independent checks); registry updates (Q-20, N-28) |
| Difficulty | moderate (assessment); a Lean formalization of one family is moderate and lean-ready |
| Status | stated (assessment complete; 12 of 20 claims checked, none found incorrect); nothing in Lean |
| Lean evidence | none |
| Audit evidence | not audited |
| Last updated | 16 November 2026: created |

## Purpose and scope

The user asked (16 November 2026) for the same kind of assessment as N-42 for
`sources/Non-AxisymmetricMHD.pdf`: O. Issan, L. José, M. Landreman, J. Citrin, B. Tracey,
*Non-axisymmetric MHD equilibria with an arbitrary number of field periods*, arXiv:2611.07672v1
(18 pages). Questions carried over from N-42: what the paper gives, whether its solutions meet
the five contract clauses C1–C5, and whether there is a gain for the project's numerics and
formal work. All statements about the paper refer to v1 of a preprint that is not peer reviewed.

## Dependencies

- The preprint. Its derivations were made with AI assistance (Gemini 4 multi-agent workflows,
  Section 7 of the paper) and checked by the authors with SymPy.
- The related 2026 literature already recorded in N-28.
- Compiled Lean: Landreman families 1 and 2 (`LandremanEquilibrium`, `LandremanFamily2*`),
  `family1_grad_counterexample`, the C1 contract (`CurrentFreeTransform`), the weak-quasisymmetry
  axis lemma.

## Sources and prior work

Checked by web search on 16 November 2026.

- The paper is on arXiv as 2611.07672 (physics.plasm-ph), authors as stated.
- **Grad's conjecture is disproved** (already recorded in N-28): J. Gómez-Serrano, L. Liehr,
  M. A. Taylor, *Counterexamples to Grad's conjecture*, arXiv:2609.24739, smooth equilibria on
  solid tori with nested pressure surfaces whose Euclidean symmetry group is exactly the cyclic
  group `C_N` for large `N`, with a Lean 4 certification. Explicit families: M. Landreman,
  arXiv:2609.26742 (`ι = 2` and sheared), and O. Issan, J. Citrin, M. Landreman, B. Tracey,
  arXiv:2610.07304 (without stellarator symmetry).
- Vacuum fields: W. Sengupta et al., arXiv:2610.28466 (Sci. Rep. 16 (2026) 31872); O. E. López,
  arXiv:2610.29921 (`ι = -1`).
- **Later papers found by the search, not in N-28:** arXiv:2611.16688, *An analytic toroidal MHD
  equilibrium with trivial Euclidean symmetry group* (cites the present paper as the
  stellarator-symmetric family with every field line closed and integer `ι`); arXiv:2611.10786,
  exact anisotropic-pressure equilibria with nested surfaces and confined drift orbits. Neither
  was read; they are leads.
- D. Lortz, Z. Angew. Math. Phys. 21 (1970) 196: existence of reflection-symmetric equilibria
  with `ι = 0` (iterative proof). The paper's Family 1 with `ρ_a = ρ₀` is presented as a
  closed-form member of this class.
- Stability with closed field lines: Phys. Fluids 17 (1974) 400 (cited by the paper as G. O.
  Spies; the search confirmed title, journal and DOI but not the author).

## Theory development

### 1. What the paper constructs

Field-aligned coordinates `(ρ, ζ, η)` with `B = ∂x/∂ζ`, and the map (their eq. (3))

`x + iy = C₁(ρ) e^{i m₁ ζ} + (C₂(ρ) + iη C₄(ρ)) e^{i m₂ ζ} − C₃(ρ) e^{i m₃ ζ}`,
`z = η + C₅(ρ) sin Nζ`,

with `(m₁, m₂, m₃) = (1 + (k−1)N, 1 + kN, 1 + (k+1)N)`, `k ∈ {1, 0, −1}`, and `C₁, …, C₅`
elementary (powers of `ρ` and rational combinations). The flux function is
`ψ = (H(ρ, η) − H(ρ_a, 0))/2`, a quadratic expression in the `C`'s, and `p = p₀ − 2ψ`. The
construction works because the Jacobian is independent of `ζ` (so `∇ · B = 0`) and the force
balance reduces to ordinary differential equations in `ρ`.

| | Family 1 (`k = 1`) | Family 2 (`k = 0`) | Family 3 (`k = −1`) |
| --- | --- | --- | --- |
| field periods | `N ≥ 1` | `N ≥ 2` | `N ≥ 3` |
| rotational transform | `0` | `0`, or `±N` for `N ≥ 3` | `±N` |
| remark | `ρ_a = ρ₀`: reflection symmetric (Lortz class) | `ι = ±N` branch has very thin cross-sections | wider cross-sections, larger β |

All have nested toroidal surfaces near the axis, non-constant pressure, stellarator symmetry,
**every field line closed** after one toroidal turn with `∮ dl/|B| = 2π` (Hamada condition), no
magnetic shear and no magnetic well or hill. The paper proves that all three families are
**unstable to ideal interchange** by an explicit trial displacement. For Family 1 with
`ρ_a = ρ₀` it gives a matched exterior vacuum field as a formal series in `ψ − δ`.

### 2. Independent checks

Scripts `scripts/issan_equilibria/check_equilibria.py` and `check_iota.py` (run with
`.venv-ws/bin/python`; sympy 1.14, mpmath, numpy). The formulas were typed from the paper;
derivatives are exact, residuals are evaluated with 40 digits at random points near the axis.
**These are untrusted numerics, not proofs.** 25 parameter cases: the three families,
`N = 1, …, 5`, both signs `s`.

- **Cartesian equations.** `∇ · B = 0`, `(∇ × B) × B = ∇p` and `B · ∇ψ = 0`, evaluated through
  the inverse Jacobian matrix and not through the paper's reduced equations: relative residuals
  below `10⁻³⁷`. A deliberately corrupted coefficient (2 → 2.01 in `C₅`) gives residuals of
  order 1, so the test discriminates.
- **Jacobian formula (9)** and the **axis condition** `∂_ρ H(ρ_a, 0) = 0`: agree.
- **Rotational transform.** The Gauss linking number of a field line with the axis is `0` for
  Family 1 and the small-`ρ_a` branch of Family 2, and `±N` (sign following `s`) for the other
  branch of Family 2 and for Family 3 (`N = 3, 4, 5`), within 0.02 (the thin cross-sections of
  Family 2 limit the accuracy of the quadrature).
- **Family 1 with `ρ_a = ρ₀`:** `C₂ ≡ 0`, and `B = H ∇ζ + ∇Φ` with the single-valued `Φ` of
  eq. (20). Consequence (see C1 below): the circulation of `B` around every poloidal loop
  `ζ = const` vanishes.
- **Instability identities** of Section 4.3: `ξ₀ × B = ∇χ`, `Q(ξ₁) = −g B`, `∇ · ξ₁ = g`,
  `ξ₀ · ∇p = −g`, `ξ₁ · ∇p = 0`: agree. With force balance and the standard energy principle
  they give `δW = ½ ∫ g² (−2ε + ε² (|B|² + γp)) dV < 0` for small `ε > 0`. The corrupted-formula
  run shows these identities are kinematic (they hold for any chart with `B = ∂_ζ x`), so the
  equilibrium enters only through `J × B = ∇p`.
- **`|B|` on the magnetic axis** is constant to `10⁻¹⁵` for Family 1 with `ρ_a = ρ₀` and varies
  by 2 % to 51 % in every other case tried.
- **Not checked:** the parameter thresholds for nestedness (`ρ_mid`, the Family 3 bound), the
  volume and β curves, the vacuum-series recurrence (22) and its convergence, the comparison
  table with other papers, and the claim of priority for `N ≥ 3`.

### 3. The five contract clauses

| Clause | Status of these equilibria | Basis |
| --- | --- | --- |
| C1 current-free transform | **fails in every case.** Family 1 (and the `ι = 0` branch of Family 2) has `ι = 0`, below any `ι_min > 0`. The `ι = ±N` branches have integer transform but carry net toroidal current (stated by the paper for `C₂ ≠ 0`) | paper; linking numbers; `CurrentFreeTransform.iota_ge` |
| C2 omnigeneity | not addressed by the paper. `|B|` varies along the axis except for Family 1 with `ρ_a = ρ₀`, so by the compiled axis lemma those cases are not weakly quasisymmetric with a generator nonvanishing on the axis and `∇ψ = 0` there. Family 1 with `ρ_a = ρ₀` is not decided by the lemma | numerical observation + `WeakQS.normB_const_of_gradient_eq_zero` |
| C3 MHD stability | **fails, by the paper's own theorem**: all three families are interchange unstable (no shear, `d²V/dΦ² = 0`) | paper §4.3; identities checked numerically |
| C4 equilibrium with nested surfaces | **holds as an exact model statement**: smooth closed forms with nested tori and `∇p ≠ 0`, for every `N ≥ 1` | paper; Cartesian equations checked numerically |
| C5 thermal performance | not addressed; β up to about 0.2 is a property of the family, not a transport result | paper Fig. 5 (not checked) |

So these are not candidates, and the paper does not claim they are: it offers benchmarks.

**One point of real interest for the plan (Q-20).** Family 1 with `ρ_a = ρ₀` is an exact
finite-β, non-axisymmetric equilibrium with nested surfaces and **zero net toroidal current
through every flux surface** (from `B = H∇ζ + ∇Φ`, `Φ` single valued). The Landreman families in
the library both carry net current (Q-18). This is the first explicit equilibrium in the
project's sources that meets the current half of C1 together with C4 at `β > 0`. It does so with
`ι = 0`, which is the other half of C1 failing: it illustrates that zero net current plus
three-dimensional shaping does not by itself give transform, and that the hard part of Q-20 is
`ι ≥ ι_min` and not the current.

### 4. Relation to Grad's conjecture and to the library

- These families are further explicit non-axisymmetric equilibria. For `N ≥ 2` they have the
  discrete rotation symmetry `C_N` and stellarator symmetry; for `N = 1` only the latter. They
  have closed field lines, like Landreman family 1 (`ι ≡ 2`), which the library proves to have no
  continuous Euclidean symmetry (`family1_grad_counterexample`).
- The library does not need another counterexample. The value of formalizing one of these
  families would be different: a current-free finite-β test bed (Family 1, `ρ_a = ρ₀`) for the
  C1 current clause, where both existing test beds fail.
- **Correction made with this note.** The Rosetta-stone page (16 November) said that Grad's
  conjecture for smooth fields in toroidal domains of `ℝ³` remains open. That was wrong: it was
  disproved in September 2026 (Gómez-Serrano–Liehr–Taylor, with a Lean certification), as N-28
  records. The page is corrected.

### 5. Gains for numerics and formal work

- **Benchmarks.** Exact solutions with `N ≥ 3` (the range of real devices: NCSX 3, HSX and TJ-II
  4, W7-X 5, LHD 10) for fixed-boundary codes that assume nested surfaces (VMEC, DESC, GVEC), and
  through the vacuum series a free-boundary benchmark. This is the paper's purpose and it is a
  real gain for code verification. Two cautions: closed field lines with zero shear are the most
  degenerate case for an equilibrium code (every surface is rational), so agreement there does
  not test the generic sheared case; and the exterior field is a truncated formal series whose
  convergence is not established.
- **For this project's validated numerics.** An exact solution is a test with a known answer for
  the interval and a posteriori machinery (force-balance residual checkers, Stokes-based current
  certificates, Mercier and interchange diagnostics). The instability result gives a rejected
  fixture for C3 with a known reason.
- **Lean readiness.** A formalization of Family 1 with `ρ_a = ρ₀` follows the pattern of
  `LandremanEquilibrium`: fields in closed form, `∇ · B = 0`, the kernel law `J × B = ∇p` with
  the actual Ampère current, a first integral, and then the new statement, zero loop current
  for the C1 contract. Differences that make it harder: the solution is given in field-aligned
  coordinates, not as explicit Cartesian functions, so either the chart must be inverted (not
  elementary) or the statements must be made through the chart, as `Contract.BoozerChart` does;
  and `N` is a parameter. Estimated moderate. It is proposed, not started.

## Claims and evidence

Twenty claims were extracted from the paper. Status: 12 checked and consistent, 0 found
incorrect, 8 not checked.

| # | Claim of the paper | Status |
| --- | --- | --- |
| 1 | eqs (3)–(8) satisfy `∇ · B = 0` | numerical check (exact derivatives, 40 digits), consistent |
| 2 | … and `J × B = ∇p` | same, consistent |
| 3 | … and `B · ∇ψ = 0` | same, consistent (immediate from `ψ = ψ(ρ, η)`) |
| 4 | Jacobian formula (9), independent of `ζ` | consistent |
| 5 | (6) places the axis at `ρ_a` | consistent |
| 6 | Hamada condition `∮ dl/|B| = 2π` | immediate from `B = ∂_ζ x` |
| 7 | `ι = 0` for Family 1 and for Family 2 with small `ρ_a` | numerical (linking number), consistent |
| 8 | `ι = ±N` (sign `−s`) for Family 2 with large `ρ_a` and Family 3 | numerical, consistent in magnitude and in dependence on `s` |
| 9 | Family 1, `ρ_a = ρ₀`: `C₂ = 0`, `B = H∇ζ + ∇Φ` (19)–(20) | consistent |
| 10 | axis radius formula (16) | consistent |
| 11 | instability identities of §4.3 | consistent |
| 12 | hence `δW < 0`: all families interchange unstable | follows from 2 and 11 with the standard energy principle; not formalized |
| 13 | discrete `N`-fold, reflection and stellarator symmetries (§3.3–3.5) | not checked (elementary) |
| 14 | nestedness thresholds (`ρ_a ≥ ρ₀`; `ρ_mid`; the Family 3 bound) | not checked |
| 15 | net toroidal current when `C₂ ≠ 0` | not checked (stated in one sentence) |
| 16 | volume and β curves (Fig. 5), breakdown values of `δ` | not checked |
| 17 | vacuum series (21)–(22) and its residual order | not checked |
| 18 | exterior field lines close and define flux surfaces "where the series converges" | not checked; convergence is not claimed by the paper |
| 19 | Table 1 (properties of other papers' solutions) | not checked beyond the abstracts found by search |
| 20 | first closed forms with `N ≥ 3` | not checked (priority claim) |

Own statements of this note:
- *Proof sketch:* zero poloidal circulation for Family 1 with `ρ_a = ρ₀`, from claim 9: on a loop
  `ζ = const` the term `H∇ζ` contributes nothing and `∇Φ` integrates to zero.
- *Numerical observation:* `|B|` is constant on the axis only in that case.
- *Assessment:* the C1–C5 table above.

## Difficulty, barriers and readiness

- No barrier to using the solutions as benchmarks.
- Lean: ready in the sense that the mathematics is elementary and checked numerically; the work
  is the chart-based statement and the size of the algebra for general `N`. A first unit could
  fix `N = 3`.
- The smallest useful next step: the Lean statement "Family 1 (`ρ_a = ρ₀`, `N = 3`): force
  balance, first integral, and zero loop current on every surface", which would give Q-20 its
  first compiled current-free finite-β instance and a rejected fixture for C1 by `ι = 0`.

## Outputs and next dependencies

- `scripts/issan_equilibria/` (two scripts and a README).
- Q-20: current best answer updated (an exact current-free finite-β equilibrium exists in closed
  form, with `ι = 0`).
- N-28: pointer to this note and to the two later papers (arXiv:2611.16688, arXiv:2611.10786).
- Rosetta-stone page: Grad entry corrected.
- No change to goals; no contract clause changes status.
