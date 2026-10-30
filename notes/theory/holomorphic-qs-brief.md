# Assessment of the holomorphic strong-QS research brief

## Metadata

| Field | Value |
| --- | --- |
| ID | `N-32` |
| Title | Assessment of "Strongly quasisymmetric vacuum fields on a given solid torus" (colleague's brief, 30 October 2026) |
| Kind | source assessment |
| Addresses | `Q-24` (exact strong QS in a volume), `Q-16` (QS solution, exact limit), `Q-25` (new: fixed-field QS jet obstruction); closes routes of `N-21` |
| Depends on | N-21 (holomorphic bundles, KYM), N-27 (quasisymmetric solution), N-30 (planar-axis obstruction), N-31 (Dommaschk fit); Lean: `Theory/Fields/WeakQuasisymmetry`, `Theory/Contract/StellaratorContract.iota_eq_zero_of_purelyToroidal` |
| Dependency requirement | none for the assessment; Q-25 needs pointwise vector calculus on `EuclideanSpace ℝ (Fin 3)` (as in `WeakQuasisymmetry`) and symmetry of second derivatives (Mathlib) |
| Produces | Q-25; the verdict below on each section of the brief; a sympy check of its explicit numbers |
| Difficulty | routine (assessment); moderate (Q-25 in Lean) |
| Status | assessment complete; Q-25 open |
| Lean evidence | none new |
| Audit evidence | the brief's explicit computations re-derived in sympy (below); the other claims checked by hand |
| Last updated | 30 October 2026: created |

## Source

`gpt/stellarator_holomorphic_research_brief.pdf` (14 pp., "corrected research brief", revised
30 October 2026). It is written as a set of assignments for another agent team. It claims no
solution of the target, and makes no novelty claims. It supersedes an earlier version in which
the embedding of the solid torus was a free variable.

## Summary of the brief

Fix an embedded Euclidean solid torus Ω and a nonzero circulation P. The vacuum field B_P
(curl-free, divergence-free, tangent to ∂Ω, circulation P) is then **unique**: the tangent harmonic
fields of a solid torus form a 1-dimensional space. The question becomes whether this one field
has all of the following:
- nonvanishing B;
- nested flux surfaces with a Morse–Bott axis;
- a strong-QS generator u with a periodic action;
- ι ≠ 0;
- no continuous Euclidean symmetry.

Strong QS (SQS) is ι_u β = dΨ, L_u α = 0 and L_u ν = 0, where α = B♭ and β = ι_B ν. The brief then
develops the following:
1. **(FQS)** For fixed vacuum B, SQS is equivalent to the system B·∇Ψ = 0,
   (B × ∇Q)·∇Ψ = −C B·∇Q with Q = ‖B‖² and C constant. The generator is recovered as
   u = (∇Ψ × B + C B)/Q. In (Ψ, C) the system is linear.
2. **Jet obstruction.** Let X = B, Y = B × ∇Q and Z = [X, Y]. Where these three fields are
   independent, define η by η(X) = 0, η(Y) = −BQ and η(Z) = −X(BQ). Then dΨ = Cη. So a point
   of rank 3 with dη ≠ 0 rules out SQS on every neighbourhood of it (C = 0 forces dΨ = 0).
   Explicit check: B = ∇(xyz) at (1, 2, 3).
3. **Period and Boozer checks.** 2πC = mP (orbit homology). In vacuum Boozer coordinates
   Ψ' = Mι − N, with I = 0 and C = MG.
4. **Global disk section.** If B ≠ 0 on Ω, the form α/P defines a fibration Ω → S¹ by disks, and
   B is transverse to the fibres (B·∇p = Q/P > 0). Its first-return map preserves the area form
   induced by β.
5. **Holomorphic lift.** On X = Ω × ℝ_t with ℱ = β + dt ∧ α, ℱ is closed and anti-self-dual, so B
   is a Hermitian–Yang–Mills line bundle (abelian Bogomolny). Uniqueness passes to the curvature,
   so the lift adds no new fields. The brief states SQS on X in this form, as (HQS).
6. **Two proved ansatz obstructions.**
   - Proposition 5.1: the flat rank-one Kähler–Yang–Mills coupling forces Q to be constant. Then
     B is constant (Δ‖B‖² = 2‖∇B‖²), and a constant field cannot be tangent to a bounded boundary.
   - Proposition 5.2: a horizontal QS generator that is holomorphic for I₀ is a Euclidean Killing
     field, so it contradicts non-symmetry.
7. **Research directions.** These are speculative and the brief marks them so: a circle-quotient
   reduction, Bogomolny/minitwistor data with affine monodromy, the elliptic curves of the flux
   tori (flat, degree-zero bundles), and higher-rank parent systems.

## Verification

All checked on 30 October 2026, with sympy for the explicit numbers and by hand otherwise.

- **(FQS) equivalence.**
  - With u = (∇Ψ × B + C B)/Q, the identity div u = −[(B × ∇Q)·∇Ψ + C B·∇Q]/Q² holds for
    arbitrary Ψ (symbolic check, with curl B = div B = 0 used for B = ∇(xyz)).
  - Further, B × u − ∇Ψ = −(B·∇Ψ)B/Q, B·u = C, and L_u α = d(B·u) = 0.
  - Correct.
- **Jet numbers at (1, 2, 3)** for B = ∇(xyz): all reproduced exactly.
  - Q = 49, X = (6, 3, 2), Y = (10, −128, 162), Z = (240, −768, 432).
  - det = 564480.
  - η = (−2201/720, 869/180, 463/240).
  - The dx∧dy coefficient of dη is 1739/21600 ≠ 0.
- **Uniqueness of B_P, the round-torus example and the disk section.** Standard and correct.
  - The round-torus example (ι = 0) is our compiled `iota_eq_zero_of_purelyToroidal`, in the
    special case of a vacuum field.
  - The disk section uses B·∇(Φ/P) = Q/P ≥ min Q/P > 0 on compact Ω, together with the
    compact-submersion (Ehresmann) theorem.
- **Propositions 5.1 and 5.2.** Correct, and elementary.
  - In 5.1 the boundary step is ‖B‖² Vol = ∫_∂Ω (B·x)(B·n) = 0.
  - In 5.2 the conformal-rescaling remark is also correct: d(e^{2f}ω₀) = 0 forces df = 0.
- **The definition of strong QS.** For vacuum fields it agrees with Boozer-coordinate QS:
  u = N∂_θ + M∂_φ with I, G constant gives B·u = NI + MG, a constant. BKM's form (B·u a flux
  function) is the general MHS version. The brief rightly warns that rescaling u by a function
  of the flux breaks constancy of C.

## Assessment for PlasmaLean

**1. The holomorphic part re-encodes the problem; it does not construct fields.** The brief says
this itself: the HYM/ASD lift has the same curvature as the unique B_P, so it cannot produce a
field that the vacuum equations do not. Its proved content is negative, the two ansatz
obstructions. These **close two routes of N-21**: the direct KYM coupling and a holomorphic QS
generator. N-21 already fenced its contract sketches as refuted; Propositions 5.1–5.2 now give
the reasons as short proofs. Directions D–F (twistors, elliptic-curve families, higher-rank
parents) remain speculative. They enter the graph only as a remark under Q-24, with no work
scheduled, in line with the T10 rule that a verdict note comes before any Lean.

**2. The framing with a fixed domain is compatible with our design search.** A vacuum field is
determined by its outer flux surface and its circulation. So "search over vacuum fields" (the
Dommaschk fit of N-31) is the same as "search over domains Ω". The brief's per-domain question
is the inner decision problem, "is this B_P exactly QS?". Its rule "do not change the shape" is
a rule for that assignment, not a restriction on design. Our Q-16 criterion is deliberately
approximate: certified tori, ι ≥ ι_min, and a certified defect small relative to ι. The brief's
rejection test "do not infer exactness from a small residual" matches our policy. The brief's
question is the vacuum case of **Q-24**.

**3. The useful new tool is the fixed-field linear system and its jet test (new Q-25).**
- It is a **pointwise, finite-jet obstruction**: it uses B and its first three derivatives at one
  point.
- For an explicit polynomial or rational vacuum field, the obstruction reduces to exact rational
  arithmetic. That is exactly the kind of certificate we can check in Lean without `decide`
  (`norm_num` on closed rationals).
- It complements our existing obstructions:
  - `family1_not_weakQS` and `family2_not_weakQS`: the axis argument, for non-vacuum fields;
  - `rationalStellarator_firstOrder_not_QS`: first order near a planar axis.
- The jet test works at **any interior point**, not only near the axis. It is local, so it
  cannot show global non-existence, but one certified point excludes exact QS on every domain
  containing it.
- Applications:
  - (a) Lean: (FQS) ⇔ (SQS) pointwise, and the obstruction lemma "rank 3, dη ≠ 0 ⇒ no SQS
    near p";
  - (b) a certified instance, B = ∇(xyz) at (1, 2, 3), as a sanity check;
  - (c) certified local non-QS points for `RationalStellarator.field` and, once fixed, for the
    Dommaschk candidate of N-31. This is expected, since the candidate is only approximately
    QS. Its value is honesty: it shows the candidate is not exactly QS, which keeps claims at
    the approximate tier;
  - (d) research: does a quantitative version, with |dη| controlling a lower bound on the
    attainable defect, give certified lower bounds on ε_QS? That would make the Q-16 tiers
    two-sided.
- Caveats from the brief: rank-deficient loci (symmetric fields are rank-deficient; for example
  [X, Y] = 0 for the axisymmetric vacuum field) need separate analysis, and gluing across them is
  open.

**4. The Boozer moment identity links C1 to strong QS.** In vacuum, Ψ' = Mι − N.
- For quasi-axisymmetry (N = 0), the QS moment is regular exactly where **ι ≠ 0**. So C1's
  ι ≥ ι_min is not only a tokamak exclusion: it is also the nondegeneracy condition of the QA
  moment.
- This supports the decided Q-16 normalisation "defect relative to ι". As ι → 0, the QA
  generator's moment degenerates.
- For quasi-helical symmetry the condition is Mι ≠ N. This is recorded in N-27.

**5. The global disk section is a clean lemma for C1/C4 work.** Every nonvanishing vacuum field on
a solid torus has a global Poincaré disk on which every field line returns, with return time
(in the field-line parameter) at most P / min Q.
- For the Dommaschk and rational fields, the section p = Φ/P (multivalued potential Φ) is
  canonical. B·∇p > 0 is automatic, whereas a toroidal angle φ needs B_φ > 0 to be checked.
- Formalizing the full fibration needs Ehresmann's theorem, which is heavy and absent from
  Mathlib. The return-map part (every field line crosses each level of p, at a rate
  ≥ min Q/P) is a moderate lemma and would serve the field-line confinement statements. It is
  recorded as an optional item under Q-25, not a separate question.

**6. Not adopted.** The brief's target excludes finite β, coils, stability and transport. Our
contract needs all of these, C3–C5. The brief also requires exact global SQS with a Morse–Bott
axis and no other critical points. That is the Q-24 standard, not the design criterion.

## Outputs

- New question **Q-25** (fixed-field QS jet obstruction): items (a)–(d) of §3, with the
  return-map lemma of §5 as an optional item.
- Q-24: the brief's vacuum formulation (FQS) and its jet test recorded as the precise local
  form of the question; directions D–F recorded as speculative.
- N-21: the KYM and holomorphic-generator routes are closed by Propositions 5.1–5.2.
- N-27 / Q-16: the moment identity Ψ' = Mι − N recorded as support for the ratio criterion.
