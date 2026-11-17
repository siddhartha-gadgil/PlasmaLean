# Skill: Reduction to a Finite Certificate

**Pre-condition:** The claim is about a concrete design, equilibrium or parameter range and
quantifies over a continuum (all points of a surface, all modes, all parameters in a box), and a
numerical computation suggests it is true. Do not use it for a general theorem with symbolic
parameters, and never as a substitute for the analytic remainder bound.

**Goal:** Prove `check c = true → ClaimedProperty (decode c)` once, by analysis, so that each
concrete instance reduces to an exact, finite, kernel-checked computation on data `c`.

**Instructions:**
1. **Split the claim** into an analytic part (valid for all data) and a finite part (the data).
   Typical analytic parts: a Newton–Kantorovich / radii-polynomial theorem (existence and
   uniqueness of a fixed point near an approximate solution), a covering lemma (cells cover the
   parameter box), a remainder bound between samples (Lipschitz, Taylor or Cauchy estimate), a
   truncation or tail bound for omitted modes.
2. **Choose the certificate data:** exact rationals or balls (centre and radius), cell lists,
   coefficient tables. Data is independent of the search algorithm that found it.
3. **State the finite conditions** the data must satisfy: inequalities between rationals, interval
   enclosures, a negative radii polynomial `Y₀ + (Z₀ − 1) r + Z₂ r² < 0`.
4. **Prove soundness** by induction over the certificate structure; keep noncomputable analysis
   behind the soundness theorem.
5. **Close instances** with the certificate tactics (`kernel_fact`, `bool_cert`, `eval_cert`,
   `fiv_cert`, `icc_cert`, the Kronecker tactics), never `decide`; see `plasmalean-lean-proofs`.
6. **Rejected fixtures.** Prove that the checker rejects a wrong certificate (a radius too small,
   a missing cell, a zero inverse), so the checker has content.
7. **Shrink, do not grow.** If the instance is too large, improve the analytic part (sharper
   remainder, better preconditioner, adaptive cells) rather than adding more data.

**Lean:** `PlasmaLean/Certificates/` (README lists formats and tactics), notably
`RadiiPolynomial.lean`, `Contraction.lean`, `BoolCert.lean`, `RationalIntervals.lean`,
`ValidatedQuadrature.lean`; the SubsetSum pattern in `PlasmaLean/SubsetSum.lean`; skill
`plasmalean-certify-numerics` for the workflow.
