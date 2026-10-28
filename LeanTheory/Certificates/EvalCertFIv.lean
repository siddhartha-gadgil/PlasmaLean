/-
Copyright (c) 2026 LeanTheory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanTheory contributors
-/
module

public import LeanTheory.Certificates.EvalCert
public import LeanTheory.Certificates.ValidatedQuadrature

/-!
# Evaluation certificates for fixed-point interval checkers (`fiv_cert`)

`fiv_cert` is `eval_cert` (`Certificates/EvalCert.lean`) with the fixed-point interval operations
of `Certificates/ValidatedQuadrature` (`FIv.add`, `sub`, `neg`, `mul`, `sq`, `inv`, `sqrt`,
`ofInt`, `ofFrac`) as kernel leaves: each node of an interval evaluation is one interval
operation applied to interval values, and everything else (cell recursions, records, `if`,
`match`) is unfolded into `ECert` steps.

**Sanity.** `fivCert_fixture` (accepted), `fivDecide_fixture` (`fiv_decide`),
`fivCert_reject_fixture` (rejected).
-/

public section

namespace LeanTheory.Certificates.EvalCert

open LeanTheory.Certificates.ValidatedQuadrature

/-- **`fiv_cert`**: `eval_cert` with the `FIv` interval operations as kernel leaves. -/
macro "fiv_cert" : tactic => `(tactic| eval_cert [
  LeanTheory.Certificates.ValidatedQuadrature.FIv.add,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sub,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.neg,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.mul,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sq,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.inv,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sqrt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofInt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofFrac])

/-- `fiv_cert?`: `fiv_cert`, reporting the numbers of nodes and kernel leaves. -/
macro "fiv_cert?" : tactic => `(tactic| eval_cert? [
  LeanTheory.Certificates.ValidatedQuadrature.FIv.add,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sub,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.neg,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.mul,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sq,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.inv,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sqrt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofInt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofFrac])

/-- **`fiv_decide`**: `eval_decide` (a decidable closed proposition, by the certificate of its
`decide`) with the `FIv` interval operations as kernel leaves. -/
macro "fiv_decide" : tactic => `(tactic| eval_decide [
  LeanTheory.Certificates.ValidatedQuadrature.FIv.add,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sub,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.neg,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.mul,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sq,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.inv,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.sqrt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofInt,
  LeanTheory.Certificates.ValidatedQuadrature.FIv.ofFrac])

/-- **Sanity** (accepted): `√2` and `1/(1/3 + 1/3)` as interval evaluations. -/
theorem fivCert_fixture :
    ((FIv.ofInt 2).sqrt.add ((FIv.ofFrac 1 3).add (FIv.ofFrac 1 3)).inv).ok = true := by
  fiv_cert

/-- **Sanity** of `fiv_decide`: a validity flag and a width bound. -/
theorem fivDecide_fixture :
    (FIv.ofInt 2).sqrt.ok = true ∧ (FIv.ofInt 2).sqrt.hi - (FIv.ofInt 2).sqrt.lo ≤ 4 := by
  fiv_decide

/-- **Sanity** (rejected): the inverse of an interval containing `0` is not valid. -/
theorem fivCert_reject_fixture : True := by
  fail_if_success (have : (FIv.ofFrac (-1) 2).inv.ok = true := by fiv_cert)
  trivial

end LeanTheory.Certificates.EvalCert
