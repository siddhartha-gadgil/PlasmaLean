/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.SolovevBallooningData
public import PlasmaLean.Certificates.EvalCert

/-!
# Evaluation certificates for the Solov'ev ballooning corner tests (`bl_cert`)

`bl_cert` is `eval_cert` (`Certificates/EvalCert.lean`) with the fixed-point ball operations of
`Design/SolovevBallooningDefs` (`Bl.ofInt`, `ofFrac`, `add`, `neg`, `sub`, `dbl`, `mul`, `sq`,
`inv`, `sqrt`, `ofLoHi`, `lo`, `hi`, `mag`) as kernel leaves: each node of a corner test
`cornerOK` is one ball operation applied to ball values, and the expression-tree recursions
(`Tm.ieval`), the list maps and the Pólya tests are unfolded into `ECert` steps.

**Sanity.** `blCert_fixture` (accepted), `blCert_reject_fixture` (rejected).
-/

public section

namespace PlasmaLean.Design.SolovevBallooning

/-- **`bl_cert`**: `eval_cert` with the `Bl` ball operations as kernel leaves. -/
macro "bl_cert" : tactic => `(tactic| eval_cert [
  PlasmaLean.Design.SolovevBallooning.Bl.ofInt,
  PlasmaLean.Design.SolovevBallooning.Bl.ofFrac,
  PlasmaLean.Design.SolovevBallooning.Bl.add,
  PlasmaLean.Design.SolovevBallooning.Bl.neg,
  PlasmaLean.Design.SolovevBallooning.Bl.sub,
  PlasmaLean.Design.SolovevBallooning.Bl.dbl,
  PlasmaLean.Design.SolovevBallooning.Bl.mul,
  PlasmaLean.Design.SolovevBallooning.Bl.sq,
  PlasmaLean.Design.SolovevBallooning.Bl.inv,
  PlasmaLean.Design.SolovevBallooning.Bl.sqrt,
  PlasmaLean.Design.SolovevBallooning.Bl.ofLoHi,
  PlasmaLean.Design.SolovevBallooning.Bl.lo,
  PlasmaLean.Design.SolovevBallooning.Bl.hi,
  PlasmaLean.Design.SolovevBallooning.Bl.mag])

/-- `bl_cert?`: `bl_cert`, reporting the numbers of nodes and kernel leaves. -/
macro "bl_cert?" : tactic => `(tactic| eval_cert? [
  PlasmaLean.Design.SolovevBallooning.Bl.ofInt,
  PlasmaLean.Design.SolovevBallooning.Bl.ofFrac,
  PlasmaLean.Design.SolovevBallooning.Bl.add,
  PlasmaLean.Design.SolovevBallooning.Bl.neg,
  PlasmaLean.Design.SolovevBallooning.Bl.sub,
  PlasmaLean.Design.SolovevBallooning.Bl.dbl,
  PlasmaLean.Design.SolovevBallooning.Bl.mul,
  PlasmaLean.Design.SolovevBallooning.Bl.sq,
  PlasmaLean.Design.SolovevBallooning.Bl.inv,
  PlasmaLean.Design.SolovevBallooning.Bl.sqrt,
  PlasmaLean.Design.SolovevBallooning.Bl.ofLoHi,
  PlasmaLean.Design.SolovevBallooning.Bl.lo,
  PlasmaLean.Design.SolovevBallooning.Bl.hi,
  PlasmaLean.Design.SolovevBallooning.Bl.mag])

/-- **Sanity** (accepted): `√2 · √2 + 1/2` as a ball evaluation is a valid ball. -/
theorem blCert_fixture : (sqrt2B.mul sqrt2B |>.add (Bl.ofFrac 1 2)).ok = true := by
  bl_cert

/-- **Sanity** (rejected): the reciprocal of a ball containing `0` is not valid. -/
theorem blCert_reject_fixture : True := by
  fail_if_success (have : (Bl.ofFrac (-1) 2).inv.ok = true := by bl_cert)
  trivial

end PlasmaLean.Design.SolovevBallooning
