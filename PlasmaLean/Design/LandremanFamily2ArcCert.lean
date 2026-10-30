/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.LandremanFamily2Quad
public import PlasmaLean.Certificates.EvalCertFIv

/-!
# Evaluation certificate for one outer-arc contribution of the family-2 Mercier checker

The tactic macro `f2_arc_cert` proves `outerArc … a = O` for a literal enclosure `O` by an
explicit evaluation certificate (`eval_cert`), after unfolding the `let`s of `tipCell`,
`sideCell` and `arcSC` with `simp`. Shared by the accepted-cell certificates
`PlasmaLean.Design.LandremanFamily2Cert1`–`Cert7` and the rejected fixtures
`PlasmaLean.Design.LandremanFamily2MercierStableA`/`B`.
-/

public section

namespace PlasmaLean.Design.LandremanFamily2Cert

open PlasmaLean.Certificates.ValidatedQuadrature PlasmaLean.Design.LandremanFamily2Quad

/-- **`f2_arc_cert`**: the evaluation certificate of one outer-arc contribution
`outerArc … a = O`. The `let`s of `tipCell`, `sideCell` and `arcSC` and the arc selection are
first unfolded by `simp` (so that every shared subterm is evaluated once by the builder), then
`eq3 (outerArc …) O = true` is certified by `eval_cert` with the interval operations and the
fast enclosures of `oned_cert` (plus `FIv.atanFast`, `FIv.sinhSmall`) as kernel leaves. -/
macro "f2_arc_cert" : tactic => `(tactic| (
  simp only [outerArc, innerSum, tipCell, sideCell, arcSC, Fin.isValue, Fin.reduceEq,
    ↓reduceIte]
  apply eq3_sound
  eval_cert [
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.add,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.sub,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.neg,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.mul,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.sq,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.inv,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.sqrt,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.ofInt,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.ofFrac,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.asinFast,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.atanFast,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.coshSmall,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.sinhSmall,
    PlasmaLean.Certificates.ValidatedQuadrature.FIv.divInt]))

end PlasmaLean.Design.LandremanFamily2Cert
