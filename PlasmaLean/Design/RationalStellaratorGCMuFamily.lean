/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCMuConfined

/-!
# Top module: `μ > 0` passing guiding centres confined forever (pitch-angle cell `λ ∈ [0, 1/16]`)

This module collects the `μ > 0` passing-family certificate (`Design/RationalStellaratorGCMu*`):

* the field: `gcFieldMu ρ₀ λ = B + ∇×(ρ(x) b)`, `ρ = ρ₀√(1 − λ|B|)`, equal to the modified field
  `modFieldFn (rhoE …)` of the Littlejohn passing reduction (`modFieldFn_rhoE_eq`), with flow form
  `gcFlowMu` and its divergence/flux identities (`gcMu_divFree`, `gcMu_flux_*`);
* a Chebyshev family in `λ` (degree 12, 13 coefficients) of KAM tori and a ball-arithmetic
  certificate over the whole cell `λ ∈ [0, 1/16]` (`RationalStellaratorGCMuData*`, `…Check*`, …);
* exact tori for every `λ` (`mu_family_torus`), trapping (`mu_family_master`), the bootstrap
  `littlejohn_mu_eq_fieldLine` and the final theorems `rationalStellarator_gc_mu_confined_forever`,
  `gc_mu_passing_confined_forever_SI`, `alpha_gc_passing_confined_forever`.

It is imported by `PlasmaLean.lean`. Its cost, about
28 CPU-minutes sequentially with a peak of 5.5 GB per process
(`notes/theory/gc-kam-status.md`), is within the default-build budget. Build it with
`lake build PlasmaLean.Design.RationalStellaratorGCMuFamily`.

**Sanity.** `mu_family_sanity`: at `λ = 0` the field is the `μ = 0` guiding-centre field.
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

/-- **Sanity**: at `λ = 0` the `μ > 0` field of the cell is `gcField (1/256)`. -/
theorem mu_family_sanity : gcFieldMu (1 / 256) 0 = gcField (1 / 256) := mu_family_lam_zero

end PlasmaLean.Design.RationalStellaratorGC
