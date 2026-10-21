/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCFamConfined

/-!
# Robust alpha confinement: the guiding-centre torus family (top module)

Top module of the certificate for the whole cell `ρ ∈ [63/16384, 65/16384]` of the guiding-centre
parameter (`B₀R₀ ∈ [67.95, 69.99] T·m` for 3.5 MeV alphas):

* `Certificates/KronBallCheb*`: Chebyshev series in `ρ` with ball coefficients (the parameter
  `ρ = ρ_c + h cos ϑ` as a third angle `w = e^{iϑ}`), their Kronecker images, norm bounds and
  complete ball-chain steps (`node3_fullN`, `norm3_fullN`, `center3_fullN`);
* `Design/RationalStellaratorGCFam{Data,Kv,Trees,Check}{H,L}*`: the stored Chebyshev coefficients
  and the kernel checks (light modules);
* `Design/RationalStellaratorGCFam{Env,Rel,Chain,Out}{H,L}`: the family ball chains;
* `Design/RationalStellaratorGCFamMaj`, `…Adm`, `…Exact`: the KAM hypotheses uniform over the cell
  and **`gc_family_torus`**;
* `Design/RationalStellaratorGCFamForever`, `…Confined`: trapping for every `ρ` of the cell and
  **`alpha_gc_confined_forever_robust`**.

Check it with `lake build PlasmaLean.Design.RationalStellaratorGCFamily`.

**Sanity.** `alpha_cell_sanity`: the design value `B₀R₀ = 69 T·m` lies in the certified interval.
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

/-- **Sanity**: the design value `B₀R₀ = 69 T·m` lies in the certified interval. -/
theorem alpha_cell_sanity : (67.95 : ℝ) ≤ 69 ∧ (69 : ℝ) ≤ 69.99 := by norm_num

end PlasmaLean.Design.RationalStellaratorGC
