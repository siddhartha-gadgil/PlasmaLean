/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.RationalStellaratorGCEwConfined

/-!
# Passing alpha guiding centres over an energy window: the (energy × pitch angle) family (top)

Top module of the energy-window certificate (not imported by `PlasmaLean.lean`; build it with
`lake build PlasmaLean.Design.RationalStellaratorGCEwFamily`; about 70 CPU-minutes, 343 modules;
the kernel checks of the node pipelines peak at 5–8.8 GB per process, everything else ≤ 3 GB):

* `Theory/KAM/ParamInterp`: differentiability of polynomial expressions with inverse-square-root
  nodes in a complex parameter, Cauchy coefficient bounds, and **interpolation with an analytic
  remainder** (`norm_sub_interp_le`, strip version `Bd_interp`);
* `Design/RationalStellaratorGCEw{1,2,3,4}*H`: the λ-family ball pipelines of four node tori at
  `ρ_j = 1/256 + t_j 2⁻³²`, `t_j ∈ {−1, −5/16, 5/16, 1}` (the fields at `ρ_j` are the nodes `DtJ`,
  `nRtJ`, `nZtJ`), and their residuals (`…EwNodes`);
* `…EwComb*`: kernel-checked norms of the coefficients `C_k` of the Lagrange family in `s`;
* `…EwInterp`, `…EwDisc`, `…EwRes`: the residual `≤ 7 × 10⁻²¹` of the family for every `|s| ≤ 1`;
* `…EwAdm`, `…EwMaj`, `…EwConst`, `…EwExact`: the KAM hypotheses over the window and
  **`ew_family_torus`**;
* `…EwForever`, `…EwConfined`: trapping, the guiding-centre bootstrap and
  **`alpha_gc_confined_forever_energy_window`** (every `E` with `|E − 3.5 MeV| ≤ 0.4 eV`, every
  `μ ∈ [0, E/(16B₀)]`, fixed design `B₀R₀`), **`alphaEwVel_volume_pos`**.

Scope: Littlejohn guiding-centre model, non-relativistic, collisionless, static vacuum model field
`field (1/4)` (not coil-produced).

**Sanity.** `ew_window_sanity`: the window contains the design energy and has half-width
`≥ 0.4 eV`, i.e. `(1 + 2⁻²⁴)² − 1 ≥ 0.4/3.5 × 10⁻⁶`.
-/

@[expose] public section

namespace PlasmaLean.Design.RationalStellaratorGC

/-- **Sanity**: `(1 − 2⁻²⁴)² ≤ 1 − 0.4/3.5 × 10⁻⁶` and `1 + 0.4/3.5 × 10⁻⁶ ≤ (1 + 2⁻²⁴)²`. -/
theorem ew_window_sanity : ((1 : ℝ) - 1 / 2 ^ 24) ^ 2 ≤ 1 - 0.4 / 3.5e6 ∧
    (1 : ℝ) + 0.4 / 3.5e6 ≤ (1 + 1 / 2 ^ 24) ^ 2 := by
  constructor <;> norm_num

end PlasmaLean.Design.RationalStellaratorGC
