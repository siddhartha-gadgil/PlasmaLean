/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.KamTorusAExact
public import PlasmaLean.Design.KamFlowIterationG

/-!
# Torus A through the generalised KAM interface (chain sanity for N-33)

The certified hypotheses `cA_kamH` of the K3d theorem (`Design/KamTorusAExact`) instantiate the
generalised KAM theorem `FlowFieldG.KamHG.kam_flow_torus` (`Design/KamFlowIterationG`) for
`field14G = field14.toG` (`R₀ = 1`, `p = 3`, fixed centre) with the constants `cA.toSCG`
(`FlowField.KamH.toG`, which needs `e δ₀ ≤ 1`; here `δ₀ = r_A/7 ≈ 0.018`, `cA_exp_δ0`). The
generalised constants `cK`, `cL`, `κ` are the certified ones.

**Result** (`torusA_exactG`): an exact real analytic invariant torus of `field14G` on the strip
`r_A/7`, `10⁻¹⁰`-close to torus A; via `field14G_invariant_iff` this is exactly the conclusion of
`torusA_exact` (`torusA_exact_viaG`). Moreover the generalised iteration *is* the old one
(`FlowField.toG_iterK`), so the limit torus is the same.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.KamNewton

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamTorusA

/-- The loss condition `e δ₀ ≤ 1` for torus A (`δ₀ = r_A/7 ≈ 0.018`). -/
theorem cA_exp_δ0 : Real.exp 1 * cA.δ0 ≤ 1 := by
  have := Real.exp_one_lt_d9
  simp only [cA, δ0A, rA]
  norm_num at this ⊢
  nlinarith

/-- **The certified torus-A hypotheses as generalised ones.** -/
theorem cA_kamHG : field14G.KamHG cA.toSCG iota u₀ z₀ e0A μA :=
  FlowField.KamH.toG cA_kamH cA_exp_δ0

/-- **Sanity**: the generalised constants of torus A are the certified ones. -/
theorem cA_toSCG_consts : cA.toSCG.cK = cA.cK ∧ cA.toSCG.cL = cA.cL ∧ cA.toSCG.kap = cA.kap :=
  ⟨cA.toSCG_cK, cA.toSCG_cL, cA.toSCG_kap⟩

/-- **An exact invariant torus of `field14G` near torus A, through the generalised KAM theorem.**
-/
theorem torusA_exactG :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ field14G.resR iota u z = 0 ∧
      field14G.resZ iota u z = 0 ∧ Close (rA / 7) iota u z u₀ z₀ μA := by
  have := cA_kamHG.kam_flow_torus
  rwa [show rInf cA.toSCG.toSC = rA / 7 from rInf_cA] at this

/-- **Re-derivation of `torusA_exact`** (same statement) from the generalised theorem, via
`field14G_invariant_iff`. -/
theorem torusA_exact_viaG :
    ∃ u z : FA, Ana u ∧ Ana z ∧ IsReal u ∧ IsReal z ∧ resR iota u z = 0 ∧
      resZ iota u z = 0 ∧ Close (rA / 7) iota u z u₀ z₀ μA := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ := torusA_exactG
  obtain ⟨hR', hZ'⟩ := (field14G_invariant_iff iota u z).1 ⟨hR, hZ⟩
  exact ⟨u, z, hu, hz, hur, hzr, hR', hZ', hC⟩

/-- **Sanity**: the generalised iterates for torus A are the certified ones (so the two limit
tori coincide). -/
theorem torusA_iterK_G (n : ℕ) : field14G.iterK iota u₀ z₀ n = field14.iterK iota u₀ z₀ n :=
  field14.toG_iterK iota u₀ z₀ n

end PlasmaLean.Design.KamNewton
