/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.KAM.DiophantineB

/-!
# The dyadic rotational transform of the `v∥ < 0` guiding-centre torus

The ball certificate of the guiding-centre torus at `ρ_s = −1/256`
(`Design/RationalStellaratorGCNegTorus*`) evaluates the transport operator with the dyadic
approximation `ι_q = IqB / 2^96` of `ι_B = (161 − √5)/1178` (`Theory/KAM/DiophantineB`); the error
`(ι_B − ι_q) ∂_θ K` is added to the ball radius (`iotaB_sub_iotaBq`: `|ι_B − ι_q| ≤ 10⁻²⁹`).

**Sanity.** `iotaBq_bounds`: `0.13477 < ι_q < 0.13478`, the enclosure of `ι_B`.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.RationalStellaratorGCNeg

open PlasmaLean.Theory.KAM

/-- Numerator of `ι_q = IqB / 2^96 ≈ (161 − √5)/1178`. -/
def IqB : ℕ := 10677907137251496300733849141

/-- The dyadic approximation `ι_q = IqB / 2^96` of `ι_B`. -/
def iotaBq : ℝ := (IqB : ℝ) / 2 ^ 96

/-- `IqB = 2^96 ι_q` in `ℂ`. -/
theorem IqB_eq : (IqB : ℂ) = 2 ^ 96 * (iotaBq : ℂ) := by
  simp only [iotaBq]; push_cast; field_simp

/-- `|ι_B − ι_q| ≤ 10⁻²⁹`. -/
theorem iotaB_sub_iotaBq : |iotaB - iotaBq| ≤ 1 / 10 ^ 29 := by
  have hlo : (161 - 1178 * ((IqB : ℝ) / 2 ^ 96)) - 1178 / 10 ^ 29 ≤ Real.sqrt 5 := by
    rw [Real.le_sqrt (by norm_num [IqB]) (by norm_num)]; norm_num [IqB]
  have hhi : Real.sqrt 5 ≤ (161 - 1178 * ((IqB : ℝ) / 2 ^ 96)) + 1178 / 10 ^ 29 := by
    rw [Real.sqrt_le_left (by norm_num [IqB])]; norm_num [IqB]
  rw [abs_le, iotaB, iotaBq]
  constructor <;> linarith

/-- Sanity: `0.13477 < ι_q < 0.13478`. -/
theorem iotaBq_bounds : 13477 / 100000 < iotaBq ∧ iotaBq < 13478 / 100000 := by
  constructor <;> norm_num [iotaBq, IqB]

end PlasmaLean.Design.RationalStellaratorGCNeg
