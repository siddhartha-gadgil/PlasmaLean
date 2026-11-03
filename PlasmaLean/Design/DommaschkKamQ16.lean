/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamNested
public import PlasmaLean.Design.DommaschkKamCQSL2
public import PlasmaLean.Design.DommaschkKamAQSL2

/-!
# The vacuum Q-16 criterion for the Dommaschk field on the nested pair of tori {C, A}

On-demand top module (not imported by `PlasmaLean.lean`). Build:
`lake build PlasmaLean.Design.DommaschkKamQ16` after `DommaschkKamNested`,
`DommaschkKamCQSL2` and `DommaschkKamAQSL2` (build stale dependencies one at a time). Axioms are
checked in `scripts/check_axioms_heavy.lean`. Research notes `notes/theory/dommaschk-qs-defect.md`
(N-34) and `notes/theory/kamflow-g-status.md`.

**Q-16 (vacuum)** asks for certified invariant tori on a nested region, with `|ι| ≥ ι_min` and a
certified quasi-axisymmetry defect small relative to `|ι|`. For the exact Dommaschk vacuum field
`B = DommaschkQA2R.field candidate` (potential `V = DommaschkQA2R.potential candidate`):

* **`dommaschk_Q16_vacuum`**: there are two surfaces `s_C`, `s_A` (`SurfaceData`) built from one
  pair of exact tori C (inner, `ι_C = −(85 + √5)/361`) and A (outer, `ι_A = −(19 + √5)/89`):
  * both are certified invariant tori (`IotaOnTorus`), nested about a common reference curve
    (`DommaschkKamNested.NestedTori`);
  * `|ι| ≥ 0.2386` on both, and the C1 clause (zero net current, `ι_min = 0.2386`) holds on the
    family `{s_C, s_A}` for every `μ₀ > 0` (as `dommaschk_nested_C1`, for the same two tori);
  * the per-torus QA defect `torusQADefect = ∂_{φ_B}|B|` is certified (`|g| ≤ 0.021` on C,
    `≤ 0.032` on A) with `|B| ≥ 1.04259` on C and `|B| ≥ 1.02656` on A;
  * the off-QA Boozer spectral defect in the oracle's normalisation, for every finite set of
    half-lattice off-QA modes, is `≤ 0.0063 |ι_C|` on C and `≤ 0.0090 |ι_A|` on A
    (`L²(J)` route: `(√2/2) δ₂/B_min` with `δ₂ = 0.002244`, `0.0031112`).
* **`dommaschk_Q16_strong`**: hence the **strong tier** `defect ≤ 0.01 |ι|` on both tori.

Scope: two thin certified tori (`r_eff ≈ 0.02` and `0.037`); this is a statement about the exact
field on the two surfaces, not omnigeneity of a region (no C2 claim, audit AC-1). The untrusted
oracle estimate of the same defect is about `0.002 |ι|` on both tori; the certified bounds are
about 3–4.5 times larger.

**Sanity.** `q16_bounds_lt_strong` (accepted: both certified ratios are below the strong tier),
`not_q16_C_tiny` (rejected: the certified C ratio does not reach `0.001 |ι|`).
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkKamQ16

open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract WEll1Z2
open PlasmaLean.Fields.VacuumBoozer
open PlasmaLean.Design.DommaschkKamNested (NestedTori nested_of_exact)
open PlasmaLean.Design.DommaschkKamC (RofC ExactTorusC surfaceC)
open PlasmaLean.Design.DommaschkKamA (ExactTorusA surfaceA)

/-- The field `B = ∇φ + Σ a_k ∇V_k` of the Dommaschk target (local notation). -/
local notation "Bdk" => DommaschkQA2R.field DommaschkQA2R.candidate

/-- The potential `V = Σ a_k V_k` of the Dommaschk target (local notation). -/
local notation "Vdk" => DommaschkQA2R.potential DommaschkQA2R.candidate

/-- **C1 on the pair `{C, A}` of given exact tori** (the argument of `dommaschk_nested_C1`). -/
theorem nested_C1_of_exact {uC zC uA zA : FA} (hC : ExactTorusC uC zC) (hA : ExactTorusA uA zA)
    {μ₀ : ℝ} (hμ : 0 < μ₀) :
    CurrentFreeTransform μ₀ Bdk {surfaceC uC zC, surfaceA uA zA} 0 (1193 / 5000) := by
  have hιC : (1193 / 5000 : ℝ) ≤ |DommaschkKamDio.dkIotaC| :=
    le_trans (by norm_num) DommaschkKamC.iotaC_ge
  refine DommaschkQA2R.candidate_currentFreeTransform hμ (Set.insert_nonempty _ _) (by norm_num)
    ?_ ?_ ?_ ?_
  · rintro s (rfl | rfl)
    · exact DommaschkKamA.ExactTorusC'.iotaOnTorusRef hC
    · exact hA.iotaOnTorus
  · rintro s (rfl | rfl)
    · exact ((DommaschkKamC.contDiff_RofC hC.ana_u).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)
    · exact ((DommaschkKamC.contDiff_RofC hA.ana_u).comp
        (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)
  · rintro s (rfl | rfl)
    · exact ((contDiff_Zof hC.ana_z).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num)
    · exact ((contDiff_Zof hA.ana_z).comp (contDiff_id.prodMk contDiff_const)).of_le
        (by norm_num)
  · rintro s (rfl | rfl)
    · exact hιC
    · exact DommaschkKamA.iotaA_ge

/-- `B_min` of torus C as a decimal. -/
theorem BminC_eq : ((DommaschkKamC.Bminq : ℚ) : ℝ) = 104259 / 100000 := by
  norm_num [DommaschkKamC.Bminq]

/-- `B_min` of torus A as a decimal. -/
theorem BminA_eq : ((DommaschkKamA.Bminq : ℚ) : ℝ) = 102656 / 100000 := by
  norm_num [DommaschkKamA.Bminq]

/-- **The vacuum Q-16 criterion on the nested pair {C, A}** of the exact Dommaschk field: two
certified invariant tori (inner C with `ι_C`, outer A with `ι_A`), nested about a common
reference curve, with `|ι| ≥ 0.2386` and the C1 clause on `{C, A}`, the certified per-torus QA
defect (`≤ 0.021` on C, `≤ 0.032` on A) and `|B|` bounds, and the certified off-QA Boozer
spectral defect `≤ 0.0063 |ι_C|` on C and `≤ 0.0090 |ι_A|` on A. -/
theorem dommaschk_Q16_vacuum :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      -- two certified invariant tori, nested
      IotaOnTorus Bdk sC.R sC.z sC.iota ∧ IotaOnTorus Bdk sA.R sA.z sA.iota ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA ∧
      -- the transform bound and clause C1 on the family {C, A}
      (1193 / 5000 : ℝ) ≤ |sC.iota| ∧ (1193 / 5000 : ℝ) ≤ |sA.iota| ∧
      (∀ μ₀ : ℝ, 0 < μ₀ → CurrentFreeTransform μ₀ Bdk {sC, sA} 0 (1193 / 5000)) ∧
      -- the certified per-torus QA defect and `|B|`
      TorusQADefectLe Bdk sC.iota (cylTorus sC.R sC.z) (21 / 1000) ∧
      TorusQADefectLe Bdk sA.iota (cylTorus sA.R sA.z) (32 / 1000) ∧
      (∀ θ φ, (104259 / 100000 : ℝ) ≤ ‖Bdk (cylTorus sC.R sC.z θ φ)‖) ∧
      (∀ θ φ, (102656 / 100000 : ℝ) ≤ ‖Bdk (cylTorus sA.R sA.z θ φ)‖) ∧
      -- the certified off-QA Boozer spectral defect relative to `|ι|`
      (∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 sC.iota (torusPot Vdk (cylTorus sC.R sC.z))
          (torusModB Bdk (cylTorus sC.R sC.z)) S ≤ (63 / 10000 : ℝ) * |sC.iota|) ∧
      (∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 sA.iota (torusPot Vdk (cylTorus sA.R sA.z))
          (torusModB Bdk (cylTorus sA.R sA.z)) S ≤ (90 / 10000 : ℝ) * |sA.iota|) := by
  obtain ⟨uC, zC, huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩ :=
    DommaschkKamC.dk_exact_of_res
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0R DommaschkKamC.e0q_le_budget)
      (DommaschkKamC.Bd_weaken DommaschkKamC.dk_e0Z DommaschkKamC.e0q_le_budget)
  obtain ⟨uA, zA, hA⟩ := DommaschkKamA.exists_exactTorusA
  have hC : ExactTorusC uC zC := ⟨huC, hzC, hurC, hzrC, hRC, hZC, hCC⟩
  have bC : ∀ θ φ, (104259 / 100000 : ℝ) ≤ ‖Bdk (cylTorus (RofC uC) (Zof zC) θ φ)‖ := fun θ φ => by
    have h1 := hC.Bmin_le θ φ
    rw [BminC_eq] at h1
    exact h1
  have bA : ∀ θ φ, (102656 / 100000 : ℝ) ≤ ‖Bdk (cylTorus (RofC uA) (Zof zA) θ φ)‖ := fun θ φ => by
    have h1 := hA.Bmin_le θ φ
    rw [BminA_eq] at h1
    exact h1
  refine ⟨surfaceC uC zC, surfaceA uA zA, _, _, _, _, rfl, rfl,
    DommaschkKamA.ExactTorusC'.iotaOnTorusRef hC, hA.iotaOnTorus, nested_of_exact hC hA,
    le_trans (by norm_num) DommaschkKamC.iotaC_ge, DommaschkKamA.iotaA_ge,
    fun μ₀ hμ => nested_C1_of_exact hC hA hμ, hC.torusQADefectLe_021, hA.torusQADefectLe_032,
    ?_,
    ?_,
    fun S hS => (hC.oracleDefect_le_L2 S hS).trans DommaschkKamC.oracleDefect_L2_num.2.2,
    fun S hS => (hA.oracleDefect_le_L2 S hS).trans DommaschkKamA.oracleDefectA_L2_num.2.2⟩
  · intro θ φ
    dsimp only [surfaceC]
    exact bC θ φ
  · intro θ φ
    dsimp only [surfaceA]
    exact bA θ φ

/-- **Sanity (accepted)**: both certified ratios lie below the strong tier `0.01`. -/
theorem q16_bounds_lt_strong : (63 / 10000 : ℝ) ≤ 1 / 100 ∧ (90 / 10000 : ℝ) ≤ 1 / 100 := by
  norm_num

/-- **Sanity (rejected)**: the certified C bound `(√2/2) δ₂/B_min` is not below `0.001 |ι_C|`
for any `|ι_C| ≤ 1/4` (the certified numbers do not prove a ten times smaller defect). -/
theorem not_q16_C_tiny :
    ¬ (14143 / 20000 * DommaschkKamC.delta2q / DommaschkKamC.Bminq ≤ 1 / 1000 * (1 / 4)) := by
  norm_num [DommaschkKamC.delta2q, DommaschkKamC.Bminq]

/-- **The strong tier of Q-16 on the nested pair {C, A}**: two nested certified invariant tori of
the exact Dommaschk field with `|ι| ≥ 0.2386` and certified off-QA Boozer spectral defect
`≤ 0.01 |ι|` on both. -/
theorem dommaschk_Q16_strong :
    ∃ (sC sA : SurfaceData) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      sC.iota = DommaschkKamDio.dkIotaC ∧ sA.iota = DommaschkKamDio.dkIotaA ∧
      IotaOnTorus Bdk sC.R sC.z sC.iota ∧ IotaOnTorus Bdk sA.R sA.z sA.iota ∧
      NestedTori sC.R sC.z sA.R sA.z R₀ z₀ ΘC ΘA ∧
      (1193 / 5000 : ℝ) ≤ |sC.iota| ∧ (1193 / 5000 : ℝ) ≤ |sA.iota| ∧
      ∀ s ∈ ({sC, sA} : Set SurfaceData), ∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 s.iota (torusPot Vdk (cylTorus s.R s.z))
          (torusModB Bdk (cylTorus s.R s.z)) S ≤ (1 / 100 : ℝ) * |s.iota| := by
  obtain ⟨sC, sA, R₀, z₀, ΘC, ΘA, e1, e2, i1, i2, hN, g1, g2, -, -, -, -, -, dC, dA⟩ :=
    dommaschk_Q16_vacuum
  refine ⟨sC, sA, R₀, z₀, ΘC, ΘA, e1, e2, i1, i2, hN, g1, g2, ?_⟩
  rintro s (rfl | rfl) S hS
  · exact (dC S hS).trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))
  · exact (dA S hS).trans (mul_le_mul_of_nonneg_right (by norm_num) (abs_nonneg _))

end PlasmaLean.Design.DommaschkKamQ16
