/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkKamCFinal
public import PlasmaLean.Design.DommaschkKamCQSIdent

/-!
# Certified quasi-axisymmetry defect on the C1 torus of the Dommaschk field (N-34, D7)

On-demand top module (not imported by `PlasmaLean.lean`): build with
`lake build PlasmaLean.Design.DommaschkKamCQS` after its on-demand dependencies
(`DommaschkKamCFinal`, `DommaschkKamCQSIdent`; build stale dependencies one at a time). Axioms
are checked in `scripts/check_axioms_heavy.lean`.

**`dommaschk_C1_qaDefect`** (unconditional): the exact Dommaschk vacuum field
`DommaschkQA2R.field candidate` has a certified invariant torus `cylTorus R Z` with rotational
transform `ι_C = −(85 + √5)/361` (`IotaOnTorus`), on which
* the per-torus quasi-axisymmetry defect `torusQADefect = ∂_{φ_B}|B|` (A1,
  `Theory/Fields/VacuumBoozerTorus`) is bounded by `21/1000` everywhere,
* `|B| ≥ 1.04259`, `B^φ > 0`, and the chart hypotheses of the spectral bound hold.

**`dommaschk_C1_oracleDefect`**: hence, by the spectral bound (A2, `torus_oracleDefect_le`), the
off-QA Boozer spectral defect in the oracle's normalisation, over any finite set of off-QA modes,
is at most `√2 · 0.020642/(2 · 1.04259) ≈ 0.0140`, i.e. about `0.058 |ι|` (sup route).

Scope: one certified torus (a thin core, `r_eff ≈ 0.02`). The sup route gives defect/|ι| ≈ 0.058,
just outside the moderate tier of Q-16 (0.05); the L² route (certified `δ₂ ≤ 0.00224`) gives
≈ 0.0063 |ι|, strong tier: `DommaschkKamCQSL2.dommaschk_C1_oracleDefect_L2`. No C2 statement is made (audit item AC-1: the omnigeneity contract is not
yet tied to the physical field).
-/

public section
noncomputable section
namespace PlasmaLean.Design.DommaschkKamC
open PlasmaLean.Theory.KAM PlasmaLean.Design.KamNewton PlasmaLean.Contract
open PlasmaLean.Fields.VacuumBoozer

/-- **C1 torus with a certified quasi-axisymmetry defect**, unconditionally. -/
theorem dommaschk_C1_qaDefect :
    ∃ R Z : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R Z DommaschkKamDio.dkIotaC ∧
      TorusQADefectLe (DommaschkQA2R.field DommaschkQA2R.candidate) DommaschkKamDio.dkIotaC
        (cylTorus R Z) (21 / 1000) ∧
      (∀ θ φ, (Bminq : ℝ) ≤ ‖DommaschkQA2R.field DommaschkQA2R.candidate (cylTorus R Z θ φ)‖) ∧
      (∀ θ φ, 0 < toroidalComp (DommaschkQA2R.field DommaschkQA2R.candidate) (cylTorus R Z) θ φ) ∧
      BoozerChartHyp 2 DommaschkKamDio.dkIotaC
        (torusPot (DommaschkQA2R.potential DommaschkQA2R.candidate) (cylTorus R Z))
        (torusModB (DommaschkQA2R.field DommaschkQA2R.candidate) (cylTorus R Z)) :=
  dommaschk_qaDefect (Bd_weaken dk_e0R e0q_le_budget) (Bd_weaken dk_e0Z e0q_le_budget)

/-- **Oracle-normalised off-QA Boozer spectral defect on the C1 torus** (sup route): for every
finite set `S` of off-QA modes (`OracleOffQA`), `oracleDefect ≤ √2 · δ/(2 · Bmin)` with the
certified `δ = deltaq = 0.020642` and `Bmin = Bminq = 1.04259`. -/
theorem dommaschk_C1_oracleDefect :
    ∃ R Z : ℝ → ℝ → ℝ,
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) R Z DommaschkKamDio.dkIotaC ∧
      ∀ S : Finset (ℤ × ℤ), (∀ q ∈ S, OracleOffQA q) →
        oracleDefect 2 DommaschkKamDio.dkIotaC
          (torusPot (DommaschkQA2R.potential DommaschkQA2R.candidate) (cylTorus R Z))
          (torusModB (DommaschkQA2R.field DommaschkQA2R.candidate) (cylTorus R Z)) S ≤
          Real.sqrt 2 * deltaq / ((2 : ℕ) * Bminq) := by
  obtain ⟨u, z, hu, hz, hur, hzr, hR, hZ, hC⟩ :=
    dk_exact_of_res (Bd_weaken dk_e0R e0q_le_budget) (Bd_weaken dk_e0Z e0q_le_budget)
  have h : ExactTorusC u z := ⟨hu, hz, hur, hzr, hR, hZ, hC⟩
  exact ⟨_, _, h.iotaOnTorus, fun S hS => h.oracleDefect_le S hS⟩

/-- The certified bound in numbers: `√2 · 0.020642/(2 · 1.04259) < 0.0141`. -/
theorem oracleDefect_bound_num : Real.sqrt 2 * deltaq / ((2 : ℕ) * Bminq) < (141 : ℝ) / 10000 := by
  have h2 : Real.sqrt 2 < 14143 / 10000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hB : (0 : ℝ) < Bminq := by norm_num [Bminq]
  rw [div_lt_iff₀ (by positivity)]
  have : Real.sqrt 2 * deltaq < (14143 / 10000) * deltaq :=
    mul_lt_mul_of_pos_right h2 (by norm_num [deltaq])
  calc Real.sqrt 2 * deltaq < (14143 / 10000) * deltaq := this
    _ ≤ 141 / 10000 * ((2 : ℕ) * Bminq) := by norm_num [deltaq, Bminq]

end PlasmaLean.Design.DommaschkKamC
