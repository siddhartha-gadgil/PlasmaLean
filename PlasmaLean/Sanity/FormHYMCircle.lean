/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMCircle
public import PlasmaLean.Sanity.FormHYMLift
public import PlasmaLean.Sanity.FormHYMStar

/-!
# Sanity checks for the lift on `ℝ³ × S¹` (`Theory/Fields/FormHYMCircle`)

The fixtures for closedness and regularity are on the manifold `ℝ³ × AddCircle 1` with
TauCeti's `mextDeriv`; the integrated energy fixtures use `AddCircle 3` as well, so that the
factor `ℓ` is exercised.

1. **Accepted.** The lifts of constant 2-forms and of the hyperbolic vacuum field `(x, y, -2z)`
   are closed on `ℝ³ × S¹`, and the constant lift is a smooth form.
2. **Rejected, one fixture for each vacuum equation.** The lift of the rotation field
   `(-y, x, 0)` (divergence free, curl `2 e₂`) and the lift of the identity field (curl free,
   divergence `3`) are closed at no point of `ℝ³ × S¹`; the rotation lift is closed on the
   manifold `Ω × S¹` for no nonempty open `Ω`.
3. **Regularity has content.** The lift of a discontinuous field of forms is not a continuous
   form on `ℝ³ × S¹` (`discontinuous_circle_not_continuous`, with `¬ Continuous w` as a
   hypothesis). Regression (audit AV-M6): a concrete instance, the step field
   `1_{x₀ ≥ 0} dx₁ ∧ dx₂` (`stepForm_not_continuous`, `stepForm_circle_not_continuous`).
4. **Energy.** `|ℱ|² = 2` for the lift of `dx₁ ∧ dx₂` (restating `lift_e0_inner` of
   `Sanity/FormHYMStar` through the general identity), and the lifts of `dx₁ ∧ dx₂` and
   `dx₂ ∧ dx₀` are orthogonal.
5. **Regression (audit AV-M5): the integrated energy identity.** For the unit field `e₀` on
   the unit ball and `ℓ = 3`, `∫_{B × S¹} |ℱ|² = 2 · 3 · vol(B)` (`energy_ball_three`); for
   `ℓ = 1` it is `2 · 1 · vol(B)` (`energy_ball_one`), one third of the former
   (`energy_ball_one_eq_third`), so the total mass of `AddCircle ℓ` enters. Degenerate case
   `Ω = ∅`: `0` (`energy_empty`). Junk case: when `‖B‖²` is not integrable on `Ω` the lifted
   integral is `0` (`energy_junk`), for instance for the unit field on all of space, whose
   energy is infinite (`energy_univ_junk`).
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMCircle

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Sanity PlasmaLean.Sanity.Audit
  PlasmaLean.Sanity.Forms PlasmaLean.Fields Matrix TauCeti
open scoped Manifold

/-! ### Accepted fixtures -/

/-- The lift of a constant 2-form is closed on `ℝ³ × S¹`. -/
theorem const_circle_closed (b : Form 2) :
    mextDeriv (hymLiftCircleForm 1 fun _ => b) = 0 :=
  (hymLiftCircleForm_closed_iff_vacuumForm 1 contDiff_const).2 (const_vacuumForm isOpen_univ b)

/-- The lift of a constant 2-form is a smooth form on `ℝ³ × S¹`. -/
theorem const_circle_smooth (b : Form 2) :
    IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) ⊤ (hymLiftCircleForm 1 fun _ => b) :=
  isSmoothForm_hymLiftCircleForm 1 contDiff_const

/-- The lift of the hyperbolic vacuum field `(x, y, -2z)` is closed on `ℝ³ × S¹`. -/
theorem hyperbolic_circle_closed :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => hyperbolicField y)) = 0 :=
  (hymLiftCircleForm_closed_iff_vacuumForm 1
    (contDiffOn_univ.1 hyperbolic_vacuumForm.contDiffOn)).2 hyperbolic_vacuumForm

/-! ### Rejected fixtures -/

/-- The flux form of the rotation field is smooth. -/
theorem contDiff_flux_rotation {n : WithTop ℕ∞} :
    ContDiff ℝ n (fluxField fun y => rotationField y) :=
  flux.toContinuousLinearEquiv.contDiff.comp rotationField.contDiff

/-- The flux form of the identity field is smooth. -/
theorem contDiff_flux_id {n : WithTop ℕ∞} : ContDiff ℝ n (fluxField fun y : Euclid3 => y) :=
  flux.toContinuousLinearEquiv.contDiff.comp contDiff_id

/-- The rotation field is not curl free: its lift is closed at no point of `ℝ³ × S¹`. -/
theorem rotation_circle_not_closed (p : Space × AddCircle (1 : ℝ)) :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => rotationField y)) p ≠ 0 := by
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  intro h
  refine FormHYMLift.rotation_lift_not_closed (x, τ) ?_
  rw [← mextDeriv_hymLiftCircleForm_coe 1 contDiff_flux_rotation.contDiffAt τ]
  exact h

/-- The identity field is not divergence free: its lift is closed at no point of `ℝ³ × S¹`. -/
theorem id_circle_not_closed (p : Space × AddCircle (1 : ℝ)) :
    mextDeriv (hymLiftCircleForm 1 (fluxField fun y => y)) p ≠ 0 := by
  obtain ⟨x, θ⟩ := p
  obtain ⟨τ, rfl⟩ := QuotientAddGroup.mk_surjective θ
  intro h
  refine FormHYMLift.id_lift_not_closed (x, τ) ?_
  rw [← mextDeriv_hymLiftCircleForm_coe 1 contDiff_flux_id.contDiffAt τ]
  exact h

/-- On the manifold `Ω × S¹`, for a nonempty open `Ω`, the rotation lift is not closed. -/
theorem rotation_region_not_closed (U : TopologicalSpace.Opens Space)
    (hne : (U : Set Space).Nonempty) :
    mextDeriv (hymLiftRegionForm 1 U (fluxField fun y => rotationField y)) ≠ 0 := fun h =>
  rotation_not_vacuumForm hne
    ((hymLiftRegionForm_closed_iff_vacuumForm 1 U contDiff_flux_rotation.contDiffOn).1 h)

/-! ### Regularity has content -/

/-- A field of 2-forms that is not continuous has a lift that is not a continuous form on
`ℝ³ × S¹`. -/
theorem discontinuous_circle_not_continuous {w : Space → Form 2} (hw : ¬ Continuous w) :
    ¬ IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) 0 (hymLiftCircleForm 1 w) := fun h =>
  hw (contDiff_zero.1 ((isSmoothForm_hymLiftCircleForm_iff 1 w).1 h))

/-! ### Energy -/

/-- The squared norm of the lift of `dx₁ ∧ dx₂` is `2`, through the general identity
`|ℱ|² = 2 |B|²`. -/
theorem lift_e0_inner : liftInner (hymLiftAt (flux (coordVec 0)))
    (hymLiftAt (flux (coordVec 0))) = 2 := by
  rw [liftInner_hymLiftAt_flux_self]
  simp [coordVec]

/-- The lifts of `dx₁ ∧ dx₂` and `dx₂ ∧ dx₀` are orthogonal. -/
theorem lift_e0_e1_inner : liftInner (hymLiftAt (flux (coordVec 0)))
    (hymLiftAt (flux (coordVec 1))) = 0 := by
  rw [liftInner_hymLiftAt_flux]
  simp [coordVec, EuclideanSpace.inner_single_left]

/-- The Yang–Mills density of the lift of `dx₁ ∧ dx₂` is `1`, twice the magnetic energy density
`½` of the unit field `e₀`. -/
theorem lift_e0_ymDensity : ymDensity (hymLiftAt (flux (coordVec 0))) = 1 := by
  rw [ymDensity_hymLiftAt_flux]
  simp [coordVec]

/-! ### A concrete discontinuous field (audit AV-M6) -/

/-- The step field of 2-forms `1_{x₀ ≥ 0} dx₁ ∧ dx₂`: the flux form of the field that is `e₀`
on the half-space `x₀ ≥ 0` and `0` elsewhere. -/
def stepForm (y : Space) : Form 2 := (if 0 ≤ y 0 then (1 : ℝ) else 0) • flux (coordVec 0)

/-- The step field is not continuous: along the `x₀`-axis its component on `(e₁, e₂)` jumps
from `0` to `1` at the origin. -/
theorem stepForm_not_continuous : ¬ Continuous stepForm := by
  intro h
  have hc : Continuous (fun t : ℝ => t • (coordVec 0 : Space)) := by fun_prop
  have h1 : Continuous
      (fun t : ℝ => (flux.toContinuousLinearEquiv.symm (stepForm (t • coordVec 0)) : Space) 0) :=
    Continuous.comp (g := fun v : Space => v 0) (EuclideanSpace.proj (0 : Fin 3)).continuous
      (flux.toContinuousLinearEquiv.symm.continuous.comp (h.comp hc))
  have e : (fun t : ℝ => (flux.toContinuousLinearEquiv.symm (stepForm (t • coordVec 0)) : Space) 0)
      = fun t : ℝ => if 0 ≤ t then (1 : ℝ) else 0 := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [stepForm, ht]
  rw [e] at h1
  have l1 : Filter.Tendsto (fun t : ℝ => if 0 ≤ t then (1 : ℝ) else 0) (nhdsWithin 0 (Set.Iio 0))
      (nhds 1) := by
    have := h1.continuousAt (x := 0)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have l2 : Filter.Tendsto (fun t : ℝ => if 0 ≤ t then (1 : ℝ) else 0) (nhdsWithin 0 (Set.Iio 0))
      (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [not_le.2 ht]
  exact one_ne_zero (tendsto_nhds_unique l1 l2)

/-- **Regression (audit AV-M6): a concrete lift that is not a continuous form.** The lift of the
step field `1_{x₀ ≥ 0} dx₁ ∧ dx₂` to `ℝ³ × S¹` is not a continuous form. Unlike
`discontinuous_circle_not_continuous`, no discontinuity is assumed: it is proved
(`stepForm_not_continuous`). -/
theorem stepForm_circle_not_continuous :
    ¬ IsSmoothForm (𝓘(ℝ, Space).prod 𝓘(ℝ)) 0 (hymLiftCircleForm 1 stepForm) :=
  discontinuous_circle_not_continuous stepForm_not_continuous

/-! ### The integrated energy identity (audit AV-M5) -/

section Energy

open MeasureTheory

/-- `0 < 3`, for the circle `ℝ/3ℤ` of the energy fixtures. A proved local instance: nothing is
exported. -/
local instance fact_three_pos : Fact ((0 : ℝ) < 3) := ⟨by norm_num⟩

/-- **Regression (audit AV-M5): the integrated energy identity on the unit ball, `ℓ = 3`.** For
the unit field `e₀`, `∫_{B × (ℝ/3ℤ)} |ℱ|² = 2 · 3 · vol(B)`, with `B` the open unit ball: twice
the circumference times `∫_B |e₀|² = vol(B)`. -/
theorem energy_ball_three :
    ∫ p in Metric.ball (0 : Space) 1 ×ˢ (Set.univ : Set (AddCircle (3 : ℝ))),
        liftInner (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p)
          (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p) =
      2 * 3 * (volume (Metric.ball (0 : Space) 1)).toReal := by
  rw [integral_liftInner_hymLiftCircle]
  simp [coordVec, Measure.real]

/-- **Regression (audit AV-M5): the same integral with `ℓ = 1`** is `2 · 1 · vol(B)`. -/
theorem energy_ball_one :
    ∫ p in Metric.ball (0 : Space) 1 ×ˢ (Set.univ : Set (AddCircle (1 : ℝ))),
        liftInner (hymLiftCircle 1 (fluxField fun _ => coordVec 0) p)
          (hymLiftCircle 1 (fluxField fun _ => coordVec 0) p) =
      2 * 1 * (volume (Metric.ball (0 : Space) 1)).toReal := by
  rw [integral_liftInner_hymLiftCircle]
  simp [coordVec, Measure.real]

/-- **Regression (audit AV-M5): the total mass of `AddCircle ℓ` enters.** The energy integral
over `B × (ℝ/ℤ)` is one third of the integral over `B × (ℝ/3ℤ)`. -/
theorem energy_ball_one_eq_third :
    ∫ p in Metric.ball (0 : Space) 1 ×ˢ (Set.univ : Set (AddCircle (1 : ℝ))),
        liftInner (hymLiftCircle 1 (fluxField fun _ => coordVec 0) p)
          (hymLiftCircle 1 (fluxField fun _ => coordVec 0) p) =
      (∫ p in Metric.ball (0 : Space) 1 ×ˢ (Set.univ : Set (AddCircle (3 : ℝ))),
        liftInner (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p)
          (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p)) / 3 := by
  rw [energy_ball_one, energy_ball_three]
  ring

/-- The fixtures `energy_ball_three` and `energy_ball_one` are not `0 = 0`: the unit ball has
positive finite volume. -/
theorem volume_ball_toReal_pos : 0 < (volume (Metric.ball (0 : Space) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne

/-- **Regression (audit AV-M5): the degenerate case `Ω = ∅`** gives `0`. -/
theorem energy_empty (B : Space → Space) :
    ∫ p in (∅ : Set Space) ×ˢ (Set.univ : Set (AddCircle (3 : ℝ))),
        liftInner (hymLiftCircle 3 (fluxField B) p) (hymLiftCircle 3 (fluxField B) p) = 0 := by
  rw [integral_liftInner_hymLiftCircle]
  simp

/-- **Regression (audit AV-M5): the junk case, made explicit.** When `‖B‖²` is not integrable
on `Ω`, the lifted energy integral is the junk value `0` of the Bochner integral, and the
identity `integral_liftInner_hymLiftCircle` reads `0 = 2ℓ · 0`: it says nothing about the
energy. -/
theorem energy_junk (ℓ : ℝ) [Fact (0 < ℓ)] (B : Space → Space) (Ω : Set Space)
    (h : ¬ IntegrableOn (fun x => ‖B x‖ ^ 2) Ω) :
    ∫ p in Ω ×ˢ (Set.univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ (fluxField B) p) (hymLiftCircle ℓ (fluxField B) p) = 0 := by
  rw [integral_liftInner_hymLiftCircle, integral_undef h, mul_zero]

/-- **Regression (audit AV-M5): a concrete junk value.** The unit field `e₀` on all of space
has infinite energy; its lifted energy integral over `ℝ³ × (ℝ/3ℤ)` is `0`. -/
theorem energy_univ_junk :
    ∫ p in (Set.univ : Set Space) ×ˢ (Set.univ : Set (AddCircle (3 : ℝ))),
        liftInner (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p)
          (hymLiftCircle 3 (fluxField fun _ => coordVec 0) p) = 0 := by
  refine energy_junk 3 _ _ fun h => ?_
  have h1 : IntegrableOn (fun _ : Space => (1 : ℝ)) Set.univ := by
    simpa [coordVec] using h
  rw [integrableOn_const_iff] at h1
  simp at h1

end Energy

end PlasmaLean.Sanity.FormHYMCircle
