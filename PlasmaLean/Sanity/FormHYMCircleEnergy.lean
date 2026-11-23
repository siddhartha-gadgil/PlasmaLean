/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMCircleEnergy
public import PlasmaLean.Sanity.Forms
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Sanity checks for Yang–Mills minimality on `Ω × S¹` (`Theory/Fields/FormHYMCircleEnergy`)

The variation is `a = f(x) dτ` with `f` a smooth bump function at the origin of `ℝ³` (`1` on the
ball of radius `1`, `0` outside the ball of radius `2`). It does not depend on `τ`, so it is
periodic with every period, and it vanishes outside `K × ℝ` with `K` the closed ball of radius
`2`. It is not compactly supported in `ℝ³ × ℝ`, so the theorem of `FormHYMEnergy` does not apply
to it.

1. **Strict instance, `Ω = ℝ³`.** For the hyperbolic vacuum field `(x, y, -2z)` and every
   `ℓ > 0` the change of energy over one period is strictly positive
   (`hyperbolic_slab_energy_pos`). The lift is not integrable; only the difference is integrated.
2. **Degenerate instance.** For `a = 0` the change of energy is `0`
   (`hyperbolic_slab_energy_zero`).
3. **Strict instance with finite energy, `Ω ≠ ℝ³`.** For the constant field `e₀` on the open
   ball of radius `3`, the two energies are written separately and
   `∫_{Ω × (0,ℓ]} |ℱ|² < ∫_{Ω × (0,ℓ]} |ℱ + da|²` (`const_ball_slab_energy_lt`); the same on the
   manifold `Ω × (ℝ/ℓℤ)` (`const_ball_circle_energy_lt`).
4. **Periodicity is needed.** For the constant field `e₀` on `ℝ³` and the non-periodic
   `a = τ f(x) dx₀`, which satisfies every hypothesis of
   `integral_slab_liftInner_extDeriv_eq_zero` except periodicity, the cross term over one period
   is `ℓ ∫ f > 0` (`nonperiodic_cross_term`).

Not instantiated: a variation that depends on `τ` periodically (such as
`f(x) sin(2πτ/ℓ) dx₀`), and a field `G` that is not co-closed.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMCircleEnergy

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Sanity
  PlasmaLean.Sanity.Forms Matrix MeasureTheory Set
open scoped RealInnerProductSpace

/-! ### The variation -/

/-- A smooth bump function at the origin of `ℝ³`: `1` on the ball of radius `1`, `0` outside
the ball of radius `2`. -/
def spaceBump : ContDiffBump (0 : Space) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The `τ`-independent variation `a = f(x) dτ` of the connection. -/
def circleVar (p : LiftSpace) : LiftForm 1 := spaceBump p.1 • dTau

/-- The variation is of class `C¹`. -/
theorem contDiff_circleVar : ContDiff ℝ 1 circleVar :=
  (spaceBump.contDiff.comp contDiff_fst).smul contDiff_const

/-- The variation is periodic in `τ` with every period. -/
theorem circleVar_periodic (ℓ : ℝ) (x : Space) (τ : ℝ) :
    circleVar (x, τ + ℓ) = circleVar (x, τ) := by
  simp only [circleVar]

/-- The bump function vanishes outside the closed ball of radius `2`. -/
theorem spaceBump_eq_zero {x : Space} (hx : x ∉ Metric.closedBall (0 : Space) 2) :
    spaceBump x = 0 := by
  apply spaceBump.zero_of_le_dist
  rw [Metric.mem_closedBall, not_le] at hx
  exact hx.le

/-- The variation vanishes at `(x, τ)` for `x` outside the closed ball of radius `2`. -/
theorem circleVar_eq_zero (x : Space) (τ : ℝ) (hx : x ∉ Metric.closedBall (0 : Space) 2) :
    circleVar (x, τ) = 0 := by
  simp [circleVar, spaceBump_eq_zero hx]

/-- The curvature of the variation on the plane `(e₀, e_τ)` is the derivative of the bump
function in the direction `e₀`. -/
theorem extDeriv_circleVar_apply (p : LiftSpace) :
    extDeriv circleVar p ![(coordVec 0, 0), (0, 1)] = fderiv ℝ spaceBump p.1 (coordVec 0) := by
  have hf : HasFDerivAt spaceBump (fderiv ℝ spaceBump p.1) p.1 :=
    (spaceBump.contDiff (n := 1)).differentiable one_ne_zero p.1 |>.hasFDerivAt
  have hg : HasFDerivAt (fun q : LiftSpace => spaceBump q.1)
      ((fderiv ℝ spaceBump p.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) p :=
    hf.comp p hasFDerivAt_fst
  have h : HasFDerivAt circleVar
      (((fderiv ℝ spaceBump p.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)).smulRight dTau) p :=
    hg.smul_const dTau
  rw [TauCeti.extDeriv_apply_pair, h.fderiv]
  simp

/-- **The variation changes the curvature**: `da ≠ 0` at some point. Otherwise the bump function
would be constant along the line `t ↦ t e₀`, but it is `1` at the origin and `0` at distance
`2`. -/
theorem exists_extDeriv_circleVar_ne_zero : ∃ p, extDeriv circleVar p ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz (x : Space) : fderiv ℝ spaceBump x (coordVec 0) = 0 := by
    rw [← extDeriv_circleVar_apply (x, 0), hcon (x, 0)]
    rfl
  have hdiff : Differentiable ℝ spaceBump :=
    (spaceBump.contDiff (n := 1)).differentiable one_ne_zero
  let e : Space := coordVec 0
  have hg (t : ℝ) : HasDerivAt (fun r : ℝ => spaceBump (r • e)) 0 t := by
    have h1 : HasDerivAt (fun r : ℝ => r • e) ((1 : ℝ) • e) t := (hasDerivAt_id t).smul_const e
    have h2 := (hdiff (t • e)).hasFDerivAt.comp_hasDerivAt t h1
    rw [one_smul, hz] at h2
    exact h2
  have hconst := is_const_of_deriv_eq_zero (f := fun r : ℝ => spaceBump (r • e))
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 0 2
  have h0 : spaceBump ((0 : ℝ) • e) = 1 := by
    rw [zero_smul]
    exact spaceBump.one_of_mem_closedBall (Metric.mem_closedBall_self spaceBump.rIn_pos.le)
  have hn : ‖e‖ = 1 := by simp [e, coordVec]
  have h2 : spaceBump ((2 : ℝ) • e) = 0 := by
    apply spaceBump.zero_of_le_dist
    rw [dist_zero_right, norm_smul, hn]
    simp [spaceBump]
  simp only [h0, h2] at hconst
  exact one_ne_zero hconst

/-- The closed ball of radius `2` lies in the whole space. -/
theorem closedBall_subset_univ : Metric.closedBall (0 : Space) 2 ⊆ (univ : Set Space) :=
  subset_univ _

/-! ### 1. and 2. The hyperbolic field on `ℝ³ × S¹` -/

/-- **Minimality on `ℝ³ × S¹`, strict instance.** For the lift `ℱ` of the hyperbolic vacuum
field and the `τ`-independent variation `a = f dτ`, the change of energy over one period is
strictly positive for every `ℓ > 0`. The integrand is integrable on the slab although `|ℱ|²` is
not. -/
theorem hyperbolic_slab_energy_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
      (liftInner (hymLift (fluxField fun y => hyperbolicField y) p + extDeriv circleVar p)
          (hymLift (fluxField fun y => hyperbolicField y) p + extDeriv circleVar p) -
        liftInner (hymLift (fluxField fun y => hyperbolicField y) p)
          (hymLift (fluxField fun y => hyperbolicField y) p)) := by
  have h0 := hyperbolic_vacuumForm.integral_slab_energy_hymLift_perturbation_nonneg hℓ
    contDiff_circleVar (circleVar_periodic ℓ) (isCompact_closedBall (0 : Space) 2)
    closedBall_subset_univ circleVar_eq_zero
  have h1 := hyperbolic_vacuumForm.integral_slab_energy_hymLift_perturbation_eq_zero_iff hℓ
    contDiff_circleVar (circleVar_periodic ℓ) (isCompact_closedBall (0 : Space) 2)
    closedBall_subset_univ circleVar_eq_zero
  obtain ⟨p, hp⟩ := exists_extDeriv_circleVar_ne_zero
  exact lt_of_le_of_ne h0 fun h => hp (h1.1 h.symm p)

/-- **Minimality on `ℝ³ × S¹`, degenerate instance**: for the zero variation the change of
energy over one period vanishes. -/
theorem hyperbolic_slab_energy_zero {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
      (liftInner (hymLift (fluxField fun y => hyperbolicField y) p +
            extDeriv (fun _ : LiftSpace => (0 : LiftForm 1)) p)
          (hymLift (fluxField fun y => hyperbolicField y) p +
            extDeriv (fun _ : LiftSpace => (0 : LiftForm 1)) p) -
        liftInner (hymLift (fluxField fun y => hyperbolicField y) p)
          (hymLift (fluxField fun y => hyperbolicField y) p)) = 0 := by
  refine (hyperbolic_vacuumForm.integral_slab_energy_hymLift_perturbation_eq_zero_iff hℓ
    contDiff_const (fun _ _ => rfl) (isCompact_closedBall (0 : Space) 2)
    closedBall_subset_univ (fun _ _ _ => rfl)).2 fun p => ?_
  exact image_eq_zero_of_notMem_tsupport fun h => by
    have := TauCeti.tsupport_extDeriv_subset h
    simp [tsupport] at this

/-! ### 3. The constant field on a ball: finite energy -/

/-- The constant field `e₀` has finite magnetic energy on the open ball of radius `3`. -/
theorem const_integrableOn_ball :
    IntegrableOn (fun _ : Space => ‖flux.symm (flux (coordVec 0))‖ ^ 2)
      (Metric.ball (0 : Space) 3) :=
  integrableOn_const (measure_ball_lt_top).ne

/-- The energy of the variation over one period is strictly positive. -/
theorem circleVar_slab_energy_pos {ℓ : ℝ} (hℓ : 0 < ℓ) :
    0 < ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
      liftInner (extDeriv circleVar p) (extDeriv circleVar p) := by
  have h0 : 0 ≤ ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
      liftInner (extDeriv circleVar p) (extDeriv circleVar p) :=
    integral_nonneg fun p => liftInner_self_nonneg _
  have h1 := integral_slab_liftInner_extDeriv_self_eq_zero_iff hℓ contDiff_circleVar
    (circleVar_periodic ℓ) (isCompact_closedBall (0 : Space) 2) circleVar_eq_zero
  obtain ⟨p, hp⟩ := exists_extDeriv_circleVar_ne_zero
  exact lt_of_le_of_ne h0 fun h => hp (h1.1 h.symm p)

/-- The closed ball of radius `2` lies in the open ball of radius `3`. -/
theorem closedBall_subset_ball : Metric.closedBall (0 : Space) 2 ⊆ Metric.ball (0 : Space) 3 :=
  Metric.closedBall_subset_ball (by norm_num)

/-- **Strict minimality with finite energy, on a proper subregion.** For the constant field
`e₀` on the open ball `Ω` of radius `3` and the variation `a = f dτ` (supported in the closed
ball of radius `2`), the energy of the lift over `Ω × (0, ℓ]` is strictly smaller than the
energy of the varied connection. Both are finite: the integrands are integrable. -/
theorem const_ball_slab_energy_lt {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ p in Metric.ball (0 : Space) 3 ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift (fun _ => flux (coordVec 0)) p)
          (hymLift (fun _ => flux (coordVec 0)) p) <
      ∫ p in Metric.ball (0 : Space) 3 ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift (fun _ => flux (coordVec 0)) p + extDeriv circleVar p)
          (hymLift (fun _ => flux (coordVec 0)) p + extDeriv circleVar p) := by
  have hv : VacuumForm (Metric.ball (0 : Space) 3) fun _ => flux (coordVec 0) :=
    const_vacuumForm Metric.isOpen_ball _
  have h := (hv.integral_slab_energy_hymLift_add hℓ contDiff_circleVar (circleVar_periodic ℓ)
    (isCompact_closedBall (0 : Space) 2) closedBall_subset_ball circleVar_eq_zero
    const_integrableOn_ball).2
  have hpos := circleVar_slab_energy_pos hℓ
  rw [← setIntegral_region_slab_eq closedBall_subset_ball
    (φ := fun p => liftInner (extDeriv circleVar p) (extDeriv circleVar p))
    (fun x τ hx => by
      rw [extDeriv_eq_zero_of_notMem (isCompact_closedBall (0 : Space) 2) circleVar_eq_zero hx,
        liftInner_zero_right])] at hpos
  rw [h, integral_slab_liftInner_hymLift hℓ.le]
  linarith

/-- The curvature of the variation does not depend on `τ`. -/
theorem extDeriv_circleVar_tau_indep (x : Space) (τ : ℝ) :
    extDeriv circleVar (x, τ) = extDeriv circleVar (x, 0) := by
  have h := extDeriv_tau_periodic (a := circleVar) (ℓ := τ) (fun _ _ => rfl) x 0
  rwa [zero_add] at h

/-- **The same on the manifold `Ω × (ℝ/ℓℤ)`**: the curvature of the variation descends to the
field `D (x, θ) = da (x, 0)` on `ℝ³ × (ℝ/ℓℤ)`, and the energy of the circle lift over `Ω × S¹`
is strictly smaller than that of the varied connection. -/
theorem const_ball_circle_energy_lt (ℓ : ℝ) [Fact (0 < ℓ)] :
    ∫ q in Metric.ball (0 : Space) 3 ×ˢ (univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ (fun _ => flux (coordVec 0)) q)
          (hymLiftCircle ℓ (fun _ => flux (coordVec 0)) q) <
      ∫ q in Metric.ball (0 : Space) 3 ×ˢ (univ : Set (AddCircle ℓ)),
        liftInner (hymLiftCircle ℓ (fun _ => flux (coordVec 0)) q + extDeriv circleVar (q.1, 0))
          (hymLiftCircle ℓ (fun _ => flux (coordVec 0)) q + extDeriv circleVar (q.1, 0)) := by
  have hℓ : 0 < ℓ := Fact.out
  have hD (p : LiftSpace) : (fun q : Space × AddCircle ℓ => extDeriv circleVar (q.1, 0))
      (liftCover ℓ p) = extDeriv circleVar p :=
    (extDeriv_circleVar_tau_indep p.1 p.2).symm
  rw [setIntegral_circle_eq_setIntegral_slab, setIntegral_circle_eq_setIntegral_slab]
  simp only [hymLiftCircle_liftCover, hD]
  exact const_ball_slab_energy_lt hℓ

/-! ### 4. Periodicity is needed -/

/-- The non-periodic variation `a = τ f(x) dx₀`. -/
def growVar (p : LiftSpace) : LiftForm 1 := (p.2 * spaceBump p.1) • dX 0

/-- The non-periodic variation is of class `C¹`. -/
theorem contDiff_growVar : ContDiff ℝ 1 growVar :=
  (contDiff_snd.mul (spaceBump.contDiff.comp contDiff_fst)).smul contDiff_const

/-- The non-periodic variation vanishes at `(x, τ)` for `x` outside the closed ball of radius
`2`. -/
theorem growVar_eq_zero (x : Space) (τ : ℝ) (hx : x ∉ Metric.closedBall (0 : Space) 2) :
    growVar (x, τ) = 0 := by
  simp [growVar, spaceBump_eq_zero hx]

/-- `dx₀` on a one-vector family. -/
theorem dX_apply_fun (i : Fin 3) (v : Fin 1 → LiftSpace) : dX i v = (v 0).1 i :=
  (congrArg (fun u => dX i u) (show v = ![v 0] from funext fun j => by fin_cases j; rfl)).trans
    (dX_apply i (v 0))

/-- The inner product with the lift of the constant field `e₀`:
`⟨ℱ, H⟩ = H(e₁, e₂) - H(e₀, e_τ)`. -/
theorem liftInner_hymLiftAt_coordVec_zero (H : LiftForm 2) :
    liftInner (hymLiftAt (flux (coordVec 0))) H =
      H ![(coordVec 1, 0), (coordVec 2, 0)] - H ![(coordVec 0, 0), (0, 1)] := by
  rw [liftInner_eq]
  simp only [hymLiftAt_apply, hodge_flux, flux_apply, volForm_vec, flat_apply]
  simp [coordVec, PiLp.inner_apply]
  ring

/-- The cross term of the non-periodic variation with the lift of the constant field `e₀` is
the bump function: `⟨ℱ, da⟩ (x, τ) = f(x)`. -/
theorem liftInner_extDeriv_growVar (p : LiftSpace) :
    liftInner (hymLift (fun _ => flux (coordVec 0)) p) (extDeriv growVar p) = spaceBump p.1 := by
  have hf : HasFDerivAt spaceBump (fderiv ℝ spaceBump p.1) p.1 :=
    (spaceBump.contDiff (n := 1)).differentiable one_ne_zero p.1 |>.hasFDerivAt
  have hg : HasFDerivAt (fun q : LiftSpace => spaceBump q.1)
      ((fderiv ℝ spaceBump p.1).comp (ContinuousLinearMap.fst ℝ Space ℝ)) p :=
    hf.comp p hasFDerivAt_fst
  have hc := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).mul hg
  have h := hc.smul_const (dX 0)
  change liftInner (hymLiftAt (flux (coordVec 0))) (extDeriv growVar p) = spaceBump p.1
  rw [liftInner_hymLiftAt_coordVec_zero, TauCeti.extDeriv_apply_pair,
    TauCeti.extDeriv_apply_pair]
  have hfd : fderiv ℝ growVar p = _ := h.fderiv
  rw [hfd]
  simp [dX_apply_fun, coordVec]

/-- **Periodicity is needed.** The lift of the constant field `e₀` on `Ω = ℝ³` and the
variation `a = τ f(x) dx₀` satisfy every hypothesis of
`integral_slab_liftInner_extDeriv_eq_zero` except periodicity of `a` (`a` is `C¹` and vanishes
outside `K × ℝ` for the closed ball `K` of radius `2`), and the cross term over one period is
`ℓ ∫ f`, which is strictly positive. -/
theorem nonperiodic_cross_term {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ContDiff ℝ 1 growVar ∧
    (∀ x τ, x ∉ Metric.closedBall (0 : Space) 2 → growVar (x, τ) = 0) ∧
    ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift (fun _ => flux (coordVec 0)) p) (extDeriv growVar p) =
      ℓ * ∫ x, spaceBump x ∧
    0 < ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift (fun _ => flux (coordVec 0)) p) (extDeriv growVar p) := by
  have hm : (volume : Measure LiftSpace).restrict ((univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ) =
      (volume : Measure Space).prod (volume.restrict (Ioc (0 : ℝ) ℓ)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hr : (volume.restrict (Ioc (0 : ℝ) ℓ)).real univ = ℓ := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hℓ.le]
  have e : ∫ p in (univ : Set Space) ×ˢ Ioc (0 : ℝ) ℓ,
        liftInner (hymLift (fun _ => flux (coordVec 0)) p) (extDeriv growVar p) =
      ℓ * ∫ x, spaceBump x := by
    simp only [liftInner_extDeriv_growVar]
    rw [hm, integral_fun_fst (fun x : Space => spaceBump x), hr, smul_eq_mul]
  refine ⟨contDiff_growVar, growVar_eq_zero, e, ?_⟩
  rw [e]
  exact mul_pos hℓ spaceBump.integral_pos

end PlasmaLean.Sanity.FormHYMCircleEnergy
