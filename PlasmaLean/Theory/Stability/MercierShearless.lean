/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Stability.MercierGeneral
public import PlasmaLean.Theory.Fields.BiotSavart
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Shearless surfaces without a magnetic well are Mercier unstable

We work with the general Mercier index `MercierGeneral.mercierIndex` (Landreman–Jorge 2020,
eq. (3.1), a SUPPLIED formula; its derivation from `δW` is not formalized):

  `(2π)⁶ D_Merc = [s_G 2π² ι' - ∫ B·Ξ w]² + [s_ψ μ₀ p' V'' - ∫ |Ξ|² w] ∫ B² w`,

with `w = 1/|∇ψ|³` times the area element and `Ξ = μ₀ J - I' B`.

**Main result (`mercierIndex_neg_of_forceBalance`).** Suppose on one flux surface
* the shear vanishes, `ι' = 0`;
* there is no magnetic well, `s_ψ μ₀ p' V'' ≤ 0` (for instance `V'' = 0`);
* force balance `J × B = ∇p` holds at every point of the surface and `∇p ≠ 0` there;
* the three surface integrals are genuine integrals, with the SAME everywhere-positive
  weight, over a parametrisation of the surface by a nonzero measure.

Then `D_Merc < 0` (the Mercier criterion is violated), whatever the value of `I'`, the
signs `s_G, s_ψ` and the normalisation of the weight.

**Mechanism.** With `ι' = 0` and no well, `(2π)⁶ D_Merc ≤ (∫B·Ξ w)² - ∫|Ξ|² w ∫B² w`, which
is `≤ 0` by Cauchy–Schwarz. Equality would need `Ξ ∥ B` almost everywhere; but
`(Ξ - tB) × B = μ₀ J × B = μ₀ ∇p ≠ 0` for every real `t` (`cross_sub_smul`), so `Ξ` is
nowhere parallel to `B` (the diamagnetic current `B × ∇p/B²` is never zero), and the
Cauchy–Schwarz inequality is strict (`integral_inner_sq_lt`). This is the
Pfirsch–Schlüter/geodesic-curvature destabilisation of Mercier's criterion, which nothing
can balance when there is neither shear nor a well.

Sanity: `integral_inner_sq_eq_of_parallel` shows that the strictness hypothesis cannot be
dropped (if `Ξ = t₀ B` everywhere the Cauchy–Schwarz inequality is an equality).

Scope: local (interchange) criterion only; no ballooning, global, resistive or kinetic
statement. For exactly shearless surfaces Mercier's asymptotic derivation itself
degenerates; the statement here is about the sign of the supplied index.
-/

public section
noncomputable section
namespace PlasmaLean.Stability.MercierShearless
open Real MeasureTheory PlasmaLean.Fields PlasmaLean.Stability.MercierGeneral
open scoped RealInnerProductSpace

/-! ## Pointwise: force balance makes `Ξ` nowhere parallel to `B` -/

/-- Linearity of the cross product in the first slot, with `B × B = 0`:
`(c J - s B) × B = c (J × B)`. -/
theorem cross_sub_smul (c s : ℝ) (J B : Space) :
    cross (c • J - s • B) B = c • cross J B := by
  unfold cross
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, cross_self, smul_zero, sub_zero, WithLp.toLp_smul]

/-- If `J × B = g ≠ 0` then `B ≠ 0`. -/
theorem field_ne_zero_of_cross {J B g : Space} (hfb : cross J B = g) (hg : g ≠ 0) : B ≠ 0 := by
  rintro rfl
  apply hg
  rw [← hfb]
  unfold cross
  simp

/-- If `J × B = g ≠ 0` and `c ≠ 0`, then `Ξ = c J - I' B` is nowhere parallel to `B`:
`Ξ - t B ≠ 0` for every real `t`. -/
theorem xi_sub_smul_ne_zero {c I' : ℝ} {J B g : Space} (hc : c ≠ 0) (hfb : cross J B = g)
    (hg : g ≠ 0) (t : ℝ) : c • J - I' • B - t • B ≠ 0 := by
  intro h
  have h1 : cross (c • J - (I' + t) • B) B = c • g := by rw [cross_sub_smul, hfb]
  rw [add_smul, ← sub_sub, h] at h1
  have h2 : cross 0 B = 0 := by unfold cross; simp
  rw [h2] at h1
  exact hg ((smul_eq_zero.mp h1.symm).resolve_left hc)

/-! ## Strict Cauchy–Schwarz for weighted surface integrals -/

section CauchySchwarz
variable {P : Type*} [MeasurableSpace P] {μ : Measure P}

/-- The integral of an everywhere-positive integrable function over a nonzero measure is
positive. -/
theorem integral_pos_of_forall_pos [NeZero μ] {f : P → ℝ} (hf : ∀ x, 0 < f x)
    (hi : Integrable f μ) : 0 < ∫ x, f x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg (fun x => (hf x).le) hi).2 ?_
  have : Function.support f = Set.univ := Set.eq_univ_of_forall (fun x => (hf x).ne')
  rw [this]
  exact Measure.measure_univ_pos.mpr (NeZero.ne μ)

/-- Pointwise expansion `‖Ξ - tB‖² w = ‖Ξ‖² w - 2t ⟪B, Ξ⟫ w + t² ‖B‖² w`. -/
theorem norm_sub_smul_sq_mul (B Ξ : Space) (w t : ℝ) :
    ‖Ξ - t • B‖ ^ 2 * w = ‖Ξ‖ ^ 2 * w - 2 * t * (⟪B, Ξ⟫ * w) + t ^ 2 * (‖B‖ ^ 2 * w) := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_comm]
  ring

/-- **Strict Cauchy–Schwarz.** If the weight is positive, `B` never vanishes and `Ξ` is
nowhere parallel to `B`, then `(∫⟪B,Ξ⟫w)² < ∫‖Ξ‖²w · ∫‖B‖²w` (for a nonzero measure). -/
theorem integral_inner_sq_lt [NeZero μ] (B Ξ : P → Space) (w : P → ℝ) (hw : ∀ x, 0 < w x)
    (hB : ∀ x, B x ≠ 0) (hpar : ∀ x (t : ℝ), Ξ x - t • B x ≠ 0)
    (iB : Integrable (fun x => ‖B x‖ ^ 2 * w x) μ)
    (iX : Integrable (fun x => ‖Ξ x‖ ^ 2 * w x) μ)
    (iBX : Integrable (fun x => ⟪B x, Ξ x⟫ * w x) μ) :
    (∫ x, ⟪B x, Ξ x⟫ * w x ∂μ) ^ 2 < (∫ x, ‖Ξ x‖ ^ 2 * w x ∂μ) * ∫ x, ‖B x‖ ^ 2 * w x ∂μ := by
  set a := ∫ x, ‖Ξ x‖ ^ 2 * w x ∂μ
  set b := ∫ x, ⟪B x, Ξ x⟫ * w x ∂μ
  set c := ∫ x, ‖B x‖ ^ 2 * w x ∂μ
  have hc : 0 < c := integral_pos_of_forall_pos
    (fun x => mul_pos (pow_pos (norm_pos_iff.mpr (hB x)) 2) (hw x)) iB
  set t := b / c
  have iT : Integrable (fun x => ‖Ξ x - t • B x‖ ^ 2 * w x) μ := by
    have := (iX.sub (iBX.const_mul (2 * t))).add (iB.const_mul (t ^ 2))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [norm_sub_smul_sq_mul]
  have hT : 0 < ∫ x, ‖Ξ x - t • B x‖ ^ 2 * w x ∂μ := integral_pos_of_forall_pos
    (fun x => mul_pos (pow_pos (norm_pos_iff.mpr (hpar x t)) 2) (hw x)) iT
  have hexp : ∫ x, ‖Ξ x - t • B x‖ ^ 2 * w x ∂μ = a - 2 * t * b + t ^ 2 * c := by
    simp_rw [norm_sub_smul_sq_mul]
    have e1 : ∫ x, ‖Ξ x‖ ^ 2 * w x - 2 * t * (⟪B x, Ξ x⟫ * w x) + t ^ 2 * (‖B x‖ ^ 2 * w x) ∂μ
        = ∫ x, ‖Ξ x‖ ^ 2 * w x - 2 * t * (⟪B x, Ξ x⟫ * w x) ∂μ +
          ∫ x, t ^ 2 * (‖B x‖ ^ 2 * w x) ∂μ :=
      integral_add (iX.sub (iBX.const_mul _)) (iB.const_mul _)
    have e2 : ∫ x, ‖Ξ x‖ ^ 2 * w x - 2 * t * (⟪B x, Ξ x⟫ * w x) ∂μ
        = a - ∫ x, 2 * t * (⟪B x, Ξ x⟫ * w x) ∂μ := integral_sub iX (iBX.const_mul _)
    rw [e1, e2, integral_const_mul, integral_const_mul]
  rw [hexp] at hT
  have ht : t * c = b := div_mul_cancel₀ b hc.ne'
  nlinarith

/-- Sanity (the strictness hypothesis is needed): if `Ξ = t₀ B` everywhere, Cauchy–Schwarz
is an equality, `(∫⟪B,Ξ⟫w)² = ∫‖Ξ‖²w · ∫‖B‖²w`. -/
theorem integral_inner_sq_eq_of_parallel (B : P → Space) (w : P → ℝ) (t₀ : ℝ) :
    (∫ x, ⟪B x, t₀ • B x⟫ * w x ∂μ) ^ 2 =
      (∫ x, ‖t₀ • B x‖ ^ 2 * w x ∂μ) * ∫ x, ‖B x‖ ^ 2 * w x ∂μ := by
  have h1 : ∀ x, ⟪B x, t₀ • B x⟫ * w x = t₀ * (‖B x‖ ^ 2 * w x) := fun x => by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  have h2 : ∀ x, ‖t₀ • B x‖ ^ 2 * w x = t₀ ^ 2 * (‖B x‖ ^ 2 * w x) := fun x => by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  simp_rw [h1, h2]
  rw [integral_const_mul, integral_const_mul]
  ring

end CauchySchwarz

/-! ## The Mercier index -/

/-- **Shearless, no well, strict Cauchy–Schwarz ⇒ Mercier unstable.** If `ι' = 0`,
`s_ψ μ₀ p' V'' ≤ 0`, `∫B²w > 0` and `(∫B·Ξ w)² < ∫|Ξ|²w ∫B²w`, then `D_Merc < 0`. -/
theorem mercierIndex_neg_of_shearless {d : MercierSurfaceData} (hι : d.iotaPrime = 0)
    (hwell : d.sψ * d.muPprime * d.Vpp ≤ 0) (hB : 0 < d.intB2)
    (hCS : d.intBXi ^ 2 < d.intXi2 * d.intB2) : mercierIndex d < 0 := by
  refine mercierIndex_neg_of_hill hB hwell ?_
  unfold MercierSurfaceData.shearBracket
  rw [hι, mul_zero, zero_sub, neg_sq]
  exact hCS

/-- **Mercier instability of shearless surfaces without a well, from force balance.**
On a flux surface parametrised by a nonzero measure space `P`, let `B, J, g : P → Space` be
the field, current and pressure gradient at the surface points, with `J × B = g` and
`g ≠ 0` everywhere, and let `w > 0` be any weight. Put `Ξ = μ₀ J - I' B` (any `I'`).
If the shear vanishes and there is no well (`s_ψ μ₀ p' V'' ≤ 0`), the general Mercier index
built from the weighted integrals is negative. -/
theorem mercierIndex_neg_of_forceBalance {P : Type*} [MeasurableSpace P] {μ : Measure P}
    [NeZero μ] {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (I' sG sψ muP Vpp : ℝ)
    (hwell : sψ * muP * Vpp ≤ 0) (B J g : P → Space) (w : P → ℝ)
    (hfb : ∀ x, cross (J x) (B x) = g x) (hg : ∀ x, g x ≠ 0) (hw : ∀ x, 0 < w x)
    (iB : Integrable (fun x => ‖B x‖ ^ 2 * w x) μ)
    (iX : Integrable (fun x => ‖μ₀ • J x - I' • B x‖ ^ 2 * w x) μ)
    (iBX : Integrable (fun x => ⟪B x, μ₀ • J x - I' • B x⟫ * w x) μ) :
    mercierIndex ⟨sG, sψ, 0, muP, Vpp, ∫ x, ⟪B x, μ₀ • J x - I' • B x⟫ * w x ∂μ,
      ∫ x, ‖μ₀ • J x - I' • B x‖ ^ 2 * w x ∂μ, ∫ x, ‖B x‖ ^ 2 * w x ∂μ⟩ < 0 := by
  have hB : ∀ x, B x ≠ 0 := fun x => field_ne_zero_of_cross (hfb x) (hg x)
  have hCS := integral_inner_sq_lt (μ := μ) B (fun x => μ₀ • J x - I' • B x) w hw hB
    (fun x t => xi_sub_smul_ne_zero hμ (hfb x) (hg x) t) iB iX iBX
  have hc : 0 < ∫ x, ‖B x‖ ^ 2 * w x ∂μ := integral_pos_of_forall_pos
    (fun x => mul_pos (pow_pos (norm_pos_iff.mpr (hB x)) 2) (hw x)) iB
  exact mercierIndex_neg_of_shearless rfl hwell hc hCS

/-- Special case `V'' = 0` (no well and no hill): any shearless surface with a nonzero
pressure gradient is Mercier unstable. -/
theorem mercierIndex_neg_of_forceBalance_Vpp_zero {P : Type*} [MeasurableSpace P]
    {μ : Measure P} [NeZero μ] {μ₀ : ℝ} (hμ : μ₀ ≠ 0) (I' sG sψ muP : ℝ)
    (B J g : P → Space) (w : P → ℝ)
    (hfb : ∀ x, cross (J x) (B x) = g x) (hg : ∀ x, g x ≠ 0) (hw : ∀ x, 0 < w x)
    (iB : Integrable (fun x => ‖B x‖ ^ 2 * w x) μ)
    (iX : Integrable (fun x => ‖μ₀ • J x - I' • B x‖ ^ 2 * w x) μ)
    (iBX : Integrable (fun x => ⟪B x, μ₀ • J x - I' • B x⟫ * w x) μ) :
    mercierIndex ⟨sG, sψ, 0, muP, 0, ∫ x, ⟪B x, μ₀ • J x - I' • B x⟫ * w x ∂μ,
      ∫ x, ‖μ₀ • J x - I' • B x‖ ^ 2 * w x ∂μ, ∫ x, ‖B x‖ ^ 2 * w x ∂μ⟩ < 0 :=
  mercierIndex_neg_of_forceBalance hμ I' sG sψ muP 0 (by simp) B J g w hfb hg hw iB iX iBX

end PlasmaLean.Stability.MercierShearless
