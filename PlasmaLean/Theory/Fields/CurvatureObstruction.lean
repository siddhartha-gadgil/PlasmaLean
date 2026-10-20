/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.Subharmonic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The curvature obstruction to minimum-B around a closed field line

Track T1/T8. Source: P. Helander, *Theory of plasma confinement in non-axisymmetric
magnetic fields*, Rep. Prog. Phys. 77 (2014) 087001, §2.4 Eq. (24) (curvature identity
`κ = μ₀∇p/B² + ∇⊥B/B`, here in the vacuum case `∇p = 0`) and §3.3 (the argument that
the field strength cannot increase away from a closed, necessarily curved, magnetic
axis). See `notes/theory/toroidal-min-b-obstruction.md`, Theorem A and Corollaries B, C.

Definitions (all on `Euclid3`).
* `unitField B y = B y / ‖B y‖`, the unit vector `b` along the field.
* `fieldCurvature B x = Db(x) b(x) = (b·∇)b`, the field-line curvature vector `κ`.

Main results.
* `fieldCurvature_eq`: for `B` differentiable at `x` with `B x ≠ 0`,
  `κ = (L b - ⟪b, L b⟫ b) / ‖B‖` with `L = DB(x)`; `inner_unitField_fieldCurvature`:
  `κ ⊥ b`.
* `gradient_norm_eq` and `gradient_perp_norm_eq_curvature` (**Theorem A, vacuum**):
  if moreover `∇ × B = 0` at `x`, then `∇|B| = (DB) b` and
  `∇⊥|B| = ∇|B| - ⟪b, ∇|B|⟫ b = |B| κ`. The `|B|²/2` version is
  `gradient_perp_halfNormSq_eq_curvature`.
* `fieldCurvature_eq_zero_of_transverse_critical`, `curvature_zero_of_normSq_critical`,
  `VacuumField.curvature_zero_of_isLocalMin` / `_of_isLocalMax` (**Corollary B**): at a
  point where `B ≠ 0`, `∇ × B = 0`, and `|B|` is critical in the directions normal to `B`
  (in particular at a 3-D critical point, local min or local max of `|B|`), `κ = 0`.
* `not_forall_fieldCurvature_eq_zero` (geometric core of **Corollary C**): along a
  closed field line (`γ' = B ∘ γ` on `[0, T]`, `γ T = γ 0`, `T > 0`) on which `B ≠ 0`
  and `B` is differentiable, the curvature cannot vanish identically. (The unit tangent
  would be constant, so `⟪γ, u₀⟫` would be strictly increasing.)
* `VacuumField.not_closed_fieldLine_transverse_minB`,
  `VacuumField.not_closed_fieldLine_minB` (**Corollary C**): in a vacuum region, there is
  no closed field line with `B ≠ 0` along which every point is a minimum of `|B|`
  along every line normal to `B` (resp. a 3-D local minimum of `|B|`).

Meaning of "minimum-B along a closed axis" used here: for every `s ∈ [0, T]` and every
`v ⊥ B(γ s)`, the function `σ ↦ |B(γ s + σ v)|` has a local minimum at `σ = 0`
(`TransverseMinB`). This is implied by a local minimum of `|B|` on the normal plane, and
by a 3-D local minimum. Only first-order (critical point) information is used.

Topology: in a simply connected region a curl-free field has no closed field lines, so
Corollary C is meaningful only in multiply connected regions; see
`Sanity.wireField_not_transverseMinB` for a witness that its hypotheses are satisfiable.

Not covered: the finite-β version (`∇p = 0` on the axis, MHS force balance) and the
quantitative Fenchel bound `∮ κ ds ≥ 2π`.
-/

open scoped RealInnerProductSpace Topology
open Set InnerProductSpace

public section
noncomputable section

namespace PlasmaLean.Vacuum

/-! ### Unit field and field-line curvature -/

/-- The unit vector field `b = B / |B|` (equal to `0` where `B = 0`). -/
@[expose] def unitField (B : Euclid3 → Euclid3) (y : Euclid3) : Euclid3 := ‖B y‖⁻¹ • B y

/-- The field-line curvature vector `κ = (b·∇)b = Db(x) b(x)`, `b = B/|B|`. -/
@[expose] def fieldCurvature (B : Euclid3 → Euclid3) (x : Euclid3) : Euclid3 :=
  fderiv ℝ (unitField B) x (unitField B x)

/-- The unit field has norm one where `B ≠ 0`. -/
theorem norm_unitField {B : Euclid3 → Euclid3} {x : Euclid3} (h0 : B x ≠ 0) :
    ‖unitField B x‖ = 1 := by
  rw [unitField, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h0)]

/-- `B = |B| b`. -/
theorem norm_smul_unitField {B : Euclid3 → Euclid3} {x : Euclid3} (h0 : B x ≠ 0) :
    ‖B x‖ • unitField B x = B x := by
  rw [unitField, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0), one_smul]

/-- Derivative of `|B|`: `D|B|(x) v = ⟪B, L v⟫ / |B|` where `L = DB(x)`, `B x ≠ 0`. -/
theorem hasFDerivAt_norm_field {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) :
    HasFDerivAt (fun y => ‖B y‖) (‖B x‖⁻¹ • (innerSL ℝ (B x)).comp L) x := by
  have hn : ‖B x‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hsq : ‖B x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn
  have h := hB.norm_sq.sqrt hsq
  have heq : (fun y => √(‖B y‖ ^ 2)) = fun y => ‖B y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg _)
  rw [heq] at h
  convert h using 1
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    smul_eq_mul, Real.sqrt_sq (norm_nonneg _)]
  simp only [two_smul]
  field_simp
  ring

/-- Derivative of the unit field `b = B/|B|` at a point where `B ≠ 0`. -/
theorem hasFDerivAt_unitField {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) :
    HasFDerivAt (unitField B)
      (‖B x‖⁻¹ • L + ((-(‖B x‖ ^ 2)⁻¹) • (‖B x‖⁻¹ • (innerSL ℝ (B x)).comp L)).smulRight (B x))
      x := by
  have hn : ‖B x‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hinv := (hasDerivAt_inv hn).comp_hasFDerivAt x (hasFDerivAt_norm_field hB h0)
  exact hinv.smul hB

/-- **Curvature formula.** For `B` differentiable at `x` with `B x ≠ 0`, `L = DB(x)` and
`b = B/|B|`: `κ = |B|⁻¹ (L b - ⟪b, L b⟫ b)`. -/
theorem fieldCurvature_eq {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) :
    fieldCurvature B x = ‖B x‖⁻¹ •
      (L (unitField B x) - ⟪unitField B x, L (unitField B x)⟫ • unitField B x) := by
  have hn : ‖B x‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  rw [fieldCurvature, (hasFDerivAt_unitField hB h0).fderiv]
  set b := unitField B x
  have hBb : B x = ‖B x‖ • b := (norm_smul_unitField h0).symm
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [hBb, inner_smul_left]
  simp only [conj_trivial, smul_sub, smul_smul]
  rw [← hBb]
  match_scalars
  all_goals (try simp only [smul_eq_mul])
  all_goals field_simp

/-- The curvature is normal to the field: `⟪b, κ⟫ = 0`. -/
theorem inner_unitField_fieldCurvature {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) :
    ⟪unitField B x, fieldCurvature B x⟫ = 0 := by
  rw [fieldCurvature_eq hB h0, inner_smul_right, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, norm_unitField h0]
  ring

/-! ### Symmetric Jacobian and the gradient of `|B|` -/

/-- Coordinate expansion `v = ∑ⱼ vⱼ eⱼ`. -/
theorem eq_sum_coordVec (v : Euclid3) : v = ∑ j : Fin 3, v j • coordVec j := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three]

/-- A curl-free derivative operator is self-adjoint: `⟪L v, w⟫ = ⟪v, L w⟫`. -/
theorem inner_map_comm_of_curlOp_eq_zero {L : Euclid3 →L[ℝ] Euclid3} (h : curlOp L = 0)
    (v w : Euclid3) : ⟪L v, w⟫ = ⟪v, L w⟫ := by
  have hs := (curlOp_eq_zero_iff L).mp h
  have expand : ∀ u : Euclid3, L u = ∑ j : Fin 3, u j • L (coordVec j) := fun u => by
    conv_lhs => rw [eq_sum_coordVec u]
    simp [map_sum, map_smul]
  rw [expand v, expand w]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hs 0 1, hs 0 2, hs 1 2]
  ring

/-- **Vacuum gradient of `|B|`.** If `B` has derivative `L` at `x`, `B x ≠ 0` and
`∇ × B = 0` there (`curlOp L = 0`), then `∇|B|(x) = L b = (b·∇)B`. -/
theorem hasGradientAt_norm_field {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) (hcurl : curlOp L = 0) :
    HasGradientAt (fun y => ‖B y‖) (L (unitField B x)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hasFDerivAt_norm_field hB h0 using 1
  ext v
  simp only [toDual_apply_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  rw [inner_map_comm_of_curlOp_eq_zero hcurl, unitField, inner_smul_left]
  simp

/-- `∇|B|(x) = DB(x) b(x)` for a curl-free field (gradient form). -/
theorem gradient_norm_eq {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (h0 : B x ≠ 0) (hcurl : curlOp L = 0) :
    gradient (fun y => ‖B y‖) x = L (unitField B x) :=
  (hasGradientAt_norm_field hB h0 hcurl).gradient

/-- **Curvature identity (Helander 2014, Eq. 24, vacuum case).** For `B` differentiable
at `x`, `B x ≠ 0`, `∇ × B = 0` at `x`: `∇⊥|B| = ∇|B| - ⟪b, ∇|B|⟫ b = |B| κ`. -/
theorem gradient_perp_norm_eq_curvature {B : Euclid3 → Euclid3} {x : Euclid3}
    (hB : DifferentiableAt ℝ B x) (h0 : B x ≠ 0) (hcurl : fieldCurl B x = 0) :
    gradient (fun y => ‖B y‖) x -
        ⟪unitField B x, gradient (fun y => ‖B y‖) x⟫ • unitField B x =
      ‖B x‖ • fieldCurvature B x := by
  rw [gradient_norm_eq hB.hasFDerivAt h0 hcurl, fieldCurvature_eq hB.hasFDerivAt h0, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0), one_smul]

/-- Vacuum gradient of `|B|²/2`: `∇(|B|²/2) = (B·∇)B = L B`. -/
theorem gradient_halfNormSq_eq {B : Euclid3 → Euclid3} {L : Euclid3 →L[ℝ] Euclid3}
    {x : Euclid3} (hB : HasFDerivAt B L x) (hcurl : curlOp L = 0) :
    gradient (fun y => ‖B y‖ ^ 2 / 2) x = L (B x) := by
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf : (fun y => ‖B y‖ ^ 2 / 2) = fun y => ‖B y‖ ^ 2 * (1 / 2) := by
    funext y; ring
  rw [hf]
  convert hB.norm_sq.mul_const (1 / 2 : ℝ) using 1
  ext v
  simp only [toDual_apply_apply, smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, two_smul, add_apply]
  rw [inner_map_comm_of_curlOp_eq_zero hcurl]
  ring

/-- **Curvature identity, `|B|²/2` form.** `∇(|B|²/2) - b (b·∇)(|B|²/2) = |B|² κ` for a
curl-free field with `B x ≠ 0`. -/
theorem gradient_perp_halfNormSq_eq_curvature {B : Euclid3 → Euclid3} {x : Euclid3}
    (hB : DifferentiableAt ℝ B x) (h0 : B x ≠ 0) (hcurl : fieldCurl B x = 0) :
    gradient (fun y => ‖B y‖ ^ 2 / 2) x -
        ⟪unitField B x, gradient (fun y => ‖B y‖ ^ 2 / 2) x⟫ • unitField B x =
      ‖B x‖ ^ 2 • fieldCurvature B x := by
  have hn : ‖B x‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hL : fderiv ℝ B x (B x) = ‖B x‖ • fderiv ℝ B x (unitField B x) := by
    conv_lhs => rw [← norm_smul_unitField h0]
    exact map_smul _ _ _
  rw [gradient_halfNormSq_eq hB.hasFDerivAt hcurl, fieldCurvature_eq hB.hasFDerivAt h0, hL,
    inner_smul_right]
  match_scalars <;> field_simp

/-! ### Corollary B: critical points of `|B|` have straight field lines -/

/-- **Transverse criticality kills the curvature.** If `B` is differentiable at `x`,
`B x ≠ 0`, `∇ × B = 0` at `x`, and the derivative of `|B|` vanishes in every direction
normal to `B(x)`, then `κ(x) = 0`. -/
theorem fieldCurvature_eq_zero_of_transverse_critical {B : Euclid3 → Euclid3} {x : Euclid3}
    (hB : DifferentiableAt ℝ B x) (h0 : B x ≠ 0) (hcurl : fieldCurl B x = 0)
    (hcrit : ∀ v, ⟪B x, v⟫ = 0 → fderiv ℝ (fun y => ‖B y‖) x v = 0) :
    fieldCurvature B x = 0 := by
  set κ := fieldCurvature B x
  have hbκ : ⟪unitField B x, κ⟫ = 0 := inner_unitField_fieldCurvature hB.hasFDerivAt h0
  have hBκ : ⟪B x, κ⟫ = 0 := by
    rw [← norm_smul_unitField h0, inner_smul_left, hbκ, mul_zero]
  have hg := hasGradientAt_norm_field hB.hasFDerivAt h0 hcurl
  have hd : fderiv ℝ (fun y => ‖B y‖) x κ = ⟪fderiv ℝ B x (unitField B x), κ⟫ := by
    rw [hg.hasFDerivAt.fderiv, toDual_apply_apply]
  have hLκ : ⟪fderiv ℝ B x (unitField B x), κ⟫ = 0 := by rw [← hd]; exact hcrit κ hBκ
  have hκeq : κ = _ := fieldCurvature_eq hB.hasFDerivAt h0
  have hκκ : ⟪κ, κ⟫ = 0 := by
    rw [congrArg (fun w => ⟪w, κ⟫) hκeq]
    rw [inner_smul_left, inner_sub_left, inner_smul_left, hLκ, hbκ]
    simp
  exact inner_self_eq_zero.mp hκκ

/-- **Corollary B (critical point form).** If `|B|²` is critical at `x`
(`D|B|²(x) = 0`), `B x ≠ 0` and `∇ × B = 0` there, then `κ(x) = 0`. -/
theorem curvature_zero_of_normSq_critical {B : Euclid3 → Euclid3} {x : Euclid3}
    (hB : DifferentiableAt ℝ B x) (h0 : B x ≠ 0) (hcurl : fieldCurl B x = 0)
    (hcrit : fderiv ℝ (fun y => ‖B y‖ ^ 2) x = 0) :
    fieldCurvature B x = 0 := by
  apply fieldCurvature_eq_zero_of_transverse_critical hB h0 hcurl
  intro v _
  have h1 := (hasFDerivAt_norm_field hB.hasFDerivAt h0).fderiv
  have h2 := hB.hasFDerivAt.norm_sq.fderiv
  rw [hcrit] at h2
  have h3 := congrArg (fun T : Euclid3 →L[ℝ] ℝ => T v) h2
  simp only [zero_apply, smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, nsmul_eq_mul] at h3
  rw [h1]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul]
  have : ⟪B x, fderiv ℝ B x v⟫ = 0 := by
    have := h3.symm
    simpa using this
  rw [this, mul_zero]

/-- **Corollary B for vacuum fields: a local minimum of `|B|` with `B ≠ 0` has a straight
field line through it.** -/
theorem VacuumField.curvature_zero_of_isLocalMin {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hV : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) (h0 : B x ≠ 0)
    (hmin : IsLocalMin (fun y => ‖B y‖) x) : fieldCurvature B x = 0 := by
  have hB : DifferentiableAt ℝ B x :=
    (hV.contDiffOn.differentiableOn (by simp) x hx).differentiableAt (hV.isOpen.mem_nhds hx)
  apply fieldCurvature_eq_zero_of_transverse_critical hB h0 (hV.curl_eq_zero x hx)
  intro v _
  rw [hmin.fderiv_eq_zero, zero_apply]

/-- Corollary B at a local maximum of `|B|` (with `B ≠ 0`). -/
theorem VacuumField.curvature_zero_of_isLocalMax {Ω : Set Euclid3} {B : Euclid3 → Euclid3}
    (hV : VacuumField Ω B) {x : Euclid3} (hx : x ∈ Ω) (h0 : B x ≠ 0)
    (hmax : IsLocalMax (fun y => ‖B y‖) x) : fieldCurvature B x = 0 := by
  have hB : DifferentiableAt ℝ B x :=
    (hV.contDiffOn.differentiableOn (by simp) x hx).differentiableAt (hV.isOpen.mem_nhds hx)
  apply fieldCurvature_eq_zero_of_transverse_critical hB h0 (hV.curl_eq_zero x hx)
  intro v _
  rw [hmax.fderiv_eq_zero, zero_apply]

/-! ### Corollary C: no minimum-B along a closed field line -/

/-- **A closed field line is curved somewhere.** Let `γ` solve the field-line equation
`γ' = B ∘ γ` on `[0, T]`, `T > 0`, with `γ T = γ 0`, and suppose `B ≠ 0` and `B` is
differentiable along `γ`. Then the field-line curvature `κ` does not vanish at every
point of `γ([0, T])`. -/
theorem not_forall_fieldCurvature_eq_zero {B : Euclid3 → Euclid3} {γ : ℝ → Euclid3} {T : ℝ}
    (hT : 0 < T) (hγ : ∀ s ∈ Icc 0 T, HasDerivAt γ (B (γ s)) s)
    (h0 : ∀ s ∈ Icc 0 T, B (γ s) ≠ 0) (hB : ∀ s ∈ Icc 0 T, DifferentiableAt ℝ B (γ s))
    (closed : γ T = γ 0) : ¬ ∀ s ∈ Icc 0 T, fieldCurvature B (γ s) = 0 := by
  intro hκ
  -- the unit tangent `τ = b ∘ γ` has zero derivative on `[0, T]`
  have hτ (s : ℝ) (hs : s ∈ Icc 0 T) : HasDerivAt (fun r => unitField B (γ r)) 0 s := by
    have h1 := ((hasFDerivAt_unitField (hB s hs).hasFDerivAt (h0 s hs)).differentiableAt
      |>.hasFDerivAt).comp_hasDerivAt s (hγ s hs)
    have h2 : fderiv ℝ (unitField B) (γ s) (B (γ s)) = 0 := by
      have := hκ s hs
      rw [fieldCurvature] at this
      rw [← norm_smul_unitField (h0 s hs), map_smul, this, smul_zero]
    rw [h2] at h1
    exact h1
  have hτc : ContinuousOn (fun r => unitField B (γ r)) (Icc 0 T) :=
    fun s hs => (hτ s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hτc
    (fun s hs => (hτ s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
  set u₀ := unitField B (γ 0)
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hu₀ : ‖u₀‖ = 1 := norm_unitField (h0 0 h0mem)
  -- `f = ⟪γ, u₀⟫` has derivative `|B(γ s)| > 0`
  have hf (s : ℝ) (hs : s ∈ Icc 0 T) :
      HasDerivAt (fun r => ⟪γ r, u₀⟫) ‖B (γ s)‖ s := by
    have h1 := (hγ s hs).inner ℝ (hasDerivAt_const s u₀)
    have hBs : B (γ s) = ‖B (γ s)‖ • u₀ := by
      rw [← hconst s hs, norm_smul_unitField (h0 s hs)]
    convert h1 using 1
    rw [inner_zero_right, zero_add]
    nth_rewrite 2 [hBs]
    rw [inner_smul_left, real_inner_self_eq_norm_sq, hu₀]
    simp
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun r => ⟪γ r, u₀⟫)
    (fun s => ‖B (γ s)‖) hT (fun s hs => (hf s hs).continuousAt.continuousWithinAt)
    (fun s hs => hf s (Ioo_subset_Icc_self hs))
  rw [closed, sub_self, zero_div] at hslope
  exact h0 c (Ioo_subset_Icc_self hc) (norm_eq_zero.mp hslope)

/-- **Minimum-B along a closed axis** (first-order, transverse form): at every point of
`γ([0, T])` and along every line normal to `B`, `|B|` has a local minimum. -/
@[expose] def TransverseMinB (B : Euclid3 → Euclid3) (γ : ℝ → Euclid3) (T : ℝ) : Prop :=
  ∀ s ∈ Icc 0 T, ∀ v, ⟪B (γ s), v⟫ = 0 → IsLocalMin (fun σ : ℝ => ‖B (γ s + σ • v)‖) 0

/-- A local minimum of `|B|` along a normal line gives a vanishing directional derivative. -/
theorem fderiv_norm_field_eq_zero_of_isLocalMin_line {B : Euclid3 → Euclid3} {x v : Euclid3}
    (hB : DifferentiableAt ℝ B x) (h0 : B x ≠ 0)
    (hmin : IsLocalMin (fun σ : ℝ => ‖B (x + σ • v)‖) 0) :
    fderiv ℝ (fun y => ‖B y‖) x v = 0 := by
  have hN := ((hasFDerivAt_norm_field hB.hasFDerivAt h0).differentiableAt).hasFDerivAt
  have hline : HasDerivAt (fun σ : ℝ => x + σ • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h := hN.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  exact hmin.hasDerivAt_eq_zero h

/-- **Corollary C (vacuum, transverse form).** In a vacuum region `Ω` there is no closed
field line `γ` (`γ' = B ∘ γ` on `[0, T]`, `T > 0`, `γ T = γ 0`, `γ([0,T]) ⊆ Ω`) with
`B ≠ 0` along it, such that `|B|` has a local minimum at each of its points along every
line normal to `B` (`TransverseMinB`).

Remark (topology). If `Ω` is simply connected, a curl-free `B` is a gradient `∇Φ`, and
`Φ` strictly increases along field lines, so there are no closed field lines at all and
the statement is vacuous. It has content only in multiply connected regions (e.g. the
complement of a coil or of a toroidal current), which is the toroidal setting. A
non-vacuous instance (the straight-wire field `(-y, x, 0)/(x² + y²)` with the unit
circle as closed field line) is in `Sanity/CurvatureObstruction`. -/
theorem VacuumField.not_closed_fieldLine_transverse_minB {Ω : Set Euclid3}
    {B : Euclid3 → Euclid3} (hV : VacuumField Ω B) {γ : ℝ → Euclid3} {T : ℝ} (hT : 0 < T)
    (hγΩ : ∀ s ∈ Icc 0 T, γ s ∈ Ω) (hγ : ∀ s ∈ Icc 0 T, HasDerivAt γ (B (γ s)) s)
    (h0 : ∀ s ∈ Icc 0 T, B (γ s) ≠ 0) (closed : γ T = γ 0) : ¬ TransverseMinB B γ T := by
  intro hmin
  have hB (s : ℝ) (hs : s ∈ Icc 0 T) : DifferentiableAt ℝ B (γ s) :=
    (hV.contDiffOn.differentiableOn (by simp) _ (hγΩ s hs)).differentiableAt
      (hV.isOpen.mem_nhds (hγΩ s hs))
  refine not_forall_fieldCurvature_eq_zero hT hγ h0 hB closed (fun s hs => ?_)
  exact fieldCurvature_eq_zero_of_transverse_critical (hB s hs) (h0 s hs)
    (hV.curl_eq_zero _ (hγΩ s hs)) (fun v hv =>
      fderiv_norm_field_eq_zero_of_isLocalMin_line (hB s hs) (h0 s hs) (hmin s hs v hv))

/-- **Corollary C (vacuum, 3-D local minimum form).** In a vacuum region there is no
closed field line with `B ≠ 0` along it at every point of which `|B|` has a (3-D) local
minimum. -/
theorem VacuumField.not_closed_fieldLine_minB {Ω : Set Euclid3}
    {B : Euclid3 → Euclid3} (hV : VacuumField Ω B) {γ : ℝ → Euclid3} {T : ℝ} (hT : 0 < T)
    (hγΩ : ∀ s ∈ Icc 0 T, γ s ∈ Ω) (hγ : ∀ s ∈ Icc 0 T, HasDerivAt γ (B (γ s)) s)
    (h0 : ∀ s ∈ Icc 0 T, B (γ s) ≠ 0) (closed : γ T = γ 0) :
    ¬ ∀ s ∈ Icc 0 T, IsLocalMin (fun y => ‖B y‖) (γ s) := by
  intro hmin
  have hB (s : ℝ) (hs : s ∈ Icc 0 T) : DifferentiableAt ℝ B (γ s) :=
    (hV.contDiffOn.differentiableOn (by simp) _ (hγΩ s hs)).differentiableAt
      (hV.isOpen.mem_nhds (hγΩ s hs))
  exact not_forall_fieldCurvature_eq_zero hT hγ h0 hB closed
    (fun s hs => hV.curvature_zero_of_isLocalMin (hγΩ s hs) (h0 s hs) (hmin s hs))

end PlasmaLean.Vacuum
