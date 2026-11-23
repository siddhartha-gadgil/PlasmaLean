/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Theory.Fields.FormHYMStar
public import PlasmaLean.Sanity.FormHYMLift

/-!
# Sanity checks for the Hodge star on 2-forms of `ℝ³ × ℝ` (`Theory/Fields/FormHYMStar`)

1. **Values of the star.** `⋆(dx₁ ∧ dx₂)` is `1` on the plane `(e₀, e_τ)` and `0` on
   `(e₁, e₂)`; `⋆(dx₀ ∧ dτ)` is `1` on `(e₁, e₂)` and `0` on `(e₀, e_τ)`. The order of the
   factors matters: `⋆(dx₀ ∧ dx₁) = dx₂ ∧ dτ` is `1` on `(e₂, e_τ)` and `-1` on `(e_τ, e₂)`.
2. **Accepted.** The lift of `dx₁ ∧ dx₂` (field `e₀`) is a non-zero form with `⋆F = -F`; its
   squared norm is `2` and `F ∧ F = -2 vol` on the standard frame.
3. **Rejected.** The form with the opposite sign of `Sanity/FormHYMLift`,
   `π^*b + π^*(⋆b) ∧ dτ`, is non-zero and self-dual, so it is not anti-self-dual.
4. **Neither.** `π^*(dx₁ ∧ dx₂)` alone is neither self-dual nor anti-self-dual.
5. **Orientation.** For the opposite orientation the lift is self-dual (N-37).
6. **Circle.** The circle form of a constant field at the class of `τ` is the lift.
-/

public section
noncomputable section

namespace PlasmaLean.Sanity.FormHYMStar

open PlasmaLean PlasmaLean.Vacuum PlasmaLean.Forms PlasmaLean.Fields Matrix Module

/-- The dimension of the Euclidean lift space, needed to state TauCeti's Hodge star. -/
local instance : Fact (finrank ℝ LiftEuclid = 4) := ⟨finrank_liftEuclid⟩

/-! ### Values of the star -/

/-- `⋆(dx₁ ∧ dx₂)` is `1` on the plane `(e₀, e_τ)`. -/
theorem star_dx1dx2_tau :
    liftStar (ContinuousAlternatingMap.wedge (dX 1) (dX 2) : LiftForm 2)
      ![(coordVec 0, 0), (0, 1)] = 1 := by
  rw [liftStar_dX_wedge_dX.1, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-- `⋆(dx₁ ∧ dx₂)` vanishes on the plane `(e₁, e₂)`. -/
theorem star_dx1dx2_spatial :
    liftStar (ContinuousAlternatingMap.wedge (dX 1) (dX 2) : LiftForm 2)
      ![(coordVec 1, 0), (coordVec 2, 0)] = 0 := by
  rw [liftStar_dX_wedge_dX.1, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-- `⋆(dx₀ ∧ dτ)` is `1` on the plane `(e₁, e₂)`. -/
theorem star_dx0dtau_spatial :
    liftStar (ContinuousAlternatingMap.wedge (dX 0) dTau : LiftForm 2)
      ![(coordVec 1, 0), (coordVec 2, 0)] = 1 := by
  rw [liftStar_dX_wedge_dTau.1, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-- `⋆(dx₀ ∧ dτ)` vanishes on the plane `(e₀, e_τ)`. -/
theorem star_dx0dtau_tau :
    liftStar (ContinuousAlternatingMap.wedge (dX 0) dTau : LiftForm 2)
      ![(coordVec 0, 0), (0, 1)] = 0 := by
  rw [liftStar_dX_wedge_dTau.1, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-- `⋆(dx₀ ∧ dx₁)` is `1` on `(e₂, e_τ)`. -/
theorem star_dx0dx1_tau :
    liftStar (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2)
      ![(coordVec 2, 0), (0, 1)] = 1 := by
  rw [liftStar_dX_wedge_dX.2.2, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-- `⋆(dx₀ ∧ dx₁)` is `-1` on `(e_τ, e₂)`: the star has the sign of `dx₂ ∧ dτ`, not of
`dτ ∧ dx₂`. -/
theorem star_dx0dx1_tau_swapped :
    liftStar (ContinuousAlternatingMap.wedge (dX 0) (dX 1) : LiftForm 2)
      ![(0, 1), (coordVec 2, 0)] = -1 := by
  rw [liftStar_dX_wedge_dX.2.2, ContinuousAlternatingMap.wedge_apply_one_one]
  simp [dX_apply, coordVec]

/-! ### Accepted: the lift of `dx₁ ∧ dx₂` -/

/-- The lift of `dx₁ ∧ dx₂` is anti-self-dual for the star. -/
theorem lift_e0_antiSelfDual :
    liftStar (hymLiftAt (flux (coordVec 0))) = -hymLiftAt (flux (coordVec 0)) :=
  liftStar_hymLiftAt _

/-- The lift of `dx₁ ∧ dx₂` is not zero. -/
theorem lift_e0_ne_zero : hymLiftAt (flux (coordVec 0)) ≠ 0 := by
  intro h
  have := FormHYMLift.lift_e0_spatial
  rw [h] at this
  norm_num at this

/-- The lift of `dx₁ ∧ dx₂` is not self-dual. -/
theorem lift_e0_not_selfDual :
    liftStar (hymLiftAt (flux (coordVec 0))) ≠ hymLiftAt (flux (coordVec 0)) := by
  intro h
  have k := liftStar_apply_mixed (hymLiftAt (flux (coordVec 0)))
  rw [h, FormHYMLift.lift_e0_tau, FormHYMLift.lift_e0_spatial] at k
  norm_num at k

/-- The squared norm of the lift of `dx₁ ∧ dx₂` is `2`: `1` from `dx₁ ∧ dx₂` and `1` from
`dx₀ ∧ dτ`. -/
theorem lift_e0_inner : liftInner (hymLiftAt (flux (coordVec 0)))
    (hymLiftAt (flux (coordVec 0))) = 2 := by
  rw [liftInner_eq]
  simp only [hymLiftAt_apply, hodge_flux, flux_apply, volForm_vec, flat_apply]
  simp [coordVec, EuclideanSpace.inner_single_left]
  norm_num

/-- `F ∧ F = -|F|² vol` for the anti-self-dual lift: on the standard frame the value is `-2`. -/
theorem lift_e0_wedge_self :
    (ContinuousAlternatingMap.wedge (hymLiftAt (flux (coordVec 0)))
      (hymLiftAt (flux (coordVec 0))))
      ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)] = -2 := by
  have h := wedge_liftStar_apply (hymLiftAt (flux (coordVec 0))) (hymLiftAt (flux (coordVec 0)))
    ![(coordVec 0, 0), (coordVec 1, 0), (coordVec 2, 0), (0, 1)]
  rw [liftStar_hymLiftAt, lift_e0_inner, liftVol_frame,
    show -hymLiftAt (flux (coordVec 0)) = (-1 : ℝ) • hymLiftAt (flux (coordVec 0)) by simp,
    ContinuousAlternatingMap.wedge_smul_right] at h
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  linarith

/-! ### Rejected: the form with the opposite sign -/

/-- The wrong-sign form of `Sanity/FormHYMLift`, `π^*b + π^*(⋆b) ∧ dτ` for `b = dx₁ ∧ dx₂`. -/
def wrongSign : LiftForm 2 :=
  2 • (flux (coordVec 0)).compContinuousLinearMap (ContinuousLinearMap.fst ℝ Space ℝ) -
    hymLiftAt (flux (coordVec 0))

/-- The wrong-sign form is the self-dual lift of `dx₁ ∧ dx₂`. -/
theorem wrongSign_eq : wrongSign = sdLiftAt (flux (coordVec 0)) := by
  apply liftForm2_ext
  intro u v s t
  have e : ((Prod.fst : LiftSpace → Space) ∘ ![(u, s), (v, t)]) = ![u, v] := by
    funext i; fin_cases i <;> rfl
  simp only [wrongSign, sdLiftAt, ContinuousAlternatingMap.sub_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.coe_fst', e, hymLiftAt_apply, ofParts_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- The wrong-sign form is self-dual. -/
theorem wrongSign_selfDual : liftStar wrongSign = wrongSign := by
  rw [wrongSign_eq, liftStar_sdLiftAt]

/-- The wrong-sign form is not zero. -/
theorem wrongSign_ne_zero : wrongSign ≠ 0 := by
  intro h
  have k := congrArg spatialPart h
  rw [wrongSign_eq, sdLiftAt, spatialPart_ofParts, map_zero, map_eq_zero_iff _ flux.injective]
    at k
  have k0 := congrArg (fun v : Space => v 0) k
  simp [coordVec] at k0

/-- The wrong-sign form is not anti-self-dual for the star, in agreement with
`wrong_sign_not_antiSelfDual` for the component condition. -/
theorem wrongSign_not_antiSelfDual : liftStar wrongSign ≠ -wrongSign := by
  intro h
  exact FormHYMLift.wrong_sign_not_antiSelfDual ((isAntiSelfDual_iff_liftStar _).2 h)

/-! ### Neither self-dual nor anti-self-dual -/

/-- The star of `π^*(dx₁ ∧ dx₂)` is `dx₀ ∧ dτ`, which has no spatial part. -/
theorem star_spatial_only :
    liftStar (ofParts (flux (coordVec 0)) 0) = ofParts 0 (flat (coordVec 0)) := by
  simp

/-- `π^*(dx₁ ∧ dx₂)` alone is not self-dual. -/
theorem spatial_only_not_selfDual :
    liftStar (ofParts (flux (coordVec 0)) 0) ≠ ofParts (flux (coordVec 0)) 0 := by
  intro h
  have k := congrArg spatialPart h
  rw [star_spatial_only, spatialPart_ofParts, spatialPart_ofParts, eq_comm,
    map_eq_zero_iff _ flux.injective] at k
  have k0 := congrArg (fun v : Space => v 0) k
  simp [coordVec] at k0

/-- `π^*(dx₁ ∧ dx₂)` alone is not anti-self-dual. -/
theorem spatial_only_not_antiSelfDual :
    liftStar (ofParts (flux (coordVec 0)) 0) ≠ -ofParts (flux (coordVec 0)) 0 := by
  intro h
  have k := congrArg spatialPart h
  rw [star_spatial_only, map_neg, spatialPart_ofParts, spatialPart_ofParts, eq_comm,
    neg_eq_zero, map_eq_zero_iff _ flux.injective] at k
  have k0 := congrArg (fun v : Space => v 0) k
  simp [coordVec] at k0

/-! ### Orientation -/

/-- For the opposite orientation `dτ ∧ dx₀ ∧ dx₁ ∧ dx₂` the lift is self-dual (N-37): TauCeti's
star of the reversed orientation fixes it. -/
theorem lift_selfDual_opposite_orientation (b : Form 2) :
    (-liftOrientation).formHodgeStar two_add_two_eq_finrank_liftEuclid
      (euclidForm (hymLiftAt b)) = euclidForm (hymLiftAt b) := by
  rw [← euclidForm_neg_liftStar, liftStar_hymLiftAt, neg_neg]

/-! ### Circle -/

/-- The circle form of a constant field at the class of `τ` is the lift of the constant. -/
theorem const_circle (ℓ τ : ℝ) (b : Form 2) (x : Space) :
    hymLiftCircle ℓ (fun _ => b) (x, (τ : AddCircle ℓ)) = hymLiftAt b := rfl

/-- The circle form takes the same value at `τ` and `τ + ℓ`, which are the same point of the
circle. -/
theorem circle_period (ℓ τ : ℝ) (w : Space → Form 2) (x : Space) :
    hymLiftCircle ℓ w (x, ((τ + ℓ : ℝ) : AddCircle ℓ)) =
      hymLiftCircle ℓ w (x, (τ : AddCircle ℓ)) := by
  rw [AddCircle.coe_add_period]

end PlasmaLean.Sanity.FormHYMStar
