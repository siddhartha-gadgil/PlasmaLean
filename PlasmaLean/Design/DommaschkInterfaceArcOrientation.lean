/-
Copyright (c) 2026 PlasmaLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PlasmaLean contributors
-/
module

public import PlasmaLean.Design.DommaschkInterfaceArcBounds
public import PlasmaLean.Design.DommaschkKamEmbedded

/-!
# The sign of the interface normal relative to the certified polar centre

The oriented normal is the actual cross product of the toroidal and poloidal
chart derivatives in Euclidean three-space. On the θ=0 arc its scalar product
with the meridional displacement from the Q-16 centre is strictly positive.
The lower bound on radial displacement and the upper bound on vertical
displacement use the stored A/C nesting certificate.
-/

@[expose] public section
noncomputable section

namespace PlasmaLean.Design.DommaschkInterfaceArcOrientation

open PlasmaLean.Theory.KAM WEll1Z2 PlasmaLean.Forms PlasmaLean.Fields PlasmaLean.Contract
open PlasmaLean.Certificates.KronExpr KamNewton DommaschkKamA
open DommaschkKamC (RofC rotψi)
open DommaschkInterfaceArcGeometry DommaschkInterfaceArcProfiles DommaschkInterfaceArcBounds
open Real
open scoped RealInnerProductSpace

private theorem radial_gap {u z : FA} (h : ExactTorusA u z) (φ : ℝ) :
    1 / 100 < RofC u 0 φ - Rref φ := by
  let F := (rotψi u - rU) * cθ + (rotψi z - rZ) * sθ
  have hF : IsReal F := isReal_rad (isReal_rotψi' h.real_u) (isReal_rotψi' h.real_z)
  have e0 := nN_eRA
  rw [eval_eTree (s := 219) (F := 205) (by simp only [trN_eRA, Ex.eval])] at e0
  have hR : XN 205 = (xA 4 - rU) * cθ + (xA 5 - rZ) * sθ := by
    rw [show XN 205 = xN 197 * xN 199 + xN 198 * xN 200 from rfl, xN_XA, xN_YA, xN_ct, xN_st]
  rw [hR] at e0
  have hs := valN_le 219 (by norm_num)
  have he : Bd 0 (XN 219 * F - 1) (1 / 100) := by
    apply (sq_near e0 hs (rad_near h.osc_U h.osc_Z)).le
    have hq := (Rat.cast_le (K := ℝ)).2 (show (247113 / 25000000000000 : ℚ) +
      (BN 219 + EN 219) * (1 / 10 ^ 10 + 1 / 10 ^ 10) ≤ 1 / 100 by kernel_fact)
    push_cast at hq ⊢
    linarith
  have hsb : Bd 0 (XN 219) 70 := by
    apply hs.le
    exact_mod_cast (show BN 219 + EN 219 ≤ 70 by kernel_fact)
  have ef : (eval F 0 (2 * φ)).re = RofC u 0 φ - Rref φ := by
    simpa only [F, cos_zero, mul_one, sin_zero, mul_zero, add_zero] using
      (eval_rad (isReal_rotψi' h.real_u) (isReal_rotψi' h.real_z) 0 (2 * φ)).trans
        (rad_contract u z 0 φ).symm
  have ep := (Complex.abs_re_le_norm _).trans (norm_eval_le_of_Bd le_rfl he 0 (2 * φ))
  rw [eval_sub', WEll1Z2.eval_mul, eval_one, eval_ofReal_re hF] at ep
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, ef] at ep
  have hs' := (Complex.re_le_norm _).trans (norm_eval_le_of_Bd le_rfl hsb 0 (2 * φ))
  have hp : 0 < RofC u 0 φ - Rref φ := by simpa using h.radial_pos 0 φ
  linarith [(abs_le.mp ep).1, mul_le_mul_of_nonneg_right hs' hp.le]

private theorem vertical_gap {u z : FA} (h : ExactTorusA u z) (φ : ℝ) :
    |Zof z 0 φ - Zref φ| ≤ 3 / 50 := by
  have hv := normN 198 (by norm_num)
  rw [xN_YA] at hv
  have hd := h.osc_Z.add hv
  rw [sub_add_sub_cancel] at hd
  have hd' : Bd 0 (rotψi z - rZ) (3 / 50) := by
    apply hd.le
    have hq := (Rat.cast_le (K := ℝ)).2 (show (1 / 10 ^ 10 : ℚ) + BN 198 ≤ 3 / 50 by kernel_fact)
    push_cast at hq
    exact hq
  have he := (Complex.abs_re_le_norm _).trans (norm_eval_le_of_Bd le_rfl hd' 0 (2 * φ))
  simpa only [DommaschkKamNested.dist_coordsZ, eval_sub', Complex.sub_re] using he

/-- The meridional displacement from the certified polar centre to the surface point. -/
def polarRay (R z : ℝ → ℝ → ℝ) (θ φ : ℝ) : Space :=
  torusMap R z (θ, φ) - cylPoint (Rref φ) φ (Zref φ)

/-- The normal with the orientation used in the curvature row. -/
def chartNormal (R z : ℝ → ℝ → ℝ) (θ φ : ℝ) : Space :=
  let d := fderiv ℝ (torusMap R z) (θ, φ)
  cross (d (0, 1)) (d (1, 0))

/-- The Euclidean dot product is the meridional determinant times the cylindrical radius. -/
theorem normal_dot_polarRay {R z : ℝ → ℝ → ℝ} (h : PeriodicC2Torus R z) (θ φ : ℝ) :
    ⟪chartNormal R z θ φ, polarRay R z θ φ⟫ =
      R θ φ * ((R θ φ - Rref φ) * deriv (fun t => z t φ) θ -
        (z θ φ - Zref φ) * deriv (fun t => R t φ) θ) := by
  simp only [chartNormal, polarRay, h.fderiv_torusMap_θ, h.fderiv_torusMap_φ, torusMap,
    cylPoint, cross, cross_apply, PiLp.inner_apply, Fin.sum_univ_three, Real.inner_apply,
    PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, WithLp.ofLp_toLp]
  linear_combination (R θ φ * ((R θ φ - Rref φ) * deriv (fun t => z t φ) θ -
    (z θ φ - Zref φ) * deriv (fun t => R t φ) θ)) * (sin_sq_add_cos_sq φ)

/-- Throughout the certified arc the chosen geometric normal points towards greater
meridional radius relative to the certified polar centre. -/
theorem normal_dot_polarRay_positive {u z : FA} (h : ExactTorusA u z) {φ : ℝ}
    (hφ : φ ∈ Set.Icc 0 (1 / 5)) :
    0 < ⟪chartNormal (RofC u) (Zof z) 0 φ, polarRay (RofC u) (Zof z) 0 φ⟫ := by
  have hb := inBox_of_seedMargin h (seedMargins.2.2 φ hφ)
  have hz := mem_gridBox_iff.mp (hb .zθ)
  have hr := mem_gridBox_iff.mp (hb .rθ)
  change (1427 : ℝ) / 65536 ≤ deriv (fun t => Zof z t φ) 0 ∧ _ at hz
  simp only [Int.cast_neg, Int.cast_ofNat] at hr
  change (-88 : ℝ) / 65536 ≤ deriv (fun t => RofC u t φ) 0 ∧
    deriv (fun t => RofC u t φ) 0 ≤ 8 / 65536 at hr
  have hv : |deriv (fun t => RofC u t φ) 0| ≤ 1 / 500 := by
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
  have hcross := mul_le_mul (vertical_gap h φ) hv (abs_nonneg _) (by norm_num)
  rw [← abs_mul] at hcross
  have hmain := mul_le_mul (radial_gap h φ).le
    (show (1 / 50 : ℝ) ≤ deriv (fun t => Zof z t φ) 0 by linarith [hz.1])
    (by norm_num) (by linarith [radial_gap h φ])
  rw [normal_dot_polarRay (DommaschkKamEmbedded.torusA_embedded h).toPeriodicC2Torus]
  apply mul_pos (h.R_pos 0 φ)
  linarith [(abs_le.mp hcross).2]

end PlasmaLean.Design.DommaschkInterfaceArcOrientation
